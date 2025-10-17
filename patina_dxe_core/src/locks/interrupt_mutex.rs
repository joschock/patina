//! InterruptMutex: A mutex that disables interrupts to provide mutual
//! exclusion.
//!
//! Critical sections are protected by obtaining an `InterruptGuard` object from
//! the `InterruptMutex` via the `lock` or `try_lock` methods. The
//! `InterruptGuard` provides access to the protected data via dereferencing.
//! When the `InterruptGuard` goes out of scope, the lock is released.
//!
//! Interrupts are disabled when the lock is held, and restored to their
//! previous state when the lock is released.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use core::{
    cell::UnsafeCell,
    fmt,
    ops::{Deref, DerefMut},
};

pub struct InterruptMutex<T: ?Sized> {
    locked: UnsafeCell<bool>,
    name: &'static str,
    data: UnsafeCell<T>,
}

pub struct InterruptGuard<'a, T: ?Sized + 'a> {
    lock: &'a UnsafeCell<bool>,
    interrupts_enabled: bool,
    #[allow(unused)]
    name: &'static str,
    data: *mut T,
}

// Safety: interrupt control is used to protect against concurrent access.
unsafe impl<T: ?Sized + Send> Sync for InterruptMutex<T> {}
// Safety: interrupt control is used to protect against concurrent access.
unsafe impl<T: ?Sized + Send> Send for InterruptMutex<T> {}

// Safety: interrupt control is used to protect against concurrent access.
unsafe impl<T: ?Sized + Sync> Sync for InterruptGuard<'_, T> {}
// Safety: interrupt control is used to protect against concurrent access.
unsafe impl<T: ?Sized + Send> Send for InterruptGuard<'_, T> {}

impl<T> InterruptMutex<T> {
    /// Creates a new InterruptMutex wrapping the provided data.
    ///
    /// # Safety
    ///
    /// Caller must ensure that critical sections protected by this mutex do not enable interrupts.
    /// Enabling interrupts while holding the lock will violate the mutual exclusion guarantee.
    ///
    /// Note: restore_tpl() will re-enable interrupts if restoring to a TPL lower than TPL_HIGH_LEVEL and would thus
    /// violate the safety contract.
    ///
    #[allow(dead_code)]
    pub const unsafe fn new(data: T, name: &'static str) -> Self {
        Self { locked: UnsafeCell::new(false), name, data: UnsafeCell::new(data) }
    }
}

// Returns whether interrupts are currently enabled (true) or disabled (false).
fn interupts_enabled() -> bool {
    patina_internal_cpu::interrupts::get_interrupt_state().expect("Interrupts non-functional.")
}

// Disables interrupts and returns the previous interrupt state.
fn disable_interrupts() -> bool {
    let current_state = interupts_enabled();
    if current_state {
        patina_internal_cpu::interrupts::disable_interrupts();
    }
    current_state
}

// Restores interrupts to the provided state.
fn restore_interrupts(state: bool) {
    if state {
        patina_internal_cpu::interrupts::enable_interrupts()
    }
}

impl<T: ?Sized> InterruptMutex<T> {
    /// Lock the InterruptMutex and return an InterruptGuard object used to access the data.
    ///
    /// Safety: Lock reentrance is not supported; attempt to re-lock something already locked will panic.
    #[allow(dead_code)]
    pub fn lock(&self) -> InterruptGuard<'_, T> {
        self.try_lock().unwrap_or_else(|| panic!("Re-entrant locks for {:?} not permitted.", self.name))
    }

    /// Attempts to lock the InterruptMutex, and if successful, returns a guard object that can be used to access the data.
    pub fn try_lock(&self) -> Option<InterruptGuard<'_, T>> {
        let interrupts_enabled = disable_interrupts();
        // SAFETY: Interrupts are disabled.
        if unsafe { self.locked.get().read_volatile() } {
            // Lock is already held, restore interrupt state and fail to acquire lock.
            debug_assert!(
                !interupts_enabled(),
                "Interrupts were re-enabled while holding the lock for {:?}. This violates mutual exclusion!",
                self.name
            );
            restore_interrupts(interrupts_enabled);
            None
        } else {
            // SAFETY: The lock enforces single-threaded access to the data, so it is safe to provide a mutable reference here.
            unsafe {
                self.locked.get().write_volatile(true);
                Some(InterruptGuard {
                    lock: &self.locked,
                    interrupts_enabled,
                    name: self.name,
                    data: &mut *self.data.get(),
                })
            }
        }
    }

    #[allow(unused)]
    pub fn name(&self) -> &'static str {
        self.name
    }
}

impl<T: ?Sized> Deref for InterruptGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &'_ T {
        //  SAFETY: data is only accessible through the lock.
        unsafe { &*self.data }
    }
}

impl<T: ?Sized> DerefMut for InterruptGuard<'_, T> {
    fn deref_mut(&mut self) -> &'_ mut T {
        //  SAFETY: data is only accessible through the lock.
        unsafe { &mut *self.data }
    }
}

impl<T: ?Sized> Drop for InterruptGuard<'_, T> {
    fn drop(&mut self) {
        debug_assert!(
            !interupts_enabled(),
            "Interrupts were re-enabled while holding the lock for {:?}. This violates mutual exclusion!",
            self.name
        );
        // SAFETY: We hold the lock and that implies interrupts are disabled.
        unsafe { self.lock.get().write_volatile(false) };
        restore_interrupts(self.interrupts_enabled);
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for InterruptMutex<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.try_lock() {
            Some(guard) => {
                write!(f, "InterruptMutex {{ data: ").and_then(|()| (*guard).fmt(f)).and_then(|()| write!(f, " }}"))
            }
            None => write!(f, "InterruptMutex {{ <locked> }}"),
        }
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for InterruptGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for InterruptGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[cfg(test)]
#[coverage(off)]
mod tests {
    use super::*;

    #[test]
    fn test_interrupt_mutex_basic() {
        // SAFETY: This test code upholds the safety contract by never enabling interrupts while holding the lock.
        let lock = unsafe { InterruptMutex::new(42, "test_lock") };
        {
            let guard = lock.lock();
            assert_eq!(*guard, 42);
        }
        {
            let mut guard = lock.lock();
            *guard = 43;
        }
        {
            let guard = lock.lock();
            assert_eq!(*guard, 43);
        }
    }

    #[test]
    #[should_panic(expected = "Re-entrant locks for \"test_lock\" not permitted.")]
    fn test_interrupt_mutex_reentrant() {
        // SAFETY: This test code upholds the safety contract by never enabling interrupts while holding the lock.
        let lock = unsafe { InterruptMutex::new(42, "test_lock") };
        let _guard1 = lock.lock();
        let _guard2 = lock.lock(); // This should panic
    }

    #[test]
    fn test_interrupt_mutex_try_lock() {
        // SAFETY: This test code upholds the safety contract by never enabling interrupts while holding the lock.
        let lock = unsafe { InterruptMutex::new(42, "test_lock") };
        {
            let guard1 = lock.try_lock().expect("Failed to acquire lock");
            assert_eq!(*guard1, 42);
            let guard2 = lock.try_lock();
            assert!(guard2.is_none(), "Should not be able to acquire lock while already held");
        }
        {
            let guard3 = lock.try_lock().expect("Failed to acquire lock after release");
            assert_eq!(*guard3, 42);
        }
    }

    #[test]
    fn test_interrupt_mutex_debug() {
        // SAFETY: This test code upholds the safety contract by never enabling interrupts while holding the lock.
        let lock = unsafe { InterruptMutex::new(42, "test_lock") };
        let debug_str = format!("{:?}", lock);
        assert_eq!(debug_str, "InterruptMutex { data: 42 }");
        let _guard = lock.lock();
        let debug_str_locked = format!("{:?}", lock);
        assert_eq!(debug_str_locked, "InterruptMutex { <locked> }");
    }

    #[test]
    fn test_interrupt_guard_debug_display() {
        // SAFETY: This test code upholds the safety contract by never enabling interrupts while holding the lock.
        let lock = unsafe { InterruptMutex::new(42, "test_lock") };
        {
            let guard = lock.lock();
            let debug_str = format!("{:?}", guard);
            assert_eq!(debug_str, "42");
            let display_str = format!("{}", guard);
            assert_eq!(display_str, "42");
        }
    }
}
