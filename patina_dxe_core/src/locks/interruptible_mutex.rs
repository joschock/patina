//! InterruptibleMutex: enforces mutual exclusion for a critical section while
//! leaving interrupts enabled.
//!
//! Critical sections are protected by obtaining a `InterruptibleMutexGuard`
//! object from the `InterruptibleMutex` via the `lock` or `try_lock` methods.
//! The `InterruptibleMutexGuard` provides access to the protected data via
//! dereferencing. When the `InterruptibleMutexGuard` goes out of scope, the
//! lock is released.
//!
//! Interrupts are permitted during the lifetime of the guard, and are only
//! briefly disabled while acquiring and releasing the lock.
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

use crate::locks::interrupt_mutex::InterruptMutex;

pub struct InterruptibleMutex<T: ?Sized> {
    lock: InterruptMutex<bool>,
    data: UnsafeCell<T>,
}

pub struct InterruptibleMutexGuard<'a, T: ?Sized + 'a> {
    lock: &'a InterruptMutex<bool>,
    data: *mut T,
}

// Safety: InterruptMutex is used to protect against concurrent access to lock flag.
unsafe impl<T: ?Sized + Send> Sync for InterruptibleMutex<T> {}
// Safety: InterruptMutex is used to protect against concurrent access to lock flag.
unsafe impl<T: ?Sized + Send> Send for InterruptibleMutex<T> {}

// Safety: InterruptMutex is used to protect against concurrent access to lock flag.
unsafe impl<T: ?Sized + Sync> Sync for InterruptibleMutexGuard<'_, T> {}
// Safety: InterruptMutex is used to protect against concurrent access to lock flag.
unsafe impl<T: ?Sized + Send> Send for InterruptibleMutexGuard<'_, T> {}

impl<T> InterruptibleMutex<T> {
    #[allow(unused)]
    pub const fn new(data: T, name: &'static str) -> Self {
        // SAFETY: this implementation upholds the safety requirement that interrupts are not enabled while the
        // InterruptMutex lock is held.
        unsafe { Self { lock: InterruptMutex::new(false, name), data: UnsafeCell::new(data) } }
    }
}

impl<T: ?Sized> InterruptibleMutex<T> {
    /// Lock the Mutex and return a MutexGuard object used to access the data.
    ///
    /// Safety: Lock reentrance is not supported; attempt to re-lock something already locked will panic.
    #[allow(unused)]
    pub fn lock(&self) -> InterruptibleMutexGuard<'_, T> {
        self.try_lock().unwrap_or_else(|| panic!("Re-entrant locks for {:?} not permitted.", self.lock.name()))
    }

    /// Attempts to lock the Mutex, and if successful, returns a guard object that can be used to access the data.
    pub fn try_lock(&self) -> Option<InterruptibleMutexGuard<'_, T>> {
        let mut lock = self.lock.try_lock()?;

        if *lock {
            // Lock is already held, fail to acquire lock.
            None
        } else {
            // Acquire the lock.
            *lock = true;
            // SAFETY: data is only accessible through the lock, so it is safe to provide a mutable reference here.
            unsafe { Some(InterruptibleMutexGuard { lock: &self.lock, data: &mut *self.data.get() }) }
        }
    }
    #[allow(unused)]
    pub fn name(&self) -> &'static str {
        self.lock.name()
    }
}

impl<T: ?Sized> Deref for InterruptibleMutexGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &'_ T {
        //  SAFETY: data is only accessible through the lock.
        unsafe { &*self.data }
    }
}

impl<T: ?Sized> DerefMut for InterruptibleMutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &'_ mut T {
        //  SAFETY: data is only accessible through the lock.
        unsafe { &mut *self.data }
    }
}

impl<T: ?Sized> Drop for InterruptibleMutexGuard<'_, T> {
    fn drop(&mut self) {
        // Release the lock.
        // Note: any other context that might try_lock() (such as an interrupt handler) would be interrupting this
        // context and would release the lock before resuming this context. This means that try_lock() here should
        // always succeed. Use a try_lock().expect() to aid in debugging if this is not the case.
        let mut lock = self
            .lock
            .try_lock()
            .unwrap_or_else(|| panic!("Unable to acquire lock for {:?} in drop.", self.lock.name()));
        *lock = false;
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for InterruptibleMutex<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.try_lock() {
            Some(guard) => write!(f, "Mutex {{ data: ").and_then(|()| (*guard).fmt(f)).and_then(|()| write!(f, " }}")),
            None => write!(f, "Mutex {{ <locked> }}"),
        }
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for InterruptibleMutexGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for InterruptibleMutexGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[cfg(test)]
#[coverage(off)]
mod tests {
    use super::*;

    #[test]
    fn test_mutex_basic() {
        let lock = InterruptibleMutex::new(42, "test_lock");
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
    fn test_mutex_reentrant() {
        let lock = InterruptibleMutex::new(42, "test_lock");
        let _guard1 = lock.lock();
        let _guard2 = lock.lock(); // This should panic
    }

    #[test]
    fn test_mutex_try_lock() {
        let lock = InterruptibleMutex::new(42, "test_lock");
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
    fn test_mutex_debug() {
        let lock = InterruptibleMutex::new(42, "test_lock");
        let debug_str = format!("{:?}", lock);
        assert_eq!(debug_str, "Mutex { data: 42 }");
        let _guard = lock.lock();
        let debug_str_locked = format!("{:?}", lock);
        assert_eq!(debug_str_locked, "Mutex { <locked> }");
    }

    #[test]
    fn test_mutex_guard_debug_display() {
        let lock = InterruptibleMutex::new(42, "test_lock");
        {
            let guard = lock.lock();
            let debug_str = format!("{:?}", guard);
            assert_eq!(debug_str, "42");
            let display_str = format!("{}", guard);
            assert_eq!(display_str, "42");
        }
    }
}
