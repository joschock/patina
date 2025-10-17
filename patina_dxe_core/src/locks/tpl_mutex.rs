//! TplMutex: Mutex implementation that also adjusts UEFI TPL levels
//!
//! This module uses a Mutex to provide mutual exclusion, but also raises and
//! lowers the UEFI TPL level when the mutex is locked and unlocked.
//!
//! This mutex guarantees that the critical section protected by the guard
//! cannot be interrupted by code running at TPL equal to or lower than the
//! lock's TPL level. At TPL_HIGH_LEVEL, interrupts are disabled, so that
//! means that the critical section cannot be interrupted by anything.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
use core::{
    fmt,
    ops::{Deref, DerefMut},
};

use r_efi::efi;

use crate::{
    events::{raise_tpl, restore_tpl},
    locks::interruptible_mutex::{InterruptibleMutex, InterruptibleMutexGuard},
};

/// Used to guard data with a locked MUTEX and TPL level.
pub struct TplMutex<T: ?Sized> {
    tpl_lock_level: efi::Tpl,
    data: InterruptibleMutex<T>,
}
/// Wrapper for guarded data, which can be accessed by Deref or DerefMut on this object.
pub struct TplGuard<'a, T: ?Sized + 'a> {
    release_tpl: efi::Tpl,
    guard: Option<InterruptibleMutexGuard<'a, T>>,
}

unsafe impl<T: ?Sized + Send> Sync for TplMutex<T> {}
unsafe impl<T: ?Sized + Send> Send for TplMutex<T> {}

unsafe impl<T: ?Sized + Sync> Sync for TplGuard<'_, T> {}
unsafe impl<T: ?Sized + Send> Send for TplGuard<'_, T> {}

impl<T> TplMutex<T> {
    /// Instantiates a new TplMutex with the given TPL level, data object, and name string.
    pub const fn new(tpl_lock_level: efi::Tpl, data: T, name: &'static str) -> Self {
        Self { tpl_lock_level, data: InterruptibleMutex::new(data, name) }
    }
}

impl<T: ?Sized> TplMutex<T> {
    /// Lock the TplMutex and return a TplGuard object used to access the data. This will raise the system TPL level
    /// to the level specified at TplMutex creation.
    ///
    /// Safety: Lock reentrance is not supported; attempt to re-lock something already locked will panic.
    pub fn lock(&self) -> TplGuard<'_, T> {
        self.try_lock().unwrap_or_else(|| panic!("Re-entrant locks for {:?} not permitted.", self.data.name()))
    }

    /// Attempts to lock the TplMutex, and if successful, returns a guard object that can be used to access the data.
    pub fn try_lock(&self) -> Option<TplGuard<'_, T>> {
        let release_tpl = raise_tpl(self.tpl_lock_level);
        if let Some(guard) = self.data.try_lock() {
            Some(TplGuard { release_tpl, guard: Some(guard) })
        } else {
            restore_tpl(release_tpl);
            None
        }
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for TplMutex<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.try_lock() {
            Some(guard) => write!(
                f,
                "TplMutex {{ lock_tpl: {:x?}, release_tpl: {:x?}, data: ",
                self.tpl_lock_level, guard.release_tpl
            )
            .and_then(|()| (*guard).fmt(f))
            .and_then(|()| write!(f, " }}")),
            None => write!(f, "TplMutex {{ lock_tpl: {:x?}, data: <locked> }}", self.tpl_lock_level),
        }
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for TplGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for TplGuard<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized> Deref for TplGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &'_ T {
        self.guard.as_ref().expect("invalid deref of dropped guard")
    }
}

impl<T: ?Sized> DerefMut for TplGuard<'_, T> {
    fn deref_mut(&mut self) -> &'_ mut T {
        self.guard.as_mut().expect("invalid deref_mut of dropped guard")
    }
}

impl<T: ?Sized> Drop for TplGuard<'_, T> {
    fn drop(&mut self) {
        let guard = self.guard.take().expect("invalid drop of already-dropped guard");
        // Ensure MutexGuard is dropped before restoring TPL. This is needed since restoring the TPL may
        // invoke notification callbacks that could try to acquire the same mutex.
        drop(guard);
        restore_tpl(self.release_tpl);
    }
}

#[cfg(test)]
#[coverage(off)]
mod tests {
    use super::*;

    fn with_reset_state<F: Fn() + std::panic::RefUnwindSafe>(f: F) {
        let result = crate::test_support::with_global_lock(|| {
            raise_tpl(efi::TPL_HIGH_LEVEL);
            restore_tpl(efi::TPL_APPLICATION);
            f();
        });
        match result {
            Ok(()) => {}
            Err(e) => {
                std::panic::resume_unwind(e);
            }
        }
    }

    #[test]
    fn test_tpl_mutex_basic() {
        with_reset_state(|| {
            let lock = TplMutex::new(efi::TPL_NOTIFY, 42, "test_lock");
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
        });
    }

    #[test]
    #[should_panic(expected = "Re-entrant locks for \"test_lock\" not permitted.")]
    fn test_tpl_mutex_reentrant() {
        with_reset_state(|| {
            let lock = TplMutex::new(efi::TPL_NOTIFY, 42, "test_lock");
            let _guard1 = lock.lock();
            let _guard2 = lock.lock(); // This should panic
        });
    }

    #[test]
    fn test_tpl_mutex_try_lock() {
        with_reset_state(|| {
            let lock = TplMutex::new(efi::TPL_NOTIFY, 42, "test_lock");
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
        });
    }
    #[test]
    fn test_tpl_mutex_debug() {
        with_reset_state(|| {
            let lock = TplMutex::new(efi::TPL_NOTIFY, 42, "test_lock");
            let debug_str = format!("{:?}", lock);
            assert_eq!(debug_str, "TplMutex { lock_tpl: 10, release_tpl: 4, data: 42 }");
            let _guard = lock.lock();
            let debug_str_locked = format!("{:?}", lock);
            assert_eq!(debug_str_locked, "TplMutex { lock_tpl: 10, data: <locked> }");
        });
    }

    #[test]
    fn test_tpl_mutex_guard_debug_display() {
        with_reset_state(|| {
            let lock = TplMutex::new(efi::TPL_NOTIFY, 42, "test_lock");
            {
                let guard = lock.lock();
                let debug_str = format!("{:?}", guard);
                assert_eq!(debug_str, "42");
                let display_str = format!("{}", guard);
                assert_eq!(display_str, "42");
            }
        });
    }
}
