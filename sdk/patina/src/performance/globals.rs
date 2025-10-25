//! Globals used in the Patina SDK performance code.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation.
//!
//! SPDX-License-Identifier: Apache-2.0
//!
use crate::{
    boot_services::{StandardBootServices, tpl::Tpl},
    performance::table::FBPT,
    tpl_mutex::TplMutex,
};
use core::cell::OnceCell;

struct GlobalState {
    boot_services: StandardBootServices,
    fbpt: TplMutex<FBPT>,
    image_count: TplMutex<u32>,
    perf_measurement_mask: TplMutex<u32>,
}
/// Static state for the performance component.
struct StaticState(OnceCell<GlobalState>);

impl StaticState {
    /// Creates a new uninitialized static state.
    const fn uninit() -> Self {
        Self(OnceCell::new())
    }

    /// Initializes the static state.
    ///
    /// ## Errors
    ///
    /// Returns `Already initialized` if the static state has already been initialized.
    /// Returns `Currently initializing somewhere else` if another thread is currently initializing the static state.
    fn init(&self, bs: StandardBootServices) -> Result<(), &'static str> {
        // ensure concurrent initialization of static state is prevented. Use TPL_HIGH_LEVEL to block interrupts.
        let mutex = TplMutex::new(bs.clone(), Tpl(r_efi::efi::TPL_HIGH_LEVEL), ());
        let _init_guard = mutex.lock();
        self.0
            .set(GlobalState {
                boot_services: bs.clone(),
                fbpt: TplMutex::new(bs.clone(), Tpl::NOTIFY, FBPT::new()),
                image_count: TplMutex::new(bs.clone(), Tpl::NOTIFY, 0),
                perf_measurement_mask: TplMutex::new(bs.clone(), Tpl::NOTIFY, 0),
            })
            .map_err(|_| "Already initialized")
    }

    /// Gets the inner static state if it has been initialized.
    ///
    /// Returns `None` if the state is not yet initialized.
    /// Returns `None` if the state is currently being initialized.
    /// Returns `Some` with references to the `GlobalState` if initialized.
    fn inner(&self) -> Option<&GlobalState> {
        self.0.get()
    }
}

/// SAFETY: Initializing the `OnceCell` under TPL_HIGH_LEVEL satisfies the `Send` requirement for
/// synchronization on the `set` calls inside `init`.
unsafe impl Send for StaticState {}

/// SAFETY: Initializing the `OnceCell` under TPL_HIGH_LEVEL satisfies the `Send` requirement for
/// synchronization on the `set` calls inside `init`.
unsafe impl Sync for StaticState {}

static STATIC_STATE: StaticState = StaticState::uninit();

/// Set performance component static state.
pub fn set_perf_measurement_mask(mask: u32) {
    if let Some(state) = STATIC_STATE.inner() {
        *state.perf_measurement_mask.lock() = mask;
    } else {
        log::warn!("Performance static state not initialized, cannot set mask.");
    }
}

/// Get performance component static state.
pub fn get_perf_measurement_mask() -> u32 {
    if let Some(state) = STATIC_STATE.inner() {
        *state.perf_measurement_mask.lock()
    } else {
        log::warn!("Performance static state not initialized, returning 0 mask.");
        0
    }
}

/// Get the current load image count.
pub fn get_load_image_count() -> u32 {
    if let Some(state) = STATIC_STATE.inner() {
        *state.image_count.lock()
    } else {
        log::warn!("Performance static state not initialized, returning 0 image count.");
        0
    }
}

/// Increment the load image count.
pub fn increment_load_image_count() {
    if let Some(state) = STATIC_STATE.inner() {
        *state.image_count.lock() += 1;
    } else {
        log::warn!("Performance static state not initialized, cannot increment image count.");
    }
}

/// Set load image count to a specific value.
pub fn set_load_image_count(count: u32) {
    if let Some(state) = STATIC_STATE.inner() {
        *state.image_count.lock() = count;
    } else {
        log::warn!("Performance static state not initialized, cannot set image count.");
    }
}

/// Set performance component static state.
#[coverage(off)]
pub fn set_static_state(boot_services: StandardBootServices) -> Result<(), &'static str> {
    STATIC_STATE.init(boot_services)
}

/// Get performance component static state.
#[coverage(off)]
pub fn get_static_state() -> Option<(&'static StandardBootServices, &'static TplMutex<FBPT>)> {
    STATIC_STATE.inner().map(|state| (&state.boot_services, &state.fbpt))
}

#[cfg(test)]
#[coverage(off)]
mod tests {
    use super::*;
    use r_efi::efi;
    pub fn create_static_boot_services() -> StandardBootServices {
        let boot_services = core::mem::MaybeUninit::zeroed();
        let mut boot_services: efi::BootServices = unsafe { boot_services.assume_init() };

        // Create dummy function pointers to use for initialization
        extern "efiapi" fn dummy_raise_tpl(_new_tpl: efi::Tpl) -> efi::Tpl {
            0
        }
        extern "efiapi" fn dummy_restore_tpl(_old_tpl: efi::Tpl) {}

        boot_services.raise_tpl = dummy_raise_tpl;
        boot_services.restore_tpl = dummy_restore_tpl;
        unsafe { StandardBootServices::new(Box::leak(Box::new(boot_services))) }
    }

    #[test]
    fn test_get_static_state() {
        let static_boot_services = create_static_boot_services();
        static STATIC_STATE: StaticState = StaticState::uninit();
        assert!(STATIC_STATE.inner().is_none());
        assert!(STATIC_STATE.init(static_boot_services.clone()).is_ok());
        assert!(STATIC_STATE.inner().is_some());
        assert!(STATIC_STATE.init(static_boot_services.clone()).is_err());
    }
}
