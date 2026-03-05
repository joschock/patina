//! UEFI Protocol FFI definitions for PCI bus operations.
//!
//! Contains `#[repr(C)]` struct definitions for UEFI protocols consumed by the
//! PCI bus driver that are not available in the `r-efi` crate.

pub mod host_bridge_alloc;
pub mod root_bridge_io;
