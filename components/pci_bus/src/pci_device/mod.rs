//! PCI device data structures.
//!
//! This module re-exports BAR definitions, PCI config space header types,
//! and [`PciIoDevice`], the primary per-device state struct used throughout
//! PCI enumeration, resource allocation, and protocol production.

pub mod bar;
pub mod config_access;
pub mod device;
pub mod pci_config;

pub use bar::{PciBar, PciBarType};
pub use config_access::{PciConfigAccess, PciLocation};
pub use device::{PciIoDevice, PciIoDeviceRef};
pub use pci_config::{PCI_HEADER_TYPE_BRIDGE, PCI_HEADER_TYPE_MULTI_FUNC, PciType00, PciType01};
