//! PCI device data structures.
//!
//! This module re-exports BAR definitions, PCI config space header types,
//! and [`PciIoDevice`], the primary per-device state struct used throughout
//! PCI enumeration, resource allocation, and protocol production.

pub mod bar;
pub mod device;
pub mod pci_config;

pub use bar::{PCI_MAX_BAR, PciBar, PciBarType};
pub use device::{PciIoDevice, PciIoDeviceRef};
pub use pci_config::{PciType00, PciType01};
