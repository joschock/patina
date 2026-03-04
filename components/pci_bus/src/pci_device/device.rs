//! PCI I/O device state.
//!
//! Defines [`PciIoDevice`], the central per-device struct that tracks identity,
//! BAR state, hierarchy, capabilities, and lifecycle status for each discovered
//! PCI device.
//!


use alloc::{rc::Rc, vec::Vec};
use core::cell::RefCell;

use r_efi::efi;

use super::{
    PCI_MAX_BAR, PciBar,
    pci_config::PciType00,
};
use crate::protocols::root_bridge_io::PciRootBridgeIoProtocol;

/// Shared, mutable reference to a [`PciIoDevice`].
pub type PciIoDeviceRef = Rc<RefCell<PciIoDevice>>;

/// Bridge decode capability flags.
///
pub mod bridge_decode {
    /// Bridge supports 32-bit I/O decode.
    pub const IO32: u32 = 0x0001;
    /// Bridge supports 32-bit prefetchable memory decode.
    pub const PMEM32: u32 = 0x0002;
    /// Bridge supports 64-bit prefetchable memory decode.
    pub const PMEM64: u32 = 0x0004;
    /// Bridge supports 16-bit I/O decode.
    pub const IO16: u32 = 0x0008;
    /// Bridge supports combined prefetchable/non-prefetchable memory.
    pub const PMEM_MEM_COMBINE: u32 = 0x0010;
    /// Bridge supports 64-bit non-prefetchable memory decode.
    pub const MEM64: u32 = 0x0020;
    /// Bridge supports 32-bit non-prefetchable memory decode.
    pub const MEM32: u32 = 0x0040;
}

/// Per-PCI-device state used throughout enumeration, resource allocation,
/// and PCI I/O Protocol production.
pub struct PciIoDevice {
    // -- Handle & identity --
    /// UEFI handle for this device (set during registration).
    pub handle: efi::Handle,
    /// Bus number.
    pub bus_number: u8,
    /// Device number (0-31).
    pub device_number: u8,
    /// Function number (0-7).
    pub function_number: u8,
    /// PCI Type 00h configuration space header, read during enumeration.
    pub pci: PciType00,

    // -- Protocols --
    /// Device path protocol for this device.
    pub device_path: *mut r_efi::protocols::device_path::Protocol,
    /// Pointer to the PCI Root Bridge I/O Protocol for the root bridge
    /// this device is behind.
    pub pci_root_bridge_io: *mut PciRootBridgeIoProtocol,

    // -- BARs --
    /// Standard BARs (6 entries).
    pub pci_bar: [PciBar; PCI_MAX_BAR],

    // -- Hierarchy --
    /// Parent bridge (None for root bridge children).
    pub parent: Option<alloc::rc::Weak<RefCell<PciIoDevice>>>,
    /// Child devices (populated for bridges).
    pub child_list: Vec<PciIoDeviceRef>,

    // -- Lifecycle flags --
    /// True if a UEFI handle has been created for this device.
    pub registered: bool,
    /// True if resources have been allocated for this device.
    pub allocated: bool,

    // -- Attributes --
    /// Currently enabled attributes.
    pub attributes: u64,
    /// Attributes supported by this device.
    pub supports: u64,
    /// Bridge decode capabilities (combination of `bridge_decode` flags).
    pub decodes: u32,

    // -- Option ROM --
    /// True if the ROM image originates from the device's expansion ROM BAR.
    pub embedded_rom: bool,
    /// Size of the option ROM image in bytes.
    pub rom_size: u32,
    /// True if all option ROM images have been processed.
    pub all_op_rom_processed: bool,
    /// True if an EFI driver was found in the option ROM.
    pub bus_override: bool,
    /// If true, skip option ROM processing for this device.
    pub ignore_rom: bool,

    // -- PCIe / capability offsets --
    /// True if this device has PCIe capabilities.
    pub is_pci_exp: bool,
    /// True if ARI (Alternative Routing-ID Interpretation) is enabled.
    pub is_ari_enabled: bool,
    /// Offset of the PCIe capability structure in config space.
    pub pci_express_capability_offset: u8,
    /// Offset of the ARI extended capability (0 if not present).
    pub ari_capability_offset: u32,
    /// Offset of the SR-IOV extended capability (0 if not present).
    pub sriov_capability_offset: u32,
    /// Offset of the MR-IOV extended capability (0 if not present).
    pub mriov_capability_offset: u32,

    // -- SR-IOV --
    /// Virtual Function BARs (for SR-IOV capable devices).
    pub vf_pci_bar: [PciBar; PCI_MAX_BAR],
    /// System page size for SR-IOV.
    pub system_page_size: u32,
    /// Initial number of Virtual Functions.
    pub initial_vfs: u16,
    /// Number of bus numbers reserved for this device's VFs.
    pub reserved_bus_num: u16,

    // -- Bridge-specific --
    /// Non-standard I/O window alignment for PCI-PCI bridges (default 4K).
    pub bridge_io_alignment: u16,

    // -- Resizable BAR --
    /// Offset of the Resizable BAR extended capability (0 if not present).
    pub resizable_bar_offset: u32,
    /// Number of resizable BARs.
    pub resizable_bar_number: u32,

    // -- PCIe Max Payload --
    /// Maximum payload size setting.
    pub max_payload_size: u8,

    // -- Hot plug --
    /// Resource padding descriptors for hot-pluggable slots.
    pub resource_padding_descriptors: *mut core::ffi::c_void,
    /// Padding attributes for hot plug resource reservation.
    pub padding_attributes: u64,
    /// Bus number range descriptors for PCI root bridges.
    pub bus_number_ranges: *mut core::ffi::c_void,
}

impl PciIoDevice {
    /// Creates a new `PciIoDevice` with default/zero values.
    pub fn new() -> Self {
        Self {
            handle: core::ptr::null_mut(),
            bus_number: 0,
            device_number: 0,
            function_number: 0,
            pci: PciType00::default(),
            device_path: core::ptr::null_mut(),
            pci_root_bridge_io: core::ptr::null_mut(),
            pci_bar: [PciBar::default(); PCI_MAX_BAR],
            parent: None,
            child_list: Vec::new(),
            registered: false,
            allocated: false,
            attributes: 0,
            supports: 0,
            decodes: 0,
            embedded_rom: false,
            rom_size: 0,
            all_op_rom_processed: false,
            bus_override: false,
            ignore_rom: false,
            is_pci_exp: false,
            is_ari_enabled: false,
            pci_express_capability_offset: 0,
            ari_capability_offset: 0,
            sriov_capability_offset: 0,
            mriov_capability_offset: 0,
            vf_pci_bar: [PciBar::default(); PCI_MAX_BAR],
            system_page_size: 0,
            initial_vfs: 0,
            reserved_bus_num: 0,
            bridge_io_alignment: 0,
            resizable_bar_offset: 0,
            resizable_bar_number: 0,
            max_payload_size: 0,
            resource_padding_descriptors: core::ptr::null_mut(),
            padding_attributes: 0,
            bus_number_ranges: core::ptr::null_mut(),
        }
    }
}

impl Default for PciIoDevice {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_pci_io_device_default() {
        let dev = PciIoDevice::new();
        assert_eq!(dev.bus_number, 0);
        assert_eq!(dev.device_number, 0);
        assert_eq!(dev.function_number, 0);
        assert!(!dev.registered);
        assert!(!dev.allocated);
        assert!(!dev.is_pci_exp);
        assert!(dev.child_list.is_empty());
        assert_eq!(dev.pci.hdr.vendor_id, 0);
    }
}
