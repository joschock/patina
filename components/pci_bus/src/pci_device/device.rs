//! PCI I/O device state.
//!
//! Defines [`PciIoDevice`], the central per-device struct that tracks identity,
//! BAR state, hierarchy, capabilities, and lifecycle status for each discovered
//! PCI device.

use alloc::{rc::Rc, vec::Vec};
use core::cell::RefCell;

use r_efi::efi;

use super::{
    PciBar,
    bar::InvalidBarError,
    config_access::{PciConfigAccess, PciLocation},
    pci_config::{PCI_HEADER_TYPE_BRIDGE, PciType00},
};
use crate::protocols::root_bridge_io::PciRootBridgeIoProtocol;

// -- BAR scanning constants --

const PCI_BAR0_OFFSET: u32 = 0x10;
const PCI_BAR1_OFFSET: u32 = 0x14;
const PCI_BAR5_OFFSET: u32 = 0x24;
const BAR_REGISTER_SIZE: u32 = 4;

// BAR register bit fields
const BAR_BIT_IO_SPACE: u32 = 0x01;
const BAR_MEM_TYPE_MASK: u32 = 0x06;
const BAR_MEM_TYPE_32: u32 = 0x00;
const BAR_MEM_TYPE_64: u32 = 0x04;
const BAR_BIT_PREFETCHABLE: u32 = 0x08;

// -- Capability constants --

const PCI_CAPABILITY_POINTER_OFFSET: u32 = 0x34;
const PCIE_CAPABILITY_BASE_OFFSET: u32 = 0x100;
const PCI_STATUS_OFFSET: u32 = 0x06;
const PCI_STATUS_CAPABILITIES_LIST: u16 = 0x0010;

const CAP_ID_PCIEXP: u8 = 0x10;
const EXCAP_ID_ARI: u16 = 0x000E;
const EXCAP_ID_SRIOV: u16 = 0x0010;
const EXCAP_ID_MRIOV: u16 = 0x0011;
const EXCAP_ID_REBAR: u16 = 0x0015;

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
#[allow(dead_code)]
pub struct PciIoDevice {
    // -- Handle & identity --
    /// UEFI handle for this device (set during registration).
    handle: efi::Handle,
    /// Bus number.
    bus_number: u8,
    /// Device number (0-31).
    device_number: u8,
    /// Function number (0-7).
    function_number: u8,
    /// PCI Type 00h configuration space header, read during enumeration.
    pci: PciType00,

    // -- Protocols --
    /// Device path protocol for this device.
    device_path: *mut r_efi::protocols::device_path::Protocol,
    /// Pointer to the PCI Root Bridge I/O Protocol for the root bridge
    /// this device is behind.
    pci_root_bridge_io: *mut PciRootBridgeIoProtocol,

    // -- BARs --
    /// Decoded BARs for this device.
    pci_bar: Vec<PciBar>,

    // -- Hierarchy --
    /// Parent bridge (None for root bridge children).
    parent: Option<alloc::rc::Weak<RefCell<PciIoDevice>>>,
    /// Child devices (populated for bridges).
    child_list: Vec<PciIoDeviceRef>,

    // -- Lifecycle flags --
    /// True if a UEFI handle has been created for this device.
    registered: bool,
    /// True if resources have been allocated for this device.
    allocated: bool,

    // -- Attributes --
    /// Currently enabled attributes.
    attributes: u64,
    /// Attributes supported by this device.
    supports: u64,
    /// Bridge decode capabilities (combination of `bridge_decode` flags).
    decodes: u32,

    // -- Option ROM --
    /// True if the ROM image originates from the device's expansion ROM BAR.
    embedded_rom: bool,
    /// Size of the option ROM image in bytes.
    rom_size: u32,
    /// True if all option ROM images have been processed.
    all_op_rom_processed: bool,
    /// True if an EFI driver was found in the option ROM.
    bus_override: bool,
    /// If true, skip option ROM processing for this device.
    ignore_rom: bool,

    // -- PCIe / capability offsets --
    /// True if this device has PCIe capabilities.
    is_pci_exp: bool,
    /// True if ARI (Alternative Routing-ID Interpretation) is enabled.
    is_ari_enabled: bool,
    /// Offset of the PCIe capability structure in config space.
    pci_express_capability_offset: u8,
    /// Offset of the ARI extended capability (0 if not present).
    ari_capability_offset: u32,
    /// Offset of the SR-IOV extended capability (0 if not present).
    sriov_capability_offset: u32,
    /// Offset of the MR-IOV extended capability (0 if not present).
    mriov_capability_offset: u32,

    // -- SR-IOV --
    /// Virtual Function BARs (for SR-IOV capable devices).
    vf_pci_bar: Vec<PciBar>,
    /// System page size for SR-IOV.
    system_page_size: u32,
    /// Initial number of Virtual Functions.
    initial_vfs: u16,
    /// Number of bus numbers reserved for this device's VFs.
    reserved_bus_num: u16,

    // -- Bridge-specific --
    /// Non-standard I/O window alignment for PCI-PCI bridges (default 4K).
    bridge_io_alignment: u16,

    // -- Resizable BAR --
    /// Offset of the Resizable BAR extended capability (0 if not present).
    resizable_bar_offset: u32,
    /// Number of resizable BARs.
    resizable_bar_number: u32,

    // -- PCIe Max Payload --
    /// Maximum payload size setting.
    max_payload_size: u8,

    // -- Hot plug --
    /// Resource padding descriptors for hot-pluggable slots.
    resource_padding_descriptors: *mut core::ffi::c_void,
    /// Padding attributes for hot plug resource reservation.
    padding_attributes: u64,
    /// Bus number range descriptors for PCI root bridges.
    bus_number_ranges: *mut core::ffi::c_void,
}

impl PciIoDevice {
    /// Creates a fully-initialized device from a discovered config header.
    ///
    /// Populates identity, parent link, BARs, and capabilities, then wraps
    /// the result in `Rc<RefCell<...>>` for shared ownership.
    pub fn new(
        config: &dyn PciConfigAccess,
        loc: PciLocation,
        pci: PciType00,
        parent: Option<&PciIoDeviceRef>,
    ) -> PciIoDeviceRef {
        let mut dev = Self {
            bus_number: loc.bus,
            device_number: loc.device,
            function_number: loc.function,
            pci,
            parent: parent.map(Rc::downgrade),
            ..Self::default()
        };

        dev.scan_bars(config);
        dev.detect_capabilities(config);

        Rc::new(RefCell::new(dev))
    }

    /// Returns the PCI location (bus/device/function) of this device.
    pub fn location(&self) -> PciLocation {
        PciLocation::new(self.bus_number, self.device_number, self.function_number)
    }

    /// Returns true if this device is a PCI-PCI bridge (header type 01h).
    pub fn is_bridge(&self) -> bool {
        (self.pci.hdr.header_type & 0x7F) == PCI_HEADER_TYPE_BRIDGE
    }

    // -- Read accessors --

    /// Returns a slice of this device's decoded BARs.
    pub fn bars(&self) -> &[PciBar] {
        &self.pci_bar
    }

    /// Returns a slice of this device's SR-IOV Virtual Function BARs.
    pub fn vf_bars(&self) -> &[PciBar] {
        &self.vf_pci_bar
    }

    /// Returns a slice of this device's child devices.
    pub fn children(&self) -> &[PciIoDeviceRef] {
        &self.child_list
    }

    /// Returns true if this device has a parent bridge.
    pub fn has_parent(&self) -> bool {
        self.parent.is_some()
    }

    /// Returns the bridge decode capability flags.
    pub fn decodes(&self) -> u32 {
        self.decodes
    }

    /// Returns the bridge I/O window alignment.
    pub fn bridge_io_alignment(&self) -> u16 {
        self.bridge_io_alignment
    }

    /// Returns the PCI config header read during enumeration.
    pub fn pci_header(&self) -> &PciType00 {
        &self.pci
    }

    // -- Write accessors --

    /// Adds a child device to this bridge's child list.
    pub fn add_child(&mut self, child: PciIoDeviceRef) {
        self.child_list.push(child);
    }

    /// Clones the child device list (used for iteration while mutating).
    pub fn clone_children(&self) -> Vec<PciIoDeviceRef> {
        self.child_list.clone()
    }

    /// Marks this device as having resources allocated.
    pub fn set_allocated(&mut self) {
        self.allocated = true;
    }

    /// Sets the base address of a BAR after resource programming.
    pub fn set_bar_base_address(&mut self, index: usize, address: u64) {
        if let Some(bar) = self.pci_bar.get_mut(index) {
            bar.base_address = address;
        }
    }

    /// Sets the base address of a VF BAR after resource programming.
    pub fn set_vf_bar_base_address(&mut self, index: usize, address: u64) {
        if let Some(bar) = self.vf_pci_bar.get_mut(index) {
            bar.base_address = address;
        }
    }

    /// Sets the bridge decode capability flags.
    pub fn set_decodes(&mut self, decodes: u32) {
        self.decodes = decodes;
    }

    /// Returns the PCI Root Bridge I/O Protocol pointer for this device.
    pub fn root_bridge_io(&self) -> *mut PciRootBridgeIoProtocol {
        self.pci_root_bridge_io
    }

    /// Returns the currently enabled attributes for this device.
    pub fn attributes(&self) -> u64 {
        self.attributes
    }

    /// Returns the attributes supported by this device.
    pub fn supports(&self) -> u64 {
        self.supports
    }

    /// Sets the currently enabled attributes.
    pub fn set_attributes(&mut self, attributes: u64) {
        self.attributes = attributes;
    }

    // -- BAR scanning (private) --

    fn parse_bar(&self, config: &dyn PciConfigAccess, offset: u32) -> Result<Option<PciBar>, InvalidBarError> {
        let loc = self.location();
        let Some((sizing_mask, saved)) = config.probe_bar(loc, offset) else {
            return Ok(None);
        };

        if (sizing_mask & BAR_BIT_IO_SPACE) != 0 {
            return PciBar::from_io(sizing_mask, saved, offset).map(Some);
        }

        let prefetchable = (sizing_mask & BAR_BIT_PREFETCHABLE) != 0;

        match sizing_mask & BAR_MEM_TYPE_MASK {
            BAR_MEM_TYPE_32 => PciBar::from_mem32(sizing_mask, saved, prefetchable, offset).map(Some),
            BAR_MEM_TYPE_64 => {
                let (upper_sizing, upper_saved) =
                    config.probe_bar(loc, offset + BAR_REGISTER_SIZE).unwrap_or((0xFFFF_FFFF, 0));
                PciBar::from_mem64(sizing_mask, saved, upper_sizing, upper_saved, prefetchable, offset).map(Some)
            }
            _ => Err(InvalidBarError { offset, sizing_mask }),
        }
    }

    /// Probes and populates the BAR list for this device.
    pub fn scan_bars(&mut self, config: &dyn PciConfigAccess) {
        let last_offset = if self.is_bridge() { PCI_BAR1_OFFSET } else { PCI_BAR5_OFFSET };
        let mut bars = Vec::new();
        let mut offset = PCI_BAR0_OFFSET;

        while offset <= last_offset {
            match self.parse_bar(config, offset) {
                Ok(Some(bar)) => {
                    offset = bar.next_offset();
                    bars.push(bar);
                }
                Ok(None) => {
                    offset += BAR_REGISTER_SIZE;
                }
                Err(e) => {
                    log::warn!("scan_bars: failed to parse BAR at offset {:#x}: {:?}", offset, e);
                    offset += BAR_REGISTER_SIZE;
                }
            }
        }

        self.pci_bar = bars;
    }

    // -- Capability walking (private) --

    fn has_capability_list(&self, config: &dyn PciConfigAccess) -> bool {
        let status = config.read_config_u16(self.location(), PCI_STATUS_OFFSET);
        (status & PCI_STATUS_CAPABILITIES_LIST) != 0
    }

    fn locate_capability(&self, config: &dyn PciConfigAccess, cap_id: u8) -> Option<u8> {
        if !self.has_capability_list(config) {
            return None;
        }

        let loc = self.location();
        let mut cap_ptr = config.read_config_u8(loc, PCI_CAPABILITY_POINTER_OFFSET);

        while cap_ptr >= 0x40 && (cap_ptr & 0x03) == 0x00 {
            let entry = config.read_config_u16(loc, cap_ptr as u32);

            let entry_id = (entry & 0xFF) as u8;
            if entry_id == cap_id {
                return Some(cap_ptr);
            }

            let next = (entry >> 8) as u8;
            if next == cap_ptr {
                break;
            }
            cap_ptr = next;
        }

        None
    }

    fn locate_extended_capability(&self, config: &dyn PciConfigAccess, cap_id: u16) -> Option<u32> {
        let loc = self.location();
        let mut cap_ptr = PCIE_CAPABILITY_BASE_OFFSET;

        while cap_ptr != 0 {
            cap_ptr &= 0xFFC;

            let entry = config.read_config_u32(loc, cap_ptr);

            if entry == 0xFFFF_FFFF {
                break;
            }

            let entry_id = (entry & 0xFFFF) as u16;
            if entry_id == cap_id {
                return Some(cap_ptr);
            }

            cap_ptr = (entry >> 20) & 0xFFF;
        }

        None
    }

    /// Detects PCIe and extended capabilities, populating the
    /// corresponding offset fields.
    fn detect_capabilities(&mut self, config: &dyn PciConfigAccess) {
        if let Some(offset) = self.locate_capability(config, CAP_ID_PCIEXP) {
            self.is_pci_exp = true;
            self.pci_express_capability_offset = offset;

            if let Some(ari) = self.locate_extended_capability(config, EXCAP_ID_ARI) {
                self.ari_capability_offset = ari;
            }
            if let Some(sriov) = self.locate_extended_capability(config, EXCAP_ID_SRIOV) {
                self.sriov_capability_offset = sriov;
            }
            if let Some(mriov) = self.locate_extended_capability(config, EXCAP_ID_MRIOV) {
                self.mriov_capability_offset = mriov;
            }
            if let Some(rebar) = self.locate_extended_capability(config, EXCAP_ID_REBAR) {
                self.resizable_bar_offset = rebar;
            }
        }
    }
}

impl Default for PciIoDevice {
    fn default() -> Self {
        Self {
            handle: core::ptr::null_mut(),
            bus_number: 0,
            device_number: 0,
            function_number: 0,
            pci: PciType00::default(),
            device_path: core::ptr::null_mut(),
            pci_root_bridge_io: core::ptr::null_mut(),
            pci_bar: Vec::new(),
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
            vf_pci_bar: Vec::new(),
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

// Test-only setters for fields that are only written in test code.
#[cfg(test)]
impl PciIoDevice {
    /// Sets the BAR list (test only).
    pub fn set_pci_bar(&mut self, bars: Vec<PciBar>) {
        self.pci_bar = bars;
    }

    /// Creates a default device wrapped in `Rc<RefCell<...>>` (test only).
    pub fn default_ref() -> PciIoDeviceRef {
        Rc::new(RefCell::new(PciIoDevice::default()))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_pci_io_device_default() {
        let dev = PciIoDevice::default();
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
