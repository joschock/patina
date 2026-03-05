//! PCI configuration space header types.
//!
//! Defines `#[repr(C)]` structs matching the PCI Local Bus Specification
//! standard header layouts (Type 00h for endpoints, Type 01h for bridges).

/// Header type value for PCI-PCI bridges (Type 01h).
pub const PCI_HEADER_TYPE_BRIDGE: u8 = 0x01;

/// Header type bit indicating a multi-function device.
pub const PCI_HEADER_TYPE_MULTI_FUNC: u8 = 0x80;

/// Device-independent portion of the PCI configuration space header (first 16 bytes).
///
/// Common to all PCI device types (Type 00h and 01h).
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct PciDeviceIndependentRegion {
    /// Vendor ID.
    pub vendor_id: u16,
    /// Device ID.
    pub device_id: u16,
    /// Command register.
    pub command: u16,
    /// Status register.
    pub status: u16,
    /// Revision ID.
    pub revision_id: u8,
    /// Class code (3 bytes: interface, sub-class, base class).
    pub class_code: [u8; 3],
    /// Cache line size.
    pub cache_line_size: u8,
    /// Latency timer.
    pub latency_timer: u8,
    /// Header type (bit 7 = multi-function).
    pub header_type: u8,
    /// Built-in self test.
    pub bist: u8,
}

/// Type 00h device-specific portion of PCI configuration space.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct PciDeviceHeaderTypeRegion {
    /// Base address registers.
    pub bar: [u32; 6],
    /// CIS pointer.
    pub cis_ptr: u32,
    /// Subsystem vendor ID.
    pub subsystem_vendor_id: u16,
    /// Subsystem ID.
    pub subsystem_id: u16,
    /// Expansion ROM base address.
    pub expansion_rom_bar: u32,
    /// Capability pointer.
    pub capability_ptr: u8,
    /// Reserved.
    pub reserved1: [u8; 3],
    /// Reserved.
    pub reserved2: u32,
    /// Interrupt line.
    pub interrupt_line: u8,
    /// Interrupt pin.
    pub interrupt_pin: u8,
    /// Minimum grant.
    pub min_gnt: u8,
    /// Maximum latency.
    pub max_lat: u8,
}

/// PCI Type 00h (endpoint) configuration space header.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct PciType00 {
    /// Device-independent header (common 16 bytes).
    pub hdr: PciDeviceIndependentRegion,
    /// Type 00h device-specific region.
    pub device: PciDeviceHeaderTypeRegion,
}

/// PCI-PCI Bridge (Type 01h) specific portion of configuration space.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct PciBridgeControlRegion {
    /// Bridge BARs (only 2 for bridges).
    pub bar: [u32; 2],
    /// Primary bus number.
    pub primary_bus: u8,
    /// Secondary bus number.
    pub secondary_bus: u8,
    /// Subordinate bus number.
    pub subordinate_bus: u8,
    /// Secondary latency timer.
    pub secondary_latency_timer: u8,
    /// I/O base (lower 8 bits).
    pub io_base: u8,
    /// I/O limit (lower 8 bits).
    pub io_limit: u8,
    /// Secondary status.
    pub secondary_status: u16,
    /// Memory base.
    pub memory_base: u16,
    /// Memory limit.
    pub memory_limit: u16,
    /// Prefetchable memory base (lower 16 bits).
    pub prefetchable_memory_base: u16,
    /// Prefetchable memory limit (lower 16 bits).
    pub prefetchable_memory_limit: u16,
    /// Prefetchable base upper 32 bits.
    pub prefetchable_base_upper32: u32,
    /// Prefetchable limit upper 32 bits.
    pub prefetchable_limit_upper32: u32,
    /// I/O base upper 16 bits.
    pub io_base_upper16: u16,
    /// I/O limit upper 16 bits.
    pub io_limit_upper16: u16,
    /// Capability pointer.
    pub capability_ptr: u8,
    /// Reserved.
    pub reserved: [u8; 3],
    /// Expansion ROM base address.
    pub expansion_rom_bar: u32,
    /// Interrupt line.
    pub interrupt_line: u8,
    /// Interrupt pin.
    pub interrupt_pin: u8,
    /// Bridge control.
    pub bridge_control: u16,
}

/// PCI Type 01h (PCI-to-PCI bridge) configuration space header.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct PciType01 {
    /// Device-independent header (common 16 bytes).
    pub hdr: PciDeviceIndependentRegion,
    /// Bridge-specific region.
    pub bridge: PciBridgeControlRegion,
}

/// PCI-to-PCI bridge (Type 01h) aperture register offsets in config space.
pub mod ppb_regs {
    /// I/O base (lower 8 bits).
    pub const IO_BASE: u32 = 0x1C;
    /// I/O limit (lower 8 bits).
    pub const IO_LIMIT: u32 = 0x1D;
    /// Non-prefetchable memory base (upper 16 bits of 32-bit address).
    pub const MEM_BASE: u32 = 0x20;
    /// Non-prefetchable memory limit (upper 16 bits of 32-bit address).
    pub const MEM_LIMIT: u32 = 0x22;
    /// Prefetchable memory base (upper 16 bits).
    pub const PMEM_BASE: u32 = 0x24;
    /// Prefetchable memory limit (upper 16 bits).
    pub const PMEM_LIMIT: u32 = 0x26;
    /// Prefetchable base upper 32 bits.
    pub const PMEM_BASE_UPPER: u32 = 0x28;
    /// Prefetchable limit upper 32 bits.
    pub const PMEM_LIMIT_UPPER: u32 = 0x2C;
    /// I/O base upper 16 bits.
    pub const IO_BASE_UPPER: u32 = 0x30;
    /// I/O limit upper 16 bits.
    pub const IO_LIMIT_UPPER: u32 = 0x32;
}

#[cfg(test)]
mod test {
    use super::*;
    use core::mem;

    #[test]
    fn test_pci_header_sizes() {
        assert_eq!(mem::size_of::<PciDeviceIndependentRegion>(), 16);
        assert_eq!(mem::size_of::<PciDeviceHeaderTypeRegion>(), 48);
        assert_eq!(mem::size_of::<PciType00>(), 64);
        assert_eq!(mem::size_of::<PciBridgeControlRegion>(), 48);
        assert_eq!(mem::size_of::<PciType01>(), 64);
    }
}
