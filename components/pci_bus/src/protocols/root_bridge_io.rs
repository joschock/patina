//! PCI Root Bridge I/O Protocol FFI definitions.
//!
//! Defines the `#[repr(C)]` struct matching `EFI_PCI_ROOT_BRIDGE_IO_PROTOCOL`
//! from the UEFI specification. This protocol is consumed by the PCI bus driver
//! to perform PCI configuration, memory, and I/O operations on a PCI root bridge.
//!
//! Reference: UEFI Specification 2.10, Section 14.2

use core::ffi::c_void;

use patina::{BinaryGuid, uefi_protocol::ProtocolInterface};
use r_efi::efi;

/// Width values for PCI Root Bridge I/O operations.
///
/// Matches `EFI_PCI_ROOT_BRIDGE_IO_PROTOCOL_WIDTH` from the UEFI spec.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Width {
    /// 8-bit operation.
    Uint8 = 0,
    /// 16-bit operation.
    Uint16,
    /// 32-bit operation.
    Uint32,
    /// 64-bit operation.
    Uint64,
    /// 8-bit FIFO operation (address not incremented).
    FifoUint8,
    /// 16-bit FIFO operation.
    FifoUint16,
    /// 32-bit FIFO operation.
    FifoUint32,
    /// 64-bit FIFO operation.
    FifoUint64,
    /// 8-bit fill operation (data not incremented).
    FillUint8,
    /// 16-bit fill operation.
    FillUint16,
    /// 32-bit fill operation.
    FillUint32,
    /// 64-bit fill operation.
    FillUint64,
    /// Sentinel value.
    Maximum,
}

/// DMA operation types for Map/Unmap.
///
/// Matches `EFI_PCI_ROOT_BRIDGE_IO_PROTOCOL_OPERATION` from the UEFI spec.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operation {
    /// Read from system memory by a 32-bit bus master.
    BusMasterRead = 0,
    /// Write to system memory by a 32-bit bus master.
    BusMasterWrite,
    /// Common buffer access by a 32-bit bus master.
    BusMasterCommonBuffer,
    /// Read from system memory by a 64-bit bus master.
    BusMasterRead64,
    /// Write to system memory by a 64-bit bus master.
    BusMasterWrite64,
    /// Common buffer access by a 64-bit bus master.
    BusMasterCommonBuffer64,
    /// Sentinel value.
    Maximum,
}

/// PCI address for Root Bridge I/O Pci.Read/Pci.Write operations.
///
/// Matches `EFI_PCI_ROOT_BRIDGE_IO_PROTOCOL_PCI_ADDRESS`.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct PciAddress {
    /// Register number (bits 7:0 of config offset).
    pub register: u8,
    /// Function number (0-7).
    pub function: u8,
    /// Device number (0-31).
    pub device: u8,
    /// Bus number (0-255).
    pub bus: u8,
    /// Extended register number (bits 11:8 of config offset, 0 for standard space).
    pub extended_register: u32,
}

/// Function pointer type for PollMem/PollIo operations.
pub type PollIoMem = unsafe extern "efiapi" fn(
    this: *mut PciRootBridgeIoProtocol,
    width: Width,
    address: u64,
    mask: u64,
    value: u64,
    delay: u64,
    result: *mut u64,
) -> efi::Status;

/// Function pointer type for Mem/Io/Pci Read/Write operations.
pub type IoMem = unsafe extern "efiapi" fn(
    this: *mut PciRootBridgeIoProtocol,
    width: Width,
    address: u64,
    count: usize,
    buffer: *mut c_void,
) -> efi::Status;

/// Paired Read/Write function pointers for a single address space.
///
/// Matches `EFI_PCI_ROOT_BRIDGE_IO_PROTOCOL_ACCESS`.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Access {
    /// Read operation.
    pub read: IoMem,
    /// Write operation.
    pub write: IoMem,
}

/// Function pointer type for CopyMem.
pub type CopyMem = unsafe extern "efiapi" fn(
    this: *mut PciRootBridgeIoProtocol,
    width: Width,
    dest_address: u64,
    src_address: u64,
    count: usize,
) -> efi::Status;

/// Function pointer type for Map.
pub type Map = unsafe extern "efiapi" fn(
    this: *mut PciRootBridgeIoProtocol,
    operation: Operation,
    host_address: *mut c_void,
    number_of_bytes: *mut usize,
    device_address: *mut efi::PhysicalAddress,
    mapping: *mut *mut c_void,
) -> efi::Status;

/// Function pointer type for Unmap.
pub type Unmap = unsafe extern "efiapi" fn(
    this: *mut PciRootBridgeIoProtocol,
    mapping: *mut c_void,
) -> efi::Status;

/// Function pointer type for AllocateBuffer.
pub type AllocateBuffer = unsafe extern "efiapi" fn(
    this: *mut PciRootBridgeIoProtocol,
    alloc_type: efi::AllocateType,
    memory_type: efi::MemoryType,
    pages: usize,
    host_address: *mut *mut c_void,
    attributes: u64,
) -> efi::Status;

/// Function pointer type for FreeBuffer.
pub type FreeBuffer = unsafe extern "efiapi" fn(
    this: *mut PciRootBridgeIoProtocol,
    pages: usize,
    host_address: *mut c_void,
) -> efi::Status;

/// Function pointer type for Flush.
pub type Flush =
    unsafe extern "efiapi" fn(this: *mut PciRootBridgeIoProtocol) -> efi::Status;

/// Function pointer type for GetAttributes.
pub type GetAttributes = unsafe extern "efiapi" fn(
    this: *mut PciRootBridgeIoProtocol,
    supports: *mut u64,
    attributes: *mut u64,
) -> efi::Status;

/// Function pointer type for SetAttributes.
pub type SetAttributes = unsafe extern "efiapi" fn(
    this: *mut PciRootBridgeIoProtocol,
    attributes: u64,
    resource_base: *mut u64,
    resource_length: *mut u64,
) -> efi::Status;

/// Function pointer type for Configuration.
pub type Configuration = unsafe extern "efiapi" fn(
    this: *mut PciRootBridgeIoProtocol,
    resources: *mut *mut c_void,
) -> efi::Status;

/// PCI Root Bridge I/O Protocol.
///
/// Matches `EFI_PCI_ROOT_BRIDGE_IO_PROTOCOL` from the UEFI specification.
/// Provides Memory, I/O, PCI configuration, and DMA interfaces for accessing
/// PCI controllers behind a PCI Root Bridge Controller.
#[repr(C)]
pub struct PciRootBridgeIoProtocol {
    /// Handle of the PCI Host Bridge that owns this root bridge.
    pub parent_handle: efi::Handle,
    /// Poll memory-mapped I/O address.
    pub poll_mem: PollIoMem,
    /// Poll I/O port address.
    pub poll_io: PollIoMem,
    /// Memory-mapped I/O read/write.
    pub mem: Access,
    /// I/O port read/write.
    pub io: Access,
    /// PCI configuration space read/write.
    pub pci: Access,
    /// Copy memory between MMIO regions.
    pub copy_mem: CopyMem,
    /// Map system memory for DMA.
    pub map: Map,
    /// Unmap DMA mapping.
    pub unmap: Unmap,
    /// Allocate DMA-compatible buffer.
    pub allocate_buffer: AllocateBuffer,
    /// Free DMA buffer.
    pub free_buffer: FreeBuffer,
    /// Flush posted writes.
    pub flush: Flush,
    /// Get supported and current attributes.
    pub get_attributes: GetAttributes,
    /// Set attributes for a resource range.
    pub set_attributes: SetAttributes,
    /// Get current resource configuration.
    pub configuration: Configuration,
    /// PCI segment number.
    pub segment_number: u32,
}

// SAFETY: The struct layout matches the UEFI spec's EFI_PCI_ROOT_BRIDGE_IO_PROTOCOL
// and the GUID is the standard protocol GUID from the specification.
unsafe impl ProtocolInterface for PciRootBridgeIoProtocol {
    const PROTOCOL_GUID: efi::Guid =
        *BinaryGuid::from_string("2f707ebb-4a1a-11d4-9a38-0090273fc14d").as_efi_guid();
}

// PCI Root Bridge I/O Protocol attribute constants.

/// ISA motherboard I/O range attribute.
pub const PCI_ATTRIBUTE_ISA_MOTHERBOARD_IO: u64 = 0x0001;
/// ISA I/O range attribute.
pub const PCI_ATTRIBUTE_ISA_IO: u64 = 0x0002;
/// VGA palette I/O range attribute.
pub const PCI_ATTRIBUTE_VGA_PALETTE_IO: u64 = 0x0004;
/// VGA memory range attribute.
pub const PCI_ATTRIBUTE_VGA_MEMORY: u64 = 0x0008;
/// VGA I/O range attribute.
pub const PCI_ATTRIBUTE_VGA_IO: u64 = 0x0010;
/// IDE primary I/O range attribute.
pub const PCI_ATTRIBUTE_IDE_PRIMARY_IO: u64 = 0x0020;
/// IDE secondary I/O range attribute.
pub const PCI_ATTRIBUTE_IDE_SECONDARY_IO: u64 = 0x0040;
/// Memory write-combine attribute.
pub const PCI_ATTRIBUTE_MEMORY_WRITE_COMBINE: u64 = 0x0080;
/// Memory cached attribute.
pub const PCI_ATTRIBUTE_MEMORY_CACHED: u64 = 0x0800;
/// Memory disable attribute.
pub const PCI_ATTRIBUTE_MEMORY_DISABLE: u64 = 0x1000;
/// Dual address cycle (64-bit DMA) attribute.
pub const PCI_ATTRIBUTE_DUAL_ADDRESS_CYCLE: u64 = 0x8000;
/// ISA I/O 16-bit decode attribute.
pub const PCI_ATTRIBUTE_ISA_IO_16: u64 = 0x10000;
/// VGA palette I/O 16-bit decode attribute.
pub const PCI_ATTRIBUTE_VGA_PALETTE_IO_16: u64 = 0x20000;
/// VGA I/O 16-bit decode attribute.
pub const PCI_ATTRIBUTE_VGA_IO_16: u64 = 0x40000;

#[cfg(test)]
mod test {
    use super::*;
    use core::mem;

    #[test]
    fn test_root_bridge_io_protocol_guid() {
        let guid = PciRootBridgeIoProtocol::PROTOCOL_GUID;
        // EFI_PCI_ROOT_BRIDGE_IO_PROTOCOL_GUID = {0x2f707ebb, 0x4a1a, 0x11d4, ...}
        assert_eq!(guid.as_fields(), (0x2f707ebb, 0x4a1a, 0x11d4, 0x9a, 0x38, &[0x00, 0x90, 0x27, 0x3f, 0xc1, 0x4d]));
    }

    #[test]
    fn test_width_enum_values() {
        assert_eq!(Width::Uint8 as u32, 0);
        assert_eq!(Width::Uint16 as u32, 1);
        assert_eq!(Width::Uint32 as u32, 2);
        assert_eq!(Width::Uint64 as u32, 3);
        assert_eq!(Width::FifoUint8 as u32, 4);
        assert_eq!(Width::Maximum as u32, 12);
    }

    #[test]
    fn test_operation_enum_values() {
        assert_eq!(Operation::BusMasterRead as u32, 0);
        assert_eq!(Operation::BusMasterCommonBuffer64 as u32, 5);
        assert_eq!(Operation::Maximum as u32, 6);
    }

    #[test]
    fn test_pci_address_layout() {
        assert_eq!(mem::size_of::<PciAddress>(), 8);
    }
}
