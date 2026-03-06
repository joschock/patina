//! PCI I/O Protocol implementation.
//!
//! Provides [`PciIoInstance`], a `#[repr(C)]` wrapper around the r_efi PCI I/O
//! Protocol function pointer table. Each discovered PCI device gets its own
//! instance installed on a UEFI handle via `install_protocol_interface`.
//!
//! Context recovery: `PciIoInstance` places the protocol struct as its first
//! field, so a `*mut r_efi::protocols::pci_io::Protocol` received in any
//! callback can be cast directly to `*mut PciIoInstance` to recover the
//! device context.

use core::ffi::c_void;

use r_efi::{efi, protocols::pci_io as pci_io_proto};

use crate::{
    pci_device::{
        bar::PciBarType,
        device::{PciIoDevice, PciIoDeviceRef},
        encode_pci_address,
    },
    protocols::root_bridge_io::{Operation as RbiOp, PciRootBridgeIoProtocol, Width},
};

/// Per-device PCI I/O Protocol instance.
///
/// # Layout
///
/// The `protocol` field **must** be first so that a pointer to
/// `pci_io_proto::Protocol` (as handed to UEFI callers) is also a valid
/// pointer to `PciIoInstance`. This enables zero-cost context recovery in
/// every `extern "efiapi"` callback.
#[repr(C)]
pub struct PciIoInstance {
    /// r_efi function pointer table exposed to UEFI consumers.
    protocol: pci_io_proto::Protocol,
    /// Shared reference to the device this protocol serves.
    device: PciIoDeviceRef,
}

impl PciIoInstance {
    /// Creates a new PCI I/O Protocol instance for the given device.
    pub fn new(device: PciIoDeviceRef) -> Self {
        Self {
            protocol: pci_io_proto::Protocol {
                poll_mem: pci_io_poll_mem,
                poll_io: pci_io_poll_io,
                mem: pci_io_proto::Access { read: pci_io_mem_read, write: pci_io_mem_write },
                io: pci_io_proto::Access { read: pci_io_io_read, write: pci_io_io_write },
                pci: pci_io_proto::ConfigAccess { read: pci_io_config_read, write: pci_io_config_write },
                copy_mem: pci_io_copy_mem,
                map: pci_io_map,
                unmap: pci_io_unmap,
                allocate_buffer: pci_io_allocate_buffer,
                free_buffer: pci_io_free_buffer,
                flush: pci_io_flush,
                get_location: pci_io_get_location,
                attributes: pci_io_attributes,
                get_bar_attributes: pci_io_get_bar_attributes,
                set_bar_attributes: pci_io_set_bar_attributes,
                rom_size: 0,
                rom_image: core::ptr::null_mut(),
            },
            device,
        }
    }

    /// Recovers a `&PciIoInstance` from a raw protocol pointer.
    ///
    /// # Safety
    ///
    /// `proto` must point to the `protocol` field of a valid `PciIoInstance`.
    /// This is guaranteed when the pointer comes from a UEFI callback whose
    /// protocol was installed via [`PciIoInstance::new`].
    unsafe fn from_proto(proto: *mut pci_io_proto::Protocol) -> Option<&'static Self> {
        // SAFETY: caller guarantees proto points to the protocol field of a valid PciIoInstance.
        unsafe { (proto as *const Self).as_ref() }
    }

    /// Returns a reference to the underlying device.
    fn device(&self) -> core::cell::Ref<'_, PciIoDevice> {
        self.device.borrow()
    }

    /// Returns the Root Bridge I/O Protocol pointer from the device.
    fn root_bridge_io(&self) -> *mut PciRootBridgeIoProtocol {
        self.device.borrow().root_bridge_io()
    }
}

// ---------------------------------------------------------------------------
// Private helpers for PCI I/O Protocol functions.
// ---------------------------------------------------------------------------

/// Maximum valid PCI configuration space offset (4K for PCIe extended config).
const PCI_CONFIG_SPACE_SIZE: u32 = 0x1000;

/// Validates a BAR-relative access and returns the absolute address.
///
/// Checks that `bar_index` is valid, the BAR is the correct type (memory vs IO),
/// and the access range `[offset, offset + size*count)` fits within the BAR.
/// Returns the absolute address on success, or an error status.
fn validate_bar_access(
    instance: &PciIoInstance,
    bar_index: u8,
    offset: u64,
    count: usize,
    width: pci_io_proto::Width,
    expect_memory: bool,
) -> Result<u64, efi::Status> {
    if bar_index == pci_io_proto::PASS_THROUGH_BAR {
        return Ok(offset);
    }

    let dev = instance.device();
    let bars = dev.bars();
    let bar = bars.get(bar_index as usize).ok_or(efi::Status::UNSUPPORTED)?;

    let is_memory = matches!(
        bar.bar_type,
        PciBarType::Mem32 | PciBarType::PMem32 | PciBarType::Mem64 | PciBarType::PMem64 | PciBarType::Mem
    );

    if expect_memory != is_memory {
        return Err(efi::Status::UNSUPPORTED);
    }

    let byte_width = 1u64 << (width & 0x03);
    let access_size = byte_width.saturating_mul(count as u64);
    let end = offset.saturating_add(access_size);

    if end > bar.length {
        return Err(efi::Status::INVALID_PARAMETER);
    }

    Ok(bar.base_address.saturating_add(offset))
}

/// Converts a PCI I/O width constant to the Root Bridge I/O Width enum for
/// memory/IO operations (supports standard, FIFO, and Fill widths).
fn pci_io_width_to_rb_io_width(width: pci_io_proto::Width) -> Option<Width> {
    match width {
        pci_io_proto::WIDTH_UINT8 => Some(Width::Uint8),
        pci_io_proto::WIDTH_UINT16 => Some(Width::Uint16),
        pci_io_proto::WIDTH_UINT32 => Some(Width::Uint32),
        pci_io_proto::WIDTH_UINT64 => Some(Width::Uint64),
        pci_io_proto::WIDTH_FIFO_UINT8 => Some(Width::FifoUint8),
        pci_io_proto::WIDTH_FIFO_UINT16 => Some(Width::FifoUint16),
        pci_io_proto::WIDTH_FIFO_UINT32 => Some(Width::FifoUint32),
        pci_io_proto::WIDTH_FIFO_UINT64 => Some(Width::FifoUint64),
        pci_io_proto::WIDTH_FILL_UINT8 => Some(Width::FillUint8),
        pci_io_proto::WIDTH_FILL_UINT16 => Some(Width::FillUint16),
        pci_io_proto::WIDTH_FILL_UINT32 => Some(Width::FillUint32),
        pci_io_proto::WIDTH_FILL_UINT64 => Some(Width::FillUint64),
        _ => {
            log::warn!("pci_io_width_to_rbi_width: unsupported width {width:#x}");
            debug_assert!(false, "unexpected PCI I/O width: {width:#x}");
            None
        }
    }
}

/// Converts a PCI I/O width constant to the Root Bridge I/O Width enum.
/// Only standard widths (Uint8/16/32) are valid for PCI config space.
fn config_width_to_rbi_width(width: pci_io_proto::Width) -> Option<Width> {
    match width {
        pci_io_proto::WIDTH_UINT8 => Some(Width::Uint8),
        pci_io_proto::WIDTH_UINT16 => Some(Width::Uint16),
        pci_io_proto::WIDTH_UINT32 => Some(Width::Uint32),
        _ => {
            log::warn!("config_width_to_rbi_width: unsupported config width {width:#x}");
            debug_assert!(false, "unexpected PCI config width: {width:#x}");
            None
        }
    }
}

/// Returns the byte size for a given PCI I/O width constant.
fn width_byte_size(width: pci_io_proto::Width) -> u32 {
    1u32 << (width & 0x03)
}

/// Maps a PCI I/O DMA operation to the Root Bridge I/O operation.
/// Uses 64-bit variants if the device supports dual address cycle (DAC).
fn map_dma_operation(
    operation: pci_io_proto::Operation,
    supports_dac: bool,
) -> Option<crate::protocols::root_bridge_io::Operation> {
    match (operation, supports_dac) {
        (pci_io_proto::OPERATION_BUS_MASTER_READ, false) => Some(RbiOp::BusMasterRead),
        (pci_io_proto::OPERATION_BUS_MASTER_READ, true) => Some(RbiOp::BusMasterRead64),
        (pci_io_proto::OPERATION_BUS_MASTER_WRITE, false) => Some(RbiOp::BusMasterWrite),
        (pci_io_proto::OPERATION_BUS_MASTER_WRITE, true) => Some(RbiOp::BusMasterWrite64),
        (pci_io_proto::OPERATION_BUS_MASTER_COMMON_BUFFER, false) => Some(RbiOp::BusMasterCommonBuffer),
        (pci_io_proto::OPERATION_BUS_MASTER_COMMON_BUFFER, true) => Some(RbiOp::BusMasterCommonBuffer64),
        _ => {
            log::warn!("map_dma_operation: unsupported DMA operation {operation:#x}");
            debug_assert!(false, "unexpected DMA operation: {operation:#x}");
            None
        }
    }
}

// ---------------------------------------------------------------------------
// PCI I/O Protocol function implementations.
// ---------------------------------------------------------------------------

/// Polls a memory-mapped BAR register until a condition is met or a timeout expires.
///
/// Delegates to `RootBridgeIo.PollMem` after translating the BAR-relative offset
/// to an absolute address.
extern "efiapi" fn pci_io_poll_mem(
    proto: *mut pci_io_proto::Protocol,
    width: pci_io_proto::Width,
    bar_index: u8,
    offset: u64,
    mask: u64,
    value: u64,
    delay: u64,
    result: *mut u64,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };
    if result.is_null() {
        return efi::Status::INVALID_PARAMETER;
    }

    let addr = match validate_bar_access(instance, bar_index, offset, 1, width, true) {
        Ok(address) => address,
        Err(status) => return status,
    };

    let Some(rbi_width) = pci_io_width_to_rb_io_width(width) else {
        return efi::Status::INVALID_PARAMETER;
    };

    // SAFETY: rbi_proto and result are valid; delegate polling to Root Bridge I/O.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        (rbi_proto.poll_mem)(instance.root_bridge_io(), rbi_width, addr, mask, value, delay, result)
    }
}

/// Polls an I/O BAR register until a condition is met or a timeout expires.
///
/// Delegates to `RootBridgeIo.PollIo` after translating the BAR-relative offset
/// to an absolute address.
extern "efiapi" fn pci_io_poll_io(
    proto: *mut pci_io_proto::Protocol,
    width: pci_io_proto::Width,
    bar_index: u8,
    offset: u64,
    mask: u64,
    value: u64,
    delay: u64,
    result: *mut u64,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };
    if result.is_null() {
        return efi::Status::INVALID_PARAMETER;
    }

    let addr = match validate_bar_access(instance, bar_index, offset, 1, width, false) {
        Ok(address) => address,
        Err(status) => return status,
    };

    let Some(rbi_width) = pci_io_width_to_rb_io_width(width) else {
        return efi::Status::INVALID_PARAMETER;
    };

    // SAFETY: rbi_proto and result are valid; delegate polling to Root Bridge I/O.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        (rbi_proto.poll_io)(instance.root_bridge_io(), rbi_width, addr, mask, value, delay, result)
    }
}

/// Reads from a memory-mapped BAR region.
///
/// Validates the BAR type and bounds, then delegates to `RootBridgeIo.Mem.Read`.
extern "efiapi" fn pci_io_mem_read(
    proto: *mut pci_io_proto::Protocol,
    width: pci_io_proto::Width,
    bar_index: u8,
    offset: u64,
    count: usize,
    buffer: *mut c_void,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };
    if buffer.is_null() {
        return efi::Status::INVALID_PARAMETER;
    }
    let Some(rbi_width) = pci_io_width_to_rb_io_width(width) else {
        return efi::Status::INVALID_PARAMETER;
    };

    let addr = match validate_bar_access(instance, bar_index, offset, count, width, true) {
        Ok(address) => address,
        Err(status) => return status,
    };

    // SAFETY: rbi is valid per construction invariant; buffer validated above.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        (rbi_proto.mem.read)(instance.root_bridge_io(), rbi_width, addr, count, buffer)
    }
}

/// Writes to a memory-mapped BAR region.
///
/// Validates the BAR type and bounds, then delegates to `RootBridgeIo.Mem.Write`.
extern "efiapi" fn pci_io_mem_write(
    proto: *mut pci_io_proto::Protocol,
    width: pci_io_proto::Width,
    bar_index: u8,
    offset: u64,
    count: usize,
    buffer: *mut c_void,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };
    if buffer.is_null() {
        return efi::Status::INVALID_PARAMETER;
    }
    let Some(rbi_width) = pci_io_width_to_rb_io_width(width) else {
        return efi::Status::INVALID_PARAMETER;
    };

    let addr = match validate_bar_access(instance, bar_index, offset, count, width, true) {
        Ok(address) => address,
        Err(status) => return status,
    };

    // SAFETY: rbi is valid per construction invariant; buffer validated above.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        (rbi_proto.mem.write)(instance.root_bridge_io(), rbi_width, addr, count, buffer)
    }
}

/// Reads from an I/O BAR region.
///
/// Validates the BAR type and bounds, then delegates to `RootBridgeIo.Io.Read`.
extern "efiapi" fn pci_io_io_read(
    proto: *mut pci_io_proto::Protocol,
    width: pci_io_proto::Width,
    bar_index: u8,
    offset: u64,
    count: usize,
    buffer: *mut c_void,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };
    if buffer.is_null() {
        return efi::Status::INVALID_PARAMETER;
    }
    let Some(rbi_width) = pci_io_width_to_rb_io_width(width) else {
        return efi::Status::INVALID_PARAMETER;
    };

    let addr = match validate_bar_access(instance, bar_index, offset, count, width, false) {
        Ok(address) => address,
        Err(status) => return status,
    };

    // SAFETY: rbi is valid per construction invariant; buffer validated above.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        (rbi_proto.io.read)(instance.root_bridge_io(), rbi_width, addr, count, buffer)
    }
}

/// Writes to an I/O BAR region.
///
/// Validates the BAR type and bounds, then delegates to `RootBridgeIo.Io.Write`.
extern "efiapi" fn pci_io_io_write(
    proto: *mut pci_io_proto::Protocol,
    width: pci_io_proto::Width,
    bar_index: u8,
    offset: u64,
    count: usize,
    buffer: *mut c_void,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };
    if buffer.is_null() {
        return efi::Status::INVALID_PARAMETER;
    }
    let Some(rbi_width) = pci_io_width_to_rb_io_width(width) else {
        return efi::Status::INVALID_PARAMETER;
    };

    let addr = match validate_bar_access(instance, bar_index, offset, count, width, false) {
        Ok(address) => address,
        Err(status) => return status,
    };

    // SAFETY: rbi is valid per construction invariant; buffer validated above.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        (rbi_proto.io.write)(instance.root_bridge_io(), rbi_width, addr, count, buffer)
    }
}

/// Reads from PCI configuration space.
///
/// Validates that the width is a standard config width (Uint8/16/32) and the access
/// falls within the 4K PCIe extended configuration space. Encodes the device
/// location into an RBI PCI address and delegates to `RootBridgeIo.Pci.Read`.
extern "efiapi" fn pci_io_config_read(
    proto: *mut pci_io_proto::Protocol,
    width: pci_io_proto::Width,
    offset: u32,
    count: usize,
    buffer: *mut c_void,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };
    if buffer.is_null() {
        return efi::Status::INVALID_PARAMETER;
    }
    let Some(rbi_width) = config_width_to_rbi_width(width) else {
        return efi::Status::INVALID_PARAMETER;
    };

    let size = width_byte_size(width);
    let end = offset.saturating_add(size.saturating_mul(count as u32));
    if end > PCI_CONFIG_SPACE_SIZE {
        return efi::Status::UNSUPPORTED;
    }

    let dev = instance.device();
    let loc = dev.location();
    let addr = encode_pci_address(loc, offset);
    let rbi = instance.root_bridge_io();

    // SAFETY: rbi is valid per construction invariant; buffer validated above.
    unsafe {
        let rbi_proto = &*rbi;
        (rbi_proto.pci.read)(rbi, rbi_width, addr, count, buffer)
    }
}

/// Writes to PCI configuration space.
///
/// Validates that the width is a standard config width (Uint8/16/32) and the access
/// falls within the 4K PCIe extended configuration space. Encodes the device
/// location into an RBI PCI address and delegates to `RootBridgeIo.Pci.Write`.
extern "efiapi" fn pci_io_config_write(
    proto: *mut pci_io_proto::Protocol,
    width: pci_io_proto::Width,
    offset: u32,
    count: usize,
    buffer: *mut c_void,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };
    if buffer.is_null() {
        return efi::Status::INVALID_PARAMETER;
    }
    let Some(rbi_width) = config_width_to_rbi_width(width) else {
        return efi::Status::INVALID_PARAMETER;
    };

    let size = width_byte_size(width);
    let end = offset.saturating_add(size.saturating_mul(count as u32));
    if end > PCI_CONFIG_SPACE_SIZE {
        return efi::Status::UNSUPPORTED;
    }

    let dev = instance.device();
    let loc = dev.location();
    let addr = encode_pci_address(loc, offset);
    let rbi = instance.root_bridge_io();

    // SAFETY: rbi is valid per construction invariant; buffer validated above.
    unsafe {
        let rbi_proto = &*rbi;
        (rbi_proto.pci.write)(rbi, rbi_width, addr, count, buffer)
    }
}

/// Copies data between two memory-mapped BAR regions.
///
/// Both source and destination are validated as memory BARs with sufficient
/// range. Delegates to `RootBridgeIo.CopyMem`.
extern "efiapi" fn pci_io_copy_mem(
    proto: *mut pci_io_proto::Protocol,
    width: pci_io_proto::Width,
    dest_bar_index: u8,
    dest_offset: u64,
    src_bar_index: u8,
    src_offset: u64,
    count: usize,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };

    let Some(rbi_width) = pci_io_width_to_rb_io_width(width) else {
        return efi::Status::INVALID_PARAMETER;
    };

    let dest_addr = match validate_bar_access(instance, dest_bar_index, dest_offset, count, width, true) {
        Ok(address) => address,
        Err(status) => return status,
    };
    let src_addr = match validate_bar_access(instance, src_bar_index, src_offset, count, width, true) {
        Ok(address) => address,
        Err(status) => return status,
    };

    // SAFETY: rbi is valid; both addresses validated above.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        (rbi_proto.copy_mem)(instance.root_bridge_io(), rbi_width, dest_addr, src_addr, count)
    }
}

/// Maps a host buffer for DMA access by the PCI device.
///
/// Selects the 64-bit DMA operation variant when the device supports dual
/// address cycle (DAC). Delegates to `RootBridgeIo.Map`.
extern "efiapi" fn pci_io_map(
    proto: *mut pci_io_proto::Protocol,
    operation: pci_io_proto::Operation,
    host_address: *mut c_void,
    number_of_bytes: *mut usize,
    device_address: *mut efi::PhysicalAddress,
    mapping: *mut *mut c_void,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };

    let supports_dac = (instance.device().attributes() & pci_io_proto::ATTRIBUTE_DUAL_ADDRESS_CYCLE) != 0;
    let Some(rbi_op) = map_dma_operation(operation, supports_dac) else {
        return efi::Status::INVALID_PARAMETER;
    };

    // SAFETY: rbi is valid; delegate to Root Bridge I/O Map.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        (rbi_proto.map)(instance.root_bridge_io(), rbi_op, host_address, number_of_bytes, device_address, mapping)
    }
}

/// Unmaps a previously mapped DMA buffer. Delegates to `RootBridgeIo.Unmap`.
extern "efiapi" fn pci_io_unmap(proto: *mut pci_io_proto::Protocol, mapping: *mut c_void) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };

    // SAFETY: rbi is valid; delegate to Root Bridge I/O Unmap.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        (rbi_proto.unmap)(instance.root_bridge_io(), mapping)
    }
}

/// Allocates pages suitable for DMA by the PCI device.
///
/// When the device does not support DAC and the caller requests `ALLOCATE_ANY_PAGES`,
/// the allocation is forced below 4 GB via `ALLOCATE_MAX_ADDRESS`. The DAC attribute
/// bit is stripped before delegating to `RootBridgeIo.AllocateBuffer`.
extern "efiapi" fn pci_io_allocate_buffer(
    proto: *mut pci_io_proto::Protocol,
    alloc_type: efi::AllocateType,
    memory_type: efi::MemoryType,
    pages: usize,
    host_address: *mut *mut c_void,
    attributes: pci_io_proto::Attribute,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };

    let supports_dac = (instance.device().attributes() & pci_io_proto::ATTRIBUTE_DUAL_ADDRESS_CYCLE) != 0;

    // Filter out the DAC attribute — the RBI doesn't understand it.
    let rbi_attributes = attributes & !pci_io_proto::ATTRIBUTE_DUAL_ADDRESS_CYCLE;

    // If device lacks DAC, force allocation below 4GB.
    let effective_type =
        if !supports_dac && alloc_type == efi::ALLOCATE_ANY_PAGES { efi::ALLOCATE_MAX_ADDRESS } else { alloc_type };

    // SAFETY: rbi is valid; delegate to Root Bridge I/O AllocateBuffer.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        (rbi_proto.allocate_buffer)(
            instance.root_bridge_io(),
            effective_type,
            memory_type,
            pages,
            host_address,
            rbi_attributes,
        )
    }
}

/// Frees pages previously allocated with `allocate_buffer`.
/// Delegates to `RootBridgeIo.FreeBuffer`.
extern "efiapi" fn pci_io_free_buffer(
    proto: *mut pci_io_proto::Protocol,
    pages: usize,
    host_address: *mut c_void,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };

    // SAFETY: rbi is valid; delegate to Root Bridge I/O FreeBuffer.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        (rbi_proto.free_buffer)(instance.root_bridge_io(), pages, host_address)
    }
}

/// Flushes all posted PCI write transactions to system memory.
/// Delegates to `RootBridgeIo.Flush`.
extern "efiapi" fn pci_io_flush(proto: *mut pci_io_proto::Protocol) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };

    // SAFETY: rbi is valid; delegate to Root Bridge I/O Flush.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        (rbi_proto.flush)(instance.root_bridge_io())
    }
}

/// Returns the PCI bus location (segment, bus, device, function) of this device.
///
/// The segment number comes from the Root Bridge I/O Protocol; bus/device/function
/// come from the device's stored location.
extern "efiapi" fn pci_io_get_location(
    proto: *mut pci_io_proto::Protocol,
    segment_number: *mut usize,
    bus_number: *mut usize,
    device_number: *mut usize,
    function_number: *mut usize,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };
    if segment_number.is_null() || bus_number.is_null() || device_number.is_null() || function_number.is_null() {
        return efi::Status::INVALID_PARAMETER;
    }

    let dev = instance.device();
    let loc = dev.location();

    // SAFETY: caller-provided pointers validated as non-null above.
    unsafe {
        let rbi_proto = &*instance.root_bridge_io();
        *segment_number = rbi_proto.segment_number as usize;
        *bus_number = loc.bus as usize;
        *device_number = loc.device as usize;
        *function_number = loc.function as usize;
    }

    efi::Status::SUCCESS
}

/// Gets or modifies the device's PCI I/O attributes.
///
/// Supports GET, SET, ENABLE, DISABLE, and SUPPORTED operations per the UEFI spec.
///
/// # Panics
///
/// SET, ENABLE, and DISABLE operations call `borrow_mut()` on the device
/// `RefCell`. A re-entrant call on the same device while a mutable borrow
/// is held will panic.
extern "efiapi" fn pci_io_attributes(
    proto: *mut pci_io_proto::Protocol,
    operation: pci_io_proto::AttributeOperation,
    attributes: pci_io_proto::Attribute,
    result: *mut pci_io_proto::Attribute,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };

    match operation {
        pci_io_proto::ATTRIBUTE_OPERATION_GET => {
            if result.is_null() {
                return efi::Status::INVALID_PARAMETER;
            }
            // SAFETY: result validated as non-null above.
            unsafe { *result = instance.device().attributes() };
            efi::Status::SUCCESS
        }
        pci_io_proto::ATTRIBUTE_OPERATION_SET => {
            instance.device.borrow_mut().set_attributes(attributes);
            efi::Status::SUCCESS
        }
        pci_io_proto::ATTRIBUTE_OPERATION_ENABLE => {
            let mut dev = instance.device.borrow_mut();
            let current = dev.attributes();
            dev.set_attributes(current | attributes);
            efi::Status::SUCCESS
        }
        pci_io_proto::ATTRIBUTE_OPERATION_DISABLE => {
            let mut dev = instance.device.borrow_mut();
            let current = dev.attributes();
            dev.set_attributes(current & !attributes);
            efi::Status::SUCCESS
        }
        pci_io_proto::ATTRIBUTE_OPERATION_SUPPORTED => {
            if result.is_null() {
                return efi::Status::INVALID_PARAMETER;
            }
            // SAFETY: result validated as non-null above.
            unsafe { *result = instance.device().supports() };
            efi::Status::SUCCESS
        }
        _ => efi::Status::INVALID_PARAMETER,
    }
}

/// Returns the supported attributes for a specific BAR.
///
/// The `resources` output (ACPI QWORD address-space descriptor) is not yet
/// implemented — see follow-up task `6f-bar-resource-descriptor`.
extern "efiapi" fn pci_io_get_bar_attributes(
    proto: *mut pci_io_proto::Protocol,
    bar_index: u8,
    supports: *mut pci_io_proto::Attribute,
    _resources: *mut *mut c_void,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };

    let dev = instance.device();
    let bars = dev.bars();
    if (bar_index as usize) >= bars.len() {
        return efi::Status::UNSUPPORTED;
    }

    if !supports.is_null() {
        // SAFETY: supports validated as non-null.
        unsafe { *supports = 0 };
    }

    efi::Status::SUCCESS
}

/// Sets attributes for a specific BAR region.
///
/// Validates inputs but performs no actual attribute changes, matching the
/// C reference `PciIoSetBarAttributes` behavior.
extern "efiapi" fn pci_io_set_bar_attributes(
    proto: *mut pci_io_proto::Protocol,
    _attributes: pci_io_proto::Attribute,
    bar_index: u8,
    offset: *mut u64,
    length: *mut u64,
) -> efi::Status {
    // SAFETY: proto originates from a PciIoInstance installed via install_protocol_interface.
    let Some(instance) = (unsafe { PciIoInstance::from_proto(proto) }) else {
        return efi::Status::INVALID_PARAMETER;
    };
    if offset.is_null() || length.is_null() {
        return efi::Status::INVALID_PARAMETER;
    }

    let dev = instance.device();
    let bars = dev.bars();
    if (bar_index as usize) >= bars.len() {
        return efi::Status::UNSUPPORTED;
    }

    // Matches C reference: validates inputs but performs no actual attribute changes.
    efi::Status::SUCCESS
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::pci_device::device::PciIoDevice;

    #[test]
    fn test_protocol_is_first_field() {
        // Verify that PciIoInstance's protocol field is at offset 0,
        // which is required for safe context recovery.
        assert_eq!(
            core::mem::offset_of!(PciIoInstance, protocol),
            0,
            "protocol must be the first field for context recovery"
        );
    }

    #[test]
    fn test_instance_creation() {
        let device = PciIoDevice::default_ref();
        let instance = PciIoInstance::new(device);
        assert_eq!(instance.protocol.rom_size, 0);
        assert!(instance.protocol.rom_image.is_null());
    }

    #[test]
    fn test_context_recovery_roundtrip() {
        let device = PciIoDevice::default_ref();
        let instance = PciIoInstance::new(device);
        let proto_ptr = &instance.protocol as *const pci_io_proto::Protocol as *mut pci_io_proto::Protocol;

        // SAFETY: proto_ptr points to the protocol field of a valid PciIoInstance.
        let recovered = unsafe { PciIoInstance::from_proto(proto_ptr) }.expect("recovery should succeed");

        assert_eq!(recovered.device.borrow().location(), instance.device.borrow().location());
    }
}
