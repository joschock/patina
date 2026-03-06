//! Safe abstraction over PCI configuration space access.
//!
//! The [`PciConfigAccess`] trait provides safe typed read/write operations
//! for PCI config space, hiding the unsafe FFI calls to the Root Bridge I/O
//! Protocol behind a safe interface. All enumerator code uses this trait
//! instead of raw protocol pointers.

use patina::{
    boot_services::{BootServices, tpl::Tpl},
    tpl_mutex::TplMutex,
};
use r_efi::efi;

use super::pci_config::PciType00;
use crate::protocols::root_bridge_io::{PciRootBridgeIoProtocol, Width};

/// Identifies a specific PCI function by bus/device/function number.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PciLocation {
    pub bus: u8,
    pub device: u8,
    pub function: u8,
}

impl PciLocation {
    pub fn new(bus: u8, device: u8, function: u8) -> Self {
        Self { bus, device, function }
    }
}

/// Safe interface for PCI configuration space read/write operations.
pub trait PciConfigAccess {
    /// Reads an 8-bit value from config space.
    fn read_config_u8(&self, loc: PciLocation, offset: u32) -> u8;

    /// Reads a 16-bit value from config space.
    fn read_config_u16(&self, loc: PciLocation, offset: u32) -> u16;

    /// Reads a 32-bit value from config space.
    fn read_config_u32(&self, loc: PciLocation, offset: u32) -> u32;

    /// Writes a 32-bit value to config space.
    fn write_config_u32(&self, loc: PciLocation, offset: u32, value: u32);

    /// Probes a BAR by writing all-1s, reading back the sizing mask, then
    /// restoring the original value. Returns `None` if the BAR is unimplemented
    /// (sizing mask is zero).
    ///
    /// The default implementation performs the probe without TPL protection,
    /// suitable for test mocks. Real implementations should override this to
    /// raise TPL around the destructive write-read-restore sequence.
    fn probe_bar(&self, loc: PciLocation, offset: u32) -> Option<(u32, u32)> {
        let saved = self.read_config_u32(loc, offset);
        self.write_config_u32(loc, offset, 0xFFFF_FFFF);
        let sizing_mask = self.read_config_u32(loc, offset);
        self.write_config_u32(loc, offset, saved);
        if sizing_mask == 0 { None } else { Some((sizing_mask, saved)) }
    }

    /// Reads a full Type 00h PCI config header (64 bytes).
    ///
    /// Returns `None` if vendor ID is 0xFFFF (device not present).
    fn read_config_header(&self, loc: PciLocation) -> Option<PciType00> {
        let mut pci = PciType00::default();
        let ptr = &mut pci as *mut PciType00 as *mut u32;

        for i in 0..16u32 {
            // SAFETY: ptr is valid for 16 u32 writes (sizeof PciType00 == 64)
            unsafe {
                *ptr.add(i as usize) = self.read_config_u32(loc, i * 4);
            }
        }

        if pci.hdr.vendor_id == 0xFFFF { None } else { Some(pci) }
    }
}

/// Encodes a PCI location and config space offset into the 64-bit address
/// format expected by the Root Bridge I/O Protocol's Pci.Read/Pci.Write.
pub(crate) fn encode_pci_address(loc: PciLocation, offset: u32) -> u64 {
    let mut addr: u64 = 0;
    addr |= (loc.bus as u64) << 24;
    addr |= (loc.device as u64) << 16;
    addr |= (loc.function as u64) << 8;
    if offset < 256 {
        addr |= offset as u64;
    } else {
        addr |= (offset as u64) << 32;
    }
    addr
}

/// Real implementation of [`PciConfigAccess`] backed by a PCI Root Bridge
/// I/O Protocol pointer.
///
/// # Safety
///
/// The caller must ensure the `PciRootBridgeIoProtocol` pointer remains
/// valid for the lifetime of this wrapper.
pub struct RootBridgeIoAccess<B: BootServices> {
    rbi: *mut PciRootBridgeIoProtocol,
    tpl_mutex: TplMutex<(), B>,
}

impl<B: BootServices> RootBridgeIoAccess<B> {
    /// Creates a new wrapper around the given Root Bridge I/O Protocol.
    ///
    /// # Safety
    ///
    /// `rbi` must be a valid pointer for the lifetime of this struct.
    pub unsafe fn new(rbi: *mut PciRootBridgeIoProtocol, boot_services: B) -> Self {
        Self { rbi, tpl_mutex: TplMutex::new(boot_services, Tpl(efi::TPL_HIGH_LEVEL), ()) }
    }

    /// Returns the underlying protocol pointer.
    pub fn protocol(&self) -> *mut PciRootBridgeIoProtocol {
        self.rbi
    }
}

impl<B: BootServices> PciConfigAccess for RootBridgeIoAccess<B> {
    fn read_config_u8(&self, loc: PciLocation, offset: u32) -> u8 {
        let mut value: u8 = 0;
        let addr = encode_pci_address(loc, offset);
        // SAFETY: rbi is valid per construction invariant
        unsafe {
            let proto = &*self.rbi;
            let status =
                (proto.pci.read)(self.rbi, Width::Uint8, addr, 1, &mut value as *mut u8 as *mut core::ffi::c_void);
            if status.is_error() {
                log::warn!("PCI config read_u8 failed at {:?} offset {:#x}: {:#x}", loc, offset, status.as_usize());
            }
        }
        value
    }

    fn read_config_u16(&self, loc: PciLocation, offset: u32) -> u16 {
        let mut value: u16 = 0;
        let addr = encode_pci_address(loc, offset);
        // SAFETY: rbi is valid per construction invariant
        unsafe {
            let proto = &*self.rbi;
            let status =
                (proto.pci.read)(self.rbi, Width::Uint16, addr, 1, &mut value as *mut u16 as *mut core::ffi::c_void);
            if status.is_error() {
                log::warn!("PCI config read_u16 failed at {:?} offset {:#x}: {:#x}", loc, offset, status.as_usize());
            }
        }
        value
    }

    fn read_config_u32(&self, loc: PciLocation, offset: u32) -> u32 {
        let mut value: u32 = 0;
        let addr = encode_pci_address(loc, offset);
        // SAFETY: rbi is valid per construction invariant
        unsafe {
            let proto = &*self.rbi;
            let status =
                (proto.pci.read)(self.rbi, Width::Uint32, addr, 1, &mut value as *mut u32 as *mut core::ffi::c_void);
            if status.is_error() {
                log::warn!("PCI config read_u32 failed at {:?} offset {:#x}: {:#x}", loc, offset, status.as_usize());
            }
        }
        value
    }

    fn write_config_u32(&self, loc: PciLocation, offset: u32, value: u32) {
        let addr = encode_pci_address(loc, offset);
        // SAFETY: rbi is valid per construction invariant
        unsafe {
            let proto = &*self.rbi;
            let status =
                (proto.pci.write)(self.rbi, Width::Uint32, addr, 1, &value as *const u32 as *mut core::ffi::c_void);
            if status.is_error() {
                log::warn!("PCI config write_u32 failed at {:?} offset {:#x}: {:#x}", loc, offset, status.as_usize());
            }
        }
    }

    fn probe_bar(&self, loc: PciLocation, offset: u32) -> Option<(u32, u32)> {
        let saved = self.read_config_u32(loc, offset);

        // Raise TPL to prevent timer interrupts while BAR is temporarily invalid.
        let _guard = self.tpl_mutex.lock();
        self.write_config_u32(loc, offset, 0xFFFF_FFFF);
        let sizing_mask = self.read_config_u32(loc, offset);
        self.write_config_u32(loc, offset, saved);
        drop(_guard);

        if sizing_mask == 0 { None } else { Some((sizing_mask, saved)) }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_encode_pci_address_standard() {
        let loc = PciLocation::new(0x05, 0x1F, 0x03);
        let addr = encode_pci_address(loc, 0x10);
        assert_eq!(addr & 0xFF, 0x10); // register
        assert_eq!((addr >> 8) & 0xFF, 0x03); // function
        assert_eq!((addr >> 16) & 0xFF, 0x1F); // device
        assert_eq!((addr >> 24) & 0xFF, 0x05); // bus
    }

    #[test]
    fn test_encode_pci_address_extended_register() {
        let loc = PciLocation::new(0, 0, 0);
        let addr = encode_pci_address(loc, 0x100);
        assert_eq!(addr & 0xFF, 0); // low bits empty
        assert_eq!(addr >> 32, 0x100); // extended register in upper 32
    }
}
