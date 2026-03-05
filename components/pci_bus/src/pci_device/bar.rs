//! PCI BAR (Base Address Register) definitions.
//!
//! Defines the BAR type classification and per-BAR state used throughout
//! PCI enumeration and resource allocation.

const SIZE_4KB: u64 = 0x1000;

// BAR register bit fields
const IO_BAR_BASE_MASK: u32 = 0xFFFF_FFFC;
const MEM_BAR_BASE_MASK: u32 = 0xFFFF_FFF0;

fn min_alignment(length: u64) -> u64 {
    if length < SIZE_4KB { SIZE_4KB - 1 } else { length - 1 }
}

/// Error returned when a BAR register contains a non-zero sizing mask
/// that cannot be classified as a valid BAR type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidBarError {
    pub offset: u32,
    pub sizing_mask: u32,
}

/// Classification of a PCI BAR's address space and width.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PciBarType {
    /// BAR type has not been determined.
    #[default]
    Unknown = 0,
    /// 16-bit I/O BAR.
    Io16,
    /// 32-bit I/O BAR.
    Io32,
    /// 32-bit non-prefetchable memory BAR.
    Mem32,
    /// 32-bit prefetchable memory BAR.
    PMem32,
    /// 64-bit non-prefetchable memory BAR.
    Mem64,
    /// 64-bit prefetchable memory BAR.
    PMem64,
    /// Expansion ROM BAR.
    OpRom,
    /// Generic I/O BAR (bridge I/O window).
    Io,
    /// Generic memory BAR (bridge memory window).
    Mem,
}

impl PciBarType {
    /// Returns true if this BAR type occupies two config space registers.
    pub fn is_64bit(self) -> bool {
        matches!(self, PciBarType::Mem64 | PciBarType::PMem64)
    }
}

/// State for a single PCI Base Address Register.
///
/// Tracks the decoded address, size, and type of a BAR as determined during
/// enumeration and updated during resource allocation.
#[derive(Debug, Clone, Copy, Default)]
pub struct PciBar {
    /// Base address assigned to this BAR (0 before allocation).
    pub base_address: u64,
    /// Size of the address range decoded by this BAR.
    pub length: u64,
    /// Natural alignment requirement of this BAR.
    pub alignment: u64,
    /// Type of address space this BAR decodes.
    pub bar_type: PciBarType,
    /// If true, the BAR type was determined by hardware and cannot be changed.
    pub bar_type_fixed: bool,
    /// Offset of this BAR register in PCI configuration space.
    pub offset: u16,
}

impl PciBar {
    /// Returns the config space offset of the next BAR register after this one.
    pub fn next_offset(&self) -> u32 {
        self.offset as u32 + if self.bar_type.is_64bit() { 8 } else { 4 }
    }

    /// Constructs an I/O BAR from sizing mask and saved register contents.
    pub(crate) fn from_io(
        sizing_mask: u32,
        saved: u32,
        offset: u32,
    ) -> Result<Self, InvalidBarError> {
        let is_32bit = (sizing_mask & 0xFFFF_0000) != 0;
        let raw_size = (!(sizing_mask & IO_BAR_BASE_MASK)).wrapping_add(1);
        let length = if is_32bit { raw_size as u64 } else { (raw_size & 0xFFFF) as u64 };

        if length == 0 {
            return Err(InvalidBarError { offset, sizing_mask });
        }

        Ok(Self {
            base_address: (saved & IO_BAR_BASE_MASK) as u64,
            length,
            alignment: length - 1,
            bar_type: if is_32bit { PciBarType::Io32 } else { PciBarType::Io16 },
            bar_type_fixed: false,
            offset: offset as u16,
        })
    }

    /// Constructs a 32-bit memory BAR from sizing mask and saved register contents.
    pub(crate) fn from_mem32(
        sizing_mask: u32,
        saved: u32,
        prefetchable: bool,
        offset: u32,
    ) -> Result<Self, InvalidBarError> {
        let length = (!(sizing_mask & MEM_BAR_BASE_MASK) as u64).wrapping_add(1);

        if length == 0 {
            return Err(InvalidBarError { offset, sizing_mask });
        }

        Ok(Self {
            base_address: (saved & MEM_BAR_BASE_MASK) as u64,
            length,
            alignment: min_alignment(length),
            bar_type: if prefetchable { PciBarType::PMem32 } else { PciBarType::Mem32 },
            bar_type_fixed: false,
            offset: offset as u16,
        })
    }

    /// Constructs a 64-bit memory BAR from lower and upper sizing/saved values.
    pub(crate) fn from_mem64(
        lower_sizing: u32,
        lower_saved: u32,
        upper_sizing: u32,
        upper_saved: u32,
        prefetchable: bool,
        offset: u32,
    ) -> Result<Self, InvalidBarError> {
        let base = (lower_saved & MEM_BAR_BASE_MASK) as u64 | ((upper_saved as u64) << 32);
        let combined =
            (lower_sizing & MEM_BAR_BASE_MASK) as u64 | ((upper_sizing as u64) << 32);
        let length = (!combined).wrapping_add(1);

        if length == 0 {
            return Err(InvalidBarError { offset, sizing_mask: lower_sizing });
        }

        Ok(Self {
            base_address: base,
            length,
            alignment: min_alignment(length),
            bar_type: if prefetchable { PciBarType::PMem64 } else { PciBarType::Mem64 },
            bar_type_fixed: false,
            offset: offset as u16,
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_bar_type_enum_values() {
        assert_eq!(PciBarType::Unknown as u32, 0);
        assert_eq!(PciBarType::Io16 as u32, 1);
        assert_eq!(PciBarType::Io32 as u32, 2);
        assert_eq!(PciBarType::Mem32 as u32, 3);
        assert_eq!(PciBarType::PMem32 as u32, 4);
        assert_eq!(PciBarType::Mem64 as u32, 5);
        assert_eq!(PciBarType::PMem64 as u32, 6);
        assert_eq!(PciBarType::OpRom as u32, 7);
        assert_eq!(PciBarType::Io as u32, 8);
        assert_eq!(PciBarType::Mem as u32, 9);
    }

    #[test]
    fn test_bar_default() {
        let bar = PciBar::default();
        assert_eq!(bar.base_address, 0);
        assert_eq!(bar.length, 0);
        assert_eq!(bar.alignment, 0);
        assert_eq!(bar.bar_type, PciBarType::Unknown);
        assert!(!bar.bar_type_fixed);
        assert_eq!(bar.offset, 0);
    }
}
