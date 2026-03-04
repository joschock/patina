//! PCI BAR (Base Address Register) definitions.
//!
//! Defines the BAR type classification and per-BAR state used throughout
//! PCI enumeration and resource allocation.
//!

/// Maximum number of standard BARs per PCI device (excludes expansion ROM BAR).
pub const PCI_MAX_BAR: usize = 6;

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
    /// Sentinel value.
    MaxType,
}

/// State for a single PCI Base Address Register.
///
/// Tracks the decoded address, size, and type of a BAR as determined during
/// enumeration and updated during resource allocation.
#[derive(Debug, Clone, Copy)]
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

impl Default for PciBar {
    fn default() -> Self {
        Self {
            base_address: 0,
            length: 0,
            alignment: 0,
            bar_type: PciBarType::Unknown,
            bar_type_fixed: false,
            offset: 0,
        }
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
        assert_eq!(PciBarType::MaxType as u32, 10);
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
