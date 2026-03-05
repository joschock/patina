//! PCI resource tree node.
//!
//! [`PciResourceNode`] represents a single resource requirement (BAR or bridge
//! aperture) in the resource allocation tree. During enumeration, leaf nodes
//! are created for each device BAR and bridge nodes aggregate their children's
//! requirements.
//!

use alloc::vec::Vec;

use crate::pci_device::{PciBarType, device::PciIoDeviceRef, ppb_regs};

/// Rounds `value` up to the next multiple of the alignment granularity.
///
/// `alignment_mask` is a PCI-style bitmask (e.g., `0xFFF` for 4KB alignment).
/// The actual granularity is `alignment_mask + 1`.
fn align_up(value: u64, alignment_mask: u64) -> u64 {
    let granularity = alignment_mask + 1;
    if granularity == 0 {
        return value;
    }
    value.div_ceil(granularity) * granularity
}

/// Indicates whether a resource node represents actual device requirements
/// or hot-plug padding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PciResourceUsage {
    /// Resource is for a real device BAR or bridge aperture.
    #[default]
    Typical,
    /// Resource is padding reserved for potential hot-plug devices.
    Padding,
}

/// Identifies the source of a resource requirement and its resource type.
///
/// For BAR sources, the resource type is carried as payload and may be mutated
/// during resource degradation. For bridge sources, the resource type is fixed
/// and derived from the variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceKind {
    /// A standard device BAR with its resource type. The index is a slot in the
    /// [`PciIoDevice::pci_bar`](crate::pci_device::PciIoDevice) Vec, **not** a
    /// BAR register number — 64-bit BARs consume two registers but one Vec slot.
    Bar(u8, PciBarType),
    /// An SR-IOV Virtual Function BAR with its resource type. The index is a
    /// slot in the [`PciIoDevice::vf_pci_bar`](crate::pci_device::PciIoDevice)
    /// Vec, not a BAR register number.
    VirtualBar(u8, PciBarType),
    /// Bridge I/O forwarding window (always [`PciBarType::Io16`]).
    BridgeIo,
    /// Bridge 32-bit non-prefetchable memory window (always [`PciBarType::Mem32`]).
    BridgeMem32,
    /// Bridge 64-bit non-prefetchable memory pool (always [`PciBarType::Mem64`]).
    ///
    /// PCI-to-PCI bridges have no dedicated 64-bit non-prefetchable window;
    /// this variant programs the same registers as [`BridgeMem32`](Self::BridgeMem32).
    /// It exists so the resource pool's type accurately reflects what it collects.
    BridgeMem64,
    /// Bridge 32-bit prefetchable memory window (always [`PciBarType::PMem32`]).
    BridgePMem32,
    /// Bridge 64-bit prefetchable memory window (always [`PciBarType::PMem64`]).
    BridgePMem64,
}

impl ResourceKind {
    /// Returns the [`PciBarType`] associated with this source.
    pub fn res_type(&self) -> PciBarType {
        match self {
            Self::Bar(_, t) | Self::VirtualBar(_, t) => *t,
            Self::BridgeIo => PciBarType::Io16,
            Self::BridgeMem32 => PciBarType::Mem32,
            Self::BridgeMem64 => PciBarType::Mem64,
            Self::BridgePMem32 => PciBarType::PMem32,
            Self::BridgePMem64 => PciBarType::PMem64,
        }
    }

    /// Updates the resource type for BAR sources (used during degradation).
    ///
    /// Bridge sources are unchanged since they represent fixed hardware windows.
    /// Calling this on a bridge source is a logic error and triggers a debug assert.
    pub fn set_res_type(&mut self, new_type: PciBarType) {
        match self {
            Self::Bar(_, t) | Self::VirtualBar(_, t) => *t = new_type,
            _ => {
                debug_assert!(false, "set_res_type called on bridge source {:?}", self);
            }
        }
    }
}

/// A node in the PCI resource allocation tree.
///
/// Leaf nodes represent individual device BAR requirements. Bridge nodes
/// aggregate their children to compute the aperture the bridge must decode.
/// The tree is built bottom-up during enumeration and programmed top-down
/// during resource allocation.
pub struct PciResourceNode {
    /// The device that owns this resource requirement.
    pub pci_dev: PciIoDeviceRef,
    /// Natural alignment requirement.
    pub alignment: u64,
    /// Assigned offset within the parent's aperture (set during allocation).
    pub offset: u64,
    /// What this resource node represents and its resource type.
    pub kind: ResourceKind,
    /// Size of the resource requirement.
    pub length: u64,
    /// Reserved for internal use.
    pub reserved: bool,
    /// Whether this is a real requirement or hot-plug padding.
    pub resource_usage: PciResourceUsage,
    /// Child resource nodes (populated for bridge aperture nodes).
    pub child_list: Vec<PciResourceNode>,
}

impl PciResourceNode {
    /// Creates a new resource node with the given parameters.
    pub fn new(
        pci_dev: PciIoDeviceRef,
        length: u64,
        alignment: u64,
        kind: ResourceKind,
        resource_usage: PciResourceUsage,
    ) -> Self {
        Self { pci_dev, alignment, offset: 0, kind, length, reserved: false, resource_usage, child_list: Vec::new() }
    }

    /// Calculates the resource aperture (bottom-up sizing).
    ///
    /// Sorts children by alignment descending for optimal packing, then computes
    /// the `offset` field on each child and the total `length` on this node.
    /// For I/O resources, uses a simplified allocation without ISA/VGA alias skipping.
    pub fn calculate_aperture(&mut self) {
        self.child_list.sort_by(|a, b| b.alignment.cmp(&a.alignment));
        let mut aperture_typical: u64 = 0;
        let mut aperture_padding: u64 = 0;

        for child in &mut self.child_list {
            let aperture = match child.resource_usage {
                PciResourceUsage::Typical => &mut aperture_typical,
                PciResourceUsage::Padding => &mut aperture_padding,
            };

            child.offset = align_up(*aperture, child.alignment);
            *aperture = child.offset + child.length;
        }

        aperture_typical = align_up(aperture_typical, self.alignment);
        aperture_padding = align_up(aperture_padding, self.alignment);

        self.length = aperture_typical.max(aperture_padding);

        // Promote alignment to first (largest) child's alignment
        if let Some(first_child) = self.child_list.first()
            && first_child.alignment > self.alignment
        {
            self.alignment = first_child.alignment;
        }
    }

    /// Recursively programs resource addresses top-down through the tree.
    ///
    /// `base` is the starting address for this node's aperture. Each child's
    /// actual address is `base + child.offset` (computed during aperture calculation).
    pub fn program(&mut self, base: u64, config: &dyn crate::pci_device::PciConfigAccess) {
        for child in &mut self.child_list {
            match child.kind {
                ResourceKind::BridgeIo
                | ResourceKind::BridgeMem32
                | ResourceKind::BridgeMem64
                | ResourceKind::BridgePMem32
                | ResourceKind::BridgePMem64 => {
                    child.program(base + child.offset, config);
                    child.program_ppb_aperture(base, config);
                }
                ResourceKind::Bar(_, _) => {
                    child.program_bar(base, config);
                }
                ResourceKind::VirtualBar(_, _) => {
                    child.program_vf_bar(base, config);
                }
            }
        }
    }

    /// Programs a device BAR register with its assigned base address.
    fn program_bar(&mut self, base: u64, config: &dyn crate::pci_device::PciConfigAccess) {
        let bar_index = match self.kind {
            ResourceKind::Bar(i, _) => i as usize,
            _ => {
                log::warn!("program_bar called with non-Bar kind: {:?}", self.kind);
                debug_assert!(false, "program_bar called with non-Bar kind: {:?}", self.kind);
                return;
            }
        };

        let address = base + self.offset;
        let dev = self.pci_dev.borrow();
        let loc = dev.location();

        if bar_index >= dev.pci_bar.len() {
            return;
        }

        let bar_offset = dev.pci_bar[bar_index].offset as u32;
        let bar_type = dev.pci_bar[bar_index].bar_type;
        drop(dev);

        match bar_type {
            PciBarType::Io16 | PciBarType::Io32 | PciBarType::Mem32 | PciBarType::PMem32 => {
                config.write_config_u32(loc, bar_offset, address as u32);
            }
            PciBarType::Mem64 | PciBarType::PMem64 => {
                config.write_config_u32(loc, bar_offset, address as u32);
                config.write_config_u32(loc, bar_offset + 4, (address >> 32) as u32);
            }
            _ => {
                log::warn!("program_bar: unexpected bar_type {:?} at index {}", bar_type, bar_index);
                debug_assert!(false, "program_bar: unexpected bar_type {:?}", bar_type);
                return;
            }
        }

        let mut dev = self.pci_dev.borrow_mut();
        dev.allocated = true;
        dev.pci_bar[bar_index].base_address = address;
    }

    /// Programs a VF (Virtual Function) BAR register.
    fn program_vf_bar(&mut self, base: u64, config: &dyn crate::pci_device::PciConfigAccess) {
        let bar_index = match self.kind {
            ResourceKind::VirtualBar(i, _) => i as usize,
            _ => {
                log::warn!("program_vf_bar called with non-VirtualBar kind: {:?}", self.kind);
                debug_assert!(false, "program_vf_bar called with non-VirtualBar kind: {:?}", self.kind);
                return;
            }
        };

        let address = base + self.offset;
        let dev = self.pci_dev.borrow();
        let loc = dev.location();

        if bar_index >= dev.vf_pci_bar.len() {
            return;
        }

        let bar_offset = dev.vf_pci_bar[bar_index].offset as u32;
        let bar_type = dev.vf_pci_bar[bar_index].bar_type;
        drop(dev);

        match bar_type {
            PciBarType::Mem32 | PciBarType::PMem32 => {
                config.write_config_u32(loc, bar_offset, address as u32);
            }
            PciBarType::Mem64 | PciBarType::PMem64 => {
                config.write_config_u32(loc, bar_offset, address as u32);
                config.write_config_u32(loc, bar_offset + 4, (address >> 32) as u32);
            }
            _ => {
                log::warn!("program_vf_bar: unexpected bar_type {:?} at index {}", bar_type, bar_index);
                debug_assert!(false, "program_vf_bar: unexpected bar_type {:?}", bar_type);
                return;
            }
        }

        let mut dev = self.pci_dev.borrow_mut();
        dev.allocated = true;
        dev.vf_pci_bar[bar_index].base_address = address;
    }

    /// Programs PCI-PCI bridge aperture registers.
    fn program_ppb_aperture(&mut self, base: u64, config: &dyn crate::pci_device::PciConfigAccess) {
        if self.length == 0 {
            return;
        }
        if self.resource_usage == PciResourceUsage::Padding {
            debug_assert!(false, "program_ppb_aperture called on a Padding node: {:?}", self.kind);
            return;
        }

        let address = base + self.offset;
        let dev = self.pci_dev.borrow();
        let loc = dev.location();
        drop(dev);

        self.pci_dev.borrow_mut().allocated = true;

        match self.kind {
            ResourceKind::BridgeIo => {
                let io_base = (address >> 8) as u32;
                let io_limit = ((address + self.length - 1) >> 8) as u32;

                config.write_config_u32(loc, ppb_regs::IO_BASE, io_base & 0xFF);
                config.write_config_u32(loc, ppb_regs::IO_BASE_UPPER, (io_base >> 8) & 0xFFFF);
                config.write_config_u32(loc, ppb_regs::IO_LIMIT, io_limit & 0xFF);
                config.write_config_u32(loc, ppb_regs::IO_LIMIT_UPPER, (io_limit >> 8) & 0xFFFF);
            }
            ResourceKind::BridgeMem32 => {
                let mem_base = (address >> 16) as u32;
                let mem_limit = ((address + self.length - 1) >> 16) as u32;

                config.write_config_u32(loc, ppb_regs::MEM_BASE, mem_base & 0xFFFF);
                config.write_config_u32(loc, ppb_regs::MEM_LIMIT, mem_limit & 0xFFFF);
            }
            // PCI-to-PCI bridges have no 64-bit non-prefetchable memory window.
            // This pool is always degraded to BridgeMem32 before programming.
            ResourceKind::BridgeMem64 => {
                log::warn!("BridgeMem64 resource reached programming without degradation (length={:#x})", self.length);
                debug_assert!(false, "BridgeMem64 should have been degraded to BridgeMem32");
            }
            ResourceKind::BridgePMem32 | ResourceKind::BridgePMem64 => {
                let pmem_base = (address >> 16) as u32;
                let pmem_limit = ((address + self.length - 1) >> 16) as u32;

                config.write_config_u32(loc, ppb_regs::PMEM_BASE, pmem_base & 0xFFFF);
                config.write_config_u32(loc, ppb_regs::PMEM_LIMIT, pmem_limit & 0xFFFF);
                config.write_config_u32(loc, ppb_regs::PMEM_BASE_UPPER, (address >> 32) as u32);
                config.write_config_u32(loc, ppb_regs::PMEM_LIMIT_UPPER, ((address + self.length - 1) >> 32) as u32);
            }
            ResourceKind::Bar(_, _) | ResourceKind::VirtualBar(_, _) => {
                log::warn!("program_ppb_aperture called with non-bridge kind: {:?}", self.kind);
                debug_assert!(false, "program_ppb_aperture called with non-bridge kind: {:?}", self.kind);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use alloc::rc::Rc;
    use core::cell::RefCell;

    use super::*;
    use crate::pci_device::PciIoDevice;

    fn dummy_dev() -> PciIoDeviceRef {
        Rc::new(RefCell::new(PciIoDevice::default()))
    }

    #[test]
    fn test_resource_node_new() {
        let dev = dummy_dev();
        let node = PciResourceNode::new(
            dev,
            0x1000,
            0xFFF,
            ResourceKind::Bar(0, PciBarType::Mem32),
            PciResourceUsage::Typical,
        );
        assert_eq!(node.alignment, 0xFFF);
        assert_eq!(node.length, 0x1000);
        assert_eq!(node.kind.res_type(), PciBarType::Mem32);
        assert_eq!(node.resource_usage, PciResourceUsage::Typical);
        assert_eq!(node.kind, ResourceKind::Bar(0, PciBarType::Mem32));
        assert!(node.child_list.is_empty());
    }

    #[test]
    fn test_calculate_aperture_sorts_by_alignment_descending() {
        let dev = dummy_dev();
        let mut bridge = PciResourceNode::new(dev.clone(), 0, 0, ResourceKind::BridgeMem32, PciResourceUsage::Typical);

        let small = PciResourceNode::new(
            dev.clone(),
            0x100,
            0xFF,
            ResourceKind::Bar(0, PciBarType::Mem32),
            PciResourceUsage::Typical,
        );
        let large = PciResourceNode::new(
            dev.clone(),
            0x1000,
            0xFFF,
            ResourceKind::Bar(1, PciBarType::Mem32),
            PciResourceUsage::Typical,
        );
        let medium =
            PciResourceNode::new(dev, 0x400, 0x3FF, ResourceKind::Bar(2, PciBarType::Mem32), PciResourceUsage::Typical);

        bridge.child_list.push(small);
        bridge.child_list.push(large);
        bridge.child_list.push(medium);

        bridge.calculate_aperture();

        assert_eq!(bridge.child_list.len(), 3);
        assert_eq!(bridge.child_list[0].alignment, 0xFFF);
        assert_eq!(bridge.child_list[1].alignment, 0x3FF);
        assert_eq!(bridge.child_list[2].alignment, 0xFF);
    }

    #[test]
    fn test_align_up() {
        // 0xFFF mask = 4KB granularity
        assert_eq!(align_up(0, 0xFFF), 0);
        assert_eq!(align_up(1, 0xFFF), 0x1000);
        assert_eq!(align_up(0x1000, 0xFFF), 0x1000);
        assert_eq!(align_up(0x1001, 0xFFF), 0x2000);
    }
}
