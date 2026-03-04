//! PCI resource tree node.
//!
//! [`PciResourceNode`] represents a single resource requirement (BAR or bridge
//! aperture) in the resource allocation tree. During enumeration, leaf nodes
//! are created for each device BAR and bridge nodes aggregate their children's
//! requirements.
//!


use alloc::vec::Vec;

use crate::pci_device::device::PciIoDeviceRef;
use crate::pci_device::PciBarType;

/// Indicates whether a resource node represents actual device requirements
/// or hot-plug padding.
///

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PciResourceUsage {
    /// Resource is for a real device BAR or bridge aperture.
    #[default]
    Typical,
    /// Resource is padding reserved for potential hot-plug devices.
    Padding,
}

/// A node in the PCI resource allocation tree.
///
/// Leaf nodes represent individual device BAR requirements. Bridge nodes
/// aggregate their children to compute the aperture the bridge must decode.
/// The tree is built bottom-up during enumeration and programmed top-down
/// during resource allocation.
///

pub struct PciResourceNode {
    /// The device that owns this resource requirement.
    pub pci_dev: PciIoDeviceRef,
    /// Natural alignment requirement.
    pub alignment: u64,
    /// Assigned offset within the parent's aperture (set during allocation).
    pub offset: u64,
    /// BAR index within the device (0-5), or bridge window identifier.
    pub bar: u8,
    /// Type of resource (I/O, Mem32, PMem64, etc.).
    pub res_type: PciBarType,
    /// Size of the resource requirement.
    pub length: u64,
    /// Reserved for internal use.
    pub reserved: bool,
    /// Whether this is a real requirement or hot-plug padding.
    pub resource_usage: PciResourceUsage,
    /// True for virtual BARs (e.g., SR-IOV VF BARs).
    pub virtual_bar: bool,
    /// Child resource nodes (populated for bridge aperture nodes).
    pub child_list: Vec<PciResourceNode>,
}

impl PciResourceNode {
    /// Creates a new resource node with the given parameters.
    pub fn new(
        pci_dev: PciIoDeviceRef,
        length: u64,
        alignment: u64,
        bar: u8,
        res_type: PciBarType,
        resource_usage: PciResourceUsage,
    ) -> Self {
        Self {
            pci_dev,
            alignment,
            offset: 0,
            bar,
            res_type,
            length,
            reserved: false,
            resource_usage,
            virtual_bar: false,
            child_list: Vec::new(),
        }
    }

    /// Inserts a child node sorted by alignment in descending order.
    ///
    /// This ensures optimal packing when resources are assigned top-down.
    pub fn insert_sorted(&mut self, node: PciResourceNode) {
        let pos = self
            .child_list
            .iter()
            .position(|child| child.alignment < node.alignment)
            .unwrap_or(self.child_list.len());
        self.child_list.insert(pos, node);
    }
}

#[cfg(test)]
mod test {
    use alloc::rc::Rc;
    use core::cell::RefCell;

    use super::*;
    use crate::pci_device::PciIoDevice;

    fn dummy_dev() -> PciIoDeviceRef {
        Rc::new(RefCell::new(PciIoDevice::new()))
    }

    #[test]
    fn test_resource_node_new() {
        let dev = dummy_dev();
        let node = PciResourceNode::new(
            dev,
            0x1000,
            0xFFF,
            0,
            PciBarType::Mem32,
            PciResourceUsage::Typical,
        );
        assert_eq!(node.alignment, 0xFFF);
        assert_eq!(node.length, 0x1000);
        assert_eq!(node.res_type, PciBarType::Mem32);
        assert_eq!(node.resource_usage, PciResourceUsage::Typical);
        assert!(!node.virtual_bar);
        assert!(node.child_list.is_empty());
    }

    #[test]
    fn test_insert_sorted_by_alignment_descending() {
        let dev = dummy_dev();
        let mut bridge = PciResourceNode::new(
            dev.clone(),
            0,
            0,
            0,
            PciBarType::Mem32,
            PciResourceUsage::Typical,
        );

        let small = PciResourceNode::new(
            dev.clone(),
            0x100,
            0xFF,
            0,
            PciBarType::Mem32,
            PciResourceUsage::Typical,
        );
        let large = PciResourceNode::new(
            dev.clone(),
            0x1000,
            0xFFF,
            1,
            PciBarType::Mem32,
            PciResourceUsage::Typical,
        );
        let medium = PciResourceNode::new(
            dev,
            0x400,
            0x3FF,
            2,
            PciBarType::Mem32,
            PciResourceUsage::Typical,
        );

        bridge.insert_sorted(small);
        bridge.insert_sorted(large);
        bridge.insert_sorted(medium);

        assert_eq!(bridge.child_list.len(), 3);
        assert_eq!(bridge.child_list[0].alignment, 0xFFF);
        assert_eq!(bridge.child_list[1].alignment, 0x3FF);
        assert_eq!(bridge.child_list[2].alignment, 0xFF);
    }
}
