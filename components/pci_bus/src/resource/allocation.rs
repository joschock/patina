//! PCI resource allocation.
//!
//! Implements the resource allocation engine: building a resource tree from
//! device BAR requirements, calculating bridge apertures bottom-up, applying
//! resource degradation for unsupported decode capabilities, and programming
//! addresses top-down into BAR and bridge aperture registers.

use alloc::vec::Vec;

use crate::pci_device::{PciBarType, device::PciIoDeviceRef};

use super::resource_node::{PciResourceNode, PciResourceUsage, ResourceKind};

/// Memory bridge alignment (1 MB - 1).
const PPB_MEM_ALIGNMENT: u64 = 0xF_FFFF;

/// The five resource pools for a bridge or root.
pub struct ResourcePools {
    /// I/O resource pool.
    pub io: PciResourceNode,
    /// 32-bit non-prefetchable memory pool.
    pub mem32: PciResourceNode,
    /// 32-bit prefetchable memory pool.
    pub pmem32: PciResourceNode,
    /// 64-bit non-prefetchable memory pool.
    pub mem64: PciResourceNode,
    /// 64-bit prefetchable memory pool.
    pub pmem64: PciResourceNode,
}

impl ResourcePools {
    /// Creates empty resource pools for the given bridge device.
    ///
    /// # Panics
    ///
    /// Debug-asserts that `bridge` is a PCI-to-PCI bridge (header type 1).
    pub fn new(bridge: PciIoDeviceRef) -> Self {
        debug_assert!(bridge.borrow().is_bridge(), "ResourcePools::new() requires a bridge device");

        let io_alignment = bridge.borrow().bridge_io_alignment() as u64;
        let io_alignment = if io_alignment == 0 { 0xFFF } else { io_alignment };

        Self {
            io: PciResourceNode::new(
                bridge.clone(),
                0,
                io_alignment,
                ResourceKind::BridgeIo,
                PciResourceUsage::Typical,
            ),
            mem32: PciResourceNode::new(
                bridge.clone(),
                0,
                PPB_MEM_ALIGNMENT,
                ResourceKind::BridgeMem32,
                PciResourceUsage::Typical,
            ),
            pmem32: PciResourceNode::new(
                bridge.clone(),
                0,
                PPB_MEM_ALIGNMENT,
                ResourceKind::BridgePMem32,
                PciResourceUsage::Typical,
            ),
            mem64: PciResourceNode::new(
                bridge.clone(),
                0,
                PPB_MEM_ALIGNMENT,
                ResourceKind::BridgeMem64,
                PciResourceUsage::Typical,
            ),
            pmem64: PciResourceNode::new(
                bridge,
                0,
                PPB_MEM_ALIGNMENT,
                ResourceKind::BridgePMem64,
                PciResourceUsage::Typical,
            ),
        }
    }

    /// Returns true if any pool has resource requests.
    pub fn has_requests(&self) -> bool {
        !self.io.child_list.is_empty()
            || !self.mem32.child_list.is_empty()
            || !self.pmem32.child_list.is_empty()
            || !self.mem64.child_list.is_empty()
            || !self.pmem64.child_list.is_empty()
    }

    /// Merges non-empty child bridge aperture pools into this set of pools.
    ///
    /// For each pool in `child_pools` that has children or non-zero length,
    /// calculates its aperture and pushes it into the corresponding parent pool.
    fn merge_child_pools(&mut self, child_pools: ResourcePools) {
        let pairs = [
            (child_pools.io, &mut self.io),
            (child_pools.mem32, &mut self.mem32),
            (child_pools.pmem32, &mut self.pmem32),
            (child_pools.mem64, &mut self.mem64),
            (child_pools.pmem64, &mut self.pmem64),
        ];

        for (mut child, parent) in pairs {
            if !child.child_list.is_empty() || child.length > 0 {
                child.calculate_aperture();
                parent.child_list.push(child);
            }
        }
    }

    /// Calculates apertures for all five resource pools.
    fn calculate_all_apertures(&mut self) {
        self.io.calculate_aperture();
        self.mem32.calculate_aperture();
        self.pmem32.calculate_aperture();
        self.mem64.calculate_aperture();
        self.pmem64.calculate_aperture();
    }

    /// Extracts BAR requirements from a device and inserts them into the
    /// appropriate resource pools.
    pub fn add_device_resources(&mut self, dev: &PciIoDeviceRef) {
        let dev_ref = dev.borrow();

        for (index, bar) in dev_ref.bars().iter().enumerate() {
            let node = PciResourceNode::new(
                dev.clone(),
                bar.length,
                bar.alignment,
                ResourceKind::Bar(index as u8, bar.bar_type),
                PciResourceUsage::Typical,
            );

            match bar.bar_type {
                PciBarType::Io16 | PciBarType::Io32 => {
                    self.io.child_list.push(node);
                }
                PciBarType::Mem32 | PciBarType::OpRom => {
                    self.mem32.child_list.push(node);
                }
                PciBarType::PMem32 => {
                    self.pmem32.child_list.push(node);
                }
                PciBarType::Mem64 => {
                    self.mem64.child_list.push(node);
                }
                PciBarType::PMem64 => {
                    self.pmem64.child_list.push(node);
                }
                _ => {
                    log::warn!("add_device_resources: unexpected bar_type {:?} at BAR index {}", bar.bar_type, index);
                    debug_assert!(false, "add_device_resources: unexpected bar_type {:?}", bar.bar_type);
                }
            }
        }

        // SR-IOV Virtual Function BARs
        for (index, bar) in dev_ref.vf_bars().iter().enumerate() {
            let node = PciResourceNode::new(
                dev.clone(),
                bar.length,
                bar.alignment,
                ResourceKind::VirtualBar(index as u8, bar.bar_type),
                PciResourceUsage::Typical,
            );

            match bar.bar_type {
                PciBarType::Mem32 => {
                    self.mem32.child_list.push(node);
                }
                PciBarType::Mem64 => {
                    self.mem64.child_list.push(node);
                }
                PciBarType::PMem32 => {
                    self.pmem32.child_list.push(node);
                }
                PciBarType::PMem64 => {
                    self.pmem64.child_list.push(node);
                }
                _ => {
                    log::warn!(
                        "add_device_resources: unexpected vf_bar_type {:?} at VF BAR index {}",
                        bar.bar_type,
                        index
                    );
                    debug_assert!(false, "add_device_resources: unexpected vf_bar_type {:?}", bar.bar_type);
                }
            }
        }
    }

    /// Applies resource degradation based on bridge decode capabilities.
    ///
    /// Degradation paths:
    /// - PMEM64 → PMEM32 (if bridge lacks PMEM64 decode)
    /// - MEM64 → MEM32 (if bridge lacks MEM64 decode)
    /// - PMEM32 → MEM32 (if bridge lacks PMEM32 decode)
    /// - PMEM32+PMEM64 conflict → PMEM32 merges to MEM32
    /// - Combined PMem+Mem decode → merge prefetchable into non-prefetchable
    ///
    /// # Panics
    ///
    /// Debug-asserts that `bridge` is a PCI-to-PCI bridge (header type 1).
    pub fn degrade(&mut self, bridge: &PciIoDeviceRef) {
        use crate::pci_device::device::bridge_decode;

        debug_assert!(bridge.borrow().is_bridge(), "degrade() requires a bridge device");

        let decodes = bridge.borrow().decodes();
        let has_parent = bridge.borrow().has_parent();

        // If bridge doesn't support MEM64, degrade to MEM32
        if (decodes & bridge_decode::MEM64) == 0 {
            drain_and_retype(&mut self.mem32, &mut self.mem64);
        }

        // If bridge doesn't support PMEM64, degrade to PMEM32
        if (decodes & bridge_decode::PMEM64) == 0 {
            drain_and_retype(&mut self.pmem32, &mut self.pmem64);
        }

        // If both PMEM64 and PMEM32 have requests (can't satisfy both on one bridge),
        // keep PMEM64 and degrade PMEM32 to MEM32
        if !self.pmem64.child_list.is_empty() && has_parent {
            drain_and_retype(&mut self.mem32, &mut self.pmem32);
        }

        // If bridge doesn't support PMEM32, degrade to MEM32
        if (decodes & bridge_decode::PMEM32) == 0 {
            drain_and_retype(&mut self.mem32, &mut self.pmem32);
        }

        // If bridge supports combined PMem+Mem decoding, merge prefetchable into non-prefetchable
        if (decodes & bridge_decode::PMEM_MEM_COMBINE) != 0 {
            drain_preserving_type(&mut self.mem32, &mut self.pmem32);
            drain_preserving_type(&mut self.mem64, &mut self.pmem64);
        }
    }
}

/// Recursively builds the resource tree for a bridge and all its children.
///
/// For each child device, extracts BAR requirements into the pools. For child
/// bridges, recursively builds sub-trees and inserts bridge aperture nodes.
pub fn create_resource_map(bridge: &PciIoDeviceRef, pools: &mut ResourcePools) {
    let children: Vec<PciIoDeviceRef> = bridge.borrow().clone_children();

    for child in &children {
        pools.add_device_resources(child);

        if child.borrow().is_bridge() {
            let mut child_pools = ResourcePools::new(child.clone());

            create_resource_map(child, &mut child_pools);

            child_pools.degrade(child);

            pools.merge_child_pools(child_pools);
        }
    }

    pools.degrade(bridge);

    pools.calculate_all_apertures();
}

// -- Resource degradation --

/// Drains all children from `src` into `dst`, retyping each node to match `dst`.
fn drain_and_retype(dst: &mut PciResourceNode, src: &mut PciResourceNode) {
    for mut node in src.child_list.drain(..).collect::<Vec<_>>() {
        node.kind.set_res_type(dst.kind.res_type());
        dst.child_list.push(node);
    }
}

/// Drains all children from `src` into `dst`, preserving each node's resource type.
fn drain_preserving_type(dst: &mut PciResourceNode, src: &mut PciResourceNode) {
    for node in src.child_list.drain(..).collect::<Vec<_>>() {
        dst.child_list.push(node);
    }
}

#[cfg(test)]
mod test {
    use alloc::rc::Rc;
    use core::cell::RefCell;

    use super::*;
    use crate::pci_device::{PciBar, PciIoDevice};

    fn dummy_dev() -> PciIoDeviceRef {
        Rc::new(RefCell::new(PciIoDevice::default()))
    }

    fn dev_with_bars(bars: Vec<PciBar>) -> PciIoDeviceRef {
        let mut dev = PciIoDevice::default();
        dev.set_pci_bar(bars);
        Rc::new(RefCell::new(dev))
    }

    #[test]
    fn test_resource_pools_new() {
        let bridge = dummy_dev();
        let pools = ResourcePools::new(bridge);
        assert_eq!(pools.io.kind.res_type(), PciBarType::Io16);
        assert_eq!(pools.mem32.kind.res_type(), PciBarType::Mem32);
        assert_eq!(pools.pmem32.kind.res_type(), PciBarType::PMem32);
        assert_eq!(pools.mem64.kind.res_type(), PciBarType::Mem64);
        assert_eq!(pools.pmem64.kind.res_type(), PciBarType::PMem64);
        assert!(!pools.has_requests());
    }

    #[test]
    fn test_get_resource_from_device_mem32() {
        let bridge = dummy_dev();
        let mut pools = ResourcePools::new(bridge);

        let dev = dev_with_bars(vec![PciBar {
            length: 0x1000,
            alignment: 0xFFF,
            bar_type: PciBarType::Mem32,
            offset: 0x10,
            ..Default::default()
        }]);

        pools.add_device_resources(&dev);

        assert_eq!(pools.mem32.child_list.len(), 1);
        assert_eq!(pools.mem32.child_list[0].length, 0x1000);
        assert_eq!(pools.mem32.child_list[0].alignment, 0xFFF);
        assert_eq!(pools.mem32.child_list[0].kind, ResourceKind::Bar(0, PciBarType::Mem32));
    }

    #[test]
    fn test_get_resource_from_device_mixed() {
        let bridge = dummy_dev();
        let mut pools = ResourcePools::new(bridge);

        let dev = dev_with_bars(vec![
            PciBar { length: 0x100, alignment: 0xFF, bar_type: PciBarType::Io32, offset: 0x10, ..Default::default() },
            PciBar {
                length: 0x10000,
                alignment: 0xFFFF,
                bar_type: PciBarType::Mem64,
                offset: 0x18,
                ..Default::default()
            },
        ]);

        pools.add_device_resources(&dev);

        assert_eq!(pools.io.child_list.len(), 1);
        assert_eq!(pools.mem64.child_list.len(), 1);
        assert!(pools.mem32.child_list.is_empty());
    }

    #[test]
    fn test_calculate_aperture_single() {
        let bridge = dummy_dev();
        let mut root = PciResourceNode::new(
            bridge.clone(),
            0,
            PPB_MEM_ALIGNMENT,
            ResourceKind::BridgeMem32,
            PciResourceUsage::Typical,
        );

        let child = PciResourceNode::new(
            bridge,
            0x1000,
            0xFFF,
            ResourceKind::Bar(0, PciBarType::Mem32),
            PciResourceUsage::Typical,
        );
        root.child_list.push(child);

        root.calculate_aperture();

        assert_eq!(root.child_list[0].offset, 0);
        assert_eq!(root.length, 0x10_0000); // Rounded up to 1MB alignment
    }

    #[test]
    fn test_calculate_aperture_multiple() {
        let bridge = dummy_dev();
        let mut root = PciResourceNode::new(
            bridge.clone(),
            0,
            PPB_MEM_ALIGNMENT,
            ResourceKind::BridgeMem32,
            PciResourceUsage::Typical,
        );

        // Large BAR (64KB aligned)
        let large = PciResourceNode::new(
            bridge.clone(),
            0x10000,
            0xFFFF,
            ResourceKind::Bar(0, PciBarType::Mem32),
            PciResourceUsage::Typical,
        );
        // Small BAR (4KB aligned)
        let small = PciResourceNode::new(
            bridge,
            0x1000,
            0xFFF,
            ResourceKind::Bar(1, PciBarType::Mem32),
            PciResourceUsage::Typical,
        );

        root.child_list.push(large);
        root.child_list.push(small);

        root.calculate_aperture();

        // Large bar at offset 0, small bar at 0x10000
        assert_eq!(root.child_list[0].offset, 0);
        assert_eq!(root.child_list[0].length, 0x10000);
        assert_eq!(root.child_list[1].offset, 0x10000);
        assert_eq!(root.child_list[1].length, 0x1000);
        // Total: 0x11000, rounded up to 1MB
        assert_eq!(root.length, 0x10_0000);
    }

    #[test]
    fn test_drain_and_retype() {
        let dev = dummy_dev();
        let mut dst =
            PciResourceNode::new(dev.clone(), 0, 0xFFFFF, ResourceKind::BridgeMem32, PciResourceUsage::Typical);
        let mut src =
            PciResourceNode::new(dev.clone(), 0, 0xFFFFF, ResourceKind::BridgePMem64, PciResourceUsage::Typical);

        let child = PciResourceNode::new(
            dev,
            0x10000,
            0xFFFF,
            ResourceKind::Bar(0, PciBarType::PMem64),
            PciResourceUsage::Typical,
        );
        src.child_list.push(child);

        drain_and_retype(&mut dst, &mut src);

        assert!(src.child_list.is_empty());
        assert_eq!(dst.child_list.len(), 1);
        assert_eq!(dst.child_list[0].kind.res_type(), PciBarType::Mem32);
    }

    #[test]
    fn test_degrade_no_mem64() {
        let bridge_dev = dummy_dev();
        // Bridge with no MEM64/PMEM64 decode support
        bridge_dev.borrow_mut().set_decodes(0);
        let mut pools = ResourcePools::new(bridge_dev.clone());

        let dev = dev_with_bars(vec![PciBar {
            length: 0x10000,
            alignment: 0xFFFF,
            bar_type: PciBarType::Mem64,
            offset: 0x10,
            ..Default::default()
        }]);

        pools.add_device_resources(&dev);
        assert_eq!(pools.mem64.child_list.len(), 1);

        pools.degrade(&bridge_dev);

        assert!(pools.mem64.child_list.is_empty());
        assert_eq!(pools.mem32.child_list.len(), 1);
        assert_eq!(pools.mem32.child_list[0].kind.res_type(), PciBarType::Mem32);
    }
}
