//! PCI bus scanning — recursive device discovery.
//!
//! Scans a PCI bus by iterating over all device/function combinations,
//! reading the vendor ID to detect present devices, then creating
//! [`PciIoDevice`] instances for each. Bridges trigger recursive scanning
//! of their secondary bus.

use crate::pci_device::{PCI_HEADER_TYPE_MULTI_FUNC, PciConfigAccess, PciIoDevice, PciIoDeviceRef, PciLocation};

const PCI_MAX_DEVICE: u8 = 31;
const PCI_MAX_FUNC: u8 = 7;
const PCI_BRIDGE_SECONDARY_BUS_OFFSET: u32 = 0x19;

/// Recursively scans a PCI bus and collects all discovered devices.
///
/// For each device/function on the bus:
/// 1. Reads the config header to check if a device is present
/// 2. Creates a [`PciIoDevice`] with BAR and capability info
/// 3. If the device is a PCI-PCI bridge, recursively scans the secondary bus
/// 4. Adds the device to the parent bridge's child list
pub fn scan_bus(config: &dyn PciConfigAccess, parent: &PciIoDeviceRef, start_bus: u8) {
    for device in 0..=PCI_MAX_DEVICE {
        for function in 0..=PCI_MAX_FUNC {
            let loc = PciLocation::new(start_bus, device, function);

            let Some(pci) = config.read_config_header(loc) else {
                if function == 0 {
                    break;
                }
                continue;
            };

            log::debug!(
                "scan_bus: found device at {:?} (vendor={:#06x}, device={:#06x})",
                loc,
                pci.hdr.vendor_id,
                pci.hdr.device_id
            );

            let pci_dev = PciIoDevice::new(config, loc, pci, Some(parent));

            if pci_dev.borrow().is_bridge() {
                let sec_bus = config.read_config_u8(loc, PCI_BRIDGE_SECONDARY_BUS_OFFSET);

                if sec_bus > start_bus {
                    log::debug!("scan_bus: scanning secondary bus {:#04x} behind bridge at {:?}", sec_bus, loc);
                    scan_bus(config, &pci_dev, sec_bus);
                } else {
                    log::warn!(
                        "scan_bus: bridge at {:?} has invalid secondary bus {:#04x} (start_bus={:#04x})",
                        loc,
                        sec_bus,
                        start_bus
                    );
                }
            }

            parent.borrow_mut().add_child(pci_dev);

            if function == 0 && (pci.hdr.header_type & PCI_HEADER_TYPE_MULTI_FUNC) == 0 {
                break;
            }
        }
    }
}
