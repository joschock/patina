//! PCI Host Bridge Resource Allocation Protocol FFI definitions.
//!
//! Defines the `#[repr(C)]` struct matching
//! `EFI_PCI_HOST_BRIDGE_RESOURCE_ALLOCATION_PROTOCOL` from the PI specification.
//! This protocol is consumed by the PCI bus driver to coordinate enumeration
//! phases and resource allocation with the host bridge driver.

use core::ffi::c_void;

use patina::{BinaryGuid, uefi_protocol::ProtocolInterface};
use r_efi::efi;

/// Enumeration phase notifications sent to the host bridge driver.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HostBridgePhase {
    /// Reset host bridge PCI apertures and internal data structures.
    BeginEnumeration = 0,
    /// Bus allocation phase is about to begin.
    BeginBusAllocation,
    /// Bus allocation and bus programming phase is complete.
    EndBusAllocation,
    /// Resource allocation phase is about to begin.
    BeginResourceAllocation,
    /// Allocate resources per previously submitted requests.
    AllocateResources,
    /// Program host bridge hardware to decode allocated resources.
    SetResources,
    /// De-allocate previously allocated resources and reset apertures.
    FreeResources,
    /// Resource allocation phase is completed.
    EndResourceAllocation,
    /// Host bridge enumeration is completed.
    EndEnumeration,
    /// Sentinel value.
    Maximum,
}

/// Controller-level enumeration phase notifications.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControllerPhase {
    /// About to begin enumerating the bus behind a PCI-PCI bridge.
    BeforeChildBusEnumeration = 0,
    /// About to probe BAR registers for a PCI function.
    BeforeResourceCollection,
}

/// Host bridge allocation attribute flags.
pub const COMBINE_MEM_PMEM: u64 = 1;
/// Host bridge supports 64-bit memory windows.
pub const MEM64_DECODE: u64 = 2;

/// Function pointer type for NotifyPhase.
pub type NotifyPhase = unsafe extern "efiapi" fn(
    this: *mut PciHostBridgeResourceAllocationProtocol,
    phase: HostBridgePhase,
) -> efi::Status;

/// Function pointer type for GetNextRootBridge.
pub type GetNextRootBridge = unsafe extern "efiapi" fn(
    this: *mut PciHostBridgeResourceAllocationProtocol,
    root_bridge_handle: *mut efi::Handle,
) -> efi::Status;

/// Function pointer type for GetAllocAttributes.
pub type GetAllocAttributes = unsafe extern "efiapi" fn(
    this: *mut PciHostBridgeResourceAllocationProtocol,
    root_bridge_handle: efi::Handle,
    attributes: *mut u64,
) -> efi::Status;

/// Function pointer type for StartBusEnumeration.
pub type StartBusEnumeration = unsafe extern "efiapi" fn(
    this: *mut PciHostBridgeResourceAllocationProtocol,
    root_bridge_handle: efi::Handle,
    configuration: *mut *mut c_void,
) -> efi::Status;

/// Function pointer type for SetBusNumbers.
pub type SetBusNumbers = unsafe extern "efiapi" fn(
    this: *mut PciHostBridgeResourceAllocationProtocol,
    root_bridge_handle: efi::Handle,
    configuration: *mut c_void,
) -> efi::Status;

/// Function pointer type for SubmitResources.
pub type SubmitResources = unsafe extern "efiapi" fn(
    this: *mut PciHostBridgeResourceAllocationProtocol,
    root_bridge_handle: efi::Handle,
    configuration: *mut c_void,
) -> efi::Status;

/// Function pointer type for GetProposedResources.
pub type GetProposedResources = unsafe extern "efiapi" fn(
    this: *mut PciHostBridgeResourceAllocationProtocol,
    root_bridge_handle: efi::Handle,
    configuration: *mut *mut c_void,
) -> efi::Status;

/// Function pointer type for PreprocessController.
pub type PreprocessController = unsafe extern "efiapi" fn(
    this: *mut PciHostBridgeResourceAllocationProtocol,
    root_bridge_handle: efi::Handle,
    pci_address: u64,
    phase: ControllerPhase,
) -> efi::Status;

/// PCI Host Bridge Resource Allocation Protocol.
///
/// Provides interfaces for the PCI bus driver to coordinate enumeration
/// and resource allocation with the platform's host bridge driver.
#[repr(C)]
pub struct PciHostBridgeResourceAllocationProtocol {
    /// Notify the host bridge of enumeration phase transitions.
    pub notify_phase: NotifyPhase,
    /// Get the next PCI root bridge handle.
    pub get_next_root_bridge: GetNextRootBridge,
    /// Get allocation attributes for a root bridge.
    pub get_alloc_attributes: GetAllocAttributes,
    /// Set up a root bridge for bus enumeration.
    pub start_bus_enumeration: StartBusEnumeration,
    /// Program a root bridge to decode a bus number range.
    pub set_bus_numbers: SetBusNumbers,
    /// Submit I/O and memory resource requirements.
    pub submit_resources: SubmitResources,
    /// Get proposed resource assignments.
    pub get_proposed_resources: GetProposedResources,
    /// Pre-initialize a PCI controller before enumeration.
    pub preprocess_controller: PreprocessController,
}

// SAFETY: The struct layout matches the PI spec's
// EFI_PCI_HOST_BRIDGE_RESOURCE_ALLOCATION_PROTOCOL and the GUID is the
// standard protocol GUID from the specification.
unsafe impl ProtocolInterface for PciHostBridgeResourceAllocationProtocol {
    const PROTOCOL_GUID: efi::Guid =
        *BinaryGuid::from_string("cf8034be-6768-4d8b-b739-7cce683a9fbe").as_efi_guid();
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_host_bridge_alloc_protocol_guid() {
        let guid = PciHostBridgeResourceAllocationProtocol::PROTOCOL_GUID;
        assert_eq!(
            guid.as_fields(),
            (0xcf8034be, 0x6768, 0x4d8b, 0xb7, 0x39, &[0x7c, 0xce, 0x68, 0x3a, 0x9f, 0xbe])
        );
    }

    #[test]
    fn test_host_bridge_phase_enum_values() {
        assert_eq!(HostBridgePhase::BeginEnumeration as u32, 0);
        assert_eq!(HostBridgePhase::BeginBusAllocation as u32, 1);
        assert_eq!(HostBridgePhase::EndBusAllocation as u32, 2);
        assert_eq!(HostBridgePhase::BeginResourceAllocation as u32, 3);
        assert_eq!(HostBridgePhase::EndEnumeration as u32, 8);
        assert_eq!(HostBridgePhase::Maximum as u32, 9);
    }

    #[test]
    fn test_controller_phase_enum_values() {
        assert_eq!(ControllerPhase::BeforeChildBusEnumeration as u32, 0);
        assert_eq!(ControllerPhase::BeforeResourceCollection as u32, 1);
    }
}
