//! PCI Bus Patina component entry point.
//!
//! Defines [`PciBusComponent`] which, when dispatched, installs a UEFI Driver
//! Binding that consumes PCI Root Bridge I/O Protocol instances and produces
//! PCI I/O Protocol for each discovered PCI device.

use alloc::boxed::Box;
use core::ptr::NonNull;

use r_efi::{efi, protocols::device_path::Protocol as EfiDevicePathProtocol};

use patina::{
    BinaryGuid,
    boot_services::{BootServices, StandardBootServices},
    component::{component, params},
    driver_binding::{DriverBinding, UefiDriverBinding},
    error::Result,
    uefi_protocol::ProtocolInterface,
};

use crate::protocols::root_bridge_io::PciRootBridgeIoProtocol;

/// Zero-sized marker protocol used to create a dedicated driver binding handle.
#[repr(C)]
struct PciBusMarker;

// SAFETY: PciBusMarker is a ZST whose GUID uniquely identifies this component.
unsafe impl ProtocolInterface for PciBusMarker {
    const PROTOCOL_GUID: efi::Guid = *BinaryGuid::from_string("3323f52c-5a73-40eb-b0d4-c0acde555568").as_efi_guid();
}

/// PCI Bus Patina component.
///
/// When dispatched, installs a UEFI Driver Binding that enumerates PCI devices
/// on root bridges and produces PCI I/O Protocol for each.
pub struct PciBusComponent;

#[component]
impl PciBusComponent {
    fn entry_point(self, boot_services: StandardBootServices, image_handle: params::Handle) -> Result<()> {
        let boot_services: &'static StandardBootServices = Box::leak(Box::new(boot_services));
        install_pci_bus_driver_binding(boot_services, *image_handle)
    }
}

/// Installs the PCI bus driver binding using the provided boot services.
///
/// Separated from the component entry point to allow testing with
/// `MockBootServices`.
fn install_pci_bus_driver_binding<T: BootServices + Clone + 'static>(
    boot_services: &'static T,
    image_handle: efi::Handle,
) -> Result<()> {
    // Create a separate driver_binding handle to avoid conflict on the image handle.
    let (driver_binding_handle, _marker_key) =
        boot_services.install_protocol_interface(None, Box::new(PciBusMarker))?;

    let driver_binding = PciBusDriverBinding::new(boot_services, driver_binding_handle);

    let mut driver_binding =
        UefiDriverBinding::new_with_driver_handle(driver_binding, image_handle, driver_binding_handle, boot_services);

    driver_binding.install().map_err(patina::error::EfiError::from)?;

    Ok(())
}

/// PCI bus driver binding implementation.
///
/// Manages PCI bus instances on controllers that expose the PCI Root Bridge I/O
/// Protocol.
pub struct PciBusDriverBinding<T: BootServices + Clone + 'static> {
    boot_services: &'static T,
    agent: efi::Handle,
}

impl<T: BootServices + Clone + 'static> PciBusDriverBinding<T> {
    /// Creates a new PCI bus driver bound to the given agent handle.
    pub fn new(boot_services: &'static T, agent: efi::Handle) -> Self {
        Self { boot_services, agent }
    }
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
impl<T: BootServices + Clone + 'static> DriverBinding for PciBusDriverBinding<T> {
    /// Tests if the given controller supports the PCI Root Bridge I/O Protocol.
    fn driver_binding_supported<U: BootServices + 'static>(
        &self,
        _boot_services: &'static U,
        controller: efi::Handle,
        _remaining_device_path: Option<NonNull<EfiDevicePathProtocol>>,
    ) -> core::result::Result<bool, efi::Status> {
        // Try to open the PCI Root Bridge I/O Protocol to test support.
        // SAFETY: Testing protocol presence on controller; the protocol pointer
        // is not dereferenced and is immediately closed.
        let result = unsafe {
            self.boot_services.open_protocol::<PciRootBridgeIoProtocol>(
                controller,
                self.agent,
                controller,
                efi::OPEN_PROTOCOL_BY_DRIVER,
            )
        };

        match result {
            Ok(_protocol) => {
                // Protocol exists and we opened it; close it since this is just a test.
                let _ = self.boot_services.close_protocol(
                    controller,
                    &PciRootBridgeIoProtocol::PROTOCOL_GUID,
                    self.agent,
                    controller,
                );
                Ok(true)
            }
            Err(status) if status == efi::Status::ALREADY_STARTED => {
                // Another instance of this driver already manages this controller.
                Err(efi::Status::ALREADY_STARTED)
            }
            Err(_) => Ok(false),
        }
    }

    /// Starts PCI bus support for the given controller.
    ///
    /// Opens the Root Bridge I/O protocol, enumerates PCI devices, allocates
    /// resources, and installs PCI I/O Protocol for each discovered device.
    fn driver_binding_start<U: BootServices + 'static>(
        &mut self,
        _boot_services: &'static U,
        controller: efi::Handle,
        _remaining_device_path: Option<NonNull<EfiDevicePathProtocol>>,
    ) -> core::result::Result<(), efi::Status> {
        log::trace!("driver_binding_start: starting PCI bus on controller {:?}", controller);

        // TODO: Phase 4 - Enumerate PCI devices
        // TODO: Phase 5 - Allocate resources
        // TODO: Phase 8 - Register devices

        Ok(())
    }

    /// Stops PCI bus support for the given controller.
    fn driver_binding_stop<U: BootServices + 'static>(
        &mut self,
        _boot_services: &'static U,
        controller: efi::Handle,
        _number_of_children: usize,
        _child_handle_buffer: Option<NonNull<efi::Handle>>,
    ) -> core::result::Result<(), efi::Status> {
        log::trace!("driver_binding_stop: stopping PCI bus on controller {:?}", controller);

        // TODO: Phase 8 - Deregister devices

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use patina::boot_services::{MockBootServices, c_ptr::CPtr};

    use super::*;

    #[test]
    fn test_install_pci_bus_binding_should_install() {
        let boot_services = Box::leak(Box::new(MockBootServices::new()));

        boot_services.expect_install_protocol_interface::<PciBusMarker, Box<PciBusMarker>>().returning(
            |handle, protocol_interface| {
                assert_eq!(handle, None);
                Ok((0x5678 as efi::Handle, protocol_interface.metadata()))
            },
        );

        boot_services.expect_install_protocol_interface_unchecked().returning(|handle, protocol, interface| {
            if protocol == &efi::protocols::driver_binding::PROTOCOL_GUID {
                assert!(handle.is_some_and(|handle| handle as usize == 0x5678));
                assert!(!interface.is_null());
                return Ok(0x9abc as efi::Handle);
            }
            panic!("Unexpected protocol installation: {:?}", protocol);
        });

        let mock_image_handle = 0x1234 as efi::Handle;
        install_pci_bus_driver_binding(boot_services, mock_image_handle).expect("install should succeed");
    }

    #[test]
    fn test_install_pci_bus_binding_handles_failure() {
        let boot_services = Box::leak(Box::new(MockBootServices::new()));

        boot_services
            .expect_install_protocol_interface::<PciBusMarker, Box<PciBusMarker>>()
            .returning(|_, _| Err(efi::Status::OUT_OF_RESOURCES));

        let mock_image_handle = 0x1234 as efi::Handle;
        assert_eq!(
            install_pci_bus_driver_binding(boot_services, mock_image_handle),
            Err(efi::Status::OUT_OF_RESOURCES.into())
        );
    }
}
