//! PCI Bus Driver — Patina component.
//!
//! This crate provides a Patina component that consumes the PCI Root Bridge I/O
//! Protocol and produces the PCI I/O Protocol for each discovered PCI device.
//!
//! ## License
//!
//! Copyright (c) Microsoft Corporation. All rights reserved.
//!
#![cfg_attr(not(test), no_std)]

extern crate alloc;

pub mod bus_scan;
pub mod component;
pub mod pci_device;
pub mod pci_io;
pub mod protocols;
pub mod resource;
