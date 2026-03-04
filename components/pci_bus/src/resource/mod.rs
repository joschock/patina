//! PCI resource allocation data structures.
//!
//! Re-exports [`PciResourceNode`] and [`PciResourceUsage`] from the
//! `resource_node` submodule.

pub mod resource_node;

pub use resource_node::{PciResourceNode, PciResourceUsage};
