//! PCI resource allocation data structures and logic.
//!
//! Re-exports [`PciResourceNode`] and [`PciResourceUsage`] from the
//! `resource_node` submodule, and provides resource allocation functions
//! in the `allocation` submodule.

pub mod allocation;
pub mod resource_node;

pub use allocation::ResourcePools;
pub use resource_node::{PciResourceNode, PciResourceUsage, ResourceKind};
