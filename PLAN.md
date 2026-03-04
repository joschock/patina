# PciBusDxe → Patina Component Conversion Plan

## Current Progress

> **Last updated:** 2026-03-04 (Session 1)
>
> **Build:** `cargo build -p pci_bus` ✅ | `cargo test -p pci_bus` ✅ (6 tests passing)
>
> | Phase | Status | Notes |
> |-------|--------|-------|
> | 1. Scaffolding & Protocol FFI | 🔶 Partial | Crate created, root_bridge_io done. 7 more protocols to add as needed. |
> | 2. Core Data Structures | ⬜ Not started | |
> | 3. Component & Driver Binding | 🔶 Skeleton | Entry point + driver binding compile with stub Start/Stop. |
> | 4. PCI Enumeration | ⬜ Not started | |
> | 5. Resource Allocation | ⬜ Not started | |
> | 6. PCI I/O Protocol | ⬜ Not started | |
> | 7. Supporting Features | ⬜ Not started | |
> | 8. Device Lifecycle | ⬜ Not started | |
> | 9. Testing | ⬜ Not started | 6 tests exist from Phases 1 & 3 |
> | 10. Integration & Docs | ⬜ Not started | |
>
> **Next steps:** Phase 2 (PciBar, PciIoDevice, PciResourceNode data structures), then Phase 4
> (enumeration) which also requires the Host Bridge Resource Allocation protocol FFI definition.

---

## Agent Context & Cross-Session Instructions

> **For future agents working on this conversion:** This is a multi-session project converting a
> ~19,400-line C UEFI driver to Rust. Read this entire document before starting any work.

### Re-establishing Context

1. **Read this plan first** — it contains the full architecture, phase breakdown, and design decisions.
2. **Check implementation progress** — look at `components/pci_bus/src/` to see what files exist and
   which phases are complete. Each phase builds on the previous one.
3. **Reference the C original** at `~/devices2/MU_BASECORE/MdeModulePkg/Bus/Pci/PciBusDxe/` — this is
   the source-of-truth for behavior. When in doubt about logic, read the corresponding C file.
4. **Reference the HID component** (PR #1364, branch `hid_component` on `joschock/patina`) as the
   canonical example of a UEFI driver → Patina component conversion. The pattern for component entry
   point, driver binding, marker protocol, and testing is established there.
5. **Check patina SDK** at `sdk/patina/src/` for available infrastructure — especially
   `driver_binding.rs`, `boot_services.rs`, `uefi_protocol.rs`, and `device_path/node_defs.rs`.
6. **Run `cargo build -p pci_bus` and `cargo test -p pci_bus`** to verify current state compiles and
   tests pass before making changes.

### Key Files to Understand

| File | Purpose |
|------|---------|
| `~/devices2/.../PciBusDxe/PciBus.h` | Master header with PCI_IO_DEVICE struct and all declarations |
| `~/devices2/.../PciBusDxe/PciBusDxe.inf` | Module deps, protocols consumed/produced, PCDs |
| `~/devices2/.../PciBusDxe/PciBus.c` | Entry point + driver binding (Supported/Start/Stop) |
| `~/devices2/.../PciBusDxe/PciEnumerator.c` | Top-level enumeration orchestration |
| `~/devices2/.../PciBusDxe/PciEnumeratorSupport.c` | Bus scanning, BAR sizing (~3,100 lines) |
| `~/devices2/.../PciBusDxe/PciResourceSupport.c` | Resource tree and allocation (~2,400 lines) |
| `~/devices2/.../PciBusDxe/PciIo.c` | PCI I/O Protocol implementation (~2,150 lines) |
| `~/devices2/.../PciBusDxe/PciLib.c` | Common PCI library functions (~1,940 lines) |
| `~/devices2/.../PciBusDxe/PciDeviceSupport.c` | Device registration/deregistration |

### Conventions to Follow

- **Crate naming:** `pci_bus` (not `patina_pci_bus` — per existing convention in `uefi_hid`)
- **Module layout:** Follow RFC #9 component crate standards (see `docs/src/component/requirements.md`)
- **No-std:** `#![cfg_attr(not(test), no_std)]` with `extern crate alloc;`
- **Lints:** Use `[lints] workspace = true`
- **Tests:** Use `MockBootServices` from `patina::boot_services`; prefix tests with `test_`
- **Safety comments:** All `unsafe` blocks must have `// SAFETY:` comments
- **Doc comments:** All public items documented (`missing_docs` lint is error in workspace)
- **Feature flags:** Map C PCDs to Cargo features with `#[cfg(feature = "...")]`
- **User review:** Stop after completing each phase and wait for user review/approval before
  proceeding to the next phase.

### What NOT to Do

- Don't do a 1:1 C-to-Rust translation — use idiomatic Rust (Vec instead of linked lists, enum
  instead of #define constants, Result instead of status code checking)
- Don't try to implement everything in one session — each phase should produce compilable code
- Don't modify patina SDK or core code — all new code goes in `components/pci_bus/`
- Don't skip tests — write them alongside implementation, not as an afterthought

---

## Problem Statement

Convert the existing UEFI PciBusDxe driver (~19,400 lines of C across 30 files in
`MdeModulePkg/Bus/Pci/PciBusDxe`) into a Patina component written in Rust. The driver implements
full PCI bus enumeration, resource allocation, and produces the PCI I/O Protocol for each discovered
device.

## Reference Implementation

The conversion follows the same pattern as the UEFI HID component (PR #1364):
- `#[component]` entry point installs a `UefiDriverBinding`
- `DriverBinding` trait methods (Supported/Start/Stop) manage per-controller instances
- UEFI protocol FFI structs defined locally for protocols not in r-efi
- `MockBootServices` used for unit testing

## Existing Patina Infrastructure

**Available:**
- `patina::driver_binding::{DriverBinding, UefiDriverBinding}` — full driver binding support
- `r_efi::protocols::pci_io` — PCI I/O Protocol FFI definitions
- `patina::device_path::node_defs::Pci` — PCI device path node
- `patina::macros::pci::pci_address!` — PCI address computation
- `patina::boot_services::BootServices` — Protocol install/open/locate/close
- `patina::uefi_protocol::ProtocolInterface` — Protocol GUID trait

**NOT Available (must be defined in-crate):**
- PCI Root Bridge I/O Protocol (`EFI_PCI_ROOT_BRIDGE_IO_PROTOCOL`)
- PCI Host Bridge Resource Allocation Protocol
- PCI Hot Plug Init Protocol
- PCI Platform Protocol / PCI Override Protocol
- Incompatible PCI Device Support Protocol
- Device Security Protocol
- Decompress Protocol
- PCI Enumeration Complete Protocol

---

## Architecture Overview

```
components/pci_bus/
├── Cargo.toml
├── README.md
└── src/
    ├── lib.rs                     # Component entry point
    ├── component.rs               # #[component] impl + driver binding install
    ├── driver_binding.rs          # DriverBinding trait impl (Supported/Start/Stop)
    ├── pci_device.rs              # PciIoDevice struct (Rust equivalent of PCI_IO_DEVICE)
    ├── pci_device/
    │   └── bar.rs                 # PciBar definitions
    ├── pci_io/
    │   ├── mod.rs                 # PCI I/O Protocol implementation
    │   ├── config.rs              # Config space read/write
    │   ├── mem_io.rs              # Memory and I/O space operations
    │   ├── dma.rs                 # Map/Unmap/AllocateBuffer/FreeBuffer
    │   └── attributes.rs          # Attribute get/set operations
    ├── enumerator/
    │   ├── mod.rs                 # Top-level enumeration orchestration
    │   ├── bus_scan.rs            # Bus/device/function scanning
    │   ├── bar_scan.rs            # BAR detection and sizing
    │   └── capabilities.rs        # PCIe/ARI/SR-IOV capability parsing
    ├── resource/
    │   ├── mod.rs                 # Resource allocation orchestration
    │   ├── resource_node.rs       # Resource tree data structures
    │   ├── aperture.rs            # Bridge aperture calculation
    │   └── programming.rs         # BAR/bridge register programming
    ├── protocols/
    │   ├── mod.rs                 # Re-exports
    │   ├── root_bridge_io.rs      # PCI Root Bridge I/O Protocol FFI
    │   ├── host_bridge_alloc.rs   # Host Bridge Resource Allocation FFI
    │   ├── hot_plug_init.rs       # PCI Hot Plug Init Protocol FFI
    │   ├── pci_platform.rs        # PCI Platform/Override Protocol FFI
    │   ├── incompatible.rs        # Incompatible PCI Device Support FFI
    │   ├── enumeration_complete.rs # PCI Enumeration Complete Protocol
    │   └── device_security.rs     # Device Security Protocol FFI
    ├── hot_plug.rs                # Hot plug support logic
    ├── option_rom.rs              # Option ROM loading/processing
    ├── command.rs                 # PCI command register helpers
    ├── power_management.rs        # Power state management
    ├── driver_override.rs         # Bus-specific driver override
    ├── component_name.rs          # Component Name Protocol support
    └── rom_table.rs               # ROM table management
```

---

## Implementation Phases

### Phase 1: Project Scaffolding & Protocol FFI Definitions

**Goal:** Create the crate skeleton and define all UEFI protocol FFI types that aren't in r-efi.

**Status:** ✅ Scaffold done; Root Bridge I/O protocol done. Remaining protocols can be added as needed.

**Tasks:**

1. **Create crate structure** ✅
   - `components/pci_bus/Cargo.toml` with workspace deps (patina, r-efi, log, etc.)
   - `src/lib.rs` with module declarations, `#![cfg_attr(not(test), no_std)]`
   - Crate is part of workspace via `components/*` glob — no Cargo.toml edit needed

2. **Define PCI Root Bridge I/O Protocol** (`protocols/root_bridge_io.rs`) ✅
   - `#[repr(C)]` struct matching `EFI_PCI_ROOT_BRIDGE_IO_PROTOCOL`
   - All function pointer types, Width/Operation enums, PciAddress struct, Access struct
   - Attribute constants (ISA, VGA, memory, DAC, etc.)
   - `unsafe impl ProtocolInterface` with GUID `2f707ebb-4a1a-11d4-...`
   - Tests for GUID, enum values, and struct layout

3. **Define Host Bridge Resource Allocation Protocol** (`protocols/host_bridge_alloc.rs`)
   - `#[repr(C)]` struct matching `EFI_PCI_HOST_BRIDGE_RESOURCE_ALLOCATION_PROTOCOL`
   - NotifyPhase, GetNextRootBridge, GetAllocAttributes, StartBusEnumeration, SetBusNumbers,
     SubmitResources, GetProposedResources, PreprocessController
   - Phase enum values (BeginEnumeration, BeginBusAllocation, etc.)
   - Reference: `MdePkg/Include/Protocol/PciHostBridgeResourceAllocation.h`

4. **Define remaining protocol FFI types** ⬜ (add as needed when consuming code is written)
   - Host Bridge Resource Allocation (`MdePkg/Include/Protocol/PciHostBridgeResourceAllocation.h`) — needed in Phase 4
   - Hot Plug Init (`MdePkg/Include/Protocol/PciHotPlugInit.h`) — needed in Phase 7
   - PCI Platform / PCI Override (`MdePkg/Include/Protocol/PciPlatform.h`) — needed in Phase 7
   - Incompatible PCI Device Support (`MdePkg/Include/Protocol/IncompatiblePciDeviceSupport.h`) — needed in Phase 7
   - Device Security (`MdePkg/Include/Protocol/DeviceSecurity.h`) — needed in Phase 7
   - Decompress (`MdePkg/Include/Protocol/Decompress.h`) — needed in Phase 7
   - PCI Enumeration Complete (GUID-only, no interface) — needed in Phase 8

### Phase 2: Core Data Structures

**Goal:** Define the Rust equivalents of C data structures.

**Status:** Not started

**Tasks:**

1. **PciBar** (`pci_device/bar.rs`)
   - Enum `PciBarType { Unknown, Io16, Io32, Mem32, PMem32, Mem64, PMem64, OpRom, Io, Mem, MaxType }`
     (11 variants matching C enum order — `Unknown` = 0, `MaxType` = 10)
   - Struct `PciBar { base_address: u64, length: u64, alignment: u64, bar_type: PciBarType,
     bar_type_fixed: bool, offset: u16 }`
   - Constant `PCI_MAX_BAR: usize = 6` (standard BARs only; ROM BAR handled separately)
   - Reference: `PCI_BAR` and `PCI_BAR_TYPE` in `PciBus.h`

2. **PciIoDevice** (`pci_device.rs`)
   - Primary struct with device state fields (C has ~40+ fields; some won't translate directly)
   - Device identity: bus/device/function, PCI config header (`PCI_TYPE00` from r-efi or custom)
   - Resource management: `pci_bar: [PciBar; PCI_MAX_BAR]`, attributes (`u64`), supports (`u64`),
     decodes (`u32`)
   - Hierarchy: parent handle (`Option<efi::Handle>`), children `Vec<Box<PciIoDevice>>` (replaces
     C `LIST_ENTRY ChildList`)
   - Status flags: registered, allocated, all_op_rom_processed, embedded_rom, bus_override
   - ROM: rom_size (`u32`), ignore_rom (`bool`)
   - Protocol pointers: device_path, pci_root_bridge_io (stored as pointers, not embedded structs)
   - PCIe capabilities: is_pci_exp, is_ari_enabled, pci_express_capability_offset (`u8`),
     ari/sriov/mriov capability offsets (`u32`)
   - SR-IOV: `vf_pci_bar: [PciBar; PCI_MAX_BAR]`, system_page_size, initial_vfs, reserved_bus_num
   - Bridge: bridge_io_alignment (`u16`), resizable_bar_offset/number
   - Hot plug: resource_padding_descriptors, padding_attributes, bus_number_ranges
   - Max payload size (`u8`)
   - Handle (`efi::Handle`)
   - **Not translated directly:** C `Signature` (use Rust type system), `Link` (use Vec in parent),
     inline protocol structs (`PciIo`, `PciDriverOverride`, `LoadFile2` — build at registration time)
   - Methods for construction, capability queries
   - Reference: `PCI_IO_DEVICE` in `PciBus.h`

3. **PciResourceNode** (`resource/resource_node.rs`)
   - Tree structure for resource requirements
   - Fields: alignment (`u64`), offset (`u64`), length (`u64`), bar (`u8`),
     res_type (`PciBarType`), reserved (`bool`), resource_usage (`PciResourceUsage`),
     virtual_bar (`bool`), pci_dev back-reference (`Option<*mut PciIoDevice>`)
   - Enum `PciResourceUsage { Typical, Padding }`
   - Children `Vec<PciResourceNode>` (replaces C `LIST_ENTRY ChildList`)
   - Methods: insert_sorted (by alignment descending), calculate_aperture
   - Reference: `PCI_RESOURCE_NODE` in `PciResourceSupport.h`

### Phase 3: Component Entry Point & Driver Binding

**Goal:** Implement the Patina component and UEFI driver binding.

**Status:** 🔶 Skeleton done — component entry point and driver binding Supported/Start/Stop compile and have tests. Start/Stop bodies are stubs (TODO comments for Phases 4/5/8).

**Tasks:**

1. **Component definition** (`component.rs`) ✅
   - `pub struct PciBusComponent;` with `#[component]` macro
   - Accepts `StandardBootServices` and `params::Handle`
   - Installs `UefiDriverBinding` with `PciBusMarker` protocol (zero-sized, unique GUID)
   - `install_pci_bus_driver_binding()` helper separated for testability
   - 2 unit tests passing (success and failure paths)

2. **Driver Binding** (also in `component.rs`) ✅ skeleton
   - `PciBusDriverBinding<T: BootServices>` struct with `&'static T` and agent handle
   - `impl DriverBinding for PciBusDriverBinding<T>`
   - **Supported():** Opens `PciRootBridgeIoProtocol` BY_DRIVER, closes immediately; returns ALREADY_STARTED if applicable
   - **TODO (Phase 4):** Supported() also needs `RemainingDevicePath` validation (must be end-of-path
     or valid `HW_PCI_DP` node) and `DevicePathProtocol` open BY_DRIVER, matching the C reference
   - **Start():** Stub body (TODO comments for Phases 4/5/8)
   - **Stop():** Stub body (TODO comment for Phase 8)
   - **Note:** The C reference does not use a private per-instance marker protocol; it relies on
     BY_DRIVER opens and global state. A per-instance marker (like HID's pattern) can be added later
     if a need is identified during implementation of Start/Stop.
   - **Note:** `open_protocol` is `unsafe` — wrapped with SAFETY comment
   - **Note:** DriverBinding trait uses `core::result::Result<T, efi::Status>`, NOT `patina::error::Result`
   - **Note:** Tests need `use patina::boot_services::c_ptr::CPtr` for `metadata()`

3. **PCD Configuration** (optional: via `Config<PciBusConfig>` or Cargo features)
   - Feature flags map to PCDs (see Design Decisions section)

### Phase 4: PCI Enumeration

**Goal:** Implement device discovery and bus scanning.

**Status:** Not started

**C source reference:** `PciEnumerator.c` (~2,248 lines), `PciEnumeratorSupport.c` (~3,114 lines)

**Tasks:**

1. **Top-level enumeration** (`enumerator/mod.rs`)
   - `pci_host_bridge_enumerator()` — drives full enumeration sequence
   - `pci_root_bridge_enumerator()` — enumerate a single root bridge
   - Notify phases via Host Bridge Resource Allocation Protocol:
     BeginEnumeration → BeginBusAllocation → EndBusAllocation →
     BeginResourceAllocation → (submit) → EndResourceAllocation →
     EndEnumeration

2. **Bus scanning** (`enumerator/bus_scan.rs`)
   - `pci_device_info_collector()` — recursive device scanning
   - For each bus (0-255), device (0-31), function (0-7):
     - Read vendor/device ID via Root Bridge I/O Pci.Read
     - Skip if vendor == 0xFFFF
     - Create `PciIoDevice` instance
     - Check header type for multi-function and bridge detection
     - For bridges: assign secondary bus number, recurse into downstream bus
   - Reference: `PciPciDeviceInfoCollector()` in `PciEnumeratorSupport.c`

3. **BAR scanning** (`enumerator/bar_scan.rs`)
   - Read and parse BAR registers (offset 0x10-0x24)
   - Write 0xFFFFFFFF, read back to determine size
   - Detect BAR type from low bits (IO vs Mem, 32 vs 64, prefetchable)
   - Handle 64-bit BARs spanning two registers
   - Parse expansion ROM BAR (offset 0x30)
   - Reference: `BarExisted()`, `PciParseBar()` in `PciEnumeratorSupport.c`

4. **Capability parsing** (`enumerator/capabilities.rs`)
   - Walk PCI capability linked list (starting from Cap Pointer at offset 0x34)
   - Detect PCIe capabilities (Cap ID 0x10): link width/speed, slot info
   - Parse ARI capability (extended, Cap ID 0x000E)
   - Parse SR-IOV capability (extended, Cap ID 0x0010): VF count, system page size
   - Parse MR-IOV capability (extended, Cap ID 0x0011)
   - Detect resizable BAR capability (extended, Cap ID 0x0015)
   - Reference: Various functions in `PciEnumeratorSupport.c`

### Phase 5: Resource Allocation

**Goal:** Implement BAR and bridge aperture resource allocation.

**Status:** Not started

**C source reference:** `PciResourceSupport.c` (~2,395 lines)

**Tasks:**

1. **Resource tree construction** (`resource/mod.rs`)
   - `create_resource_map()` — build resource requirement tree from device list
   - Five separate trees: IO, Mem32, PMem32, Mem64, PMem64
   - Root nodes represent root bridge apertures
   - Leaf nodes represent device BAR requirements
   - Bridge nodes aggregate children

2. **Aperture calculation** (`resource/aperture.rs`)
   - `calculate_resource_aperture()` — recursive bottom-up aperture sizing
   - Sort children by alignment (descending) for optimal packing
   - Bridge apertures = sum of children + alignment padding
   - VGA range avoidance (0x3B0-0x3BB, 0x3C0-0x3DF for IO)
   - ISA aliasing range handling (0x100-0x3FF)
   - Resource degradation when host bridge doesn't support 64-bit:
     PMem64 → Mem64 → Mem32; PMem64 → PMem32 → Mem32; IO32 → IO16

3. **Resource programming** (`resource/programming.rs`)
   - `program_resource()` — top-down address assignment from root bridge apertures
   - `program_bar()` — write base address into device BAR registers
   - `program_ppb_aperture()` — set PCI-PCI bridge IO/Mem/PMem windows
   - `program_upstream_bridge_for_rom()` — temporary aperture for ROM access
   - Submit resource requests via Host Bridge Resource Allocation Protocol

### Phase 6: PCI I/O Protocol Production

**Goal:** Implement the PCI I/O Protocol installed for each discovered device.

**Status:** Not started

**C source reference:** `PciIo.c` (~2,152 lines)

**Tasks:**

1. **Protocol structure** (`pci_io/mod.rs`)
   - Build `r_efi::protocols::pci_io::Protocol` function pointer table
   - Each `extern "efiapi"` function recovers `PciIoDevice` context
   - Context recovery: store `PciIoDevice` pointer adjacent to protocol struct,
     use pointer math (like C's `CR()` / `CONTAINING_RECORD` macro)
   - Alternatively: use a wrapper struct `PciIoWrapper { protocol: Protocol, device: *mut PciIoDevice }`

2. **Config space** (`pci_io/config.rs`)
   - `pci_io_config_read()` / `pci_io_config_write()`
   - Validate width (8/16/32), count, and offset within config space
   - Build PCI address from device's segment/bus/dev/fn + offset
   - Delegate to Root Bridge I/O Protocol's Pci.Read/Pci.Write
   - Reference: `PciIoConfigRead()`, `PciIoConfigWrite()` in `PciIo.c`

3. **Memory & I/O** (`pci_io/mem_io.rs`)
   - MMIO read/write: validate BAR, translate to Root Bridge I/O Mem.Read/Write
   - I/O port read/write: validate BAR, translate to Root Bridge I/O Io.Read/Write
   - Poll operations: periodic read-and-check with timeout
   - Memory copy: between device memory regions
   - Reference: `PciIoMemRead()`, `PciIoIoRead()`, `PciIoPollMem()` etc.

4. **DMA** (`pci_io/dma.rs`)
   - Map: translate system address to device-visible DMA address
   - Unmap: release DMA mapping
   - AllocateBuffer: allocate DMA-coherent memory
   - FreeBuffer: release DMA buffer
   - Flush: ensure cache coherency
   - Handle dual-address-cycle (DAC) for 64-bit DMA
   - Reference: `PciIoMap()`, `PciIoAllocateBuffer()` etc.

5. **Attributes** (`pci_io/attributes.rs`)
   - Operations: Get (current), Set (enable/disable), ListSupported
   - Manage IO, Memory, BusMaster, VGA, ISA attributes via command register
   - BAR attribute queries (memory type, prefetchability)
   - GetLocation: return segment/bus/device/function tuple

### Phase 7: Supporting Features

**Goal:** Implement auxiliary functionality.

**Status:** Not started

**Tasks:**

1. **PCI Command Register** (`command.rs`) — Reference: `PciCommand.c` (264 lines)
   - `pci_read_command_register()` / `pci_set_command_register()` / `pci_clear_command_register()`
   - Bit manipulation for IO, Memory, BusMaster, VGA palette snoop
   - Bridge control register helpers

2. **Hot Plug Support** (`hot_plug.rs`) — Reference: `PciHotPlugSupport.c` (477 lines)
   - Feature-gated (`#[cfg(feature = "hot-plug")]`)
   - Discover Hot Plug Controllers via Hot Plug Init Protocol
   - Detect SHPC (Standard Hot Plug Controller) and PCIe native hot plug
   - Resource padding descriptors for hot-pluggable slots
   - Hot Plug Request Protocol installation

3. **Option ROM** (`option_rom.rs`) — Reference: `PciOptionRomSupport.c` (773 lines)
   - Read ROM BAR and determine ROM size
   - Load ROM image into memory, verify 0x55AA signature
   - Decompress if compressed (via Decompress Protocol)
   - Scan for EFI driver images within ROM
   - LoadFile2 protocol for ROM image access

4. **Driver Override** (`driver_override.rs`) — Reference: `PciDriverOverride.c` (189 lines)
   - `BusSpecificDriverOverride` protocol implementation
   - Track EFI driver image handles loaded from option ROMs
   - GetDriver: iterate through override driver list

5. **Power Management** (`power_management.rs`) — Reference: `PciPowerManagement.c` (82 lines)
   - Detect PM capability register
   - Read/write power state (D0-D3)
   - Reset to D0 during enumeration

6. **Component Name** (`component_name.rs`) — Reference: `ComponentName.c` (169 lines)
   - ComponentName / ComponentName2 protocol
   - Return driver name ("PCI Bus Driver") and controller names

7. **ROM Table** (`rom_table.rs`) — Reference: `PciRomTable.c` (137 lines)
   - Global table of processed option ROM images
   - Registration and lookup by device path

### Phase 8: Device Registration & Lifecycle

**Goal:** Handle UEFI handle/protocol lifecycle for discovered PCI devices.

**Status:** Not started

**C source reference:** `PciDeviceSupport.c` (~1,151 lines), `PciLib.c` (~1,939 lines)

**Tasks:**

1. **Device registration** (in driver_binding Start flow)
   - Create new UEFI handle per PCI device (`install_protocol_interface`)
   - Install `PciIoProtocol` on device handle
   - Build and install `DevicePathProtocol` (append PCI node to parent path)
   - Install `BusSpecificDriverOverride` if option ROM drivers found
   - Install `LoadFile2` if option ROM present
   - Open Root Bridge I/O on device handle with `BY_CHILD_CONTROLLER`
   - Reference: `RegisterPciDevice()` in `PciDeviceSupport.c`

2. **Device deregistration** (in driver_binding Stop flow)
   - Uninstall all protocols from device handles
   - Close Root Bridge I/O Protocol (`BY_CHILD_CONTROLLER`)
   - Drop `PciIoDevice` (free resources)
   - Recursively stop child controllers first
   - Reference: `DeRegisterPciDevice()` in `PciDeviceSupport.c`

3. **Enumeration complete signaling**
   - Install `gEfiPciEnumerationCompleteProtocolGuid` with NULL interface
   - Signals to other drivers that PCI enumeration is done

### Phase 9: Testing

**Goal:** Comprehensive unit test coverage using mock boot services.

**Status:** Not started

**Tasks:**

1. **Protocol FFI tests**
   - `core::mem::size_of::<Protocol>()` matches UEFI spec expectations
   - Field offset verification via `core::mem::offset_of!`
   - GUID correctness (compare against known values)

2. **Core logic tests** (using `MockBootServices`)
   - BAR scanning with mocked config space reads (various BAR types)
   - Resource tree construction and aperture calculation (simple and complex topologies)
   - Device enumeration with mock Root Bridge I/O (single device, bridge, multi-function)
   - PCI I/O operations with mock underlying Root Bridge I/O
   - Driver binding Supported (protocol present/absent), Start, Stop flows

3. **Edge case tests**
   - Multi-function devices (header type bit 7)
   - 64-bit BAR spanning two registers
   - Resource degradation paths (PMem64 → Mem32)
   - Hot plug padding calculations
   - Option ROM with multiple images
   - Empty bus scan (no devices)

### Phase 10: Integration & Documentation

**Goal:** Integrate into workspace and document.

**Status:** Not started

**Tasks:**

1. **Workspace integration**
   - Add `"components/pci_bus"` to workspace members in root `Cargo.toml`
   - Add workspace dependency entries for any new crates used
   - Verify `cargo build -p pci_bus` and `cargo test -p pci_bus` pass
   - Update `cspell.yml` with PCI-specific terms (aperture, subordinate, etc.)

2. **README.md** (in `components/pci_bus/`)
   - Architecture overview with module diagram
   - Protocols consumed/produced table
   - Feature flags documentation
   - Platform integration instructions (`ComponentInfo` setup)
   - Testing instructions

3. **Code documentation**
   - All public items documented (workspace lint: `missing_docs = error`)
   - Module-level doc comments explaining architecture and data flow
   - Safety comments on all `unsafe` blocks

---

## Key Design Decisions

### 1. Trait Abstractions for Consumed Protocols

Wrap raw FFI protocol pointers behind safe Rust traits (similar to HID's `HidIo` trait). This
enables unit testing with mocks and provides type safety.

```rust
pub trait PciRootBridgeIo {
    fn pci_read(&self, width: Width, address: u64, count: usize, buffer: &mut [u8]) -> Result<(), efi::Status>;
    fn pci_write(&self, width: Width, address: u64, count: usize, buffer: &[u8]) -> Result<(), efi::Status>;
    // ... other operations
}
```

### 2. PciIoDevice Ownership Model

Each `PciIoDevice` is `Box`-allocated and installed as a private protocol on its handle (like HID's
`HidInstance` pattern). The driver binding's Stop method recovers ownership via
`open_protocol_unchecked` + `Box::from_raw` to drop the device cleanly.

### 3. Feature Flags for Optional Functionality

| Feature | Default | Maps to PCD |
|---------|---------|-------------|
| `hot-plug` | off | PcdPciBusHotplugDeviceSupport |
| `io-alignment-probe` | off | PcdPciBridgeIoAlignmentProbe |
| `unaligned-pci-io` | off | PcdUnalignedPciIoEnable |
| `degrade-for-optrom` | on | PcdPciDegradeResourceForOptionRom |
| `sriov` | off | PcdSrIovSupport |
| `ari` | off | PcdAriSupport |
| `mriov` | off | PcdMrIovSupport |
| `resizable-bar` | off | PcdPcieResizableBarSupport |
| `defer-bme` | off | PcdDeferBME |
| `disable-bme-on-ebs` | off | PcdDisableBMEonEBS |

### 4. Resource Tree as Rust Data Structure

Replace C linked lists with `Vec`-based children in resource nodes. The tree is built bottom-up
(leaf devices first) and programmed top-down (root bridge first). This is a natural fit for Rust's
ownership model.

### 5. Error Handling

Use `Result<T, efi::Status>` throughout internal APIs. The FFI boundary converts to/from
`efi::Status` return codes. Log errors via `log` crate before returning.

### 6. Phased Implementation Strategy

This is a very large conversion (~19K lines of C). Each phase produces a compilable and testable
increment. **After completing each phase, stop and wait for user review before starting the next
phase.**

- **Phases 1-3:** Minimal compilable component that installs driver binding → **review**
- **Phase 4:** Enumeration discovers devices (no resource allocation yet) → **review**
- **Phase 5:** Resources allocated and BARs programmed → **review**
- **Phase 6:** Full PCI I/O Protocol available to downstream drivers → **review**
- **Phase 7:** Hot plug, option ROM, and other features added incrementally → **review**
- **Phases 8-10:** Polish, testing, documentation → **review after each**

---

## C File → Rust Module Mapping

| C Source File | Lines | Rust Module | Phase |
|---------------|-------|-------------|-------|
| `PciBus.c` | 461 | `component.rs`, `driver_binding.rs` | 3 |
| `PciBus.h` | 1,135 | `pci_device.rs`, `pci_device/bar.rs` | 2 |
| `PciEnumerator.c` | 2,248 | `enumerator/mod.rs` | 4 |
| `PciEnumeratorSupport.c` | 3,114 | `enumerator/bus_scan.rs`, `bar_scan.rs`, `capabilities.rs` | 4 |
| `PciResourceSupport.c` | 2,395 | `resource/mod.rs`, `aperture.rs`, `programming.rs` | 5 |
| `PciIo.c` | 2,152 | `pci_io/*.rs` | 6 |
| `PciLib.c` | 1,939 | `driver_binding.rs` (Start/Stop helpers), `pci_device.rs` | 3, 8 |
| `PciDeviceSupport.c` | 1,151 | `driver_binding.rs` (register/deregister) | 8 |
| `PciOptionRomSupport.c` | 773 | `option_rom.rs` | 7 |
| `PciHotPlugSupport.c` | 477 | `hot_plug.rs` | 7 |
| `PciCommand.c` | 264 | `command.rs` | 7 |
| `PciDriverOverride.c` | 189 | `driver_override.rs` | 7 |
| `ComponentName.c` | 169 | `component_name.rs` | 7 |
| `PciRomTable.c` | 137 | `rom_table.rs` | 7 |
| `PciPowerManagement.c` | 82 | `power_management.rs` | 7 |
| Protocol headers | ~2,700 | `protocols/*.rs` | 1 |

---

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Missing protocol definitions in r-efi | High | Define FFI structs in-crate with careful spec alignment |
| C-to-Rust semantic mismatches (pointer math, linked lists) | Medium | Use idiomatic Rust (Vec, Option, enum) rather than 1:1 translation |
| Unsafe code at FFI boundaries | Medium | Minimize unsafe surface; wrap in safe abstractions immediately |
| Testing without real PCI hardware | Medium | Extensive mock-based testing; validate on hardware in later phase |
| Feature parity with C version | Low | Track features via feature flags; start minimal, add incrementally |

## Estimated Scope

- **Protocol FFI definitions:** ~1,500 lines
- **Core data structures:** ~800 lines
- **Component + Driver Binding:** ~400 lines
- **Enumeration:** ~2,000 lines
- **Resource allocation:** ~1,500 lines
- **PCI I/O Protocol:** ~1,200 lines
- **Supporting features:** ~1,500 lines
- **Tests:** ~2,000 lines
- **Documentation:** ~300 lines
- **Total estimated:** ~11,200 lines of Rust

This is notably smaller than the C original (~19,400 lines) due to Rust's expressiveness, removal
of boilerplate (error handling macros, manual memory management), and use of standard library
collections.
