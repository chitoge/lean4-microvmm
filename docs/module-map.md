# Module map

This map points to the current stable module responsibilities.

## Public entry points

- `Main.lean`: executable entry point and CLI dispatch.
- `Microvmm.lean`: runtime facade for probes, Linux boot entry points, and user-facing diagnostics.
- `Microvmm/Proof.lean`: public proof index that re-exports the current proof modules.

## Core types and shared utilities

- `Microvmm/Common.lean`: shared numeric and byte helpers used across the repo.
- `Microvmm/Outcome.lean`: explicit result type used by validation-heavy code paths.
- `Microvmm/Core/Address.lean`: typed wrappers for guest-physical, MMIO, and I/O addresses.
- `Microvmm/Boot.lean`, `Microvmm/Host.lean`, `Microvmm/Linux.lean`, and `Microvmm/Model.lean`: compatibility facades that preserve a stable top-level import surface while the implementation stays split into smaller modules.

## Host boundary and KVM layer

- `Microvmm/FFI.lean`: raw extern declarations.
- `ffi/shim.c`: trusted C boundary for syscalls, ioctls, mmaps, and packed guest-memory helpers.
- `Microvmm/Kvm/Types.lean`: typed wrappers for KVM resources, exits, and error stages.
- `Microvmm/Kvm/Resource.lean`: VM, VCPU, run-area, and guest-memory lifetime management.
- `Microvmm/Kvm/VcpuSetup.lean`: guest-agnostic protected-mode VCPU setup helpers.

## Host console and operator I/O

- `Microvmm/Host/SerialModel.lean`: UART and serial replay state models.
- `Microvmm/Host/ConsoleTypes.lean`: persistent handle and runtime record types.
- `Microvmm/Host/ConsoleRuntime.lean`: pure client-queue and replay-seeding behavior.
- `Microvmm/Host/ConsoleHandles.lean`: host-handle orchestration around the pure runtime state.
- `Microvmm/Host/Stdio.lean`, `Microvmm/Host/Socket.lean`, and `Microvmm/Host/WakeTimer.lean`: actual host-side transport drivers.

## Bus and platform routing

- `Microvmm/Bus/Pci.lean`: PCI config routing and passive config reads.
- `Microvmm/Bus/Mmio.lean`: passive LAPIC MMIO handling.
- `Microvmm/Bus/Platform.lean`: Linux platform routing and fixed virtio-pci placement.

## Guest Linux subsystem

- `Microvmm/Guest/Linux/Cli.lean`: parse and validate boot requests.
- `Microvmm/Guest/Linux/Image.lean`: bzImage and initrd parsing and validation.
- `Microvmm/Guest/Linux/Plan.lean`: pure boot plan records, typed boot writes, fixed layout constants, and the normalized final-write view used by placement proofs.
- `Microvmm/Guest/Linux/Console.lean`: serial transcript capture and readiness detection.
- `Microvmm/Guest/Linux/Platform.lean`: Linux runtime state that combines serial and virtio-pci platform state, now with proof-facing BAR action and explicit MMIO-access helpers above the host MMIO read.
- `Microvmm/Guest/Linux/Runtime.lean`: bounded Linux boot and interactive run loops, now exposing proof-facing loop and interactive-transport state for the virtio MMIO branch proofs.

## Virtio device and transport code

- `Microvmm/Device/Virtio/Core.lean`: shared virtio status machine, feature negotiation, queue activation, and queue immutability tracking.
- `Microvmm/Device/Virtio/Rng.lean`: seeded pseudorandom entropy completion against guest memory, including the explicit PRNG state, pure completion plan, and proof-facing completion write trace consumed by the live executor and its per-write Lean guest-write wrappers.
- `Microvmm/VirtioMmio.lean`: fixed MMIO transport used by the standalone entropy probe, now with an explicit decoded write helper (`virtioMmioWriteOffset`), explicit MMIO shell helpers (`handleVirtioMmioAccess`, `handleVirtioMmioExit`), and the bounded standalone loop entry (`runVirtioEntropyLoop`) exposed for proof.
- `Microvmm/VirtioPci.lean`: modern PCI transport exposed to the Linux guest, now with an explicit decoded BAR write helper (`virtioPciBarWriteOffset`) that captures transport behavior after BAR decoding.

## Proof surface

- `Microvmm/Proof/Kvm/Resource.lean`: thin wrapper theorems showing that the KVM guest-read, guest-write, MMIO-observer, IRQ, and run-entry helpers used by the virtio path are direct decoders over the raw FFI calls.
- `Microvmm/Proof/Kvm/RawBoundary.lean`: explicit contract packaging for the remaining raw FFI/shim boundary used by the proved virtio `processQueue` path.
- `Microvmm/Proof/Serial/Replay.lean`: replay-buffer size and representation facts.
- `Microvmm/Proof/Host/ConsoleRuntime.lean`: console backlog bounds and client-attachment structure.
- `Microvmm/Proof/Linux/Console.lean`: monotonicity of probe and interactive readiness.
- `Microvmm/Proof/Linux/BootPlan.lean`: fixed boot-plan span facts plus whole-plan non-overlap and in-range theorems over the normalized final-write view.
- `Microvmm/Proof/Linux/Platform.lean`: Linux virtio-pci BAR action, explicit-access MMIO routing, and MMIO-exit refinements that recover the real virtio-rng executor trace and its realization by the Lean guest-write wrappers, plus additive Linux-facing corollaries that preserve the packaged `descriptorValidForDevice` judgment across the real `processQueue` path.
- `Microvmm/Proof/Linux/Runtime.lean`: one-step Linux serial and interactive run-loop MMIO `processQueue` refinements up to the named raw boundary, with console preservation and recovered executor reports over the real virtio-pci BAR path, plus thin runtime corollaries that thread the same packaged descriptor-validity judgment through those one-step Linux branches.
- `Microvmm/Proof/Virtio/Core.lean`: live-queue preservation facts for post-activation queue size, ready, and address writes.
- `Microvmm/Proof/Virtio/Cve2026_5747.lean`: CVE-focused corollaries for the mutation-after-activation bug class.
- `Microvmm/Proof/Virtio/Mmio.lean`: decoded MMIO write-path corollaries for queue immutability, virtio-rng DMA-target stability, direct descriptor-validity preservation across decoded post-activation queue writes, notify-then-execute refinement, explicit-access and MMIO-exit executor-report recovery, and the one-step run-loop MMIO shell up to the named raw boundary above the raw KVM observers.
- `Microvmm/Proof/Virtio/Pci.lean`: decoded PCI BAR/common-config write-path corollaries for the same queue safety properties, direct descriptor-validity preservation across decoded post-activation queue writes, plus notify-then-execute refinement.
- `Microvmm/Proof/Virtio/Rng.lean`: virtio-rng DMA target stability facts, an activation-side `queueShapeValid` theorem for successful queue activation, packaged queue-geometry and descriptor-validity invariants for the accepted request shape, a preserved-live-queue equivalence theorem showing the same observed descriptor request cannot be reclassified by post-activation queue writes, the pure completion-plan theorem for one queue, one bounded completion, one descriptor-length seeded payload, one-step PRNG progress, and new proof-facing packages for executor-read and completion-write regions that stay inside already-validated queue/payload spans.
- `Microvmm/Proof/Virtio/RngExecution.lean`: executor-level virtio-rng refinement facts showing that the real completion path emits exactly the proved write trace, installs the proved next PRNG state, and realizes that trace through the Lean `guestWriteU*` wrappers before the raw shim boundary.
