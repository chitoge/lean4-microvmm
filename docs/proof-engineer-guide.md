# Proof Engineer Guide

This document is the shortest way to understand what Microvmm is claiming today without already being familiar with VMM or virtio implementation details.

## What this project is

Microvmm is a Lean 4 micro-VMM for x86_64 Linux/KVM. It runs one Linux guest, exposes one virtio-rng device, and keeps the trusted C boundary narrow: the shim does raw KVM, guest-memory, and host-IO work, while guest layout, device semantics, and proof-facing invariants live in Lean.

The documented external runtime surface is intentionally narrow: interactive Linux boot with the repository's initrd over the serial console. The internal probe paths still exist for development and proof support, but the reader-facing surface is the interactive initrd boot path.

## Minimal VMM and virtio primer

- A VMM enters the guest with `KVM_RUN`, observes exits, and decides how each exit should be handled.
- A split virtqueue has three guest-memory regions: a descriptor table, an avail ring written by the guest, and a used ring written by the device.
- In this repository, the accepted virtio-rng request shape is deliberately small: queue 0 only, queue size 1, one writable descriptor, no `NEXT`, and no `INDIRECT` descriptors.
- The interesting safety question is whether post-activation guest writes or malformed descriptors can make the device read or write the wrong guest memory. The current proofs target that question directly.

## What is claimed today

This is the same claim-by-claim view as [virtio](virtio.md), but rewritten to point readers
directly at the top-level theorem names exported by `Microvmm/Proof.lean`.

| Claim | Status | Start in `Microvmm/Proof.lean` | Current precise reading |
| --- | --- | --- | --- |
| Virtio queue structural safety: every reachable descriptor chain terminates, with no cycles and bounded traversal | Partial | `virtioQueueStructuralSafety_forAcceptedRngRequest` | Covered only for the currently accepted virtio-rng request shape: queue size is fixed to `1`, the accepted descriptor must be writable, `NEXT` and `INDIRECT` are rejected, and `descNext = 0`. That makes the accepted chain length exactly one. There is not yet a general theorem over arbitrary reachable descriptor chains. |
| Queue transitions preserve descriptor validity invariants: indices stay in bounds, descriptors reference legal memory regions, and malformed chains cannot become validated later | Yes | `virtioQueueActivationEstablishesAcceptedShape`, `virtioAcceptedRngRequestSatisfiesDescriptorValidityInvariants`, `virtioPreservedQueueTransitionPreservesDescriptorValidity`, `linuxPlatformProcessQueuePreservesDescriptorValidity`, `linuxSerialProcessQueueStepPreservesDescriptorValidity`, `linuxInteractiveProcessQueueStepPreservesDescriptorValidity` | The current proof surface packages `queueShapeValid`, `queueGeometryInvariants`, `descriptorValidityInvariants`, and `descriptorValidForDevice` for the accepted virtio-rng shape. Activation establishes the queue-shape fact; successful accepted requests satisfy the geometry, head-bound, flag, non-chaining, and payload-span checks; preserved live queues cannot reclassify the same observed request; and the Linux BAR/MMIO `processQueue` shells carry the same judgment through the runtime-facing path. Narrowness: this is still only the current accepted virtio-rng shape. |
| A descriptor is never simultaneously owned by both guest and device, as a linear capability discipline | No | no top-level theorem yet | The repo does not yet model descriptor ownership or linear capabilities explicitly, so there is no current proof of this property. |
| After activation, queue configuration is immutable | Yes | `virtioQueueConfigurationImmutableAfterActivation_queueNum`, `virtioQueueConfigurationImmutableAfterActivation_queueReady`, `virtioQueueConfigurationImmutableAfterActivation_queueAddress`, `virtioQueueConfigurationLatchedAfterActivation_queueNum`, `virtioQueueConfigurationLatchedAfterActivation_queueReady`, `virtioQueueConfigurationLatchedAfterActivation_queueAddress` | This is one of the strongest current proof stories: successful post-activation queue size, ready, and address writes preserve the live and latched queue. |
| All queue state transitions follow the lifecycle graph | No | no top-level theorem yet | The implementation enforces a narrow status/activation discipline through `handleStatusWrite`, `validateQueueDraft`, and `writeQueueReady`, but there is not yet an explicit proof that all reachable queue/device state transitions follow a named lifecycle graph. |
| For virtio-rng, every valid request eventually completes | No | weaker substitutes: `linuxPlatformProcessQueueRefines`, `linuxSerialProcessQueueStepRefinesUpToRawBoundary`, `linuxInteractiveProcessQueueStepRefinesUpToRawBoundary` | The current proofs stop at one-step MMIO-exit and run-loop `processQueue` witnesses up to the named raw boundary, with recovered executor reports for the successful branch. They do not yet prove that every valid request will eventually reach completion under the actual run loops. |
| For virtio-rng, the device writes exactly the requested buffer length | Yes | `virtioRngAcceptedRequestWritesExactlyRequestedBufferLength`, `virtioRngExecutorReportsPureCompletionTrace`, `virtioRngPublicCompletionRefinesPureCompletionTrace` | In the current accepted virtio-rng request shape, the pure planner proves `completedLen = descLen` and `payload.length = descLen`, and the executor proof ties the real write trace back to that plan. The remaining narrowness is in queue shape, not in the completed byte count. |
| All device memory accesses remain within validated guest regions | Yes | `virtioRngAcceptedRequestAccessesStayWithinValidatedRegions` | For the current accepted virtio-rng request shape, the proof packages one theorem for executor reads and one theorem for completion writes, each phrased as “already-validated base region” plus “concrete offsets touched by the real path fit inside that region.” Narrowness: this is still only the current accepted virtio-rng shape and the successful completion path up to the named raw boundary, not a general theorem over arbitrary virtio devices or arbitrary failing traces. |

## Assumptions and trusted boundary

- `ffi/shim.c` and the extern declarations in `Microvmm/FFI.lean` remain trusted. They perform raw ioctls, guest-memory reads and writes, and host IO.
- The current virtio execution proofs stop at the named raw boundary above those shim calls and above Lean runtime semantics.
- The Linux-facing theorems are successful-branch refinement theorems. They do not claim a full liveness result for arbitrary exit traces.
- The current proofs are about one virtio-rng device and one accepted request shape, not about arbitrary virtio devices or arbitrary descriptor chains.

## What is not claimed yet

- There is no current theorem for general descriptor-chain ownership or linear capabilities. `Microvmm/Proof.lean` intentionally leaves that row without a top-level theorem.
- There is no current theorem stating that all queue/device states follow a named lifecycle graph. `Microvmm/Proof.lean` intentionally leaves that row without a top-level theorem.
- There is no current liveness theorem that every valid request eventually completes under the real run loops. `Microvmm/Proof.lean` intentionally exports weaker successful-branch refinement theorems instead.
- There is no proof of the raw shim itself.

## Reading path

1. Read `Microvmm/Proof.lean` for the top-level theorem names.
2. Use the table above as the proof-oriented index, then read [virtio](virtio.md) for the executable contract and fuller narrative around each claim.
3. Read [proof-roadmap](proof-roadmap.md) for the detailed module-by-module proof surface.
4. Use [architecture](architecture.md) and [module-map](module-map.md) when you need to jump from a theorem to the owning implementation module.
5. Use [guest-linux](guest-linux.md) for the documented Linux/initrd runtime contract that the Linux-facing theorems talk about.