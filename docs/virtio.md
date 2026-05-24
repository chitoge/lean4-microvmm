# Virtio guide

This document describes the current virtio surface. It explains both the executable contract and the hardening choices behind it. For subsystem structure, see [architecture](architecture.md). For the current proof surface, see [proof-roadmap](proof-roadmap.md).

## Current assumptions

| Aspect | Current contract | Why it is narrow |
| --- | --- | --- |
| Device type | One virtio-rng device | The goal is to make one small device understandable before adding broader device coverage. |
| Feature negotiation | The host offers only `VIRTIO_F_VERSION_1` | This keeps the negotiated surface deterministic and easy to audit. |
| Queue shape | Queue 0 only, split ring, size 1 | The current rng path does not need multiple queues or larger ring geometry. |
| Descriptor shape | One writable descriptor, no indirect descriptors, no chained requests | The implementation rejects more general queue shapes instead of silently accepting them. |
| Device-specific config | None | Virtio-rng does not need a richer device-specific register surface in this slice. |
| Returned data | Descriptor-length seeded pseudorandom bytes, with stream prefix `96 6f a6 57 b7 ad 3d 99 ...` | The standalone probe sees a reproducible prefix, while later bytes still advance explicit PRNG state across accepted requests. |

## Shared core versus transport adapters

- `Microvmm/Device/Virtio/Core.lean` owns the shared virtio state machine: feature selectors, driver features, status transitions, queue activation, queue latching, and mutation tracking.
- `Microvmm/Device/Virtio/Rng.lean` owns seeded pseudorandom request completion against guest memory, including the explicit PRNG state, the pure completion plan, and the pure completion write trace that the live executor sends through the Lean `guestWriteU*` wrappers.
- `Microvmm/VirtioMmio.lean` is the standalone modern MMIO transport. It exposes one device at fixed guest physical address `0x0d000000`, is used by the default entropy probe, factors its decoded write behavior through `virtioMmioWriteOffset`, and now also exposes `handleVirtioMmioAccess`, `handleVirtioMmioExit`, and `runVirtioEntropyLoop` so the proof layer can talk about the same observed-access and loop control points the runtime executes after the host MMIO read.
- `Microvmm/VirtioPci.lean` is the modern PCI transport. It exposes one function at bus `0`, device `1`, function `0`, with one BAR and the common, notify, ISR, and device capability windows that Linux expects, and now factors decoded BAR writes through `virtioPciBarWriteOffset` for the same reason.
- `Microvmm/Bus/Platform.lean` routes Linux PCI config cycles and BAR MMIO traffic into that PCI transport instead of hiding the transport inside the Linux runtime itself, while `Microvmm/Guest/Linux/Platform.lean` and `Microvmm/Guest/Linux/Runtime.lean` now expose proof-facing BAR/MMIO and loop control points above the host MMIO read, IRQ pulse, and KVM exit dispatch.

This split matters because the device logic lives in one place while MMIO and PCI stay as thin register-translation layers.

## Seeded pseudorandom rng behavior

- The host now carries explicit virtio-rng PRNG state in `VirtioDeviceState` and advances it on each accepted request.
- The current generator is `xoshiro256**`, initialized from a fixed root seed through the standard `SplitMix64` state expansion. It is pseudorandom by seed, not host-nondeterministic.
- The default root seed is chosen so the entropy stream begins with `96 6f a6 57 b7 ad 3d 99 3a f9 74 40 80 5b 65 45 8f d8 03 3c da 58 b0 9f 16 87 95 c3 5b 58 81 32`, which keeps the standalone probe's first 8 bytes reproducible. Linux may consume earlier virtio-rng output before `/init` reads `/dev/hwrng`, so the guest initrd check validates advancing output rather than assuming offset 0.
- Each accepted request writes exactly its descriptor length, and longer reads consume as many seeded eight-byte PRNG chunks as needed to fill that buffer.
- Later requests and later portions of the same longer read produce different bytes because the PRNG state advances across each generated chunk.

## Queue immutability and hardening

The most important virtio hardening choice in this repository is that queue configuration becomes immutable once the guest sets `QueueReady = 1`.

- Before activation, the guest writes queue size and descriptor, available, and used-ring addresses into a staged queue draft.
- At activation time, the draft is validated and copied into the authoritative active and latched queue state.
- After activation, later guest writes do not change the live queue. They are recorded only as attempted mutations.
- Completion logic uses the latched queue, not the rewritten values.
- Final validation checks that completion happened through the original queue and that the deliberately bogus rewritten addresses remained unused.

This is a direct defense against a class of virtio bugs in which a driver or malicious guest rewrites queue geometry or ring addresses after the device appears configured. If a VMM accepts those rewrites too late, descriptor interpretation can move to attacker-chosen memory. Microvmm hardens that edge by latching the queue once and treating later rewrites as evidence, not authority.

The current proof surface now makes that hardening argument explicit.

For an entry point that matches the public claims in this document, start with
`Microvmm/Proof.lean`. It now re-exports top-level theorem names for the main queue-immutability,
descriptor-validity, bounded-access, executor-refinement, and Linux-runtime refinement claims
before you descend into the detailed proof modules.

- `Microvmm/Proof/Virtio/Core.lean` proves that successful post-activation queue size, ready, and address writes preserve the live queue.
- `Microvmm/Proof/Virtio/Cve2026_5747.lean` packages those facts into the mutation-after-activation argument for the Firecracker CVE-2026-5747 bug class.
- `Microvmm/Proof/Virtio/Mmio.lean` and `Microvmm/Proof/Virtio/Pci.lean` now lift those shared proofs through the real decoded MMIO and PCI write-path helpers, including direct transport-level preservation theorems for the packaged descriptor-validity judgment on post-activation queue-register writes, and they also connect the decoded notify branches to the real rng executor plus its Lean guest-write-wrapper realization.
- `Microvmm/Proof/Linux/Platform.lean` lifts the Linux BAR action and explicit MMIO BAR route one step higher again, and now also threads the packaged `descriptorValidForDevice` judgment from the post-write PCI transport state through the real `processQueue` executor path.
- `Microvmm/Proof/Linux/Runtime.lean` packages the successful Linux serial and interactive MMIO `processQueue` branches up to the remaining raw boundary by recovering the MMIO-exit witness, console preservation, and executor report instead of claiming a stale whole-loop equality, and it now carries the same packaged descriptor-validity judgment through those one-step Linux run-loop branches.
- `Microvmm/Proof/Virtio/Rng.lean` proves that successful activation establishes the current accepted queue shape, that the seeded virtio-rng completion path computes its avail, used, and descriptor DMA targets from the active queue, that a successful pure completion plan always produces one bounded completion whose payload length matches the descriptor-requested length, and that the concrete executor read/write offsets for that accepted shape stay inside already-validated queue/payload regions.
- `Microvmm/Proof/Virtio/RngExecution.lean` proves that the real executor used by both MMIO and PCI emits exactly the pure completion write trace derived from that plan, installs the plan's next PRNG state, and realizes that trace through the Lean `guestWriteU*` wrappers.
- `Microvmm/Proof/Kvm/Resource.lean` names the last Lean-side step explicitly by proving that those guest-write wrappers, MMIO observers, IRQ helpers, and run-entry helpers are just thin decoders over the raw FFI calls, and `Microvmm/Proof/Kvm/RawBoundary.lean` packages that remaining raw contract as the still-trusted FFI/shim edge.

The executor-facing and runtime-facing theorems are now phrased as `IOResultRunsTo` witnesses on the real IO actions. The stale runtime/MMIO whole-loop equalities were intentionally pruned; the surviving proof surface stops at explicit MMIO-exit witnesses, recovered executor reports, and the named raw boundary.

That last point matters because the virtio proofs no longer stop at an abstract plan or only at transport wrapper helpers. The active VM execution path now goes through decoded MMIO/PCI write helpers, then the standalone or Linux explicit-access shell, then a one-step MMIO-exit/run-loop witness, and then a report-producing executor whose concrete write trace is proved to flow through the Lean `guestWriteU*` wrappers. The repo now also names the remaining raw contract explicitly instead of leaving it implicit. On that virtio execution path, the remaining trusted base is the raw FFI/shim boundary and Lean runtime semantics, not an unproved Lean control-flow layer above it. What remains unproved is liveness across fully general exit traces and the raw shim behavior itself, not the Lean-side virtio dispatch path.

## Other safety checks already implemented

- Descriptor tables, available rings, and used rings must all fit inside guest RAM before they are touched.
- The queue head must stay within the single configured queue.
- The descriptor must be writable and must not set `NEXT` or `INDIRECT`.
- The descriptor's requested payload span must fit entirely inside guest RAM before any device write occurs.
- The used-ring update is bounds-checked and advances only one guest-visible completion.
- On PCI, Linux sees a plausible modern transport surface, including BAR sizing, common configuration, notify capability, ISR handling, and a minimal host bridge needed for direct PCI probing.

## Claim-by-claim status

The list below answers a natural external-reader question: which stronger virtio claims are already
proved here, which are only covered in the repo's current narrow virtio-rng model, and which are
not yet proved at all.

`Microvmm/Proof.lean` now exports claim-shaped top-level theorems for the positive and partial
rows below. For the `No` rows, it instead records that no such top-level theorem exists yet and
the table explains the current gap.

| Claim | Status | Where to check | Current precise reading |
| --- | --- | --- | --- |
| Virtio queue structural safety: every reachable descriptor chain terminates, with no cycles and bounded traversal | Partial | `Microvmm/Device/Virtio/Rng.lean`, `Microvmm/Proof/Virtio/Rng.lean` | Covered only for the currently accepted virtio-rng request shape: queue size is fixed to `1`, the accepted descriptor must be writable, `NEXT` and `INDIRECT` are rejected, and `descNext = 0`. That makes the accepted chain length exactly one. There is not yet a general theorem over arbitrary reachable descriptor chains. |
| Queue transitions preserve descriptor validity invariants: indices stay in bounds, descriptors reference legal memory regions, and malformed chains cannot become validated later | Yes | `Microvmm/Proof/Virtio/Core.lean`, `Microvmm/Proof/Virtio/Rng.lean`, `Microvmm/Proof/Virtio/{Mmio,Pci}.lean`, `Microvmm/Proof/Linux/{Platform,Runtime}.lean` | `Microvmm/Proof/Virtio/Rng.lean` now packages `queueShapeValid`, `queueGeometryInvariants`, `descriptorValidityInvariants`, and `descriptorValidForDevice`. `writeQueueReady_one_establishes_queueShapeValid` records the activation-side queue-shape fact the core can honestly establish; `buildDeterministicEntropyCompletionPlan_encodes_validity` proves that any successful accepted virtio-rng request satisfies the queue-geometry, head-bound, flag, non-chaining, and payload-span checks; `descriptorValidForDevice_iff_preserved_queue`, together with the post-activation `preservesLiveQueue` lemmas from `Microvmm/Proof/Virtio/Core.lean`, proves queue-register writes cannot later reclassify that same observed request; `Microvmm/Proof/Virtio/{Mmio,Pci}.lean` lift that packaged judgment directly through the decoded MMIO and PCI queue-write paths; and `Microvmm/Proof/Linux/{Platform,Runtime}.lean` now carry the same judgment through the Linux BAR/MMIO `processQueue` shells. Narrowness: this is still the current accepted virtio-rng shape only (queue size `1`, single writable non-`NEXT`, non-`INDIRECT` descriptor). |
| A descriptor is never simultaneously owned by both guest and device, as a linear capability discipline | No | no current proof module | The repo does not yet model descriptor ownership or linear capabilities explicitly, so there is no current proof of this property. |
| After activation, queue configuration is immutable | Yes | `Microvmm/Proof/Virtio/Core.lean`, `Microvmm/Proof/Virtio/Cve2026_5747.lean`, `Microvmm/Proof/Virtio/{Mmio,Pci}.lean` | This is one of the strongest current proof stories: successful post-activation queue size, ready, and address writes preserve the live and latched queue, and the transport proofs lift that fact through the real MMIO and PCI entry points. |
| All queue state transitions follow the lifecycle graph | No | `Microvmm/Device/Virtio/Core.lean` implements the checks, but there is no proof module yet | The implementation enforces a narrow status/activation discipline through `handleStatusWrite`, `validateQueueDraft`, and `writeQueueReady`, but there is not yet an explicit proof that all reachable queue/device state transitions follow a named lifecycle graph. |
| For virtio-rng, every valid request eventually completes | No | `Microvmm/Proof/Virtio/Mmio.lean`, `Microvmm/Proof/Linux/Runtime.lean` show only the current branch mechanics | The current proofs stop at one-step MMIO-exit and run-loop `processQueue` witnesses up to the named raw boundary, with recovered executor reports for the successful branch. They do not yet prove that every valid request will eventually reach completion under the actual run loops. |
| For virtio-rng, the device writes exactly the requested buffer length | Yes | `Microvmm/Device/Virtio/Rng.lean`, `Microvmm/Proof/Virtio/Rng.lean`, `Microvmm/Proof/Virtio/RngExecution.lean` | In the current accepted virtio-rng request shape, the pure planner proves `completedLen = descLen` and `payload.length = descLen`, and the executor proof ties the real write trace back to that plan. The remaining narrowness is in queue shape, not in the completed byte count. |
| All device memory accesses remain within validated guest regions | Yes | `Microvmm/Common.lean`, `Microvmm/Device/Virtio/Rng.lean`, `Microvmm/Proof/Virtio/{Rng,RngExecution}.lean`, `Microvmm/Proof/Kvm/{Resource,RawBoundary}.lean` | For the current accepted virtio-rng request shape, `Microvmm/Proof/Virtio/Rng.lean` now packages one theorem for executor reads and one theorem for completion writes, each phrased as “already-validated base region” plus “concrete offsets touched by the real path fit inside that region.” `Microvmm/Proof/Virtio/RngExecution.lean` ties the live executor back to the same completion plan and write trace, and `Microvmm/Proof/Kvm/{Resource,RawBoundary}.lean` keep the remaining shim/FFI boundary explicit. Narrowness: this is still only the current accepted virtio-rng shape and the successful completion path up to the named raw boundary, not a general theorem over arbitrary virtio devices or arbitrary failing traces. |

## MMIO versus PCI in plain language

- The MMIO probe is the smallest transport path. It is good for focused device bring-up because every access arrives as a visible KVM MMIO exit.
- The PCI path is the realistic Linux-facing path. It adds config-space identity, BAR programming, and capability discovery, but it still delegates queue and completion rules to the same core implementation.

## What this slice does not cover

Microvmm does not yet implement multi-queue devices, packed rings, indirect descriptors, chained requests, MSI or MSI-X, hotplug, migration, or non-rng virtio devices. Those are intentionally outside the current proof and bring-up target.