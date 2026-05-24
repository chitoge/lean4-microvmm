# Microvmm

Microvmm is a Lean 4 micro-VMM for x86_64 Linux/KVM. It keeps the trusted C shim small and moves Linux boot policy, virtio device semantics, and proof-facing invariants into Lean.

Today the project is intentionally narrow:

- one Linux guest path
- one virtio-rng device
- one documented external runtime surface: interactive Linux boot with the repository's initrd over the serial console
- one proof surface aimed at making the virtio execution path readable to proof engineers

The runtime entry point is `import Microvmm` and the top-level proof entry point is `import Microvmm.Proof`.

## What you can do here

- Build the runtime and the current proof surface.
- Boot the provided Linux guest with the provided initrd and interact with it over COM1.
- Inspect a proof tree that currently focuses on virtio queue immutability, accepted-request validity, exact virtio-rng completion shape, and bounded guest-memory accesses up to the named raw boundary.

## Quick start

Requirements:

- Linux x64 host
- `/dev/kvm` accessible to the current user
- Lean toolchain from `lean-toolchain`
- standard build tools for Lean, Linux kernel, and BusyBox builds

Build the project and the guest artifacts:

```sh
lake build
lake build Microvmm.Proof # for checking the proofs only
bash support/kernel/build-linux-bzimage.sh 7.0
bash support/initrd/build-initrd.sh
```
Or you can download the prebuilt artifacts from a tagged GitHub Release. Ordinary CI runs also upload the same files as workflow artifacts.

Run the documented interactive guest path:

```sh
lake env ./.lake/build/bin/microvmm linux \
  --kernel artifacts/kernel/linux-7.0-microvmm-bzImage \
  --initrd artifacts/initrd/microvmm-initrd.cpio.gz \
  --interactive
```

When boot succeeds, the initrd emits `MICROVMM_INITRD_READY` and the guest is ready for interactive input.

## Read next

- [Proof engineer guide](docs/proof-engineer-guide.md): current claims, assumptions, and where to start in `Microvmm/Proof.lean`
- [Build and run](docs/build-and-run.md): host requirements, artifact policy, build commands, and interactive run modes
- [Virtio guide](docs/virtio.md): executable virtio contract and claim-by-claim status
- [Proof roadmap](docs/proof-roadmap.md): module-by-module proof surface
- [Architecture](docs/architecture.md): subsystem layout and trusted boundary
- [Module map](docs/module-map.md): where implementation and proof modules live

## Scope

Microvmm does not currently aim to be a general-purpose VMM. The current code and proofs are scoped to one Linux/KVM bring-up path and one virtio-rng device so that the implementation and the proof story stay close to the live execution path.

The current CI workflow publishes the default Linux x64 Lean build; it does not force a static link. Tagged `v*` pushes also publish the staged host binary, kernel, and initrd files as GitHub Release assets.