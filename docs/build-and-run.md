# Build and run

This document covers the documented operator path for Microvmm and the commands used to check the proof surface.

## Host requirements

- Linux x64 host.
- `/dev/kvm` present and accessible to the current user.
- Lean toolchain from `lean-toolchain`.
- Standard build tools for Lean, Linux kernel, and BusyBox builds.

## Artifact policy

- Generated host binaries and guest images are not source-controlled in this repository.
- GitHub Actions builds and uploads the Linux x64 host binary, the guest bzImage, and the guest initrd as workflow artifacts on ordinary CI runs.
- Pushing a `v*` tag publishes the same staged files as GitHub Release assets.
- The provided host binary artifact is built on Linux x64 runners and should be treated as Linux x64-only.
- The current CI workflow publishes the default Linux x64 Lean build and does not force a static link.

## Local build

```sh
lake build
lake build Microvmm.Proof
lake build microvmm-test
lake env ./.lake/build/bin/microvmm-test
bash support/kernel/build-linux-bzimage.sh 7.0
bash support/initrd/build-initrd.sh
```

`lake build Microvmm.Proof` is the command that checks the current proof surface.

## Interactive run

The documented runtime surface is interactive Linux boot with the repository's initrd.

1. Host stdio mode.

```sh
lake env ./.lake/build/bin/microvmm linux \
  --kernel artifacts/kernel/linux-7.0-microvmm-bzImage \
  --initrd artifacts/initrd/microvmm-initrd.cpio.gz \
  --interactive
```

2. Unix-socket console mode with a persistent serial log.

```sh
lake env ./.lake/build/bin/microvmm linux \
  --kernel artifacts/kernel/linux-7.0-microvmm-bzImage \
  --initrd artifacts/initrd/microvmm-initrd.cpio.gz \
  --interactive \
  --console-socket /tmp/microvmm-console.sock \
  --serial-log /tmp/microvmm-serial.log
```

When boot succeeds, the initrd emits `MICROVMM_INITRD_READY` and the guest is ready for interactive input.

## Checking proofs

Use the top-level proof target:

```sh
lake build Microvmm.Proof
```

If you want the reader-facing proof entry point after the build succeeds, start from `Microvmm/Proof.lean` and then follow the linked modules and docs.