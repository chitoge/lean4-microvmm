# Guest Linux guide

This document describes the documented Linux guest contract. It is written for operators, implementers, and proof readers. For subsystem structure, see [architecture](architecture.md). For the module layout behind this path, see [module-map](module-map.md).

## What the public Linux path does

`microvmm linux` boots one Linux bzImage on KVM together with the BusyBox initrd built in this repository, watches the serial transcript, verifies that the guest reached the expected virtio-pci rng checks, and then hands control to an interactive serial console.

## Boot contract

- The documented form is `microvmm linux --interactive --kernel PATH --initrd PATH`.
- Interactive boot always requires an initrd and is the only runtime surface documented for external users.
- Server-backed interactive mode requires both `--console-socket PATH` and `--serial-log PATH`.
- The validated artifact build writes the guest kernel to `artifacts/kernel/linux-7.0-microvmm-bzImage` and the initrd to `artifacts/initrd/microvmm-initrd.cpio.gz`.
- If `--cmdline` is omitted, the current default is `console=ttyS0,115200 earlyprintk=serial,ttyS0,115200 ignore_loglevel nokaslr`.

## Image and memory contract

- The bzImage parser expects a Linux bzImage with boot protocol version 2.10 or later.
- The image must advertise the normal high-loaded kernel path and command-line support.
- The planner requires enough guest memory for the kernel header's advertised `init_size` window.
- Guest RAM is currently fixed at 64 MiB.
- The current fixed boot layout places boot parameters at `0x10000`, the command line at `0x20000`, and the kernel at `0x100000`.
- If an initrd is present, it is loaded on page alignment and passed through the low and high Linux boot-parameter fields.
- Protected-mode VCPU setup lives under `Microvmm/Kvm/VcpuSetup.lean` rather than inside the Linux guest planner.

## Runtime contract

- The Linux path runs through a bounded `KVM_RUN` loop.
- COM1 serial output is the primary observable guest channel.
- Serial transcript readiness is latched. Once readiness is seen, later bytes cannot clear it.
- Passive platform accesses are intentionally narrow: bounded passive port I/O and passive LAPIC MMIO are accepted, while unsupported shapes fail explicitly.
- Interactive success is based on seeing the initrd readiness marker `MICROVMM_INITRD_READY`.

## Initrd verification markers

The BusyBox-based `/init` script under `support/initrd/init.busybox.sh` emits stable markers so the host and the serial log can verify that the guest really reached the intended virtio-rng path.

- `MICROVMM_VIRTIO_PCI_SYSFS_OK ...`: the fixed virtio device is visible at `0000:00:01.0` with vendor `0x1af4` and device `0x1044`.
- `MICROVMM_VIRTIO_RNG_SOURCE_OK ...`: Linux selected `virtio_rng` as the active hardware RNG source.
- `MICROVMM_VIRTIO_RNG_BYTES_OK bytes=...`: `/dev/hwrng` returned a full 32-byte sample from `virtio_rng`, and the four 8-byte chunks in that sample were all distinct. Linux can consume deterministic virtio-rng output before `/init` runs, so this marker checks that the guest sees advancing device output instead of a stale repeated chunk at a fixed stream offset.
- `MICROVMM_VIRTIO_GUEST_VERIFY_OK`: the guest-side virtio verification sequence finished successfully.
- `MICROVMM_INITRD_READY`: the initrd is ready for operator input.
- Each of those checks also has a corresponding `_FAIL` form so failures are visible in the serial transcript instead of being silent hangs.

Once the interactive BusyBox shell is up, `virtio-rng-read N` reads exactly `N` bytes from `/dev/hwrng` and prints them as space-separated lowercase hex bytes. It exits non-zero on an invalid byte count, a missing `hwrng` device, or a short read.

## Operator-facing run modes

1. Interactive boot on host stdio.

```sh
lake env ./.lake/build/bin/microvmm linux \
  --kernel artifacts/kernel/linux-7.0-microvmm-bzImage \
  --initrd artifacts/initrd/microvmm-initrd.cpio.gz \
  --interactive
```

2. Interactive boot with a Unix socket and persistent serial log.

```sh
lake env ./.lake/build/bin/microvmm linux \
  --kernel artifacts/kernel/linux-7.0-microvmm-bzImage \
  --initrd artifacts/initrd/microvmm-initrd.cpio.gz \
  --interactive \
  --console-socket /tmp/microvmm-console.sock \
  --serial-log /tmp/microvmm-serial.log
```

In server-backed mode, the serial log captures output from the first boot byte onward, and Unix-socket clients receive the same serial stream. A client such as `socat -,rawer,echo=0 UNIX-CONNECT:/tmp/microvmm-console.sock` can attach to that stream.

## What this path is not trying to do

The Linux guest path is deliberately narrow. It is designed to make one serially observable Linux boot and one interactive initrd flow understandable, testable, and provable before broader platform coverage or additional devices are added.