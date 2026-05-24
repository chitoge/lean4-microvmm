import Microvmm.Bus.Mmio
import Microvmm.Bus.Pci
import Microvmm.Bus.Platform
import Microvmm.Kvm
import Microvmm.Probe
import Microvmm.VirtioPci

namespace Microvmm

private def errnoSummary (errno : UInt32) : String :=
  match errno.toNat with
  | 1 => "EPERM, errno=1"
  | 2 => "ENOENT, errno=2"
  | 5 => "EIO, errno=5"
  | 9 => "EBADF, errno=9"
  | 11 => "EAGAIN, errno=11"
  | 12 => "ENOMEM, errno=12"
  | 13 => "EACCES, errno=13"
  | 14 => "EFAULT, errno=14"
  | 17 => "EEXIST, errno=17"
  | 19 => "ENODEV, errno=19"
  | 22 => "EINVAL, errno=22"
  | 32 => "EPIPE, errno=32"
  | 71 => "EPROTO, errno=71"
  | 75 => "EOVERFLOW, errno=75"
  | 98 => "EADDRINUSE, errno=98"
  | 104 => "ECONNRESET, errno=104"
  | 107 => "ENOTCONN, errno=107"
  | 95 => "EOPNOTSUPP, errno=95"
  | 110 => "ETIMEDOUT, errno=110"
  | code => s!"errno={code}"

def decodeErrno (err : Kvm.Error) : String :=
  match err.stage, err.errno.toNat with
  | .openDev, 1 => "/dev/kvm open denied (EPERM, errno=1): operation not permitted"
  | .openDev, 2 => "/dev/kvm not found (ENOENT, errno=2): device is unavailable on this host"
  | .openDev, 13 => "/dev/kvm open denied (EACCES, errno=13): user lacks read/write access"
  | .openDev, 19 => "/dev/kvm unavailable (ENODEV, errno=19): KVM support is not enabled"
  | .openDev, _ => s!"/dev/kvm open failed ({errnoSummary err.errno})"
  | .getApiVersion, _ => s!"KVM_GET_API_VERSION failed ({errnoSummary err.errno})"
  | .createVm, _ => s!"KVM_CREATE_VM failed ({errnoSummary err.errno})"
  | .createVcpu, _ => s!"KVM_CREATE_VCPU failed ({errnoSummary err.errno})"
  | .getVcpuMmapSize, _ => s!"KVM_GET_VCPU_MMAP_SIZE failed ({errnoSummary err.errno})"
  | .probeRunArea, _ => s!"KVM VCPU run-area probe failed ({errnoSummary err.errno})"
  | .openKernelImage, 2 => "kernel image open failed (ENOENT, errno=2): expected a Linux bzImage at the requested path"
  | .openKernelImage, _ => s!"kernel image open failed ({errnoSummary err.errno})"
  | .readKernelImage, _ => s!"kernel image read failed ({errnoSummary err.errno})"
  | .openInitrdImage, 2 => "initrd image open failed (ENOENT, errno=2): expected an initrd/initramfs image at the requested path"
  | .openInitrdImage, _ => s!"initrd image open failed ({errnoSummary err.errno})"
  | .readInitrdImage, _ => s!"initrd image read failed ({errnoSummary err.errno})"
  | .pollHostStdin, _ => s!"host stdin poll/read failed ({errnoSummary err.errno})"
  | .writeHostStdout, _ => s!"host stdout write failed ({errnoSummary err.errno})"
  | .openConsoleListener, 2 => "console socket open failed (ENOENT, errno=2): expected the parent directory for the requested socket path to exist"
  | .openConsoleListener, 17 => "console socket open failed (EEXIST, errno=17): the requested socket path already exists and is not a Unix socket"
  | .openConsoleListener, 98 => "console socket open failed (EADDRINUSE, errno=98): another listener is already bound at the requested path"
  | .openConsoleListener, _ => s!"console socket open failed ({errnoSummary err.errno})"
  | .acceptConsoleClient, _ => s!"console client accept failed ({errnoSummary err.errno})"
  | .readConsoleClient, _ => s!"console client read failed ({errnoSummary err.errno})"
  | .writeConsoleClient, _ => s!"console client write failed ({errnoSummary err.errno})"
  | .openSerialLog, _ => s!"serial log open failed ({errnoSummary err.errno})"
  | .writeSerialLog, _ => s!"serial log write failed ({errnoSummary err.errno})"
  | .writeHostStderr, _ => s!"host stderr write failed ({errnoSummary err.errno})"
  | .enableHostWakeTimer, _ => s!"interactive wake timer enable failed ({errnoSummary err.errno})"
  | .disableHostWakeTimer, _ => s!"interactive wake timer disable failed ({errnoSummary err.errno})"
  | .unlinkConsoleSocket, _ => s!"console socket cleanup failed ({errnoSummary err.errno})"
  | .parseKernelImage, 71 => "kernel image parse failed (EPROTO, errno=71): expected a Linux bzImage with boot protocol >= 2.10, LOAD_HIGH, command-line support, and enough guest RAM for the header-advertised init_size window"
  | .parseKernelImage, _ => s!"kernel image parse failed ({errnoSummary err.errno})"
  | .allocGuestMemory, _ => s!"guest memory allocation failed ({errnoSummary err.errno})"
  | .registerGuestMemory, _ => s!"KVM_SET_USER_MEMORY_REGION failed ({errnoSummary err.errno})"
  | .createIrqChip, _ => s!"KVM_CREATE_IRQCHIP failed ({errnoSummary err.errno})"
  | .createPit2, _ => s!"KVM_CREATE_PIT2 failed ({errnoSummary err.errno})"
  | .setTssAddr, _ => s!"KVM_SET_TSS_ADDR failed ({errnoSummary err.errno})"
  | .configureCpuid, _ => s!"KVM CPUID setup failed ({errnoSummary err.errno})"
  | .getSregs, _ => s!"KVM_GET_SREGS failed ({errnoSummary err.errno})"
  | .setSregs, _ => s!"KVM_SET_SREGS failed ({errnoSummary err.errno})"
  | .setRegs, _ => s!"KVM_SET_REGS failed ({errnoSummary err.errno})"
  | .mapRunArea, _ => s!"kvm_run mmap failed ({errnoSummary err.errno})"
  | .runGuest, _ => s!"KVM_RUN failed ({errnoSummary err.errno})"
  | .verifyIoExit, 71 => "guest Linux exit verification failed (EPROTO, errno=71): expected exact one-byte COM1 UART semantics on 0x3f8-0x3ff, bounded 1/2/4-byte passive port IO elsewhere, safe PCI config-data reads on 0xcfc-0xcff, and passive LAPIC MMIO handling on 0xfee00000-0xfee00fff"
  | .verifyIoExit, _ => s!"guest Linux exit verification failed ({errnoSummary err.errno})"
  | .verifyTranscript, 71 => "guest transcript verification failed (EPROTO, errno=71): guest stopped before emitting recognizable Linux serial boot text"
  | .verifyTranscript, 110 => "guest transcript verification timed out (ETIMEDOUT, errno=110): bounded KVM exit loop ended before Linux serial boot text was observed"
  | .verifyTranscript, _ => s!"guest transcript verification failed ({errnoSummary err.errno})"
  | .verifyInteractiveSession, 71 => "interactive Linux session failed (EPROTO, errno=71): guest halted before the initrd serial console became ready"
  | .verifyInteractiveSession, 110 => "interactive Linux session timed out (ETIMEDOUT, errno=110): bounded KVM exit loop ended before the initrd serial console became ready or the guest halted cleanly"
  | .verifyInteractiveSession, _ => s!"interactive Linux session failed ({errnoSummary err.errno})"
  | .loadGuestCode, 71 => "guest code setup failed (EPROTO, errno=71): expected the embedded protected-mode virtio-mmio probe image and fixed guest layout to fit inside probe RAM"
  | .loadGuestCode, _ => s!"guest code setup failed ({errnoSummary err.errno})"
  | .verifyMmioExit, 71 => "virtio-mmio exit verification failed (EPROTO, errno=71): expected modern virtio-mmio traffic for one entropy queue and no unexpected register accesses"
  | .verifyMmioExit, _ => s!"virtio-mmio exit verification failed ({errnoSummary err.errno})"
  | .verifyQueueState, 71 => "virtio queue state verification failed (EPROTO, errno=71): expected queue geometry and addresses to latch at QueueReady and remain unchanged despite later guest rewrites"
  | .verifyQueueState, _ => s!"virtio queue state verification failed ({errnoSummary err.errno})"
  | .verifyGuestResult, 71 => "guest result verification failed (EPROTO, errno=71): expected one completed entropy request carrying the default seeded host entropy stream"
  | .verifyGuestResult, 110 => "guest result verification timed out (ETIMEDOUT, errno=110): guest did not reach seeded virtio-rng completion before the bounded exit budget ended"
  | .verifyGuestResult, code => s!"guest result verification failed (probe code {code}): the embedded virtio-mmio probe guest rejected the observed device behavior"
  | .unmapRunArea, _ => s!"kvm_run munmap failed ({errnoSummary err.errno})"
  | .unregisterGuestMemory, _ => s!"guest memory unregister failed ({errnoSummary err.errno})"
  | .freeGuestMemory, _ => s!"guest memory munmap failed ({errnoSummary err.errno})"
  | .closeConsoleListener, _ => s!"console listener close failed ({errnoSummary err.errno})"
  | .closeConsoleClient, _ => s!"console client close failed ({errnoSummary err.errno})"
  | .closeVcpu, _ => s!"VCPU fd close failed ({errnoSummary err.errno})"
  | .closeVm, _ => s!"VM fd close failed ({errnoSummary err.errno})"
  | .closeDev, _ => s!"/dev/kvm close failed ({errnoSummary err.errno})"

def formatVirtioProbeSuccess (success : VirtioEntropySuccess) : String :=
  s!"KVM virtio-mmio entropy probe succeeded: API version {success.apiVersion.toNat}, payload {success.payloadSummary}, mmap size {success.runAreaSize.toNat} bytes"

def formatLinuxProbeSuccess (success : ProbeSuccess) : String :=
  s!"KVM Linux bzImage probe succeeded: API version {success.apiVersion.toNat}, transcript \"{success.transcriptExcerpt}\", mmap size {success.runAreaSize.toNat} bytes"

def probeMessage : IO String := do
  match ← probeVirtioMmioEntropy with
  | .ok success =>
      pure <| formatVirtioProbeSuccess success
  | .error err =>
      pure <| decodeErrno err

def probeLinuxBzImageMessage (request : LinuxProbeRequest := {}) : IO String := do
  match ← probeLinuxBzImageBoot request with
  | .ok success =>
    pure <| formatLinuxProbeSuccess success
  | .error err =>
    pure <| decodeErrno err

end Microvmm
