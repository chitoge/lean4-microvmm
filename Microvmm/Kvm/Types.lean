import Microvmm.Outcome

namespace Microvmm.Kvm

inductive Stage where
  | openDev
  | getApiVersion
  | createVm
  | createVcpu
  | getVcpuMmapSize
  | probeRunArea
  | openKernelImage
  | readKernelImage
  | openInitrdImage
  | readInitrdImage
  | pollHostStdin
  | writeHostStdout
  | openConsoleListener
  | acceptConsoleClient
  | readConsoleClient
  | writeConsoleClient
  | openSerialLog
  | writeSerialLog
  | writeHostStderr
  | enableHostWakeTimer
  | disableHostWakeTimer
  | unlinkConsoleSocket
  | parseKernelImage
  | allocGuestMemory
  | registerGuestMemory
  | createIrqChip
  | createPit2
  | setTssAddr
  | configureCpuid
  | getSregs
  | setSregs
  | setRegs
  | mapRunArea
  | runGuest
  | verifyIoExit
  | verifyTranscript
  | verifyInteractiveSession
  | loadGuestCode
  | verifyMmioExit
  | verifyQueueState
  | verifyGuestResult
  | unmapRunArea
  | unregisterGuestMemory
  | freeGuestMemory
  | closeConsoleListener
  | closeConsoleClient
  | closeVcpu
  | closeVm
  | closeDev
deriving Repr, DecidableEq

structure Error where
  stage : Stage
  errno : UInt32
deriving Repr, DecidableEq

abbrev Result (α : Type) := Outcome Error α

structure Kvm where
  fd : UInt32
deriving Repr, DecidableEq

structure Vm where
  fd : UInt32
deriving Repr, DecidableEq

structure Vcpu where
  fd : UInt32
deriving Repr, DecidableEq

structure VmContext where
  kvm : Kvm
  vm : Vm
  apiVersion : UInt32
  runAreaSize : UInt32
deriving Repr, DecidableEq

structure VcpuContext where
  vmContext : VmContext
  id : UInt32
  vcpu : Vcpu
deriving Repr, DecidableEq

def VcpuContext.kvm (context : VcpuContext) : Kvm :=
  context.vmContext.kvm

def VcpuContext.vm (context : VcpuContext) : Vm :=
  context.vmContext.vm

def VcpuContext.apiVersion (context : VcpuContext) : UInt32 :=
  context.vmContext.apiVersion

def VcpuContext.runAreaSize (context : VcpuContext) : UInt32 :=
  context.vmContext.runAreaSize

class HasRawFd (α : Type) where
  rawFd : α → UInt32

instance : HasRawFd Kvm := ⟨Kvm.fd⟩

instance : HasRawFd Vm := ⟨Vm.fd⟩

instance : HasRawFd Vcpu := ⟨Vcpu.fd⟩

structure GuestMemory where
  handle : UInt64
  size : UInt64
deriving Repr, DecidableEq, BEq, Inhabited

structure RunArea where
  handle : UInt64
  size : UInt32
deriving Repr, DecidableEq, BEq, Inhabited

structure VcpuStateBuffer where
  handle : UInt64
deriving Repr, DecidableEq, BEq, Inhabited

end Microvmm.Kvm