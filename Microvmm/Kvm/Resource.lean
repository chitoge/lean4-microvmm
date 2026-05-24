import Microvmm.FFI
import Microvmm.Core.Address
import Microvmm.Kvm.Types

namespace Microvmm.Kvm

private def packedProbeStageBase : Nat := 4096

private def packedReadBase : Nat := 4294967296

private def pointerErrorBase : UInt64 := 0xfffffffffffff000

private def kvmExitIoIn : UInt32 := 0

private def kvmExitIoOut : UInt32 := 1

private def eproto : UInt32 := 71

private def errnoOfStatus (status : Int32) : UInt32 :=
  UInt32.ofNat status.toInt.natAbs

private def valueOfStatus (status : Int32) : UInt32 :=
  UInt32.ofNat status.toInt.toNat

def decodeValueStatus (stage : Stage) (status : Int32) : Result UInt32 :=
  if status.toInt < 0 then
    .error ⟨stage, errnoOfStatus status⟩
  else
    .ok (valueOfStatus status)

def decodeUnitStatus (stage : Stage) (status : Int32) : Result Unit :=
  if status.toInt < 0 then
    .error ⟨stage, errnoOfStatus status⟩
  else
    .ok ()

private def decodeProbeStage? (stageCode : Nat) : Option Stage :=
  match stageCode with
  | 1 => some .openKernelImage
  | 2 => some .readKernelImage
  | 3 => some .parseKernelImage
  | 4 => some .allocGuestMemory
  | 5 => some .registerGuestMemory
  | 6 => some .setTssAddr
  | 7 => some .configureCpuid
  | 8 => some .getSregs
  | 9 => some .setSregs
  | 10 => some .setRegs
  | 11 => some .mapRunArea
  | 12 => some .runGuest
  | 13 => some .verifyIoExit
  | 14 => some .verifyTranscript
  | 15 => some .unmapRunArea
  | 16 => some .unregisterGuestMemory
  | 17 => some .freeGuestMemory
  | 18 => some .loadGuestCode
  | 19 => some .verifyMmioExit
  | 20 => some .verifyQueueState
  | 21 => some .verifyGuestResult
  | _ => none

def decodeProbeStatus (status : Int32) : Result Unit :=
  if status.toInt < 0 then
    let packed := errnoOfStatus status
    let packedNat := packed.toNat
    let stageCode := packedNat / packedProbeStageBase
    let errno := UInt32.ofNat (packedNat % packedProbeStageBase)
    match decodeProbeStage? stageCode with
    | some stage => .error ⟨stage, errno⟩
    | none => .error ⟨.verifyIoExit, if errno == 0 then 22 else errno⟩
  else
    .ok ()

def preferPrimary {α : Type} (primary : Result α) (cleanup : Result Unit) : Result α :=
  match primary with
  | .error err =>
      .error err
  | .ok value =>
      match cleanup with
      | .ok () => .ok value
      | .error err => .error err

def cleanupOption {α : Type} (resource? : Option α) (cleanup : α → IO (Result Unit)) :
    IO (Result Unit) := do
  match resource? with
  | some resource => cleanup resource
  | none => pure (.ok ())

def decodeHandleStatus (stage : Stage) (raw : UInt64) : Result UInt64 :=
  if raw >= pointerErrorBase then
    let errnoNat := raw.toNat - pointerErrorBase.toNat
    let errno := UInt32.ofNat (if errnoNat == 0 then 22 else errnoNat)
    .error ⟨stage, errno⟩
  else
    .ok raw

def decodePackedRead (stage : Stage) (packed : UInt64) : Result UInt32 :=
  let errno := UInt32.ofNat (packed.toNat / packedReadBase)
  let value := UInt32.ofNat (packed.toNat % packedReadBase)
  if errno == 0 then
    .ok value
  else
    .error ⟨stage, errno⟩

def openDev : IO (Result Kvm) := do
  pure <| (decodeValueStatus .openDev (← FFI.kvmOpenRaw 0)).map Kvm.mk

def getApiVersion (kvm : Kvm) : IO (Result UInt32) := do
  pure <| decodeValueStatus .getApiVersion (← FFI.kvmGetApiVersionRaw kvm.fd)

def createVm (kvm : Kvm) : IO (Result Vm) := do
  pure <| (decodeValueStatus .createVm (← FFI.kvmCreateVmRaw kvm.fd)).map Vm.mk

def createVcpu (vm : Vm) (vcpuId : UInt32) : IO (Result Vcpu) := do
  pure <| (decodeValueStatus .createVcpu (← FFI.kvmCreateVcpuRaw vm.fd vcpuId)).map Vcpu.mk

def getVcpuMmapSize (kvm : Kvm) : IO (Result UInt32) := do
  pure <| decodeValueStatus .getVcpuMmapSize (← FFI.kvmGetVcpuMmapSizeRaw kvm.fd)

def probeRunArea (vcpu : Vcpu) (runAreaSize : UInt32) : IO (Result Unit) := do
  pure <| decodeUnitStatus .probeRunArea (← FFI.kvmProbeVcpuRunAreaRaw vcpu.fd runAreaSize)

def allocGuestMemory (size : UInt64) : IO (Result GuestMemory) := do
  pure <| (decodeHandleStatus .allocGuestMemory (← FFI.kvmAllocGuestMemoryRaw size)).map fun handle =>
    { handle, size }

def freeGuestMemory (guestMemory : GuestMemory) : IO (Result Unit) := do
  pure <| decodeUnitStatus .freeGuestMemory
    (← FFI.kvmFreeGuestMemoryRaw guestMemory.handle guestMemory.size)

def registerGuestMemory (vm : Vm) (slot : UInt32) (guestPhysAddr : UInt64)
    (guestMemory : GuestMemory) : IO (Result Unit) := do
  pure <| decodeUnitStatus .registerGuestMemory
    (← FFI.kvmRegisterGuestMemoryRaw vm.fd slot guestPhysAddr guestMemory.size guestMemory.handle)

def unregisterGuestMemory (vm : Vm) (slot : UInt32) : IO (Result Unit) := do
  pure <| decodeUnitStatus .unregisterGuestMemory
    (← FFI.kvmUnregisterGuestMemoryRaw vm.fd slot)

def createIrqChip (vm : Vm) : IO (Result Unit) := do
  pure <| decodeUnitStatus .createIrqChip (← FFI.kvmCreateIrqChipRaw vm.fd)

def createPit2 (vm : Vm) : IO (Result Unit) := do
  pure <| decodeUnitStatus .createPit2 (← FFI.kvmCreatePit2Raw vm.fd)

def setIrqLine (vm : Vm) (irq : UInt32) (level : UInt32) : IO (Result Unit) := do
  pure <| decodeUnitStatus .verifyIoExit (← FFI.kvmSetIrqLineRaw vm.fd irq level)

def setTssAddr (vm : Vm) (tssAddr : UInt64) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setTssAddr (← FFI.kvmSetTssAddrRaw vm.fd tssAddr)

def configureCpuid (kvm : Kvm) (vcpu : Vcpu) : IO (Result Unit) := do
  pure <| decodeUnitStatus .configureCpuid
    (← FFI.kvmConfigureCpuidRaw kvm.fd vcpu.fd)

def allocVcpuStateBuffer : IO (Result VcpuStateBuffer) := do
  pure <| (decodeHandleStatus .getSregs (← FFI.kvmAllocVcpuStateBufferRaw 0)).map fun handle =>
    { handle }

def freeVcpuStateBuffer (buffer : VcpuStateBuffer) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setRegs (← FFI.kvmFreeVcpuStateBufferRaw buffer.handle)

def getSregsIntoBuffer (vcpu : Vcpu) (buffer : VcpuStateBuffer) : IO (Result Unit) := do
  pure <| decodeUnitStatus .getSregs
    (← FFI.kvmGetSregsIntoBufferRaw vcpu.fd buffer.handle)

def setSregsFromBuffer (vcpu : Vcpu) (buffer : VcpuStateBuffer) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setSregs
    (← FFI.kvmSetSregsFromBufferRaw vcpu.fd buffer.handle)

def vcpuStateGetCr0 (buffer : VcpuStateBuffer) : IO UInt64 := do
  FFI.kvmVcpuStateGetCr0Raw buffer.handle

def vcpuStateSetCr0 (buffer : VcpuStateBuffer) (value : UInt64) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setSregs (← FFI.kvmVcpuStateSetCr0Raw buffer.handle value)

def vcpuStateSetCr3 (buffer : VcpuStateBuffer) (value : UInt64) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setSregs (← FFI.kvmVcpuStateSetCr3Raw buffer.handle value)

def vcpuStateSetCr4 (buffer : VcpuStateBuffer) (value : UInt64) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setSregs (← FFI.kvmVcpuStateSetCr4Raw buffer.handle value)

def vcpuStateSetEfer (buffer : VcpuStateBuffer) (value : UInt64) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setSregs (← FFI.kvmVcpuStateSetEferRaw buffer.handle value)

def vcpuStateSetGdt (buffer : VcpuStateBuffer) (base : UInt64) (limit : UInt32) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setSregs
    (← FFI.kvmVcpuStateSetGdtRaw buffer.handle base limit)

def vcpuStateSetIdt (buffer : VcpuStateBuffer) (base : UInt64) (limit : UInt32) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setSregs
    (← FFI.kvmVcpuStateSetIdtRaw buffer.handle base limit)

def vcpuStateSetFlatSegment (buffer : VcpuStateBuffer) (slot selector typ : UInt32) :
    IO (Result Unit) := do
  pure <| decodeUnitStatus .setSregs
    (← FFI.kvmVcpuStateSetFlatSegmentRaw buffer.handle slot selector typ)

def vcpuStateClearRegs (buffer : VcpuStateBuffer) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setRegs (← FFI.kvmVcpuStateClearRegsRaw buffer.handle)

def vcpuStateSetRip (buffer : VcpuStateBuffer) (value : UInt64) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setRegs (← FFI.kvmVcpuStateSetRipRaw buffer.handle value)

def vcpuStateSetRsi (buffer : VcpuStateBuffer) (value : UInt64) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setRegs (← FFI.kvmVcpuStateSetRsiRaw buffer.handle value)

def vcpuStateSetRsp (buffer : VcpuStateBuffer) (value : UInt64) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setRegs (← FFI.kvmVcpuStateSetRspRaw buffer.handle value)

def vcpuStateSetRflags (buffer : VcpuStateBuffer) (value : UInt64) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setRegs (← FFI.kvmVcpuStateSetRflagsRaw buffer.handle value)

def setRegsFromBuffer (vcpu : Vcpu) (buffer : VcpuStateBuffer) : IO (Result Unit) := do
  pure <| decodeUnitStatus .setRegs
    (← FFI.kvmSetRegsFromBufferRaw vcpu.fd buffer.handle)

def prepareVirtioMmioEntropyGuest (guestMemory : GuestMemory) : IO (Result Unit) := do
  pure <| decodeUnitStatus .loadGuestCode
    (← FFI.kvmPrepareVirtioMmioEntropyGuestRaw guestMemory.handle guestMemory.size)

def mapRunArea (vcpu : Vcpu) (runAreaSize : UInt32) : IO (Result RunArea) := do
  pure <| (decodeHandleStatus .mapRunArea (← FFI.kvmMapRunAreaRaw vcpu.fd runAreaSize)).map
    fun handle => { handle, size := runAreaSize }

def unmapRunArea (runArea : RunArea) : IO (Result Unit) := do
  pure <| decodeUnitStatus .unmapRunArea
    (← FFI.kvmUnmapRunAreaRaw runArea.handle runArea.size)

def runGuestOnce (vcpu : Vcpu) : IO (Result Unit) := do
  pure <| decodeUnitStatus .runGuest (← FFI.kvmRunRaw vcpu.fd)

def runExitReason (runArea : RunArea) : IO UInt32 := do
  FFI.kvmRunExitReasonRaw runArea.handle

def runIoDirection (runArea : RunArea) : IO UInt32 := do
  FFI.kvmRunIoDirectionRaw runArea.handle

def runIoPort (runArea : RunArea) : IO IoPort := do
  pure ⟨← FFI.kvmRunIoPortRaw runArea.handle⟩

def runIoSize (runArea : RunArea) : IO UInt32 := do
  FFI.kvmRunIoSizeRaw runArea.handle

def runIoCount (runArea : RunArea) : IO UInt32 := do
  FFI.kvmRunIoCountRaw runArea.handle

def runIoDataU8 (runArea : RunArea) : IO UInt32 := do
  FFI.kvmRunIoDataU8Raw runArea.handle

def runIoDataU16 (runArea : RunArea) : IO UInt32 := do
  FFI.kvmRunIoDataU16Raw runArea.handle

def runIoDataU32 (runArea : RunArea) : IO UInt32 := do
  FFI.kvmRunIoDataU32Raw runArea.handle

def setRunIoDataU8 (runArea : RunArea) (value : UInt32) : IO (Result Unit) := do
  pure <| decodeUnitStatus .verifyIoExit (← FFI.kvmRunSetIoDataU8Raw runArea.handle value)

def setRunIoDataU16 (runArea : RunArea) (value : UInt32) : IO (Result Unit) := do
  pure <| decodeUnitStatus .verifyIoExit (← FFI.kvmRunSetIoDataU16Raw runArea.handle value)

def setRunIoDataU32 (runArea : RunArea) (value : UInt32) : IO (Result Unit) := do
  pure <| decodeUnitStatus .verifyIoExit (← FFI.kvmRunSetIoDataU32Raw runArea.handle value)

private def readIoOutputValue (runArea : RunArea) (width count : UInt32) : IO (Result UInt32) := do
  if count != 1 then
    pure (.error ⟨.verifyIoExit, eproto⟩)
  else if width == 1 then
    pure (.ok (← runIoDataU8 runArea))
  else if width == 2 then
    pure (.ok (← runIoDataU16 runArea))
  else if width == 4 then
    pure (.ok (← runIoDataU32 runArea))
  else
    pure (.error ⟨.verifyIoExit, eproto⟩)

def setRunIoData (runArea : RunArea) (width count value : UInt32) : IO (Result Unit) := do
  if count != 1 then
    pure (.error ⟨.verifyIoExit, eproto⟩)
  else if width == 1 then
    setRunIoDataU8 runArea value
  else if width == 2 then
    setRunIoDataU16 runArea value
  else if width == 4 then
    setRunIoDataU32 runArea value
  else
    pure (.error ⟨.verifyIoExit, eproto⟩)

def runMmioPhysAddr (runArea : RunArea) : IO MmioPhysAddr := do
  pure ⟨← FFI.kvmRunMmioPhysAddrRaw runArea.handle⟩

def runMmioLen (runArea : RunArea) : IO UInt32 := do
  FFI.kvmRunMmioLenRaw runArea.handle

def runMmioIsWrite (runArea : RunArea) : IO Bool := do
  pure <| (← FFI.kvmRunMmioIsWriteRaw runArea.handle) != 0

def runMmioDataU32 (runArea : RunArea) : IO UInt32 := do
  FFI.kvmRunMmioDataU32Raw runArea.handle

def setRunMmioDataU32 (runArea : RunArea) (value : UInt32) : IO (Result Unit) := do
  pure <| decodeUnitStatus .verifyMmioExit (← FFI.kvmRunSetMmioDataU32Raw runArea.handle value)

/-- KVM leaves bytes above `mmio.len` undefined in the shared run buffer, so normalize write values
to the exit width as soon as they cross the host boundary. -/
private def normalizeMmioWriteValue (width : UInt32) (value : UInt32) : UInt32 :=
  if width == 1 then
    value &&& 0xff
  else if width == 2 then
    value &&& 0xffff
  else
    value

private def decodeIoDirection (raw : UInt32) : Result IoDirection :=
  if raw == kvmExitIoIn then
    .ok .input
  else if raw == kvmExitIoOut then
    .ok .output
  else
    .error ⟨.verifyIoExit, eproto⟩

def readIoAccess (runArea : RunArea) : IO (Result IoAccess) := do
  let width ← runIoSize runArea
  let count ← runIoCount runArea
  let port ← runIoPort runArea
  match decodeIoDirection (← runIoDirection runArea) with
  | .error err =>
      pure (.error err)
  | .ok direction =>
      if direction == .output then
      match ← readIoOutputValue runArea width count with
      | .error err =>
        pure (.error err)
      | .ok value =>
        pure (.ok { port, width, count, direction, value })
      else
        pure (.ok { port, width, count, direction })

def readMmioAccess (runArea : RunArea) : IO MmioAccess := do
  let address ← runMmioPhysAddr runArea
  let width ← runMmioLen runArea
  if ← runMmioIsWrite runArea then
    let value := normalizeMmioWriteValue width (← runMmioDataU32 runArea)
    pure { address, width, direction := .write, value := value }
  else
    pure { address, width, direction := .read }

def guestReadU8 (stage : Stage) (guestMemory : GuestMemory) (guestAddr : UInt64) :
    IO (Result UInt32) := do
  pure <| decodePackedRead stage
    (← FFI.kvmGuestReadU8PackedRaw guestMemory.handle guestMemory.size guestAddr)

def guestReadU16 (stage : Stage) (guestMemory : GuestMemory) (guestAddr : UInt64) :
    IO (Result UInt32) := do
  pure <| decodePackedRead stage
    (← FFI.kvmGuestReadU16PackedRaw guestMemory.handle guestMemory.size guestAddr)

def guestReadU32 (stage : Stage) (guestMemory : GuestMemory) (guestAddr : UInt64) :
    IO (Result UInt32) := do
  pure <| decodePackedRead stage
    (← FFI.kvmGuestReadU32PackedRaw guestMemory.handle guestMemory.size guestAddr)

def guestWriteU8 (stage : Stage) (guestMemory : GuestMemory) (guestAddr : UInt64)
    (value : UInt32) : IO (Result Unit) := do
  pure <| decodeUnitStatus stage
    (← FFI.kvmGuestWriteU8Raw guestMemory.handle guestMemory.size guestAddr value)

def guestWriteU16 (stage : Stage) (guestMemory : GuestMemory) (guestAddr : UInt64)
    (value : UInt32) : IO (Result Unit) := do
  pure <| decodeUnitStatus stage
    (← FFI.kvmGuestWriteU16Raw guestMemory.handle guestMemory.size guestAddr value)

def guestWriteU32 (stage : Stage) (guestMemory : GuestMemory) (guestAddr : UInt64)
    (value : UInt32) : IO (Result Unit) := do
  pure <| decodeUnitStatus stage
    (← FFI.kvmGuestWriteU32Raw guestMemory.handle guestMemory.size guestAddr value)

def guestWriteByteArray (stage : Stage) (guestMemory : GuestMemory) (guestAddr : UInt64)
    (bytes : ByteArray) : IO (Result Unit) := do
  pure <| decodeUnitStatus stage
    (← FFI.kvmGuestWriteByteArrayRaw guestMemory.handle guestMemory.size guestAddr bytes)

private def closeWithStage {α : Type} [HasRawFd α] (stage : Stage) (handle : α) : IO (Result Unit) := do
  pure <| decodeUnitStatus stage (← FFI.kvmCloseRaw (HasRawFd.rawFd handle))

def closeVcpu (vcpu : Vcpu) : IO (Result Unit) := do
  closeWithStage .closeVcpu vcpu

def closeVm (vm : Vm) : IO (Result Unit) := do
  closeWithStage .closeVm vm

def closeDev (kvm : Kvm) : IO (Result Unit) := do
  closeWithStage .closeDev kvm

def bindIOResult {α β : Type} (action : IO (Result α))
    (next : α → IO (Result β)) : IO (Result β) := do
  match ← action with
  | .error err =>
      pure (.error err)
  | .ok value =>
      next value

def mapIOResult {α β : Type} (action : IO (Result α)) (f : α → β) : IO (Result β) := do
  match ← action with
  | .error err =>
      pure (.error err)
  | .ok value =>
      pure (.ok (f value))

def withCleanup {α : Type} (primary : IO (Result α)) (cleanup : IO (Result Unit)) :
    IO (Result α) := do
  let primaryResult ← primary
  let cleanupResult ← cleanup
  pure <| preferPrimary primaryResult cleanupResult

def withKvm {α : Type} (body : Kvm → IO (Result α)) : IO (Result α) := do
  match ← openDev with
  | .error err =>
      pure (.error err)
  | .ok kvm =>
      withCleanup (body kvm) (closeDev kvm)

def withVm {α : Type} (kvm : Kvm) (body : Vm → IO (Result α)) : IO (Result α) := do
  match ← createVm kvm with
  | .error err =>
      pure (.error err)
  | .ok vm =>
      withCleanup (body vm) (closeVm vm)

def withVcpu {α : Type} (vm : Vm) (vcpuId : UInt32) (body : Vcpu → IO (Result α)) :
    IO (Result α) := do
  match ← createVcpu vm vcpuId with
  | .error err =>
      pure (.error err)
  | .ok vcpu =>
      withCleanup (body vcpu) (closeVcpu vcpu)

def withVmContext {α : Type} (body : VmContext → IO (Result α)) : IO (Result α) := do
  withKvm fun kvm =>
    bindIOResult (getApiVersion kvm) fun apiVersion =>
      withVm kvm fun vm =>
        bindIOResult (getVcpuMmapSize kvm) fun runAreaSize =>
          body { kvm, vm, apiVersion, runAreaSize }

def withVcpuContext {α : Type} (vmContext : VmContext) (vcpuId : UInt32)
    (body : VcpuContext → IO (Result α)) : IO (Result α) := do
  withVcpu vmContext.vm vcpuId fun vcpu =>
    body { vmContext, id := vcpuId, vcpu }

def withGuestMemory {α : Type} (size : UInt64)
    (body : GuestMemory → IO (Result α)) : IO (Result α) := do
  match ← allocGuestMemory size with
  | .error err =>
      pure (.error err)
  | .ok guestMemory =>
      withCleanup (body guestMemory) (freeGuestMemory guestMemory)

def withRegisteredGuestMemory {α : Type} (vm : Vm) (slot : UInt32)
    (guestPhysAddr : UInt64) (guestMemory : GuestMemory) (body : IO (Result α)) : IO (Result α) := do
  match ← registerGuestMemory vm slot guestPhysAddr guestMemory with
  | .error err =>
      pure (.error err)
  | .ok () =>
      withCleanup body (unregisterGuestMemory vm slot)

def withMappedRunArea {α : Type} (vcpu : Vcpu) (runAreaSize : UInt32)
    (body : RunArea → IO (Result α)) : IO (Result α) := do
  match ← mapRunArea vcpu runAreaSize with
  | .error err =>
      pure (.error err)
  | .ok runArea =>
      withCleanup (body runArea) (unmapRunArea runArea)

end Microvmm.Kvm