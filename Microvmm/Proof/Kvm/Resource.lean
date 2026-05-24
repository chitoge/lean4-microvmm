import Microvmm.Kvm.Resource

namespace Microvmm

open Kvm

theorem guestReadU16_defeq_raw (stage : Stage) (guestMemory : GuestMemory) (guestAddr : UInt64) :
    guestReadU16 stage guestMemory guestAddr =
      FFI.kvmGuestReadU16PackedRaw guestMemory.handle guestMemory.size guestAddr >>= fun packed =>
        pure (decodePackedRead stage packed) := by
  rfl

theorem guestReadU32_defeq_raw (stage : Stage) (guestMemory : GuestMemory) (guestAddr : UInt64) :
    guestReadU32 stage guestMemory guestAddr =
      FFI.kvmGuestReadU32PackedRaw guestMemory.handle guestMemory.size guestAddr >>= fun packed =>
        pure (decodePackedRead stage packed) := by
  rfl

theorem guestWriteU8_defeq_raw (stage : Stage) (guestMemory : GuestMemory) (guestAddr : UInt64)
    (value : UInt32) :
    guestWriteU8 stage guestMemory guestAddr value =
      FFI.kvmGuestWriteU8Raw guestMemory.handle guestMemory.size guestAddr value >>= fun status =>
        pure (decodeUnitStatus stage status) := by
  rfl

theorem guestWriteU16_defeq_raw (stage : Stage) (guestMemory : GuestMemory) (guestAddr : UInt64)
    (value : UInt32) :
    guestWriteU16 stage guestMemory guestAddr value =
      FFI.kvmGuestWriteU16Raw guestMemory.handle guestMemory.size guestAddr value >>= fun status =>
        pure (decodeUnitStatus stage status) := by
  rfl

theorem guestWriteU32_defeq_raw (stage : Stage) (guestMemory : GuestMemory) (guestAddr : UInt64)
    (value : UInt32) :
    guestWriteU32 stage guestMemory guestAddr value =
      FFI.kvmGuestWriteU32Raw guestMemory.handle guestMemory.size guestAddr value >>= fun status =>
        pure (decodeUnitStatus stage status) := by
  rfl

theorem runGuestOnce_defeq_raw (vcpu : Vcpu) :
    runGuestOnce vcpu =
      FFI.kvmRunRaw vcpu.fd >>= fun status => pure (decodeUnitStatus .runGuest status) := by
  rfl

theorem runExitReason_defeq_raw (runArea : RunArea) :
    runExitReason runArea = FFI.kvmRunExitReasonRaw runArea.handle := by
  rfl

theorem runMmioPhysAddr_defeq_raw (runArea : RunArea) :
    runMmioPhysAddr runArea =
      FFI.kvmRunMmioPhysAddrRaw runArea.handle >>= fun address => pure ⟨address⟩ := by
  rfl

theorem runMmioLen_defeq_raw (runArea : RunArea) :
    runMmioLen runArea = FFI.kvmRunMmioLenRaw runArea.handle := by
  rfl

theorem runMmioIsWrite_defeq_raw (runArea : RunArea) :
    runMmioIsWrite runArea =
      FFI.kvmRunMmioIsWriteRaw runArea.handle >>= fun isWrite => pure (isWrite != 0) := by
  rfl

theorem runMmioDataU32_defeq_raw (runArea : RunArea) :
    runMmioDataU32 runArea = FFI.kvmRunMmioDataU32Raw runArea.handle := by
  rfl

theorem setRunMmioDataU32_defeq_raw (runArea : RunArea) (value : UInt32) :
    setRunMmioDataU32 runArea value =
      FFI.kvmRunSetMmioDataU32Raw runArea.handle value >>= fun status =>
        pure (decodeUnitStatus .verifyMmioExit status) := by
  rfl

theorem setIrqLine_defeq_raw (vm : Vm) (irq : UInt32) (level : UInt32) :
    setIrqLine vm irq level =
      FFI.kvmSetIrqLineRaw vm.fd irq level >>= fun status =>
        pure (decodeUnitStatus .verifyIoExit status) := by
  rfl

theorem readMmioAccess_defeq_observers (runArea : RunArea) :
  readMmioAccess runArea = (do
      let address ← runMmioPhysAddr runArea
      let width ← runMmioLen runArea
      if ← runMmioIsWrite runArea then
        let rawValue ← runMmioDataU32 runArea
        let value :=
          if width == 1 then
            rawValue &&& 0xff
          else if width == 2 then
            rawValue &&& 0xffff
          else
            rawValue
        pure { address, width, direction := .write, value := value }
      else
        pure { address, width, direction := .read }) := by
  rfl

end Microvmm
