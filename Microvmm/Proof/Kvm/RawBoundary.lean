import Microvmm.Proof.Kvm.Resource

namespace Microvmm

open Microvmm.Kvm

/-- The remaining trusted Lean-side boundary for the proved virtio `processQueue` path.

This is intentionally a contract over the raw extern boundary, not a verification of `ffi/shim.c`.
The current proof tree shows that standalone MMIO and Linux virtio execution reaches only these
raw calls plus Lean runtime / `IO` semantics. -/
def VirtioGuestMemoryRawBoundary (guestMemory : GuestMemory) : Prop :=
  (∀ guestAddr,
    guestReadU16 .verifyMmioExit guestMemory guestAddr =
      FFI.kvmGuestReadU16PackedRaw guestMemory.handle guestMemory.size guestAddr >>= fun packed =>
        pure (decodePackedRead .verifyMmioExit packed)) ∧
  (∀ guestAddr,
    guestReadU32 .verifyMmioExit guestMemory guestAddr =
      FFI.kvmGuestReadU32PackedRaw guestMemory.handle guestMemory.size guestAddr >>= fun packed =>
        pure (decodePackedRead .verifyMmioExit packed)) ∧
  (∀ guestAddr value,
    guestWriteU8 .verifyMmioExit guestMemory guestAddr value =
      FFI.kvmGuestWriteU8Raw guestMemory.handle guestMemory.size guestAddr value >>= fun status =>
        pure (decodeUnitStatus .verifyMmioExit status)) ∧
  (∀ guestAddr value,
    guestWriteU16 .verifyMmioExit guestMemory guestAddr value =
      FFI.kvmGuestWriteU16Raw guestMemory.handle guestMemory.size guestAddr value >>= fun status =>
        pure (decodeUnitStatus .verifyMmioExit status)) ∧
  (∀ guestAddr value,
    guestWriteU32 .verifyMmioExit guestMemory guestAddr value =
      FFI.kvmGuestWriteU32Raw guestMemory.handle guestMemory.size guestAddr value >>= fun status =>
        pure (decodeUnitStatus .verifyMmioExit status))

def VirtioObservedMmioRawBoundary (vcpu : Vcpu) (runArea : RunArea) : Prop :=
  (runGuestOnce vcpu =
    FFI.kvmRunRaw vcpu.fd >>= fun status => pure (decodeUnitStatus .runGuest status)) ∧
  runExitReason runArea = FFI.kvmRunExitReasonRaw runArea.handle ∧
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
      pure { address, width, direction := .read })

def VirtioMmioRawBoundary (vcpu : Vcpu) (runArea : RunArea) (guestMemory : GuestMemory) : Prop :=
  VirtioObservedMmioRawBoundary vcpu runArea ∧ VirtioGuestMemoryRawBoundary guestMemory

def LinuxVirtioRawBoundary (vm : Vm) (vcpu : Vcpu) (runArea : RunArea)
    (guestMemory : GuestMemory) : Prop :=
  VirtioMmioRawBoundary vcpu runArea guestMemory ∧
    (∀ irq level,
      setIrqLine vm irq level =
        FFI.kvmSetIrqLineRaw vm.fd irq level >>= fun status =>
          pure (decodeUnitStatus .verifyIoExit status))

theorem virtioGuestMemoryRawBoundary_holds (guestMemory : GuestMemory) :
    VirtioGuestMemoryRawBoundary guestMemory := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro guestAddr
    exact guestReadU16_defeq_raw .verifyMmioExit guestMemory guestAddr
  · intro guestAddr
    exact guestReadU32_defeq_raw .verifyMmioExit guestMemory guestAddr
  · intro guestAddr value
    exact guestWriteU8_defeq_raw .verifyMmioExit guestMemory guestAddr value
  · intro guestAddr value
    exact guestWriteU16_defeq_raw .verifyMmioExit guestMemory guestAddr value
  · intro guestAddr value
    exact guestWriteU32_defeq_raw .verifyMmioExit guestMemory guestAddr value

theorem virtioObservedMmioRawBoundary_holds (vcpu : Vcpu) (runArea : RunArea) :
    VirtioObservedMmioRawBoundary vcpu runArea := by
  refine ⟨runGuestOnce_defeq_raw vcpu, runExitReason_defeq_raw runArea,
    readMmioAccess_defeq_observers runArea⟩

theorem virtioMmioRawBoundary_holds (vcpu : Vcpu) (runArea : RunArea)
    (guestMemory : GuestMemory) :
    VirtioMmioRawBoundary vcpu runArea guestMemory := by
  exact ⟨virtioObservedMmioRawBoundary_holds vcpu runArea,
    virtioGuestMemoryRawBoundary_holds guestMemory⟩

theorem linuxVirtioRawBoundary_holds (vm : Vm) (vcpu : Vcpu) (runArea : RunArea)
    (guestMemory : GuestMemory) :
    LinuxVirtioRawBoundary vm vcpu runArea guestMemory := by
  refine ⟨virtioMmioRawBoundary_holds vcpu runArea guestMemory, ?_⟩
  intro irq level
  exact setIrqLine_defeq_raw vm irq level

end Microvmm
