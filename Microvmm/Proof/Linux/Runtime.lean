import Microvmm.Guest.Linux.Runtime
import Microvmm.Proof.Kvm.RawBoundary
import Microvmm.Proof.Linux.Platform

namespace Microvmm

open Kvm

private abbrev World := Void IO.RealWorld

private theorem ioBind_apply {α β : Type} (action : IO α)
  (next : α → IO β) (world : World) :
  (action >>= next) world =
    match action world with
    | EST.Out.ok value nextWorld => next value nextWorld
    | EST.Out.error err nextWorld => EST.Out.error err nextWorld := by
  change EST.bind action next world = _
  unfold EST.bind
  cases hAction : action world <;> rfl

private theorem ioResultRunsTo_of_ok {α : Type} {action : IO (Result α)}
    {world nextWorld : World} {value : α}
    (h : action world = EST.Out.ok (Outcome.ok value) nextWorld) :
    IOResultRunsTo action value := by
  exact ⟨world, nextWorld, h⟩

/-- The stale world-indexed loop equality is intentionally pruned here. What still survives at the
runtime layer is the explicit MMIO-exit witness, the recovered rng executor report, and the named
remaining raw boundary. -/
theorem runLinuxSerialLoop_mmio_processQueue_step_refines_upToRawBoundary
  (_remaining : Nat) (vm : Kvm.Vm) (vcpu : Kvm.Vcpu) (runArea : Kvm.RunArea)
    (guestMemory : Kvm.GuestMemory) (state : LinuxPlatformState) (access : MmioAccess)
    {afterWrite : VirtioPciState} {nextState : LinuxPlatformState}
    {world0 world1 world2 world3 : World}
    (_hRun : runGuestOnce vcpu world0 = EST.Out.ok (Outcome.ok ()) world1)
    (_hExitReason : runExitReason runArea world1 = EST.Out.ok linuxRuntimeKvmExitMmio world2)
    (hRead : readMmioAccess runArea = pure access)
    (hRoute : routePlatformMmioAccess state.bus.virtioPci access = .virtioPciBar)
    (hWriteDir : access.direction = .write)
    (hWrite : virtioPciBarWrite state.bus.virtioPci access.address access.width access.value =
      .ok (afterWrite, .processQueue))
    (hHandle : handleLinuxMmioAccess vm runArea guestMemory state access world2 =
      EST.Out.ok (Outcome.ok nextState) world3) :
    LinuxVirtioRawBoundary vm vcpu runArea guestMemory ∧
      IOResultRunsTo (handleLinuxMmioExit vm runArea guestMemory state) nextState ∧
      nextState.console = state.console ∧
      ∃ nextDevice, ∃ report : VirtioEntropyExecutionReport,
        nextState.bus.virtioPci = { afterWrite with device := nextDevice } ∧
        IOResultRunsTo
          (completeDeterministicEntropyRequestWithReport guestMemory afterWrite.device)
          (nextDevice, report) ∧
        report.writes = virtioEntropyCompletionWrites report.plan ∧
        virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes := by
  have hHandleRuns : IOResultRunsTo
      (handleLinuxMmioAccess vm runArea guestMemory state access) nextState :=
    ioResultRunsTo_of_ok hHandle
  rcases handleLinuxMmioExit_virtioPciBar_processQueue_refines vm runArea guestMemory state access
      hRead hRoute hWriteDir hWrite hHandleRuns with
    ⟨hExitRuns, hConsole, nextDevice, report, hTransport, hReportExec, hTrace,
      hTraceRealized⟩
  exact ⟨linuxVirtioRawBoundary_holds vm vcpu runArea guestMemory, hExitRuns, hConsole,
    ⟨nextDevice, report, hTransport, hReportExec, hTrace, hTraceRealized⟩⟩

/-- The one-step Linux serial runtime shell adds no device transition beyond the routed MMIO
handler, so any packaged descriptor-validity judgment already established for the post-write
device carries into the resulting platform state. -/
theorem runLinuxSerialLoop_mmio_processQueue_step_preserves_descriptorValidity
  (guestMemorySize : UInt64) (_remaining : Nat) (vm : Kvm.Vm) (vcpu : Kvm.Vcpu)
    (runArea : Kvm.RunArea) (guestMemory : Kvm.GuestMemory) (state : LinuxPlatformState)
    (access : MmioAccess)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {afterWrite : VirtioPciState} {nextState : LinuxPlatformState}
    {world0 world1 world2 world3 : World}
    (_hRun : runGuestOnce vcpu world0 = EST.Out.ok (Outcome.ok ()) world1)
    (_hExitReason : runExitReason runArea world1 = EST.Out.ok linuxRuntimeKvmExitMmio world2)
    (_hRead : readMmioAccess runArea = pure access)
    (hRoute : routePlatformMmioAccess state.bus.virtioPci access = .virtioPciBar)
    (hWriteDir : access.direction = .write)
    (hWrite : virtioPciBarWrite state.bus.virtioPci access.address access.width access.value =
      .ok (afterWrite, .processQueue))
    (hHandle : handleLinuxMmioAccess vm runArea guestMemory state access world2 =
      EST.Out.ok (Outcome.ok nextState) world3)
    (hValid : descriptorValidForDevice guestMemorySize afterWrite.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext) :
    descriptorValidForDevice guestMemorySize nextState.bus.virtioPci.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext := by
  have hHandleRuns : IOResultRunsTo
      (handleLinuxMmioAccess vm runArea guestMemory state access) nextState :=
    ioResultRunsTo_of_ok hHandle
  exact handleLinuxMmioAccess_virtioPciBar_processQueue_preserves_descriptorValidity
    guestMemorySize vm runArea guestMemory state access availIdx usedIdx head descAddrLow
    descAddrHigh descLen descFlags descNext hRoute hWriteDir hWrite hHandleRuns hValid

/-- The interactive runtime shell keeps the same surviving proof payload: the MMIO-exit witness,
the executor report, and the explicit raw boundary, without the stale loop-step equality. -/
theorem runLinuxInteractiveLoop_mmio_processQueue_step_refines_upToRawBoundary
  (_remaining : Nat) (vm : Kvm.Vm) (vcpu : Kvm.Vcpu) (runArea : Kvm.RunArea)
    (guestMemory : Kvm.GuestMemory) (state queuedState : InteractiveRunState)
    (access : MmioAccess) {afterWrite : VirtioPciState} {nextPlatform : LinuxPlatformState}
    {world0 world1 world2 world3 world4 : World}
    (_hService : serviceInteractiveTransport vm state world0 =
      EST.Out.ok (Outcome.ok queuedState) world1)
    (_hRun : runGuestOnce vcpu world1 = EST.Out.ok (Outcome.ok ()) world2)
    (_hExitReason : runExitReason runArea world2 = EST.Out.ok linuxRuntimeKvmExitMmio world3)
    (hRead : readMmioAccess runArea = pure access)
    (hRoute : routePlatformMmioAccess queuedState.platform.bus.virtioPci access = .virtioPciBar)
    (hWriteDir : access.direction = .write)
    (hWrite : virtioPciBarWrite queuedState.platform.bus.virtioPci access.address access.width
      access.value = .ok (afterWrite, .processQueue))
    (hHandle : handleLinuxMmioAccess vm runArea guestMemory queuedState.platform access world3 =
      EST.Out.ok (Outcome.ok nextPlatform) world4) :
    LinuxVirtioRawBoundary vm vcpu runArea guestMemory ∧
      IOResultRunsTo (handleLinuxMmioExit vm runArea guestMemory queuedState.platform)
        nextPlatform ∧
      nextPlatform.console = queuedState.platform.console ∧
      ∃ nextDevice, ∃ report : VirtioEntropyExecutionReport,
        nextPlatform.bus.virtioPci = { afterWrite with device := nextDevice } ∧
        IOResultRunsTo
          (completeDeterministicEntropyRequestWithReport guestMemory afterWrite.device)
          (nextDevice, report) ∧
        report.writes = virtioEntropyCompletionWrites report.plan ∧
        virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes := by
  have hHandleRuns : IOResultRunsTo
      (handleLinuxMmioAccess vm runArea guestMemory queuedState.platform access) nextPlatform :=
    ioResultRunsTo_of_ok hHandle
  rcases handleLinuxMmioExit_virtioPciBar_processQueue_refines vm runArea guestMemory
      queuedState.platform access hRead hRoute hWriteDir hWrite hHandleRuns with
    ⟨hExitRuns, hConsole, nextDevice, report, hTransport, hReportExec, hTrace,
      hTraceRealized⟩
  exact ⟨linuxVirtioRawBoundary_holds vm vcpu runArea guestMemory, hExitRuns, hConsole,
    ⟨nextDevice, report, hTransport, hReportExec, hTrace, hTraceRealized⟩⟩

/-- The interactive runtime shell preserves the same packaged descriptor-validity judgment along
the routed virtio-pci MMIO `processQueue` branch, because the only device transition after the BAR
write is the executor path already handled by the platform theorem. -/
theorem runLinuxInteractiveLoop_mmio_processQueue_step_preserves_descriptorValidity
  (guestMemorySize : UInt64) (_remaining : Nat) (vm : Kvm.Vm) (vcpu : Kvm.Vcpu)
    (runArea : Kvm.RunArea) (guestMemory : Kvm.GuestMemory)
    (state queuedState : InteractiveRunState) (access : MmioAccess)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {afterWrite : VirtioPciState} {nextPlatform : LinuxPlatformState}
    {world0 world1 world2 world3 world4 : World}
    (_hService : serviceInteractiveTransport vm state world0 =
      EST.Out.ok (Outcome.ok queuedState) world1)
    (_hRun : runGuestOnce vcpu world1 = EST.Out.ok (Outcome.ok ()) world2)
    (_hExitReason : runExitReason runArea world2 = EST.Out.ok linuxRuntimeKvmExitMmio world3)
    (_hRead : readMmioAccess runArea = pure access)
    (hRoute : routePlatformMmioAccess queuedState.platform.bus.virtioPci access = .virtioPciBar)
    (hWriteDir : access.direction = .write)
    (hWrite : virtioPciBarWrite queuedState.platform.bus.virtioPci access.address access.width
      access.value = .ok (afterWrite, .processQueue))
    (hHandle : handleLinuxMmioAccess vm runArea guestMemory queuedState.platform access world3 =
      EST.Out.ok (Outcome.ok nextPlatform) world4)
    (hValid : descriptorValidForDevice guestMemorySize afterWrite.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext) :
    descriptorValidForDevice guestMemorySize nextPlatform.bus.virtioPci.device availIdx usedIdx
      head descAddrLow descAddrHigh descLen descFlags descNext := by
  have hHandleRuns : IOResultRunsTo
      (handleLinuxMmioAccess vm runArea guestMemory queuedState.platform access)
      nextPlatform := ioResultRunsTo_of_ok hHandle
  exact handleLinuxMmioAccess_virtioPciBar_processQueue_preserves_descriptorValidity
    guestMemorySize vm runArea guestMemory queuedState.platform access availIdx usedIdx head
    descAddrLow descAddrHigh descLen descFlags descNext hRoute hWriteDir hWrite hHandleRuns hValid

end Microvmm
