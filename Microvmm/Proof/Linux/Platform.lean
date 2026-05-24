import Microvmm.Bus.Mmio
import Microvmm.Guest.Linux.Platform
import Microvmm.Proof.Virtio.Pci
import Microvmm.Proof.Virtio.RngExecution

namespace Microvmm

open Kvm

private theorem ioBind_apply {α β : Type} (action : IO α)
  (next : α → IO β) (world : Void IO.RealWorld) :
  (action >>= next) world =
    match action world with
    | EST.Out.ok value nextWorld => next value nextWorld
    | EST.Out.error err nextWorld => EST.Out.error err nextWorld := by
  change EST.bind action next world = _
  unfold EST.bind
  cases hAction : action world <;> rfl

private theorem bindIOResult_apply {α β : Type} (action : IO (Result α))
  (next : α → IO (Result β)) (world : Void IO.RealWorld) :
  bindIOResult action next world =
    match action world with
    | EST.Out.ok (Outcome.error err) nextWorld =>
      EST.Out.ok (Outcome.error err) nextWorld
    | EST.Out.ok (Outcome.ok value) nextWorld =>
      next value nextWorld
    | EST.Out.error err nextWorld =>
      EST.Out.error err nextWorld := by
  unfold bindIOResult
  change EST.bind action (fun __do_lift =>
  match __do_lift with
  | Outcome.error err => pure (Outcome.error err)
  | Outcome.ok value => next value) world = _
  unfold EST.bind
  cases hAction : action world with
  | ok result nextWorld =>
    cases result <;> rfl
  | error err nextWorld =>
    rfl

private theorem mapIOResult_apply {α β : Type} (action : IO (Result α))
  (f : α → β) (world : Void IO.RealWorld) :
  mapIOResult action f world =
    match action world with
    | EST.Out.ok (Outcome.error err) nextWorld =>
      EST.Out.ok (Outcome.error err) nextWorld
    | EST.Out.ok (Outcome.ok value) nextWorld =>
      EST.Out.ok (Outcome.ok (f value)) nextWorld
    | EST.Out.error err nextWorld =>
      EST.Out.error err nextWorld := by
  unfold mapIOResult
  change EST.bind action (fun __do_lift =>
  match __do_lift with
  | Outcome.error err => pure (Outcome.error err)
  | Outcome.ok value => pure (Outcome.ok (f value))) world = _
  unfold EST.bind
  cases hAction : action world with
  | ok result nextWorld =>
    cases result <;> rfl
  | error err nextWorld =>
    rfl

/-- A successful Linux virtio-pci BAR `processQueue` action is just the real rng executor plus the
IRQ pulse; the executor report can be recovered from the erased runtime action. -/
theorem handleLinuxVirtioPciBarAction_processQueue_refines
  (vm : Kvm.Vm) (guestMemory : Kvm.GuestMemory) (transport : VirtioPciState)
    {nextTransport : VirtioPciState}
  (hAction : IOResultRunsTo
    (handleLinuxVirtioPciBarAction vm guestMemory transport .processQueue)
    nextTransport) :
    ∃ nextDevice report,
      nextTransport = { transport with device := nextDevice } ∧
    IOResultRunsTo
    (completeDeterministicEntropyRequestWithReport guestMemory transport.device)
    (nextDevice, report) ∧
      report.writes = virtioEntropyCompletionWrites report.plan ∧
      virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes := by
  rcases hAction with ⟨world0, worldFinal, hAction⟩
  unfold handleLinuxVirtioPciBarAction at hAction
  simp at hAction
  rw [bindIOResult_apply] at hAction
  cases hExec : completeDeterministicEntropyRequest guestMemory transport.device world0 with
  | error err world1 =>
    simp [hExec] at hAction
  | ok execResult world1 =>
    cases execResult with
    | error err =>
      simp [hExec] at hAction
    | ok nextDevice =>
      simp [hExec] at hAction
      rw [bindIOResult_apply] at hAction
      cases hPulse :
        pulseIrqLine vm ({ transport with device := nextDevice }).interruptLine world1 with
      | error err world2 =>
        simp [hPulse] at hAction
      | ok pulseResult world2 =>
        cases pulseResult with
        | error err =>
          simp [hPulse] at hAction
        | ok _ =>
          simp [hPulse] at hAction
          cases hAction
          have hExecRuns :
              IOResultRunsTo
                (completeDeterministicEntropyRequest guestMemory transport.device)
                nextDevice := by
            exact ⟨world0, world1, by simpa using hExec⟩
          rcases completeDeterministicEntropyRequest_ok_exists_report guestMemory
              transport.device hExecRuns with
              ⟨report, hReportExec, hWrites, hTraceRealized, _hActive, _hLatched,
                _hPrng, _hCompleted, _hInterrupt⟩
          exact ⟨nextDevice, report, rfl, hReportExec, hWrites, hTraceRealized⟩

/-- Once Linux BAR access has been observed as a write that decodes to `processQueue`, the
platform shell is just BAR write decoding followed by the BAR action proof above. -/
theorem handleLinuxVirtioPciBarAccess_write_processQueue_refines
    (vm : Kvm.Vm) (runArea : Kvm.RunArea) (guestMemory : Kvm.GuestMemory)
    (state : LinuxPlatformState) (access : MmioAccess)
    {afterWrite : VirtioPciState} {nextState : LinuxPlatformState}
    (hWriteDir : access.direction = .write)
    (hWrite : virtioPciBarWrite state.bus.virtioPci access.address access.width access.value =
      .ok (afterWrite, .processQueue))
    (hExit : IOResultRunsTo
      (handleLinuxVirtioPciBarAccess vm runArea guestMemory state access)
      nextState) :
    nextState.console = state.console ∧
      ∃ nextDevice report,
        nextState.bus.virtioPci = { afterWrite with device := nextDevice } ∧
        IOResultRunsTo
          (completeDeterministicEntropyRequestWithReport guestMemory afterWrite.device)
          (nextDevice, report) ∧
        report.writes = virtioEntropyCompletionWrites report.plan ∧
        virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes := by
  rcases hExit with ⟨world0, worldFinal, hExit⟩
  unfold handleLinuxVirtioPciBarAccess at hExit
  simp [hWriteDir, hWrite] at hExit
  rw [mapIOResult_apply] at hExit
  cases hAction :
      handleLinuxVirtioPciBarAction vm guestMemory afterWrite .processQueue world0 with
  | error err world1 =>
      simp [hAction] at hExit
  | ok actionResult world1 =>
      cases actionResult with
      | error err =>
          simp [hAction] at hExit
      | ok finalPci =>
          have hMatch := hExit
          simp [hAction] at hMatch
          rcases hMatch with ⟨rfl, rfl⟩
          have hActionRuns :
              IOResultRunsTo
                (handleLinuxVirtioPciBarAction vm guestMemory afterWrite .processQueue)
                finalPci := by
            exact ⟨world0, world1, by simpa using hAction⟩
          rcases handleLinuxVirtioPciBarAction_processQueue_refines vm guestMemory afterWrite
              hActionRuns with
            ⟨nextDevice, report, hTransport, hReportExec, hWrites, hTraceRealized⟩
          refine ⟨rfl, ?_⟩
          exact ⟨nextDevice, report, by simpa using hTransport, hReportExec, hWrites,
            hTraceRealized⟩

/-- Once Linux BAR handling has already decoded a `processQueue` write, the only remaining device
transition is the rng executor itself, which preserves the live and latched queue. The packaged
descriptor-validity judgment therefore carries from the post-write device to the resulting one. -/
theorem handleLinuxVirtioPciBarAccess_write_processQueue_preserves_descriptorValidity
    (guestMemorySize : UInt64) (vm : Kvm.Vm) (runArea : Kvm.RunArea)
    (guestMemory : Kvm.GuestMemory) (state : LinuxPlatformState) (access : MmioAccess)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {afterWrite : VirtioPciState} {nextState : LinuxPlatformState}
    (hWriteDir : access.direction = .write)
    (hWrite : virtioPciBarWrite state.bus.virtioPci access.address access.width access.value =
      .ok (afterWrite, .processQueue))
    (hHandle : IOResultRunsTo
      (handleLinuxVirtioPciBarAccess vm runArea guestMemory state access)
      nextState)
    (hValid : descriptorValidForDevice guestMemorySize afterWrite.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext) :
    descriptorValidForDevice guestMemorySize nextState.bus.virtioPci.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext := by
  rcases handleLinuxVirtioPciBarAccess_write_processQueue_refines vm runArea guestMemory state
      access hWriteDir hWrite hHandle with
    ⟨_hConsole, nextDevice, report, hTransport, hReportExec, _hWrites, _hTraceRealized⟩
  rcases completeDeterministicEntropyRequestWithReport_success_refines_executor guestMemory
      afterWrite.device hReportExec with
    ⟨_hWrites, _hWrapperTrace, hActive, hLatched, _hPrng, _hCompleted, _hInterrupt⟩
  have hPreserve : preservesLiveQueue afterWrite.device nextDevice := ⟨hActive, hLatched⟩
  have hValidNext :
      descriptorValidForDevice guestMemorySize nextDevice availIdx usedIdx head descAddrLow
        descAddrHigh descLen descFlags descNext :=
    (descriptorValidForDevice_iff_preserved_queue guestMemorySize availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext hPreserve).mp hValid
  simpa [hTransport] using hValidNext

/-- With an explicit observed MMIO access, the Linux MMIO shell reaches the virtio-pci BAR helper
exactly on the routed BAR branch; the remaining trust boundary is only the host MMIO observation. -/
theorem handleLinuxMmioAccess_virtioPciBar_processQueue_refines
    (vm : Kvm.Vm) (runArea : Kvm.RunArea) (guestMemory : Kvm.GuestMemory)
    (state : LinuxPlatformState) (access : MmioAccess)
    {afterWrite : VirtioPciState} {nextState : LinuxPlatformState}
    (hRoute : routePlatformMmioAccess state.bus.virtioPci access = .virtioPciBar)
    (hWriteDir : access.direction = .write)
    (hWrite : virtioPciBarWrite state.bus.virtioPci access.address access.width access.value =
      .ok (afterWrite, .processQueue))
    (hHandle : IOResultRunsTo
      (handleLinuxMmioAccess vm runArea guestMemory state access)
      nextState) :
    nextState.console = state.console ∧
      ∃ nextDevice report,
        nextState.bus.virtioPci = { afterWrite with device := nextDevice } ∧
        IOResultRunsTo
          (completeDeterministicEntropyRequestWithReport guestMemory afterWrite.device)
          (nextDevice, report) ∧
        report.writes = virtioEntropyCompletionWrites report.plan ∧
        virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes := by
  rcases hHandle with ⟨world0, worldFinal, hHandle⟩
  have hBarHandle :
      IOResultRunsTo
        (handleLinuxVirtioPciBarAccess vm runArea guestMemory state access)
        nextState := by
    exact ⟨world0, worldFinal, by
      unfold handleLinuxMmioAccess at hHandle
      simpa [hRoute] using hHandle⟩
  exact handleLinuxVirtioPciBarAccess_write_processQueue_refines vm runArea guestMemory state
    access hWriteDir hWrite hBarHandle

/-- The Linux MMIO shell only adds the routed BAR branch above the explicit BAR handler, so the
same packaged descriptor-validity judgment carries from the post-write device into the resulting
platform state. -/
theorem handleLinuxMmioAccess_virtioPciBar_processQueue_preserves_descriptorValidity
    (guestMemorySize : UInt64) (vm : Kvm.Vm) (runArea : Kvm.RunArea)
    (guestMemory : Kvm.GuestMemory) (state : LinuxPlatformState) (access : MmioAccess)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {afterWrite : VirtioPciState} {nextState : LinuxPlatformState}
    (hRoute : routePlatformMmioAccess state.bus.virtioPci access = .virtioPciBar)
    (hWriteDir : access.direction = .write)
    (hWrite : virtioPciBarWrite state.bus.virtioPci access.address access.width access.value =
      .ok (afterWrite, .processQueue))
    (hHandle : IOResultRunsTo
      (handleLinuxMmioAccess vm runArea guestMemory state access)
      nextState)
    (hValid : descriptorValidForDevice guestMemorySize afterWrite.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext) :
    descriptorValidForDevice guestMemorySize nextState.bus.virtioPci.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext := by
  rcases hHandle with ⟨world0, worldFinal, hHandle⟩
  have hBarHandle :
      IOResultRunsTo
        (handleLinuxVirtioPciBarAccess vm runArea guestMemory state access)
        nextState := by
    exact ⟨world0, worldFinal, by
      unfold handleLinuxMmioAccess at hHandle
      simpa [hRoute] using hHandle⟩
  exact handleLinuxVirtioPciBarAccess_write_processQueue_preserves_descriptorValidity
    guestMemorySize vm runArea guestMemory state access availIdx usedIdx head descAddrLow
    descAddrHigh descLen descFlags descNext hWriteDir hWrite hBarHandle hValid

/-- `handleLinuxMmioExit` adds only the observed MMIO access above the explicit-access Linux BAR
route theorem, so once that access is fixed the same executor-trace facts follow. -/
theorem handleLinuxMmioExit_virtioPciBar_processQueue_refines
    (vm : Kvm.Vm) (runArea : Kvm.RunArea) (guestMemory : Kvm.GuestMemory)
    (state : LinuxPlatformState) (access : MmioAccess)
    {afterWrite : VirtioPciState} {nextState : LinuxPlatformState}
    (hRead : readMmioAccess runArea = pure access)
    (hRoute : routePlatformMmioAccess state.bus.virtioPci access = .virtioPciBar)
    (hWriteDir : access.direction = .write)
    (hWrite : virtioPciBarWrite state.bus.virtioPci access.address access.width access.value =
      .ok (afterWrite, .processQueue))
    (hHandle : IOResultRunsTo
      (handleLinuxMmioAccess vm runArea guestMemory state access)
      nextState) :
    IOResultRunsTo (handleLinuxMmioExit vm runArea guestMemory state) nextState ∧
      nextState.console = state.console ∧
      ∃ nextDevice report,
        nextState.bus.virtioPci = { afterWrite with device := nextDevice } ∧
        IOResultRunsTo
          (completeDeterministicEntropyRequestWithReport guestMemory afterWrite.device)
          (nextDevice, report) ∧
        report.writes = virtioEntropyCompletionWrites report.plan ∧
        virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes := by
  rcases handleLinuxMmioAccess_virtioPciBar_processQueue_refines vm runArea guestMemory state
      access hRoute hWriteDir hWrite hHandle with
    ⟨hConsole, nextDevice, report, hTransport, hReportExec, hTrace, hTraceRealized⟩
  rcases hHandle with ⟨world0, worldFinal, hHandle⟩
  have hExitHandle :
      IOResultRunsTo (handleLinuxMmioExit vm runArea guestMemory state) nextState := by
    have hReadWorld : readMmioAccess runArea world0 = EST.Out.ok access world0 := by
      simpa using congrFun hRead world0
    refine ⟨world0, worldFinal, ?_⟩
    unfold handleLinuxMmioExit
    rw [ioBind_apply]
    simp [hReadWorld, hHandle]
  exact ⟨hExitHandle, hConsole, ⟨nextDevice, report, hTransport, hReportExec,
    hTrace, hTraceRealized⟩⟩

end Microvmm
