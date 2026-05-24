import Microvmm.Proof.Kvm.RawBoundary
import Microvmm.Proof.Virtio.Cve2026_5747
import Microvmm.Proof.Virtio.Core
import Microvmm.Proof.Virtio.RngExecution
import Microvmm.Proof.Virtio.Rng
import Microvmm.VirtioMmio

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

private theorem virtioMmioWrappedDeviceWrite_ok_inv
    (deviceWrite : ErrnoResult VirtioDeviceState) (resultAction : MmioWriteAction)
    {next : VirtioDeviceState} {action : MmioWriteAction}
    (hWrite :
      (do
        let nextDevice ← deviceWrite
        .ok (nextDevice, resultAction)) =
        .ok (next, action)) :
    deviceWrite = .ok next ∧ action = resultAction := by
  cases hDeviceWrite : deviceWrite with
  | error err =>
      simp [hDeviceWrite] at hWrite
      cases hWrite
  | ok nextDevice =>
      simp [hDeviceWrite] at hWrite
      cases hWrite
      exact ⟨by simp, rfl⟩

private theorem virtioMmioWrappedProcessQueueWrite_ok_inv
    (deviceWrite : ErrnoResult VirtioDeviceState) {next : VirtioDeviceState}
    (hWrite :
      (do
        let nextDevice ← deviceWrite
        .ok (nextDevice, MmioWriteAction.processQueue)) =
        .ok (next, MmioWriteAction.processQueue)) :
    deviceWrite = .ok next := by
  exact
    (virtioMmioWrappedDeviceWrite_ok_inv deviceWrite MmioWriteAction.processQueue hWrite).1

private def virtioMmioQueueAddrOffset (field : QueueAddrField) (highHalf : Bool) : Nat :=
  match field with
  | .desc => if highHalf then 0x084 else 0x080
  | .avail => if highHalf then 0x094 else 0x090
  | .used => if highHalf then 0x0a4 else 0x0a0

/-- The MMIO queue-size register is a thin transport wrapper over the shared virtio core, so the
core's post-activation queue-latching and DMA-target stability lemmas apply unchanged at the MMIO
surface. -/
theorem virtioMmioQueueNumWriteDevice_postActivation_safe (device : VirtioDeviceState)
    (value usedIdx head : UInt32) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : virtioMmioQueueNumWriteDevice device value = .ok next) :
    queueConfigLatched next ∧
      deterministicEntropyDmaTargetsOfDevice next usedIdx head =
        deterministicEntropyDmaTargetsOfDevice device usedIdx head := by
  have hCore : writeQueueNum device value = .ok next := by
    simpa [virtioMmioQueueNumWriteDevice] using hWrite
  exact ⟨
    cve_2026_5747_queueNum_postActivation_safe device value hActive hLatched hCore,
    writeQueueNum_keeps_deterministicEntropyDmaTargets_whenActive device value usedIdx head
      hActive hCore
  ⟩

/-- The same transport-wrapper argument applies to MMIO `QueueReady`. -/
theorem virtioMmioQueueReadyWriteDevice_postActivation_safe (device : VirtioDeviceState)
    (value usedIdx head : UInt32) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : virtioMmioQueueReadyWriteDevice device value = .ok next) :
    queueConfigLatched next ∧
      deterministicEntropyDmaTargetsOfDevice next usedIdx head =
        deterministicEntropyDmaTargetsOfDevice device usedIdx head := by
  have hCore : writeQueueReady device value = .ok next := by
    simpa [virtioMmioQueueReadyWriteDevice] using hWrite
  exact ⟨
    cve_2026_5747_queueReady_postActivation_safe device value hActive hLatched hCore,
    writeQueueReady_keeps_deterministicEntropyDmaTargets_whenActive device value usedIdx head
      hActive hCore
  ⟩

/-- The MMIO queue-address registers also inherit the shared queue-latching and DMA-target
stability argument because the transport only forwards the decoded field write. -/
theorem virtioMmioQueueAddrWriteDevice_postActivation_safe (device : VirtioDeviceState)
    (field : QueueAddrField) (value : UInt32) (highHalf : Bool) (usedIdx head : UInt32)
    {next : VirtioDeviceState} (hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : virtioMmioQueueAddrWriteDevice device field value highHalf = .ok next) :
    queueConfigLatched next ∧
      deterministicEntropyDmaTargetsOfDevice next usedIdx head =
        deterministicEntropyDmaTargetsOfDevice device usedIdx head := by
  have hCore : writeQueueAddr device field value highHalf = .ok next := by
    simpa [virtioMmioQueueAddrWriteDevice] using hWrite
  exact ⟨
    cve_2026_5747_queueAddr_postActivation_safe device field value highHalf hActive hLatched hCore,
    writeQueueAddr_keeps_deterministicEntropyDmaTargets_whenActive device field value highHalf
      usedIdx head hActive hCore
  ⟩

/-- The decoded MMIO queue-size write entry point is still a thin reduction onto the shared queue
write helper, so post-activation queue safety carries through the real decoded transport path. -/
theorem virtioMmioWriteOffset_queueNum_postActivation_safe (device : VirtioDeviceState)
    (value usedIdx head : UInt32) {next : VirtioDeviceState} {action : MmioWriteAction}
    (hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : virtioMmioWriteOffset device 0x038 value = .ok (next, action)) :
    action = .none ∧
      queueConfigLatched next ∧
      deterministicEntropyDmaTargetsOfDevice next usedIdx head =
        deterministicEntropyDmaTargetsOfDevice device usedIdx head := by
  have hWrapperAction :
      virtioMmioQueueNumWriteDevice device value = .ok next ∧
        action = MmioWriteAction.none := by
    exact virtioMmioWrappedDeviceWrite_ok_inv
      (virtioMmioQueueNumWriteDevice device value)
      MmioWriteAction.none
      (by
        simpa [virtioMmioWriteOffset, virtioMmioWriteQueueNum] using hWrite)
  rcases hWrapperAction with ⟨hWrapper, hAction⟩
  rcases virtioMmioQueueNumWriteDevice_postActivation_safe device value usedIdx head hActive
      hLatched hWrapper with ⟨hNextLatched, hTargets⟩
  exact ⟨hAction, hNextLatched, hTargets⟩

/-- The decoded MMIO queue-ready write path inherits the same post-activation safety facts. -/
theorem virtioMmioWriteOffset_queueReady_postActivation_safe (device : VirtioDeviceState)
    (value usedIdx head : UInt32) {next : VirtioDeviceState} {action : MmioWriteAction}
    (hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : virtioMmioWriteOffset device 0x044 value = .ok (next, action)) :
    action = .none ∧
      queueConfigLatched next ∧
      deterministicEntropyDmaTargetsOfDevice next usedIdx head =
        deterministicEntropyDmaTargetsOfDevice device usedIdx head := by
  have hWrapperAction :
      virtioMmioQueueReadyWriteDevice device value = .ok next ∧
        action = MmioWriteAction.none := by
    exact virtioMmioWrappedDeviceWrite_ok_inv
      (virtioMmioQueueReadyWriteDevice device value)
      MmioWriteAction.none
      (by
        simpa [virtioMmioWriteOffset, virtioMmioWriteQueueReady] using hWrite)
  rcases hWrapperAction with ⟨hWrapper, hAction⟩
  rcases virtioMmioQueueReadyWriteDevice_postActivation_safe device value usedIdx head hActive
      hLatched hWrapper with ⟨hNextLatched, hTargets⟩
  exact ⟨hAction, hNextLatched, hTargets⟩

/-- The decoded MMIO queue-address write path also reduces directly to the shared queue-address
helper, so the real transport decode does not weaken the post-activation safety argument. -/
theorem virtioMmioWriteOffset_queueAddr_postActivation_safe (device : VirtioDeviceState)
    (field : QueueAddrField) (value : UInt32) (highHalf : Bool) (usedIdx head : UInt32)
    {next : VirtioDeviceState} {action : MmioWriteAction}
    (hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : virtioMmioWriteOffset device (virtioMmioQueueAddrOffset field highHalf) value =
        .ok (next, action)) :
    action = .none ∧
      queueConfigLatched next ∧
      deterministicEntropyDmaTargetsOfDevice next usedIdx head =
        deterministicEntropyDmaTargetsOfDevice device usedIdx head := by
  have hWrapperAction :
      virtioMmioQueueAddrWriteDevice device field value highHalf = .ok next ∧
        action = MmioWriteAction.none := by
    cases field <;> cases highHalf <;>
      exact virtioMmioWrappedDeviceWrite_ok_inv
        (virtioMmioQueueAddrWriteDevice device _ value _)
        MmioWriteAction.none
        (by
          simpa [virtioMmioWriteOffset, virtioMmioQueueAddrOffset, virtioMmioWriteQueueAddr]
            using hWrite)
  rcases hWrapperAction with ⟨hWrapper, hAction⟩
  rcases virtioMmioQueueAddrWriteDevice_postActivation_safe device field value highHalf usedIdx
      head hActive hLatched hWrapper with ⟨hNextLatched, hTargets⟩
  exact ⟨hAction, hNextLatched, hTargets⟩

/-- Post-activation MMIO queue-size writes preserve the packaged descriptor-validity judgment for
the same observed request because the live queue is unchanged. -/
theorem virtioMmioQueueNumWriteDevice_preserves_descriptorValidity
    (device : VirtioDeviceState) (value : UInt32) (guestMemorySize : UInt64)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {next : VirtioDeviceState} (hActive : device.activeQueue.isSome)
    (hWrite : virtioMmioQueueNumWriteDevice device value = .ok next)
    (hValid : descriptorValidForDevice guestMemorySize device availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext) :
    descriptorValidForDevice guestMemorySize next availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext := by
  have hCore : writeQueueNum device value = .ok next := by
    simpa [virtioMmioQueueNumWriteDevice] using hWrite
  exact (descriptorValidForDevice_iff_preserved_queue guestMemorySize availIdx usedIdx head
    descAddrLow descAddrHigh descLen descFlags descNext
    (writeQueueNum_preservesLiveQueue_whenActive device value hActive hCore)).mp hValid

/-- Post-activation MMIO `QueueReady` writes preserve the same packaged descriptor-validity
judgment. -/
theorem virtioMmioQueueReadyWriteDevice_preserves_descriptorValidity
    (device : VirtioDeviceState) (value : UInt32) (guestMemorySize : UInt64)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {next : VirtioDeviceState} (hActive : device.activeQueue.isSome)
    (hWrite : virtioMmioQueueReadyWriteDevice device value = .ok next)
    (hValid : descriptorValidForDevice guestMemorySize device availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext) :
    descriptorValidForDevice guestMemorySize next availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext := by
  have hCore : writeQueueReady device value = .ok next := by
    simpa [virtioMmioQueueReadyWriteDevice] using hWrite
  exact (descriptorValidForDevice_iff_preserved_queue guestMemorySize availIdx usedIdx head
    descAddrLow descAddrHigh descLen descFlags descNext
    (writeQueueReady_preservesLiveQueue_whenActive device value hActive hCore)).mp hValid

/-- Post-activation MMIO queue-address writes likewise preserve descriptor validity because the
same active queue remains authoritative. -/
theorem virtioMmioQueueAddrWriteDevice_preserves_descriptorValidity
    (device : VirtioDeviceState) (field : QueueAddrField) (value : UInt32) (highHalf : Bool)
    (guestMemorySize : UInt64)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {next : VirtioDeviceState} (hActive : device.activeQueue.isSome)
    (hWrite : virtioMmioQueueAddrWriteDevice device field value highHalf = .ok next)
    (hValid : descriptorValidForDevice guestMemorySize device availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext) :
    descriptorValidForDevice guestMemorySize next availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext := by
  have hCore : writeQueueAddr device field value highHalf = .ok next := by
    simpa [virtioMmioQueueAddrWriteDevice] using hWrite
  exact (descriptorValidForDevice_iff_preserved_queue guestMemorySize availIdx usedIdx head
    descAddrLow descAddrHigh descLen descFlags descNext
    (writeQueueAddr_preservesLiveQueue_whenActive device field value highHalf hActive hCore)).mp hValid

/-- The decoded MMIO queue-size write path preserves descriptor validity after transport decode. -/
theorem virtioMmioWriteOffset_queueNum_preserves_descriptorValidity (device : VirtioDeviceState)
    (value : UInt32) (guestMemorySize : UInt64)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {next : VirtioDeviceState} {action : MmioWriteAction}
    (hActive : device.activeQueue.isSome)
    (hWrite : virtioMmioWriteOffset device 0x038 value = .ok (next, action))
    (hValid : descriptorValidForDevice guestMemorySize device availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext) :
    action = .none ∧
      descriptorValidForDevice guestMemorySize next availIdx usedIdx head descAddrLow
        descAddrHigh descLen descFlags descNext := by
  have hWrapperAction :
      virtioMmioQueueNumWriteDevice device value = .ok next ∧
        action = MmioWriteAction.none := by
    exact virtioMmioWrappedDeviceWrite_ok_inv
      (virtioMmioQueueNumWriteDevice device value)
      MmioWriteAction.none
      (by
        simpa [virtioMmioWriteOffset, virtioMmioWriteQueueNum] using hWrite)
  rcases hWrapperAction with ⟨hWrapper, hAction⟩
  exact ⟨hAction, virtioMmioQueueNumWriteDevice_preserves_descriptorValidity device value
    guestMemorySize availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext
    hActive hWrapper hValid⟩

/-- The decoded MMIO `QueueReady` write path preserves descriptor validity after transport decode. -/
theorem virtioMmioWriteOffset_queueReady_preserves_descriptorValidity (device : VirtioDeviceState)
    (value : UInt32) (guestMemorySize : UInt64)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {next : VirtioDeviceState} {action : MmioWriteAction}
    (hActive : device.activeQueue.isSome)
    (hWrite : virtioMmioWriteOffset device 0x044 value = .ok (next, action))
    (hValid : descriptorValidForDevice guestMemorySize device availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext) :
    action = .none ∧
      descriptorValidForDevice guestMemorySize next availIdx usedIdx head descAddrLow
        descAddrHigh descLen descFlags descNext := by
  have hWrapperAction :
      virtioMmioQueueReadyWriteDevice device value = .ok next ∧
        action = MmioWriteAction.none := by
    exact virtioMmioWrappedDeviceWrite_ok_inv
      (virtioMmioQueueReadyWriteDevice device value)
      MmioWriteAction.none
      (by
        simpa [virtioMmioWriteOffset, virtioMmioWriteQueueReady] using hWrite)
  rcases hWrapperAction with ⟨hWrapper, hAction⟩
  exact ⟨hAction, virtioMmioQueueReadyWriteDevice_preserves_descriptorValidity device value
    guestMemorySize availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext
    hActive hWrapper hValid⟩

/-- The decoded MMIO queue-address write path preserves descriptor validity after transport decode. -/
theorem virtioMmioWriteOffset_queueAddr_preserves_descriptorValidity (device : VirtioDeviceState)
    (field : QueueAddrField) (value : UInt32) (highHalf : Bool) (guestMemorySize : UInt64)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {next : VirtioDeviceState} {action : MmioWriteAction}
    (hActive : device.activeQueue.isSome)
    (hWrite : virtioMmioWriteOffset device (virtioMmioQueueAddrOffset field highHalf) value =
      .ok (next, action))
    (hValid : descriptorValidForDevice guestMemorySize device availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext) :
    action = .none ∧
      descriptorValidForDevice guestMemorySize next availIdx usedIdx head descAddrLow
        descAddrHigh descLen descFlags descNext := by
  have hWrapperAction :
      virtioMmioQueueAddrWriteDevice device field value highHalf = .ok next ∧
        action = MmioWriteAction.none := by
    cases field <;> cases highHalf <;>
      exact virtioMmioWrappedDeviceWrite_ok_inv
        (virtioMmioQueueAddrWriteDevice device _ value _)
        MmioWriteAction.none
        (by
          simpa [virtioMmioWriteOffset, virtioMmioQueueAddrOffset, virtioMmioWriteQueueAddr]
            using hWrite)
  rcases hWrapperAction with ⟨hWrapper, hAction⟩
  exact ⟨hAction, virtioMmioQueueAddrWriteDevice_preserves_descriptorValidity device field value
    highHalf guestMemorySize availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags
    descNext hActive hWrapper hValid⟩

/-- The decoded MMIO notify branch reaches the real rng executor: notification preserves the
latched queue, and a successful completion from that state still realizes the executor trace while
keeping the same DMA-target view of the active queue. -/
theorem virtioMmioWriteOffset_notify_then_complete_refines (guestMemory : GuestMemory)
    (device : VirtioDeviceState) (usedIdx head : UInt32)
    {afterWrite next : VirtioDeviceState} {report : VirtioEntropyExecutionReport}
  (_hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : virtioMmioWriteOffset device 0x050 0 = .ok (afterWrite, .processQueue))
    (hExec : IOResultRunsTo
      (completeDeterministicEntropyRequestWithReport guestMemory afterWrite)
      (next, report)) :
    queueConfigLatched afterWrite ∧
      queueConfigLatched next ∧
      deterministicEntropyDmaTargetsOfDevice next usedIdx head =
        deterministicEntropyDmaTargetsOfDevice device usedIdx head ∧
      report.writes = virtioEntropyCompletionWrites report.plan ∧
      virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes := by
  have hNotify : markQueueNotified device = .ok afterWrite := by
    exact virtioMmioWrappedProcessQueueWrite_ok_inv
      (markQueueNotified device)
      (by
        simpa [virtioMmioWriteOffset] using hWrite)
  have hAfterPreserve : preservesLiveQueue device afterWrite :=
    markQueueNotified_preservesLiveQueue device hNotify
  have hAfterLatched : queueConfigLatched afterWrite :=
    preservesLiveQueue_keeps_queueConfigLatched hAfterPreserve hLatched
  have hAfterTargets : deterministicEntropyDmaTargetsOfDevice afterWrite usedIdx head =
      deterministicEntropyDmaTargetsOfDevice device usedIdx head :=
    preservesLiveQueue_keeps_deterministicEntropyDmaTargets usedIdx head hAfterPreserve
  rcases completeDeterministicEntropyRequestWithReport_success_refines_executor guestMemory
      afterWrite hExec with ⟨hWrites, hWrapperTrace, hNextActive, hNextLatched,
        _hPrng, _hCompleted, _hInterrupt⟩
  have hNextPreserve : preservesLiveQueue afterWrite next := ⟨hNextActive, hNextLatched⟩
  have hNextLatchedProp : queueConfigLatched next :=
    preservesLiveQueue_keeps_queueConfigLatched hNextPreserve hAfterLatched
  have hNextTargetsFromAfter : deterministicEntropyDmaTargetsOfDevice next usedIdx head =
      deterministicEntropyDmaTargetsOfDevice afterWrite usedIdx head :=
    preservesLiveQueue_keeps_deterministicEntropyDmaTargets usedIdx head hNextPreserve
  exact ⟨hAfterLatched, hNextLatchedProp, hNextTargetsFromAfter.trans hAfterTargets,
    hWrites, hWrapperTrace⟩

/-- Once the standalone MMIO shell has an explicit observed `MmioAccess`, the surviving proof
payload on the `processQueue` branch is the recovered executor report rather than the stale raw
decode equality. -/
theorem handleVirtioMmioAccess_processQueue_refines
    (runArea : Kvm.RunArea) (guestMemory : Kvm.GuestMemory) (device : VirtioDeviceState)
    (access : MmioAccess) {afterWrite next : VirtioDeviceState}
    (hStep : stepVirtioMmioAccess device access =
      .ok { state := afterWrite, response := none, action := .processQueue })
    (hHandle : IOResultRunsTo
      (handleVirtioMmioAccess runArea guestMemory device access)
      next) :
    ∃ report : VirtioEntropyExecutionReport,
      IOResultRunsTo (completeDeterministicEntropyRequestWithReport guestMemory afterWrite)
        (next, report) ∧
      report.writes = virtioEntropyCompletionWrites report.plan ∧
      virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes := by
  rcases hHandle with ⟨world0, worldFinal, hHandle⟩
  have hExecRuns :
      IOResultRunsTo (completeDeterministicEntropyRequest guestMemory afterWrite) next := by
    refine ⟨world0, worldFinal, ?_⟩
    unfold handleVirtioMmioAccess at hHandle
    simpa [hStep] using hHandle
  rcases completeDeterministicEntropyRequest_ok_exists_report guestMemory afterWrite hExecRuns with
    ⟨report, hReportExec, hWrites, hTraceRealized, _hActive, _hLatched, _hPrng,
      _hCompleted, _hInterrupt⟩
  exact ⟨report, hReportExec, hWrites, hTraceRealized⟩

/-- `handleVirtioMmioExit` adds only the observed MMIO access above the explicit-access shell, so
once that access is fixed the surviving witness is the recovered executor report. -/
theorem handleVirtioMmioExit_observed_processQueue_refines
    (runArea : Kvm.RunArea) (guestMemory : Kvm.GuestMemory) (device : VirtioDeviceState)
    (access : MmioAccess) {afterWrite next : VirtioDeviceState}
    (hRead : readMmioAccess runArea = pure access)
    (hStep : stepVirtioMmioAccess device access =
      .ok { state := afterWrite, response := none, action := .processQueue })
    (hHandle : IOResultRunsTo
      (handleVirtioMmioAccess runArea guestMemory device access)
      next) :
    IOResultRunsTo (handleVirtioMmioExit runArea guestMemory device) next ∧
      ∃ report : VirtioEntropyExecutionReport,
        IOResultRunsTo (completeDeterministicEntropyRequestWithReport guestMemory afterWrite)
          (next, report) ∧
        report.writes = virtioEntropyCompletionWrites report.plan ∧
        virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes := by
  rcases handleVirtioMmioAccess_processQueue_refines runArea guestMemory device access hStep hHandle
      with ⟨report, hReportExec, hTrace, hTraceRealized⟩
  rcases hHandle with ⟨world0, worldFinal, hHandle⟩
  have hExitHandle : IOResultRunsTo (handleVirtioMmioExit runArea guestMemory device) next := by
    have hReadWorld : readMmioAccess runArea world0 = EST.Out.ok access world0 := by
      simpa using congrFun hRead world0
    refine ⟨world0, worldFinal, ?_⟩
    unfold handleVirtioMmioExit
    rw [ioBind_apply]
    simp [hReadWorld, hHandle]
  exact ⟨hExitHandle, ⟨report, hReportExec, hTrace, hTraceRealized⟩⟩

theorem runVirtioEntropyLoop_mmio_processQueue_step_refines_upToRawBoundary
    (_remaining : Nat) (vcpu : Kvm.Vcpu) (runArea : Kvm.RunArea)
    (guestMemory : Kvm.GuestMemory) (device : VirtioDeviceState) (access : MmioAccess)
    {afterWrite next : VirtioDeviceState} {world0 world1 world2 world3 : World}
    (_hRun : runGuestOnce vcpu world0 = EST.Out.ok (Outcome.ok ()) world1)
    (_hExitReason : runExitReason runArea world1 = EST.Out.ok virtioMmioKvmExitMmio world2)
    (hRead : readMmioAccess runArea = pure access)
    (hStep : stepVirtioMmioAccess device access =
      .ok { state := afterWrite, response := none, action := .processQueue })
    (hHandle : handleVirtioMmioAccess runArea guestMemory device access world2 =
      EST.Out.ok (Outcome.ok next) world3) :
    VirtioMmioRawBoundary vcpu runArea guestMemory ∧
      IOResultRunsTo (handleVirtioMmioExit runArea guestMemory device) next ∧
      ∃ report : VirtioEntropyExecutionReport,
        IOResultRunsTo (completeDeterministicEntropyRequestWithReport guestMemory afterWrite)
          (next, report) ∧
        report.writes = virtioEntropyCompletionWrites report.plan ∧
        virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes := by
  have hHandleRuns : IOResultRunsTo
      (handleVirtioMmioAccess runArea guestMemory device access)
      next :=
    ioResultRunsTo_of_ok hHandle
  rcases handleVirtioMmioExit_observed_processQueue_refines runArea guestMemory device access
      hRead hStep hHandleRuns with
    ⟨hExitRuns, report, hReportExec, hTrace, hTraceRealized⟩
  exact ⟨virtioMmioRawBoundary_holds vcpu runArea guestMemory, hExitRuns,
    ⟨report, hReportExec, hTrace, hTraceRealized⟩⟩

end Microvmm
