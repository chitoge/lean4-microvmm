import Microvmm.Proof.Virtio.Cve2026_5747
import Microvmm.Proof.Virtio.Core
import Microvmm.Proof.Virtio.RngExecution
import Microvmm.Proof.Virtio.Rng
import Microvmm.VirtioPci

namespace Microvmm

private def virtioPciQueueAddrOffset (field : QueueAddrField) (highHalf : Bool) : Nat :=
  match field with
  | .desc => if highHalf then 0x24 else 0x20
  | .avail => if highHalf then 0x2c else 0x28
  | .used => if highHalf then 0x34 else 0x30

private theorem virtioPciWrappedDeviceWrite_ok_inv (state : VirtioPciState)
    (deviceWrite : ErrnoResult VirtioDeviceState) (resultAction : MmioWriteAction)
    {next : VirtioPciState} {action : MmioWriteAction}
    (hWrite :
      (do
        let nextDevice ← deviceWrite
        .ok ({ state with device := nextDevice }, resultAction)) =
        .ok (next, action)) :
    deviceWrite = .ok next.device ∧ action = resultAction := by
  cases hDeviceWrite : deviceWrite with
  | error err =>
      simp [hDeviceWrite] at hWrite
      cases hWrite
  | ok nextDevice =>
      simp [hDeviceWrite] at hWrite
      cases hWrite
      exact ⟨by simp, rfl⟩

private theorem virtioPciWrappedProcessQueueWrite_ok_inv (state : VirtioPciState)
    (deviceWrite : ErrnoResult VirtioDeviceState) {next : VirtioPciState}
    (hWrite :
      (do
        let nextDevice ← deviceWrite
        .ok ({ state with device := nextDevice }, MmioWriteAction.processQueue)) =
        .ok (next, MmioWriteAction.processQueue)) :
    deviceWrite = .ok next.device := by
  exact (virtioPciWrappedDeviceWrite_ok_inv state deviceWrite MmioWriteAction.processQueue hWrite).1

/-- The PCI common-config queue-size field is a thin transport wrapper over the shared virtio core,
so successful post-activation writes preserve both the queue-latching invariant and the rng DMA
targets derived from the active queue. -/
theorem virtioPciCommonCfgQueueNumWriteDevice_postActivation_safe (state : VirtioPciState)
  (value usedIdx head : UInt32) {next : VirtioDeviceState}
    (hActive : state.device.activeQueue.isSome)
    (hLatched : queueConfigLatched state.device)
    (hWrite : virtioPciCommonCfgQueueNumWriteDevice state value = .ok next) :
    queueConfigLatched next ∧
      deterministicEntropyDmaTargetsOfDevice next usedIdx head =
        deterministicEntropyDmaTargetsOfDevice state.device usedIdx head := by
  have hCore : writeQueueNum state.device (value &&& 0xffff) = .ok next := by
    simpa [virtioPciCommonCfgQueueNumWriteDevice] using hWrite
  exact ⟨
    cve_2026_5747_queueNum_postActivation_safe state.device (value &&& 0xffff) hActive hLatched hCore,
    writeQueueNum_keeps_deterministicEntropyDmaTargets_whenActive state.device (value &&& 0xffff)
      usedIdx head hActive hCore
  ⟩

/-- The same proof lifts directly to the PCI common-config `QueueReady` field. -/
theorem virtioPciCommonCfgQueueReadyWriteDevice_postActivation_safe (state : VirtioPciState)
  (value usedIdx head : UInt32) {next : VirtioDeviceState}
    (hActive : state.device.activeQueue.isSome)
    (hLatched : queueConfigLatched state.device)
    (hWrite : virtioPciCommonCfgQueueReadyWriteDevice state value = .ok next) :
    queueConfigLatched next ∧
      deterministicEntropyDmaTargetsOfDevice next usedIdx head =
        deterministicEntropyDmaTargetsOfDevice state.device usedIdx head := by
  have hCore : writeQueueReady state.device (value &&& 0xffff) = .ok next := by
    simpa [virtioPciCommonCfgQueueReadyWriteDevice] using hWrite
  exact ⟨
    cve_2026_5747_queueReady_postActivation_safe state.device (value &&& 0xffff) hActive hLatched hCore,
    writeQueueReady_keeps_deterministicEntropyDmaTargets_whenActive state.device (value &&& 0xffff)
      usedIdx head hActive hCore
  ⟩

/-- Queue-address writes through the PCI common-config window also inherit the shared transport-
agnostic hardening argument. -/
theorem virtioPciCommonCfgQueueAddrWriteDevice_postActivation_safe (state : VirtioPciState)
    (field : QueueAddrField) (value : UInt32) (highHalf : Bool) (usedIdx head : UInt32)
    {next : VirtioDeviceState} (hActive : state.device.activeQueue.isSome)
    (hLatched : queueConfigLatched state.device)
    (hWrite : virtioPciCommonCfgQueueAddrWriteDevice state field value highHalf = .ok next) :
    queueConfigLatched next ∧
      deterministicEntropyDmaTargetsOfDevice next usedIdx head =
        deterministicEntropyDmaTargetsOfDevice state.device usedIdx head := by
  have hCore : writeQueueAddr state.device field value highHalf = .ok next := by
    simpa [virtioPciCommonCfgQueueAddrWriteDevice] using hWrite
  exact ⟨
    cve_2026_5747_queueAddr_postActivation_safe state.device field value highHalf hActive hLatched hCore,
    writeQueueAddr_keeps_deterministicEntropyDmaTargets_whenActive state.device field value
      highHalf usedIdx head hActive hCore
  ⟩

/-- The decoded PCI common-config queue-size write path reduces directly to the existing shared
queue helper, so the real decoded transport preserves the post-activation safety argument. -/
theorem virtioPciBarWriteOffset_queueNum_postActivation_safe (state : VirtioPciState)
    (value usedIdx head : UInt32) {next : VirtioPciState} {action : MmioWriteAction}
    (hActive : state.device.activeQueue.isSome)
    (hLatched : queueConfigLatched state.device)
    (hWrite : virtioPciBarWriteOffset state 0x18 2 2 value = .ok (next, action)) :
    action = .none ∧
      queueConfigLatched next.device ∧
      deterministicEntropyDmaTargetsOfDevice next.device usedIdx head =
        deterministicEntropyDmaTargetsOfDevice state.device usedIdx head := by
  have hDecoded : virtioPciCommonCfgWrite state 0x18 2 value = .ok (next, action) := by
    simpa [virtioPciBarWriteOffset, virtioPciCommonCfgLength, virtioPciNotifyCfgOffset,
      virtioPciDeviceCfgOffset, virtioPciDeviceCfgLength] using hWrite
  have hWrapperAction :
      virtioPciCommonCfgQueueNumWriteDevice state value = .ok next.device ∧
        action = .none := by
    exact virtioPciWrappedDeviceWrite_ok_inv state
      (virtioPciCommonCfgQueueNumWriteDevice state value)
      MmioWriteAction.none
      (by
        simpa [virtioPciCommonCfgWrite, virtioPciCommonCfgWriteQueueNum] using hDecoded)
  rcases hWrapperAction with ⟨hWrapper, hAction⟩
  rcases virtioPciCommonCfgQueueNumWriteDevice_postActivation_safe state value usedIdx head
      hActive hLatched hWrapper with ⟨hNextLatched, hTargets⟩
  exact ⟨hAction, hNextLatched, hTargets⟩

/-- The decoded PCI common-config queue-ready path preserves the same post-activation facts. -/
theorem virtioPciBarWriteOffset_queueReady_postActivation_safe (state : VirtioPciState)
    (value usedIdx head : UInt32) {next : VirtioPciState} {action : MmioWriteAction}
    (hActive : state.device.activeQueue.isSome)
    (hLatched : queueConfigLatched state.device)
    (hWrite : virtioPciBarWriteOffset state 0x1c 2 2 value = .ok (next, action)) :
    action = .none ∧
      queueConfigLatched next.device ∧
      deterministicEntropyDmaTargetsOfDevice next.device usedIdx head =
        deterministicEntropyDmaTargetsOfDevice state.device usedIdx head := by
  have hDecoded : virtioPciCommonCfgWrite state 0x1c 2 value = .ok (next, action) := by
    simpa [virtioPciBarWriteOffset, virtioPciCommonCfgLength, virtioPciNotifyCfgOffset,
      virtioPciDeviceCfgOffset, virtioPciDeviceCfgLength] using hWrite
  have hWrapperAction :
      virtioPciCommonCfgQueueReadyWriteDevice state value = .ok next.device ∧
        action = .none := by
    exact virtioPciWrappedDeviceWrite_ok_inv state
      (virtioPciCommonCfgQueueReadyWriteDevice state value)
      MmioWriteAction.none
      (by
        simpa [virtioPciCommonCfgWrite, virtioPciCommonCfgWriteQueueReady] using hDecoded)
  rcases hWrapperAction with ⟨hWrapper, hAction⟩
  rcases virtioPciCommonCfgQueueReadyWriteDevice_postActivation_safe state value usedIdx head
      hActive hLatched hWrapper with ⟨hNextLatched, hTargets⟩
  exact ⟨hAction, hNextLatched, hTargets⟩

/-- Queue-address writes through the decoded PCI BAR path still reduce to the shared queue-address
helper after transport decoding. -/
theorem virtioPciBarWriteOffset_queueAddr_postActivation_safe (state : VirtioPciState)
    (field : QueueAddrField) (value : UInt32) (highHalf : Bool) (usedIdx head : UInt32)
    {next : VirtioPciState} {action : MmioWriteAction}
    (hActive : state.device.activeQueue.isSome)
    (hLatched : queueConfigLatched state.device)
    (hWrite : virtioPciBarWriteOffset state (virtioPciQueueAddrOffset field highHalf) 4 4 value =
        .ok (next, action)) :
    action = .none ∧
      queueConfigLatched next.device ∧
      deterministicEntropyDmaTargetsOfDevice next.device usedIdx head =
        deterministicEntropyDmaTargetsOfDevice state.device usedIdx head := by
  have hDecoded : virtioPciCommonCfgWrite state (virtioPciQueueAddrOffset field highHalf) 4 value =
      .ok (next, action) := by
    cases field <;> cases highHalf <;>
      simpa [virtioPciBarWriteOffset, virtioPciQueueAddrOffset, virtioPciCommonCfgLength,
        virtioPciNotifyCfgOffset, virtioPciDeviceCfgOffset, virtioPciDeviceCfgLength] using hWrite
  have hWrapperAction :
      virtioPciCommonCfgQueueAddrWriteDevice state field value highHalf = .ok next.device ∧
        action = .none := by
    cases field <;> cases highHalf <;>
      exact virtioPciWrappedDeviceWrite_ok_inv state
        (virtioPciCommonCfgQueueAddrWriteDevice state _ value _)
        MmioWriteAction.none
        (by
          simpa [virtioPciCommonCfgWrite, virtioPciQueueAddrOffset,
            virtioPciCommonCfgWriteQueueAddr] using hDecoded)
  rcases hWrapperAction with ⟨hWrapper, hAction⟩
  rcases virtioPciCommonCfgQueueAddrWriteDevice_postActivation_safe state field value highHalf
      usedIdx head hActive hLatched hWrapper with ⟨hNextLatched, hTargets⟩
  exact ⟨hAction, hNextLatched, hTargets⟩

/-- Post-activation PCI common-config queue-size writes preserve the packaged descriptor-validity
judgment for the same observed request. -/
theorem virtioPciCommonCfgQueueNumWriteDevice_preserves_descriptorValidity
    (state : VirtioPciState) (value : UInt32) (guestMemorySize : UInt64)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {next : VirtioDeviceState} (hActive : state.device.activeQueue.isSome)
    (hWrite : virtioPciCommonCfgQueueNumWriteDevice state value = .ok next)
    (hValid : descriptorValidForDevice guestMemorySize state.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext) :
    descriptorValidForDevice guestMemorySize next availIdx usedIdx head descAddrLow descAddrHigh
      descLen descFlags descNext := by
  have hCore : writeQueueNum state.device (value &&& 0xffff) = .ok next := by
    simpa [virtioPciCommonCfgQueueNumWriteDevice] using hWrite
  exact (descriptorValidForDevice_iff_preserved_queue guestMemorySize availIdx usedIdx head
    descAddrLow descAddrHigh descLen descFlags descNext
    (writeQueueNum_preservesLiveQueue_whenActive state.device (value &&& 0xffff) hActive hCore)).mp hValid

/-- Post-activation PCI common-config `QueueReady` writes preserve descriptor validity. -/
theorem virtioPciCommonCfgQueueReadyWriteDevice_preserves_descriptorValidity
    (state : VirtioPciState) (value : UInt32) (guestMemorySize : UInt64)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {next : VirtioDeviceState} (hActive : state.device.activeQueue.isSome)
    (hWrite : virtioPciCommonCfgQueueReadyWriteDevice state value = .ok next)
    (hValid : descriptorValidForDevice guestMemorySize state.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext) :
    descriptorValidForDevice guestMemorySize next availIdx usedIdx head descAddrLow descAddrHigh
      descLen descFlags descNext := by
  have hCore : writeQueueReady state.device (value &&& 0xffff) = .ok next := by
    simpa [virtioPciCommonCfgQueueReadyWriteDevice] using hWrite
  exact (descriptorValidForDevice_iff_preserved_queue guestMemorySize availIdx usedIdx head
    descAddrLow descAddrHigh descLen descFlags descNext
    (writeQueueReady_preservesLiveQueue_whenActive state.device (value &&& 0xffff) hActive hCore)).mp hValid

/-- Post-activation PCI common-config queue-address writes preserve descriptor validity. -/
theorem virtioPciCommonCfgQueueAddrWriteDevice_preserves_descriptorValidity
    (state : VirtioPciState) (field : QueueAddrField) (value : UInt32) (highHalf : Bool)
    (guestMemorySize : UInt64)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {next : VirtioDeviceState} (hActive : state.device.activeQueue.isSome)
    (hWrite : virtioPciCommonCfgQueueAddrWriteDevice state field value highHalf = .ok next)
    (hValid : descriptorValidForDevice guestMemorySize state.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext) :
    descriptorValidForDevice guestMemorySize next availIdx usedIdx head descAddrLow descAddrHigh
      descLen descFlags descNext := by
  have hCore : writeQueueAddr state.device field value highHalf = .ok next := by
    simpa [virtioPciCommonCfgQueueAddrWriteDevice] using hWrite
  exact (descriptorValidForDevice_iff_preserved_queue guestMemorySize availIdx usedIdx head
    descAddrLow descAddrHigh descLen descFlags descNext
    (writeQueueAddr_preservesLiveQueue_whenActive state.device field value highHalf hActive hCore)).mp hValid

/-- The decoded PCI BAR queue-size write path preserves descriptor validity after transport
decode. -/
theorem virtioPciBarWriteOffset_queueNum_preserves_descriptorValidity (state : VirtioPciState)
    (value : UInt32) (guestMemorySize : UInt64)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {next : VirtioPciState} {action : MmioWriteAction}
    (hActive : state.device.activeQueue.isSome)
    (hWrite : virtioPciBarWriteOffset state 0x18 2 2 value = .ok (next, action))
    (hValid : descriptorValidForDevice guestMemorySize state.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext) :
    action = .none ∧
      descriptorValidForDevice guestMemorySize next.device availIdx usedIdx head descAddrLow
        descAddrHigh descLen descFlags descNext := by
  have hDecoded : virtioPciCommonCfgWrite state 0x18 2 value = .ok (next, action) := by
    simpa [virtioPciBarWriteOffset, virtioPciCommonCfgLength, virtioPciNotifyCfgOffset,
      virtioPciDeviceCfgOffset, virtioPciDeviceCfgLength] using hWrite
  have hWrapperAction :
      virtioPciCommonCfgQueueNumWriteDevice state value = .ok next.device ∧
        action = .none := by
    exact virtioPciWrappedDeviceWrite_ok_inv state
      (virtioPciCommonCfgQueueNumWriteDevice state value)
      MmioWriteAction.none
      (by
        simpa [virtioPciCommonCfgWrite, virtioPciCommonCfgWriteQueueNum] using hDecoded)
  rcases hWrapperAction with ⟨hWrapper, hAction⟩
  exact ⟨hAction,
    virtioPciCommonCfgQueueNumWriteDevice_preserves_descriptorValidity state value guestMemorySize
      availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext hActive hWrapper
      hValid⟩

/-- The decoded PCI BAR `QueueReady` write path preserves descriptor validity after transport
decode. -/
theorem virtioPciBarWriteOffset_queueReady_preserves_descriptorValidity (state : VirtioPciState)
    (value : UInt32) (guestMemorySize : UInt64)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {next : VirtioPciState} {action : MmioWriteAction}
    (hActive : state.device.activeQueue.isSome)
    (hWrite : virtioPciBarWriteOffset state 0x1c 2 2 value = .ok (next, action))
    (hValid : descriptorValidForDevice guestMemorySize state.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext) :
    action = .none ∧
      descriptorValidForDevice guestMemorySize next.device availIdx usedIdx head descAddrLow
        descAddrHigh descLen descFlags descNext := by
  have hDecoded : virtioPciCommonCfgWrite state 0x1c 2 value = .ok (next, action) := by
    simpa [virtioPciBarWriteOffset, virtioPciCommonCfgLength, virtioPciNotifyCfgOffset,
      virtioPciDeviceCfgOffset, virtioPciDeviceCfgLength] using hWrite
  have hWrapperAction :
      virtioPciCommonCfgQueueReadyWriteDevice state value = .ok next.device ∧
        action = .none := by
    exact virtioPciWrappedDeviceWrite_ok_inv state
      (virtioPciCommonCfgQueueReadyWriteDevice state value)
      MmioWriteAction.none
      (by
        simpa [virtioPciCommonCfgWrite, virtioPciCommonCfgWriteQueueReady] using hDecoded)
  rcases hWrapperAction with ⟨hWrapper, hAction⟩
  exact ⟨hAction,
    virtioPciCommonCfgQueueReadyWriteDevice_preserves_descriptorValidity state value guestMemorySize
      availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext hActive hWrapper
      hValid⟩

/-- The decoded PCI BAR queue-address write path preserves descriptor validity after transport
decode. -/
theorem virtioPciBarWriteOffset_queueAddr_preserves_descriptorValidity (state : VirtioPciState)
    (field : QueueAddrField) (value : UInt32) (highHalf : Bool) (guestMemorySize : UInt64)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {next : VirtioPciState} {action : MmioWriteAction}
    (hActive : state.device.activeQueue.isSome)
    (hWrite : virtioPciBarWriteOffset state (virtioPciQueueAddrOffset field highHalf) 4 4 value =
      .ok (next, action))
    (hValid : descriptorValidForDevice guestMemorySize state.device availIdx usedIdx head
      descAddrLow descAddrHigh descLen descFlags descNext) :
    action = .none ∧
      descriptorValidForDevice guestMemorySize next.device availIdx usedIdx head descAddrLow
        descAddrHigh descLen descFlags descNext := by
  have hDecoded : virtioPciCommonCfgWrite state (virtioPciQueueAddrOffset field highHalf) 4 value =
      .ok (next, action) := by
    cases field <;> cases highHalf <;>
      simpa [virtioPciBarWriteOffset, virtioPciQueueAddrOffset, virtioPciCommonCfgLength,
        virtioPciNotifyCfgOffset, virtioPciDeviceCfgOffset, virtioPciDeviceCfgLength] using hWrite
  have hWrapperAction :
      virtioPciCommonCfgQueueAddrWriteDevice state field value highHalf = .ok next.device ∧
        action = .none := by
    cases field <;> cases highHalf <;>
      exact virtioPciWrappedDeviceWrite_ok_inv state
        (virtioPciCommonCfgQueueAddrWriteDevice state _ value _)
        MmioWriteAction.none
        (by
          simpa [virtioPciCommonCfgWrite, virtioPciQueueAddrOffset,
            virtioPciCommonCfgWriteQueueAddr] using hDecoded)
  rcases hWrapperAction with ⟨hWrapper, hAction⟩
  exact ⟨hAction,
    virtioPciCommonCfgQueueAddrWriteDevice_preserves_descriptorValidity state field value highHalf
      guestMemorySize availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext
      hActive hWrapper hValid⟩

/-- The decoded PCI notify branch reaches the same real rng executor used by Linux BAR handling:
notification preserves the latched queue, and a successful completion from that state keeps the
same DMA-target view while exposing the executor's concrete write trace. -/
theorem virtioPciBarWriteOffset_notify_then_complete_refines (guestMemory : Kvm.GuestMemory)
    (state : VirtioPciState) (width : UInt32) (usedIdx head : UInt32)
    {afterWrite : VirtioPciState} {next : VirtioDeviceState} {report : VirtioEntropyExecutionReport}
    (hWidth : width = 2 ∨ width = 4)
  (_hActive : state.device.activeQueue.isSome)
    (hLatched : queueConfigLatched state.device)
    (hWrite : virtioPciBarWriteOffset state virtioPciNotifyCfgOffset.toNat width.toNat width 0 =
      .ok (afterWrite, .processQueue))
    (hExec : IOResultRunsTo
      (completeDeterministicEntropyRequestWithReport guestMemory afterWrite.device)
      (next, report)) :
    queueConfigLatched afterWrite.device ∧
      queueConfigLatched next ∧
      deterministicEntropyDmaTargetsOfDevice next usedIdx head =
        deterministicEntropyDmaTargetsOfDevice state.device usedIdx head ∧
      report.writes = virtioEntropyCompletionWrites report.plan ∧
      virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes := by
  have hNotify : markQueueNotified state.device = .ok afterWrite.device := by
    exact virtioPciWrappedProcessQueueWrite_ok_inv state
      (markQueueNotified state.device)
      (by
    rcases hWidth with rfl | rfl <;>
      simpa [virtioPciBarWriteOffset, virtioPciNotifyCfgOffset, virtioPciCommonCfgLength,
        virtioPciDeviceCfgOffset, virtioPciDeviceCfgLength] using hWrite)
  have hAfterPreserve : preservesLiveQueue state.device afterWrite.device :=
    markQueueNotified_preservesLiveQueue state.device hNotify
  have hAfterLatched : queueConfigLatched afterWrite.device :=
    preservesLiveQueue_keeps_queueConfigLatched hAfterPreserve hLatched
  have hAfterTargets : deterministicEntropyDmaTargetsOfDevice afterWrite.device usedIdx head =
      deterministicEntropyDmaTargetsOfDevice state.device usedIdx head :=
    preservesLiveQueue_keeps_deterministicEntropyDmaTargets usedIdx head hAfterPreserve
  rcases completeDeterministicEntropyRequestWithReport_success_refines_executor guestMemory
      afterWrite.device hExec with ⟨hWrites, hWrapperTrace, hNextActive, hNextLatched,
        _hPrng, _hCompleted, _hInterrupt⟩
  have hNextPreserve : preservesLiveQueue afterWrite.device next := ⟨hNextActive, hNextLatched⟩
  have hNextLatchedProp : queueConfigLatched next :=
    preservesLiveQueue_keeps_queueConfigLatched hNextPreserve hAfterLatched
  have hNextTargetsFromAfter : deterministicEntropyDmaTargetsOfDevice next usedIdx head =
      deterministicEntropyDmaTargetsOfDevice afterWrite.device usedIdx head :=
    preservesLiveQueue_keeps_deterministicEntropyDmaTargets usedIdx head hNextPreserve
  exact ⟨hAfterLatched, hNextLatchedProp, hNextTargetsFromAfter.trans hAfterTargets,
    hWrites, hWrapperTrace⟩

end Microvmm
