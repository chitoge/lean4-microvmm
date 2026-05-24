import Microvmm.Proof.Kvm.Resource
import Microvmm.Proof.Kvm.RawBoundary
import Microvmm.Proof.Host.ConsoleRuntime
import Microvmm.Proof.Linux.BootPlan
import Microvmm.Proof.Linux.Console
import Microvmm.Proof.Linux.Platform
import Microvmm.Proof.Linux.Runtime
import Microvmm.Proof.Serial.Replay
import Microvmm.Proof.Virtio.Core
import Microvmm.Proof.Virtio.Cve2026_5747
import Microvmm.Proof.Virtio.Mmio
import Microvmm.Proof.Virtio.Pci
import Microvmm.Proof.Virtio.Rng
import Microvmm.Proof.Virtio.RngExecution

namespace Microvmm

open Kvm

/-- Formal version of the first row in `docs/virtio.md`: the current proof surface only covers
the accepted virtio-rng request shape, where queue size is fixed to 1 and the observed descriptor
chain is forced to length 1 by rejecting `NEXT`, `INDIRECT`, and non-zero `descNext`. -/
theorem virtioQueueStructuralSafety_forAcceptedRngRequest
    (guestMemorySize : UInt64) (queue : QueueConfig) (prngState : PrngState)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {plan : DeterministicEntropyCompletionPlan}
    (hPlan : buildDeterministicEntropyCompletionPlan guestMemorySize queue prngState availIdx
      usedIdx head descAddrLow descAddrHigh descLen descFlags descNext = some plan) :
    queue.num = virtioQueueNumMax ∧
      head = 0 ∧
      descNext = 0 ∧
      (descFlags &&& ((0x01 : UInt32) ||| 0x04)) = 0 := by
  have hValid := buildDeterministicEntropyCompletionPlan_encodes_validity guestMemorySize queue
    prngState availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext hPlan
  rcases hValid with
    ⟨⟨hNum, _hDescSpan, _hAvailSpan, _hUsedSpan⟩, _hAvailIdx, hHead,
      hNoNextOrIndirect, _hWritable, hDescNext, _hPayloadSpan⟩
  have hHeadZero : head = 0 := by
    simpa [hNum, virtioQueueNumMax] using hHead
  exact ⟨hNum, hHeadZero, hDescNext, by simpa using hNoNextOrIndirect⟩

/-- Formal version of the second row's activation-side fact: once `QueueReady := 1` succeeds on
an inactive device, the active queue satisfies the accepted queue-shape predicate used by the
current virtio-rng model. -/
theorem virtioQueueActivationEstablishesAcceptedShape (device : VirtioDeviceState)
    {next : VirtioDeviceState} (hInactive : device.activeQueue.isNone)
    (hWrite : writeQueueReady device 1 = .ok next) :
    ∃ queue, next.activeQueue = some queue ∧ queueShapeValid queue := by
  exact writeQueueReady_one_establishes_queueShapeValid device hInactive hWrite

/-- Formal version of the second row's accepted-request fact: any successful accepted virtio-rng
request satisfies the packaged queue-geometry, index, flag, and payload-span invariants. -/
theorem virtioAcceptedRngRequestSatisfiesDescriptorValidityInvariants
    (guestMemorySize : UInt64) (queue : QueueConfig) (prngState : PrngState)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {plan : DeterministicEntropyCompletionPlan}
    (hPlan : buildDeterministicEntropyCompletionPlan guestMemorySize queue prngState availIdx
      usedIdx head descAddrLow descAddrHigh descLen descFlags descNext = some plan) :
    descriptorValidityInvariants guestMemorySize queue availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext := by
  exact buildDeterministicEntropyCompletionPlan_encodes_validity guestMemorySize queue prngState
    availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext hPlan

/-- Formal version of the second row's transition claim at the shared virtio core: any transition
that preserves the live queue preserves the `descriptorValidForDevice` judgment for the same
observed descriptor fields. -/
theorem virtioPreservedQueueTransitionPreservesDescriptorValidity
    (guestMemorySize : UInt64) {before after : VirtioDeviceState}
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    (hPreserve : preservesLiveQueue before after) :
    descriptorValidForDevice guestMemorySize before availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext ↔
    descriptorValidForDevice guestMemorySize after availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext := by
  exact descriptorValidForDevice_iff_preserved_queue guestMemorySize availIdx usedIdx head
    descAddrLow descAddrHigh descLen descFlags descNext hPreserve

/-- Formal version of the second row's Linux-platform lift: once the routed BAR `processQueue`
branch succeeds, the same descriptor-validity judgment carries from the post-write transport state
into the resulting Linux platform state. -/
theorem linuxPlatformProcessQueuePreservesDescriptorValidity
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
  exact handleLinuxMmioAccess_virtioPciBar_processQueue_preserves_descriptorValidity
    guestMemorySize vm runArea guestMemory state access availIdx usedIdx head descAddrLow
    descAddrHigh descLen descFlags descNext hRoute hWriteDir hWrite hHandle hValid

/-- Formal version of the second row's Linux serial-runtime lift. -/
theorem linuxSerialProcessQueueStepPreservesDescriptorValidity
    (guestMemorySize : UInt64) (_remaining : Nat) (vm : Kvm.Vm) (vcpu : Kvm.Vcpu)
    (runArea : Kvm.RunArea) (guestMemory : Kvm.GuestMemory) (state : LinuxPlatformState)
    (access : MmioAccess)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {afterWrite : VirtioPciState} {nextState : LinuxPlatformState}
    {world0 world1 world2 world3 : Void IO.RealWorld}
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
  exact runLinuxSerialLoop_mmio_processQueue_step_preserves_descriptorValidity guestMemorySize
    _remaining vm vcpu runArea guestMemory state access availIdx usedIdx head descAddrLow
    descAddrHigh descLen descFlags descNext _hRun _hExitReason _hRead hRoute hWriteDir hWrite
    hHandle hValid

/-- Formal version of the second row's Linux interactive-runtime lift. -/
theorem linuxInteractiveProcessQueueStepPreservesDescriptorValidity
    (guestMemorySize : UInt64) (_remaining : Nat) (vm : Kvm.Vm) (vcpu : Kvm.Vcpu)
    (runArea : Kvm.RunArea) (guestMemory : Kvm.GuestMemory)
    (state queuedState : InteractiveRunState) (access : MmioAccess)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {afterWrite : VirtioPciState} {nextPlatform : LinuxPlatformState}
    {world0 world1 world2 world3 world4 : Void IO.RealWorld}
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
  exact runLinuxInteractiveLoop_mmio_processQueue_step_preserves_descriptorValidity
    guestMemorySize _remaining vm vcpu runArea guestMemory state queuedState access availIdx
    usedIdx head descAddrLow descAddrHigh descLen descFlags descNext _hService _hRun
    _hExitReason _hRead hRoute hWriteDir hWrite hHandle hValid

/- There is intentionally no top-level theorem here for the third row in `docs/virtio.md`.
The current model does not encode descriptor ownership as a linear capability discipline. -/

/-- Formal version of the fourth row for `queue_size`: once the queue is active, this register
write cannot change the live queue used for execution. -/
theorem virtioQueueConfigurationImmutableAfterActivation_queueNum
    (device : VirtioDeviceState) (value : UInt32) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hWrite : writeQueueNum device value = .ok next) :
    preservesLiveQueue device next := by
  exact writeQueueNum_preservesLiveQueue_whenActive device value hActive hWrite

/-- Formal version of the fourth row for `queue_ready`. -/
theorem virtioQueueConfigurationImmutableAfterActivation_queueReady
    (device : VirtioDeviceState) (value : UInt32) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hWrite : writeQueueReady device value = .ok next) :
    preservesLiveQueue device next := by
  exact writeQueueReady_preservesLiveQueue_whenActive device value hActive hWrite

/-- Formal version of the fourth row for queue-address registers. -/
theorem virtioQueueConfigurationImmutableAfterActivation_queueAddress
    (device : VirtioDeviceState) (field : QueueAddrField) (value : UInt32)
    (highHalf : Bool) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hWrite : writeQueueAddr device field value highHalf = .ok next) :
    preservesLiveQueue device next := by
  exact writeQueueAddr_preservesLiveQueue_whenActive device field value highHalf hActive hWrite

/-- CVE-focused corollary of the fourth row for `queue_size`: the latched execution queue stays
unchanged after a post-activation rewrite attempt. -/
theorem virtioQueueConfigurationLatchedAfterActivation_queueNum
    (device : VirtioDeviceState) (value : UInt32) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : writeQueueNum device value = .ok next) :
    queueConfigLatched next := by
  exact cve_2026_5747_queueNum_postActivation_safe device value hActive hLatched hWrite

/-- CVE-focused corollary of the fourth row for `queue_ready`. -/
theorem virtioQueueConfigurationLatchedAfterActivation_queueReady
    (device : VirtioDeviceState) (value : UInt32) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : writeQueueReady device value = .ok next) :
    queueConfigLatched next := by
  exact cve_2026_5747_queueReady_postActivation_safe device value hActive hLatched hWrite

/-- CVE-focused corollary of the fourth row for queue-address registers. -/
theorem virtioQueueConfigurationLatchedAfterActivation_queueAddress
    (device : VirtioDeviceState) (field : QueueAddrField) (value : UInt32)
    (highHalf : Bool) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : writeQueueAddr device field value highHalf = .ok next) :
    queueConfigLatched next := by
  exact cve_2026_5747_queueAddr_postActivation_safe device field value highHalf
    hActive hLatched hWrite

/- There is intentionally no top-level theorem here for the fifth row in `docs/virtio.md`.
The implementation enforces a narrow lifecycle discipline, but that lifecycle graph is not yet
formalized as a proved reachability theorem. -/

/- There is intentionally no top-level liveness theorem here for the sixth row in `docs/virtio.md`.
The strongest current execution-facing statements are the one-step successful-branch refinements
below, which stop at explicit MMIO-exit witnesses, recovered executor reports, and the named raw
boundary. -/

/-- Current weaker statement standing in place of the unproved liveness row for the Linux platform
MMIO shell: the routed BAR `processQueue` branch reaches the real executor path and recovers its
trace. -/
theorem linuxPlatformProcessQueueRefines (vm : Kvm.Vm) (runArea : Kvm.RunArea)
    (guestMemory : Kvm.GuestMemory) (state : LinuxPlatformState) (access : MmioAccess)
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
  exact handleLinuxMmioAccess_virtioPciBar_processQueue_refines vm runArea guestMemory state
    access hRoute hWriteDir hWrite hHandle

/-- Current weaker statement standing in place of the unproved liveness row for the Linux serial
run loop. -/
theorem linuxSerialProcessQueueStepRefinesUpToRawBoundary (_remaining : Nat) (vm : Kvm.Vm)
    (vcpu : Kvm.Vcpu) (runArea : Kvm.RunArea) (guestMemory : Kvm.GuestMemory)
    (state : LinuxPlatformState) (access : MmioAccess)
    {afterWrite : VirtioPciState} {nextState : LinuxPlatformState}
    {world0 world1 world2 world3 : Void IO.RealWorld}
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
  exact runLinuxSerialLoop_mmio_processQueue_step_refines_upToRawBoundary _remaining vm vcpu
    runArea guestMemory state access _hRun _hExitReason hRead hRoute hWriteDir hWrite hHandle

/-- Current weaker statement standing in place of the unproved liveness row for the Linux
interactive run loop. -/
theorem linuxInteractiveProcessQueueStepRefinesUpToRawBoundary (_remaining : Nat)
    (vm : Kvm.Vm) (vcpu : Kvm.Vcpu) (runArea : Kvm.RunArea)
    (guestMemory : Kvm.GuestMemory) (state queuedState : InteractiveRunState)
    (access : MmioAccess) {afterWrite : VirtioPciState} {nextPlatform : LinuxPlatformState}
    {world0 world1 world2 world3 world4 : Void IO.RealWorld}
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
  exact runLinuxInteractiveLoop_mmio_processQueue_step_refines_upToRawBoundary _remaining vm
    vcpu runArea guestMemory state queuedState access _hService _hRun _hExitReason hRead hRoute
    hWriteDir hWrite hHandle

/-- Formal version of the seventh row in `docs/virtio.md`: a successful accepted virtio-rng
completion plan writes exactly the requested payload length. -/
theorem virtioRngAcceptedRequestWritesExactlyRequestedBufferLength
    (guestMemorySize : UInt64) (queue : QueueConfig) (prngState : PrngState)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {plan : DeterministicEntropyCompletionPlan}
    (hPlan : buildDeterministicEntropyCompletionPlan guestMemorySize queue prngState availIdx
      usedIdx head descAddrLow descAddrHigh descLen descFlags descNext = some plan) :
    plan.completedLen = descLen ∧ plan.payload.length = descLen.toNat := by
  rcases buildDeterministicEntropyCompletionPlan_some_implies_endToEndSafety guestMemorySize queue
      prngState availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext hPlan with
    ⟨_hNum, _hTargets, _hPayloadAddr, _hUsedIndexAddr, _hNextUsedIdx, _hCompletedHead,
      _hNextPrngState, hCompletedLen, _hPayload, hPayloadLen⟩
  exact ⟨hCompletedLen, hPayloadLen⟩

/-- Executor-side companion to the seventh row: the live executor reports exactly the pure
completion plan and write trace it executed. -/
theorem virtioRngExecutorReportsPureCompletionTrace (guestMemory : Kvm.GuestMemory)
    (device : VirtioDeviceState) (plan : DeterministicEntropyCompletionPlan)
    {next : VirtioDeviceState} {report : VirtioEntropyExecutionReport}
    (hExec : IOResultRunsTo (realizeDeterministicEntropyCompletionPlan guestMemory device plan)
      (next, report)) :
    report.plan = plan ∧
      report.writes = virtioEntropyCompletionWrites plan ∧
      virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes ∧
      next.activeQueue = device.activeQueue ∧
      next.latchedQueue = device.latchedQueue ∧
      next.prngState = plan.nextPrngState ∧
      next.requestCompleted = true ∧
      next.interruptStatus = 1 := by
  exact realizeDeterministicEntropyCompletionPlan_success_reports_trace guestMemory device plan hExec

/-- Public-entry companion to the seventh row: the exported completion function refines to the
same plan-derived trace on success. -/
theorem virtioRngPublicCompletionRefinesPureCompletionTrace (guestMemory : Kvm.GuestMemory)
    (device : VirtioDeviceState) {next : VirtioDeviceState}
    {report : VirtioEntropyExecutionReport}
    (hExec : IOResultRunsTo (completeDeterministicEntropyRequestWithReport guestMemory device)
      (next, report)) :
    report.writes = virtioEntropyCompletionWrites report.plan ∧
      virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes ∧
      next.activeQueue = device.activeQueue ∧
      next.latchedQueue = device.latchedQueue ∧
      next.prngState = report.plan.nextPrngState ∧
      next.requestCompleted = true ∧
      next.interruptStatus = 1 := by
  exact completeDeterministicEntropyRequestWithReport_success_refines_executor guestMemory device hExec

/-- Formal version of the eighth row in `docs/virtio.md`: the accepted virtio-rng path packages
both executor reads and completion writes as offsets inside regions validated before execution. -/
theorem virtioRngAcceptedRequestAccessesStayWithinValidatedRegions
    (guestMemorySize : UInt64) (queue : QueueConfig) (prngState : PrngState)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {plan : DeterministicEntropyCompletionPlan}
    (hPlan : buildDeterministicEntropyCompletionPlan guestMemorySize queue prngState availIdx
      usedIdx head descAddrLow descAddrHigh descLen descFlags descNext = some plan) :
    deterministicEntropyExecutorReadRegionsValidated guestMemorySize queue usedIdx head plan ∧
      deterministicEntropyCompletionWriteRegionsValidated guestMemorySize queue usedIdx plan := by
  exact buildDeterministicEntropyCompletionPlan_some_implies_memoryAccessesStayWithinValidatedRegions
    guestMemorySize queue prngState availIdx usedIdx head descAddrLow descAddrHigh descLen
    descFlags descNext hPlan

end Microvmm
