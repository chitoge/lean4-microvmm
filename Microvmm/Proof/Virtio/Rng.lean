import Init.Omega
import Microvmm.Device.Virtio.Rng
import Microvmm.Proof.Virtio.Core

namespace Microvmm

/-- Proof-facing view of the guest addresses that seeded virtio-rng completion derives from
the currently active queue. Later queue-register rewrites can only retarget DMA if they change
`activeQueue`, so this wrapper is the narrow bridge from the queue-latching proofs to rng-local DMA
address reasoning. -/
def deterministicEntropyDmaTargetsOfDevice (device : VirtioDeviceState)
  (usedIdx head : UInt32) : Option (GuestPhysAddr × GuestPhysAddr × GuestPhysAddr) :=
  device.activeQueue.map fun queue => deterministicEntropyDmaTargets queue usedIdx head

theorem prngNextPayload_advances_requestsServed (state : PrngState) :
    (prngNextPayload state).1.requestsServed = state.requestsServed + 1 := by
  simp [prngNextPayload, prngStep]

theorem prngNextPayload_has_fixed_length (state : PrngState) :
    (prngNextPayload state).2.length = virtioPayloadLength.toNat := by
  simp [prngNextPayload, prngPayloadBytes, virtioPayloadLength]

theorem prngGeneratePayloadChunks_has_expected_length (state : PrngState) (count : Nat) :
    (prngGeneratePayloadChunks state count).2.length = count * virtioPayloadLength.toNat := by
  induction count generalizing state with
  | zero =>
      simp [prngGeneratePayloadChunks]
  | succ count ih =>
      simp [prngGeneratePayloadChunks, ih, prngNextPayload_has_fixed_length, Nat.succ_mul,
        Nat.add_comm]

theorem prngGenerateBytes_has_requested_length (state : PrngState) (length : Nat) :
    (prngGenerateBytes state length).2.length = length := by
  cases hLength : length with
  | zero =>
      simp [prngGenerateBytes]
  | succ count =>
      have hRemainderBound : count % virtioPayloadLength.toNat + 1 ≤ virtioPayloadLength.toNat := by
        have hMod : count % virtioPayloadLength.toNat < virtioPayloadLength.toNat := by
          simpa using Nat.mod_lt count (by simp [virtioPayloadLength])
        exact Nat.succ_le_of_lt hMod
      have hDecomp : count = (count / virtioPayloadLength.toNat) * virtioPayloadLength.toNat + count % virtioPayloadLength.toNat := by
        simpa [Nat.mul_comm] using (Nat.div_add_mod count virtioPayloadLength.toNat).symm
      have hTakeBound : count + 1 ≤ ((count / virtioPayloadLength.toNat) + 1) * virtioPayloadLength.toNat := by
        calc
          count + 1 = ((count / virtioPayloadLength.toNat) * virtioPayloadLength.toNat + count % virtioPayloadLength.toNat) + 1 := by
            exact congrArg (fun n => n + 1) hDecomp
          _ = (count / virtioPayloadLength.toNat) * virtioPayloadLength.toNat + (count % virtioPayloadLength.toNat + 1) := by
            rw [Nat.add_assoc]
          _ ≤ (count / virtioPayloadLength.toNat) * virtioPayloadLength.toNat + virtioPayloadLength.toNat :=
            Nat.add_le_add_left hRemainderBound _
          _ = ((count / virtioPayloadLength.toNat) + 1) * virtioPayloadLength.toNat := by
            calc
              (count / virtioPayloadLength.toNat) * virtioPayloadLength.toNat + virtioPayloadLength.toNat
                  = virtioPayloadLength.toNat * (count / virtioPayloadLength.toNat) + virtioPayloadLength.toNat * 1 := by
                      simp [Nat.mul_comm]
              _ = virtioPayloadLength.toNat * ((count / virtioPayloadLength.toNat) + 1) := by
                      rw [Nat.left_distrib]
              _ = ((count / virtioPayloadLength.toNat) + 1) * virtioPayloadLength.toNat := by
                      rw [Nat.mul_comm]
      simp [prngGenerateBytes, prngGeneratePayloadChunks_has_expected_length,
        Nat.min_eq_left hTakeBound]

/-- A successful deterministic entropy completion plan is fully determined by the validated active
queue, descriptor fields, and explicit PRNG state: it keeps the queue-size-1 contract, uses the
queue-derived DMA targets, publishes exactly one used-ring completion, and writes exactly the
descriptor-requested number of seeded-pseudorandom bytes while advancing the PRNG state. -/
theorem buildDeterministicEntropyCompletionPlan_some_implies_endToEndSafety
    (guestMemorySize : UInt64) (queue : QueueConfig) (prngState : PrngState)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {plan : DeterministicEntropyCompletionPlan}
    (hPlan :
      buildDeterministicEntropyCompletionPlan guestMemorySize queue prngState availIdx usedIdx head
        descAddrLow descAddrHigh descLen descFlags descNext = some plan) :
    queue.num = virtioQueueNumMax ∧
      (plan.availEntryAddr, plan.usedEntryAddr, plan.descEntryAddr) =
        deterministicEntropyDmaTargets queue usedIdx head ∧
      plan.payloadAddr = ⟨combineLowHigh descAddrLow descAddrHigh⟩ ∧
      plan.usedIndexAddr = ⟨queue.usedAddr.value + UInt64.ofNat 2⟩ ∧
      plan.nextUsedIdx = (usedIdx + 1) &&& 0xffff ∧
      plan.completedHead = head ∧
      plan.nextPrngState = (prngGenerateBytes prngState descLen.toNat).1 ∧
      plan.completedLen = descLen ∧
      plan.payload = (prngGenerateBytes prngState descLen.toNat).2 ∧
      plan.payload.length = descLen.toNat := by
  simp [buildDeterministicEntropyCompletionPlan] at hPlan
  rcases hPlan with ⟨hNum, _hQueueDescSpan, _hQueueAvailSpan, _hQueueUsedSpan,
    _hAvailIdx, _hHead, _hNoNextOrIndirect, _hWritable, _hDescNext, _hPayloadSpan, rfl⟩
  refine ⟨hNum, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simpa using prngGenerateBytes_has_requested_length prngState descLen.toNat

/-- Queue activation can only establish shape facts that are independent of guest memory size:
the accepted queue count and the non-zero ring base addresses enforced by `validateQueueDraft`. -/
def queueShapeValid (queue : QueueConfig) : Prop :=
  queue.num = virtioQueueNumMax ∧
  queue.descAddr.value ≠ 0 ∧
  queue.availAddr.value ≠ 0 ∧
  queue.usedAddr.value ≠ 0

/-- Any successful `validateQueueDraft` result satisfies the activation-known queue shape facts. -/
theorem validateQueueDraft_ok_implies_queueShapeValid
    (draft : RawQueueConfig) {queue : QueueConfig}
    (hValidate : validateQueueDraft draft = .ok queue) :
    queueShapeValid queue := by
  unfold validateQueueDraft at hValidate
  split at hValidate
  · simp at hValidate
  · cases hValidate
    rename_i hValid
    simpa [queueShapeValid, and_assoc] using hValid

/-- Successful first activation (`QueueReady := 1` while no queue is active) exposes a concrete
active queue satisfying the same shape predicate proven by `validateQueueDraft`. -/
theorem writeQueueReady_one_establishes_queueShapeValid
    (device : VirtioDeviceState) {next : VirtioDeviceState}
    (hInactive : device.activeQueue.isNone)
    (hWrite : writeQueueReady device 1 = .ok next) :
    ∃ queue, next.activeQueue = some queue ∧ queueShapeValid queue := by
  unfold writeQueueReady at hWrite
  split at hWrite
  · simp at hWrite
  · have hNoSome : device.activeQueue.isSome = false := by
      cases hActive : device.activeQueue <;> simp [hActive] at hInactive ⊢
    simp [hNoSome] at hWrite
    let stagedQueue := { device.stagedQueue with ready := 1 }
    cases hValidate : validateQueueDraft stagedQueue with
    | error err =>
        simp [stagedQueue, hValidate] at hWrite
    | ok activeQueue =>
        simp [stagedQueue, hValidate] at hWrite
        cases hWrite
        exact ⟨activeQueue, rfl,
          validateQueueDraft_ok_implies_queueShapeValid stagedQueue hValidate⟩

/-- Queue geometry is valid for seeded virtio-rng: fixed size, all ring structures in bounds. -/
def queueGeometryInvariants (guestMemorySize : UInt64) (queue : QueueConfig) : Prop :=
  queue.num = virtioQueueNumMax ∧
  guestSpanValidFor guestMemorySize queue.descAddr.value
    (queue.num.toUInt64 * 16) ∧
  guestSpanValidFor guestMemorySize queue.availAddr.value (splitAvailSpan queue.num) ∧
  guestSpanValidFor guestMemorySize queue.usedAddr.value (splitUsedSpan queue.num)

/-- A descriptor is valid for seeded virtio-rng completion when it satisfies all checks: queue
geometry, driver-visible ring progression, descriptor head in bounds, required flags, no chaining,
and payload span. Literal bit masks avoid depending on private runtime defs. -/
def descriptorValidityInvariants (guestMemorySize : UInt64) (queue : QueueConfig)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32) : Prop :=
  queueGeometryInvariants guestMemorySize queue ∧
  (usedIdx + 1) &&& 0xffff = availIdx ∧
  head < queue.num ∧
  (descFlags &&& (0x01 ||| 0x04)) = 0 ∧
  (descFlags &&& 0x02) ≠ 0 ∧
  descNext = 0 ∧
  guestSpanValidFor guestMemorySize (⟨combineLowHigh descAddrLow descAddrHigh⟩ : GuestPhysAddr).value
    descLen.toUInt64

/-- A successful completion plan construction exactly encodes all descriptor validity invariants
for the accepted virtio-rng request shape. -/
theorem buildDeterministicEntropyCompletionPlan_encodes_validity
    (guestMemorySize : UInt64) (queue : QueueConfig) (prngState : PrngState)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {plan : DeterministicEntropyCompletionPlan}
    (hPlan : buildDeterministicEntropyCompletionPlan guestMemorySize queue prngState
      availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext = some plan) :
    descriptorValidityInvariants guestMemorySize queue availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext := by
  simp [buildDeterministicEntropyCompletionPlan] at hPlan
  rcases hPlan with ⟨hNum, hQueueSpans, hDescriptorChecks, _hPlan⟩
  rcases hQueueSpans with ⟨⟨hDescSpan, hAvailSpan⟩, hUsedSpan⟩
  rcases hDescriptorChecks with ⟨hDescriptorChecks, hPayloadSpan⟩
  rcases hDescriptorChecks with ⟨hDescriptorChecks, hDescNext⟩
  rcases hDescriptorChecks with ⟨hDescriptorChecks, hWritable⟩
  rcases hDescriptorChecks with ⟨hAvailHead, hNoChainOrIndirect⟩
  rcases hAvailHead with ⟨hAvailIdx, hHead⟩
  constructor
  · exact ⟨hNum, hDescSpan, hAvailSpan, hUsedSpan⟩
  constructor
  · exact hAvailIdx.symm
  constructor
  · exact hHead
  constructor
  · simpa using hNoChainOrIndirect
  constructor
  · simpa using hWritable
  constructor
  · exact hDescNext
  · exact hPayloadSpan

/-- Proof-facing package for the executor reads on the accepted virtio-rng path: the queue's desc,
avail, and used regions are already validated, and the concrete read offsets used by the executor
fit within those validated regions. -/
def deterministicEntropyExecutorReadRegionsValidated (guestMemorySize : UInt64)
    (queue : QueueConfig) (usedIdx head : UInt32) (plan : DeterministicEntropyCompletionPlan) :
    Prop :=
  queueGeometryInvariants guestMemorySize queue ∧
  plan.availEntryAddr = deterministicEntropyAvailEntryAddr queue usedIdx ∧
  plan.descEntryAddr = deterministicEntropyDescEntryAddr queue head ∧
  2 + 2 ≤ (splitAvailSpan queue.num).toNat ∧
  2 + 2 ≤ (splitUsedSpan queue.num).toNat ∧
  4 + deterministicEntropyRingSlot queue usedIdx * 2 + 2 ≤ (splitAvailSpan queue.num).toNat ∧
  head.toNat * 16 + 16 ≤ queue.num.toNat * 16

/-- Proof-facing package for the completion writes on the accepted virtio-rng path: the queue's
used ring remains validated, the descriptor payload span is validated, and the concrete used-ring
write offsets fit within the validated used region. -/
def deterministicEntropyCompletionWriteRegionsValidated (guestMemorySize : UInt64)
    (queue : QueueConfig) (usedIdx : UInt32) (plan : DeterministicEntropyCompletionPlan) : Prop :=
  queueGeometryInvariants guestMemorySize queue ∧
  guestSpanValidFor guestMemorySize plan.payloadAddr.value plan.completedLen.toUInt64 ∧
  plan.payload.length = plan.completedLen.toNat ∧
  plan.usedEntryAddr = deterministicEntropyUsedEntryAddr queue usedIdx ∧
  plan.usedIndexAddr = ⟨queue.usedAddr.value + UInt64.ofNat 2⟩ ∧
  4 + deterministicEntropyRingSlot queue usedIdx * 8 + 8 ≤ (splitUsedSpan queue.num).toNat ∧
  2 + 2 ≤ (splitUsedSpan queue.num).toNat

/-- A successful completion-plan construction packages the executor's concrete read addresses as
fixed offsets inside the already-validated avail, used, and descriptor regions for the accepted
queue shape. -/
theorem buildDeterministicEntropyCompletionPlan_some_implies_executorReadRegionsValidated
    (guestMemorySize : UInt64) (queue : QueueConfig) (prngState : PrngState)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {plan : DeterministicEntropyCompletionPlan}
    (hPlan : buildDeterministicEntropyCompletionPlan guestMemorySize queue prngState availIdx
      usedIdx head descAddrLow descAddrHigh descLen descFlags descNext = some plan) :
    deterministicEntropyExecutorReadRegionsValidated guestMemorySize queue usedIdx head plan := by
  have hValid := buildDeterministicEntropyCompletionPlan_encodes_validity guestMemorySize queue
    prngState availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext hPlan
  rcases hValid with ⟨hGeometry, _hAvailIdx, hHead, _hNoChainOrIndirect, _hWritable,
    _hDescNext, _hPayloadSpan⟩
  rcases buildDeterministicEntropyCompletionPlan_some_implies_endToEndSafety guestMemorySize queue
      prngState availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext hPlan with
    ⟨hNum, hTargets, _hPayloadAddr, _hUsedIndexAddr, _hNextUsedIdx, _hCompletedHead,
      _hNextPrng, _hCompletedLen, _hPayload, _hPayloadLen⟩
  have hAvailEntry : plan.availEntryAddr = deterministicEntropyAvailEntryAddr queue usedIdx := by
    exact congrArg Prod.fst hTargets
  have hDescEntry : plan.descEntryAddr = deterministicEntropyDescEntryAddr queue head := by
    exact congrArg Prod.snd (congrArg Prod.snd hTargets)
  have hHeadZeroWord : head = 0 := by
    simpa [hNum, virtioQueueNumMax] using hHead
  have hHeadZero : head.toNat = 0 := by
    simp [hHeadZeroWord]
  refine ⟨hGeometry, hAvailEntry, hDescEntry, ?_, ?_, ?_, ?_⟩
  · simp [splitAvailSpan, hNum, virtioQueueNumMax]
  · simp [splitUsedSpan, hNum, virtioQueueNumMax]
  · simp [deterministicEntropyRingSlot, splitAvailSpan, hNum, virtioQueueNumMax, Nat.mod_one]
  · simp [hNum, virtioQueueNumMax, hHeadZero]

/-- A successful completion-plan construction likewise packages the real completion writes as
validated payload and used-ring regions plus concrete write offsets that stay inside the validated
used ring. -/
theorem buildDeterministicEntropyCompletionPlan_some_implies_completionWriteRegionsValidated
    (guestMemorySize : UInt64) (queue : QueueConfig) (prngState : PrngState)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {plan : DeterministicEntropyCompletionPlan}
    (hPlan : buildDeterministicEntropyCompletionPlan guestMemorySize queue prngState availIdx
      usedIdx head descAddrLow descAddrHigh descLen descFlags descNext = some plan) :
    deterministicEntropyCompletionWriteRegionsValidated guestMemorySize queue usedIdx plan := by
  have hValid := buildDeterministicEntropyCompletionPlan_encodes_validity guestMemorySize queue
    prngState availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext hPlan
  rcases hValid with ⟨hGeometry, _hAvailIdx, _hHead, _hNoChainOrIndirect, _hWritable,
    _hDescNext, hPayloadSpan⟩
  rcases buildDeterministicEntropyCompletionPlan_some_implies_endToEndSafety guestMemorySize queue
      prngState availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext hPlan with
    ⟨hNum, hTargets, hPayloadAddr, hUsedIndexAddr, _hNextUsedIdx, _hCompletedHead,
      _hNextPrng, hCompletedLen, _hPayload, hPayloadLen⟩
  have hUsedEntry : plan.usedEntryAddr = deterministicEntropyUsedEntryAddr queue usedIdx := by
    exact congrArg Prod.fst (congrArg Prod.snd hTargets)
  have hPayloadSpanPlan :
      guestSpanValidFor guestMemorySize plan.payloadAddr.value plan.completedLen.toUInt64 := by
    simpa [hPayloadAddr, hCompletedLen] using hPayloadSpan
  refine ⟨hGeometry, hPayloadSpanPlan, ?_, hUsedEntry, hUsedIndexAddr, ?_, ?_⟩
  · simpa [hCompletedLen] using hPayloadLen
  · simp [deterministicEntropyRingSlot, splitUsedSpan, hNum, virtioQueueNumMax, Nat.mod_one]
  · simp [splitUsedSpan, hNum, virtioQueueNumMax]

/-- For the accepted virtio-rng request shape, successful completion-plan construction packages
all executor reads and completion writes as concrete offsets inside regions that were already
validated during plan construction. This is the proof-facing theorem behind the claim that device
memory accesses stay within validated guest regions up to the raw C/Lean boundary. -/
theorem buildDeterministicEntropyCompletionPlan_some_implies_memoryAccessesStayWithinValidatedRegions
    (guestMemorySize : UInt64) (queue : QueueConfig) (prngState : PrngState)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    {plan : DeterministicEntropyCompletionPlan}
    (hPlan : buildDeterministicEntropyCompletionPlan guestMemorySize queue prngState availIdx
      usedIdx head descAddrLow descAddrHigh descLen descFlags descNext = some plan) :
    deterministicEntropyExecutorReadRegionsValidated guestMemorySize queue usedIdx head plan ∧
      deterministicEntropyCompletionWriteRegionsValidated guestMemorySize queue usedIdx plan := by
  exact ⟨
    buildDeterministicEntropyCompletionPlan_some_implies_executorReadRegionsValidated
      guestMemorySize queue prngState availIdx usedIdx head descAddrLow descAddrHigh descLen
      descFlags descNext hPlan,
    buildDeterministicEntropyCompletionPlan_some_implies_completionWriteRegionsValidated
      guestMemorySize queue prngState availIdx usedIdx head descAddrLow descAddrHigh descLen
      descFlags descNext hPlan
  ⟩

/-- A descriptor identified by its observed fields is valid for device execution if the device has
an active queue and the packaged descriptor validity invariants hold for that queue. -/
def descriptorValidForDevice (guestMemorySize : UInt64) (device : VirtioDeviceState)
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32) : Prop :=
  ∃ queue, device.activeQueue = some queue ∧
    descriptorValidityInvariants guestMemorySize queue availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext

/-- Post-activation queue-register writes cannot reclassify the same observed descriptor request:
if the live queue is preserved, the descriptor-validity judgment is equivalent before and after. -/
theorem descriptorValidForDevice_iff_preserved_queue
    (guestMemorySize : UInt64) {before after : VirtioDeviceState}
    (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags descNext : UInt32)
    (hPreserve : preservesLiveQueue before after) :
    descriptorValidForDevice guestMemorySize before availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext ↔
    descriptorValidForDevice guestMemorySize after availIdx usedIdx head descAddrLow
      descAddrHigh descLen descFlags descNext := by
  rcases hPreserve with ⟨hActive, _hLatched⟩
  constructor
  · intro ⟨queue, hQueueBefore, hValidBefore⟩
    refine ⟨queue, ?_, hValidBefore⟩
    calc
      after.activeQueue = before.activeQueue := hActive
      _ = some queue := hQueueBefore
  · intro ⟨queue, hQueueAfter, hValidAfter⟩
    refine ⟨queue, ?_, hValidAfter⟩
    calc
      before.activeQueue = after.activeQueue := hActive.symm
      _ = some queue := hQueueAfter

/-- Any queue-register write that preserves the live queue also preserves the guest addresses used
by seeded virtio-rng completion for the same visible ring slot and descriptor head. -/
theorem preservesLiveQueue_keeps_deterministicEntropyDmaTargets
  {before after : VirtioDeviceState} (usedIdx head : UInt32)
    (hPreserve : preservesLiveQueue before after) :
    deterministicEntropyDmaTargetsOfDevice after usedIdx head =
      deterministicEntropyDmaTargetsOfDevice before usedIdx head := by
  rcases hPreserve with ⟨hActive, _hLatched⟩
  simp [deterministicEntropyDmaTargetsOfDevice, hActive]

/-- Post-activation queue-size rewrites cannot retarget seeded virtio-rng DMA because they
leave the active queue unchanged. -/
theorem writeQueueNum_keeps_deterministicEntropyDmaTargets_whenActive
  (device : VirtioDeviceState) (value : UInt32) (usedIdx head : UInt32)
    {next : VirtioDeviceState} (hActive : device.activeQueue.isSome)
    (hWrite : writeQueueNum device value = .ok next) :
    deterministicEntropyDmaTargetsOfDevice next usedIdx head =
      deterministicEntropyDmaTargetsOfDevice device usedIdx head := by
  exact preservesLiveQueue_keeps_deterministicEntropyDmaTargets usedIdx head
    (writeQueueNum_preservesLiveQueue_whenActive device value hActive hWrite)

/-- Post-activation queue-ready rewrites are likewise unable to retarget seeded
virtio-rng completion because they stay in diagnostic shadow state. -/
theorem writeQueueReady_keeps_deterministicEntropyDmaTargets_whenActive
  (device : VirtioDeviceState) (value : UInt32) (usedIdx head : UInt32)
    {next : VirtioDeviceState} (hActive : device.activeQueue.isSome)
    (hWrite : writeQueueReady device value = .ok next) :
    deterministicEntropyDmaTargetsOfDevice next usedIdx head =
      deterministicEntropyDmaTargetsOfDevice device usedIdx head := by
  exact preservesLiveQueue_keeps_deterministicEntropyDmaTargets usedIdx head
    (writeQueueReady_preservesLiveQueue_whenActive device value hActive hWrite)

/-- Post-activation queue-address rewrites cannot retarget seeded virtio-rng DMA either,
because the completion path computes its avail, used, and descriptor addresses from the latched
active queue rather than the attempted rewrite shadow. -/
theorem writeQueueAddr_keeps_deterministicEntropyDmaTargets_whenActive
    (device : VirtioDeviceState) (field : QueueAddrField) (value : UInt32) (highHalf : Bool)
  (usedIdx head : UInt32) {next : VirtioDeviceState} (hActive : device.activeQueue.isSome)
    (hWrite : writeQueueAddr device field value highHalf = .ok next) :
    deterministicEntropyDmaTargetsOfDevice next usedIdx head =
      deterministicEntropyDmaTargetsOfDevice device usedIdx head := by
  exact preservesLiveQueue_keeps_deterministicEntropyDmaTargets usedIdx head
    (writeQueueAddr_preservesLiveQueue_whenActive device field value highHalf hActive hWrite)

end Microvmm
