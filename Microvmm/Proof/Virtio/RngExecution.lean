import Microvmm.Device.Virtio.Rng
import Microvmm.Proof.Kvm.Resource
import Microvmm.Proof.Virtio.Rng

namespace Microvmm

open Kvm

def IOResultRunsTo {α : Type} (action : IO (Result α)) (value : α) : Prop :=
  ∃ world nextWorld,
  action world = EST.Out.ok (Outcome.ok value) nextWorld

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

def virtioEntropyWriteRealizedByWrapper (guestMemory : GuestMemory)
  (write : VirtioEntropyWrite) : Prop :=
  executeVirtioEntropyWrite guestMemory write =
  match write.width with
  | .u8 =>
    guestWriteU8 .verifyMmioExit guestMemory write.addr.value write.value
  | .u16 =>
    guestWriteU16 .verifyMmioExit guestMemory write.addr.value write.value
  | .u32 =>
    guestWriteU32 .verifyMmioExit guestMemory write.addr.value write.value

def virtioEntropyWriteTraceRealizedByWrappers (guestMemory : GuestMemory) :
  List VirtioEntropyWrite → Prop
  | [] => True
  | write :: remaining =>
    virtioEntropyWriteRealizedByWrapper guestMemory write ∧
    virtioEntropyWriteTraceRealizedByWrappers guestMemory remaining

theorem executeVirtioEntropyWrite_realizes_wrapper
    (guestMemory : GuestMemory) (write : VirtioEntropyWrite) :
    virtioEntropyWriteRealizedByWrapper guestMemory write := by
  unfold virtioEntropyWriteRealizedByWrapper executeVirtioEntropyWrite
  cases write.width <;> simp

theorem executeVirtioEntropyWriteTrace_realizes_wrappers
    (guestMemory : GuestMemory) (writes : List VirtioEntropyWrite) :
    virtioEntropyWriteTraceRealizedByWrappers guestMemory writes := by
  induction writes with
  | nil =>
      simp [virtioEntropyWriteTraceRealizedByWrappers]
  | cons write remaining ih =>
      exact ⟨executeVirtioEntropyWrite_realizes_wrapper guestMemory write, ih⟩

/-- Executing a validated completion plan reports exactly the pure write trace derived from that
plan and only updates the completion-facing device flags. This is the proof hook that ties the
virtio-rng execution theorem surface to the real VM executor path. -/
theorem realizeDeterministicEntropyCompletionPlan_success_reports_trace
    (guestMemory : GuestMemory) (device : VirtioDeviceState)
    (plan : DeterministicEntropyCompletionPlan) {next : VirtioDeviceState}
    {report : VirtioEntropyExecutionReport}
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
  rcases hExec with ⟨world, nextWorld, hExec⟩
  unfold realizeDeterministicEntropyCompletionPlan at hExec
  rw [bindIOResult_apply] at hExec
  cases hWrites :
      executeVirtioEntropyWriteTrace guestMemory (virtioEntropyCompletionWrites plan) world with
  | error err world' =>
      simp [hWrites] at hExec
  | ok result world' =>
      cases result with
      | error err =>
          simp [hWrites] at hExec
      | ok value =>
          cases value
          have hExec' := hExec
          simp [hWrites] at hExec'
          have hRealized :
            virtioEntropyWriteTraceRealizedByWrappers guestMemory
            (virtioEntropyCompletionWrites plan) :=
          executeVirtioEntropyWriteTrace_realizes_wrappers guestMemory
            (virtioEntropyCompletionWrites plan)
          cases hExec'
          simp [hRealized]

/-- The public virtio-rng executor is now just the report-producing executor with the trace erased.
This keeps the live VM path aligned with the proof-facing execution surface. -/
theorem completeDeterministicEntropyRequest_defeq_withReport
    (guestMemory : GuestMemory) (device : VirtioDeviceState) :
    completeDeterministicEntropyRequest guestMemory device =
      mapIOResult (completeDeterministicEntropyRequestWithReport guestMemory device) Prod.fst := by
  rfl

/-- A successful virtio-rng completion goes through the real executor, so it preserves the live
and latched queue while returning the same plan-derived write trace that `realize...` exposes. -/
theorem completeDeterministicEntropyRequestWithReport_success_refines_executor
    (guestMemory : GuestMemory) (device : VirtioDeviceState)
    {next : VirtioDeviceState} {report : VirtioEntropyExecutionReport}
    (hExec : IOResultRunsTo (completeDeterministicEntropyRequestWithReport guestMemory device)
      (next, report)) :
    report.writes = virtioEntropyCompletionWrites report.plan ∧
      virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes ∧
      next.activeQueue = device.activeQueue ∧
      next.latchedQueue = device.latchedQueue ∧
      next.prngState = report.plan.nextPrngState ∧
      next.requestCompleted = true ∧
      next.interruptStatus = 1 := by
  rcases hExec with ⟨world0, worldFinal, hExec⟩
  unfold completeDeterministicEntropyRequestWithReport at hExec
  cases hActive : device.activeQueue with
  | none =>
      simp [hActive] at hExec
      cases hExec
  | some activeQueue =>
      by_cases hNum : (activeQueue.num != virtioQueueNumMax) = true
      · simp [hActive, hNum] at hExec
        cases hExec
      · have hNumFalse : (activeQueue.num != virtioQueueNumMax) = false := by
          cases hCheck : activeQueue.num != virtioQueueNumMax with
          | false =>
            rfl
          | true =>
              exact False.elim (hNum hCheck)
        by_cases hSpans :
            ((guestSpanValidFor guestMemory.size activeQueue.descAddr.value
                (activeQueue.num.toUInt64 * 16) = false ∨
              guestSpanValidFor guestMemory.size activeQueue.availAddr.value
                (splitAvailSpan activeQueue.num) = false) ∨
              guestSpanValidFor guestMemory.size activeQueue.usedAddr.value
                (splitUsedSpan activeQueue.num) = false)
        · simp [hActive, hNumFalse, hSpans] at hExec
          cases hExec
        · simp [hActive, hNumFalse, hSpans] at hExec
          rw [ioBind_apply] at hExec
          cases hAvailIdxRead :
              guestReadU16 Stage.verifyMmioExit guestMemory (activeQueue.availAddr + 2) world0 with
          | error ioErr world1 =>
              simp [hAvailIdxRead] at hExec
          | ok availIdxResult world1 =>
              cases availIdxResult with
              | error err =>
                  simp [hAvailIdxRead] at hExec
                  cases hExec
              | ok availIdx =>
                  simp [hAvailIdxRead] at hExec
                  rw [ioBind_apply] at hExec
                  cases hUsedIdxRead :
                      guestReadU16 Stage.verifyMmioExit guestMemory (activeQueue.usedAddr + 2) world1 with
                  | error ioErr world2 =>
                      simp [hUsedIdxRead] at hExec
                  | ok usedIdxResult world2 =>
                      cases usedIdxResult with
                      | error err =>
                          simp [hUsedIdxRead] at hExec
                          cases hExec
                      | ok usedIdx =>
                          simp [hUsedIdxRead] at hExec
                          rw [ioBind_apply] at hExec
                          cases hHeadRead :
                            guestReadU16 Stage.verifyMmioExit guestMemory
                            (deterministicEntropyAvailEntryAddr activeQueue usedIdx).value world2 with
                          | error ioErr world3 =>
                            simp [hHeadRead] at hExec
                          | ok headResult world3 =>
                            cases headResult with
                            | error err =>
                              simp [hHeadRead] at hExec
                              cases hExec
                            | ok head =>
                              simp [hHeadRead] at hExec
                              rw [ioBind_apply] at hExec
                              cases hDescAddrLowRead :
                                guestReadU32 Stage.verifyMmioExit guestMemory
                                (deterministicEntropyDescEntryAddr activeQueue head).value world3 with
                              | error ioErr world4 =>
                                simp [hDescAddrLowRead] at hExec
                              | ok descAddrLowResult world4 =>
                                cases descAddrLowResult with
                                | error err =>
                                  simp [hDescAddrLowRead] at hExec
                                  cases hExec
                                | ok descAddrLow =>
                                  simp [hDescAddrLowRead] at hExec
                                  rw [ioBind_apply] at hExec
                                  cases hDescAddrHighRead :
                                    guestReadU32 Stage.verifyMmioExit guestMemory
                                    ((deterministicEntropyDescEntryAddr activeQueue head).value + 4) world4 with
                                  | error ioErr world5 =>
                                    simp [hDescAddrHighRead] at hExec
                                  | ok descAddrHighResult world5 =>
                                    cases descAddrHighResult with
                                    | error err =>
                                      simp [hDescAddrHighRead] at hExec
                                      cases hExec
                                    | ok descAddrHigh =>
                                      simp [hDescAddrHighRead] at hExec
                                      rw [ioBind_apply] at hExec
                                      cases hDescLenRead :
                                        guestReadU32 Stage.verifyMmioExit guestMemory
                                        ((deterministicEntropyDescEntryAddr activeQueue head).value + 8) world5 with
                                      | error ioErr world6 =>
                                        simp [hDescLenRead] at hExec
                                      | ok descLenResult world6 =>
                                        cases descLenResult with
                                        | error err =>
                                          simp [hDescLenRead] at hExec
                                          cases hExec
                                        | ok descLen =>
                                          simp [hDescLenRead] at hExec
                                          rw [ioBind_apply] at hExec
                                          cases hDescFlagsRead :
                                            guestReadU16 Stage.verifyMmioExit guestMemory
                                            ((deterministicEntropyDescEntryAddr activeQueue head).value + 12) world6 with
                                          | error ioErr world7 =>
                                            simp [hDescFlagsRead] at hExec
                                          | ok descFlagsResult world7 =>
                                            cases descFlagsResult with
                                            | error err =>
                                              simp [hDescFlagsRead] at hExec
                                              cases hExec
                                            | ok descFlags =>
                                              simp [hDescFlagsRead] at hExec
                                              rw [ioBind_apply] at hExec
                                              cases hDescNextRead :
                                                guestReadU16 Stage.verifyMmioExit guestMemory
                                                ((deterministicEntropyDescEntryAddr activeQueue head).value + 14) world7 with
                                              | error ioErr world8 =>
                                                simp [hDescNextRead] at hExec
                                              | ok descNextResult world8 =>
                                                cases descNextResult with
                                                | error err =>
                                                  simp [hDescNextRead] at hExec
                                                  cases hExec
                                                | ok descNext =>
                                                  simp [hDescNextRead] at hExec
                                                  cases hPlan :
                                                    buildDeterministicEntropyCompletionPlan
                                                    guestMemory.size activeQueue
                                                    device.prngState availIdx usedIdx head
                                                    descAddrLow descAddrHigh descLen
                                                    descFlags descNext with
                                                  | none =>
                                                    simp [hPlan] at hExec
                                                    cases hExec
                                                  | some plan =>
                                                    simp [hPlan] at hExec
                                                    have hRealize :
                                                      IOResultRunsTo
                                                      (realizeDeterministicEntropyCompletionPlan
                                                        guestMemory device plan)
                                                      (next, report) :=
                                                      ⟨world8, worldFinal, by
                                                        simpa using hExec⟩
                                                    rcases
                                                      realizeDeterministicEntropyCompletionPlan_success_reports_trace
                                                      guestMemory device plan hRealize with
                                                    ⟨hPlanEq, hWrites, hWrapperTrace,
                                                      hActiveEq, hLatchedEq, hPrngEq,
                                                      hCompleted, hInterrupt⟩
                                                    cases hPlanEq
                                                    exact ⟨hWrites, hWrapperTrace,
                                                      by simpa [hActive] using hActiveEq,
                                                      hLatchedEq, hPrngEq, hCompleted,
                                                      hInterrupt⟩

/-- The erased public completion function succeeds exactly when the report-producing executor
succeeds, so higher transport shells can recover the executed write trace without changing the
runtime implementation. -/
theorem completeDeterministicEntropyRequest_ok_exists_report
    (guestMemory : GuestMemory) (device : VirtioDeviceState) {next : VirtioDeviceState}
    (hExec : IOResultRunsTo (completeDeterministicEntropyRequest guestMemory device) next) :
    ∃ report,
      IOResultRunsTo (completeDeterministicEntropyRequestWithReport guestMemory device)
        (next, report) ∧
      report.writes = virtioEntropyCompletionWrites report.plan ∧
      virtioEntropyWriteTraceRealizedByWrappers guestMemory report.writes ∧
      next.activeQueue = device.activeQueue ∧
      next.latchedQueue = device.latchedQueue ∧
      next.prngState = report.plan.nextPrngState ∧
      next.requestCompleted = true ∧
      next.interruptStatus = 1 := by
  rcases hExec with ⟨world, nextWorld, hExec⟩
  rw [completeDeterministicEntropyRequest_defeq_withReport] at hExec
  rw [mapIOResult_apply] at hExec
  cases hWith : completeDeterministicEntropyRequestWithReport guestMemory device world with
  | error err world' =>
      simp [hWith] at hExec
  | ok result world' =>
      cases result with
      | error err =>
          simp [hWith] at hExec
      | ok value =>
          cases value with
          | mk next' report =>
              have hMatch := hExec
              simp [hWith] at hMatch
              rcases hMatch with ⟨rfl, rfl⟩
              have hReportExec :
                  IOResultRunsTo (completeDeterministicEntropyRequestWithReport guestMemory device)
                    (next', report) := by
                exact ⟨world, world', by simpa using hWith⟩
              rcases
                  completeDeterministicEntropyRequestWithReport_success_refines_executor
                    guestMemory device hReportExec with
                ⟨hWrites, hWrapperTrace, hActive, hLatched, hPrng, hCompleted, hInterrupt⟩
              exact ⟨report, hReportExec, hWrites, hWrapperTrace, hActive, hLatched, hPrng,
                hCompleted, hInterrupt⟩

end Microvmm
