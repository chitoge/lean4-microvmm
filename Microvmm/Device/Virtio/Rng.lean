import Microvmm.Device.Virtio.Core
import Microvmm.Kvm

namespace Microvmm

open Kvm

/-- One `xoshiro256**` output word yields eight virtio-rng payload bytes. -/
def virtioPayloadLength : UInt32 := 8

private def prngPayloadByte (word : UInt64) (shift : UInt64) : UInt32 :=
    UInt32.ofNat (((word >>> shift) &&& (0xff : UInt64)).toNat)

private def prngRotateLeft7 (word : UInt64) : UInt64 :=
    (word <<< 7) ||| (word >>> 57)

private def prngRotateLeft45 (word : UInt64) : UInt64 :=
    (word <<< 45) ||| (word >>> 19)

private def prngOutputWord (state : PrngState) : UInt64 :=
    (prngRotateLeft7 (state.s1 * 5)) * 9

def prngStep (state : PrngState) : PrngState :=
    let t : UInt64 := state.s1 <<< 17
    let s2 := state.s2 ^^^ state.s0
    let s3 := state.s3 ^^^ state.s1
    let s1 := state.s1 ^^^ s2
    let s0 := state.s0 ^^^ s3
    let s2 := s2 ^^^ t
    let s3 := prngRotateLeft45 s3
    {
      s0 := s0
      s1 := s1
      s2 := s2
      s3 := s3
      requestsServed := state.requestsServed + 1
    }

def prngPayloadBytes (word : UInt64) : List UInt32 :=
    [ prngPayloadByte word 56
    , prngPayloadByte word 48
    , prngPayloadByte word 40
    , prngPayloadByte word 32
    , prngPayloadByte word 24
    , prngPayloadByte word 16
    , prngPayloadByte word 8
    , prngPayloadByte word 0
    ]

def prngNextPayload (state : PrngState) : PrngState × List UInt32 :=
    let outputWord := prngOutputWord state
    let nextState := prngStep state
    (nextState, prngPayloadBytes outputWord)

def prngGeneratePayloadChunks (state : PrngState) : Nat → PrngState × List UInt32
    | 0 =>
            (state, [])
    | count + 1 =>
            let (nextState, chunk) := prngNextPayload state
            let (finalState, tail) := prngGeneratePayloadChunks nextState count
            (finalState, chunk ++ tail)

def prngGenerateBytes (state : PrngState) (length : Nat) : PrngState × List UInt32 :=
        let chunkLen := virtioPayloadLength.toNat
        let chunkCount :=
            match length with
            | 0 => 0
            | count + 1 => (count / chunkLen) + 1
        let (finalState, payload) := prngGeneratePayloadChunks state chunkCount
        (finalState, payload.take length)

def virtioPayload : List UInt32 :=
    (prngNextPayload defaultVirtioEntropyPrngState).2

def virtioPayloadSummary : String := "first 8 bytes [96 6f a6 57 b7 ad 3d 99]"

private def vringDescFNext : UInt32 := 0x01

private def vringDescFWrite : UInt32 := 0x02

private def vringDescFIndirect : UInt32 := 0x04

def splitAvailSpan (queueNum : UInt32) : UInt64 :=
  4 + (UInt64.ofNat queueNum.toNat) * 2 + 2

def splitUsedSpan (queueNum : UInt32) : UInt64 :=
  4 + (UInt64.ofNat queueNum.toNat) * 8 + 2

def deterministicEntropyRingSlot (queue : QueueConfig) (usedIdx : UInt32) : Nat :=
    usedIdx.toNat % queue.num.toNat

def deterministicEntropyAvailEntryAddr (queue : QueueConfig) (usedIdx : UInt32) : GuestPhysAddr :=
    ⟨queue.availAddr.value + UInt64.ofNat (4 + deterministicEntropyRingSlot queue usedIdx * 2)⟩

def deterministicEntropyUsedEntryAddr (queue : QueueConfig) (usedIdx : UInt32) : GuestPhysAddr :=
    ⟨queue.usedAddr.value + UInt64.ofNat (4 + deterministicEntropyRingSlot queue usedIdx * 8)⟩

def deterministicEntropyDescEntryAddr (queue : QueueConfig) (head : UInt32) : GuestPhysAddr :=
    ⟨queue.descAddr.value + UInt64.ofNat (head.toNat * 16)⟩

def deterministicEntropyDmaTargets (queue : QueueConfig) (usedIdx head : UInt32) :
        GuestPhysAddr × GuestPhysAddr × GuestPhysAddr :=
    ( deterministicEntropyAvailEntryAddr queue usedIdx
    , deterministicEntropyUsedEntryAddr queue usedIdx
    , deterministicEntropyDescEntryAddr queue head )

inductive VirtioEntropyWriteWidth where
    | u8
    | u16
    | u32
deriving Repr, DecidableEq, BEq

structure VirtioEntropyWrite where
    addr : GuestPhysAddr
    width : VirtioEntropyWriteWidth
    value : UInt32
deriving Repr, DecidableEq, BEq

/-- Pure description of one accepted virtio-rng request. The planner fixes every guest address,
payload byte, and used-ring update before the IO path touches guest memory. -/
structure DeterministicEntropyCompletionPlan where
    availEntryAddr : GuestPhysAddr
    usedEntryAddr : GuestPhysAddr
    descEntryAddr : GuestPhysAddr
    payloadAddr : GuestPhysAddr
    usedIndexAddr : GuestPhysAddr
    nextUsedIdx : UInt32
    completedHead : UInt32
    nextPrngState : PrngState
    completedLen : UInt32
    payload : List UInt32
deriving Repr, DecidableEq

/-- Report returned by the live executor so proofs can compare the executed guest-memory trace with
the pure plan that justified it. -/
structure VirtioEntropyExecutionReport where
    plan : DeterministicEntropyCompletionPlan
    writes : List VirtioEntropyWrite
deriving Repr, DecidableEq

private def payloadWritesAt (baseAddr : GuestPhysAddr) (payload : List UInt32)
    (offset : UInt64 := 0) : List VirtioEntropyWrite :=
  match payload with
  | [] =>
      []
  | byteValue :: remaining =>
      { addr := ⟨baseAddr.value + offset⟩, width := .u8, value := byteValue } ::
        payloadWritesAt baseAddr remaining (offset + 1)

def virtioEntropyCompletionWrites (plan : DeterministicEntropyCompletionPlan) :
        List VirtioEntropyWrite :=
    let payloadWrites := payloadWritesAt plan.payloadAddr plan.payload
    payloadWrites ++
        [ { addr := plan.usedEntryAddr, width := .u32, value := plan.completedHead }
        , { addr := ⟨plan.usedEntryAddr.value + 4⟩, width := .u32, value := plan.completedLen }
        , { addr := plan.usedIndexAddr, width := .u16, value := plan.nextUsedIdx }
        ]

/-- This pure completion plan is the proof-facing cut for seeded virtio-rng completion: if the
queue geometry and descriptor fields validate, the device has exactly one PRNG-derived payload to
write and exactly one used-ring completion to publish. The IO path below only executes this plan. -/
def buildDeterministicEntropyCompletionPlan (guestMemorySize : UInt64) (queue : QueueConfig)
        (prngState : PrngState) (availIdx usedIdx head descAddrLow descAddrHigh descLen descFlags
          descNext : UInt32) :
        Option DeterministicEntropyCompletionPlan :=
    let descSpan : UInt64 := (UInt64.ofNat queue.num.toNat) * 16
    let availSpan := splitAvailSpan queue.num
    let usedSpan := splitUsedSpan queue.num
    let expectedAvailIdx := (usedIdx + 1) &&& 0xffff
    let descAddr : GuestPhysAddr := ⟨combineLowHigh descAddrLow descAddrHigh⟩
    let requestedLenNat := descLen.toNat
    let (nextPrngState, payload) := prngGenerateBytes prngState requestedLenNat
    if queue.num != virtioQueueNumMax then
        none
    else if !guestSpanValidFor guestMemorySize queue.descAddr.value descSpan ||
            !guestSpanValidFor guestMemorySize queue.availAddr.value availSpan ||
            !guestSpanValidFor guestMemorySize queue.usedAddr.value usedSpan then
        none
    else if availIdx != expectedAvailIdx || head >= queue.num ||
            (descFlags &&& (vringDescFNext ||| vringDescFIndirect)) != 0 ||
            (descFlags &&& vringDescFWrite) == 0 || descNext != 0 ||
            !guestSpanValidFor guestMemorySize descAddr.value (UInt64.ofNat requestedLenNat) then
        none
    else
        some {
            availEntryAddr := deterministicEntropyAvailEntryAddr queue usedIdx
            usedEntryAddr := deterministicEntropyUsedEntryAddr queue usedIdx
            descEntryAddr := deterministicEntropyDescEntryAddr queue head
            payloadAddr := descAddr
            usedIndexAddr := ⟨queue.usedAddr.value + UInt64.ofNat 2⟩
            nextUsedIdx := expectedAvailIdx
            completedHead := head
            nextPrngState := nextPrngState
            completedLen := descLen
            payload := payload
        }

def executeVirtioEntropyWrite (guestMemory : GuestMemory) (write : VirtioEntropyWrite) :
    IO (Result Unit) := do
  match write.width with
  | .u8 =>
      guestWriteU8 .verifyMmioExit guestMemory write.addr.value write.value
  | .u16 =>
      guestWriteU16 .verifyMmioExit guestMemory write.addr.value write.value
  | .u32 =>
      guestWriteU32 .verifyMmioExit guestMemory write.addr.value write.value

def executeVirtioEntropyWriteTrace (guestMemory : GuestMemory)
    (writes : List VirtioEntropyWrite) : IO (Result Unit) := do
  match writes with
  | [] =>
      pure (.ok ())
  | write :: remaining =>
      bindIOResult (executeVirtioEntropyWrite guestMemory write) fun _ =>
        executeVirtioEntropyWriteTrace guestMemory remaining

/-- Execute the exact guest-memory write trace described by a validated virtio-rng completion plan.
The proof-facing refinement surface talks about `virtioEntropyCompletionWrites`; this function is
the live VM path that sends those writes to the trusted packed guest-write helpers. -/
def realizeDeterministicEntropyCompletionPlan (guestMemory : GuestMemory)
    (device : VirtioDeviceState) (plan : DeterministicEntropyCompletionPlan) :
    IO (Result (VirtioDeviceState × VirtioEntropyExecutionReport)) := do
  let writes := virtioEntropyCompletionWrites plan
  bindIOResult (executeVirtioEntropyWriteTrace guestMemory writes) fun _ =>
    pure (.ok (
            { device with
                    interruptStatus := 1
                    requestCompleted := true
                    prngState := plan.nextPrngState },
      { plan := plan, writes := writes }
    ))

/-- Proof-facing variant of virtio-rng completion. It is the real executor used by the VM path,
but it also returns the completion plan and exact write trace that were executed so proofs can map
to the live device path up to the trusted guest-write boundary. -/
def completeDeterministicEntropyRequestWithReport (guestMemory : GuestMemory)
    (device : VirtioDeviceState) : IO (Result (VirtioDeviceState × VirtioEntropyExecutionReport)) := do
  match device.activeQueue with
  | none =>
      pure (.error ⟨.verifyMmioExit, eproto⟩)
  | some activeQueue =>
      let descSpan : UInt64 := (UInt64.ofNat activeQueue.num.toNat) * 16
      let availSpan := splitAvailSpan activeQueue.num
      let usedSpan := splitUsedSpan activeQueue.num
      if activeQueue.num != virtioQueueNumMax then
        pure (.error ⟨.verifyMmioExit, eproto⟩)
      else if !guestSpanValidFor guestMemory.size activeQueue.descAddr.value descSpan ||
          !guestSpanValidFor guestMemory.size activeQueue.availAddr.value availSpan ||
          !guestSpanValidFor guestMemory.size activeQueue.usedAddr.value usedSpan then
        pure (.error ⟨.verifyMmioExit, eproto⟩)
      else
        match ← guestReadU16 .verifyMmioExit guestMemory (activeQueue.availAddr + 2) with
        | .error err =>
            pure (.error err)
        | .ok availIdx =>
            match ← guestReadU16 .verifyMmioExit guestMemory (activeQueue.usedAddr + 2) with
            | .error err =>
                pure (.error err)
            | .ok usedIdx =>
                let availEntryAddr := deterministicEntropyAvailEntryAddr activeQueue usedIdx
                match ← guestReadU16 .verifyMmioExit guestMemory availEntryAddr with
                | .error err =>
                    pure (.error err)
                | .ok head =>
                    let descEntryAddr := deterministicEntropyDescEntryAddr activeQueue head
                    match ← guestReadU32 .verifyMmioExit guestMemory descEntryAddr with
                    | .error err =>
                        pure (.error err)
                    | .ok descAddrLow =>
                        match ← guestReadU32 .verifyMmioExit guestMemory (descEntryAddr + 4) with
                        | .error err =>
                            pure (.error err)
                        | .ok descAddrHigh =>
                            match ← guestReadU32 .verifyMmioExit guestMemory (descEntryAddr + 8) with
                            | .error err =>
                                pure (.error err)
                            | .ok descLen =>
                                match ← guestReadU16 .verifyMmioExit guestMemory (descEntryAddr + 12) with
                                | .error err =>
                                    pure (.error err)
                                | .ok descFlags =>
                                    match ← guestReadU16 .verifyMmioExit guestMemory (descEntryAddr + 14) with
                                    | .error err =>
                                        pure (.error err)
                                    | .ok descNext =>
                                        match buildDeterministicEntropyCompletionPlan guestMemory.size
                                            activeQueue device.prngState availIdx usedIdx head descAddrLow descAddrHigh
                                            descLen descFlags descNext with
                                        | none =>
                                            pure (.error ⟨.verifyMmioExit, eproto⟩)
                                        | some plan =>
                                            realizeDeterministicEntropyCompletionPlan guestMemory device plan

/-- Linux may keep one outstanding buffer while advancing `avail_idx`, so completion compares the
guest-visible `avail_idx` and `used_idx` rather than assuming a one-shot ring state. -/
def completeDeterministicEntropyRequest (guestMemory : GuestMemory) (device : VirtioDeviceState) :
    IO (Result VirtioDeviceState) :=
  mapIOResult (completeDeterministicEntropyRequestWithReport guestMemory device) Prod.fst

end Microvmm
