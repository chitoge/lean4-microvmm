import Microvmm.Common
import Microvmm.Core.Address

namespace Microvmm

/-- Summary returned by the standalone virtio-mmio entropy probe after the guest finishes the
expected request/completion exchange. -/
structure VirtioEntropySuccess where
  apiVersion : UInt32
  runAreaSize : UInt32
  payloadSummary : String
deriving Repr, DecidableEq

/-- Queue register contents exactly as written by the guest before activation. These values are
not trusted for execution until `QueueReady` validates them and converts them into `QueueConfig`. -/
structure RawQueueConfig where
  num : UInt32 := 0
  descAddr : UInt64 := 0
  availAddr : UInt64 := 0
  usedAddr : UInt64 := 0
  ready : UInt32 := 0
deriving Repr, DecidableEq, BEq, Inhabited

/-- Validated queue geometry used by the live device path. Once activation succeeds, execution
reads only from this typed queue rather than from the mutable raw register shadow. -/
structure QueueConfig where
  num : UInt32
  descAddr : GuestPhysAddr
  availAddr : GuestPhysAddr
  usedAddr : GuestPhysAddr
deriving Repr, DecidableEq, BEq

/-- Explicit deterministic PRNG state for virtio-rng. Keeping the seed evolution in Lean makes
the executable path and the proof path talk about the same byte stream. -/
structure PrngState where
  s0 : UInt64
  s1 : UInt64
  s2 : UInt64
  s3 : UInt64
  requestsServed : UInt64 := 0
deriving Repr, DecidableEq, BEq

def defaultVirtioEntropyPrngSeed : UInt64 := 0x57b35061c255afe1

private def splitMix64Gamma : UInt64 := 0x9e3779b97f4a7c15

private def splitMix64Mix1 : UInt64 := 0xbf58476d1ce4e5b9

private def splitMix64Mix2 : UInt64 := 0x94d049bb133111eb

private def splitMix64Output (state : UInt64) : UInt64 :=
  let z1 := (state ^^^ (state >>> 30)) * splitMix64Mix1
  let z2 := (z1 ^^^ (z1 >>> 27)) * splitMix64Mix2
  z2 ^^^ (z2 >>> 31)

def defaultVirtioEntropyPrngState : PrngState :=
  let seed0 := defaultVirtioEntropyPrngSeed + splitMix64Gamma
  let seed1 := seed0 + splitMix64Gamma
  let seed2 := seed1 + splitMix64Gamma
  let seed3 := seed2 + splitMix64Gamma
  {
    s0 := splitMix64Output seed0
    s1 := splitMix64Output seed1
    s2 := splitMix64Output seed2
    s3 := splitMix64Output seed3
  }

instance : Inhabited PrngState where
  default := defaultVirtioEntropyPrngState

/-- Device state is split into four queue views so the implementation and the proofs can talk
precisely about what the guest most recently wrote, what has been validated, and what later guest
mutation attempts tried to change. -/
structure VirtioDeviceState where
  deviceFeaturesSel : UInt32 := 0
  driverFeaturesSel : UInt32 := 0
  driverFeatures : UInt64 := 0
  status : UInt32 := 0
  queueSel : UInt32 := 0
  interruptStatus : UInt32 := 0
  resetSeen : Bool := false
  featuresOkAccepted : Bool := false
  driverOkSeen : Bool := false
  mutationAttempted : Bool := false
  mutationIgnored : Bool := false
  notifySeen : Bool := false
  requestCompleted : Bool := false
  prngState : PrngState := defaultVirtioEntropyPrngState
  stagedQueue : RawQueueConfig := default
  activeQueue : Option QueueConfig := none
  latchedQueue : Option QueueConfig := none
  attemptedQueue : RawQueueConfig := default
deriving Repr, DecidableEq, BEq

instance : Inhabited VirtioDeviceState where
  default := {}

inductive QueueAddrField where
  | desc
  | avail
  | used
deriving Repr, DecidableEq

inductive MmioWriteAction where
  | none
  | processQueue
deriving Repr, DecidableEq

/-- Transport decoders return both the next state and whether that write should trigger virtio-rng
request execution. This keeps MMIO and PCI as thin register-translation layers above the shared
device core. -/
structure MmioStep (σ : Type) where
  state : σ
  response : Option UInt32 := none
  action : MmioWriteAction := .none

def virtioQueueNumMax : UInt32 := 1

def virtioFVersion1Bit : UInt64 := 0x0000000100000000

def virtioStatusAcknowledge : UInt32 := 0x01

def virtioStatusDriver : UInt32 := 0x02

def virtioStatusDriverOk : UInt32 := 0x04

def virtioStatusFeaturesOk : UInt32 := 0x08

def queueConfigEquals (lhs : QueueConfig) (rhs : QueueConfig) : Bool :=
  lhs == rhs

def rawQueueOf (queue : QueueConfig) : RawQueueConfig :=
  {
    num := queue.num
    descAddr := queue.descAddr.value
    availAddr := queue.availAddr.value
    usedAddr := queue.usedAddr.value
    ready := 1
  }

def currentQueueRegisters (device : VirtioDeviceState) : RawQueueConfig :=
  match device.activeQueue with
  | some queue => rawQueueOf queue
  | none => device.stagedQueue

def deviceFeaturesWord (device : VirtioDeviceState) : UInt32 :=
  if device.deviceFeaturesSel == 0 then
    low32 virtioFVersion1Bit
  else if device.deviceFeaturesSel == 1 then
    high32 virtioFVersion1Bit
  else
    0

def driverFeaturesWord (device : VirtioDeviceState) : UInt32 :=
  if device.driverFeaturesSel == 0 then
    low32 device.driverFeatures
  else if device.driverFeaturesSel == 1 then
    high32 device.driverFeatures
  else
    0

def resetVirtioDevice (sawReset : Bool) : VirtioDeviceState :=
  let device : VirtioDeviceState := default
  { device with resetSeen := sawReset }

def setDeviceFeaturesSel (device : VirtioDeviceState) (value : UInt32) : VirtioDeviceState :=
  { device with deviceFeaturesSel := value }

def setDriverFeaturesSel (device : VirtioDeviceState) (value : UInt32) : VirtioDeviceState :=
  { device with driverFeaturesSel := value }

def setDriverFeatures (device : VirtioDeviceState) (value : UInt32) : VirtioDeviceState :=
  let nextFeatures :=
    if device.driverFeaturesSel == 0 then
      setU64Low device.driverFeatures value
    else if device.driverFeaturesSel == 1 then
      setU64High device.driverFeatures value
    else
      device.driverFeatures
  { device with driverFeatures := nextFeatures }

def selectedQueueSize (device : VirtioDeviceState) : UInt32 :=
  if device.queueSel != 0 then
    0
  else
    match device.activeQueue with
    | some queue => queue.num
    | none =>
        if device.stagedQueue.num == 0 then
          virtioQueueNumMax
        else
          device.stagedQueue.num

def writeQueueSel (device : VirtioDeviceState) (value : UInt32) : ErrnoResult VirtioDeviceState :=
  if value != 0 then
    .error eproto
  else
    .ok { device with queueSel := value }

def acknowledgeInterruptStatus (device : VirtioDeviceState) (value : UInt32) : VirtioDeviceState :=
  { device with interruptStatus := device.interruptStatus &&& (~~~value) }

def markQueueNotified (device : VirtioDeviceState) : ErrnoResult VirtioDeviceState :=
  if !device.driverOkSeen || device.activeQueue.isNone then
    .error eproto
  else
    .ok { device with notifySeen := true }

/-- Once `QueueReady` latches a valid queue, later guest writes are kept only in
`attemptedQueue` so proofs can talk about ignored mutations without changing the live queue. -/
def noteIgnoredQueueMutation (device : VirtioDeviceState) : VirtioDeviceState :=
  match device.latchedQueue with
  | none => device
  | some latchedQueue =>
      { device with
        mutationAttempted := device.mutationAttempted || device.attemptedQueue != rawQueueOf latchedQueue
        mutationIgnored :=
          match device.activeQueue with
          | some activeQueue => queueConfigEquals activeQueue latchedQueue
          | none => false }

def updateQueueAddr (queue : RawQueueConfig) (field : QueueAddrField) (value : UInt32)
    (highHalf : Bool) : RawQueueConfig :=
  let updated :=
    match field with
    | .desc =>
        if highHalf then setU64High queue.descAddr value else setU64Low queue.descAddr value
    | .avail =>
        if highHalf then setU64High queue.availAddr value else setU64Low queue.availAddr value
    | .used =>
        if highHalf then setU64High queue.usedAddr value else setU64Low queue.usedAddr value
  match field with
  | .desc => { queue with descAddr := updated }
  | .avail => { queue with availAddr := updated }
  | .used => { queue with usedAddr := updated }

/-- `QueueReady` is the single activation gate for the current virtio-rng model: one queue, size
1, and non-zero desc/avail/used ring bases. MMIO and PCI both reuse this helper so proofs can cite
one executable definition of queue activation. -/
def validateQueueDraft (queue : RawQueueConfig) : ErrnoResult QueueConfig :=
  if queue.num != virtioQueueNumMax || queue.descAddr == 0 || queue.availAddr == 0 ||
      queue.usedAddr == 0 then
    .error eproto
  else
    .ok {
      num := queue.num
      descAddr := ⟨queue.descAddr⟩
      availAddr := ⟨queue.availAddr⟩
      usedAddr := ⟨queue.usedAddr⟩
    }

def handleStatusWrite (device : VirtioDeviceState) (value : UInt32) :
    ErrnoResult VirtioDeviceState := do
  if value == 0 then
    pure <| resetVirtioDevice true
  else
    let _ ←
      if (value &&& device.status) != device.status then
        .error eproto
      else
        .ok ()
    let mut next := device
    let mut status := value
    if (status &&& virtioStatusFeaturesOk) != 0 then
      if next.driverFeatures == virtioFVersion1Bit then
        next := { next with featuresOkAccepted := true }
      else
        status := status &&& (~~~virtioStatusFeaturesOk)
    if (status &&& virtioStatusDriverOk) != 0 then
      let _ ←
        if !next.featuresOkAccepted || next.activeQueue.isNone then
          .error eproto
        else
          .ok ()
      next := { next with driverOkSeen := true }
    pure { next with status := status }

def writeQueueNum (device : VirtioDeviceState) (value : UInt32) : ErrnoResult VirtioDeviceState :=
  if device.queueSel != 0 then
    .error eproto
  else if device.activeQueue.isSome then
    let next := { device with attemptedQueue := { device.attemptedQueue with num := value } }
    .ok <| noteIgnoredQueueMutation next
  else
    let nextQueue := { device.stagedQueue with num := value }
    .ok { device with stagedQueue := nextQueue, attemptedQueue := nextQueue }

def writeQueueAddr (device : VirtioDeviceState) (field : QueueAddrField) (value : UInt32)
    (highHalf : Bool) : ErrnoResult VirtioDeviceState :=
  if device.queueSel != 0 then
    .error eproto
  else if device.activeQueue.isSome then
    let attemptedQueue := updateQueueAddr device.attemptedQueue field value highHalf
    .ok <| noteIgnoredQueueMutation { device with attemptedQueue := attemptedQueue }
  else
    let stagedQueue := updateQueueAddr device.stagedQueue field value highHalf
    .ok { device with stagedQueue := stagedQueue, attemptedQueue := stagedQueue }

def writeQueueReady (device : VirtioDeviceState) (value : UInt32) : ErrnoResult VirtioDeviceState :=
  if device.queueSel != 0 || value > 1 then
    .error eproto
  else if device.activeQueue.isSome then
    let next := { device with attemptedQueue := { device.attemptedQueue with ready := value } }
    .ok <| noteIgnoredQueueMutation next
  else if value == 0 then
    .ok { device with stagedQueue := { device.stagedQueue with ready := 0 } }
  else
    let stagedQueue := { device.stagedQueue with ready := 1 }
    match validateQueueDraft stagedQueue with
    | .error err =>
        .error err
    | .ok activeQueue =>
        .ok {
          device with
          stagedQueue := stagedQueue
          activeQueue := some activeQueue
          latchedQueue := some activeQueue
          attemptedQueue := rawQueueOf activeQueue }

end Microvmm
