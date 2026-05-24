namespace Microvmm

structure SerialState where
  dll : UInt32 := 0
  dlm : UInt32 := 0
  ier : UInt32 := 0
  lcr : UInt32 := 0x03
  mcr : UInt32 := 0
  fcr : UInt32 := 0
  scratch : UInt32 := 0
  inputQueue : List UInt32 := []
deriving Repr, DecidableEq

structure SerialReplayBuffer where
  bytes : ByteArray := ByteArray.empty
deriving DecidableEq

def SerialReplayBuffer.pushBounded (buffer : SerialReplayBuffer) (capacity : Nat)
    (byteValue : UInt32) : SerialReplayBuffer :=
  let normalized := byteValue &&& 0xff
  let nextBytes := buffer.bytes.push (UInt8.ofNat normalized.toNat)
  if nextBytes.size <= capacity then
    { bytes := nextBytes }
  else
    let start := nextBytes.size - capacity
    let keptBytes :=
      (List.range capacity).foldl
        (fun acc offset => acc.push (nextBytes.get! (start + offset)))
        ByteArray.empty
    { bytes := keptBytes }

def SerialReplayBuffer.toOutputBytes (buffer : SerialReplayBuffer) : List UInt32 :=
  (List.range buffer.bytes.size).map fun index =>
    UInt32.ofNat (buffer.bytes.get! index).toNat

def SerialReplayBuffer.render (buffer : SerialReplayBuffer) : String :=
  buffer.toOutputBytes.foldl
    (fun rendered byteValue => rendered.push (Char.ofNat byteValue.toNat))
    ""

instance : Repr SerialReplayBuffer where
  reprPrec buffer _ := repr buffer.render

/-- `retainedSuffix` keeps only the recent serial tail needed to recognize readiness markers
that can straddle byte boundaries; once a marker has been seen, the latched flags let later
truncation forget older bytes safely. -/
structure SerialProtocolState where
  retainedSuffix : String := ""
  probeReady : Bool := false
  interactiveReady : Bool := false
deriving Repr, DecidableEq

structure SerialConsole where
  uart : SerialState := {}
  replay : SerialReplayBuffer := {}
  protocol : SerialProtocolState := {}
deriving Repr, DecidableEq

structure SerialStep where
  console : SerialConsole
  response : Option UInt32 := none
  outputByte? : Option UInt32 := none
  ready : Bool := false
deriving Repr, DecidableEq

end Microvmm