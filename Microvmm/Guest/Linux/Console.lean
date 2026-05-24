import Microvmm.Bus.Mmio
import Microvmm.Bus.Platform
import Microvmm.Host
import Microvmm.Kvm

namespace Microvmm

open Kvm

private def mapOutcomeError {ε ε' α : Type}
    (f : ε → ε') : Outcome ε α → Outcome ε' α
  | .error err => .error (f err)
  | .ok value => .ok value

/-- Serial/MMIO guest-exit rules stay typed in the pure Linux domain; the outer runtime keeps the
existing `.verifyIoExit` / `EPROTO` surface so user-visible diagnostics do not change. -/
inductive LinuxConsoleError where
  | lapicMmioRequiresDwordAccess
  | passivePortAccessOutOfRange
  | passivePortInputUnsupported
  | com1RequiresByteAccess
  | unsupportedCom1InputRegister (offset : Nat)
  | unsupportedCom1OutputRegister (offset : Nat)
deriving Repr, DecidableEq

def linuxConsoleErrorToKvmError (_ : LinuxConsoleError) : Kvm.Error :=
  ⟨.verifyIoExit, eproto⟩

private def linuxConsoleErrorToErrno (_ : LinuxConsoleError) : UInt32 :=
  eproto

private def serialReplayCapacity : Nat := 4096

def serialInputCapacity : Nat := 1024

private def consoleAcceptBudget : Nat := 16

private def transcriptExcerptLength : Nat := 120

private def initrdReadyMarker : String := "MICROVMM_INITRD_READY"

def probeTranscriptReady (transcript : SerialProtocolState) : Bool :=
  transcript.probeReady

def interactiveTranscriptReady (transcript : SerialProtocolState) : Bool :=
  transcript.interactiveReady

private def probeReadyMarkers : List String := [
  "Linux",
  "Decompressing",
  "Booting the kernel"
]

private def serialProtocolSuffixCapacity : Nat :=
  (probeReadyMarkers ++ [initrdReadyMarker]).foldl
    (fun current marker => Nat.max current marker.length)
    0

private def retainRecentSuffix (text : String) (capacity : Nat) : String :=
  if text.length <= capacity then
    text
  else
    (text.drop (text.length - capacity)).toString

private def probeSuffixReady (suffix : String) : Bool :=
  probeReadyMarkers.any fun marker => suffix.contains marker

def buildTranscriptExcerpt (replay : SerialReplayBuffer) : String :=
  (replay.render.take transcriptExcerptLength).toString

/-- The retained suffix only needs to cover the longest readiness marker. Readiness itself is
monotone once observed, so later suffix trimming must preserve prior success as a latched flag. -/
private def observeSerialProtocolByte (protocol : SerialProtocolState)
    (byteValue : UInt32) : SerialProtocolState :=
  let dataByte := byteValue &&& 0xff
  let nextSuffix := retainRecentSuffix
    (protocol.retainedSuffix.push (Char.ofNat dataByte.toNat))
    serialProtocolSuffixCapacity
  {
    retainedSuffix := nextSuffix
    probeReady := protocol.probeReady || probeSuffixReady nextSuffix
    interactiveReady := protocol.interactiveReady || nextSuffix.contains initrdReadyMarker
  }

def captureSerialOutputByte (console : SerialConsole) (byteValue : UInt32) : SerialConsole :=
  {
    console with
    replay := console.replay.pushBounded serialReplayCapacity byteValue
    protocol := observeSerialProtocolByte console.protocol byteValue
  }

theorem observeSerialProtocolByte_probeReady_monotone (protocol : SerialProtocolState)
    (byteValue : UInt32) :
    protocol.probeReady = true ->
      (observeSerialProtocolByte protocol byteValue).probeReady = true := by
  intro hReady
  unfold observeSerialProtocolByte
  simp [hReady]

theorem observeSerialProtocolByte_interactiveReady_monotone (protocol : SerialProtocolState)
    (byteValue : UInt32) :
    protocol.interactiveReady = true ->
      (observeSerialProtocolByte protocol byteValue).interactiveReady = true := by
  intro hReady
  unfold observeSerialProtocolByte
  simp [hReady]

private def isCom1RegisterWrite (access : IoAccess) (offset : Nat) : Bool :=
  access.direction == .output && access.width == 1 && access.count == 1 &&
    access.port.value == com1Port.value + UInt32.ofNat offset

def shouldPulseCom1TxIrq (access : IoAccess) (serialState : SerialState) : Bool :=
  serialInterruptLineEnabled serialState && serialTransmitInterruptPending serialState &&
    ((isCom1RegisterWrite access 0 && (serialState.lcr &&& 0x80) == 0) ||
      isCom1RegisterWrite access 1 || isCom1RegisterWrite access 4)

def shouldPulseCom1RxIrq (before after : SerialState) : Bool :=
  serialInterruptLineEnabled after && serialReceiveInterruptPending after &&
    before.inputQueue.isEmpty && !after.inputQueue.isEmpty

def enqueueSerialInput (console : SerialConsole) (byteValue : UInt32) : SerialConsole :=
  let dataByte := byteValue &&& 0xff
  if console.uart.inputQueue.length < serialInputCapacity then
    {
      console with
      uart := {
        console.uart with
        inputQueue := console.uart.inputQueue ++ [dataByte]
      }
    }
  else
    console

private def dequeueSerialInput (serialState : SerialState) : UInt32 × SerialState :=
  match serialState.inputQueue with
  | [] => (0, serialState)
  | byteValue :: remaining =>
      (byteValue, { serialState with inputQueue := remaining })

def stepPassiveLinuxMmioTyped (access : MmioAccess) : Outcome LinuxConsoleError (Option UInt32) := do
  match stepPassiveLapicMmioTyped access with
  | .ok response? =>
      .ok response?
  | .error .requiresDwordAccess =>
      .error .lapicMmioRequiresDwordAccess

def stepPassiveLinuxMmio (access : MmioAccess) : ErrnoResult (Option UInt32) :=
  mapOutcomeError linuxConsoleErrorToErrno <| stepPassiveLinuxMmioTyped access

def stepSerialConsoleTyped (console : SerialConsole)
    (access : IoAccess) : Outcome LinuxConsoleError SerialStep := do
  let serialState := console.uart
  match serialPortBase? access.port.value with
  | none =>
      if boundedPassivePortAccess access then
        match access.direction with
        | .input =>
            match passivePortInput? access with
            | some response => .ok { console, response := some response }
            | none => .error .passivePortInputUnsupported
        | .output => .ok { console }
      else
        .error .passivePortAccessOutOfRange
  | some basePort =>
      let offset := access.port.value - basePort
      if basePort == com1Port.value then
        if access.width != 1 || access.count != 1 then
          .error .com1RequiresByteAccess
        else
          match access.direction with
          | .input =>
              match offset.toNat with
              | 0 =>
                  if (serialState.lcr &&& 0x80) != 0 then
                    .ok { console, response := some serialState.dll }
                  else
                    let (response, nextSerialState) := dequeueSerialInput serialState
                    .ok {
                      console := { console with uart := nextSerialState }
                      response := some response
                    }
              | 1 =>
                  .ok {
                    console
                    response := some <| if (serialState.lcr &&& 0x80) != 0 then serialState.dlm else serialState.ier
                  }
              | 2 => .ok { console, response := some <| serialIir serialState }
              | 3 => .ok { console, response := some serialState.lcr }
              | 4 => .ok { console, response := some serialState.mcr }
              | 5 => .ok { console, response := some <| serialLsr serialState }
              | 6 => .ok { console, response := some 0xb0 }
              | 7 => .ok { console, response := some serialState.scratch }
              | _ => .error (.unsupportedCom1InputRegister offset.toNat)
          | .output =>
              let dataByte := access.value
              match offset.toNat with
              | 0 =>
                  if (serialState.lcr &&& 0x80) != 0 then
                    .ok { console := { console with uart := { serialState with dll := dataByte } } }
                  else
                    let outputByte := dataByte &&& 0xff
                    let nextConsole := captureSerialOutputByte console outputByte
                    .ok {
                      console := nextConsole
                      outputByte? := some outputByte
                      ready := probeTranscriptReady nextConsole.protocol }
              | 1 =>
                  if (serialState.lcr &&& 0x80) != 0 then
                    .ok { console := { console with uart := { serialState with dlm := dataByte } } }
                  else
                    .ok { console := { console with uart := { serialState with ier := dataByte } } }
              | 2 => .ok { console := { console with uart := { serialState with fcr := dataByte } } }
              | 3 => .ok { console := { console with uart := { serialState with lcr := dataByte } } }
              | 4 => .ok { console := { console with uart := { serialState with mcr := dataByte } } }
              | 7 => .ok { console := { console with uart := { serialState with scratch := dataByte } } }
              | _ => .error (.unsupportedCom1OutputRegister offset.toNat)
      else if boundedPassivePortAccess access then
        match access.direction with
        | .input =>
            match passivePortInput? access with
            | some response => .ok { console, response := some response }
            | none => .error .passivePortInputUnsupported
        | .output => .ok { console }
      else
        .error .passivePortAccessOutOfRange

def stepSerialConsole (console : SerialConsole) (access : IoAccess) : Result SerialStep :=
  mapOutcomeError linuxConsoleErrorToKvmError <| stepSerialConsoleTyped console access

private def pollHostSerialInput (console : SerialConsole) : IO (Result SerialConsole) := do
  if console.uart.inputQueue.length >= serialInputCapacity then
    pure (.ok console)
  else
    mapIOResult (readHostStdinByteNonblocking) fun
      | none => console
      | some byteValue => enqueueSerialInput console byteValue

def emitSerialOutputByte (outputByte? : Option UInt32) : IO (Result Unit) := do
  match outputByte? with
  | none => pure (.ok ())
  | some byteValue => writeHostStdoutByte byteValue

def interactiveTransportReady (console : SerialConsole) : Bool :=
  interactiveTranscriptReady console.protocol

private def acceptConsoleServerClients (remaining : Nat) (replay : SerialReplayBuffer)
    (serverState : ConsoleServerState) :
    IO (Result ConsoleServerState) := do
  match remaining with
  | 0 =>
      pure (.ok serverState)
  | remaining + 1 =>
      match ← acceptConsoleClientNonblocking serverState.host.listener with
      | .error err =>
          pure (.error err)
      | .ok none =>
          pure (.ok serverState)
      | .ok (some client) =>
          let clientId := serverState.host.nextClientId
          let nextState : ConsoleServerState := {
            host := {
              serverState.host with
              nextClientId := clientId + 1
              clients := serverState.host.clients ++ [{ id := clientId, client := client }]
            }
            runtime := attachConsoleServerClient serverState.runtime clientId replay
          }
          acceptConsoleServerClients remaining replay nextState

private def flushConsoleClientPendingOutput (client : ConsoleClient)
    (pendingOutput : List UInt32) : IO (Option (List UInt32)) := do
  match pendingOutput with
  | [] =>
      pure (some [])
  | byteValue :: remaining =>
      match ← writeConsoleClientByteNonblocking client byteValue with
      | .error _ =>
          closeConsoleClientQuietly client
          pure none
      | .ok .sent =>
          flushConsoleClientPendingOutput client remaining
      | .ok .blocked =>
          pure (some pendingOutput)
      | .ok .disconnected =>
          closeConsoleClientQuietly client
          pure none

private def flushConsoleServerClient (runtime : ConsoleServerRuntime)
    (clientHandle : ConsoleClientHandle) :
    IO (ConsoleServerRuntime × Option ConsoleClientHandle) := do
  let clientRuntime :=
    match findConsoleClientRuntime? runtime clientHandle.id with
    | some clientState => clientState
    | none => { id := clientHandle.id }
  match ← flushConsoleClientPendingOutput clientHandle.client clientRuntime.pendingOutput with
  | some pendingOutput =>
      pure
        ({ runtime with
            clients :=
              (setConsoleClientRuntime runtime
                { clientRuntime with pendingOutput := pendingOutput }).clients },
          some clientHandle)
  | none =>
      pure (dropConsoleServerClient runtime clientHandle.id, none)

private def flushConsoleServerClientsList (runtime : ConsoleServerRuntime)
    (clients : List ConsoleClientHandle) :
    IO (ConsoleServerRuntime × List ConsoleClientHandle) := do
  match clients with
  | [] =>
      pure (runtime, [])
  | clientHandle :: rest =>
      let (runtime', clientHandle?) ← flushConsoleServerClient runtime clientHandle
      let (runtime'', rest') ← flushConsoleServerClientsList runtime' rest
      pure <| match clientHandle? with
      | some nextClient => (runtime'', nextClient :: rest')
      | none => (runtime'', rest')

private def pollConsoleServerClientInput (clientHandle : ConsoleClientHandle) :
    IO (Option ConsoleClientHandle × Option UInt32) := do
  match ← readConsoleClientByteNonblocking clientHandle.client with
  | .error _ =>
      closeConsoleClientQuietly clientHandle.client
      pure (none, none)
  | .ok .noData =>
      pure (some clientHandle, none)
  | .ok .disconnected =>
      closeConsoleClientQuietly clientHandle.client
      pure (none, none)
  | .ok (.byte byteValue) =>
      pure (some clientHandle, some byteValue)

private def pollConsoleServerInputsList (remainingCapacity : Nat)
    (runtime : ConsoleServerRuntime) (clients : List ConsoleClientHandle) :
    IO (ConsoleServerRuntime × List ConsoleClientHandle × List UInt32) := do
  match clients with
  | [] =>
      pure (runtime, [], [])
  | clientHandle :: rest =>
      if remainingCapacity == 0 then
        pure (runtime, clientHandle :: rest, [])
      else
        let (clientHandle?, inputByte?) ← pollConsoleServerClientInput clientHandle
        -- Host disconnects happen before the pure runtime drops the matching queue entry so the
        -- live handle and proof-relevant queue state never diverge on which clients still exist.
        let runtime' :=
          match clientHandle? with
          | some _ => runtime
          | none => dropConsoleServerClient runtime clientHandle.id
        let remainingCapacity' :=
          match inputByte? with
          | some _ => remainingCapacity - 1
          | none => remainingCapacity
        let (runtime'', rest', inputBytes) ←
          pollConsoleServerInputsList remainingCapacity' runtime' rest
        let clients' :=
          match clientHandle? with
          | some nextClient => nextClient :: rest'
          | none => rest'
        let inputBytes' :=
          match inputByte? with
          | some byteValue => byteValue :: inputBytes
          | none => inputBytes
        pure (runtime'', clients', inputBytes')

private def pollConsoleServerInput (console : SerialConsole) (serverState : ConsoleServerState) :
    IO (SerialConsole × ConsoleServerState) := do
  let remainingCapacity := serialInputCapacity - console.uart.inputQueue.length
  let (runtime, clients, inputBytes) ←
    pollConsoleServerInputsList remainingCapacity serverState.runtime serverState.host.clients
  pure
    (inputBytes.foldl enqueueSerialInput console,
      { host := { serverState.host with clients := clients }, runtime := runtime })

private def closeDroppedConsoleServerClients (droppedClientIds : List ConsoleClientId)
    (clients : List ConsoleClientHandle) : IO (List ConsoleClientHandle) := do
  match clients with
  | [] =>
      pure []
  | clientHandle :: rest =>
      let rest' ← closeDroppedConsoleServerClients droppedClientIds rest
      if droppedClientIds.contains clientHandle.id then
        -- Once the pure runtime rejects a queue append, close the host socket before forgetting
        -- the handle so later proofs only reason about the surviving runtime clients.
        closeConsoleClientQuietly clientHandle.client
        pure rest'
      else
        pure (clientHandle :: rest')

def pollInteractiveTransportInput (console : SerialConsole)
    (transport : InteractiveConsoleTransport) :
    IO (Result (SerialConsole × InteractiveConsoleTransport)) := do
  let ready := interactiveTransportReady console
  match transport with
  | .stdio =>
      if ready then
        mapIOResult (pollHostSerialInput console) fun queuedConsole =>
          (queuedConsole, .stdio)
      else
        pure (.ok (console, .stdio))
  | .server serverState =>
      bindIOResult
        (acceptConsoleServerClients consoleAcceptBudget console.replay serverState)
        fun acceptedState => do
        let (runtime, flushedClients) ←
          flushConsoleServerClientsList acceptedState.runtime acceptedState.host.clients
        let flushedState := {
          host := { acceptedState.host with clients := flushedClients }
          runtime := runtime
        }
        if ready then
          let (queuedConsole, nextState) ← pollConsoleServerInput console flushedState
          pure (.ok (queuedConsole, .server nextState))
        else
          pure (.ok (console, .server flushedState))

def emitInteractiveOutputByte (transport : InteractiveConsoleTransport)
    (outputByte? : Option UInt32) : IO (Result InteractiveConsoleTransport) := do
  match outputByte? with
  | none =>
      pure (.ok transport)
  | some byteValue =>
      match transport with
      | .stdio =>
          mapIOResult (writeHostStdoutByte byteValue) fun _ =>
            .stdio
      | .server serverState =>
          bindIOResult (writeSerialLogByte serverState.host.serialLog byteValue) fun _ => do
            let queued := queueConsoleServerOutput serverState.runtime byteValue
            let acceptedClients ←
              closeDroppedConsoleServerClients queued.droppedClientIds serverState.host.clients
            let (runtime, clients) ← flushConsoleServerClientsList queued.runtime acceptedClients
            pure (.ok (.server {
              host := { serverState.host with clients := clients }
              runtime := runtime
            }))

end Microvmm