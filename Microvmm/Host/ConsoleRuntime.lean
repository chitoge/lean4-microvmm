import Microvmm.Host.ConsoleTypes

namespace Microvmm

private def normalizeByte (byteValue : UInt32) : UInt32 :=
  byteValue &&& 0xff

def queueConsoleClientOutput (clientState : ConsoleClientRuntime) (byteValue : UInt32) :
    Option ConsoleClientRuntime :=
  if clientState.pendingOutput.length < consoleClientOutputCapacity then
    some {
      clientState with
      pendingOutput := clientState.pendingOutput ++ [normalizeByte byteValue]
    }
  else
    none

def queueConsoleClientReplay (clientState : ConsoleClientRuntime) (replay : SerialReplayBuffer) :
    Option ConsoleClientRuntime :=
  replay.toOutputBytes.foldl
    (fun queuedClient? byteValue => do
      let queuedClient ← queuedClient?
      queueConsoleClientOutput queuedClient byteValue)
    (some clientState)

private def findConsoleClientRuntimeList? (clients : List ConsoleClientRuntime)
    (clientId : ConsoleClientId) : Option ConsoleClientRuntime :=
  match clients with
  | [] => none
  | clientState :: rest =>
      if clientState.id == clientId then
        some clientState
      else
        findConsoleClientRuntimeList? rest clientId

def findConsoleClientRuntime? (runtime : ConsoleServerRuntime)
    (clientId : ConsoleClientId) : Option ConsoleClientRuntime :=
  findConsoleClientRuntimeList? runtime.clients clientId

private def setConsoleClientRuntimeList (clients : List ConsoleClientRuntime)
    (updated : ConsoleClientRuntime) : List ConsoleClientRuntime :=
  match clients with
  | [] => [updated]
  | clientState :: rest =>
      if clientState.id == updated.id then
        updated :: rest
      else
        clientState :: setConsoleClientRuntimeList rest updated

def setConsoleClientRuntime (runtime : ConsoleServerRuntime)
    (updated : ConsoleClientRuntime) : ConsoleServerRuntime :=
  { runtime with clients := setConsoleClientRuntimeList runtime.clients updated }

private def dropConsoleServerClientList (clients : List ConsoleClientRuntime)
    (clientId : ConsoleClientId) : List ConsoleClientRuntime :=
  match clients with
  | [] => []
  | clientState :: rest =>
      if clientState.id == clientId then
        rest
      else
        clientState :: dropConsoleServerClientList rest clientId

def dropConsoleServerClient (runtime : ConsoleServerRuntime)
    (clientId : ConsoleClientId) : ConsoleServerRuntime :=
  { runtime with clients := dropConsoleServerClientList runtime.clients clientId }

/-- Replay seeding is kept pure so late-attach behavior can be reasoned about without mentioning
host socket handles. -/
def seedConsoleClientRuntime (clientId : ConsoleClientId)
    (replay : SerialReplayBuffer) : ConsoleClientRuntime :=
  match queueConsoleClientReplay ({ id := clientId } : ConsoleClientRuntime) replay with
  | some queuedClient => queuedClient
  | none => { id := clientId }

def attachConsoleServerClient (runtime : ConsoleServerRuntime)
    (clientId : ConsoleClientId) (replay : SerialReplayBuffer) : ConsoleServerRuntime :=
  { runtime with clients := runtime.clients ++ [seedConsoleClientRuntime clientId replay] }

structure QueueConsoleServerOutputResult where
  runtime : ConsoleServerRuntime
  droppedClientIds : List ConsoleClientId := []
deriving Repr, DecidableEq

def queueConsoleServerOutput (runtime : ConsoleServerRuntime)
    (byteValue : UInt32) : QueueConsoleServerOutputResult :=
  let rec go (clients : List ConsoleClientRuntime) :
      List ConsoleClientRuntime × List ConsoleClientId :=
    match clients with
    | [] => ([], [])
    | clientState :: rest =>
        let (restClients, restDropped) := go rest
        match queueConsoleClientOutput clientState byteValue with
        | some queuedClient => (queuedClient :: restClients, restDropped)
        | none => (restClients, clientState.id :: restDropped)
  let (clients, droppedClientIds) := go runtime.clients
  { runtime := { clients := clients }, droppedClientIds := droppedClientIds }

end Microvmm