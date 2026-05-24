import Microvmm.FFI
import Microvmm.Host.ConsoleTypes
import Microvmm.Host.Socket
import Microvmm.Kvm.Resource

namespace Microvmm

open Kvm

private def closeWithStage {α : Type} [HasRawFd α] (stage : Stage) (handle : α) : IO (Result Unit) :=
  do pure <| decodeUnitStatus stage (← FFI.kvmCloseRaw (HasRawFd.rawFd handle))

def closeConsoleListener (listener : ConsoleListener) : IO (Result Unit) := do
  closeWithStage .closeConsoleListener listener

def closeConsoleClient (client : ConsoleClient) : IO (Result Unit) := do
  closeWithStage .closeConsoleClient client

def closeConsoleClientQuietly (client : ConsoleClient) : IO Unit := do
  let _ ← closeConsoleClient client
  pure ()

def cleanupConsoleListener (config : ConsoleServerConfig) (listener : ConsoleListener) :
    IO (Result Unit) := do
  let closeResult ← closeConsoleListener listener
  let unlinkResult ← unlinkConsoleSocketPath config.socketPath
  pure <| preferPrimary closeResult unlinkResult

private def closeConsoleClientHandles (clients : List ConsoleClientHandle) : IO (Result Unit) := do
  match clients with
  | [] => pure (.ok ())
  | clientHandle :: rest =>
      let closeResult ← closeConsoleClient clientHandle.client
      let restResult ← closeConsoleClientHandles rest
      pure <| preferPrimary closeResult restResult

def cleanupConsoleServerState (serverState : ConsoleServerState) : IO (Result Unit) := do
  let clientsResult ← closeConsoleClientHandles serverState.host.clients
  let listenerResult ← cleanupConsoleListener serverState.host.config serverState.host.listener
  pure <| preferPrimary clientsResult listenerResult

def cleanupInteractiveConsoleTransport (transport : InteractiveConsoleTransport) :
    IO (Result Unit) := do
  match transport with
  | .stdio => pure (.ok ())
  | .server serverState => cleanupConsoleServerState serverState

end Microvmm