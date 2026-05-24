import Microvmm.Host.SerialModel
import Microvmm.Kvm.Types

namespace Microvmm

open Kvm

structure ConsoleServerConfig where
  socketPath : System.FilePath
  serialLogPath : System.FilePath
deriving Repr, DecidableEq

structure ConsoleListener where
  fd : UInt32
deriving Repr, DecidableEq

structure ConsoleClient where
  fd : UInt32
deriving Repr, DecidableEq

abbrev ConsoleClientId := Nat

structure ConsoleClientHandle where
  id : ConsoleClientId
  client : ConsoleClient
deriving Repr, DecidableEq

instance : HasRawFd ConsoleListener := ⟨ConsoleListener.fd⟩

instance : HasRawFd ConsoleClient := ⟨ConsoleClient.fd⟩

structure ConsoleClientRuntime where
  id : ConsoleClientId
  pendingOutput : List UInt32 := []
deriving Repr, DecidableEq

structure ConsoleServerRuntime where
  clients : List ConsoleClientRuntime := []
deriving Repr, DecidableEq

structure ConsoleServerHostState where
  config : ConsoleServerConfig
  listener : ConsoleListener
  serialLog : IO.FS.Handle
  nextClientId : ConsoleClientId := 0
  clients : List ConsoleClientHandle := []

structure ConsoleServerState where
  host : ConsoleServerHostState
  runtime : ConsoleServerRuntime := {}

inductive InteractiveConsoleMode where
  | stdio
  | server (config : ConsoleServerConfig)
deriving Repr, DecidableEq

inductive InteractiveConsoleTransport where
  | stdio
  | server (state : ConsoleServerState)

inductive ConsoleClientRead where
  | noData
  | disconnected
  | byte (value : UInt32)
deriving Repr, DecidableEq

inductive ConsoleClientWrite where
  | sent
  | blocked
  | disconnected
deriving Repr, DecidableEq

def consoleClientOutputCapacity : Nat := 16384

end Microvmm