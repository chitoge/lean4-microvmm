import Microvmm.FFI
import Microvmm.Host.ConsoleTypes
import Microvmm.Kvm.Resource

namespace Microvmm

open Kvm

private def errnoOfStatus (status : Int32) : UInt32 :=
  UInt32.ofNat status.toInt.natAbs

private def normalizeByte (byteValue : UInt32) : UInt32 :=
  byteValue &&& 0xff

private def eagain : UInt32 := 11

private def epipe : UInt32 := 32

private def econnreset : UInt32 := 104

private def enotconn : UInt32 := 107

def openConsoleListener (path : System.FilePath) : IO (Result ConsoleListener) := do
  pure <| (decodeValueStatus .openConsoleListener (← FFI.hostUnixListenerOpenRaw path.toString)).map
    ConsoleListener.mk

def acceptConsoleClientNonblocking (listener : ConsoleListener) : IO (Result (Option ConsoleClient)) := do
  let status ← FFI.hostUnixListenerAcceptNonblockingRaw listener.fd
  if status.toInt < 0 then
    pure (.error ⟨.acceptConsoleClient, errnoOfStatus status⟩)
  else
    let encoded := status.toInt.toNat
    if encoded == 0 then
      pure (.ok none)
    else
      pure (.ok (some ⟨UInt32.ofNat (encoded - 1)⟩))

def readConsoleClientByteNonblocking (client : ConsoleClient) : IO (Result ConsoleClientRead) := do
  let status ← FFI.hostSocketReadU8NonblockingRaw client.fd
  if status.toInt < 0 then
    pure (.error ⟨.readConsoleClient, errnoOfStatus status⟩)
  else
    let encoded := status.toInt.toNat
    if encoded == 0 then
      pure (.ok .noData)
    else if encoded == 257 then
      pure (.ok .disconnected)
    else
      pure (.ok (.byte (normalizeByte (UInt32.ofNat (encoded - 1)))))

def writeConsoleClientByteNonblocking (client : ConsoleClient) (byteValue : UInt32) :
    IO (Result ConsoleClientWrite) := do
  let status ← FFI.hostSocketWriteU8NonblockingRaw client.fd (normalizeByte byteValue)
  if status.toInt < 0 then
    let errno := errnoOfStatus status
    if errno == eagain then
      pure (.ok .blocked)
    else if errno == epipe || errno == econnreset || errno == enotconn then
      pure (.ok .disconnected)
    else
      pure (.error ⟨.writeConsoleClient, errno⟩)
  else
    pure (.ok .sent)

def unlinkConsoleSocketPath (path : System.FilePath) : IO (Result Unit) := do
  pure <| decodeUnitStatus .unlinkConsoleSocket (← FFI.hostUnlinkPathRaw path.toString)

end Microvmm