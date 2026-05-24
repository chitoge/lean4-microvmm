import Microvmm.FFI
import Microvmm.Kvm.Resource

namespace Microvmm

open Kvm

private def errnoOfStatus (status : Int32) : UInt32 :=
  UInt32.ofNat status.toInt.natAbs

private def normalizeByte (byteValue : UInt32) : UInt32 :=
  byteValue &&& 0xff

private def byteArrayOfByte (byteValue : UInt32) : ByteArray :=
  ByteArray.empty.push (UInt8.ofNat (normalizeByte byteValue).toNat)

def readHostStdinByteNonblocking : IO (Result (Option UInt32)) := do
  let status ← FFI.hostStdinReadU8NonblockingRaw 0
  if status.toInt < 0 then
    pure (.error ⟨.pollHostStdin, errnoOfStatus status⟩)
  else
    let value := status.toInt.toNat
    if value == 0 then
      pure (.ok none)
    else
      pure (.ok (some (normalizeByte (UInt32.ofNat (value - 1)))))

def writeHostStdoutByte (byteValue : UInt32) : IO (Result Unit) := do
  let status ← FFI.hostStdoutWriteU8Raw (normalizeByte byteValue)
  if status.toInt < 0 then
    pure (.error ⟨.writeHostStdout, errnoOfStatus status⟩)
  else
    pure (.ok ())

def openSerialLogHandle (path : System.FilePath) : IO (Result IO.FS.Handle) := do
  try
    pure (.ok (← IO.FS.Handle.mk path .write))
  catch _ =>
    pure (.error ⟨.openSerialLog, 5⟩)

def writeSerialLogByte (serialLog : IO.FS.Handle) (byteValue : UInt32) : IO (Result Unit) := do
  try
    serialLog.write (byteArrayOfByte byteValue)
    serialLog.flush
    pure (.ok ())
  catch _ =>
    pure (.error ⟨.writeSerialLog, 5⟩)

def writeHostStderrLine (message : String) : IO (Result Unit) := do
  try
    let stderr ← IO.getStderr
    stderr.putStr (message.push '\n')
    stderr.flush
    pure (.ok ())
  catch _ =>
    pure (.error ⟨.writeHostStderr, 5⟩)

private def pathExistsResult (path : System.FilePath) (stage : Stage) : IO (Result Bool) := do
  try
    pure (.ok (← path.pathExists))
  catch _ =>
    pure (.error ⟨stage, 5⟩)

def readHostBinaryFile (path : System.FilePath) (openStage readStage : Stage) :
    IO (Result ByteArray) := do
  match ← pathExistsResult path openStage with
  | .error err =>
      pure (.error err)
  | .ok false =>
      pure (.error ⟨openStage, 2⟩)
  | .ok true =>
      try
        pure (.ok (← IO.FS.readBinFile path))
      catch _ =>
        pure (.error ⟨readStage, 5⟩)

def readHostOptionalBinaryFile (path? : Option System.FilePath) (openStage readStage : Stage) :
    IO (Result (Option ByteArray)) := do
  match path? with
  | none =>
      pure (.ok none)
  | some path =>
      mapIOResult (readHostBinaryFile path openStage readStage) some

end Microvmm
