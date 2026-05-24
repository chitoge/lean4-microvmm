import Microvmm.FFI
import Microvmm.Kvm.Resource

namespace Microvmm

open Kvm

private def defaultHostWakeTimerIntervalUsec : UInt32 := 20000

def enableHostWakeTimer (intervalUsec : UInt32 := defaultHostWakeTimerIntervalUsec) :
    IO (Result Unit) := do
  pure <| decodeUnitStatus .enableHostWakeTimer (← FFI.hostEnableWakeTimerRaw intervalUsec)

def disableHostWakeTimer : IO (Result Unit) := do
  pure <| decodeUnitStatus .disableHostWakeTimer (← FFI.hostDisableWakeTimerRaw 0)

def withHostWakeTimer {α : Type} (body : IO (Result α)) : IO (Result α) := do
  match ← enableHostWakeTimer with
  | .error err =>
      pure (.error err)
  | .ok () =>
      withCleanup body disableHostWakeTimer

end Microvmm