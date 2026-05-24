import Microvmm.Guest.Linux.Console

namespace Microvmm

/-- Probe readiness is latched after the first matching marker, so later transcript bytes cannot
clear the pure readiness witness even when only a suffix is retained. -/
theorem captureSerialOutputByte_probeReady_monotone (console : SerialConsole)
    (byteValue : UInt32) :
    console.protocol.probeReady = true ->
      (captureSerialOutputByte console byteValue).protocol.probeReady = true := by
  intro hReady
  unfold captureSerialOutputByte
  exact observeSerialProtocolByte_probeReady_monotone console.protocol byteValue hReady

/-- Interactive readiness uses the same latched protocol bit, which keeps the initrd handoff proof
stable after suffix truncation drops older transcript bytes. -/
theorem captureSerialOutputByte_interactiveReady_monotone (console : SerialConsole)
    (byteValue : UInt32) :
    console.protocol.interactiveReady = true ->
      (captureSerialOutputByte console byteValue).protocol.interactiveReady = true := by
  intro hReady
  unfold captureSerialOutputByte
  exact observeSerialProtocolByte_interactiveReady_monotone console.protocol byteValue hReady

end Microvmm