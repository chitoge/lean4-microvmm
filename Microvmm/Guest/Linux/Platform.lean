import Microvmm.Bus.Platform
import Microvmm.Device.Virtio.Rng
import Microvmm.Guest.Linux.Console
import Microvmm.Kvm
import Microvmm.VirtioPci

namespace Microvmm

open Kvm

private def com1IrqLine : UInt32 := 4

private def linuxVirtioPciInterruptLine : UInt32 := 10

/-- Probe and interactive Linux boots share one guest-visible platform state so early PCI config
enumeration and later BAR-backed queue completion observe the same pure transport history. -/
structure LinuxPlatformState where
  console : SerialConsole
  bus : PlatformBusState

def initialLinuxPlatformState : LinuxPlatformState :=
  {
    console := {}
    bus := initialPlatformBusState linuxVirtioPciInterruptLine
  }

def pulseIrqLine (vm : Vm) (irqLine : UInt32) : IO (Result Unit) := do
  bindIOResult (setIrqLine vm irqLine 1) fun _ =>
    setIrqLine vm irqLine 0

def pulseCom1Irq (vm : Vm) : IO (Result Unit) :=
  pulseIrqLine vm com1IrqLine

private def handleSerialIoExit (vm : Vm) (runArea : RunArea) (console : SerialConsole) :
    IO (Result SerialStep) := do
  match ← readIoAccess runArea with
  | .error err =>
      pure (.error err)
  | .ok access =>
      match stepSerialConsole console access with
      | .error err =>
          pure (.error err)
      | .ok step =>
          let responseResult ←
            match step.response with
            | some response => setRunIoData runArea access.width access.count response
            | none => pure (.ok ())
          match responseResult with
          | .error err => pure (.error err)
          | .ok () =>
              if shouldPulseCom1TxIrq access step.console.uart then
                bindIOResult (pulseCom1Irq vm) fun _ =>
                  pure (.ok step)
              else
                pure (.ok step)

structure LinuxIoExitStep where
  state : LinuxPlatformState
  outputByte? : Option UInt32 := none
  ready : Bool := false

private def handleLinuxPciConfigIoExit (runArea : RunArea) (state : LinuxPlatformState)
    (access : IoAccess) : IO (Result LinuxPlatformState) := do
  if access.count != 1 then
    pure (.error ⟨.verifyIoExit, eproto⟩)
  else
    match access.direction with
    | .input =>
        match virtioPciPortRead state.bus.virtioPci access.port access.width with
        | .error errno =>
            pure (.error ⟨.verifyIoExit, errno⟩)
        | .ok (nextPci, response) =>
            bindIOResult (setRunIoData runArea access.width access.count response) fun _ =>
              pure (.ok { state with bus := { state.bus with virtioPci := nextPci } })
    | .output =>
        match virtioPciPortWrite state.bus.virtioPci access.port access.width access.value with
        | .error errno =>
            pure (.error ⟨.verifyIoExit, errno⟩)
        | .ok nextPci =>
            pure (.ok { state with bus := { state.bus with virtioPci := nextPci } })

def handleLinuxIoExit (vm : Vm) (runArea : RunArea) (state : LinuxPlatformState) :
    IO (Result LinuxIoExitStep) := do
  match ← readIoAccess runArea with
  | .error err =>
      pure (.error err)
  | .ok access =>
      match routePlatformIoAccess access with
      | .pciConfig _ =>
          mapIOResult (handleLinuxPciConfigIoExit runArea state access) fun nextState =>
            { state := nextState }
      | .passive =>
          match ← handleSerialIoExit vm runArea state.console with
          | .error err =>
              pure (.error err)
          | .ok step =>
              pure (.ok {
                state := { state with console := step.console }
                outputByte? := step.outputByte?
                ready := step.ready
              })

private def handlePassiveLinuxMmioAccess (runArea : RunArea) (access : MmioAccess) :
    IO (Result Unit) := do
  match stepPassiveLinuxMmioTyped access with
  | .error err =>
      pure (.error (linuxConsoleErrorToKvmError err))
  | .ok response? =>
      match response? with
      | some response =>
          match ← setRunMmioDataU32 runArea response with
          | .error err => pure (.error err)
          | .ok () => pure (.ok ())
      | none => pure (.ok ())

def handleLinuxVirtioPciBarAction (vm : Vm) (guestMemory : GuestMemory)
    (transport : VirtioPciState) (action : MmioWriteAction) : IO (Result VirtioPciState) := do
  match action with
  | .none =>
      pure (.ok transport)
  | .processQueue =>
      bindIOResult (completeDeterministicEntropyRequest guestMemory transport.device) fun nextDevice =>
        let nextTransport := { transport with device := nextDevice }
        bindIOResult (pulseIrqLine vm nextTransport.interruptLine) fun _ =>
          pure (.ok nextTransport)

def handleLinuxVirtioPciBarAccess (vm : Vm) (runArea : RunArea)
    (guestMemory : GuestMemory) (state : LinuxPlatformState) (access : MmioAccess) :
    IO (Result LinuxPlatformState) := do
  match access.direction with
  | .read =>
      match virtioPciBarRead state.bus.virtioPci access.address access.width with
      | .error errno =>
          pure (.error ⟨.verifyMmioExit, errno⟩)
      | .ok (nextPci, response) =>
          bindIOResult (setRunMmioDataU32 runArea response) fun _ =>
            pure (.ok { state with bus := { state.bus with virtioPci := nextPci } })
  | .write =>
      match virtioPciBarWrite state.bus.virtioPci access.address access.width access.value with
      | .error errno =>
          pure (.error ⟨.verifyMmioExit, errno⟩)
      | .ok (nextPci, action) =>
          mapIOResult (handleLinuxVirtioPciBarAction vm guestMemory nextPci action) fun finalPci =>
            { state with bus := { state.bus with virtioPci := finalPci } }

def handleLinuxMmioAccess (vm : Vm) (runArea : RunArea) (guestMemory : GuestMemory)
    (state : LinuxPlatformState) (access : MmioAccess) : IO (Result LinuxPlatformState) := do
  match routePlatformMmioAccess state.bus.virtioPci access with
  | .virtioPciBar =>
      handleLinuxVirtioPciBarAccess vm runArea guestMemory state access
  | .passiveLapic =>
      bindIOResult (handlePassiveLinuxMmioAccess runArea access) fun _ =>
        pure (.ok state)

def handleLinuxMmioExit (vm : Vm) (runArea : RunArea) (guestMemory : GuestMemory)
    (state : LinuxPlatformState) : IO (Result LinuxPlatformState) := do
  let access ← readMmioAccess runArea
  handleLinuxMmioAccess vm runArea guestMemory state access

end Microvmm
