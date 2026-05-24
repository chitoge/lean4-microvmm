import Microvmm.Guest.Linux.Cli
import Microvmm.Guest.Linux.Console
import Microvmm.Guest.Linux.Image
import Microvmm.Guest.Linux.Plan
import Microvmm.Guest.Linux.Platform
import Microvmm.Host
import Microvmm.Kvm
import Microvmm.Kvm.VcpuSetup

namespace Microvmm

open Kvm

private structure LinuxBootConfig where
  kernelPath : System.FilePath
  commandLine : String
  initrdPath? : Option System.FilePath := none

private def LinuxProbeRequest.bootConfig (request : LinuxProbeRequest) : LinuxBootConfig :=
  {
    kernelPath := request.kernelPath
    commandLine := request.commandLine
    initrdPath? := request.initrdPath?
  }

private def LinuxInteractiveRequest.bootConfig (request : LinuxInteractiveRequest) : LinuxBootConfig :=
  {
    kernelPath := request.kernelPath
    commandLine := request.commandLine
    initrdPath? := some request.initrdPath
  }

private def tssAddr : GuestPhysAddr := ⟨0xfffbd000⟩

private def linuxMaxKvmExits : Nat := 200000

private def interactiveLinuxMaxKvmExits : Nat := 5000000

private def kvmExitIo : UInt32 := 2

private def kvmExitHlt : UInt32 := 5

private def kvmExitMmio : UInt32 := 6

private def kvmExitShutdown : UInt32 := 8

def linuxRuntimeKvmExitIo : UInt32 := kvmExitIo

def linuxRuntimeKvmExitHlt : UInt32 := kvmExitHlt

def linuxRuntimeKvmExitMmio : UInt32 := kvmExitMmio

def linuxRuntimeKvmExitShutdown : UInt32 := kvmExitShutdown

private def pushU16LE (bytes : ByteArray) (value : UInt32) : ByteArray :=
  bytes.push (UInt8.ofNat (value.toNat % 256))
    |>.push (UInt8.ofNat ((value.toNat / 256) % 256))

private def pushU32LE (bytes : ByteArray) (value : UInt32) : ByteArray :=
  (((pushU16LE bytes value) |>.push (UInt8.ofNat ((value.toNat / 65536) % 256)))
    |>.push (UInt8.ofNat ((value.toNat / 16777216) % 256)))

private def pushU64LE (bytes : ByteArray) (value : UInt64) : ByteArray :=
  pushU32LE (pushU32LE bytes (low32 value)) (high32 value)

private def mkGdtEntryBytes (base : UInt32) (limit : UInt32) (access : UInt32)
    (flags : UInt32) : ByteArray :=
  let granularity : UInt32 := UInt32.ofNat ((limit.toNat / 65536) % 16) ||| (flags &&& 0xf0)
  let bytes0 := pushU16LE ByteArray.empty (limit &&& 0xffff)
  let bytes1 := pushU16LE bytes0 (base &&& 0xffff)
  let bytes2 := bytes1.push (UInt8.ofNat ((base.toNat / 65536) % 256))
  let bytes3 := bytes2.push (UInt8.ofNat access.toNat)
  let bytes4 := bytes3.push (UInt8.ofNat granularity.toNat)
  bytes4.push (UInt8.ofNat ((base.toNat / 16777216) % 256))

private def mkE820EntryBytes (addr size : UInt64) (typ : UInt32) : ByteArray :=
  pushU32LE (pushU64LE (pushU64LE ByteArray.empty addr) size) typ

private def applyLinuxBootWrite (guestMemory : GuestMemory)
    (write : LinuxBootWrite) : IO (Result Unit) := do
  match write.payload with
  | .bytes bytes =>
      guestWriteByteArray .loadGuestCode guestMemory write.addr.value bytes
  | .u8 value =>
      guestWriteU8 .loadGuestCode guestMemory write.addr.value value
  | .u16 value =>
      guestWriteU16 .loadGuestCode guestMemory write.addr.value value
  | .u32 value =>
      guestWriteU32 .loadGuestCode guestMemory write.addr.value value
  | .e820Entry regionAddr regionSize typ =>
      guestWriteByteArray .loadGuestCode guestMemory write.addr.value
        (mkE820EntryBytes regionAddr regionSize typ)
  | .gdtEntry base limit access flags =>
      guestWriteByteArray .loadGuestCode guestMemory write.addr.value
        (mkGdtEntryBytes base limit access flags)

private def applyLinuxBootWrites (guestMemory : GuestMemory) :
    List LinuxBootWrite → IO (Result Unit)
  | [] =>
      pure (.ok ())
  | write :: remaining =>
      bindIOResult (applyLinuxBootWrite guestMemory write) fun _ =>
        applyLinuxBootWrites guestMemory remaining

private def applyLinuxBootPlan (guestMemory : GuestMemory)
    (plan : LinuxBootPlan) : IO (Result Unit) := do
  applyLinuxBootWrites guestMemory plan.writes

private def prepareLinuxGuest (guestMemory : GuestMemory) (imageBytes : ByteArray)
    (layout : BzImageLayout) (bootInputs : LinuxBootInputs) : IO (Result Unit) := do
  let plan := buildLinuxBootPlan imageBytes layout bootInputs
  applyLinuxBootPlan guestMemory plan

private def readLinuxBzImage (kernelPath : System.FilePath) : IO (Result ByteArray) := do
  match ← readHostBinaryFile kernelPath .openKernelImage .readKernelImage with
  | .error err =>
      pure (.error err)
  | .ok bytes =>
      if bytes.size == 0 then
        pure (.error ⟨.readKernelImage, eproto⟩)
      else
        pure (.ok bytes)

private def readLinuxInitramfs (initrdPath? : Option System.FilePath) : IO (Result (Option ByteArray)) := do
  match ← readHostOptionalBinaryFile initrdPath? .openInitrdImage .readInitrdImage with
  | .error err =>
      pure (.error err)
  | .ok none =>
      pure (.ok none)
  | .ok (some bytes) =>
      if bytes.size == 0 then
        pure (.error ⟨.readInitrdImage, eproto⟩)
      else
        pure (.ok (some bytes))

private def configureLinuxVm (vm : Vm) : IO (Result Unit) := do
  match ← createIrqChip vm with
  | .error err =>
      pure (.error err)
  | .ok () =>
      match ← createPit2 vm with
      | .error err =>
          pure (.error err)
      | .ok () =>
          setTssAddr vm tssAddr

private def configureLinuxBzImageVcpu (vcpuContext : VcpuContext) : IO (Result Unit) := do
  match ← configureCpuid vcpuContext.kvm vcpuContext.vcpu with
  | .error err =>
      pure (.error err)
  | .ok () =>
      configureProtectedModeVcpu vcpuContext.vcpu kernelLoadAddr bootParamsAddr

private def withPreparedLinuxGuest {α : Type} (request : LinuxBootConfig)
    (body : VcpuContext → GuestMemory → RunArea → IO (Result α)) : IO (Result α) := do
  withVmContext fun vmContext =>
    bindIOResult (readLinuxBzImage request.kernelPath) fun imageBytes =>
      match parseBzImageLayout imageBytes with
      | .error err =>
          pure (.error err)
      | .ok layout =>
          bindIOResult (readLinuxInitramfs request.initrdPath?) fun initramfsBytes? =>
            match validateLinuxBootInputs layout request.commandLine initramfsBytes? with
            | .error err =>
                pure (.error err)
            | .ok bootInputs =>
                bindIOResult (configureLinuxVm vmContext.vm) fun _ =>
                  withVcpuContext vmContext defaultVcpuId fun vcpuContext =>
                    withGuestMemory linuxGuestMemorySize fun guestMemory =>
                      bindIOResult (prepareLinuxGuest guestMemory imageBytes layout bootInputs) fun _ =>
                        withRegisteredGuestMemory vcpuContext.vm 0 0 guestMemory do
                          bindIOResult (configureLinuxBzImageVcpu vcpuContext) fun _ =>
                            withMappedRunArea vcpuContext.vcpu vcpuContext.runAreaSize fun runArea =>
                              body vcpuContext guestMemory runArea

def runLinuxSerialLoop (remaining : Nat) (vm : Vm) (vcpu : Vcpu) (runArea : RunArea)
    (guestMemory : GuestMemory) (state : LinuxPlatformState) : IO (Result String) := do
  match remaining with
  | 0 =>
      pure (.error ⟨.verifyTranscript, etimedout⟩)
  | remaining + 1 =>
      match ← runGuestOnce vcpu with
      | .error err =>
          pure (.error err)
      | .ok () =>
          let exitReason ← runExitReason runArea
          if exitReason == kvmExitIo then
            match ← handleLinuxIoExit vm runArea state with
            | .error err =>
                pure (.error err)
            | .ok step =>
                if step.ready then
                  pure (.ok (buildTranscriptExcerpt step.state.console.replay))
                else
                  runLinuxSerialLoop remaining vm vcpu runArea guestMemory step.state
          else if exitReason == kvmExitMmio then
            match ← handleLinuxMmioExit vm runArea guestMemory state with
            | .error err =>
                pure (.error err)
            | .ok nextState =>
                runLinuxSerialLoop remaining vm vcpu runArea guestMemory nextState
          else if exitReason == kvmExitHlt then
            pure (.error ⟨.verifyTranscript, eproto⟩)
          else
            pure (.error ⟨.verifyIoExit, eproto⟩)

structure InteractiveRunState where
  platform : LinuxPlatformState
  transport : InteractiveConsoleTransport

structure InteractiveRunOutcome where
  state : InteractiveRunState
  session : Result Unit

def serviceInteractiveTransport (vm : Vm) (state : InteractiveRunState) :
    IO (Result InteractiveRunState) := do
  let ready := interactiveTransportReady state.platform.console
  bindIOResult (pollInteractiveTransportInput state.platform.console state.transport) fun
    | (queuedConsole, nextTransport) =>
        bindIOResult
          (if ready && shouldPulseCom1RxIrq state.platform.console.uart queuedConsole.uart then
            pulseCom1Irq vm
          else
            pure (.ok ())) fun _ =>
          let nextPlatform := { state.platform with console := queuedConsole }
          pure (.ok { state with platform := nextPlatform, transport := nextTransport })

def runLinuxInteractiveLoop (remaining : Nat) (vm : Vm) (vcpu : Vcpu) (runArea : RunArea)
    (guestMemory : GuestMemory) (state : InteractiveRunState) : IO InteractiveRunOutcome := do
  match remaining with
  | 0 =>
      pure { state, session := .error ⟨.verifyInteractiveSession, etimedout⟩ }
  | remaining + 1 =>
      match ← serviceInteractiveTransport vm state with
      | .error err =>
          pure { state, session := .error err }
      | .ok queuedState =>
          match ← runGuestOnce vcpu with
          | .error err =>
              if err.errno == 4 then
                runLinuxInteractiveLoop remaining vm vcpu runArea guestMemory queuedState
              else
                pure { state := queuedState, session := .error err }
          | .ok () =>
              let exitReason ← runExitReason runArea
              if exitReason == kvmExitIo then
                match ← handleLinuxIoExit vm runArea queuedState.platform with
                | .error err =>
                    pure { state := queuedState, session := .error err }
                | .ok step =>
                    let nextState := { queuedState with platform := step.state }
                    match ← emitInteractiveOutputByte queuedState.transport step.outputByte? with
                    | .error err =>
                        pure { state := nextState, session := .error err }
                    | .ok nextTransport =>
                        runLinuxInteractiveLoop remaining vm vcpu runArea guestMemory
                          { nextState with transport := nextTransport }
              else if exitReason == kvmExitMmio then
                match ← handleLinuxMmioExit vm runArea guestMemory queuedState.platform with
                | .error err =>
                    pure { state := queuedState, session := .error err }
                | .ok nextPlatform =>
                    runLinuxInteractiveLoop remaining vm vcpu runArea guestMemory
                      { queuedState with platform := nextPlatform }
              else if exitReason == kvmExitHlt || exitReason == kvmExitShutdown then
                if interactiveTransportReady queuedState.platform.console then
                  pure { state := queuedState, session := .ok () }
                else
                  pure { state := queuedState, session := .error ⟨.verifyInteractiveSession, eproto⟩ }
              else
                pure { state := queuedState, session := .error ⟨.verifyIoExit, eproto⟩ }

def probeLinuxBzImageBoot (request : LinuxProbeRequest := {}) : IO (Result ProbeSuccess) := do
  withPreparedLinuxGuest request.bootConfig fun vcpuContext guestMemory runArea =>
    mapIOResult
      (runLinuxSerialLoop linuxMaxKvmExits vcpuContext.vm vcpuContext.vcpu runArea
        guestMemory initialLinuxPlatformState)
      fun transcriptExcerpt =>
      ⟨vcpuContext.apiVersion, vcpuContext.runAreaSize, transcriptExcerpt⟩

private def runLinuxInteractiveSession (request : LinuxInteractiveRequest)
    (transport : InteractiveConsoleTransport) : IO (Result Unit) := do
  let initialState : InteractiveRunState :=
    { platform := initialLinuxPlatformState, transport := transport }
  let sessionResult ← withHostWakeTimer do
    withPreparedLinuxGuest request.bootConfig fun vcpuContext guestMemory runArea => do
      let outcome ← runLinuxInteractiveLoop interactiveLinuxMaxKvmExits
        vcpuContext.vm vcpuContext.vcpu runArea guestMemory initialState
      pure (.ok outcome)
  match sessionResult with
  | .error err =>
      let cleanupResult ← cleanupInteractiveConsoleTransport transport
      pure <| preferPrimary (.error err) cleanupResult
  | .ok outcome =>
      let cleanupResult ← cleanupInteractiveConsoleTransport outcome.state.transport
      pure <| preferPrimary outcome.session cleanupResult

def runLinuxInteractiveBoot (request : LinuxInteractiveRequest) : IO (Result Unit) := do
  match request.consoleMode with
  | .stdio =>
      runLinuxInteractiveSession request .stdio
  | .server config =>
      match ← openConsoleListener config.socketPath with
      | .error err =>
          pure (.error err)
      | .ok listener =>
          match ← openSerialLogHandle config.serialLogPath with
          | .error err =>
              let cleanupResult ← cleanupConsoleListener config listener
              pure <| preferPrimary (.error err) cleanupResult
          | .ok serialLog =>
              let initialTransport : InteractiveConsoleTransport :=
                .server { host := { config, listener, serialLog }, runtime := {} }
              let startupResult ←
                bindIOResult (writeHostStderrLine s!"microvmm: console socket {config.socketPath}") fun _ =>
                  writeHostStderrLine s!"microvmm: serial log {config.serialLogPath}"
              match startupResult with
              | .error err =>
                  let cleanupResult ← cleanupInteractiveConsoleTransport initialTransport
                  pure <| preferPrimary (.error err) cleanupResult
              | .ok () =>
                  runLinuxInteractiveSession request initialTransport

end Microvmm