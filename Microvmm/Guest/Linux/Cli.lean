import Microvmm.Host
import Microvmm.Outcome

namespace Microvmm

def defaultLinuxKernelPath : System.FilePath := "test-bzImage2"

def defaultLinuxBootCommandLine : String :=
  "console=ttyS0,115200 earlyprintk=serial,ttyS0,115200 ignore_loglevel nokaslr"

private def defaultInteractiveLinuxBootCommandLine : String :=
  defaultLinuxBootCommandLine

inductive ConsoleTransportSelection where
  | stdio
  | server
deriving Repr, DecidableEq

/-- Preserve whether `--cmdline` was omitted so later policy does not depend on string equality. -/
inductive LinuxCommandLineSpec where
  | implicitDefault
  | explicit (value : String)
deriving Repr, DecidableEq

structure RawLinuxBootArgs where
  kernelPath : System.FilePath := defaultLinuxKernelPath
  commandLineSpec : LinuxCommandLineSpec := .implicitDefault
  initrdPath? : Option System.FilePath := none
  interactive : Bool := false
  consoleTransport? : Option ConsoleTransportSelection := none
  consoleSocketPath? : Option System.FilePath := none
  serialLogPath? : Option System.FilePath := none
deriving Repr, DecidableEq

structure LinuxProbeRequest where
  kernelPath : System.FilePath := defaultLinuxKernelPath
  commandLineSpec : LinuxCommandLineSpec := .implicitDefault
  initrdPath? : Option System.FilePath := none
deriving Repr, DecidableEq

structure LinuxInteractiveRequest where
  kernelPath : System.FilePath := defaultLinuxKernelPath
  commandLineSpec : LinuxCommandLineSpec := .implicitDefault
  initrdPath : System.FilePath
  consoleMode : InteractiveConsoleMode
deriving Repr, DecidableEq

/-- Invalid probe/interactive combinations are pushed out before the runtime path sees them. -/
inductive LinuxBootRequest where
  | probe (request : LinuxProbeRequest)
  | interactive (request : LinuxInteractiveRequest)
deriving Repr, DecidableEq

private def resolveLinuxCommandLine (commandLineSpec : LinuxCommandLineSpec)
    (mode? : Option InteractiveConsoleMode := none) : String :=
  match commandLineSpec with
  | .explicit value => value
  | .implicitDefault =>
      match mode? with
      | some .stdio =>
          defaultInteractiveLinuxBootCommandLine
      | some (.server _) | none =>
          defaultLinuxBootCommandLine

def LinuxProbeRequest.commandLine (request : LinuxProbeRequest) : String :=
  resolveLinuxCommandLine request.commandLineSpec

def LinuxInteractiveRequest.commandLine (request : LinuxInteractiveRequest) : String :=
  resolveLinuxCommandLine request.commandLineSpec request.consoleMode

private def mapOutcomeError {ε ε' α : Type}
    (f : ε → ε') : Outcome ε α → Outcome ε' α
  | .error err => .error (f err)
  | .ok value => .ok value

/-- Pure CLI/config validation stays typed so later lemmas can name the exact rejected shape.
The outer CLI entry points still render the established strings through
`linuxCliErrorMessage`, while host/runtime failures remain in `Kvm.Error`. -/
inductive LinuxCliError where
  | kernelPathMissing
  | kernelPathEmpty
  | initrdPathMissing
  | initrdPathEmpty
  | commandLineMissing
  | commandLineEmpty
  | consoleTransportMissing
  | invalidConsoleTransport (value : String)
  | consoleSocketMissing
  | consoleSocketEmpty
  | serialLogMissing
  | serialLogEmpty
  | unknownOption (option : String)
  | interactiveRequiresInitrd
  | consoleTransportRequiresInteractive
  | serverOptionsRequireInteractive
  | serverModeRequiresSocketAndSerialLog
  | stdioTransportRejectsServerOptions
deriving Repr, DecidableEq

def linuxCliErrorMessage : LinuxCliError → String
  | .kernelPathMissing => "linux option --kernel requires a path"
  | .kernelPathEmpty => "linux option --kernel requires a non-empty path"
  | .initrdPathMissing => "linux option --initrd requires a path"
  | .initrdPathEmpty => "linux option --initrd requires a non-empty path"
  | .commandLineMissing => "linux option --cmdline requires a value"
  | .commandLineEmpty => "linux option --cmdline requires a non-empty value"
  | .consoleTransportMissing => "linux option --console-transport requires stdio or server"
  | .invalidConsoleTransport _ => "linux option --console-transport expects stdio or server"
  | .consoleSocketMissing => "linux option --console-socket requires a path"
  | .consoleSocketEmpty => "linux option --console-socket requires a non-empty path"
  | .serialLogMissing => "linux option --serial-log requires a path"
  | .serialLogEmpty => "linux option --serial-log requires a non-empty path"
  | .unknownOption option => s!"unknown linux option: {option}"
  | .interactiveRequiresInitrd => "linux option --interactive requires --initrd PATH"
  | .consoleTransportRequiresInteractive =>
      "linux option --console-transport requires --interactive"
  | .serverOptionsRequireInteractive =>
      "linux options --console-socket PATH and --serial-log PATH require --interactive"
  | .serverModeRequiresSocketAndSerialLog =>
      "linux interactive server mode requires both --console-socket PATH and --serial-log PATH"
  | .stdioTransportRejectsServerOptions =>
      "linux stdio console transport does not accept --console-socket PATH or --serial-log PATH"

def linuxUsage : String :=
  "usage: microvmm linux [--kernel PATH] [--initrd PATH] [--cmdline TEXT] [--interactive] [--console-transport stdio|server] [--console-socket PATH] [--serial-log PATH]"

private def parseConsoleTransportSelectionTyped (value : String) :
    Outcome LinuxCliError ConsoleTransportSelection :=
  match value with
  | "stdio" => .ok .stdio
  | "server" => .ok .server
  | _ => .error (.invalidConsoleTransport value)

private def interactiveConsoleServerConfigTyped
    (consoleSocketPath? serialLogPath? : Option System.FilePath) :
    Outcome LinuxCliError ConsoleServerConfig :=
  match consoleSocketPath?, serialLogPath? with
  | some socketPath, some serialLogPath =>
      .ok { socketPath, serialLogPath }
  | _, _ =>
      .error .serverModeRequiresSocketAndSerialLog

private def elaborateInteractiveConsoleModeTyped (args : RawLinuxBootArgs) :
    Outcome LinuxCliError InteractiveConsoleMode :=
  match args.consoleTransport? with
  | some .stdio =>
      if args.consoleSocketPath?.isSome || args.serialLogPath?.isSome then
        .error .stdioTransportRejectsServerOptions
      else
        .ok .stdio
  | some .server =>
      match interactiveConsoleServerConfigTyped args.consoleSocketPath? args.serialLogPath? with
      | .error err => .error err
      | .ok config => .ok (.server config)
  | none =>
      match args.consoleSocketPath?, args.serialLogPath? with
      | none, none =>
          .ok .stdio
      | _, _ =>
          -- Preserve the existing CLI inference: server-path flags imply server mode once interactive boot is requested.
          match interactiveConsoleServerConfigTyped args.consoleSocketPath? args.serialLogPath? with
          | .error err => .error err
          | .ok config => .ok (.server config)

def elaborateLinuxBootRequestTyped (args : RawLinuxBootArgs) : Outcome LinuxCliError LinuxBootRequest :=
  if args.interactive && args.initrdPath?.isNone then
    .error .interactiveRequiresInitrd
  else if !args.interactive && args.consoleTransport?.isSome then
    .error .consoleTransportRequiresInteractive
  else if !args.interactive &&
      (args.consoleSocketPath?.isSome || args.serialLogPath?.isSome) then
    .error .serverOptionsRequireInteractive
  else if args.interactive then
    match args.initrdPath? with
    | none =>
        .error .interactiveRequiresInitrd
    | some initrdPath =>
        match elaborateInteractiveConsoleModeTyped args with
        | .error err => .error err
        | .ok consoleMode =>
            .ok <| .interactive {
              kernelPath := args.kernelPath
              commandLineSpec := args.commandLineSpec
              initrdPath := initrdPath
              consoleMode := consoleMode
            }
  else
    .ok <| .probe {
      kernelPath := args.kernelPath
      commandLineSpec := args.commandLineSpec
      initrdPath? := args.initrdPath?
    }

def elaborateLinuxBootRequest (args : RawLinuxBootArgs) : Outcome String LinuxBootRequest :=
  mapOutcomeError linuxCliErrorMessage <| elaborateLinuxBootRequestTyped args

def parseRawLinuxArgumentsTyped (request : RawLinuxBootArgs) (args : List String) :
    Outcome LinuxCliError RawLinuxBootArgs :=
  match args with
  | [] =>
      .ok request
  | "--kernel" :: [] =>
      .error .kernelPathMissing
  | "--kernel" :: path :: rest =>
      if path.isEmpty then
        .error .kernelPathEmpty
      else
        parseRawLinuxArgumentsTyped { request with kernelPath := path } rest
  | "--initrd" :: [] =>
      .error .initrdPathMissing
  | "--initrd" :: path :: rest =>
      if path.isEmpty then
        .error .initrdPathEmpty
      else
        parseRawLinuxArgumentsTyped { request with initrdPath? := some path } rest
  | "--cmdline" :: [] =>
      .error .commandLineMissing
  | "--cmdline" :: commandLine :: rest =>
      if commandLine.isEmpty then
        .error .commandLineEmpty
      else
        parseRawLinuxArgumentsTyped { request with commandLineSpec := .explicit commandLine } rest
  | "--console-transport" :: [] =>
      .error .consoleTransportMissing
  | "--console-transport" :: value :: rest =>
      if value.isEmpty then
        .error .consoleTransportMissing
      else
        match parseConsoleTransportSelectionTyped value with
        | .error err => .error err
        | .ok consoleTransport =>
            parseRawLinuxArgumentsTyped { request with consoleTransport? := some consoleTransport } rest
  | "--console-socket" :: [] =>
      .error .consoleSocketMissing
  | "--console-socket" :: path :: rest =>
      if path.isEmpty then
        .error .consoleSocketEmpty
      else
        parseRawLinuxArgumentsTyped { request with consoleSocketPath? := some path } rest
  | "--serial-log" :: [] =>
      .error .serialLogMissing
  | "--serial-log" :: path :: rest =>
      if path.isEmpty then
        .error .serialLogEmpty
      else
        parseRawLinuxArgumentsTyped { request with serialLogPath? := some path } rest
  | "--interactive" :: rest =>
      parseRawLinuxArgumentsTyped { request with interactive := true } rest
  | option :: _ =>
      .error (.unknownOption option)

def parseRawLinuxArguments (request : RawLinuxBootArgs) (args : List String) :
    Outcome String RawLinuxBootArgs :=
  mapOutcomeError linuxCliErrorMessage <| parseRawLinuxArgumentsTyped request args

end Microvmm