import Microvmm

open Microvmm

def main (args : List String) : IO Unit := do
  match args with
  | "linux" :: linuxArgs =>
      match parseRawLinuxArguments {} linuxArgs with
      | .error err =>
          throw <| IO.userError s!"{err}\n{linuxUsage}"
      | .ok rawArgs =>
          match elaborateLinuxBootRequest rawArgs with
          | .error err =>
              throw <| IO.userError s!"{err}\n{linuxUsage}"
          | .ok request =>
              match request with
              | .interactive interactiveRequest =>
                  match ← Microvmm.runLinuxInteractiveBoot interactiveRequest with
                  | .ok () => pure ()
                  | .error err => throw <| IO.userError (Microvmm.decodeErrno err)
              | .probe probeRequest =>
                  IO.println (← Microvmm.probeLinuxBzImageMessage probeRequest)
  | _ =>
      IO.println (← Microvmm.probeMessage)