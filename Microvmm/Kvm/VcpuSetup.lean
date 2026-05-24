import Microvmm.Common

namespace Microvmm

open Kvm

def bootGdtAddr : GuestPhysAddr := ⟨0x5000⟩

private def protectedModeStackPointer : GuestPhysAddr := ⟨0x80000⟩

private def bootCs : UInt32 := 0x10

private def bootDs : UInt32 := 0x18

private def cr0ProtectionEnable : UInt64 := 0x1

private def cr0PagingMask : UInt64 := 0x80000000

private def setFlatSegments (buffer : VcpuStateBuffer) : IO (Result Unit) := do
  let segmentSetters : List (UInt32 × UInt32 × UInt32) := [
    (0, bootCs, UInt32.ofNat 0xb),
    (1, bootDs, UInt32.ofNat 0x3),
    (2, bootDs, UInt32.ofNat 0x3),
    (3, bootDs, UInt32.ofNat 0x3),
    (4, bootDs, UInt32.ofNat 0x3),
    (5, bootDs, UInt32.ofNat 0x3)
  ]
  let rec loop (remaining : List (UInt32 × UInt32 × UInt32)) : IO (Result Unit) := do
    match remaining with
    | [] =>
        pure (.ok ())
    | (slot, selector, typ) :: tail =>
        match ← vcpuStateSetFlatSegment buffer slot selector typ with
        | .error err =>
            pure (.error err)
        | .ok () =>
            loop tail
  loop segmentSetters

def configureProtectedModeVcpu (vcpu : Vcpu) (rip : UInt64) (rsi : UInt64) :
    IO (Result Unit) := do
  match ← allocVcpuStateBuffer with
  | .error err =>
      pure (.error err)
  | .ok buffer =>
      let setupResult ←
        match ← getSregsIntoBuffer vcpu buffer with
        | .error err =>
            pure (.error err)
        | .ok () =>
            let cr0 := ← vcpuStateGetCr0 buffer
            match ← vcpuStateSetGdt buffer bootGdtAddr (UInt32.ofNat (4 * 8 - 1)) with
            | .error err =>
                pure (.error err)
            | .ok () =>
                match ← vcpuStateSetIdt buffer 0 0 with
                | .error err =>
                    pure (.error err)
                | .ok () =>
                    match ← vcpuStateSetCr0 buffer ((cr0 ||| cr0ProtectionEnable) &&& (~~~cr0PagingMask)) with
                    | .error err =>
                        pure (.error err)
                    | .ok () =>
                        match ← vcpuStateSetCr3 buffer 0 with
                        | .error err =>
                            pure (.error err)
                        | .ok () =>
                            match ← vcpuStateSetCr4 buffer 0 with
                            | .error err =>
                                pure (.error err)
                            | .ok () =>
                                match ← vcpuStateSetEfer buffer 0 with
                                | .error err =>
                                    pure (.error err)
                                | .ok () =>
                                    match ← setFlatSegments buffer with
                                    | .error err =>
                                        pure (.error err)
                                    | .ok () =>
                                        match ← setSregsFromBuffer vcpu buffer with
                                        | .error err =>
                                            pure (.error err)
                                        | .ok () =>
                                            match ← vcpuStateClearRegs buffer with
                                            | .error err =>
                                                pure (.error err)
                                            | .ok () =>
                                                match ← vcpuStateSetRip buffer rip with
                                                | .error err =>
                                                    pure (.error err)
                                                | .ok () =>
                                                    match ← vcpuStateSetRsi buffer rsi with
                                                    | .error err =>
                                                        pure (.error err)
                                                    | .ok () =>
                                                        match ← vcpuStateSetRsp buffer protectedModeStackPointer with
                                                        | .error err =>
                                                            pure (.error err)
                                                        | .ok () =>
                                                            match ← vcpuStateSetRflags buffer 0x2 with
                                                            | .error err =>
                                                                pure (.error err)
                                                            | .ok () =>
                                                                setRegsFromBuffer vcpu buffer
      let freeResult ← freeVcpuStateBuffer buffer
      pure <| preferPrimary setupResult freeResult

def configureVirtioMmioEntropyVcpu (vcpuContext : VcpuContext) : IO (Result Unit) := do
  configureProtectedModeVcpu vcpuContext.vcpu 0x1000 0

end Microvmm