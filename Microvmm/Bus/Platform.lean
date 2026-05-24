import Microvmm.Bus.Pci
import Microvmm.Host.SerialModel

namespace Microvmm

def com1Port : IoPort := ⟨0x3f8⟩

private def com1PortCount : UInt32 := 8

private def com2Port : IoPort := ⟨0x2f8⟩

private def com3Port : IoPort := ⟨0x3e8⟩

private def com4Port : IoPort := ⟨0x2e8⟩

structure PlatformBusState where
  virtioPci : VirtioPciState
deriving Repr, DecidableEq

def initialPlatformBusState (interruptLine : UInt32) : PlatformBusState :=
  {
    virtioPci := { (default : VirtioPciState) with interruptLine := interruptLine }
  }

def serialReceiveInterruptPending (serialState : SerialState) : Bool :=
  !serialState.inputQueue.isEmpty && (serialState.ier &&& 0x01) != 0

def serialTransmitInterruptPending (serialState : SerialState) : Bool :=
  (serialState.ier &&& 0x02) != 0

def serialInterruptLineEnabled (serialState : SerialState) : Bool :=
  (serialState.mcr &&& 0x08) != 0

def serialIir (serialState : SerialState) : UInt32 :=
  let fifoBits := if (serialState.fcr &&& 0x01) != 0 then 0xc0 else 0x00
  if serialReceiveInterruptPending serialState then
    fifoBits ||| 0x04
  else if serialTransmitInterruptPending serialState then
    fifoBits ||| 0x02
  else
    fifoBits ||| 0x01

def serialLsr (serialState : SerialState) : UInt32 :=
  0x60 ||| if serialState.inputQueue.isEmpty then 0 else 0x01

def serialPortBase? (port : UInt32) : Option UInt32 :=
  if port >= com1Port.value && port < com1Port.value + com1PortCount then
    some com1Port.value
  else if port >= com2Port.value && port < com2Port.value + com1PortCount then
    some com2Port.value
  else if port >= com3Port.value && port < com3Port.value + com1PortCount then
    some com3Port.value
  else if port >= com4Port.value && port < com4Port.value + com1PortCount then
    some com4Port.value
  else
    none

def ioByteWidth? (width : UInt32) : Option Nat :=
  if width == 1 then
    some 1
  else if width == 2 then
    some 2
  else if width == 4 then
    some 4
  else
    none

def passiveSerialReadByte? (serialState : SerialState) (offset : Nat) : Option UInt32 :=
  match offset with
  | 0 => some 0
  | 1 => some 0
  | 2 => some <| serialIir serialState
  | 3 => some serialState.lcr
  | 4 => some serialState.mcr
  | 5 => some <| serialLsr serialState
  | 6 => some 0xb0
  | 7 => some serialState.scratch
  | _ => none

def passiveSerialRead? (serialState : SerialState) (offset : Nat) (width : UInt32) : Option UInt32 := do
  let widthNat ← ioByteWidth? width
  if offset + widthNat > com1PortCount.toNat then
    none
  else
    (List.range widthNat).foldl
      (fun acc? index =>
        match acc?, passiveSerialReadByte? serialState (offset + index) with
        | some acc, some byteValue =>
            some <| acc ||| ((byteValue &&& 0xff) <<< (UInt32.ofNat (8 * index)))
        | _, _ => none)
      (some 0)

def boundedPassivePortAccess (access : IoAccess) : Bool :=
  if access.count != 1 then
    false
  else
    match ioByteWidth? access.width with
    | none => false
    | some widthNat =>
        match serialPortBase? access.port.value with
        | some basePort =>
            if basePort == com1Port.value then
              false
            else
              (access.port.value - basePort).toNat + widthNat <= com1PortCount.toNat
        | none =>
            access.port.value.toNat + widthNat <= 0x10000

def passivePortInput? (access : IoAccess) (serialState : SerialState := {}) : Option UInt32 :=
  match serialPortBase? access.port.value with
  | some basePort =>
      if basePort == com1Port.value then
        none
      else
        passiveSerialRead? serialState (access.port.value - basePort).toNat access.width
  | none =>
      match passivePciConfigRead? access.port.value access.width with
      | some response => some response
      | none =>
          if boundedPassivePortAccess access then
            some 0
          else
            none

inductive PlatformIoRoute where
  | pciConfig (surface : PciConfigRoutingSurface)
  | passive
deriving Repr, DecidableEq

def routePlatformIoAccess (access : IoAccess) : PlatformIoRoute :=
  match pciConfigRoutingSurface? access with
  | some surface => .pciConfig surface
  | none => .passive

end Microvmm