import Microvmm.VirtioPci

namespace Microvmm

private def ioByteWidth? (width : UInt32) : Option Nat :=
  match width.toNat with
  | 1 => some 1
  | 2 => some 2
  | 4 => some 4
  | _ => none

inductive PciConfigRoutingSurface where
  | address
  | data (byteOffset : Nat)
deriving Repr, DecidableEq

def pciConfigRoutingSurface? (access : IoAccess) : Option PciConfigRoutingSurface :=
  if access.port.value == virtioPciConfigAddressPort.value then
    some .address
  else if access.port.value >= virtioPciConfigDataPort.value &&
      access.port.value < virtioPciConfigDataPort.value + 4 then
    some <| .data (access.port.value - virtioPciConfigDataPort.value).toNat
  else
    none

def passivePciConfigRead? (port width : UInt32) : Option UInt32 := do
  let widthNat ← ioByteWidth? width
  if port.toNat < virtioPciConfigDataPort.value.toNat ||
      port.toNat + widthNat > virtioPciConfigDataPort.value.toNat + 4 then
    none
  else if widthNat == 1 then
    some 0xff
  else if widthNat == 2 then
    some 0xffff
  else if widthNat == 4 then
    some 0xffffffff
  else
    none

def routesToVirtioPciConfig (access : IoAccess) : Bool :=
  match pciConfigRoutingSurface? access with
  | some _ => true
  | none => false

end Microvmm