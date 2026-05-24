import Microvmm.Kvm.Resource

namespace Microvmm

def defaultVcpuId : UInt32 := 0

private def packedReadBase : Nat := 4294967296

def eproto : UInt32 := 71

def etimedout : UInt32 := 110

abbrev ErrnoResult (α : Type) := Outcome UInt32 α

def guestSpanValidFor (guestSize : UInt64) (guestAddr : UInt64) (spanSize : UInt64) : Bool :=
  if guestAddr <= guestSize then
    spanSize <= guestSize - guestAddr
  else
    false

def combineLowHigh (low : UInt32) (high : UInt32) : UInt64 :=
  (UInt64.ofNat high.toNat <<< 32) ||| UInt64.ofNat low.toNat

def low32 (value : UInt64) : UInt32 :=
  UInt32.ofNat (value.toNat % packedReadBase)

def high32 (value : UInt64) : UInt32 :=
  UInt32.ofNat (value.toNat / packedReadBase)

def setU64Low (target : UInt64) (value : UInt32) : UInt64 :=
  let highMask : UInt64 := 0xffffffff00000000
  (target &&& highMask) ||| UInt64.ofNat value.toNat

def setU64High (target : UInt64) (value : UInt32) : UInt64 :=
  let lowMask : UInt64 := 0x00000000ffffffff
  (target &&& lowMask) ||| (UInt64.ofNat value.toNat <<< 32)

end Microvmm