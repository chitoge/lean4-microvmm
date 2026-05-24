import Microvmm.Common
import Microvmm.VirtioPci

namespace Microvmm

private def lapicMmioBase : MmioPhysAddr := ⟨0xfee00000⟩

private def lapicMmioSize : UInt64 := 0x1000

private def lapicIdOffset : UInt64 := 0x20

private def lapicVersionOffset : UInt64 := 0x30

private def lapicVersionValue : UInt32 := 0x00050014

inductive PassiveLapicMmioError where
  | requiresDwordAccess
deriving Repr, DecidableEq

inductive PlatformMmioRoute where
  | virtioPciBar
  | passiveLapic
deriving Repr, DecidableEq

/-- Once the guest assigns BAR0, any MMIO whose start address lands inside that window is owned by
the virtio-pci transport rather than the passive LAPIC model. This encodes the invariant that the
single BAR remains disjoint from the LAPIC window in the Linux guest configuration. -/
def activeVirtioPciBarWindowContains (state : VirtioPciState)
    (address : MmioPhysAddr) : Bool :=
  if state.bar0Base == 0 then
    false
  else
    let base := UInt64.ofNat state.bar0Base.toNat
    let limit := base + UInt64.ofNat state.bar0Size.toNat
    base <= address.value && address.value < limit

def routePlatformMmioAccess (state : VirtioPciState) (access : MmioAccess) : PlatformMmioRoute :=
  if activeVirtioPciBarWindowContains state access.address then
    .virtioPciBar
  else
    .passiveLapic

def stepPassiveLapicMmioTyped (access : MmioAccess) :
    Outcome PassiveLapicMmioError (Option UInt32) := do
  if access.width != 4 || access.address.value < lapicMmioBase.value ||
      access.address.value >= lapicMmioBase.value + lapicMmioSize then
    .error .requiresDwordAccess
  else
    let offset := access.address.value - lapicMmioBase.value
    match access.direction with
    | .read =>
        if offset == lapicIdOffset then
          .ok (some 0)
        else if offset == lapicVersionOffset then
          .ok (some lapicVersionValue)
        else
          .ok (some 0)
    | .write =>
        .ok none

def stepPassiveLapicMmio (access : MmioAccess) : ErrnoResult (Option UInt32) :=
  match stepPassiveLapicMmioTyped access with
  | .ok response? =>
      .ok response?
  | .error .requiresDwordAccess =>
      .error eproto

end Microvmm