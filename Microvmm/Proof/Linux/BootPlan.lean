import Init.Omega
import Microvmm.Guest.Linux.Plan

namespace Microvmm

def linuxBootPlanFinalWriteViewPlacementOk (layout : BzImageLayout) (bootInputs : LinuxBootInputs) : Prop :=
  layout.headerCopySize <= maxSetupHeaderCopySize ∧
    kernelLoadAddr.value.toNat + layout.kernelBytes <= linuxGuestMemorySize.toNat ∧
    commandLineAddr.value.toNat + bootInputs.cmdlineBytes.size <= kernelLoadAddr.value.toNat ∧
    match bootInputs.initramfs? with
    | none => True
    | some (initramfsLayout, _) =>
        kernelLoadAddr.value.toNat + layout.kernelBytes <= initramfsLayout.loadAddr.value.toNat ∧
          initramfsLayout.loadAddr.value.toNat + initramfsLayout.size.toNat <= linuxGuestMemorySize.toNat

def linuxBootPlanWritesInRange (writes : List LinuxBootWrite) : Prop :=
  ∀ write ∈ writes, write.span.2 <= linuxGuestMemorySize.toNat

def linuxBootPlanFinalWriteViewImageOk (imageBytes : ByteArray) (layout : BzImageLayout) : Prop :=
  bzSetupSectsOffset + layout.headerCopySize <= imageBytes.size ∧
    layout.setupBytes <= imageBytes.size ∧
    layout.kernelBytes = imageBytes.size - layout.setupBytes

/-- These helper lemmas expose the fixed GDT/e820 byte windows directly from the pure planner, so
later invariants can reason about placement without unfolding byte encoders or guest writes. -/
abbrev planGdtEntryWrite_byteSize := planGdtEntryWrite_byteSize_impl

abbrev planGdtEntryWrite_span := planGdtEntryWrite_span_impl

abbrev planE820EntryWrite_byteSize := planE820EntryWrite_byteSize_impl

abbrev planE820EntryWrite_span := planE820EntryWrite_span_impl

/-- The protected-mode handoff descriptors occupy adjacent eight-byte slots in the fixed boot GDT,
so later proofs can treat the code and data descriptors as non-overlapping planned writes. -/
abbrev planGdtEntryWrite_handoff_descriptors_disjoint :=
  planGdtEntryWrite_handoff_descriptors_disjoint_impl

/-- The first two Linux e820 records are laid out back-to-back, which lets later proofs reason
about the low-RAM and VGA-hole entries independently. -/
abbrev planE820EntryWrite_lowRam_vgaHole_disjoint :=
  planE820EntryWrite_lowRam_vgaHole_disjoint_impl

end Microvmm
