import Microvmm.Common
import Microvmm.Core.Address
import Microvmm.Kvm.VcpuSetup

namespace Microvmm

structure ProbeSuccess where
  apiVersion : UInt32
  runAreaSize : UInt32
  transcriptExcerpt : String
deriving Repr, DecidableEq

structure BzImageLayout where
  headerCopySize : Nat
  setupBytes : Nat
  kernelBytes : Nat
  protocol : UInt32
  cmdlineSize : UInt32
  loadFlags : UInt32
  runtimeStart : UInt64
  runtimeWindowEnd : UInt64
  initrdAddrMax : UInt32
deriving Repr, DecidableEq

structure InitramfsLayout where
  loadAddr : GuestPhysAddr
  size : UInt64
deriving Repr, DecidableEq

structure LinuxBootParamsPointers where
  cmdLinePtr : UInt32
  extCmdLinePtr : UInt32
  ramdiskImage : UInt32
  ramdiskSize : UInt32
  extRamdiskImage : UInt32
  extRamdiskSize : UInt32
deriving Repr, DecidableEq

structure LinuxBootInputs where
  cmdlineBytes : ByteArray
  initramfs? : Option (InitramfsLayout × ByteArray) := none
deriving DecidableEq

/-- Keep Linux boot writes tagged with their role so later proofs can talk about placements
and fixed metadata without re-decoding raw guest bytes. `e820Entry` and `gdtEntry` remain
explicit because they encode boot-time invariants rather than arbitrary payloads. -/
inductive LinuxBootWriteKind where
  | kernelImage
  | bootParamsHeader
  | bootParamsHeaderSegment (index : UInt64)
  | initramfsImage
  | bootFlagSentinel
  | typeOfLoader
  | loadFlags
  | heapEndPtr
  | code32Start
  | ramdiskImage
  | ramdiskSize
  | cmdLinePtr
  | extCmdLinePtr
  | extRamdiskImage
  | extRamdiskSize
  | altMemK
  | e820EntryCount
  | screenInfoExtMemK
  | screenInfoVideoMode
  | screenInfoVideoCols
  | screenInfoVideoLines
  | screenInfoVideoIsVga
  | screenInfoVideoPoints
  | e820Entry (index : UInt64)
  | commandLine
  | gdtEntry (index : UInt64)
deriving Repr, DecidableEq, BEq

inductive LinuxBootWritePayload where
  | bytes (data : ByteArray)
  | u8 (value : UInt32)
  | u16 (value : UInt32)
  | u32 (value : UInt32)
  | e820Entry (addr size : UInt64) (typ : UInt32)
  | gdtEntry (base limit access flags : UInt32)
deriving DecidableEq, BEq

structure LinuxBootWrite where
  kind : LinuxBootWriteKind
  addr : GuestPhysAddr
  payload : LinuxBootWritePayload
deriving DecidableEq, BEq

/-- Boot-plan proofs reason about mathematical byte spans rather than wrapping `UInt64`
arithmetic, so placement and non-overlap lemmas stay on the pure planning surface. -/
def LinuxBootWritePayload.byteSize : LinuxBootWritePayload → Nat
  | .bytes data => data.size
  | .u8 _ => 1
  | .u16 _ => 2
  | .u32 _ => 4
  | .e820Entry .. => 20
  | .gdtEntry .. => 8

def LinuxBootWrite.byteSize (write : LinuxBootWrite) : Nat :=
  write.payload.byteSize

def LinuxBootWrite.span (write : LinuxBootWrite) : Nat × Nat :=
  let start := write.addr.value.toNat
  (start, start + write.byteSize)

def LinuxBootWrite.disjoint (lhs rhs : LinuxBootWrite) : Prop :=
  lhs.span.2 <= rhs.span.1 || rhs.span.2 <= lhs.span.1

/-- The replay order is part of the proof-facing surface so the interpreter stays a deterministic,
inspectable projection of the pure planning step. -/
structure LinuxBootPlan where
  writes : List LinuxBootWrite
deriving DecidableEq, BEq

def LinuxBootPlan.findWrite? (plan : LinuxBootPlan)
    (kind : LinuxBootWriteKind) : Option LinuxBootWrite :=
  let rec loop (remaining : List LinuxBootWrite) : Option LinuxBootWrite :=
    match remaining with
    | [] => none
    | write :: tail =>
        if write.kind == kind then
          some write
        else
          loop tail
  loop plan.writes

def linuxGuestMemorySize : UInt64 := 64 * 1024 * 1024

def lowMemoryLimit : UInt64 := 0x100000

def kernelLoadAddr : GuestPhysAddr := ⟨0x100000⟩

def bootParamsAddr : GuestPhysAddr := ⟨0x10000⟩

def commandLineAddr : GuestPhysAddr := ⟨0x20000⟩

def bootFlag : UInt32 := 0xaa55

def headerMagic : UInt32 := 0x53726448

def minBootProtocol : UInt32 := 0x020a

def loadedHighFlag : UInt32 := 0x01

def quietFlag : UInt32 := 0x20

def canUseHeapFlag : UInt32 := 0x80

def videoTypeVgaColor : UInt32 := 0x22

def cmdlineMaxFallback : UInt32 := 255

def e820TypeRam : UInt32 := 1

def e820TypeReserved : UInt32 := 2

def bzSetupSectsOffset : Nat := 0x1f1

def bzBootFlagOffset : Nat := 0x1fe

def bzHeaderMagicOffset : Nat := 0x202

def bzVersionOffset : Nat := 0x206

def bzTypeOfLoaderOffset : Nat := 0x210

def bzLoadFlagsOffset : Nat := 0x211

def bzCode32StartOffset : Nat := 0x214

def bzRamdiskImageOffset : Nat := 0x218

def bzRamdiskSizeOffset : Nat := 0x21c

def bzInitrdAddrMaxOffset : Nat := 0x22c

def bzHeapEndPtrOffset : Nat := 0x224

def bzCmdLinePtrOffset : Nat := 0x228

def bzKernelAlignmentOffset : Nat := 0x230

def bzRelocatableKernelOffset : Nat := 0x234

def bzCmdlineSizeOffset : Nat := 0x238

def bzPrefAddressOffset : Nat := 0x258

def bzInitSizeOffset : Nat := 0x260

def bzHeaderCopyFloor : Nat := bzInitSizeOffset - bzSetupSectsOffset + 4

def bpScreenInfoExtMemKOffset : UInt64 := 0x002

def bpScreenInfoVideoModeOffset : UInt64 := 0x006

def bpScreenInfoVideoColsOffset : UInt64 := 0x007

def bpScreenInfoVideoLinesOffset : UInt64 := 0x00e

def bpScreenInfoVideoIsVgaOffset : UInt64 := 0x00f

def bpScreenInfoVideoPointsOffset : UInt64 := 0x010

def bpExtRamdiskImageOffset : UInt64 := 0x0c0

def bpExtRamdiskSizeOffset : UInt64 := 0x0c4

def bpExtCmdLinePtrOffset : UInt64 := 0x0c8

def bpAltMemKOffset : UInt64 := 0x1e0

def bpE820EntriesOffset : UInt64 := 0x1e8

def bpHeaderOffset : UInt64 := 0x1f1

def bpE820TableOffset : UInt64 := 0x2d0

def bootParamsHeaderBootFlagRelOffset : Nat := bzBootFlagOffset - bzSetupSectsOffset

def bootParamsHeaderBootFlagEndRelOffset : Nat := bootParamsHeaderBootFlagRelOffset + 2

def bootParamsHeaderTypeOfLoaderRelOffset : Nat := bzTypeOfLoaderOffset - bzSetupSectsOffset

def bootParamsHeaderLoadFlagsEndRelOffset : Nat := bootParamsHeaderTypeOfLoaderRelOffset + 2

def bootParamsHeaderCode32StartRelOffset : Nat := bzCode32StartOffset - bzSetupSectsOffset

def bootParamsHeaderRamdiskSizeEndRelOffset : Nat := bzRamdiskSizeOffset - bzSetupSectsOffset + 4

def bootParamsHeaderHeapEndPtrRelOffset : Nat := bzHeapEndPtrOffset - bzSetupSectsOffset

def bootParamsHeaderHeapEndPtrEndRelOffset : Nat := bootParamsHeaderHeapEndPtrRelOffset + 2

def bootParamsHeaderCmdLinePtrRelOffset : Nat := bzCmdLinePtrOffset - bzSetupSectsOffset

def bootParamsHeaderCmdLinePtrEndRelOffset : Nat := bootParamsHeaderCmdLinePtrRelOffset + 4

def e820EntrySize : UInt64 := 20

def gdtEntrySize : UInt64 := 8

def bootParamsSize : UInt64 := 0x1000

def initramfsAlignment : UInt64 := 0x1000

def maxSetupHeaderCopySize : Nat := 0x26c - 0x1f1

def linuxBootParamsPointers (cmdLineAddr : GuestPhysAddr)
    (initramfs? : Option InitramfsLayout) : LinuxBootParamsPointers :=
  let ramdiskImage :=
    match initramfs? with
    | some layout => layout.loadAddr.value
    | none => 0
  let ramdiskSize :=
    match initramfs? with
    | some layout => layout.size
    | none => 0
  {
    cmdLinePtr := low32 cmdLineAddr.value
    extCmdLinePtr := high32 cmdLineAddr.value
    ramdiskImage := low32 ramdiskImage
    ramdiskSize := low32 ramdiskSize
    extRamdiskImage := high32 ramdiskImage
    extRamdiskSize := high32 ramdiskSize
  }

def linuxBootBytesWrite (kind : LinuxBootWriteKind) (addr : GuestPhysAddr)
    (bytes : ByteArray) : LinuxBootWrite :=
  { kind, addr, payload := .bytes bytes }

def linuxBootU8Write (kind : LinuxBootWriteKind) (addr : GuestPhysAddr)
    (value : UInt32) : LinuxBootWrite :=
  { kind, addr, payload := .u8 value }

def linuxBootU16Write (kind : LinuxBootWriteKind) (addr : GuestPhysAddr)
    (value : UInt32) : LinuxBootWrite :=
  { kind, addr, payload := .u16 value }

def linuxBootU32Write (kind : LinuxBootWriteKind) (addr : GuestPhysAddr)
    (value : UInt32) : LinuxBootWrite :=
  { kind, addr, payload := .u32 value }

def guestAddrOffset (base : GuestPhysAddr) (offset : UInt64) : GuestPhysAddr :=
  ⟨base.value + offset⟩

def planBootParamsHeaderSegmentWrite (segmentIndex : UInt64) (start stop : Nat)
    (headerBytes : ByteArray) : LinuxBootWrite :=
  linuxBootBytesWrite (.bootParamsHeaderSegment segmentIndex)
    (guestAddrOffset bootParamsAddr (bpHeaderOffset + UInt64.ofNat start))
    (headerBytes.extract start stop)

def planGdtEntryWrite (entryIndex : UInt64)
    (base limit access flags : UInt32) : LinuxBootWrite :=
  {
    kind := .gdtEntry entryIndex
    addr := guestAddrOffset bootGdtAddr (entryIndex * gdtEntrySize)
    payload := .gdtEntry base limit access flags
  }

def planE820EntryWrite (entryIndex : UInt64)
    (regionAddr regionSize : UInt64) (typ : UInt32) : LinuxBootWrite :=
  {
    kind := .e820Entry entryIndex
    addr := guestAddrOffset bootParamsAddr (bpE820TableOffset + entryIndex * e820EntrySize)
    payload := .e820Entry regionAddr regionSize typ
  }

theorem planGdtEntryWrite_byteSize_impl (entryIndex : UInt64)
    (base limit access flags : UInt32) :
    (planGdtEntryWrite entryIndex base limit access flags).byteSize = gdtEntrySize.toNat := by
  simp [LinuxBootWrite.byteSize, LinuxBootWritePayload.byteSize, planGdtEntryWrite, gdtEntrySize]

theorem planGdtEntryWrite_span_impl (entryIndex : UInt64)
    (base limit access flags : UInt32) :
    (planGdtEntryWrite entryIndex base limit access flags).span =
      let start := (guestAddrOffset bootGdtAddr (entryIndex * gdtEntrySize)).value.toNat
      (start, start + gdtEntrySize.toNat) := by
  simp [LinuxBootWrite.span, LinuxBootWrite.byteSize, LinuxBootWritePayload.byteSize,
    planGdtEntryWrite, gdtEntrySize]

theorem planE820EntryWrite_byteSize_impl (entryIndex : UInt64)
    (regionAddr regionSize : UInt64) (typ : UInt32) :
    (planE820EntryWrite entryIndex regionAddr regionSize typ).byteSize = e820EntrySize.toNat := by
  simp [LinuxBootWrite.byteSize, LinuxBootWritePayload.byteSize, planE820EntryWrite,
    e820EntrySize]

theorem planE820EntryWrite_span_impl (entryIndex : UInt64)
    (regionAddr regionSize : UInt64) (typ : UInt32) :
    (planE820EntryWrite entryIndex regionAddr regionSize typ).span =
      let start :=
        (guestAddrOffset bootParamsAddr (bpE820TableOffset + entryIndex * e820EntrySize)).value.toNat
      (start, start + e820EntrySize.toNat) := by
  simp [LinuxBootWrite.span, LinuxBootWrite.byteSize, LinuxBootWritePayload.byteSize,
    planE820EntryWrite, e820EntrySize]

theorem planGdtEntryWrite_handoff_descriptors_disjoint_impl :
    (planGdtEntryWrite 2 0 0x000fffff 0x9b 0xc0).disjoint
      (planGdtEntryWrite 3 0 0x000fffff 0x93 0xc0) := by
  simp [LinuxBootWrite.disjoint, LinuxBootWrite.span, LinuxBootWrite.byteSize,
    LinuxBootWritePayload.byteSize, planGdtEntryWrite, guestAddrOffset, bootGdtAddr,
    gdtEntrySize]

theorem planE820EntryWrite_lowRam_vgaHole_disjoint_impl :
    (planE820EntryWrite 0 0 0x000a0000 e820TypeRam).disjoint
      (planE820EntryWrite 1 0x000a0000 0x00060000 e820TypeReserved) := by
  simp [LinuxBootWrite.disjoint, LinuxBootWrite.span, LinuxBootWrite.byteSize,
    LinuxBootWritePayload.byteSize, planE820EntryWrite, guestAddrOffset, bootParamsAddr,
    bpE820TableOffset, e820EntrySize]

def planOptionalInitramfsWrites
    (initramfs? : Option (InitramfsLayout × ByteArray)) : List LinuxBootWrite :=
  match initramfs? with
  | none =>
      []
  | some (layout, initramfsBytes) =>
      [linuxBootBytesWrite .initramfsImage layout.loadAddr initramfsBytes]

def planLinuxBootParamsPointerWrites
    (pointers : LinuxBootParamsPointers) : List LinuxBootWrite := [
      linuxBootU32Write .ramdiskImage
        (guestAddrOffset bootParamsAddr (UInt64.ofNat bzRamdiskImageOffset)) pointers.ramdiskImage,
      linuxBootU32Write .ramdiskSize
        (guestAddrOffset bootParamsAddr (UInt64.ofNat bzRamdiskSizeOffset)) pointers.ramdiskSize,
      linuxBootU32Write .cmdLinePtr
        (guestAddrOffset bootParamsAddr (UInt64.ofNat bzCmdLinePtrOffset)) pointers.cmdLinePtr,
      linuxBootU32Write .extCmdLinePtr
        (guestAddrOffset bootParamsAddr bpExtCmdLinePtrOffset) pointers.extCmdLinePtr,
      linuxBootU32Write .extRamdiskImage
        (guestAddrOffset bootParamsAddr bpExtRamdiskImageOffset) pointers.extRamdiskImage,
      linuxBootU32Write .extRamdiskSize
        (guestAddrOffset bootParamsAddr bpExtRamdiskSizeOffset) pointers.extRamdiskSize
    ]

def planBootParamsHeaderFinalWrites (headerBytes : ByteArray) : List LinuxBootWrite := [
    planBootParamsHeaderSegmentWrite 0 0 bootParamsHeaderBootFlagRelOffset headerBytes,
    planBootParamsHeaderSegmentWrite 1 bootParamsHeaderBootFlagEndRelOffset
      bootParamsHeaderTypeOfLoaderRelOffset headerBytes,
    planBootParamsHeaderSegmentWrite 2 bootParamsHeaderLoadFlagsEndRelOffset
      bootParamsHeaderCode32StartRelOffset headerBytes,
    planBootParamsHeaderSegmentWrite 3 bootParamsHeaderRamdiskSizeEndRelOffset
      bootParamsHeaderHeapEndPtrRelOffset headerBytes,
    planBootParamsHeaderSegmentWrite 4 bootParamsHeaderHeapEndPtrEndRelOffset
      bootParamsHeaderCmdLinePtrRelOffset headerBytes,
    planBootParamsHeaderSegmentWrite 5 bootParamsHeaderCmdLinePtrEndRelOffset headerBytes.size
      headerBytes
  ]

/-- Build the ordered guest-memory write plan for Linux bzImage boot preparation.
`validateLinuxBootInputs` already established that the fixed placements used here fit inside guest
RAM, so this step remains pure and exposes the layout needed for later proofs. -/
def buildLinuxBootPlan (imageBytes : ByteArray)
    (layout : BzImageLayout) (bootInputs : LinuxBootInputs) : LinuxBootPlan :=
  let kernelBytes := imageBytes.extract layout.setupBytes imageBytes.size
  let headerBytes := imageBytes.extract bzSetupSectsOffset (bzSetupSectsOffset + layout.headerCopySize)
  let bootParamsPointers :=
    linuxBootParamsPointers commandLineAddr (bootInputs.initramfs?.map Prod.fst)
  let altMemKNat := ((linuxGuestMemorySize - lowMemoryLimit) / 1024).toNat
  let altMemK := UInt32.ofNat altMemKNat
  let screenInfoExtMemK := UInt32.ofNat (min altMemKNat 65535)
  let loadFlags := (layout.loadFlags ||| canUseHeapFlag) &&& (~~~quietFlag)
  let initramfsWrites := planOptionalInitramfsWrites bootInputs.initramfs?
  -- Linux still expects the conventional low RAM / reserved VGA hole / high RAM map in this order.
  let e820Writes : List LinuxBootWrite := [
    planE820EntryWrite 0 0 0x000a0000 e820TypeRam,
    planE820EntryWrite 1 0x000a0000 0x00060000 e820TypeReserved,
    planE820EntryWrite 2 0x00100000 (linuxGuestMemorySize - 0x00100000) e820TypeRam
  ]
  -- `configureProtectedModeVcpu` points KVM at `bootGdtAddr`, so entries 2 and 3 stay aligned with
  -- the fixed flat code/data descriptors used for the Linux handoff.
  let gdtWrites : List LinuxBootWrite := [
    planGdtEntryWrite 2 0 0x000fffff 0x9b 0xc0,
    planGdtEntryWrite 3 0 0x000fffff 0x93 0xc0
  ]
  {
    writes :=
      [
        linuxBootBytesWrite .kernelImage kernelLoadAddr kernelBytes,
        linuxBootBytesWrite .bootParamsHeader (guestAddrOffset bootParamsAddr bpHeaderOffset) headerBytes
      ] ++ initramfsWrites ++
      [
        linuxBootU16Write .bootFlagSentinel (guestAddrOffset bootParamsAddr (UInt64.ofNat 0x1fa)) 0xffff,
        linuxBootU8Write .typeOfLoader (guestAddrOffset bootParamsAddr (UInt64.ofNat bzTypeOfLoaderOffset)) 0xff,
        linuxBootU8Write .loadFlags (guestAddrOffset bootParamsAddr (UInt64.ofNat bzLoadFlagsOffset)) loadFlags,
        linuxBootU16Write .heapEndPtr (guestAddrOffset bootParamsAddr (UInt64.ofNat bzHeapEndPtrOffset)) 0xde00,
        linuxBootU32Write .code32Start (guestAddrOffset bootParamsAddr (UInt64.ofNat bzCode32StartOffset))
          (UInt32.ofNat kernelLoadAddr.value.toNat)
      ] ++ planLinuxBootParamsPointerWrites bootParamsPointers ++
      [
        linuxBootU32Write .altMemK (guestAddrOffset bootParamsAddr bpAltMemKOffset) altMemK,
        linuxBootU8Write .e820EntryCount (guestAddrOffset bootParamsAddr bpE820EntriesOffset) 3,
        linuxBootU16Write .screenInfoExtMemK (guestAddrOffset bootParamsAddr bpScreenInfoExtMemKOffset)
          screenInfoExtMemK,
        linuxBootU8Write .screenInfoVideoMode (guestAddrOffset bootParamsAddr bpScreenInfoVideoModeOffset) 3,
        linuxBootU8Write .screenInfoVideoCols (guestAddrOffset bootParamsAddr bpScreenInfoVideoColsOffset) 80,
        linuxBootU8Write .screenInfoVideoLines (guestAddrOffset bootParamsAddr bpScreenInfoVideoLinesOffset) 25,
        linuxBootU8Write .screenInfoVideoIsVga (guestAddrOffset bootParamsAddr bpScreenInfoVideoIsVgaOffset)
          videoTypeVgaColor,
        linuxBootU16Write .screenInfoVideoPoints (guestAddrOffset bootParamsAddr bpScreenInfoVideoPointsOffset) 16
      ] ++ e820Writes ++
      [linuxBootBytesWrite .commandLine commandLineAddr bootInputs.cmdlineBytes] ++
      gdtWrites
  }

/-- Proof-facing normalized view of the Linux boot plan. The executable planner keeps the original
header copy followed by field overrides because replay order matters there; this alternate view
splits the copied setup header around those overridden bytes so later placement theorems can talk
about the final non-overlapping write windows that the guest observes. -/
def buildLinuxBootPlanFinalWriteView (imageBytes : ByteArray)
    (layout : BzImageLayout) (bootInputs : LinuxBootInputs) : LinuxBootPlan :=
  let kernelBytes := imageBytes.extract layout.setupBytes imageBytes.size
  let headerBytes := imageBytes.extract bzSetupSectsOffset (bzSetupSectsOffset + layout.headerCopySize)
  let bootParamsPointers :=
    linuxBootParamsPointers commandLineAddr (bootInputs.initramfs?.map Prod.fst)
  let altMemKNat := ((linuxGuestMemorySize - lowMemoryLimit) / 1024).toNat
  let altMemK := UInt32.ofNat altMemKNat
  let screenInfoExtMemK := UInt32.ofNat (min altMemKNat 65535)
  let loadFlags := (layout.loadFlags ||| canUseHeapFlag) &&& (~~~quietFlag)
  let initramfsWrites := planOptionalInitramfsWrites bootInputs.initramfs?
  let e820Writes : List LinuxBootWrite := [
    planE820EntryWrite 0 0 0x000a0000 e820TypeRam,
    planE820EntryWrite 1 0x000a0000 0x00060000 e820TypeReserved,
    planE820EntryWrite 2 0x00100000 (linuxGuestMemorySize - 0x00100000) e820TypeRam
  ]
  let gdtWrites : List LinuxBootWrite := [
    planGdtEntryWrite 2 0 0x000fffff 0x9b 0xc0,
    planGdtEntryWrite 3 0 0x000fffff 0x93 0xc0
  ]
  {
    writes :=
      [linuxBootBytesWrite .kernelImage kernelLoadAddr kernelBytes] ++
      planBootParamsHeaderFinalWrites headerBytes ++
      initramfsWrites ++
      [
        linuxBootU16Write .bootFlagSentinel (guestAddrOffset bootParamsAddr (UInt64.ofNat 0x1fa)) 0xffff,
        linuxBootU8Write .typeOfLoader (guestAddrOffset bootParamsAddr (UInt64.ofNat bzTypeOfLoaderOffset)) 0xff,
        linuxBootU8Write .loadFlags (guestAddrOffset bootParamsAddr (UInt64.ofNat bzLoadFlagsOffset)) loadFlags,
        linuxBootU16Write .heapEndPtr (guestAddrOffset bootParamsAddr (UInt64.ofNat bzHeapEndPtrOffset)) 0xde00,
        linuxBootU32Write .code32Start (guestAddrOffset bootParamsAddr (UInt64.ofNat bzCode32StartOffset))
          (UInt32.ofNat kernelLoadAddr.value.toNat)
      ] ++ planLinuxBootParamsPointerWrites bootParamsPointers ++
      [
        linuxBootU32Write .altMemK (guestAddrOffset bootParamsAddr bpAltMemKOffset) altMemK,
        linuxBootU8Write .e820EntryCount (guestAddrOffset bootParamsAddr bpE820EntriesOffset) 3,
        linuxBootU16Write .screenInfoExtMemK (guestAddrOffset bootParamsAddr bpScreenInfoExtMemKOffset)
          screenInfoExtMemK,
        linuxBootU8Write .screenInfoVideoMode (guestAddrOffset bootParamsAddr bpScreenInfoVideoModeOffset) 3,
        linuxBootU8Write .screenInfoVideoCols (guestAddrOffset bootParamsAddr bpScreenInfoVideoColsOffset) 80,
        linuxBootU8Write .screenInfoVideoLines (guestAddrOffset bootParamsAddr bpScreenInfoVideoLinesOffset) 25,
        linuxBootU8Write .screenInfoVideoIsVga (guestAddrOffset bootParamsAddr bpScreenInfoVideoIsVgaOffset)
          videoTypeVgaColor,
        linuxBootU16Write .screenInfoVideoPoints (guestAddrOffset bootParamsAddr bpScreenInfoVideoPointsOffset) 16
      ] ++ e820Writes ++
      [linuxBootBytesWrite .commandLine commandLineAddr bootInputs.cmdlineBytes] ++
      gdtWrites
  }

end Microvmm
