import Microvmm.Guest.Linux.Cli
import Microvmm.Guest.Linux.Plan
import Microvmm.Kvm

namespace Microvmm

open Kvm

private def mapOutcomeError {ε ε' α : Type}
    (f : ε → ε') : Outcome ε α → Outcome ε' α
  | .error err => .error (f err)
  | .ok value => .ok value

/-- Pure bzImage/layout/input validation keeps reviewable domain constructors for later theorem
statements. The runtime boundary still adapts these back to `.parseKernelImage` so `decodeErrno`
and CLI-visible diagnostics stay stable. -/
inductive LinuxImageError where
  | imageTooSmall (size : Nat)
  | headerEndOutOfBounds (headerEnd imageSize : Nat)
  | headerCopySizeOutOfRange (size minSize maxSize : Nat)
  | truncatedRequiredHeader
  | invalidBootFlag
  | invalidHeaderMagic
  | unsupportedBootProtocol (version : UInt32)
  | missingLoadHigh
  | missingInitSize
  | kernelPayloadMissing (setupBytes imageSize : Nat)
  | unusableRuntimeStart
  | runtimeWindowOverflow
  | emptyInitramfs
  | initramfsLoadAddrOverflow
  | initramfsPlacementInvalid
  | commandLineTooLong (size limit : Nat)
  | kernelPlacementInvalid
  | bootParamsPlacementInvalid
  | commandLinePlacementInvalid
  | gdtPlacementInvalid
  | runtimeWindowExceedsGuestMemory
deriving Repr, DecidableEq

def linuxImageErrorToKvmError (_ : LinuxImageError) : Kvm.Error :=
  ⟨.parseKernelImage, eproto⟩

private def byteArrayGet? (bytes : ByteArray) (index : Nat) : Option UInt32 :=
  match bytes[index]? with
  | some byte => some <| UInt32.ofNat byte.toNat
  | none => none

private def byteArrayReadU16LE? (bytes : ByteArray) (index : Nat) : Option UInt32 := do
  let lo ← byteArrayGet? bytes index
  let hi ← byteArrayGet? bytes (index + 1)
  some (lo ||| (hi <<< 8))

private def byteArrayReadU32LE? (bytes : ByteArray) (index : Nat) : Option UInt32 := do
  let b0 ← byteArrayGet? bytes index
  let b1 ← byteArrayGet? bytes (index + 1)
  let b2 ← byteArrayGet? bytes (index + 2)
  let b3 ← byteArrayGet? bytes (index + 3)
  some (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))

private def byteArrayReadU64LE? (bytes : ByteArray) (index : Nat) : Option UInt64 := do
  let low ← byteArrayReadU32LE? bytes index
  let high ← byteArrayReadU32LE? bytes (index + 4)
  some (combineLowHigh low high)

private def alignUpU64? (value : UInt64) (alignment : UInt64) : Option UInt64 :=
  if alignment == 0 || ((alignment &&& (alignment - 1)) != 0) then
    none
  else
    let mask := alignment - 1
    let maxValue : UInt64 := 0xffffffffffffffff
    if value > maxValue - mask then
      none
    else
      some ((value + mask) &&& (~~~mask))

def parseBzImageLayoutTyped (imageBytes : ByteArray) : Outcome LinuxImageError BzImageLayout := do
  if imageBytes.size < 0x202 then
    .error (.imageTooSmall imageBytes.size)
  else
    let headerEnd :=
      match byteArrayGet? imageBytes 0x201 with
      | some value => 0x202 + value.toNat
      | none => 0
    if headerEnd <= bzSetupSectsOffset || headerEnd > imageBytes.size then
      .error (.headerEndOutOfBounds headerEnd imageBytes.size)
    else
      let headerCopySize := headerEnd - bzSetupSectsOffset
      if headerCopySize > maxSetupHeaderCopySize || headerCopySize < bzHeaderCopyFloor then
        .error (.headerCopySizeOutOfRange headerCopySize bzHeaderCopyFloor maxSetupHeaderCopySize)
      else
        match byteArrayReadU16LE? imageBytes bzBootFlagOffset,
            byteArrayReadU32LE? imageBytes bzHeaderMagicOffset,
            byteArrayReadU16LE? imageBytes bzVersionOffset,
            byteArrayGet? imageBytes bzLoadFlagsOffset,
            byteArrayReadU32LE? imageBytes bzCmdlineSizeOffset,
            byteArrayReadU32LE? imageBytes bzInitrdAddrMaxOffset,
            byteArrayGet? imageBytes bzRelocatableKernelOffset,
            byteArrayReadU64LE? imageBytes bzPrefAddressOffset,
            byteArrayReadU32LE? imageBytes bzKernelAlignmentOffset,
            byteArrayReadU32LE? imageBytes bzInitSizeOffset,
            byteArrayGet? imageBytes bzSetupSectsOffset with
        | some bootFlagValue, some headerMagicValue, some versionValue, some loadFlags,
          some rawCmdlineSize, some initrdAddrMax, some relocatableKernel, some prefAddress,
          some kernelAlignment, some initSize, some setupSects =>
            if bootFlagValue != bootFlag then
              .error .invalidBootFlag
            else if headerMagicValue != headerMagic then
              .error .invalidHeaderMagic
            else if versionValue < minBootProtocol then
              .error (.unsupportedBootProtocol versionValue)
            else if (loadFlags &&& loadedHighFlag) == 0 then
              .error .missingLoadHigh
            else if initSize == 0 then
              .error .missingInitSize
            else
              let setupSectsValue := if setupSects == 0 then 4 else setupSects.toNat
              let setupBytes := (setupSectsValue + 1) * 512
              if imageBytes.size <= setupBytes then
                .error (.kernelPayloadMissing setupBytes imageBytes.size)
              else
                let cmdlineSize := if rawCmdlineSize == 0 then cmdlineMaxFallback else rawCmdlineSize
                let runtimeStart? :=
                  if relocatableKernel != 0 then
                    let startValue := if kernelLoadAddr.value > prefAddress then kernelLoadAddr.value else prefAddress
                    alignUpU64? startValue (UInt64.ofNat kernelAlignment.toNat)
                  else if prefAddress != 0 then
                    some prefAddress
                  else
                    none
                match runtimeStart? with
                | none =>
                    .error .unusableRuntimeStart
                | some runtimeStart =>
                    let initSize64 := UInt64.ofNat initSize.toNat
                    let maxValue : UInt64 := 0xffffffffffffffff
                    if runtimeStart > maxValue - initSize64 then
                      .error .runtimeWindowOverflow
                    else
                      .ok {
                        headerCopySize := headerCopySize
                        setupBytes := setupBytes
                        kernelBytes := imageBytes.size - setupBytes
                        protocol := versionValue
                        cmdlineSize := cmdlineSize
                        loadFlags := loadFlags
                        runtimeStart := runtimeStart
                        runtimeWindowEnd := runtimeStart + initSize64
                        initrdAddrMax := initrdAddrMax
                      }
        | _, _, _, _, _, _, _, _, _, _, _ =>
            .error .truncatedRequiredHeader

def parseBzImageLayout (imageBytes : ByteArray) : Result BzImageLayout :=
  mapOutcomeError linuxImageErrorToKvmError <| parseBzImageLayoutTyped imageBytes

def planInitramfsLayoutTyped (layout : BzImageLayout)
    (initramfsSize : UInt64) : Outcome LinuxImageError InitramfsLayout := do
  if initramfsSize == 0 then
    .error .emptyInitramfs
  else
    match alignUpU64? layout.runtimeWindowEnd initramfsAlignment with
    | none =>
        .error .initramfsLoadAddrOverflow
    | some loadAddr =>
        let initrdGuestLimit := UInt64.ofNat layout.initrdAddrMax.toNat + 1
        if !guestSpanValidFor linuxGuestMemorySize loadAddr initramfsSize ||
            !guestSpanValidFor initrdGuestLimit loadAddr initramfsSize then
          .error .initramfsPlacementInvalid
        else
          .ok { loadAddr := ⟨loadAddr⟩, size := initramfsSize }

def planInitramfsLayout (layout : BzImageLayout) (initramfsSize : UInt64) : Result InitramfsLayout :=
  mapOutcomeError linuxImageErrorToKvmError <| planInitramfsLayoutTyped layout initramfsSize

def validateInitramfsLayoutTyped (layout : BzImageLayout)
    (initramfsBytes : ByteArray) : Outcome LinuxImageError InitramfsLayout :=
  planInitramfsLayoutTyped layout (UInt64.ofNat initramfsBytes.size)

def validateInitramfsLayout (layout : BzImageLayout) (initramfsBytes : ByteArray) : Result InitramfsLayout :=
  mapOutcomeError linuxImageErrorToKvmError <| validateInitramfsLayoutTyped layout initramfsBytes

def validateLinuxGuestLayoutTyped (layout : BzImageLayout)
    (commandLine : String := defaultLinuxBootCommandLine) : Outcome LinuxImageError ByteArray := do
  let cmdlineUtf8 := commandLine.toUTF8
  let cmdlineBytes := cmdlineUtf8.push 0
  if cmdlineUtf8.size >= layout.cmdlineSize.toNat then
    .error (.commandLineTooLong cmdlineUtf8.size layout.cmdlineSize.toNat)
  else if !guestSpanValidFor linuxGuestMemorySize kernelLoadAddr
      (UInt64.ofNat layout.kernelBytes) then
    .error .kernelPlacementInvalid
  else if !guestSpanValidFor linuxGuestMemorySize bootParamsAddr bootParamsSize then
    .error .bootParamsPlacementInvalid
  else if !guestSpanValidFor linuxGuestMemorySize commandLineAddr
      (UInt64.ofNat cmdlineBytes.size) then
    .error .commandLinePlacementInvalid
  else if !guestSpanValidFor linuxGuestMemorySize bootGdtAddr (4 * gdtEntrySize) then
    .error .gdtPlacementInvalid
  else if layout.runtimeWindowEnd > linuxGuestMemorySize then
    .error .runtimeWindowExceedsGuestMemory
  else
    .ok cmdlineBytes

def validateLinuxGuestLayout (layout : BzImageLayout)
    (commandLine : String := defaultLinuxBootCommandLine) : Result ByteArray :=
  mapOutcomeError linuxImageErrorToKvmError <| validateLinuxGuestLayoutTyped layout commandLine

def validateLinuxBootInputsTyped (layout : BzImageLayout)
    (commandLine : String := defaultLinuxBootCommandLine)
    (initramfsBytes? : Option ByteArray := none) : Outcome LinuxImageError LinuxBootInputs := do
  let cmdlineBytes ← validateLinuxGuestLayoutTyped layout commandLine
  match initramfsBytes? with
  | none =>
      .ok { cmdlineBytes }
  | some initramfsBytes =>
      let initramfsLayout ← validateInitramfsLayoutTyped layout initramfsBytes
      .ok { cmdlineBytes, initramfs? := some (initramfsLayout, initramfsBytes) }

def validateLinuxBootInputs (layout : BzImageLayout)
    (commandLine : String := defaultLinuxBootCommandLine)
    (initramfsBytes? : Option ByteArray := none) : Result LinuxBootInputs :=
  mapOutcomeError linuxImageErrorToKvmError <|
    validateLinuxBootInputsTyped layout commandLine initramfsBytes?

end Microvmm