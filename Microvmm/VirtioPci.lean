import Microvmm.Device.Virtio.Core

namespace Microvmm

/-- The first PCI slice fixes a single virtio function at bus 0, device 1, function 0 so
later proofs can reason about one BDF before multi-device routing exists. -/
def virtioPciBus : UInt32 := 0

private def pciHostBridgeDeviceNumber : UInt32 := 0

private def pciHostBridgeFunctionNumber : UInt32 := 0

def virtioPciDeviceNumber : UInt32 := 1

def virtioPciFunctionNumber : UInt32 := 0

def virtioPciConfigAddressPort : IoPort := ⟨0xcf8⟩

def virtioPciConfigDataPort : IoPort := ⟨0xcfc⟩

def virtioPciBar0Size : UInt32 := 0x1000

def virtioPciCommonCfgOffset : UInt32 := 0x0000

/-- Linux maps the full modern common-config struct, including the post-1.1 queue-reset/admin
fields, even when this tiny device leaves them unused. Keep the capability span large enough for
those natural-width accesses and answer them with stable zero values. -/
def virtioPciCommonCfgLength : UInt32 := 0x0040

def virtioPciNotifyCfgOffset : UInt32 := 0x0100

def virtioPciNotifyCfgLength : UInt32 := 0x0004

def virtioPciNotifyMultiplier : UInt32 := 0x0004

def virtioPciIsrCfgOffset : UInt32 := 0x0200

def virtioPciIsrCfgLength : UInt32 := 0x0001

def virtioPciDeviceCfgOffset : UInt32 := 0x0300

/-- The virtio-rng device has no device-specific fields, but Linux still requires the capability to
advertise a non-zero mappable span before it accepts the modern PCI transport. -/
def virtioPciDeviceCfgLength : UInt32 := 0x0001

private def virtioPciVendorId : UInt32 := 0x1af4

private def virtioPciRngDeviceId : UInt32 := 0x1044

private def pciHostBridgeVendorId : UInt32 := 0x8086

private def pciHostBridgeDeviceId : UInt32 := 0x1237

private def virtioPciSubsystemDeviceId : UInt32 := 0x0004

private def virtioPciStatusCapabilitiesList : UInt32 := 0x0010

private def virtioPciCommandMemorySpace : UInt32 := 0x0002

private def virtioPciInterruptLineDefault : UInt32 := 0

private def virtioPciInterruptPinIntA : UInt32 := 1

private def virtioPciRevisionId : UInt32 := 1

private def pciHostBridgeRevisionId : UInt32 := 0x02

private def virtioPciProgIf : UInt32 := 0

private def virtioPciSubclass : UInt32 := 0

private def pciHostBridgeSubclass : UInt32 := 0x00

private def virtioPciClassCode : UInt32 := 0xff

private def pciHostBridgeClassCode : UInt32 := 0x06

private def virtioPciHeaderType : UInt32 := 0x00

private def pciHostBridgeHeaderType : UInt32 := 0x00

private def virtioPciBarMemoryMask : UInt32 := 0xfffffff0

private def virtioPciCapabilityPointer : Nat := 0x50

private def virtioPciCapVendorSpecificId : UInt32 := 0x09

private def virtioPciCapCommonCfgType : UInt32 := 1

private def virtioPciCapNotifyCfgType : UInt32 := 2

private def virtioPciCapIsrCfgType : UInt32 := 3

private def virtioPciCapDeviceCfgType : UInt32 := 4

structure VirtioPciState where
  configAddress : UInt32 := 0
  command : UInt32 := 0
  bar0Base : UInt32 := 0
  bar0Size : UInt32 := virtioPciBar0Size
  bar0Sizing : Bool := false
  interruptLine : UInt32 := virtioPciInterruptLineDefault
  interruptPin : UInt32 := virtioPciInterruptPinIntA
  device : VirtioDeviceState := default
deriving Repr, DecidableEq, BEq

instance : Inhabited VirtioPciState :=
  ⟨{
    configAddress := 0
    command := 0
    bar0Base := 0
    bar0Size := virtioPciBar0Size
    bar0Sizing := false
    interruptLine := virtioPciInterruptLineDefault
    interruptPin := virtioPciInterruptPinIntA
    device := default
  }⟩

private structure PciCapability where
  offset : Nat
  next : UInt32
  len : UInt32
  cfgType : UInt32
  bar : UInt32 := 0
  regionOffset : UInt32
  regionLength : UInt32
  notifyMultiplier? : Option UInt32 := none

private def pciCapabilities : List PciCapability := [
  {
    offset := 0x50
    next := 0x60
    len := 16
    cfgType := virtioPciCapCommonCfgType
    regionOffset := virtioPciCommonCfgOffset
    regionLength := virtioPciCommonCfgLength
  },
  {
    offset := 0x60
    next := 0x74
    len := 20
    cfgType := virtioPciCapNotifyCfgType
    regionOffset := virtioPciNotifyCfgOffset
    regionLength := virtioPciNotifyCfgLength
    notifyMultiplier? := some virtioPciNotifyMultiplier
  },
  {
    offset := 0x74
    next := 0x84
    len := 16
    cfgType := virtioPciCapIsrCfgType
    regionOffset := virtioPciIsrCfgOffset
    regionLength := virtioPciIsrCfgLength
  },
  {
    offset := 0x84
    next := 0
    len := 16
    cfgType := virtioPciCapDeviceCfgType
    regionOffset := virtioPciDeviceCfgOffset
    regionLength := virtioPciDeviceCfgLength
  }
]

private def widthNat? (width : UInt32) : Option Nat :=
  match width.toNat with
  | 1 => some 1
  | 2 => some 2
  | 4 => some 4
  | _ => none

private def requireWidthNat (width : UInt32) : ErrnoResult Nat :=
  match widthNat? width with
  | some widthNat => .ok widthNat
  | none => .error eproto

private def allOnesForWidth (widthNat : Nat) : UInt32 :=
  match widthNat with
  | 1 => 0xff
  | 2 => 0xffff
  | 4 => 0xffffffff
  | _ => 0

private def byteValueAt (value : UInt32) (index : Nat) : UInt32 :=
  UInt32.ofNat ((value.toNat / (Nat.pow 256 index)) % 256)

private def replaceByte (word : UInt32) (index : Nat) (byteValue : UInt32) : UInt32 :=
  let shift := UInt32.ofNat (8 * index)
  let mask : UInt32 := (0xff : UInt32) <<< shift
  (word &&& (~~~mask)) ||| ((byteValue &&& 0xff) <<< shift)

private def overlayWord32 (current : UInt32) (startByte : Nat) (widthNat : Nat)
    (value : UInt32) : UInt32 :=
  (List.range widthNat).foldl
    (fun word index => replaceByte word (startByte + index) (byteValueAt value index))
    current

private def packWindow (readByte : Nat → UInt32) (widthNat : Nat) : UInt32 :=
  (List.range widthNat).foldl
    (fun acc index => acc ||| (readByte index <<< UInt32.ofNat (8 * index)))
    0

private def shiftRight32 (value : UInt32) (bits : Nat) : UInt32 :=
  value >>> UInt32.ofNat bits

private inductive PciConfigTarget where
  | hostBridge
  | virtioRng
deriving Repr, DecidableEq

private def configAddressTarget? (configAddress : UInt32) : Option PciConfigTarget :=
  let enabled := (configAddress &&& 0x80000000) != 0
  let bus := shiftRight32 configAddress 16 &&& 0xff
  let device := shiftRight32 configAddress 11 &&& 0x1f
  let function := shiftRight32 configAddress 8 &&& 0x07
  if !enabled || bus != virtioPciBus then
    none
  else if device == pciHostBridgeDeviceNumber && function == pciHostBridgeFunctionNumber then
    some .hostBridge
  else if device == virtioPciDeviceNumber && function == virtioPciFunctionNumber then
    some .virtioRng
  else
    none

def virtioPciConfigAddressForOffset (offset : UInt32) : UInt32 :=
  0x80000000 ||| (virtioPciDeviceNumber <<< UInt32.ofNat 11) |||
    (virtioPciFunctionNumber <<< UInt32.ofNat 8) ||| (offset &&& 0xfc)

/-- BAR sizing assumes the fixed BAR length is a non-zero power of two, which keeps the pure mask
derivation identical to the PCI sizing rule and easy to state in later proofs. -/
private def bar0SizeMask (state : VirtioPciState) : UInt32 :=
  (~~~(state.bar0Size - 1)) &&& virtioPciBarMemoryMask

private def bar0Readback (state : VirtioPciState) : UInt32 :=
  if state.bar0Sizing then
    bar0SizeMask state
  else
    state.bar0Base &&& virtioPciBarMemoryMask

private def configCommandDword (state : VirtioPciState) : UInt32 :=
  (state.command &&& 0xffff) ||| (virtioPciStatusCapabilitiesList <<< UInt32.ofNat 16)

private def readCapabilityFieldByte (cap : PciCapability) (relativeOffset : Nat) : UInt32 :=
  match relativeOffset with
  | 0 => virtioPciCapVendorSpecificId
  | 1 => cap.next &&& 0xff
  | 2 => cap.len &&& 0xff
  | 3 => cap.cfgType &&& 0xff
  | 4 => cap.bar &&& 0xff
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | offset + 8 =>
      if offset < 4 then
        byteValueAt cap.regionOffset offset
      else if offset < 8 then
        byteValueAt cap.regionLength (offset - 4)
      else
        match cap.notifyMultiplier? with
        | some multiplier => byteValueAt multiplier (offset - 8)
        | none => 0

private def readCapabilityByte? (offset : Nat) : Option UInt32 :=
  let rec loop (remaining : List PciCapability) : Option UInt32 :=
    match remaining with
    | [] => none
    | cap :: tail =>
        if cap.offset <= offset && offset < cap.offset + cap.len.toNat then
          some <| readCapabilityFieldByte cap (offset - cap.offset)
        else
          loop tail
  loop pciCapabilities

private def hostBridgeConfigByteAt (offset : Nat) : UInt32 :=
  match offset with
  | 0x00 => byteValueAt pciHostBridgeVendorId 0
  | 0x01 => byteValueAt pciHostBridgeVendorId 1
  | 0x02 => byteValueAt pciHostBridgeDeviceId 0
  | 0x03 => byteValueAt pciHostBridgeDeviceId 1
  | 0x08 => pciHostBridgeRevisionId
  | 0x09 => 0
  | 0x0a => pciHostBridgeSubclass
  | 0x0b => pciHostBridgeClassCode
  | 0x0e => pciHostBridgeHeaderType
  | _ => 0

/-- Linux x86 direct PCI probing insists on finding a plausible host bridge on bus 0 before it
trusts CF8/CFC config cycles, so expose a tiny read-only bridge at 00:00.0 next to the single
virtio-rng function. -/
private def virtioConfigByteAt (state : VirtioPciState) (offset : Nat) : UInt32 :=
  match offset with
  | 0x00 => byteValueAt virtioPciVendorId 0
  | 0x01 => byteValueAt virtioPciVendorId 1
  | 0x02 => byteValueAt virtioPciRngDeviceId 0
  | 0x03 => byteValueAt virtioPciRngDeviceId 1
  | 0x04 => byteValueAt (configCommandDword state) 0
  | 0x05 => byteValueAt (configCommandDword state) 1
  | 0x06 => byteValueAt (configCommandDword state) 2
  | 0x07 => byteValueAt (configCommandDword state) 3
  | 0x08 => virtioPciRevisionId
  | 0x09 => virtioPciProgIf
  | 0x0a => virtioPciSubclass
  | 0x0b => virtioPciClassCode
  | 0x0c => 0
  | 0x0d => 0
  | 0x0e => virtioPciHeaderType
  | 0x0f => 0
  | 0x10 => byteValueAt (bar0Readback state) 0
  | 0x11 => byteValueAt (bar0Readback state) 1
  | 0x12 => byteValueAt (bar0Readback state) 2
  | 0x13 => byteValueAt (bar0Readback state) 3
  | 0x2c => byteValueAt virtioPciVendorId 0
  | 0x2d => byteValueAt virtioPciVendorId 1
  | 0x2e => byteValueAt virtioPciSubsystemDeviceId 0
  | 0x2f => byteValueAt virtioPciSubsystemDeviceId 1
  | 0x34 => UInt32.ofNat virtioPciCapabilityPointer
  | 0x35 => 0
  | 0x3c => state.interruptLine &&& 0xff
  | 0x3d => state.interruptPin &&& 0xff
  | _ =>
      match readCapabilityByte? offset with
      | some byteValue => byteValue
      | none => 0

private def readConfigWindow (state : VirtioPciState) (target : PciConfigTarget)
    (offset : Nat) (widthNat : Nat) : UInt32 :=
  match target with
  | .hostBridge =>
      packWindow (fun index => hostBridgeConfigByteAt (offset + index)) widthNat
  | .virtioRng =>
      packWindow (fun index => virtioConfigByteAt state (offset + index)) widthNat

private def readConfigAddressPort (state : VirtioPciState) (widthNat : Nat) : UInt32 :=
  packWindow (fun index => byteValueAt state.configAddress index) widthNat

private def writeConfigAddressPort (state : VirtioPciState) (widthNat : Nat)
    (value : UInt32) : VirtioPciState :=
  { state with configAddress := overlayWord32 state.configAddress 0 widthNat value }

private def writeConfigWindow (state : VirtioPciState) (offset : Nat) (widthNat : Nat)
    (value : UInt32) : ErrnoResult VirtioPciState :=
  if offset >= 0x04 && offset + widthNat <= 0x08 then
    let nextCommand := overlayWord32 (state.command &&& 0xffff) (offset - 0x04) widthNat value &&& 0xffff
    .ok { state with command := nextCommand }
  else if offset >= 0x10 && offset + widthNat <= 0x14 then
    let nextBarValue :=
      overlayWord32 (state.bar0Base &&& virtioPciBarMemoryMask) (offset - 0x10) widthNat value
    if nextBarValue == 0xffffffff then
      .ok { state with bar0Sizing := true }
    else
      .ok {
        state with
        bar0Base := nextBarValue &&& virtioPciBarMemoryMask
        bar0Sizing := false
      }
  else
    .ok state

private def decodeConfigDataWindow (state : VirtioPciState) (port : IoPort)
    (width : UInt32) : ErrnoResult (Nat × Nat × Option PciConfigTarget) := do
  let widthNat ← requireWidthNat width
  if port.value.toNat < virtioPciConfigDataPort.value.toNat ||
      port.value.toNat + widthNat > virtioPciConfigDataPort.value.toNat + 4 then
    .error eproto
  else
    let offset := (state.configAddress &&& 0xfc).toNat +
      (port.value.toNat - virtioPciConfigDataPort.value.toNat)
    if offset + widthNat > 256 then
      .error eproto
    else
      .ok (offset, widthNat, configAddressTarget? state.configAddress)

def virtioPciPortRead (state : VirtioPciState) (port : IoPort) (width : UInt32) :
    ErrnoResult (VirtioPciState × UInt32) := do
  if port.value == virtioPciConfigAddressPort.value then
    let widthNat ← requireWidthNat width
    .ok (state, readConfigAddressPort state widthNat)
  else
    let (offset, widthNat, target?) ← decodeConfigDataWindow state port width
    match target? with
    | some target => .ok (state, readConfigWindow state target offset widthNat)
    | none => .ok (state, allOnesForWidth widthNat)

def virtioPciPortWrite (state : VirtioPciState) (port : IoPort) (width : UInt32)
    (value : UInt32) : ErrnoResult VirtioPciState := do
  if port.value == virtioPciConfigAddressPort.value then
    let widthNat ← requireWidthNat width
    .ok (writeConfigAddressPort state widthNat value)
  else
    let (offset, widthNat, target?) ← decodeConfigDataWindow state port width
    match target? with
    | some .virtioRng => writeConfigWindow state offset widthNat value
    | some .hostBridge | none => .ok state

private def barMemoryEnabled (state : VirtioPciState) : Bool :=
  state.bar0Base != 0 && (state.command &&& virtioPciCommandMemorySpace) != 0

private def decodeBarOffset (state : VirtioPciState) (physAddr : MmioPhysAddr)
    (width : UInt32) : ErrnoResult (Nat × Nat) := do
  let widthNat ← requireWidthNat width
  if !barMemoryEnabled state then
    .error eproto
  else
    let base := UInt64.ofNat state.bar0Base.toNat
    let span := UInt64.ofNat widthNat
    let limit := base + UInt64.ofNat state.bar0Size.toNat
    if physAddr.value < base || physAddr.value + span > limit then
      .error eproto
    else
      .ok (physAddr.value.toNat - base.toNat, widthNat)

private def readCommonCfg (state : VirtioPciState) (offset : Nat) (width : UInt32) :
    ErrnoResult UInt32 :=
  let queue := currentQueueRegisters state.device
  if offset == 0x00 && width == 4 then
    .ok state.device.deviceFeaturesSel
  else if offset == 0x04 && width == 4 then
    .ok (deviceFeaturesWord state.device)
  else if offset == 0x08 && width == 4 then
    .ok state.device.driverFeaturesSel
  else if offset == 0x0c && width == 4 then
    .ok (driverFeaturesWord state.device)
  else if offset == 0x10 && width == 2 then
    .ok 0xffff
  else if offset == 0x12 && width == 2 then
    .ok virtioQueueNumMax
  else if offset == 0x14 && width == 1 then
    .ok (state.device.status &&& 0xff)
  else if offset == 0x15 && width == 1 then
    .ok 0
  else if offset == 0x16 && width == 2 then
    .ok (state.device.queueSel &&& 0xffff)
  else if offset == 0x18 && width == 2 then
    .ok (selectedQueueSize state.device &&& 0xffff)
  else if offset == 0x1a && width == 2 then
    .ok 0xffff
  else if offset == 0x1c && width == 2 then
    .ok (queue.ready &&& 0xffff)
  else if offset == 0x1e && width == 2 then
    .ok 0
  else if offset == 0x20 && width == 4 then
    .ok (low32 queue.descAddr)
  else if offset == 0x24 && width == 4 then
    .ok (high32 queue.descAddr)
  else if offset == 0x28 && width == 4 then
    .ok (low32 queue.availAddr)
  else if offset == 0x2c && width == 4 then
    .ok (high32 queue.availAddr)
  else if offset == 0x30 && width == 4 then
    .ok (low32 queue.usedAddr)
  else if offset == 0x34 && width == 4 then
    .ok (high32 queue.usedAddr)
  else if offset == 0x38 && width == 2 then
    .ok 0
  else if offset == 0x3a && width == 2 then
    .ok 0
  else if offset == 0x3c && width == 2 then
    .ok 0
  else if offset == 0x3e && width == 2 then
    .ok 0
  else
    .error eproto

def virtioPciCommonCfgQueueNumWriteDevice (state : VirtioPciState) (value : UInt32) :
    ErrnoResult VirtioDeviceState :=
  writeQueueNum state.device (value &&& 0xffff)

def virtioPciCommonCfgQueueReadyWriteDevice (state : VirtioPciState) (value : UInt32) :
    ErrnoResult VirtioDeviceState :=
  writeQueueReady state.device (value &&& 0xffff)

def virtioPciCommonCfgQueueAddrWriteDevice (state : VirtioPciState) (field : QueueAddrField)
    (value : UInt32) (highHalf : Bool) : ErrnoResult VirtioDeviceState :=
  writeQueueAddr state.device field value highHalf

def virtioPciCommonCfgWriteQueueNum (state : VirtioPciState) (value : UInt32) :
    ErrnoResult (VirtioPciState × MmioWriteAction) := do
  let nextDevice ← virtioPciCommonCfgQueueNumWriteDevice state value
  .ok ({ state with device := nextDevice }, .none)

def virtioPciCommonCfgWriteQueueReady (state : VirtioPciState) (value : UInt32) :
    ErrnoResult (VirtioPciState × MmioWriteAction) := do
  let nextDevice ← virtioPciCommonCfgQueueReadyWriteDevice state value
  .ok ({ state with device := nextDevice }, .none)

def virtioPciCommonCfgWriteQueueAddr (state : VirtioPciState) (field : QueueAddrField)
    (value : UInt32) (highHalf : Bool) : ErrnoResult (VirtioPciState × MmioWriteAction) := do
  let nextDevice ← virtioPciCommonCfgQueueAddrWriteDevice state field value highHalf
  .ok ({ state with device := nextDevice }, .none)

def virtioPciCommonCfgWrite (state : VirtioPciState) (offset : Nat) (width : UInt32)
    (value : UInt32) : ErrnoResult (VirtioPciState × MmioWriteAction) := do
  if offset == 0x00 && width == 4 then
    .ok ({ state with device := setDeviceFeaturesSel state.device value }, .none)
  else if offset == 0x08 && width == 4 then
    .ok ({ state with device := setDriverFeaturesSel state.device value }, .none)
  else if offset == 0x0c && width == 4 then
    .ok ({ state with device := setDriverFeatures state.device value }, .none)
  else if offset == 0x10 && width == 2 then
    .ok (state, .none)
  else if offset == 0x14 && width == 1 then
    let nextDevice ← handleStatusWrite state.device value
    .ok ({ state with device := nextDevice }, .none)
  else if offset == 0x16 && width == 2 then
    let nextDevice ← writeQueueSel state.device (value &&& 0xffff)
    .ok ({ state with device := nextDevice }, .none)
  else if offset == 0x18 && width == 2 then
    virtioPciCommonCfgWriteQueueNum state value
  else if offset == 0x1a && width == 2 then
    .ok (state, .none)
  else if offset == 0x1c && width == 2 then
    virtioPciCommonCfgWriteQueueReady state value
  else if offset == 0x20 && width == 4 then
    virtioPciCommonCfgWriteQueueAddr state .desc value false
  else if offset == 0x24 && width == 4 then
    virtioPciCommonCfgWriteQueueAddr state .desc value true
  else if offset == 0x28 && width == 4 then
    virtioPciCommonCfgWriteQueueAddr state .avail value false
  else if offset == 0x2c && width == 4 then
    virtioPciCommonCfgWriteQueueAddr state .avail value true
  else if offset == 0x30 && width == 4 then
    virtioPciCommonCfgWriteQueueAddr state .used value false
  else if offset == 0x34 && width == 4 then
    virtioPciCommonCfgWriteQueueAddr state .used value true
  else if offset == 0x38 && width == 2 then
    .ok (state, .none)
  else if offset == 0x3a && width == 2 then
    .ok (state, .none)
  else
    .error eproto

def virtioPciBarRead (state : VirtioPciState) (physAddr : MmioPhysAddr) (width : UInt32) :
    ErrnoResult (VirtioPciState × UInt32) := do
  let (offset, widthNat) ← decodeBarOffset state physAddr width
  if offset + widthNat <= virtioPciCommonCfgLength.toNat then
    .ok (state, ← readCommonCfg state offset width)
  else if offset == virtioPciNotifyCfgOffset.toNat && widthNat <= virtioPciNotifyCfgLength.toNat then
    .ok (state, 0)
  else if offset == virtioPciIsrCfgOffset.toNat && width == 1 then
    let response := state.device.interruptStatus &&& 0xff
    let nextDevice := { state.device with interruptStatus := state.device.interruptStatus &&& (0xffffff00 : UInt32) }
    .ok ({ state with device := nextDevice }, response)
  else if offset >= virtioPciDeviceCfgOffset.toNat &&
      offset + widthNat <= virtioPciDeviceCfgOffset.toNat + virtioPciDeviceCfgLength.toNat then
    .ok (state, 0)
  else
    .error eproto

/-- Proof-facing decoded BAR write entry point: once BAR decoding succeeds, transport behavior is
just this offset-and-width case split plus the notify action. -/
def virtioPciBarWriteOffset (state : VirtioPciState) (offset widthNat : Nat) (width : UInt32)
    (value : UInt32) : ErrnoResult (VirtioPciState × MmioWriteAction) := do
  if offset + widthNat <= virtioPciCommonCfgLength.toNat then
    virtioPciCommonCfgWrite state offset width value
  else if offset == virtioPciNotifyCfgOffset.toNat &&
      (width == 2 || width == 4) then
    if value != 0 then
      .error eproto
    else
      .ok ({ state with device := (← markQueueNotified state.device) }, .processQueue)
  else if offset >= virtioPciDeviceCfgOffset.toNat &&
      offset + widthNat <= virtioPciDeviceCfgOffset.toNat + virtioPciDeviceCfgLength.toNat then
    .ok (state, .none)
  else
    .error eproto

def virtioPciBarWrite (state : VirtioPciState) (physAddr : MmioPhysAddr) (width : UInt32)
    (value : UInt32) : ErrnoResult (VirtioPciState × MmioWriteAction) := do
  let (offset, widthNat) ← decodeBarOffset state physAddr width
  virtioPciBarWriteOffset state offset widthNat width value

end Microvmm