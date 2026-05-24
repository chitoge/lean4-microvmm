import Microvmm.Kvm.VcpuSetup
import Microvmm.Device.Virtio.Core
import Microvmm.Device.Virtio.Rng

namespace Microvmm

open Kvm

private def virtioGuestMemorySize : UInt64 := 4 * 1024 * 1024

private def virtioProbeResultAddr : UInt64 := 0x00014000

private def virtioMmioBase : UInt64 := 0x0d000000

private def virtioMmioSize : UInt64 := 0x1000

private def virtioMmioMagicValue : UInt32 := 0x74726976

private def virtioMmioVersion : UInt32 := 0x2

private def virtioEntropyDeviceId : UInt32 := 0x4

private def virtioVendorId : UInt32 := 0x4d564d4d

private def virtioQueueDescAddr : UInt64 := 0x00010000

private def virtioQueueAvailAddr : UInt64 := 0x00011000

private def virtioQueueUsedAddr : UInt64 := 0x00012000

private def virtioBogusDescAddr : UInt64 := 0x00020000

private def virtioBogusAvailAddr : UInt64 := 0x00021000

private def virtioBogusUsedAddr : UInt64 := 0x00022000

private def virtioMaxKvmExits : Nat := 256

private def virtioRegMagicValue : Nat := 0x000

private def virtioRegVersion : Nat := 0x004

private def virtioRegDeviceId : Nat := 0x008

private def virtioRegVendorId : Nat := 0x00c

private def virtioRegDeviceFeatures : Nat := 0x010

private def virtioRegDeviceFeaturesSel : Nat := 0x014

private def virtioRegDriverFeatures : Nat := 0x020

private def virtioRegDriverFeaturesSel : Nat := 0x024

private def virtioRegQueueSel : Nat := 0x030

private def virtioRegQueueNumMax : Nat := 0x034

private def virtioRegQueueNum : Nat := 0x038

private def virtioRegQueueReady : Nat := 0x044

private def virtioRegQueueNotify : Nat := 0x050

private def virtioRegInterruptStatus : Nat := 0x060

private def virtioRegInterruptAck : Nat := 0x064

private def virtioRegStatus : Nat := 0x070

private def virtioRegQueueDescLow : Nat := 0x080

private def virtioRegQueueDescHigh : Nat := 0x084

private def virtioRegQueueDriverLow : Nat := 0x090

private def virtioRegQueueDriverHigh : Nat := 0x094

private def virtioRegQueueDeviceLow : Nat := 0x0a0

private def virtioRegQueueDeviceHigh : Nat := 0x0a4

private def virtioRegConfigGeneration : Nat := 0x0fc

private def virtioGuestResultSuccess : UInt32 := 0

private def kvmExitHlt : UInt32 := 5

private def kvmExitMmio : UInt32 := 6

def virtioMmioKvmExitHlt : UInt32 := kvmExitHlt

def virtioMmioKvmExitMmio : UInt32 := kvmExitMmio

private def decodeVirtioMmioOffset (physAddr : MmioPhysAddr) (len : UInt32) : ErrnoResult Nat :=
  let len64 := UInt64.ofNat len.toNat
  if len != 4 then
    .error eproto
  else if physAddr.value < virtioMmioBase then
    .error eproto
  else if physAddr.value > virtioMmioBase + virtioMmioSize - len64 then
    .error eproto
  else
    .ok (physAddr.value.toNat - virtioMmioBase.toNat)

def virtioMmioRead (device : VirtioDeviceState) (physAddr : MmioPhysAddr) (len : UInt32) :
    ErrnoResult UInt32 := do
  let queue := currentQueueRegisters device
  let offset ← decodeVirtioMmioOffset physAddr len
  if offset == virtioRegMagicValue then
    pure virtioMmioMagicValue
  else if offset == virtioRegVersion then
    pure virtioMmioVersion
  else if offset == virtioRegDeviceId then
    pure virtioEntropyDeviceId
  else if offset == virtioRegVendorId then
    pure virtioVendorId
  else if offset == virtioRegDeviceFeatures then
    pure (deviceFeaturesWord device)
  else if offset == virtioRegDeviceFeaturesSel then
    pure device.deviceFeaturesSel
  else if offset == virtioRegDriverFeatures then
    pure (driverFeaturesWord device)
  else if offset == virtioRegDriverFeaturesSel then
    pure device.driverFeaturesSel
  else if offset == virtioRegQueueSel then
    pure device.queueSel
  else if offset == virtioRegQueueNumMax then
    if device.queueSel == 0 then pure virtioQueueNumMax else pure 0
  else if offset == virtioRegQueueNum then
    pure queue.num
  else if offset == virtioRegQueueReady then
    pure queue.ready
  else if offset == virtioRegInterruptStatus then
    pure device.interruptStatus
  else if offset == virtioRegStatus then
    pure device.status
  else if offset == virtioRegQueueDescLow then
    pure (low32 queue.descAddr)
  else if offset == virtioRegQueueDescHigh then
    pure (high32 queue.descAddr)
  else if offset == virtioRegQueueDriverLow then
    pure (low32 queue.availAddr)
  else if offset == virtioRegQueueDriverHigh then
    pure (high32 queue.availAddr)
  else if offset == virtioRegQueueDeviceLow then
    pure (low32 queue.usedAddr)
  else if offset == virtioRegQueueDeviceHigh then
    pure (high32 queue.usedAddr)
  else if offset == virtioRegConfigGeneration then
    pure 0
  else
    pure 0

def virtioMmioQueueNumWriteDevice (device : VirtioDeviceState) (value : UInt32) :
    ErrnoResult VirtioDeviceState :=
  writeQueueNum device value

def virtioMmioQueueReadyWriteDevice (device : VirtioDeviceState) (value : UInt32) :
    ErrnoResult VirtioDeviceState :=
  writeQueueReady device value

def virtioMmioQueueAddrWriteDevice (device : VirtioDeviceState) (field : QueueAddrField)
    (value : UInt32) (highHalf : Bool) : ErrnoResult VirtioDeviceState :=
  writeQueueAddr device field value highHalf

def virtioMmioWriteQueueNum (device : VirtioDeviceState) (value : UInt32) :
    ErrnoResult (VirtioDeviceState × MmioWriteAction) := do
  pure ((← virtioMmioQueueNumWriteDevice device value), .none)

def virtioMmioWriteQueueReady (device : VirtioDeviceState) (value : UInt32) :
    ErrnoResult (VirtioDeviceState × MmioWriteAction) := do
  pure ((← virtioMmioQueueReadyWriteDevice device value), .none)

def virtioMmioWriteQueueAddr (device : VirtioDeviceState) (field : QueueAddrField)
    (value : UInt32) (highHalf : Bool) : ErrnoResult (VirtioDeviceState × MmioWriteAction) := do
  pure ((← virtioMmioQueueAddrWriteDevice device field value highHalf), .none)

/-- Proof-facing decoded MMIO write entry point: once address validation chooses an offset, the
remaining transport behavior is exactly this case split. -/
def virtioMmioWriteOffset (device : VirtioDeviceState) (offset : Nat) (value : UInt32) :
    ErrnoResult (VirtioDeviceState × MmioWriteAction) := do
  if offset == virtioRegDeviceFeaturesSel then
    pure (setDeviceFeaturesSel device value, .none)
  else if offset == virtioRegDriverFeaturesSel then
    if value > 1 then
      .error eproto
    else
      pure (setDriverFeaturesSel device value, .none)
  else if offset == virtioRegDriverFeatures then
    pure (setDriverFeatures device value, .none)
  else if offset == virtioRegQueueSel then
    pure ((← writeQueueSel device value), .none)
  else if offset == virtioRegQueueNum then
    virtioMmioWriteQueueNum device value
  else if offset == virtioRegQueueReady then
    virtioMmioWriteQueueReady device value
  else if offset == virtioRegQueueNotify then
    if value != 0 then
      .error eproto
    else
      pure ((← markQueueNotified device), .processQueue)
  else if offset == virtioRegInterruptAck then
    pure (acknowledgeInterruptStatus device value, .none)
  else if offset == virtioRegStatus then
    pure ((← handleStatusWrite device value), .none)
  else if offset == virtioRegQueueDescLow then
    virtioMmioWriteQueueAddr device .desc value false
  else if offset == virtioRegQueueDescHigh then
    virtioMmioWriteQueueAddr device .desc value true
  else if offset == virtioRegQueueDriverLow then
    virtioMmioWriteQueueAddr device .avail value false
  else if offset == virtioRegQueueDriverHigh then
    virtioMmioWriteQueueAddr device .avail value true
  else if offset == virtioRegQueueDeviceLow then
    virtioMmioWriteQueueAddr device .used value false
  else if offset == virtioRegQueueDeviceHigh then
    virtioMmioWriteQueueAddr device .used value true
  else
    .error eproto

def virtioMmioWrite (device : VirtioDeviceState) (physAddr : MmioPhysAddr) (len : UInt32)
    (value : UInt32) : ErrnoResult (VirtioDeviceState × MmioWriteAction) := do
  let offset ← decodeVirtioMmioOffset physAddr len
  virtioMmioWriteOffset device offset value

def stepVirtioMmioAccess (device : VirtioDeviceState) (access : MmioAccess) :
  ErrnoResult (MmioStep VirtioDeviceState) := do
  match access.direction with
  | .read =>
      let value ← virtioMmioRead device access.address access.width
      pure { state := device, response := some value }
  | .write =>
      let (nextDevice, action) ← virtioMmioWrite device access.address access.width access.value
      pure { state := nextDevice, action := action }

private def validateVirtioQueueState (guestMemory : GuestMemory) (device : VirtioDeviceState) :
    IO (Result Unit) := do
  let expectedStatus := virtioStatusAcknowledge ||| virtioStatusDriver |||
    virtioStatusDriverOk ||| virtioStatusFeaturesOk
  match device.activeQueue, device.latchedQueue with
  | some activeQueue, some latchedQueue =>
      if !device.resetSeen || !device.featuresOkAccepted || !device.driverOkSeen ||
          !device.notifySeen || !device.requestCompleted || !device.mutationAttempted ||
          !device.mutationIgnored || device.status != expectedStatus ||
          !queueConfigEquals activeQueue latchedQueue || activeQueue.num != 1 ||
          activeQueue.descAddr.value != virtioQueueDescAddr ||
          activeQueue.availAddr.value != virtioQueueAvailAddr ||
          activeQueue.usedAddr.value != virtioQueueUsedAddr ||
          device.attemptedQueue.num != 2 ||
          device.attemptedQueue.descAddr != virtioBogusDescAddr ||
          device.attemptedQueue.availAddr != virtioBogusAvailAddr ||
          device.attemptedQueue.usedAddr != virtioBogusUsedAddr then
        pure (.error ⟨.verifyQueueState, eproto⟩)
      else
        match ← guestReadU16 .verifyQueueState guestMemory (virtioBogusUsedAddr + 2) with
        | .error err =>
            pure (.error err)
        | .ok bogusUsedIdx =>
            if bogusUsedIdx == 0 then pure (.ok ()) else pure (.error ⟨.verifyQueueState, eproto⟩)
  | _, _ =>
      pure (.error ⟨.verifyQueueState, eproto⟩)

def handleVirtioMmioAccess (runArea : RunArea) (guestMemory : GuestMemory)
    (device : VirtioDeviceState) (access : MmioAccess) : IO (Result VirtioDeviceState) := do
  match stepVirtioMmioAccess device access with
  | .error errno =>
      pure (.error ⟨.verifyMmioExit, errno⟩)
  | .ok step =>
      match step.response with
      | some value =>
          match ← setRunMmioDataU32 runArea value with
          | .error err =>
              pure (.error err)
          | .ok () =>
              pure (.ok step.state)
      | none =>
          match step.action with
          | .none =>
              pure (.ok step.state)
          | .processQueue =>
            completeDeterministicEntropyRequest guestMemory step.state

def handleVirtioMmioExit (runArea : RunArea) (guestMemory : GuestMemory)
    (device : VirtioDeviceState) : IO (Result VirtioDeviceState) := do
  let access ← readMmioAccess runArea
  handleVirtioMmioAccess runArea guestMemory device access

def runVirtioEntropyLoop (remaining : Nat) (vcpu : Vcpu) (runArea : RunArea)
    (guestMemory : GuestMemory) (device : VirtioDeviceState) : IO (Result Unit) := do
  match remaining with
  | 0 =>
      pure (.error ⟨.verifyGuestResult, etimedout⟩)
  | remaining + 1 =>
      match ← runGuestOnce vcpu with
      | .error err =>
          pure (.error err)
      | .ok () =>
          let exitReason ← runExitReason runArea
          if exitReason == kvmExitMmio then
            match ← handleVirtioMmioExit runArea guestMemory device with
            | .error err =>
                pure (.error err)
            | .ok nextDevice =>
                runVirtioEntropyLoop remaining vcpu runArea guestMemory nextDevice
          else if exitReason == kvmExitHlt then
            match ← guestReadU32 .verifyGuestResult guestMemory virtioProbeResultAddr with
            | .error err =>
                pure (.error err)
            | .ok guestResultCode =>
                if guestResultCode != virtioGuestResultSuccess then
                  pure (.error ⟨.verifyGuestResult, guestResultCode⟩)
                else
                  validateVirtioQueueState guestMemory device
          else
            pure (.error ⟨.verifyMmioExit, eproto⟩)

def probeVirtioMmioEntropy : IO (Result VirtioEntropySuccess) := do
  withVmContext fun vmContext =>
    withVcpuContext vmContext defaultVcpuId fun vcpuContext =>
      withGuestMemory virtioGuestMemorySize fun guestMemory =>
        bindIOResult (prepareVirtioMmioEntropyGuest guestMemory) fun _ =>
          withRegisteredGuestMemory vcpuContext.vm 0 0 guestMemory do
            bindIOResult (configureVirtioMmioEntropyVcpu vcpuContext) fun _ =>
              withMappedRunArea vcpuContext.vcpu vcpuContext.runAreaSize fun runArea =>
                mapIOResult
                  (runVirtioEntropyLoop virtioMaxKvmExits vcpuContext.vcpu runArea guestMemory (resetVirtioDevice false))
                  fun _ => ⟨vcpuContext.apiVersion, vcpuContext.runAreaSize, virtioPayloadSummary⟩

end Microvmm