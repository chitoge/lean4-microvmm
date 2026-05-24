import Microvmm.Proof.Virtio.Spec

namespace Microvmm

/-- Ignored post-activation queue mutations only update diagnostic bookkeeping, never the live or
latched queue state. -/
theorem noteIgnoredQueueMutation_preservesLiveQueue (device : VirtioDeviceState) :
    preservesLiveQueue device (noteIgnoredQueueMutation device) := by
  cases hLatched : device.latchedQueue <;>
    simp [preservesLiveQueue, noteIgnoredQueueMutation, hLatched]

/-- Any proof that already established `activeQueue = latchedQueue` can carry that invariant across
an execution-safe queue-register write without reopening the device model. -/
theorem preservesLiveQueue_keeps_queueConfigLatched {before after : VirtioDeviceState}
    (hPreserve : preservesLiveQueue before after)
    (hLatched : queueConfigLatched before) :
    queueConfigLatched after := by
  rcases hPreserve with ⟨hActive, hLatchedQueue⟩
  unfold queueConfigLatched at hLatched ⊢
  simpa [hActive, hLatchedQueue] using hLatched

/-- Once a queue is active, later queue-size writes stay in the attempted register shadow and leave
the live queue untouched. -/
theorem writeQueueNum_preservesLiveQueue_whenActive (device : VirtioDeviceState)
    (value : UInt32) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hWrite : writeQueueNum device value = .ok next) :
    preservesLiveQueue device next := by
  by_cases hSel : device.queueSel != 0
  · simp [writeQueueNum, hSel] at hWrite
  · let updatedDevice := { device with attemptedQueue := { device.attemptedQueue with num := value } }
    have hMutation :
        preservesLiveQueue updatedDevice (noteIgnoredQueueMutation updatedDevice) :=
      noteIgnoredQueueMutation_preservesLiveQueue updatedDevice
    simp [updatedDevice, preservesLiveQueue] at hMutation
    simp [writeQueueNum, hSel, hActive] at hWrite
    cases hWrite
    exact hMutation

/-- After activation, a later `QueueReady` write is also diagnostic-only and cannot change the live
queue geometry. -/
theorem writeQueueReady_preservesLiveQueue_whenActive (device : VirtioDeviceState)
    (value : UInt32) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hWrite : writeQueueReady device value = .ok next) :
    preservesLiveQueue device next := by
  by_cases hGuard : device.queueSel != 0 || value > 1
  · simp [writeQueueReady, hGuard] at hWrite
  · let updatedDevice := { device with attemptedQueue := { device.attemptedQueue with ready := value } }
    have hMutation :
        preservesLiveQueue updatedDevice (noteIgnoredQueueMutation updatedDevice) :=
      noteIgnoredQueueMutation_preservesLiveQueue updatedDevice
    simp [updatedDevice, preservesLiveQueue] at hMutation
    simp [writeQueueReady, hGuard, hActive] at hWrite
    cases hWrite
    exact hMutation

/-- Address rewrites after activation are likewise confined to the attempted shadow queue and do
not retarget the queue used for execution. -/
theorem writeQueueAddr_preservesLiveQueue_whenActive (device : VirtioDeviceState)
    (field : QueueAddrField) (value : UInt32) (highHalf : Bool) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hWrite : writeQueueAddr device field value highHalf = .ok next) :
    preservesLiveQueue device next := by
  by_cases hSel : device.queueSel != 0
  · simp [writeQueueAddr, hSel] at hWrite
  · let updatedDevice := {
      device with attemptedQueue := updateQueueAddr device.attemptedQueue field value highHalf }
    have hMutation :
        preservesLiveQueue updatedDevice (noteIgnoredQueueMutation updatedDevice) :=
      noteIgnoredQueueMutation_preservesLiveQueue updatedDevice
    simp [updatedDevice, preservesLiveQueue] at hMutation
    simp [writeQueueAddr, hSel, hActive] at hWrite
    cases hWrite
    exact hMutation

/-- Queue notification only flips the diagnostic notify bit; it does not rewrite the live or
latched queue state used for execution. -/
theorem markQueueNotified_preservesLiveQueue (device : VirtioDeviceState)
    {next : VirtioDeviceState}
    (hWrite : markQueueNotified device = .ok next) :
    preservesLiveQueue device next := by
  unfold markQueueNotified at hWrite
  by_cases hGuard : !device.driverOkSeen || device.activeQueue.isNone
  · simp [hGuard] at hWrite
  · simp [hGuard] at hWrite
    cases hWrite
    simp [preservesLiveQueue]

end Microvmm
