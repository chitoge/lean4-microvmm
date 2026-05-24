import Microvmm.Proof.Virtio.Core

namespace Microvmm

/-- Firecracker CVE-2026-5747 relied on post-activation writes to `queue_size` changing the live
virtqueue after the initial bounds check. In this core, any successful post-activation
`queue_size` write preserves the live and latched queue states, so the mutated size cannot retarget
request processing. -/
theorem cve_2026_5747_queueNum_postActivation_safe (device : VirtioDeviceState)
    (value : UInt32) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : writeQueueNum device value = .ok next) :
    queueConfigLatched next := by
  exact preservesLiveQueue_keeps_queueConfigLatched
    (writeQueueNum_preservesLiveQueue_whenActive device value hActive hWrite) hLatched

/-- The same argument applies to later `queue_ready` rewrites: once activation has happened, the
guest can only change diagnostic shadow state, not the queue used for execution. -/
theorem cve_2026_5747_queueReady_postActivation_safe (device : VirtioDeviceState)
    (value : UInt32) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : writeQueueReady device value = .ok next) :
    queueConfigLatched next := by
  exact preservesLiveQueue_keeps_queueConfigLatched
    (writeQueueReady_preservesLiveQueue_whenActive device value hActive hWrite) hLatched

/-- The advisory describes post-activation mutation of queue configuration registers in general;
address-field rewrites are also blocked semantically because they preserve the live latched queue
invariant. -/
theorem cve_2026_5747_queueAddr_postActivation_safe (device : VirtioDeviceState)
    (field : QueueAddrField) (value : UInt32) (highHalf : Bool) {next : VirtioDeviceState}
    (hActive : device.activeQueue.isSome)
    (hLatched : queueConfigLatched device)
    (hWrite : writeQueueAddr device field value highHalf = .ok next) :
    queueConfigLatched next := by
  exact preservesLiveQueue_keeps_queueConfigLatched
    (writeQueueAddr_preservesLiveQueue_whenActive device field value highHalf hActive hWrite) hLatched

end Microvmm