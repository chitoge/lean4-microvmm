import Microvmm.Device.Virtio.Core

namespace Microvmm

/-- Proof-facing safety cut from the transport-agnostic virtio core: once a queue has been
activated, request execution must consult the latched queue rather than any later guest rewrites of
the queue registers. -/
def queueConfigLatched (device : VirtioDeviceState) : Prop :=
  device.activeQueue = device.latchedQueue

/-- A queue-register write is execution-safe when it leaves the live queue and the latched queue
unchanged. This is the minimal semantic contract needed for the post-activation mutation argument
behind CVE-2026-5747. -/
def preservesLiveQueue (before after : VirtioDeviceState) : Prop :=
  after.activeQueue = before.activeQueue ∧ after.latchedQueue = before.latchedQueue

end Microvmm