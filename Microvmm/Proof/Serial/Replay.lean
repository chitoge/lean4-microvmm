import Microvmm.Host.SerialModel

namespace Microvmm

private theorem byteArrayFoldlPushSize (items : List α) (f : α → UInt8) (bytes : ByteArray) :
    (items.foldl (fun acc item => acc.push (f item)) bytes).size = bytes.size + items.length := by
  induction items generalizing bytes with
  | nil =>
      simp
  | cons head tail ih =>
      simp [List.foldl, ih, Nat.add_left_comm, Nat.add_comm]

/-- Replay capture stays within its configured tail bound, so late-attach console proofs only need
the abstract capacity and not the byte-array slicing details. -/
theorem SerialReplayBuffer.pushBounded_size_le (buffer : SerialReplayBuffer)
    (capacity : Nat) (byteValue : UInt32) :
    (buffer.pushBounded capacity byteValue).bytes.size <= capacity := by
  by_cases h : buffer.bytes.size + 1 <= capacity
  · simp [SerialReplayBuffer.pushBounded, h]
  · simp [SerialReplayBuffer.pushBounded, h, byteArrayFoldlPushSize]

/-- `toOutputBytes` is the list-facing view of the exact replay buffer contents, which lets later
proofs move between queue/list invariants and the byte-array storage without reindexing. -/
theorem SerialReplayBuffer.toOutputBytes_length (buffer : SerialReplayBuffer) :
    buffer.toOutputBytes.length = buffer.bytes.size := by
  unfold SerialReplayBuffer.toOutputBytes
  simp

end Microvmm