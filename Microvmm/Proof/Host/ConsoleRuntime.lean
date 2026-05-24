import Microvmm.Host.ConsoleRuntime

namespace Microvmm

/-- A successful pure queue step keeps the per-client backlog within the configured cap, so later
runtime proofs can treat the guard as the only source of output backpressure. -/
theorem queueConsoleClientOutput_pendingOutput_bounded (clientState : ConsoleClientRuntime)
    (byteValue : UInt32) {queuedClient : ConsoleClientRuntime}
    (hQueued : queueConsoleClientOutput clientState byteValue = some queuedClient) :
    queuedClient.pendingOutput.length <= consoleClientOutputCapacity := by
  by_cases hCapacity : clientState.pendingOutput.length < consoleClientOutputCapacity
  · simp [queueConsoleClientOutput, hCapacity] at hQueued
    cases hQueued
    simpa [Nat.succ_eq_add_one] using Nat.succ_le_of_lt hCapacity
  · simp [queueConsoleClientOutput, hCapacity] at hQueued

/-- Late attachment appends exactly one runtime client entry, isolating structural growth from the
separate replay-seeding argument. -/
theorem attachConsoleServerClient_clients_length (runtime : ConsoleServerRuntime)
    (clientId : ConsoleClientId) (replay : SerialReplayBuffer) :
    (attachConsoleServerClient runtime clientId replay).clients.length = runtime.clients.length + 1 := by
  unfold attachConsoleServerClient
  simp

end Microvmm