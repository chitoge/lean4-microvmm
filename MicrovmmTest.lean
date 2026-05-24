import Microvmm
import Microvmm.Host

open Microvmm
open Microvmm.Kvm

structure TestCase where
  name : String
  run : IO (List String)

private def noFailures : List String := []

private def fail (name message : String) : List String :=
  [s!"{name}: {message}"]

private def merge (results : List (List String)) : List String :=
  results.foldl (· ++ ·) []

private def zeroBytes : Nat → ByteArray
  | 0 => ByteArray.empty
  | size + 1 => (zeroBytes size).push 0

private def patternedBytes (start size : Nat) : ByteArray :=
  (List.range size).foldl
    (fun bytes offset => bytes.push (UInt8.ofNat ((start + offset) % 256)))
    ByteArray.empty

private def checkEq [BEq α] [Repr α] (name : String) (expected actual : α) : List String :=
  if actual == expected then
    noFailures
  else
    fail name s!"expected {repr expected}, got {repr actual}"

private def checkLinuxBootWrite (name : String) (plan : LinuxBootPlan)
    (kind : LinuxBootWriteKind) (expectedAddr : UInt64)
    (expectedPayload : LinuxBootWritePayload) : List String :=
  match plan.findWrite? kind with
  | none =>
      fail name s!"expected planned write {repr kind}, got none"
  | some actual =>
      merge [
        checkEq (name ++ " addr") expectedAddr actual.addr.value,
        if actual.payload == expectedPayload then
          noFailures
        else
          fail (name ++ " payload") "expected payload to match planned write"
      ]

private def checkTrue (name : String) (condition : Bool) (message : String) : List String :=
  if condition then noFailures else fail name message

private def checkResultError {α : Type} (name : String) (stage : Stage) (errno : UInt32)
    (result : Result α) : List String :=
  match result with
  | .error err =>
      merge [
        checkEq (name ++ " stage") stage err.stage,
        checkEq (name ++ " errno") errno err.errno
      ]
  | .ok _ =>
      fail name s!"expected error ({repr stage}, {repr errno}), got ok"

private def checkTypedOutcomeError {ε α : Type} [DecidableEq ε] [Repr ε]
    (name : String) (expected : ε) (result : Outcome ε α) : List String :=
  match result with
  | .error actual =>
      if actual = expected then
        noFailures
      else
        fail name s!"expected error {repr expected}, got {repr actual}"
  | .ok _ =>
      fail name s!"expected error {repr expected}, got ok"

private def checkErrnoError {α : Type} (name : String) (errno : UInt32)
    (result : ErrnoResult α) : List String :=
  match result with
  | .error actual => checkEq name errno actual
  | .ok _ => fail name s!"expected errno error {repr errno}, got ok"

private def checkResultOk {α : Type} (name : String) (result : Result α) : List String :=
  match result with
  | .ok _ => noFailures
  | .error err => fail name s!"expected ok, got error {repr err}"

private def writeSerialTranscript (console : SerialConsole) (text : String) : Result SerialConsole :=
  text.toList.foldl
    (fun result nextChar =>
      match result with
      | .error err => .error err
      | .ok nextConsole =>
          match stepSerialConsole nextConsole
              { port := ⟨0x3f8⟩, width := 1, count := 1, direction := .output,
                value := UInt32.ofNat nextChar.toNat } with
          | .error err => .error err
          | .ok step => .ok step.console)
    (.ok console)

private def captureSerialOutput (console : SerialConsole) (text : String) : SerialConsole :=
  text.toList.foldl
    (fun nextConsole nextChar =>
      captureSerialOutputByte nextConsole (UInt32.ofNat nextChar.toNat))
    console

private def expectOk {α : Type} (name : String) (result : ErrnoResult α) : IO (List String × Option α) :=
  match result with
  | .ok value => pure (noFailures, some value)
  | .error err => pure (fail name s!"expected ok, got errno {repr err}", none)

private def diagnosticCases : List (String × Error × String) := [
  ("openDev eperm", ⟨.openDev, 1⟩, "/dev/kvm open denied (EPERM, errno=1): operation not permitted"),
  ("openDev enoent", ⟨.openDev, 2⟩, "/dev/kvm not found (ENOENT, errno=2): device is unavailable on this host"),
  ("openDev eacces", ⟨.openDev, 13⟩, "/dev/kvm open denied (EACCES, errno=13): user lacks read/write access"),
  ("openDev enodev", ⟨.openDev, 19⟩, "/dev/kvm unavailable (ENODEV, errno=19): KVM support is not enabled"),
  ("openDev generic", ⟨.openDev, 22⟩, "/dev/kvm open failed (EINVAL, errno=22)"),
  ("getApiVersion", ⟨.getApiVersion, 9⟩, "KVM_GET_API_VERSION failed (EBADF, errno=9)"),
  ("createVm", ⟨.createVm, 12⟩, "KVM_CREATE_VM failed (ENOMEM, errno=12)"),
  ("createVcpu", ⟨.createVcpu, 22⟩, "KVM_CREATE_VCPU failed (EINVAL, errno=22)"),
  ("getVcpuMmapSize", ⟨.getVcpuMmapSize, 95⟩, "KVM_GET_VCPU_MMAP_SIZE failed (EOPNOTSUPP, errno=95)"),
  ("probeRunArea", ⟨.probeRunArea, 14⟩, "KVM VCPU run-area probe failed (EFAULT, errno=14)"),
  ("openKernelImage enoent", ⟨.openKernelImage, 2⟩, "kernel image open failed (ENOENT, errno=2): expected a Linux bzImage at the requested path"),
  ("openKernelImage generic", ⟨.openKernelImage, 13⟩, "kernel image open failed (EACCES, errno=13)"),
  ("readKernelImage", ⟨.readKernelImage, 5⟩, "kernel image read failed (EIO, errno=5)"),
  ("openInitrdImage enoent", ⟨.openInitrdImage, 2⟩, "initrd image open failed (ENOENT, errno=2): expected an initrd/initramfs image at the requested path"),
  ("openInitrdImage generic", ⟨.openInitrdImage, 13⟩, "initrd image open failed (EACCES, errno=13)"),
  ("readInitrdImage", ⟨.readInitrdImage, 5⟩, "initrd image read failed (EIO, errno=5)"),
  ("pollHostStdin", ⟨.pollHostStdin, 5⟩, "host stdin poll/read failed (EIO, errno=5)"),
  ("writeHostStdout", ⟨.writeHostStdout, 5⟩, "host stdout write failed (EIO, errno=5)"),
  ("openConsoleListener enoent", ⟨.openConsoleListener, 2⟩, "console socket open failed (ENOENT, errno=2): expected the parent directory for the requested socket path to exist"),
  ("openConsoleListener eexist", ⟨.openConsoleListener, 17⟩, "console socket open failed (EEXIST, errno=17): the requested socket path already exists and is not a Unix socket"),
  ("openConsoleListener eaddrinuse", ⟨.openConsoleListener, 98⟩, "console socket open failed (EADDRINUSE, errno=98): another listener is already bound at the requested path"),
  ("acceptConsoleClient", ⟨.acceptConsoleClient, 9⟩, "console client accept failed (EBADF, errno=9)"),
  ("readConsoleClient", ⟨.readConsoleClient, 9⟩, "console client read failed (EBADF, errno=9)"),
  ("writeConsoleClient", ⟨.writeConsoleClient, 9⟩, "console client write failed (EBADF, errno=9)"),
  ("openSerialLog", ⟨.openSerialLog, 5⟩, "serial log open failed (EIO, errno=5)"),
  ("writeSerialLog", ⟨.writeSerialLog, 5⟩, "serial log write failed (EIO, errno=5)"),
  ("writeHostStderr", ⟨.writeHostStderr, 5⟩, "host stderr write failed (EIO, errno=5)"),
  ("enableHostWakeTimer", ⟨.enableHostWakeTimer, 22⟩, "interactive wake timer enable failed (EINVAL, errno=22)"),
  ("disableHostWakeTimer", ⟨.disableHostWakeTimer, 5⟩, "interactive wake timer disable failed (EIO, errno=5)"),
  ("unlinkConsoleSocket", ⟨.unlinkConsoleSocket, 5⟩, "console socket cleanup failed (EIO, errno=5)"),
  ("parseKernelImage eproto", ⟨.parseKernelImage, 71⟩, "kernel image parse failed (EPROTO, errno=71): expected a Linux bzImage with boot protocol >= 2.10, LOAD_HIGH, command-line support, and enough guest RAM for the header-advertised init_size window"),
  ("parseKernelImage generic", ⟨.parseKernelImage, 22⟩, "kernel image parse failed (EINVAL, errno=22)"),
  ("allocGuestMemory", ⟨.allocGuestMemory, 12⟩, "guest memory allocation failed (ENOMEM, errno=12)"),
  ("registerGuestMemory", ⟨.registerGuestMemory, 22⟩, "KVM_SET_USER_MEMORY_REGION failed (EINVAL, errno=22)"),
  ("createIrqChip", ⟨.createIrqChip, 22⟩, "KVM_CREATE_IRQCHIP failed (EINVAL, errno=22)"),
  ("createPit2", ⟨.createPit2, 22⟩, "KVM_CREATE_PIT2 failed (EINVAL, errno=22)"),
  ("setTssAddr", ⟨.setTssAddr, 22⟩, "KVM_SET_TSS_ADDR failed (EINVAL, errno=22)"),
  ("configureCpuid", ⟨.configureCpuid, 22⟩, "KVM CPUID setup failed (EINVAL, errno=22)"),
  ("getSregs", ⟨.getSregs, 9⟩, "KVM_GET_SREGS failed (EBADF, errno=9)"),
  ("setSregs", ⟨.setSregs, 22⟩, "KVM_SET_SREGS failed (EINVAL, errno=22)"),
  ("setRegs", ⟨.setRegs, 22⟩, "KVM_SET_REGS failed (EINVAL, errno=22)"),
  ("mapRunArea", ⟨.mapRunArea, 12⟩, "kvm_run mmap failed (ENOMEM, errno=12)"),
  ("runGuest", ⟨.runGuest, 4⟩, "KVM_RUN failed (errno=4)"),
  ("verifyIoExit eproto", ⟨.verifyIoExit, 71⟩, "guest Linux exit verification failed (EPROTO, errno=71): expected exact one-byte COM1 UART semantics on 0x3f8-0x3ff, bounded 1/2/4-byte passive port IO elsewhere, safe PCI config-data reads on 0xcfc-0xcff, and passive LAPIC MMIO handling on 0xfee00000-0xfee00fff"),
  ("verifyIoExit generic", ⟨.verifyIoExit, 5⟩, "guest Linux exit verification failed (EIO, errno=5)"),
  ("verifyTranscript eproto", ⟨.verifyTranscript, 71⟩, "guest transcript verification failed (EPROTO, errno=71): guest stopped before emitting recognizable Linux serial boot text"),
  ("verifyTranscript timeout", ⟨.verifyTranscript, 110⟩, "guest transcript verification timed out (ETIMEDOUT, errno=110): bounded KVM exit loop ended before Linux serial boot text was observed"),
  ("verifyTranscript generic", ⟨.verifyTranscript, 5⟩, "guest transcript verification failed (EIO, errno=5)"),
  ("verifyInteractiveSession eproto", ⟨.verifyInteractiveSession, 71⟩, "interactive Linux session failed (EPROTO, errno=71): guest halted before the initrd serial console became ready"),
  ("verifyInteractiveSession timeout", ⟨.verifyInteractiveSession, 110⟩, "interactive Linux session timed out (ETIMEDOUT, errno=110): bounded KVM exit loop ended before the initrd serial console became ready or the guest halted cleanly"),
  ("verifyInteractiveSession generic", ⟨.verifyInteractiveSession, 5⟩, "interactive Linux session failed (EIO, errno=5)"),
  ("loadGuestCode eproto", ⟨.loadGuestCode, 71⟩, "guest code setup failed (EPROTO, errno=71): expected the embedded protected-mode virtio-mmio probe image and fixed guest layout to fit inside probe RAM"),
  ("loadGuestCode generic", ⟨.loadGuestCode, 22⟩, "guest code setup failed (EINVAL, errno=22)"),
  ("verifyMmioExit eproto", ⟨.verifyMmioExit, 71⟩, "virtio-mmio exit verification failed (EPROTO, errno=71): expected modern virtio-mmio traffic for one entropy queue and no unexpected register accesses"),
  ("verifyMmioExit generic", ⟨.verifyMmioExit, 5⟩, "virtio-mmio exit verification failed (EIO, errno=5)"),
  ("verifyQueueState eproto", ⟨.verifyQueueState, 71⟩, "virtio queue state verification failed (EPROTO, errno=71): expected queue geometry and addresses to latch at QueueReady and remain unchanged despite later guest rewrites"),
  ("verifyQueueState generic", ⟨.verifyQueueState, 5⟩, "virtio queue state verification failed (EIO, errno=5)"),
  ("verifyGuestResult eproto", ⟨.verifyGuestResult, 71⟩, "guest result verification failed (EPROTO, errno=71): expected one completed entropy request carrying the default seeded host entropy stream"),
  ("verifyGuestResult timeout", ⟨.verifyGuestResult, 110⟩, "guest result verification timed out (ETIMEDOUT, errno=110): guest did not reach seeded virtio-rng completion before the bounded exit budget ended"),
  ("verifyGuestResult generic", ⟨.verifyGuestResult, 5⟩, "guest result verification failed (probe code 5): the embedded virtio-mmio probe guest rejected the observed device behavior"),
  ("unmapRunArea", ⟨.unmapRunArea, 12⟩, "kvm_run munmap failed (ENOMEM, errno=12)"),
  ("unregisterGuestMemory", ⟨.unregisterGuestMemory, 22⟩, "guest memory unregister failed (EINVAL, errno=22)"),
  ("freeGuestMemory", ⟨.freeGuestMemory, 12⟩, "guest memory munmap failed (ENOMEM, errno=12)"),
  ("closeConsoleListener", ⟨.closeConsoleListener, 9⟩, "console listener close failed (EBADF, errno=9)"),
  ("closeConsoleClient", ⟨.closeConsoleClient, 9⟩, "console client close failed (EBADF, errno=9)"),
  ("closeVcpu", ⟨.closeVcpu, 9⟩, "VCPU fd close failed (EBADF, errno=9)"),
  ("closeVm", ⟨.closeVm, 9⟩, "VM fd close failed (EBADF, errno=9)"),
  ("closeDev", ⟨.closeDev, 9⟩, "/dev/kvm close failed (EBADF, errno=9)")
]

private def runDiagnosticTests : IO (List String) := do
  pure <| merge <| diagnosticCases.map fun (name, err, expected) =>
    checkEq name expected (decodeErrno err)

private def runFormattingTests : IO (List String) := do
  pure <| merge [
    checkEq "virtio success format"
      s!"KVM virtio-mmio entropy probe succeeded: API version 12, payload {virtioPayloadSummary}, mmap size 12288 bytes"
      (formatVirtioProbeSuccess { apiVersion := 12, runAreaSize := 12288, payloadSummary := virtioPayloadSummary }),
    checkEq "linux success format"
      "KVM Linux bzImage probe succeeded: API version 12, transcript \"Linux\", mmap size 12288 bytes"
      (formatLinuxProbeSuccess { apiVersion := 12, runAreaSize := 12288, transcriptExcerpt := "Linux" })
  ]

private def configuredQueueDevice : ErrnoResult VirtioDeviceState := do
  let device1 ← writeQueueNum default 1
  let device2 ← writeQueueAddr device1 .desc 0x00010000 false
  let device3 ← writeQueueAddr device2 .avail 0x00011000 false
  let device4 ← writeQueueAddr device3 .used 0x00012000 false
  writeQueueReady device4 1

private def mutatedQueueDevice : ErrnoResult VirtioDeviceState := do
  let device0 ← configuredQueueDevice
  let device1 ← writeQueueNum device0 2
  let device2 ← writeQueueAddr device1 .desc 0x00020000 false
  let device3 ← writeQueueAddr device2 .avail 0x00021000 false
  writeQueueAddr device3 .used 0x00022000 false

private structure VirtioCompletionSnapshot where
  nextDevice : VirtioDeviceState
  report : VirtioEntropyExecutionReport
  payload : List UInt32
  requestLen : UInt32
  usedId : UInt32
  usedLen : UInt32
  usedIdx : UInt32
deriving Repr, DecidableEq

private def readGuestBytes (guestMemory : GuestMemory) (baseAddr : UInt64) (count : Nat) :
    IO (Result (List UInt32)) := do
  match count with
  | 0 =>
      pure (.ok [])
  | count + 1 =>
      bindIOResult (guestReadU8 .verifyMmioExit guestMemory baseAddr) fun byteValue =>
        bindIOResult (readGuestBytes guestMemory (baseAddr + 1) count) fun remaining =>
          pure (.ok (byteValue :: remaining))

private def prepareVirtioCompletionGuestMemory (guestMemory : GuestMemory) (requestLen : UInt32) : IO (Result Unit) := do
  bindIOResult (guestWriteU32 .verifyMmioExit guestMemory 0x00010000 0x00013000) fun _ =>
    bindIOResult (guestWriteU32 .verifyMmioExit guestMemory 0x00010004 0) fun _ =>
      bindIOResult (guestWriteU32 .verifyMmioExit guestMemory 0x00010008 requestLen) fun _ =>
        bindIOResult (guestWriteU16 .verifyMmioExit guestMemory 0x0001000c 2) fun _ =>
          bindIOResult (guestWriteU16 .verifyMmioExit guestMemory 0x0001000e 0) fun _ =>
            bindIOResult (guestWriteU16 .verifyMmioExit guestMemory 0x00011000 0) fun _ =>
              bindIOResult (guestWriteU16 .verifyMmioExit guestMemory 0x00011002 1) fun _ =>
                bindIOResult (guestWriteU16 .verifyMmioExit guestMemory 0x00011004 0) fun _ =>
                  bindIOResult (guestWriteU16 .verifyMmioExit guestMemory 0x00012000 0) fun _ =>
                    guestWriteU16 .verifyMmioExit guestMemory 0x00012002 0

private def captureVirtioCompletionSnapshot (device : VirtioDeviceState) (requestLen : UInt32) :
    IO (Result VirtioCompletionSnapshot) := do
  withGuestMemory (4 * 1024 * 1024) fun guestMemory => do
    bindIOResult (prepareVirtioCompletionGuestMemory guestMemory requestLen) fun _ =>
      bindIOResult (completeDeterministicEntropyRequestWithReport guestMemory device) fun result =>
        let (nextDevice, report) := result
        bindIOResult (readGuestBytes guestMemory 0x00013000 requestLen.toNat) fun payload =>
          bindIOResult (guestReadU32 .verifyMmioExit guestMemory 0x00012004) fun usedId =>
            bindIOResult (guestReadU32 .verifyMmioExit guestMemory 0x00012008) fun usedLen =>
              bindIOResult (guestReadU16 .verifyMmioExit guestMemory 0x00012002) fun usedIdx =>
                pure (.ok { nextDevice, report, payload, requestLen, usedId, usedLen, usedIdx })

private def runVirtioTests : IO (List String) := do
  let configuredResult ← expectOk "virtio queue configure" configuredQueueDevice
  let mutatedResult ← expectOk "virtio queue mutate" mutatedQueueDevice
  let featuresRead0 := virtioMmioRead default ⟨0x0d000010⟩ 4
  let featuresRead1 := virtioMmioRead ({ (default : VirtioDeviceState) with deviceFeaturesSel := 1 }) ⟨0x0d000010⟩ 4
  let featuresRead2 := virtioMmioRead ({ (default : VirtioDeviceState) with deviceFeaturesSel := 2 }) ⟨0x0d000010⟩ 4
  let (prngState1, payload1) := prngNextPayload defaultVirtioEntropyPrngState
  let (prngState2, payload2) := prngNextPayload prngState1
  let longRequestLen : UInt32 := 17
  let (longPrngState, longPayload) := prngGenerateBytes defaultVirtioEntropyPrngState longRequestLen.toNat
  let completionSnapshotResult ←
    match configuredResult with
    | (_, some configured) =>
        some <$> captureVirtioCompletionSnapshot configured longRequestLen
    | _ =>
        pure none
  pure <| merge <| [
    checkErrnoError "validateQueueDraft rejects zero queue" eproto (validateQueueDraft default),
    checkErrnoError "handleStatusWrite rejects DriverOk before FeaturesOk" eproto (handleStatusWrite default 0x04),
    checkErrnoError "virtioMmioRead rejects invalid width" eproto (virtioMmioRead default ⟨0x0d000000⟩ 2),
    checkErrnoError "virtioMmioWrite rejects notify before DriverOk" eproto (virtioMmioWrite default ⟨0x0d000050⟩ 4 0),
    checkEq "virtio feature low word" (.ok 0 : ErrnoResult UInt32) featuresRead0,
    checkEq "virtio feature high word" (.ok 1 : ErrnoResult UInt32) featuresRead1,
    checkEq "virtio feature other selector" (.ok 0 : ErrnoResult UInt32) featuresRead2,
    checkEq "handleStatusWrite accepts FeaturesOk with version1"
      (.ok ({ (default : VirtioDeviceState) with driverFeatures := 0x0000000100000000, featuresOkAccepted := true, status := 0x08 }) : ErrnoResult VirtioDeviceState)
      (handleStatusWrite ({ (default : VirtioDeviceState) with driverFeatures := 0x0000000100000000 }) 0x08),
    checkEq "virtio default seeded payload bytes" ([0x96, 0x6f, 0xa6, 0x57, 0xb7, 0xad, 0x3d, 0x99] : List UInt32) payload1,
    checkEq "virtio default seeded payload" virtioPayload payload1,
    checkEq "virtio prng first request count" 1 prngState1.requestsServed.toNat,
    checkEq "virtio prng second request count" 2 prngState2.requestsServed.toNat,
    checkEq "virtio prng payload length" virtioPayloadLength.toNat payload1.length,
    checkEq "virtio long payload length" longRequestLen.toNat longPayload.length,
    checkEq "virtio long payload first chunk" payload1 (longPayload.take virtioPayloadLength.toNat),
    checkEq "virtio long payload requests served" 3 longPrngState.requestsServed.toNat,
    checkTrue "virtio prng payload changes across requests" (payload2 != payload1)
      s!"expected different payloads, got {payload1} then {payload2}"
  ] ++ match configuredResult with
  | (failures, none) => [failures]
  | (failures, some configured) =>
      [failures,
       merge [
         checkTrue "configured queue active" configured.activeQueue.isSome "expected active queue after QueueReady",
         checkEq "configured queue latched" configured.activeQueue configured.latchedQueue,
         checkEq "configured queue attempted" { num := 1, descAddr := 0x00010000, availAddr := 0x00011000, usedAddr := 0x00012000, ready := 1 } configured.attemptedQueue
       ]] ++ match completionSnapshotResult with
      | none =>
          []
      | some (.error err) =>
          [fail "virtio completion snapshot" s!"expected completion snapshot, got error {repr err}"]
      | some (.ok snapshot) =>
          [merge [
            checkEq "virtio completion payload bytes" longPayload snapshot.payload,
            checkEq "virtio completion report payload bytes"
              longPayload
              (snapshot.report.writes.take longRequestLen.toNat |>.map fun write => write.value),
            checkEq "virtio completion request len" longRequestLen snapshot.requestLen,
            checkEq "virtio completion used id" 0 snapshot.usedId,
            checkEq "virtio completion used len" longRequestLen snapshot.usedLen,
            checkEq "virtio completion used idx" 1 snapshot.usedIdx,
            checkEq "virtio completion next requestCompleted" true snapshot.nextDevice.requestCompleted,
            checkEq "virtio completion next requestsServed" longPrngState.requestsServed.toNat snapshot.nextDevice.prngState.requestsServed.toNat
          ]]
  ++ match mutatedResult with
  | (failures, none) => [failures]
  | (failures, some mutated) =>
      [failures,
       match mutated.activeQueue with
       | none => fail "mutated queue active" "expected latched active queue to remain present"
       | some activeQueue =>
           merge [
             checkEq "mutated active queue desc" 0x00010000 activeQueue.descAddr.value,
             checkEq "mutated active queue avail" 0x00011000 activeQueue.availAddr.value,
             checkEq "mutated active queue used" 0x00012000 activeQueue.usedAddr.value,
             checkEq "mutated attempted queue" { num := 2, descAddr := 0x00020000, availAddr := 0x00021000, usedAddr := 0x00022000, ready := 1 } mutated.attemptedQueue,
             checkEq "mutated queue mutationAttempted" true mutated.mutationAttempted,
             checkEq "mutated queue mutationIgnored" true mutated.mutationIgnored
           ]]

private structure PciCapabilitySummary where
  pointer : UInt32
  capId : UInt32
  next : UInt32
  len : UInt32
  cfgType : UInt32
  bar : UInt32
  regionOffset : UInt32
  regionLength : UInt32
  notifyMultiplier? : Option UInt32 := none
deriving Repr, DecidableEq

private def pciConfigDataPortForOffset (offset : UInt32) : IoPort :=
  ⟨virtioPciConfigDataPort.value + (offset &&& 0x3)⟩

private def readPciConfigValue (state : VirtioPciState) (offset width : UInt32) :
    ErrnoResult (VirtioPciState × UInt32) := do
  let latchedState ←
    virtioPciPortWrite state virtioPciConfigAddressPort 4
      (virtioPciConfigAddressForOffset offset)
  virtioPciPortRead latchedState (pciConfigDataPortForOffset offset) width

private def writePciConfigValue (state : VirtioPciState) (offset width value : UInt32) :
    ErrnoResult VirtioPciState := do
  let latchedState ←
    virtioPciPortWrite state virtioPciConfigAddressPort 4
      (virtioPciConfigAddressForOffset offset)
  virtioPciPortWrite latchedState (pciConfigDataPortForOffset offset) width value

private def bar0Address (state : VirtioPciState) (offset : UInt32) : MmioPhysAddr :=
  ⟨UInt64.ofNat state.bar0Base.toNat + UInt64.ofNat offset.toNat⟩

private def readBar0Value (state : VirtioPciState) (offset width : UInt32) :
    ErrnoResult (VirtioPciState × UInt32) :=
  virtioPciBarRead state (bar0Address state offset) width

private def writeBar0NoAction (state : VirtioPciState) (offset width value : UInt32) :
    ErrnoResult VirtioPciState := do
  let (nextState, action) ← virtioPciBarWrite state (bar0Address state offset) width value
  if action == .none then
    pure nextState
  else
    .error eproto

private def configuredVirtioPciTransport : ErrnoResult VirtioPciState := do
  let state1 ← writePciConfigValue default 0x10 4 0x40000000
  writePciConfigValue state1 0x04 2 0x0002

private def readyVirtioPciDevice : ErrnoResult VirtioPciState := do
  let state0 ← configuredVirtioPciTransport
  let state1 ← writeBar0NoAction state0 (virtioPciCommonCfgOffset + 0x14) 1 0x01
  let state2 ← writeBar0NoAction state1 (virtioPciCommonCfgOffset + 0x14) 1 0x03
  let state3 ← writeBar0NoAction state2 (virtioPciCommonCfgOffset + 0x08) 4 1
  let state4 ← writeBar0NoAction state3 (virtioPciCommonCfgOffset + 0x0c) 4 1
  let state5 ← writeBar0NoAction state4 (virtioPciCommonCfgOffset + 0x14) 1 0x0b
  let state6 ← writeBar0NoAction state5 (virtioPciCommonCfgOffset + 0x16) 2 0
  let state7 ← writeBar0NoAction state6 (virtioPciCommonCfgOffset + 0x18) 2 1
  let state8 ← writeBar0NoAction state7 (virtioPciCommonCfgOffset + 0x20) 4 0x00010000
  let state9 ← writeBar0NoAction state8 (virtioPciCommonCfgOffset + 0x24) 4 0
  let state10 ← writeBar0NoAction state9 (virtioPciCommonCfgOffset + 0x28) 4 0x00011000
  let state11 ← writeBar0NoAction state10 (virtioPciCommonCfgOffset + 0x2c) 4 0
  let state12 ← writeBar0NoAction state11 (virtioPciCommonCfgOffset + 0x30) 4 0x00012000
  let state13 ← writeBar0NoAction state12 (virtioPciCommonCfgOffset + 0x34) 4 0
  let state14 ← writeBar0NoAction state13 (virtioPciCommonCfgOffset + 0x1c) 2 1
  writeBar0NoAction state14 (virtioPciCommonCfgOffset + 0x14) 1 0x0f

private def mutatedVirtioPciDevice : ErrnoResult VirtioPciState := do
  let state0 ← readyVirtioPciDevice
  let state1 ← writeBar0NoAction state0 (virtioPciCommonCfgOffset + 0x18) 2 2
  let state2 ← writeBar0NoAction state1 (virtioPciCommonCfgOffset + 0x20) 4 0x00020000
  let state3 ← writeBar0NoAction state2 (virtioPciCommonCfgOffset + 0x28) 4 0x00021000
  writeBar0NoAction state3 (virtioPciCommonCfgOffset + 0x30) 4 0x00022000

private def byteValueAt32 (value : UInt32) (index : Nat) : UInt32 :=
  UInt32.ofNat ((value.toNat / (Nat.pow 256 index)) % 256)

private def readPciCapabilitySummary (state : VirtioPciState) (pointer : UInt32) :
    ErrnoResult PciCapabilitySummary := do
  let (_, header) ← readPciConfigValue state pointer 4
  let (_, barWord) ← readPciConfigValue state (pointer + 4) 4
  let (_, regionOffset) ← readPciConfigValue state (pointer + 8) 4
  let (_, regionLength) ← readPciConfigValue state (pointer + 12) 4
  let len := byteValueAt32 header 2
  let notifyMultiplier? ←
    if len == 20 then
      match readPciConfigValue state (pointer + 16) 4 with
      | .ok (_, multiplier) => .ok (some multiplier)
      | .error err => .error err
    else
      .ok none
  pure {
    pointer := pointer
    capId := byteValueAt32 header 0
    next := byteValueAt32 header 1
    len := len
    cfgType := byteValueAt32 header 3
    bar := byteValueAt32 barWord 0
    regionOffset := regionOffset
    regionLength := regionLength
    notifyMultiplier? := notifyMultiplier?
  }

private def readPciCapabilityChain (state : VirtioPciState) : ErrnoResult (List PciCapabilitySummary) := do
  let (_, firstPointer) ← readPciConfigValue state 0x34 1
  let rec loop (pointer : UInt32) (remaining : Nat)
      (seen : List PciCapabilitySummary) : ErrnoResult (List PciCapabilitySummary) := do
    if pointer == 0 then
      pure seen.reverse
    else
      match remaining with
      | 0 => .error eproto
      | remaining + 1 =>
          let cap ← readPciCapabilitySummary state pointer
          loop cap.next remaining (cap :: seen)
  loop firstPointer 4 []

private def runVirtioPciTests : IO (List String) := do
  let addressByteWriteResult : ErrnoResult VirtioPciState := do
    let state0 ← virtioPciPortWrite default virtioPciConfigAddressPort 4 0x80000813
    virtioPciPortWrite state0 virtioPciConfigAddressPort 1 0
  let addressByteReadResult : ErrnoResult (VirtioPciState × UInt32) := do
    let state0 ← virtioPciPortWrite default virtioPciConfigAddressPort 4 0x80000813
    virtioPciPortRead state0 virtioPciConfigAddressPort 1
  let identityResult ← expectOk "virtio-pci identity vendor/device" (readPciConfigValue default 0x00 4)
  let statusCommandResult ← expectOk "virtio-pci identity status/command" (readPciConfigValue default 0x04 4)
  let revisionClassResult ← expectOk "virtio-pci identity revision/class" (readPciConfigValue default 0x08 4)
  let subsystemResult ← expectOk "virtio-pci identity subsystem" (readPciConfigValue default 0x2c 4)
  let interruptLineResult ← expectOk "virtio-pci identity interrupt line" (readPciConfigValue default 0x3c 1)
  let interruptPinResult ← expectOk "virtio-pci identity interrupt pin" (readPciConfigValue default 0x3d 1)
  let initialBarResult ← expectOk "virtio-pci initial bar read" (readPciConfigValue default 0x10 4)
  let sizedStateResult ← expectOk "virtio-pci bar size write" (writePciConfigValue default 0x10 4 0xffffffff)
  let capabilityChainResult ← expectOk "virtio-pci capability discovery" (readPciCapabilityChain default)
  let configuredTransportResult ← expectOk "virtio-pci transport configure" configuredVirtioPciTransport
  let readyStateResult ← expectOk "virtio-pci ready flow" readyVirtioPciDevice
  let mutatedStateResult ← expectOk "virtio-pci queue mutation" mutatedVirtioPciDevice
  let commandDecodeResult : ErrnoResult (VirtioPciState × UInt32) := do
    let sizedState ← writePciConfigValue default 0x10 4 0xffffffff
    let programmedState ← writePciConfigValue sizedState 0x10 4 0x40000004
    let commandState ← writePciConfigValue programmedState 0x04 2 0x0002
    readPciConfigValue commandState 0x04 4
  pure <| merge <| [
    checkEq "virtio-pci address port accepts low-byte write"
      (.ok ({ (default : VirtioPciState) with configAddress := 0x80000800 }) : ErrnoResult VirtioPciState)
      addressByteWriteResult,
    checkEq "virtio-pci address port low-byte read"
      (.ok ({ (default : VirtioPciState) with configAddress := 0x80000813 }, 0x13) : ErrnoResult (VirtioPciState × UInt32))
      addressByteReadResult,
    checkEq "virtio-pci config identity vendor/device dword"
      0x10441af4
      (match identityResult with
      | (_, some (_, value)) => value
      | _ => 0),
    checkEq "virtio-pci config identity status/command dword"
      0x00100000
      (match statusCommandResult with
      | (_, some (_, value)) => value
      | _ => 0),
    checkEq "virtio-pci config identity revision/class dword"
      0xff000001
      (match revisionClassResult with
      | (_, some (_, value)) => value
      | _ => 0),
    checkEq "virtio-pci config identity subsystem ids"
      0x00041af4
      (match subsystemResult with
      | (_, some (_, value)) => value
      | _ => 0),
    checkEq "virtio-pci config identity interrupt line"
      0
      (match interruptLineResult with
      | (_, some (_, value)) => value
      | _ => 1),
    checkEq "virtio-pci config identity interrupt pin"
      1
      (match interruptPinResult with
      | (_, some (_, value)) => value
      | _ => 0),
    checkEq "virtio-pci initial bar readback"
      0
      (match initialBarResult with
      | (_, some (_, value)) => value
      | _ => 1)
  ] ++ match sizedStateResult with
  | (failures, none) => [failures]
  | (failures, some sizedState) =>
      [failures,
       merge [
         checkEq "virtio-pci bar size probe mask"
           (.ok (sizedState, 0xfffff000) : ErrnoResult (VirtioPciState × UInt32))
           (readPciConfigValue sizedState 0x10 4),
         checkEq "virtio-pci bar programming readback"
           (.ok ({ sizedState with bar0Base := 0x40000000, bar0Sizing := false }, 0x40000000) : ErrnoResult (VirtioPciState × UInt32))
           (do
             let programmedState ← writePciConfigValue sizedState 0x10 4 0x40000004
             readPciConfigValue programmedState 0x10 4),
         match commandDecodeResult with
         | .error err => fail "virtio-pci command memory decode enable" s!"expected ok, got errno {repr err}"
         | .ok (commandState, value) =>
             merge [
               checkEq "virtio-pci command memory decode value" 0x00100002 value,
               checkEq "virtio-pci command memory decode latch"
                 (virtioPciConfigAddressForOffset 0x04) commandState.configAddress,
               checkEq "virtio-pci command memory decode command" 0x0002 commandState.command,
               checkEq "virtio-pci command memory decode bar0" 0x40000000 commandState.bar0Base,
               checkEq "virtio-pci command memory decode sizing cleared" false commandState.bar0Sizing
             ]
       ]]
  ++ match capabilityChainResult with
  | (failures, none) => [failures]
  | (failures, some caps) =>
      [failures,
       checkEq "virtio-pci capability chain"
         [
           {
             pointer := 0x50
             capId := 0x09
             next := 0x60
             len := 16
             cfgType := 1
             bar := 0
             regionOffset := virtioPciCommonCfgOffset
             regionLength := virtioPciCommonCfgLength
           },
           {
             pointer := 0x60
             capId := 0x09
             next := 0x74
             len := 20
             cfgType := 2
             bar := 0
             regionOffset := virtioPciNotifyCfgOffset
             regionLength := virtioPciNotifyCfgLength
             notifyMultiplier? := some virtioPciNotifyMultiplier
           },
           {
             pointer := 0x74
             capId := 0x09
             next := 0x84
             len := 16
             cfgType := 3
             bar := 0
             regionOffset := virtioPciIsrCfgOffset
             regionLength := virtioPciIsrCfgLength
           },
           {
             pointer := 0x84
             capId := 0x09
             next := 0x00
             len := 16
             cfgType := 4
             bar := 0
             regionOffset := virtioPciDeviceCfgOffset
             regionLength := virtioPciDeviceCfgLength
           }
         ]
         caps]
  ++ match configuredTransportResult with
  | (failures, none) => [failures]
  | (failures, some transportState) =>
      [failures,
       merge [
         checkEq "virtio-pci common cfg feature low word"
           (.ok (transportState, 0) : ErrnoResult (VirtioPciState × UInt32))
           (readBar0Value transportState (virtioPciCommonCfgOffset + 0x04) 4),
         checkEq "virtio-pci common cfg feature high word"
           (.ok ({ transportState with device := { transportState.device with deviceFeaturesSel := 1 } }, 1) : ErrnoResult (VirtioPciState × UInt32))
           (do
             let state1 ← writeBar0NoAction transportState (virtioPciCommonCfgOffset + 0x00) 4 1
             readBar0Value state1 (virtioPciCommonCfgOffset + 0x04) 4)
       ]]
  ++ match readyStateResult with
  | (failures, none) => [failures]
  | (failures, some readyState) =>
      [failures,
       merge [
         checkEq "virtio-pci common cfg features accepted" true readyState.device.featuresOkAccepted,
         checkEq "virtio-pci common cfg driver ok seen" true readyState.device.driverOkSeen,
         checkEq "virtio-pci common cfg final status" 0x0f readyState.device.status,
         checkEq "virtio-pci common cfg queue active" true readyState.device.activeQueue.isSome,
         checkEq "virtio-pci notify returns processQueue"
           (.ok ({ readyState with device := { readyState.device with notifySeen := true } }, .processQueue) : ErrnoResult (VirtioPciState × MmioWriteAction))
           (virtioPciBarWrite readyState (bar0Address readyState virtioPciNotifyCfgOffset) 2 0)
       ]]
  ++ match mutatedStateResult with
  | (failures, none) => [failures]
  | (failures, some mutatedState) =>
      [failures,
       match mutatedState.device.activeQueue with
       | none => fail "virtio-pci queue immutability active queue" "expected latched active queue to remain present"
       | some activeQueue =>
           merge [
             checkEq "virtio-pci queue immutability desc" 0x00010000 activeQueue.descAddr.value,
             checkEq "virtio-pci queue immutability avail" 0x00011000 activeQueue.availAddr.value,
             checkEq "virtio-pci queue immutability used" 0x00012000 activeQueue.usedAddr.value,
             checkEq "virtio-pci queue immutability attempted queue"
               { num := 2, descAddr := 0x00020000, availAddr := 0x00021000, usedAddr := 0x00022000, ready := 1 }
               mutatedState.device.attemptedQueue,
             checkEq "virtio-pci queue immutability mutationAttempted" true mutatedState.device.mutationAttempted,
             checkEq "virtio-pci queue immutability mutationIgnored" true mutatedState.device.mutationIgnored
           ]]
  ++ match configuredTransportResult with
  | (failures, none) => [failures]
  | (failures, some transportState) =>
      [failures,
       checkEq "virtio-pci isr read clears"
         (.ok ({ transportState with device := { transportState.device with interruptStatus := 0 } }, 1) : ErrnoResult (VirtioPciState × UInt32))
         (virtioPciBarRead
           { transportState with device := { transportState.device with interruptStatus := 1 } }
           (bar0Address transportState virtioPciIsrCfgOffset)
           1)]

private def runLinuxTests : IO (List String) := do
  let missingRead ← readHostBinaryFile "missing-bzImage" .openKernelImage .readKernelImage
  let missingInitrdRead ← readHostOptionalBinaryFile (some "missing-initrd") .openInitrdImage .readInitrdImage
  let absentInitrdRead ← readHostOptionalBinaryFile none .openInitrdImage .readInitrdImage
  let presentInitrdRead ← readHostOptionalBinaryFile (some "test-bzImage2") .openInitrdImage .readInitrdImage
  let actualRead ← readHostBinaryFile "test-bzImage2" .openKernelImage .readKernelImage
  let parseResult :=
    match actualRead with
    | .ok bytes => parseBzImageLayout bytes
    | .error err => .error err
  let validateResult :=
    match parseResult with
    | .ok layout => validateLinuxGuestLayout layout
    | .error err => .error err
  let validateCustomCmdlineResult :=
    match parseResult with
    | .ok layout => validateLinuxGuestLayout layout "console=ttyS0,115200 rdinit=/init"
    | .error err => .error err
  let validateInitramfsResult :=
    match parseResult with
    | .ok layout => validateInitramfsLayout layout (zeroBytes 4096)
    | .error err => .error err
  let parseLinuxArgsResult :=
    parseRawLinuxArguments {}
      ["--kernel", "alt-bzImage", "--initrd", "alt-initrd", "--cmdline", "console=ttyS0 rdinit=/init"]
  let expectedRawLinuxArgs : RawLinuxBootArgs :=
    {
      kernelPath := "alt-bzImage"
      commandLineSpec := .explicit "console=ttyS0 rdinit=/init"
      initrdPath? := some "alt-initrd"
    }
  let elaborateProbeLinuxRequestResult :=
    elaborateLinuxBootRequest expectedRawLinuxArgs
  let expectedProbeLinuxRequest : LinuxBootRequest :=
    .probe {
      kernelPath := "alt-bzImage"
      commandLineSpec := .explicit "console=ttyS0 rdinit=/init"
      initrdPath? := some "alt-initrd"
    }
  let parseLinuxArgsMissingInitrdResult := parseRawLinuxArguments {} ["--initrd"]
  let parseLinuxArgsInteractiveResult :=
    parseRawLinuxArguments {} ["--kernel", "alt-bzImage", "--initrd", "alt-initrd", "--interactive"]
  let expectedRawInteractiveLinuxArgs : RawLinuxBootArgs :=
    { kernelPath := "alt-bzImage", initrdPath? := some "alt-initrd", interactive := true }
  let elaborateInteractiveLinuxRequestResult :=
    elaborateLinuxBootRequest expectedRawInteractiveLinuxArgs
  let expectedInteractiveLinuxRequest : LinuxBootRequest :=
    .interactive {
      kernelPath := "alt-bzImage"
      commandLineSpec := .implicitDefault
      initrdPath := "alt-initrd"
      consoleMode := .stdio
    }
  let parseLinuxArgsExplicitStdioResult :=
    parseRawLinuxArguments {}
      ["--kernel", "alt-bzImage", "--initrd", "alt-initrd", "--interactive",
        "--console-transport", "stdio"]
  let expectedRawExplicitStdioLinuxArgs : RawLinuxBootArgs :=
    {
      expectedRawInteractiveLinuxArgs with
      consoleTransport? := some .stdio
    }
  let elaborateInteractiveLinuxExplicitStdioRequestResult :=
    elaborateLinuxBootRequest expectedRawExplicitStdioLinuxArgs
  let expectedExplicitStdioLinuxRequest : LinuxBootRequest := expectedInteractiveLinuxRequest
  let parseLinuxArgsServerResult :=
    parseRawLinuxArguments {}
      ["--kernel", "alt-bzImage", "--initrd", "alt-initrd", "--interactive",
        "--console-socket", "/tmp/microvmm.sock", "--serial-log", "/tmp/microvmm.log"]
  let expectedRawServerLinuxArgs : RawLinuxBootArgs :=
    {
      kernelPath := "alt-bzImage"
      initrdPath? := some "alt-initrd"
      interactive := true
      consoleSocketPath? := some "/tmp/microvmm.sock"
      serialLogPath? := some "/tmp/microvmm.log"
    }
  let elaborateInteractiveLinuxServerRequestResult :=
    elaborateLinuxBootRequest expectedRawServerLinuxArgs
  let expectedServerLinuxRequest : LinuxBootRequest :=
    .interactive {
      kernelPath := "alt-bzImage"
      commandLineSpec := .implicitDefault
      initrdPath := "alt-initrd"
      consoleMode := .server { socketPath := "/tmp/microvmm.sock", serialLogPath := "/tmp/microvmm.log" }
    }
  let parseLinuxArgsExplicitServerResult :=
    parseRawLinuxArguments {}
      ["--kernel", "alt-bzImage", "--initrd", "alt-initrd", "--interactive",
        "--console-transport", "server",
        "--console-socket", "/tmp/microvmm.sock", "--serial-log", "/tmp/microvmm.log"]
  let expectedRawExplicitServerLinuxArgs : RawLinuxBootArgs :=
    {
      expectedRawServerLinuxArgs with
      consoleTransport? := some .server
    }
  let elaborateInteractiveLinuxExplicitServerRequestResult :=
    elaborateLinuxBootRequest expectedRawExplicitServerLinuxArgs
  let expectedExplicitServerLinuxRequest : LinuxBootRequest := expectedServerLinuxRequest
  let parseLinuxArgsMissingTransportValueResult :=
    parseRawLinuxArguments {} ["--console-transport"]
  let parseLinuxArgsUnknownTransportValueResult :=
    parseRawLinuxArguments {} ["--console-transport", "pipe"]
  let parseLinuxArgsUnknownTransportValueTypedResult :=
    parseRawLinuxArgumentsTyped {} ["--console-transport", "pipe"]
  let parseLinuxArgsExplicitInteractiveCmdlineResult :=
    parseRawLinuxArguments {}
      ["--kernel", "alt-bzImage", "--initrd", "alt-initrd", "--interactive",
        "--cmdline", "console=ttyS0 rdinit=/init"]
  let expectedRawExplicitInteractiveCmdlineArgs : RawLinuxBootArgs :=
    {
      kernelPath := "alt-bzImage"
      commandLineSpec := .explicit "console=ttyS0 rdinit=/init"
      initrdPath? := some "alt-initrd"
      interactive := true
    }
  let elaborateInteractiveLinuxExplicitCmdlineRequestResult :=
    elaborateLinuxBootRequest expectedRawExplicitInteractiveCmdlineArgs
  let expectedExplicitInteractiveCmdlineRequest : LinuxBootRequest :=
    .interactive {
      kernelPath := "alt-bzImage"
      commandLineSpec := .explicit "console=ttyS0 rdinit=/init"
      initrdPath := "alt-initrd"
      consoleMode := .stdio
    }
  let elaborateLinuxRequestMissingInitrdResult :=
    elaborateLinuxBootRequest { kernelPath := "alt-bzImage", interactive := true }
  let elaborateLinuxRequestMissingServerLogResult :=
    elaborateLinuxBootRequest {
      kernelPath := "alt-bzImage"
      initrdPath? := some "alt-initrd"
      interactive := true
      consoleSocketPath? := some "/tmp/microvmm.sock"
    }
  let elaborateLinuxRequestExplicitServerMissingPathsResult :=
    elaborateLinuxBootRequest {
      kernelPath := "alt-bzImage"
      initrdPath? := some "alt-initrd"
      interactive := true
      consoleTransport? := some .server
    }
  let elaborateLinuxRequestExplicitStdioWithServerOptionsResult :=
    elaborateLinuxBootRequest {
      expectedRawExplicitStdioLinuxArgs with
      consoleSocketPath? := some "/tmp/microvmm.sock"
      serialLogPath? := some "/tmp/microvmm.log"
    }
  let elaborateLinuxRequestMissingInteractiveServerResult :=
    elaborateLinuxBootRequest {
      kernelPath := "alt-bzImage"
      initrdPath? := some "alt-initrd"
      consoleSocketPath? := some "/tmp/microvmm.sock"
      serialLogPath? := some "/tmp/microvmm.log"
    }
  let elaborateLinuxRequestMissingInteractiveTransportResult :=
    elaborateLinuxBootRequest {
      kernelPath := "alt-bzImage"
      consoleTransport? := some .stdio
    }
  let elaborateLinuxRequestMissingInitrdTypedResult :=
    elaborateLinuxBootRequestTyped { kernelPath := "alt-bzImage", interactive := true }
  let sampleLayout : BzImageLayout := {
    headerCopySize := 0
    setupBytes := 0
    kernelBytes := 0
    protocol := 0x020a
    cmdlineSize := 255
    loadFlags := 1
    runtimeStart := 0x00100000
    runtimeWindowEnd := 0x00300000
    initrdAddrMax := 0x03ffffff
  }
  let samplePlanLayout : BzImageLayout := {
    sampleLayout with
    headerCopySize := 0x20
    setupBytes := 0x220
    kernelBytes := 0x40
    loadFlags := 0x21
  }
  let samplePlanCommandLine := "console=ttyS0,115200 rdinit=/init"
  let samplePlanImageBytes := patternedBytes 0x10 0x260
  let samplePlanInitramfsBytes := patternedBytes 0x80 4096
  let samplePlanResult : Result (LinuxBootInputs × LinuxBootPlan) :=
    match validateLinuxBootInputs samplePlanLayout samplePlanCommandLine (some samplePlanInitramfsBytes) with
    | .error err => .error err
    | .ok bootInputs => .ok (bootInputs, buildLinuxBootPlan samplePlanImageBytes samplePlanLayout bootInputs)
  let expectedSamplePlanWriteKinds : List LinuxBootWriteKind := [
    .kernelImage,
    .bootParamsHeader,
    .initramfsImage,
    .bootFlagSentinel,
    .typeOfLoader,
    .loadFlags,
    .heapEndPtr,
    .code32Start,
    .ramdiskImage,
    .ramdiskSize,
    .cmdLinePtr,
    .extCmdLinePtr,
    .extRamdiskImage,
    .extRamdiskSize,
    .altMemK,
    .e820EntryCount,
    .screenInfoExtMemK,
    .screenInfoVideoMode,
    .screenInfoVideoCols,
    .screenInfoVideoLines,
    .screenInfoVideoIsVga,
    .screenInfoVideoPoints,
    .e820Entry 0,
    .e820Entry 1,
    .e820Entry 2,
    .commandLine,
    .gdtEntry 2,
    .gdtEntry 3
  ]
  let validateBootInputsResult :=
    validateLinuxBootInputs sampleLayout defaultLinuxBootCommandLine (some (zeroBytes 4096))
  let oversizedCommandLine := String.ofList (List.replicate 255 'x')
  let validateLinuxGuestLayoutTypedResult :=
    validateLinuxGuestLayoutTyped sampleLayout oversizedCommandLine
  let tightInitrdLimitLayout : BzImageLayout :=
    { sampleLayout with initrdAddrMax := 0x002fffff }
  let guestOverflowLayout : BzImageLayout :=
    { sampleLayout with runtimeWindowEnd := 64 * 1024 * 1024 - 2048 }
  let highAddressPointers :=
    linuxBootParamsPointers ⟨0x0000000100020000⟩
      (some { loadAddr := ⟨0x0000000123456000⟩, size := 0x0000000200003000 })
  let probeReadyConsole :=
    captureSerialOutput ({ } : SerialConsole) "Linux"
  let interactiveReadyConsole :=
    captureSerialOutput ({ } : SerialConsole) "boot\nMICROVMM_INITRD_READY\n"
  let unrelatedInteractiveConsole :=
    captureSerialOutput ({ } : SerialConsole) "boot\nLinux\n"
  let decompressingConsole :=
    captureSerialOutput ({ } : SerialConsole) "Decompressing Linux..."
  let bootingConsole :=
    captureSerialOutput ({ } : SerialConsole) "Booting the kernel"
  let unrelatedProbeConsole :=
    captureSerialOutput ({ } : SerialConsole) "hello"
  let serialResult :=
    stepSerialConsole (captureSerialOutput ({ } : SerialConsole) "Linu")
      { port := ⟨0x3f8⟩, width := 1, count := 1, direction := .output, value := UInt32.ofNat 'x'.toNat }
  let queuedSerialConsole :=
    enqueueSerialInput
      (enqueueSerialInput ({ } : SerialConsole) (UInt32.ofNat 'h'.toNat))
      (UInt32.ofNat 'i'.toNat)
  let serialLsrRead :=
    stepSerialConsole queuedSerialConsole
      { port := ⟨0x3fd⟩, width := 1, count := 1, direction := .input, value := 0 }
  let serialFirstInputRead :=
    stepSerialConsole queuedSerialConsole
      { port := ⟨0x3f8⟩, width := 1, count := 1, direction := .input, value := 0 }
  let serialSecondInputRead :=
    match serialFirstInputRead with
    | .error err => Outcome.error err
    | .ok step =>
        stepSerialConsole step.console
          { port := ⟨0x3f8⟩, width := 1, count := 1, direction := .input, value := 0 }
  let serialEmptyLsrRead :=
    match serialSecondInputRead with
    | .error err => Outcome.error err
    | .ok step =>
        stepSerialConsole step.console
          { port := ⟨0x3fd⟩, width := 1, count := 1, direction := .input, value := 0 }
  let lapicIdRead :=
    stepPassiveLinuxMmio { address := ⟨0xfee00020⟩, width := 4, direction := .read, value := 0 }
  let lapicVersionRead :=
    stepPassiveLinuxMmio { address := ⟨0xfee00030⟩, width := 4, direction := .read, value := 0 }
  let lapicWrite :=
    stepPassiveLinuxMmio { address := ⟨0xfee000b0⟩, width := 4, direction := .write, value := 0 }
  let lapicBadWidthRead :=
    stepPassiveLinuxMmio { address := ⟨0xfee00020⟩, width := 1, direction := .read, value := 0 }
  let serialBadWidthTypedResult :=
    stepSerialConsoleTyped ({ } : SerialConsole)
      { port := ⟨0x3f8⟩, width := 2, count := 1, direction := .output, value := 0 }
  let passivePortDwordRead :=
    stepSerialConsole ({ } : SerialConsole)
      { port := ⟨0x80⟩, width := 4, count := 1, direction := .input, value := 0 }
  let passivePciConfigRead :=
    stepSerialConsole ({ } : SerialConsole)
      { port := ⟨0xcfc⟩, width := 4, count := 1, direction := .input, value := 0 }
  let platformPciConfigRoute :=
    routePlatformIoAccess
      { port := virtioPciConfigAddressPort, width := 4, count := 1, direction := .output, value := 0 }
  let platformPassiveIoRoute :=
    routePlatformIoAccess
      { port := ⟨0x80⟩, width := 4, count := 1, direction := .input, value := 0 }
  let passiveMmioRoute :=
    routePlatformMmioAccess (initialPlatformBusState 10).virtioPci
      { address := ⟨0xfee00020⟩, width := 4, direction := .read, value := 0 }
  let activeMmioRoute :=
    match configuredVirtioPciTransport with
    | .error _ => .passiveLapic
    | .ok transport =>
        routePlatformMmioAccess transport
          { address := bar0Address transport virtioPciCommonCfgOffset,
            width := 4, direction := .read, value := 0 }
  let passiveSerialWideRead :=
    stepSerialConsole ({ } : SerialConsole)
      { port := ⟨0x2fd⟩, width := 2, count := 1, direction := .input, value := 0 }
  let passivePortDwordWrite :=
    stepSerialConsole (captureSerialOutput ({ } : SerialConsole) "Linux")
      { port := ⟨0xcf8⟩, width := 4, count := 1, direction := .output, value := 0x80000000 }
  let fullQueueConsole :=
    (List.range (serialInputCapacity + 8)).foldl
      (fun console index => enqueueSerialInput console (UInt32.ofNat index))
      ({ } : SerialConsole)
  let queuedConsoleClientOutput :=
    queueConsoleClientOutput
      ({ id := 7, pendingOutput := ([1, 2] : List UInt32) } : ConsoleClientRuntime)
      0x123
  let queuedConsoleClientReplay :=
    queueConsoleClientReplay
      ({ id := 7, pendingOutput := ([1] : List UInt32) } : ConsoleClientRuntime)
      (captureSerialOutput ({ } : SerialConsole) "Ab").replay
  let overflowConsoleClientOutput :=
    queueConsoleClientOutput
      ({
        id := 7
        pendingOutput := List.replicate consoleClientOutputCapacity (0 : UInt32)
      } : ConsoleClientRuntime)
      0x45
  let attachedConsoleRuntime :=
    attachConsoleServerClient
      ({ clients := [{ id := 3, pendingOutput := ([0x41] : List UInt32) }] } : ConsoleServerRuntime)
      4
      (captureSerialOutput ({ } : SerialConsole) "Ab").replay
  let droppedConsoleRuntime :=
    dropConsoleServerClient attachedConsoleRuntime 3
  let queuedConsoleServerOutput :=
    queueConsoleServerOutput
      ({ clients := [
          { id := 3, pendingOutput := ([0x41] : List UInt32) },
          {
            id := 4
            pendingOutput := List.replicate consoleClientOutputCapacity (0 : UInt32)
          }
        ] } : ConsoleServerRuntime)
      0x123
  let lateAttachReplayText :=
    (String.ofList (List.replicate 5000 'x')) ++ "MICROVMM_INITRD_READY\nmicrovmm> "
  let directReplayConsole :=
    captureSerialOutput ({ } : SerialConsole) lateAttachReplayText
  let lateAttachReplayConsole :=
    writeSerialTranscript ({ } : SerialConsole)
      lateAttachReplayText
  pure <| merge <| [
    checkResultError "missing bzImage read" .openKernelImage 2 missingRead,
    checkResultError "missing initrd read" .openInitrdImage 2 missingInitrdRead,
    checkResultOk "test bzImage read" actualRead,
    checkResultOk "present initrd read" presentInitrdRead,
    checkResultOk "test bzImage parse" parseResult,
    checkResultOk "test bzImage validate" validateResult,
    checkResultOk "test bzImage validate custom cmdline" validateCustomCmdlineResult,
    checkResultOk "test bzImage initramfs layout validate" validateInitramfsResult,
    checkEq "parseRawLinuxArguments supports initrd"
      (.ok expectedRawLinuxArgs : Outcome String RawLinuxBootArgs)
      parseLinuxArgsResult,
    checkEq "elaborateLinuxBootRequest builds probe request"
      (.ok expectedProbeLinuxRequest : Outcome String LinuxBootRequest)
      elaborateProbeLinuxRequestResult,
    checkEq "parseRawLinuxArguments requires initrd path"
      (.error "linux option --initrd requires a path" : Outcome String RawLinuxBootArgs)
      parseLinuxArgsMissingInitrdResult,
    checkEq "parseRawLinuxArguments supports interactive"
      (.ok expectedRawInteractiveLinuxArgs : Outcome String RawLinuxBootArgs)
      parseLinuxArgsInteractiveResult,
    checkEq "elaborateLinuxBootRequest accepts initrd-backed interactive mode"
      (.ok expectedInteractiveLinuxRequest : Outcome String LinuxBootRequest)
      elaborateInteractiveLinuxRequestResult,
    checkEq "parseRawLinuxArguments supports explicit stdio transport"
      (.ok expectedRawExplicitStdioLinuxArgs : Outcome String RawLinuxBootArgs)
      parseLinuxArgsExplicitStdioResult,
    checkEq "elaborateLinuxBootRequest accepts explicit stdio transport"
      (.ok expectedExplicitStdioLinuxRequest : Outcome String LinuxBootRequest)
      elaborateInteractiveLinuxExplicitStdioRequestResult,
    checkEq "parseRawLinuxArguments supports server console mode"
      (.ok expectedRawServerLinuxArgs : Outcome String RawLinuxBootArgs)
      parseLinuxArgsServerResult,
    checkEq "elaborateLinuxBootRequest infers server console mode"
      (.ok expectedServerLinuxRequest : Outcome String LinuxBootRequest)
      elaborateInteractiveLinuxServerRequestResult,
    checkEq "parseRawLinuxArguments supports explicit server transport"
      (.ok expectedRawExplicitServerLinuxArgs : Outcome String RawLinuxBootArgs)
      parseLinuxArgsExplicitServerResult,
    checkEq "elaborateLinuxBootRequest accepts explicit server transport"
      (.ok expectedExplicitServerLinuxRequest : Outcome String LinuxBootRequest)
      elaborateInteractiveLinuxExplicitServerRequestResult,
    checkEq "parseRawLinuxArguments requires transport value"
      (.error "linux option --console-transport requires stdio or server" : Outcome String RawLinuxBootArgs)
      parseLinuxArgsMissingTransportValueResult,
    checkEq "parseRawLinuxArguments rejects unknown transport value"
      (.error "linux option --console-transport expects stdio or server" : Outcome String RawLinuxBootArgs)
      parseLinuxArgsUnknownTransportValueResult,
    checkTypedOutcomeError "parseRawLinuxArgumentsTyped keeps typed transport error"
      (.invalidConsoleTransport "pipe")
      parseLinuxArgsUnknownTransportValueTypedResult,
    checkEq "parseRawLinuxArguments preserves explicit interactive cmdline"
      (.ok expectedRawExplicitInteractiveCmdlineArgs : Outcome String RawLinuxBootArgs)
      parseLinuxArgsExplicitInteractiveCmdlineResult,
    checkEq "elaborateLinuxBootRequest preserves explicit interactive cmdline"
      (.ok expectedExplicitInteractiveCmdlineRequest : Outcome String LinuxBootRequest)
      elaborateInteractiveLinuxExplicitCmdlineRequestResult,
    checkEq "elaborateLinuxBootRequest requires initrd"
      (.error "linux option --interactive requires --initrd PATH" : Outcome String LinuxBootRequest)
      elaborateLinuxRequestMissingInitrdResult,
    checkTypedOutcomeError "elaborateLinuxBootRequestTyped keeps typed missing initrd error"
      .interactiveRequiresInitrd
      elaborateLinuxRequestMissingInitrdTypedResult,
    checkEq "elaborateLinuxBootRequest requires both server options"
      (.error "linux interactive server mode requires both --console-socket PATH and --serial-log PATH" : Outcome String LinuxBootRequest)
      elaborateLinuxRequestMissingServerLogResult,
    checkEq "elaborateLinuxBootRequest explicit server requires both server options"
      (.error "linux interactive server mode requires both --console-socket PATH and --serial-log PATH" : Outcome String LinuxBootRequest)
      elaborateLinuxRequestExplicitServerMissingPathsResult,
    checkEq "elaborateLinuxBootRequest explicit stdio rejects server options"
      (.error "linux stdio console transport does not accept --console-socket PATH or --serial-log PATH" : Outcome String LinuxBootRequest)
      elaborateLinuxRequestExplicitStdioWithServerOptionsResult,
    checkEq "elaborateLinuxBootRequest requires interactive for server options"
      (.error "linux options --console-socket PATH and --serial-log PATH require --interactive" : Outcome String LinuxBootRequest)
      elaborateLinuxRequestMissingInteractiveServerResult,
    checkEq "elaborateLinuxBootRequest requires interactive for explicit transport"
      (.error "linux option --console-transport requires --interactive" : Outcome String LinuxBootRequest)
      elaborateLinuxRequestMissingInteractiveTransportResult,
    checkEq "LinuxProbeRequest renders explicit cmdline"
      "console=ttyS0 rdinit=/init"
      (match expectedProbeLinuxRequest with | .probe request => request.commandLine | _ => ""),
    checkEq "LinuxInteractiveRequest renders default cmdline"
      defaultLinuxBootCommandLine
      (match expectedInteractiveLinuxRequest with | .interactive request => request.commandLine | _ => ""),
    checkEq "LinuxInteractiveRequest renders explicit cmdline"
      "console=ttyS0 rdinit=/init"
      (match expectedExplicitInteractiveCmdlineRequest with | .interactive request => request.commandLine | _ => ""),
    checkEq "captureSerialOutputByte derives replay text"
      "Linux"
      probeReadyConsole.replay.render,
    checkEq "probeTranscriptReady Linux" true (probeTranscriptReady probeReadyConsole.protocol),
    checkEq "interactiveTranscriptReady marker" true (interactiveTranscriptReady interactiveReadyConsole.protocol),
    checkEq "interactiveTranscriptReady unrelated" false (interactiveTranscriptReady unrelatedInteractiveConsole.protocol),
    checkEq "probeTranscriptReady Decompressing" true (probeTranscriptReady decompressingConsole.protocol),
    checkEq "probeTranscriptReady Booting" true (probeTranscriptReady bootingConsole.protocol),
    checkEq "probeTranscriptReady unrelated" false (probeTranscriptReady unrelatedProbeConsole.protocol),
    checkEq "linuxBootParamsPointers clears initrd fields when absent"
      ({ cmdLinePtr := 0x00020000, extCmdLinePtr := 0, ramdiskImage := 0, ramdiskSize := 0,
         extRamdiskImage := 0, extRamdiskSize := 0 } : LinuxBootParamsPointers)
      (linuxBootParamsPointers ⟨0x00020000⟩ none),
    checkEq "linuxBootParamsPointers splits ext fields"
      ({ cmdLinePtr := 0x00020000, extCmdLinePtr := 0x1, ramdiskImage := 0x23456000,
         ramdiskSize := 0x00003000, extRamdiskImage := 0x1, extRamdiskSize := 0x2 } : LinuxBootParamsPointers)
      highAddressPointers,
    checkResultOk "buildLinuxBootPlan sample inputs" samplePlanResult,
    checkTypedOutcomeError "validateLinuxGuestLayoutTyped keeps typed cmdline overflow"
      (.commandLineTooLong oversizedCommandLine.toUTF8.size sampleLayout.cmdlineSize.toNat)
      validateLinuxGuestLayoutTypedResult,
    checkEq "planInitramfsLayout aligns after runtime window"
      (.ok ({ loadAddr := ⟨0x00300000⟩, size := 0x00002000 } : InitramfsLayout) : Result InitramfsLayout)
      (planInitramfsLayout sampleLayout 0x00002000),
    checkResultError "planInitramfsLayout rejects initrd_addr_max overflow" .parseKernelImage eproto
      (planInitramfsLayout tightInitrdLimitLayout 0x00002000),
    checkResultError "planInitramfsLayout rejects guest overflow" .parseKernelImage eproto
      (planInitramfsLayout guestOverflowLayout 0x00002000),
    checkResultError "serial rejects non-byte COM1 access" .verifyIoExit eproto
      (stepSerialConsole ({ } : SerialConsole) { port := ⟨0x3f8⟩, width := 2, count := 1, direction := .output, value := 0 }),
    checkTypedOutcomeError "stepSerialConsoleTyped keeps typed COM1 width error"
      .com1RequiresByteAccess
      serialBadWidthTypedResult,
    checkEq "stepPassiveLinuxMmio reads LAPIC ID"
      (.ok (some 0) : ErrnoResult (Option UInt32))
      lapicIdRead,
    checkEq "stepPassiveLinuxMmio reads LAPIC version"
      (.ok (some 0x00050014) : ErrnoResult (Option UInt32))
      lapicVersionRead,
    checkEq "stepPassiveLinuxMmio ignores LAPIC writes"
      (.ok none : ErrnoResult (Option UInt32))
      lapicWrite,
    checkErrnoError "stepPassiveLinuxMmio rejects non-dword width" eproto lapicBadWidthRead,
    checkEq "passive port dword input returns zeros"
      (.ok ({ console := ({ } : SerialConsole), response := some 0 } : SerialStep) : Result SerialStep)
      passivePortDwordRead,
    checkEq "passive PCI config dword input returns all ones"
      (.ok ({ console := ({ } : SerialConsole), response := some 0xffffffff } : SerialStep) : Result SerialStep)
      passivePciConfigRead,
    checkEq "platform IO routes CF8 to bus PCI config"
      (.pciConfig .address : PlatformIoRoute)
      platformPciConfigRoute,
    checkEq "platform IO keeps unrelated ports passive"
      (.passive : PlatformIoRoute)
      platformPassiveIoRoute,
    checkEq "platform MMIO keeps LAPIC traffic passive before BAR enable"
      (.passiveLapic : PlatformMmioRoute)
      passiveMmioRoute,
    checkEq "platform MMIO routes active BAR traffic to virtio-pci"
      (.virtioPciBar : PlatformMmioRoute)
      activeMmioRoute,
    checkEq "passive serial wide read composes bytes"
      (.ok ({ console := ({ } : SerialConsole), response := some 0xb060 } : SerialStep) : Result SerialStep)
      passiveSerialWideRead,
    checkEq "passive port dword output is ignored"
      (.ok ({ console := captureSerialOutput ({ } : SerialConsole) "Linux" } : SerialStep) : Result SerialStep)
      passivePortDwordWrite,
    checkEq "enqueueSerialInput bounds queue length"
      serialInputCapacity fullQueueConsole.uart.inputQueue.length,
    checkEq "queueConsoleClientOutput appends normalized byte"
      (some ({ id := 7, pendingOutput := ([1, 2, 0x23] : List UInt32) } : ConsoleClientRuntime))
      queuedConsoleClientOutput,
    checkEq "queueConsoleClientReplay replays bytes in order"
      (some ({ id := 7, pendingOutput := ([1, 0x41, 0x62] : List UInt32) } : ConsoleClientRuntime))
      queuedConsoleClientReplay,
    checkEq "queueConsoleClientOutput rejects overflow"
      (none : Option ConsoleClientRuntime)
      overflowConsoleClientOutput,
    checkEq "attachConsoleServerClient appends replay-seeded runtime"
      ({ clients := [
          { id := 3, pendingOutput := ([0x41] : List UInt32) },
          { id := 4, pendingOutput := ([0x41, 0x62] : List UInt32) }
        ] } : ConsoleServerRuntime)
      attachedConsoleRuntime,
    checkEq "dropConsoleServerClient removes matching runtime only"
      ({ clients := [{ id := 4, pendingOutput := ([0x41, 0x62] : List UInt32) }] } : ConsoleServerRuntime)
      droppedConsoleRuntime,
    checkEq "queueConsoleServerOutput keeps surviving queues and reports drops"
      ({ runtime := { clients := [{ id := 3, pendingOutput := ([0x41, 0x23] : List UInt32) }] }, droppedClientIds := [4] } : QueueConsoleServerOutputResult)
      queuedConsoleServerOutput,
    checkEq "serial completes Linux transcript"
      (.ok ({ console := captureSerialOutput ({ } : SerialConsole) "Linux", outputByte? := some (UInt32.ofNat 'x'.toNat), ready := true } : SerialStep) : Result SerialStep)
      serialResult
  ] ++ [
    match lateAttachReplayConsole with
    | .error err =>
        fail "interactive transcript keeps replay tail" s!"expected ok, got error {repr err}"
    | .ok console =>
        merge [
          checkTrue "captureSerialOutputByte keeps protocol readiness after replay overflow"
            (interactiveTranscriptReady directReplayConsole.protocol)
            "expected protocol readiness to remain true after replay overflow",
          checkTrue "interactive transcript retains ready marker after overflow"
            (console.replay.render.contains "MICROVMM_INITRD_READY")
            "expected transcript tail to retain the ready marker after overflow",
          checkTrue "interactive transcript retains prompt after overflow"
            (console.replay.render.contains "microvmm> ")
            "expected transcript tail to retain the prompt after overflow"
        ],
    match absentInitrdRead with
    | .ok none => noFailures
    | .ok (some _) => fail "absent initrd read" "expected no bytes when no initrd path is supplied"
    | .error err => fail "absent initrd read" s!"expected ok none, got error {repr err}",
    match presentInitrdRead with
    | .error err => fail "present initrd read bytes" s!"expected initrd bytes, got error {repr err}"
    | .ok none => fail "present initrd read bytes" "expected some bytes for existing path"
    | .ok (some bytes) =>
        checkTrue "present initrd read bytes" (ByteArray.size bytes > 0) "expected non-empty bytes for existing path",
    match validateBootInputsResult with
    | .error err => fail "validateLinuxBootInputs sample layout" s!"expected ok, got error {repr err}"
    | .ok bootInputs =>
        merge [
          checkEq "validateLinuxBootInputs cmdline size" (defaultLinuxBootCommandLine.toUTF8.push 0).size bootInputs.cmdlineBytes.size,
          checkEq "validateLinuxBootInputs initramfs layout"
            (some ({ loadAddr := ⟨0x00300000⟩, size := 0x00001000 } : InitramfsLayout))
            (bootInputs.initramfs?.map Prod.fst),
          checkEq "validateLinuxBootInputs initramfs byte size"
            (some 4096)
            (bootInputs.initramfs?.map fun (_, bytes) => ByteArray.size bytes)
        ],
    match samplePlanResult with
    | .error err => fail "buildLinuxBootPlan sample inputs" s!"expected ok, got error {repr err}"
    | .ok (samplePlanBootInputs, samplePlan) =>
        let planChecks :=
          merge [
            checkEq "buildLinuxBootPlan preserves write order"
              expectedSamplePlanWriteKinds
              (samplePlan.writes.map LinuxBootWrite.kind),
            checkLinuxBootWrite "buildLinuxBootPlan kernel image"
              samplePlan .kernelImage 0x00100000
              (.bytes (samplePlanImageBytes.extract samplePlanLayout.setupBytes samplePlanImageBytes.size)),
            checkLinuxBootWrite "buildLinuxBootPlan header copy"
              samplePlan .bootParamsHeader 0x000101f1
              (.bytes (samplePlanImageBytes.extract 0x1f1 (0x1f1 + samplePlanLayout.headerCopySize))),
            checkLinuxBootWrite "buildLinuxBootPlan boot flag sentinel"
              samplePlan .bootFlagSentinel 0x000101fa (.u16 0xffff),
            checkLinuxBootWrite "buildLinuxBootPlan type of loader"
              samplePlan .typeOfLoader 0x00010210 (.u8 0xff),
            checkLinuxBootWrite "buildLinuxBootPlan load flags"
              samplePlan .loadFlags 0x00010211
              (.u8 ((samplePlanLayout.loadFlags ||| 0x80) &&& (~~~(0x20 : UInt32)))),
            checkLinuxBootWrite "buildLinuxBootPlan code32 start"
              samplePlan .code32Start 0x00010214 (.u32 0x00100000),
            checkLinuxBootWrite "buildLinuxBootPlan alt_mem_k"
              samplePlan .altMemK 0x000101e0 (.u32 0x0000fc00),
            checkLinuxBootWrite "buildLinuxBootPlan e820 count"
              samplePlan .e820EntryCount 0x000101e8 (.u8 3),
            checkLinuxBootWrite "buildLinuxBootPlan screen ext_mem_k"
              samplePlan .screenInfoExtMemK 0x00010002 (.u16 0x0000fc00),
            checkLinuxBootWrite "buildLinuxBootPlan screen video mode"
              samplePlan .screenInfoVideoMode 0x00010006 (.u8 3),
            checkLinuxBootWrite "buildLinuxBootPlan screen cols"
              samplePlan .screenInfoVideoCols 0x00010007 (.u8 80),
            checkLinuxBootWrite "buildLinuxBootPlan screen lines"
              samplePlan .screenInfoVideoLines 0x0001000e (.u8 25),
            checkLinuxBootWrite "buildLinuxBootPlan screen vga type"
              samplePlan .screenInfoVideoIsVga 0x0001000f (.u8 0x22),
            checkLinuxBootWrite "buildLinuxBootPlan screen font points"
              samplePlan .screenInfoVideoPoints 0x00010010 (.u16 16),
            checkLinuxBootWrite "buildLinuxBootPlan e820 entry 0"
              samplePlan (.e820Entry 0) 0x000102d0 (.e820Entry 0 0x000a0000 1),
            checkLinuxBootWrite "buildLinuxBootPlan e820 entry 1"
              samplePlan (.e820Entry 1) 0x000102e4 (.e820Entry 0x000a0000 0x00060000 2),
            checkLinuxBootWrite "buildLinuxBootPlan e820 entry 2"
              samplePlan (.e820Entry 2) 0x000102f8
              (.e820Entry 0x00100000 (64 * 1024 * 1024 - 0x00100000) 1),
            checkLinuxBootWrite "buildLinuxBootPlan command line"
              samplePlan .commandLine 0x00020000 (.bytes samplePlanBootInputs.cmdlineBytes),
            checkLinuxBootWrite "buildLinuxBootPlan gdt entry 2"
              samplePlan (.gdtEntry 2) 0x00005010 (.gdtEntry 0 0x000fffff 0x9b 0xc0),
            checkLinuxBootWrite "buildLinuxBootPlan gdt entry 3"
              samplePlan (.gdtEntry 3) 0x00005018 (.gdtEntry 0 0x000fffff 0x93 0xc0)
          ]
        let initramfsChecks :=
          match samplePlanBootInputs.initramfs? with
          | none =>
              fail "buildLinuxBootPlan initramfs" "expected validated initramfs layout"
          | some (initramfsLayout, initramfsBytes) =>
              let samplePointers := linuxBootParamsPointers ⟨0x00020000⟩ (some initramfsLayout)
              merge [
                checkLinuxBootWrite "buildLinuxBootPlan initramfs image"
                  samplePlan .initramfsImage initramfsLayout.loadAddr.value (.bytes initramfsBytes),
                checkLinuxBootWrite "buildLinuxBootPlan ramdisk image pointer"
                  samplePlan .ramdiskImage 0x00010218 (.u32 samplePointers.ramdiskImage),
                checkLinuxBootWrite "buildLinuxBootPlan ramdisk size pointer"
                  samplePlan .ramdiskSize 0x0001021c (.u32 samplePointers.ramdiskSize),
                checkLinuxBootWrite "buildLinuxBootPlan cmdline pointer"
                  samplePlan .cmdLinePtr 0x00010228 (.u32 samplePointers.cmdLinePtr),
                checkLinuxBootWrite "buildLinuxBootPlan ext cmdline pointer"
                  samplePlan .extCmdLinePtr 0x000100c8 (.u32 samplePointers.extCmdLinePtr),
                checkLinuxBootWrite "buildLinuxBootPlan ext ramdisk image pointer"
                  samplePlan .extRamdiskImage 0x000100c0 (.u32 samplePointers.extRamdiskImage),
                checkLinuxBootWrite "buildLinuxBootPlan ext ramdisk size pointer"
                  samplePlan .extRamdiskSize 0x000100c4 (.u32 samplePointers.extRamdiskSize)
              ]
        merge [planChecks, initramfsChecks],
    match serialLsrRead with
    | .error err => fail "serial LSR read" s!"expected RX-ready response, got error {repr err}"
    | .ok step =>
        merge [
          checkEq "serial LSR reports RX ready" (some 0x61) step.response,
          checkEq "serial LSR read preserves queue" queuedSerialConsole step.console
        ],
    match serialFirstInputRead with
    | .error err => fail "serial first input read" s!"expected queued byte, got error {repr err}"
    | .ok step =>
        merge [
          checkEq "serial first input byte" (some (UInt32.ofNat 'h'.toNat)) step.response,
          checkEq "serial first input read dequeues one byte" [UInt32.ofNat 'i'.toNat] step.console.uart.inputQueue
        ],
    match serialSecondInputRead with
    | .error err => fail "serial second input read" s!"expected queued byte, got error {repr err}"
    | .ok step =>
        merge [
          checkEq "serial second input byte" (some (UInt32.ofNat 'i'.toNat)) step.response,
          checkEq "serial second input empties queue" ([] : List UInt32) step.console.uart.inputQueue
        ],
    match serialEmptyLsrRead with
    | .error err => fail "serial empty LSR read" s!"expected TX-ready response, got error {repr err}"
    | .ok step =>
        checkEq "serial empty LSR clears RX ready" (some 0x60) step.response
  ]

private def runIntegrationSmokeTests : IO (List String) := do
  match ← probeApiVersion with
  | .error _ =>
      pure noFailures
  | .ok _ =>
      let virtioMessage ← probeMessage
      let linuxMessage ← probeLinuxBzImageMessage
      let linuxCustomKernelMessage ← probeLinuxBzImageMessage { kernelPath := "test-bzImage2" }
      pure <| merge [
        checkTrue "virtio integration success"
          (virtioMessage.contains "KVM virtio-mmio entropy probe succeeded" &&
            virtioMessage.contains virtioPayloadSummary)
          s!"unexpected message: {virtioMessage}",
        checkTrue "linux integration success"
          (linuxMessage.contains "KVM Linux bzImage probe succeeded" && linuxMessage.contains "transcript \"Linux\"")
          s!"unexpected message: {linuxMessage}",
        checkTrue "linux integration explicit kernel path"
          (linuxCustomKernelMessage.contains "KVM Linux bzImage probe succeeded" &&
            linuxCustomKernelMessage.contains "transcript \"Linux\"")
          s!"unexpected message: {linuxCustomKernelMessage}"
      ]

private def tests : List TestCase := [
  { name := "diagnostics", run := runDiagnosticTests },
  { name := "formatting", run := runFormattingTests },
  { name := "virtio", run := runVirtioTests },
  { name := "virtio-pci", run := runVirtioPciTests },
  { name := "linux", run := runLinuxTests },
  { name := "integration", run := runIntegrationSmokeTests }
]

private def runAllTests : IO (List String) := do
  let mut failures : List String := []
  for test in tests do
    failures := failures ++ (← test.run)
  pure failures

def main : IO Unit := do
  let failures ← runAllTests
  if failures.isEmpty then
    IO.println s!"{tests.length} test groups passed"
  else
    for failure in failures do
      IO.eprintln failure
    throw <| IO.userError s!"{failures.length} checks failed"
