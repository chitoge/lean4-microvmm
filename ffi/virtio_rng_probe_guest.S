.intel_syntax noprefix

.section .rodata
.balign 1

.global microvmm_virtio_rng_probe_guest_start
.global microvmm_virtio_rng_probe_guest_end

.equ MMIO_BASE, 0x0d000000
.equ REG_MAGIC_VALUE, MMIO_BASE + 0x000
.equ REG_VERSION, MMIO_BASE + 0x004
.equ REG_DEVICE_ID, MMIO_BASE + 0x008
.equ REG_VENDOR_ID, MMIO_BASE + 0x00c
.equ REG_DEVICE_FEATURES, MMIO_BASE + 0x010
.equ REG_DEVICE_FEATURES_SEL, MMIO_BASE + 0x014
.equ REG_DRIVER_FEATURES, MMIO_BASE + 0x020
.equ REG_DRIVER_FEATURES_SEL, MMIO_BASE + 0x024
.equ REG_QUEUE_SEL, MMIO_BASE + 0x030
.equ REG_QUEUE_NUM_MAX, MMIO_BASE + 0x034
.equ REG_QUEUE_NUM, MMIO_BASE + 0x038
.equ REG_QUEUE_READY, MMIO_BASE + 0x044
.equ REG_QUEUE_NOTIFY, MMIO_BASE + 0x050
.equ REG_INTERRUPT_STATUS, MMIO_BASE + 0x060
.equ REG_INTERRUPT_ACK, MMIO_BASE + 0x064
.equ REG_STATUS, MMIO_BASE + 0x070
.equ REG_QUEUE_DESC_LOW, MMIO_BASE + 0x080
.equ REG_QUEUE_DESC_HIGH, MMIO_BASE + 0x084
.equ REG_QUEUE_DRIVER_LOW, MMIO_BASE + 0x090
.equ REG_QUEUE_DRIVER_HIGH, MMIO_BASE + 0x094
.equ REG_QUEUE_DEVICE_LOW, MMIO_BASE + 0x0a0
.equ REG_QUEUE_DEVICE_HIGH, MMIO_BASE + 0x0a4

.equ EXPECTED_MAGIC_VALUE, 0x74726976
.equ EXPECTED_VERSION, 0x2
.equ EXPECTED_DEVICE_ID, 0x4
.equ EXPECTED_VENDOR_ID, 0x4d564d4d

.equ STATUS_ACKNOWLEDGE, 0x1
.equ STATUS_DRIVER, 0x2
.equ STATUS_FEATURES_OK, 0x8
.equ STATUS_DRIVER_OK, 0x4

.equ STACK_TOP, 0x00008000
.equ RESULT_ADDR, 0x00014000
.equ QUEUE_DESC_ADDR, 0x00010000
.equ QUEUE_AVAIL_ADDR, 0x00011000
.equ QUEUE_USED_ADDR, 0x00012000
.equ ENTROPY_BUFFER_ADDR, 0x00013000
.equ BOGUS_DESC_ADDR, 0x00020000
.equ BOGUS_AVAIL_ADDR, 0x00021000
.equ BOGUS_USED_ADDR, 0x00022000

.equ PAYLOAD_LENGTH, 0x8
.equ RESULT_IN_PROGRESS, 0xffffffff
.equ RESULT_BAD_MAGIC, 0x1
.equ RESULT_BAD_VERSION, 0x2
.equ RESULT_BAD_DEVICE_ID, 0x3
.equ RESULT_BAD_VENDOR_ID, 0x4
.equ RESULT_BAD_FEATURES_LOW, 0x5
.equ RESULT_BAD_FEATURES_HIGH, 0x6
.equ RESULT_FEATURES_NOT_ACCEPTED, 0x7
.equ RESULT_BAD_QUEUE_NUM_MAX, 0x8
.equ RESULT_USED_TIMEOUT, 0x9
.equ RESULT_BAD_USED_ID, 0xa
.equ RESULT_BAD_USED_LEN, 0xb
.equ RESULT_BAD_PAYLOAD, 0xc

.code32
microvmm_virtio_rng_probe_guest_start:
  mov esp, STACK_TOP
  mov dword ptr [RESULT_ADDR], RESULT_IN_PROGRESS

  mov eax, dword ptr [REG_MAGIC_VALUE]
  cmp eax, EXPECTED_MAGIC_VALUE
  jne fail_magic

  mov eax, dword ptr [REG_VERSION]
  cmp eax, EXPECTED_VERSION
  jne fail_version

  mov eax, dword ptr [REG_DEVICE_ID]
  cmp eax, EXPECTED_DEVICE_ID
  jne fail_device_id

  mov eax, dword ptr [REG_VENDOR_ID]
  cmp eax, EXPECTED_VENDOR_ID
  jne fail_vendor_id

  mov dword ptr [REG_STATUS], 0
  mov dword ptr [REG_STATUS], STATUS_ACKNOWLEDGE
  mov dword ptr [REG_STATUS], STATUS_ACKNOWLEDGE | STATUS_DRIVER

  mov dword ptr [REG_DEVICE_FEATURES_SEL], 0
  mov eax, dword ptr [REG_DEVICE_FEATURES]
  test eax, eax
  jne fail_features_low

  mov dword ptr [REG_DEVICE_FEATURES_SEL], 1
  mov eax, dword ptr [REG_DEVICE_FEATURES]
  cmp eax, 1
  jne fail_features_high

  mov dword ptr [REG_DRIVER_FEATURES_SEL], 0
  mov dword ptr [REG_DRIVER_FEATURES], 0
  mov dword ptr [REG_DRIVER_FEATURES_SEL], 1
  mov dword ptr [REG_DRIVER_FEATURES], 1

  mov dword ptr [REG_STATUS], STATUS_ACKNOWLEDGE | STATUS_DRIVER | STATUS_FEATURES_OK
  mov eax, dword ptr [REG_STATUS]
  test eax, STATUS_FEATURES_OK
  jz fail_features_ok

  mov dword ptr [REG_QUEUE_SEL], 0
  mov eax, dword ptr [REG_QUEUE_NUM_MAX]
  cmp eax, 1
  jb fail_queue_num_max

  mov dword ptr [REG_QUEUE_NUM], 1
  mov dword ptr [REG_QUEUE_DESC_LOW], QUEUE_DESC_ADDR
  mov dword ptr [REG_QUEUE_DESC_HIGH], 0
  mov dword ptr [REG_QUEUE_DRIVER_LOW], QUEUE_AVAIL_ADDR
  mov dword ptr [REG_QUEUE_DRIVER_HIGH], 0
  mov dword ptr [REG_QUEUE_DEVICE_LOW], QUEUE_USED_ADDR
  mov dword ptr [REG_QUEUE_DEVICE_HIGH], 0
  mov dword ptr [REG_QUEUE_READY], 1

  mov dword ptr [REG_QUEUE_NUM], 2
  mov dword ptr [REG_QUEUE_DESC_LOW], BOGUS_DESC_ADDR
  mov dword ptr [REG_QUEUE_DESC_HIGH], 0
  mov dword ptr [REG_QUEUE_DRIVER_LOW], BOGUS_AVAIL_ADDR
  mov dword ptr [REG_QUEUE_DRIVER_HIGH], 0
  mov dword ptr [REG_QUEUE_DEVICE_LOW], BOGUS_USED_ADDR
  mov dword ptr [REG_QUEUE_DEVICE_HIGH], 0

  mov dword ptr [QUEUE_DESC_ADDR + 0], ENTROPY_BUFFER_ADDR
  mov dword ptr [QUEUE_DESC_ADDR + 4], 0
  mov dword ptr [QUEUE_DESC_ADDR + 8], PAYLOAD_LENGTH
  mov dword ptr [QUEUE_DESC_ADDR + 12], 2

  mov word ptr [QUEUE_AVAIL_ADDR + 0], 0
  mov word ptr [QUEUE_AVAIL_ADDR + 2], 1
  mov word ptr [QUEUE_AVAIL_ADDR + 4], 0
  mov word ptr [QUEUE_USED_ADDR + 0], 0
  mov word ptr [QUEUE_USED_ADDR + 2], 0

  mov dword ptr [REG_STATUS], STATUS_ACKNOWLEDGE | STATUS_DRIVER | STATUS_FEATURES_OK | STATUS_DRIVER_OK
  mov dword ptr [REG_QUEUE_NOTIFY], 0

  mov ecx, 16
poll_used:
  mov ax, word ptr [QUEUE_USED_ADDR + 2]
  cmp ax, 1
  je have_completion
  mov eax, dword ptr [REG_INTERRUPT_STATUS]
  dec ecx
  jnz poll_used
  mov eax, RESULT_USED_TIMEOUT
  jmp fail_with_code

have_completion:
  mov eax, dword ptr [QUEUE_USED_ADDR + 4]
  test eax, eax
  jne fail_used_id

  mov eax, dword ptr [QUEUE_USED_ADDR + 8]
  cmp eax, PAYLOAD_LENGTH
  jne fail_used_len

  cmp byte ptr [ENTROPY_BUFFER_ADDR + 0], 0x96
  jne fail_payload
  cmp byte ptr [ENTROPY_BUFFER_ADDR + 1], 0x6f
  jne fail_payload
  cmp byte ptr [ENTROPY_BUFFER_ADDR + 2], 0xa6
  jne fail_payload
  cmp byte ptr [ENTROPY_BUFFER_ADDR + 3], 0x57
  jne fail_payload
  cmp byte ptr [ENTROPY_BUFFER_ADDR + 4], 0xb7
  jne fail_payload
  cmp byte ptr [ENTROPY_BUFFER_ADDR + 5], 0xad
  jne fail_payload
  cmp byte ptr [ENTROPY_BUFFER_ADDR + 6], 0x3d
  jne fail_payload
  cmp byte ptr [ENTROPY_BUFFER_ADDR + 7], 0x99
  jne fail_payload

  mov dword ptr [REG_INTERRUPT_ACK], 1
  mov dword ptr [RESULT_ADDR], 0
  hlt

fail_magic:
  mov eax, RESULT_BAD_MAGIC
  jmp fail_with_code

fail_version:
  mov eax, RESULT_BAD_VERSION
  jmp fail_with_code

fail_device_id:
  mov eax, RESULT_BAD_DEVICE_ID
  jmp fail_with_code

fail_vendor_id:
  mov eax, RESULT_BAD_VENDOR_ID
  jmp fail_with_code

fail_features_low:
  mov eax, RESULT_BAD_FEATURES_LOW
  jmp fail_with_code

fail_features_high:
  mov eax, RESULT_BAD_FEATURES_HIGH
  jmp fail_with_code

fail_features_ok:
  mov eax, RESULT_FEATURES_NOT_ACCEPTED
  jmp fail_with_code

fail_queue_num_max:
  mov eax, RESULT_BAD_QUEUE_NUM_MAX
  jmp fail_with_code

fail_used_id:
  mov eax, RESULT_BAD_USED_ID
  jmp fail_with_code

fail_used_len:
  mov eax, RESULT_BAD_USED_LEN
  jmp fail_with_code

fail_payload:
  mov eax, RESULT_BAD_PAYLOAD

fail_with_code:
  mov dword ptr [RESULT_ADDR], eax
  hlt

microvmm_virtio_rng_probe_guest_end: