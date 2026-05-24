namespace Microvmm.FFI

@[extern "microvmm_kvm_open"]
opaque kvmOpenRaw : UInt32 → IO Int32

@[extern "microvmm_kvm_get_api_version"]
opaque kvmGetApiVersionRaw : UInt32 → IO Int32

@[extern "microvmm_kvm_create_vm"]
opaque kvmCreateVmRaw : UInt32 → IO Int32

@[extern "microvmm_kvm_create_vcpu"]
opaque kvmCreateVcpuRaw : UInt32 → UInt32 → IO Int32

@[extern "microvmm_kvm_get_vcpu_mmap_size"]
opaque kvmGetVcpuMmapSizeRaw : UInt32 → IO Int32

@[extern "microvmm_kvm_probe_vcpu_run_area"]
opaque kvmProbeVcpuRunAreaRaw : UInt32 → UInt32 → IO Int32

@[extern "microvmm_kvm_alloc_guest_memory"]
opaque kvmAllocGuestMemoryRaw : UInt64 → IO UInt64

@[extern "microvmm_kvm_free_guest_memory"]
opaque kvmFreeGuestMemoryRaw : UInt64 → UInt64 → IO Int32

@[extern "microvmm_kvm_register_guest_memory"]
opaque kvmRegisterGuestMemoryRaw : UInt32 → UInt32 → UInt64 → UInt64 → UInt64 → IO Int32

@[extern "microvmm_kvm_unregister_guest_memory"]
opaque kvmUnregisterGuestMemoryRaw : UInt32 → UInt32 → IO Int32

@[extern "microvmm_kvm_create_irqchip"]
opaque kvmCreateIrqChipRaw : UInt32 → IO Int32

@[extern "microvmm_kvm_create_pit2"]
opaque kvmCreatePit2Raw : UInt32 → IO Int32

@[extern "microvmm_kvm_set_irq_line"]
opaque kvmSetIrqLineRaw : UInt32 → UInt32 → UInt32 → IO Int32

@[extern "microvmm_kvm_set_tss_addr"]
opaque kvmSetTssAddrRaw : UInt32 → UInt64 → IO Int32

@[extern "microvmm_kvm_configure_cpuid"]
opaque kvmConfigureCpuidRaw : UInt32 → UInt32 → IO Int32

@[extern "microvmm_kvm_alloc_vcpu_state_buffer"]
opaque kvmAllocVcpuStateBufferRaw : UInt32 → IO UInt64

@[extern "microvmm_kvm_free_vcpu_state_buffer"]
opaque kvmFreeVcpuStateBufferRaw : UInt64 → IO Int32

@[extern "microvmm_kvm_get_sregs_into_buffer"]
opaque kvmGetSregsIntoBufferRaw : UInt32 → UInt64 → IO Int32

@[extern "microvmm_kvm_set_sregs_from_buffer"]
opaque kvmSetSregsFromBufferRaw : UInt32 → UInt64 → IO Int32

@[extern "microvmm_kvm_vcpu_state_get_cr0"]
opaque kvmVcpuStateGetCr0Raw : UInt64 → IO UInt64

@[extern "microvmm_kvm_vcpu_state_set_cr0"]
opaque kvmVcpuStateSetCr0Raw : UInt64 → UInt64 → IO Int32

@[extern "microvmm_kvm_vcpu_state_set_cr3"]
opaque kvmVcpuStateSetCr3Raw : UInt64 → UInt64 → IO Int32

@[extern "microvmm_kvm_vcpu_state_set_cr4"]
opaque kvmVcpuStateSetCr4Raw : UInt64 → UInt64 → IO Int32

@[extern "microvmm_kvm_vcpu_state_set_efer"]
opaque kvmVcpuStateSetEferRaw : UInt64 → UInt64 → IO Int32

@[extern "microvmm_kvm_vcpu_state_set_gdt"]
opaque kvmVcpuStateSetGdtRaw : UInt64 → UInt64 → UInt32 → IO Int32

@[extern "microvmm_kvm_vcpu_state_set_idt"]
opaque kvmVcpuStateSetIdtRaw : UInt64 → UInt64 → UInt32 → IO Int32

@[extern "microvmm_kvm_vcpu_state_set_flat_segment"]
opaque kvmVcpuStateSetFlatSegmentRaw : UInt64 → UInt32 → UInt32 → UInt32 → IO Int32

@[extern "microvmm_kvm_vcpu_state_clear_regs"]
opaque kvmVcpuStateClearRegsRaw : UInt64 → IO Int32

@[extern "microvmm_kvm_vcpu_state_set_rip"]
opaque kvmVcpuStateSetRipRaw : UInt64 → UInt64 → IO Int32

@[extern "microvmm_kvm_vcpu_state_set_rsi"]
opaque kvmVcpuStateSetRsiRaw : UInt64 → UInt64 → IO Int32

@[extern "microvmm_kvm_vcpu_state_set_rsp"]
opaque kvmVcpuStateSetRspRaw : UInt64 → UInt64 → IO Int32

@[extern "microvmm_kvm_vcpu_state_set_rflags"]
opaque kvmVcpuStateSetRflagsRaw : UInt64 → UInt64 → IO Int32

@[extern "microvmm_kvm_set_regs_from_buffer"]
opaque kvmSetRegsFromBufferRaw : UInt32 → UInt64 → IO Int32

@[extern "microvmm_kvm_prepare_virtio_mmio_entropy_guest"]
opaque kvmPrepareVirtioMmioEntropyGuestRaw : UInt64 → UInt64 → IO Int32

@[extern "microvmm_host_stdin_read_u8_nonblocking"]
opaque hostStdinReadU8NonblockingRaw : UInt32 → IO Int32

@[extern "microvmm_host_stdout_write_u8"]
opaque hostStdoutWriteU8Raw : UInt32 → IO Int32

@[extern "microvmm_host_unix_listener_open"]
opaque hostUnixListenerOpenRaw : @& String → IO Int32

@[extern "microvmm_host_unix_listener_accept_nonblocking"]
opaque hostUnixListenerAcceptNonblockingRaw : UInt32 → IO Int32

@[extern "microvmm_host_socket_read_u8_nonblocking"]
opaque hostSocketReadU8NonblockingRaw : UInt32 → IO Int32

@[extern "microvmm_host_socket_write_u8_nonblocking"]
opaque hostSocketWriteU8NonblockingRaw : UInt32 → UInt32 → IO Int32

@[extern "microvmm_host_unlink_path"]
opaque hostUnlinkPathRaw : @& String → IO Int32

@[extern "microvmm_host_enable_wake_timer"]
opaque hostEnableWakeTimerRaw : UInt32 → IO Int32

@[extern "microvmm_host_disable_wake_timer"]
opaque hostDisableWakeTimerRaw : UInt32 → IO Int32

@[extern "microvmm_kvm_map_run_area"]
opaque kvmMapRunAreaRaw : UInt32 → UInt32 → IO UInt64

@[extern "microvmm_kvm_unmap_run_area"]
opaque kvmUnmapRunAreaRaw : UInt64 → UInt32 → IO Int32

@[extern "microvmm_kvm_run"]
opaque kvmRunRaw : UInt32 → IO Int32

@[extern "microvmm_kvm_run_exit_reason"]
opaque kvmRunExitReasonRaw : UInt64 → IO UInt32

@[extern "microvmm_kvm_run_io_direction"]
opaque kvmRunIoDirectionRaw : UInt64 → IO UInt32

@[extern "microvmm_kvm_run_io_port"]
opaque kvmRunIoPortRaw : UInt64 → IO UInt32

@[extern "microvmm_kvm_run_io_size"]
opaque kvmRunIoSizeRaw : UInt64 → IO UInt32

@[extern "microvmm_kvm_run_io_count"]
opaque kvmRunIoCountRaw : UInt64 → IO UInt32

@[extern "microvmm_kvm_run_io_data_u8"]
opaque kvmRunIoDataU8Raw : UInt64 → IO UInt32

@[extern "microvmm_kvm_run_io_data_u16"]
opaque kvmRunIoDataU16Raw : UInt64 → IO UInt32

@[extern "microvmm_kvm_run_io_data_u32"]
opaque kvmRunIoDataU32Raw : UInt64 → IO UInt32

@[extern "microvmm_kvm_run_set_io_data_u8"]
opaque kvmRunSetIoDataU8Raw : UInt64 → UInt32 → IO Int32

@[extern "microvmm_kvm_run_set_io_data_u16"]
opaque kvmRunSetIoDataU16Raw : UInt64 → UInt32 → IO Int32

@[extern "microvmm_kvm_run_set_io_data_u32"]
opaque kvmRunSetIoDataU32Raw : UInt64 → UInt32 → IO Int32

@[extern "microvmm_kvm_run_mmio_phys_addr"]
opaque kvmRunMmioPhysAddrRaw : UInt64 → IO UInt64

@[extern "microvmm_kvm_run_mmio_len"]
opaque kvmRunMmioLenRaw : UInt64 → IO UInt32

@[extern "microvmm_kvm_run_mmio_is_write"]
opaque kvmRunMmioIsWriteRaw : UInt64 → IO UInt32

@[extern "microvmm_kvm_run_mmio_data_u32"]
opaque kvmRunMmioDataU32Raw : UInt64 → IO UInt32

@[extern "microvmm_kvm_run_set_mmio_data_u32"]
opaque kvmRunSetMmioDataU32Raw : UInt64 → UInt32 → IO Int32

@[extern "microvmm_kvm_guest_read_u8_packed"]
opaque kvmGuestReadU8PackedRaw : UInt64 → UInt64 → UInt64 → IO UInt64

@[extern "microvmm_kvm_guest_read_u16_packed"]
opaque kvmGuestReadU16PackedRaw : UInt64 → UInt64 → UInt64 → IO UInt64

@[extern "microvmm_kvm_guest_read_u32_packed"]
opaque kvmGuestReadU32PackedRaw : UInt64 → UInt64 → UInt64 → IO UInt64

@[extern "microvmm_kvm_guest_write_u8"]
opaque kvmGuestWriteU8Raw : UInt64 → UInt64 → UInt64 → UInt32 → IO Int32

@[extern "microvmm_kvm_guest_write_u16"]
opaque kvmGuestWriteU16Raw : UInt64 → UInt64 → UInt64 → UInt32 → IO Int32

@[extern "microvmm_kvm_guest_write_u32"]
opaque kvmGuestWriteU32Raw : UInt64 → UInt64 → UInt64 → UInt32 → IO Int32

@[extern "microvmm_kvm_guest_write_byte_array"]
opaque kvmGuestWriteByteArrayRaw : UInt64 → UInt64 → UInt64 → @& ByteArray → IO Int32

@[extern "microvmm_kvm_close"]
opaque kvmCloseRaw : UInt32 → IO Int32

end Microvmm.FFI
