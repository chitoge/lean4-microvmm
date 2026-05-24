#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/kvm.h>
#include <poll.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <signal.h>
#include <sys/time.h>
#include <sys/un.h>
#include <unistd.h>

#define MICROVMM_PACKED_STAGE_SHIFT 12
#define MICROVMM_PACKED_STAGE_BASE (1U << MICROVMM_PACKED_STAGE_SHIFT)
#define MICROVMM_PTR_ERROR_BASE UINT64_C(0xfffffffffffff000)
#define MICROVMM_GUEST_MEMORY_SIZE (64UL * 1024UL * 1024UL)
#define MICROVMM_GDT_ADDR 0x5000UL
#define MICROVMM_MAX_CPUID_ENTRIES 256U
#define MICROVMM_VIRTIO_GUEST_MEMORY_SIZE (4UL * 1024UL * 1024UL)
#define MICROVMM_VIRTIO_PROBE_CODE_ADDR 0x1000UL
#define MICROVMM_VIRTIO_RESULT_ADDR 0x14000UL
#define MICROVMM_VIRTIO_MMIO_BASE 0x0d000000ULL
#define MICROVMM_VIRTIO_MMIO_SIZE 0x1000ULL
#define MICROVMM_VIRTIO_MMIO_MAGIC_VALUE 0x74726976U
#define MICROVMM_VIRTIO_MMIO_VERSION 0x2U
#define MICROVMM_VIRTIO_DEVICE_ID_ENTROPY 0x4U
#define MICROVMM_VIRTIO_VENDOR_ID 0x4d564d4dU
#define MICROVMM_VIRTIO_QUEUE_NUM_MAX 1U
#define MICROVMM_VIRTIO_QUEUE_DESC_ADDR 0x10000ULL
#define MICROVMM_VIRTIO_QUEUE_AVAIL_ADDR 0x11000ULL
#define MICROVMM_VIRTIO_QUEUE_USED_ADDR 0x12000ULL
#define MICROVMM_VIRTIO_ENTROPY_BUFFER_ADDR 0x13000ULL
#define MICROVMM_VIRTIO_BOGUS_DESC_ADDR 0x20000ULL
#define MICROVMM_VIRTIO_BOGUS_AVAIL_ADDR 0x21000ULL
#define MICROVMM_VIRTIO_BOGUS_USED_ADDR 0x22000ULL
#define MICROVMM_VIRTIO_PAYLOAD_LENGTH 8U
#define MICROVMM_VIRTIO_MAX_KVM_EXITS 256U
#define MICROVMM_VIRTIO_F_VERSION_1 32U
#define MICROVMM_VIRTIO_STATUS_ACKNOWLEDGE 0x01U
#define MICROVMM_VIRTIO_STATUS_DRIVER 0x02U
#define MICROVMM_VIRTIO_STATUS_DRIVER_OK 0x04U
#define MICROVMM_VIRTIO_STATUS_FEATURES_OK 0x08U
#define MICROVMM_VRING_DESC_F_NEXT 0x01U
#define MICROVMM_VRING_DESC_F_WRITE 0x02U
#define MICROVMM_VRING_DESC_F_INDIRECT 0x04U
#define MICROVMM_VIRTIO_MMIO_REG_MAGIC_VALUE 0x000U
#define MICROVMM_VIRTIO_MMIO_REG_VERSION 0x004U
#define MICROVMM_VIRTIO_MMIO_REG_DEVICE_ID 0x008U
#define MICROVMM_VIRTIO_MMIO_REG_VENDOR_ID 0x00cU
#define MICROVMM_VIRTIO_MMIO_REG_DEVICE_FEATURES 0x010U
#define MICROVMM_VIRTIO_MMIO_REG_DEVICE_FEATURES_SEL 0x014U
#define MICROVMM_VIRTIO_MMIO_REG_DRIVER_FEATURES 0x020U
#define MICROVMM_VIRTIO_MMIO_REG_DRIVER_FEATURES_SEL 0x024U
#define MICROVMM_VIRTIO_MMIO_REG_QUEUE_SEL 0x030U
#define MICROVMM_VIRTIO_MMIO_REG_QUEUE_NUM_MAX 0x034U
#define MICROVMM_VIRTIO_MMIO_REG_QUEUE_NUM 0x038U
#define MICROVMM_VIRTIO_MMIO_REG_QUEUE_READY 0x044U
#define MICROVMM_VIRTIO_MMIO_REG_QUEUE_NOTIFY 0x050U
#define MICROVMM_VIRTIO_MMIO_REG_INTERRUPT_STATUS 0x060U
#define MICROVMM_VIRTIO_MMIO_REG_INTERRUPT_ACK 0x064U
#define MICROVMM_VIRTIO_MMIO_REG_STATUS 0x070U
#define MICROVMM_VIRTIO_MMIO_REG_QUEUE_DESC_LOW 0x080U
#define MICROVMM_VIRTIO_MMIO_REG_QUEUE_DESC_HIGH 0x084U
#define MICROVMM_VIRTIO_MMIO_REG_QUEUE_DRIVER_LOW 0x090U
#define MICROVMM_VIRTIO_MMIO_REG_QUEUE_DRIVER_HIGH 0x094U
#define MICROVMM_VIRTIO_MMIO_REG_QUEUE_DEVICE_LOW 0x0a0U
#define MICROVMM_VIRTIO_MMIO_REG_QUEUE_DEVICE_HIGH 0x0a4U
#define MICROVMM_VIRTIO_MMIO_REG_CONFIG_GENERATION 0x0fcU
#define MICROVMM_VIRTIO_RESULT_IN_PROGRESS 0xffffffffU
#define MICROVMM_VIRTIO_RESULT_SUCCESS 0U

enum microvmm_probe_stage {
  MICROVMM_PROBE_STAGE_OPEN_KERNEL_IMAGE = 1,
  MICROVMM_PROBE_STAGE_READ_KERNEL_IMAGE = 2,
  MICROVMM_PROBE_STAGE_PARSE_KERNEL_IMAGE = 3,
  MICROVMM_PROBE_STAGE_ALLOC_GUEST_MEMORY = 4,
  MICROVMM_PROBE_STAGE_REGISTER_GUEST_MEMORY = 5,
  MICROVMM_PROBE_STAGE_SET_TSS_ADDR = 6,
  MICROVMM_PROBE_STAGE_CONFIGURE_CPUID = 7,
  MICROVMM_PROBE_STAGE_GET_SREGS = 8,
  MICROVMM_PROBE_STAGE_SET_SREGS = 9,
  MICROVMM_PROBE_STAGE_SET_REGS = 10,
  MICROVMM_PROBE_STAGE_MAP_RUN_AREA = 11,
  MICROVMM_PROBE_STAGE_RUN_GUEST = 12,
  MICROVMM_PROBE_STAGE_VERIFY_IO_EXIT = 13,
  MICROVMM_PROBE_STAGE_VERIFY_TRANSCRIPT = 14,
  MICROVMM_PROBE_STAGE_UNMAP_RUN_AREA = 15,
  MICROVMM_PROBE_STAGE_UNREGISTER_GUEST_MEMORY = 16,
  MICROVMM_PROBE_STAGE_FREE_GUEST_MEMORY = 17,
  MICROVMM_PROBE_STAGE_LOAD_GUEST_CODE = 18,
  MICROVMM_PROBE_STAGE_VERIFY_MMIO_EXIT = 19,
  MICROVMM_PROBE_STAGE_VERIFY_QUEUE_STATE = 20,
  MICROVMM_PROBE_STAGE_VERIFY_GUEST_RESULT = 21,
};

struct microvmm_gdt_entry {
  uint16_t limit_low;
  uint16_t base_low;
  uint8_t base_middle;
  uint8_t access;
  uint8_t granularity;
  uint8_t base_high;
} __attribute__((packed));

struct microvmm_vring_desc {
  uint64_t addr;
  uint32_t len;
  uint16_t flags;
  uint16_t next;
} __attribute__((packed));

struct microvmm_vring_used_elem {
  uint32_t id;
  uint32_t len;
} __attribute__((packed));

struct microvmm_virtio_rng_guest_result {
  uint32_t code;
} __attribute__((packed));

struct microvmm_vcpu_state_buffer {
  struct kvm_sregs sregs;
  struct kvm_regs regs;
};

extern const uint8_t microvmm_virtio_rng_probe_guest_start[];
extern const uint8_t microvmm_virtio_rng_probe_guest_end[];

static int32_t microvmm_pack_probe_error(uint32_t stage, int err) {
  uint32_t packed = (stage << MICROVMM_PACKED_STAGE_SHIFT) |
                    ((uint32_t)err & (MICROVMM_PACKED_STAGE_BASE - 1));
  return -(int32_t)packed;
}

static uint64_t microvmm_encode_pointer_error(int err) {
  return MICROVMM_PTR_ERROR_BASE | ((uint64_t)((uint32_t)err & 0xfffU));
}

static int32_t microvmm_negative_errno(int err) {
  return err == 0 ? 0 : -(int32_t)err;
}

static int microvmm_set_nonblocking_cloexec(int fd) {
  int flags = fcntl(fd, F_GETFL, 0);

  if (flags < 0) {
    return errno;
  }
  if (fcntl(fd, F_SETFL, flags | O_NONBLOCK) < 0) {
    return errno;
  }

  flags = fcntl(fd, F_GETFD, 0);
  if (flags < 0) {
    return errno;
  }
  if (fcntl(fd, F_SETFD, flags | FD_CLOEXEC) < 0) {
    return errno;
  }

  return 0;
}

static int microvmm_prepare_unix_socket_path(const char *path) {
  struct stat st;

  if (path == NULL || path[0] == '\0') {
    return EINVAL;
  }
  if (lstat(path, &st) == 0) {
    if (!S_ISSOCK(st.st_mode)) {
      return EEXIST;
    }
    if (unlink(path) < 0) {
      return errno;
    }
  } else if (errno != ENOENT) {
    return errno;
  }

  return 0;
}

static struct sigaction microvmm_previous_wake_signal_action;
static struct itimerval microvmm_previous_wake_timer;
static int microvmm_wake_timer_active = 0;

static void microvmm_wake_signal_handler(int signal_number) {
  (void)signal_number;
}

static uint64_t microvmm_pack_read_result(int err, uint32_t value) {
  return ((uint64_t)(uint32_t)err << 32) | (uint64_t)value;
}

static struct kvm_segment *microvmm_vcpu_segment_slot(struct microvmm_vcpu_state_buffer *buffer,
                                                      uint32_t slot) {
  switch (slot) {
    case 0:
      return &buffer->sregs.cs;
    case 1:
      return &buffer->sregs.ds;
    case 2:
      return &buffer->sregs.es;
    case 3:
      return &buffer->sregs.fs;
    case 4:
      return &buffer->sregs.gs;
    case 5:
      return &buffer->sregs.ss;
    default:
      return NULL;
  }
}

static int microvmm_guest_span_valid_for(size_t guest_memory_size, uint64_t guest_addr,
                                         size_t size) {
  return guest_addr <= (uint64_t)guest_memory_size &&
         (uint64_t)size <= (uint64_t)guest_memory_size - guest_addr;
}

static void microvmm_write_gdt_entry(struct microvmm_gdt_entry *entry, uint32_t base,
                                     uint32_t limit, uint8_t access, uint8_t flags) {
  entry->limit_low = (uint16_t)(limit & 0xffffU);
  entry->base_low = (uint16_t)(base & 0xffffU);
  entry->base_middle = (uint8_t)((base >> 16) & 0xffU);
  entry->access = access;
  entry->granularity = (uint8_t)(((limit >> 16) & 0x0fU) | (flags & 0xf0U));
  entry->base_high = (uint8_t)((base >> 24) & 0xffU);
}

static struct kvm_segment microvmm_flat_segment(uint16_t selector, uint8_t type) {
  struct kvm_segment segment;

  memset(&segment, 0, sizeof(segment));
  segment.base = 0;
  segment.limit = 0xffffffffU;
  segment.selector = selector;
  segment.type = type;
  segment.present = 1;
  segment.dpl = 0;
  segment.db = 1;
  segment.s = 1;
  segment.l = 0;
  segment.g = 1;
  segment.unusable = 0;

  return segment;
}

static int microvmm_configure_cpuid(int kvm_fd, int vcpu_fd) {
  size_t allocation_size = sizeof(struct kvm_cpuid2) +
                           MICROVMM_MAX_CPUID_ENTRIES * sizeof(struct kvm_cpuid_entry2);
  struct kvm_cpuid2 *cpuid = (struct kvm_cpuid2 *)malloc(allocation_size);
  int err = 0;

  if (cpuid == NULL) {
    return ENOMEM;
  }

  memset(cpuid, 0, allocation_size);
  cpuid->nent = MICROVMM_MAX_CPUID_ENTRIES;

  if (ioctl(kvm_fd, KVM_GET_SUPPORTED_CPUID, cpuid) < 0) {
    err = errno;
    free(cpuid);
    return err;
  }

  if (ioctl(vcpu_fd, KVM_SET_CPUID2, cpuid) < 0) {
    err = errno;
    free(cpuid);
    return err;
  }

  free(cpuid);
  return 0;
}

static int microvmm_guest_read_bytes(const uint8_t *guest_memory, size_t guest_memory_size,
                                     uint64_t guest_addr, void *dst, size_t size) {
  if (!microvmm_guest_span_valid_for(guest_memory_size, guest_addr, size)) {
    return EPROTO;
  }

  memcpy(dst, guest_memory + (size_t)guest_addr, size);
  return 0;
}

static int microvmm_guest_write_bytes(uint8_t *guest_memory, size_t guest_memory_size,
                                      uint64_t guest_addr, const void *src, size_t size) {
  if (!microvmm_guest_span_valid_for(guest_memory_size, guest_addr, size)) {
    return EPROTO;
  }

  memcpy(guest_memory + (size_t)guest_addr, src, size);
  return 0;
}

static uint16_t microvmm_load_u16_le(const uint8_t *bytes) {
  return (uint16_t)(((uint16_t)bytes[0]) | ((uint16_t)bytes[1] << 8));
}

static void microvmm_store_u16_le(uint8_t *bytes, uint16_t value) {
  bytes[0] = (uint8_t)(value & 0xffU);
  bytes[1] = (uint8_t)((value >> 8) & 0xffU);
}

static uint32_t microvmm_load_u32_le(const uint8_t *bytes) {
  return ((uint32_t)bytes[0]) | ((uint32_t)bytes[1] << 8) | ((uint32_t)bytes[2] << 16) |
         ((uint32_t)bytes[3] << 24);
}

static void microvmm_store_u32_le(uint8_t *bytes, uint32_t value) {
  bytes[0] = (uint8_t)(value & 0xffU);
  bytes[1] = (uint8_t)((value >> 8) & 0xffU);
  bytes[2] = (uint8_t)((value >> 16) & 0xffU);
  bytes[3] = (uint8_t)((value >> 24) & 0xffU);
}

static size_t microvmm_split_avail_span(uint32_t queue_num) {
  return 4U + (size_t)queue_num * sizeof(uint16_t) + sizeof(uint16_t);
}

static size_t microvmm_split_used_span(uint32_t queue_num) {
  return 4U + (size_t)queue_num * sizeof(struct microvmm_vring_used_elem) +
         sizeof(uint16_t);
}

static int microvmm_prepare_virtio_rng_guest(void *guest_memory, size_t guest_memory_size) {
  uint8_t *guest_bytes = (uint8_t *)guest_memory;
  struct microvmm_gdt_entry *gdt;
  size_t guest_code_size =
      (size_t)(microvmm_virtio_rng_probe_guest_end - microvmm_virtio_rng_probe_guest_start);

  if (guest_code_size == 0 ||
      !microvmm_guest_span_valid_for(guest_memory_size, MICROVMM_VIRTIO_PROBE_CODE_ADDR,
                                     guest_code_size) ||
      !microvmm_guest_span_valid_for(guest_memory_size, MICROVMM_GDT_ADDR,
                                     4U * sizeof(struct microvmm_gdt_entry)) ||
      !microvmm_guest_span_valid_for(guest_memory_size, MICROVMM_VIRTIO_RESULT_ADDR,
                                     sizeof(struct microvmm_virtio_rng_guest_result)) ||
      !microvmm_guest_span_valid_for(guest_memory_size, MICROVMM_VIRTIO_QUEUE_DESC_ADDR,
                                     sizeof(struct microvmm_vring_desc)) ||
      !microvmm_guest_span_valid_for(guest_memory_size, MICROVMM_VIRTIO_QUEUE_AVAIL_ADDR,
                                     microvmm_split_avail_span(1U)) ||
      !microvmm_guest_span_valid_for(guest_memory_size, MICROVMM_VIRTIO_QUEUE_USED_ADDR,
                                     microvmm_split_used_span(1U)) ||
      !microvmm_guest_span_valid_for(guest_memory_size, MICROVMM_VIRTIO_ENTROPY_BUFFER_ADDR,
                                     MICROVMM_VIRTIO_PAYLOAD_LENGTH) ||
      !microvmm_guest_span_valid_for(guest_memory_size, MICROVMM_VIRTIO_BOGUS_DESC_ADDR,
                                     sizeof(struct microvmm_vring_desc)) ||
      !microvmm_guest_span_valid_for(guest_memory_size, MICROVMM_VIRTIO_BOGUS_AVAIL_ADDR,
                                     microvmm_split_avail_span(1U)) ||
      !microvmm_guest_span_valid_for(guest_memory_size, MICROVMM_VIRTIO_BOGUS_USED_ADDR,
                                     microvmm_split_used_span(1U))) {
    return EPROTO;
  }

  memcpy(guest_bytes + MICROVMM_VIRTIO_PROBE_CODE_ADDR, microvmm_virtio_rng_probe_guest_start,
         guest_code_size);

  gdt = (struct microvmm_gdt_entry *)(guest_bytes + MICROVMM_GDT_ADDR);
  memset(gdt, 0, 4U * sizeof(*gdt));
  microvmm_write_gdt_entry(&gdt[2], 0, 0x000fffffU, 0x9bU, 0xc0U);
  microvmm_write_gdt_entry(&gdt[3], 0, 0x000fffffU, 0x93U, 0xc0U);
  return 0;
}

lean_obj_res microvmm_kvm_open(uint32_t ignored) {
  (void)ignored;

  int fd = open("/dev/kvm", O_RDWR | O_CLOEXEC);
  int32_t status = fd < 0 ? -(int32_t)errno : (int32_t)fd;

  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_get_api_version(uint32_t fd_bits) {
  int fd = (int)fd_bits;
  int api_version = ioctl(fd, KVM_GET_API_VERSION, 0);
  int32_t status = api_version < 0 ? -(int32_t)errno : (int32_t)api_version;

  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_create_vm(uint32_t fd_bits) {
  int fd = (int)fd_bits;
  int vm_fd = ioctl(fd, KVM_CREATE_VM, 0);
  int32_t status = vm_fd < 0 ? -(int32_t)errno : (int32_t)vm_fd;

  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_create_vcpu(uint32_t vm_fd_bits, uint32_t vcpu_id_bits) {
  int vm_fd = (int)vm_fd_bits;
  unsigned long vcpu_id = (unsigned long)vcpu_id_bits;
  int vcpu_fd = ioctl(vm_fd, KVM_CREATE_VCPU, vcpu_id);
  int32_t status = vcpu_fd < 0 ? -(int32_t)errno : (int32_t)vcpu_fd;

  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_host_stdin_read_u8_nonblocking(uint32_t ignored) {
  (void)ignored;

  for (;;) {
    struct pollfd stdin_pollfd = {
        .fd = STDIN_FILENO,
        .events = POLLIN,
        .revents = 0,
    };
    int poll_status = poll(&stdin_pollfd, 1, 0);

    if (poll_status < 0) {
      if (errno == EINTR) {
        continue;
      }
      return lean_io_result_mk_ok(
          lean_box_uint32((uint32_t)microvmm_negative_errno(errno)));
    }
    if (poll_status == 0) {
      return lean_io_result_mk_ok(lean_box_uint32(0));
    }
    if ((stdin_pollfd.revents & POLLNVAL) != 0) {
      return lean_io_result_mk_ok(
          lean_box_uint32((uint32_t)microvmm_negative_errno(EBADF)));
    }
    if ((stdin_pollfd.revents & POLLERR) != 0) {
      return lean_io_result_mk_ok(
          lean_box_uint32((uint32_t)microvmm_negative_errno(EIO)));
    }
    if ((stdin_pollfd.revents & POLLIN) == 0) {
      return lean_io_result_mk_ok(lean_box_uint32(0));
    }

    uint8_t byte = 0;
    ssize_t count = read(STDIN_FILENO, &byte, sizeof(byte));

    if (count < 0) {
      if (errno == EINTR) {
        continue;
      }
      if (errno == EAGAIN || errno == EWOULDBLOCK) {
        return lean_io_result_mk_ok(lean_box_uint32(0));
      }
      return lean_io_result_mk_ok(
          lean_box_uint32((uint32_t)microvmm_negative_errno(errno)));
    }
    if (count == 0) {
      return lean_io_result_mk_ok(lean_box_uint32(0));
    }

    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)((int32_t)byte + 1)));
  }
}

lean_obj_res microvmm_host_stdout_write_u8(uint32_t byte_bits) {
  uint8_t byte = (uint8_t)(byte_bits & 0xffU);

  for (;;) {
    ssize_t count = write(STDOUT_FILENO, &byte, sizeof(byte));

    if (count < 0) {
      if (errno == EINTR) {
        continue;
      }
      return lean_io_result_mk_ok(
          lean_box_uint32((uint32_t)microvmm_negative_errno(errno)));
    }
    if (count == 0) {
      return lean_io_result_mk_ok(
          lean_box_uint32((uint32_t)microvmm_negative_errno(EIO)));
    }

    return lean_io_result_mk_ok(lean_box_uint32(0));
  }
}

lean_obj_res microvmm_host_unix_listener_open(b_lean_obj_arg path_obj) {
  const char *path = lean_string_cstr(path_obj);
  struct sockaddr_un addr;
  socklen_t addr_len;
  int fd;
  int err;

  err = microvmm_prepare_unix_socket_path(path);
  if (err != 0) {
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)microvmm_negative_errno(err)));
  }
  if (strlen(path) >= sizeof(addr.sun_path)) {
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)microvmm_negative_errno(ENAMETOOLONG)));
  }

  fd = socket(AF_UNIX, SOCK_STREAM, 0);
  if (fd < 0) {
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)microvmm_negative_errno(errno)));
  }

  err = microvmm_set_nonblocking_cloexec(fd);
  if (err != 0) {
    close(fd);
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)microvmm_negative_errno(err)));
  }

  memset(&addr, 0, sizeof(addr));
  addr.sun_family = AF_UNIX;
  memcpy(addr.sun_path, path, strlen(path) + 1U);
  addr_len = (socklen_t)(offsetof(struct sockaddr_un, sun_path) + strlen(path) + 1U);

  if (bind(fd, (struct sockaddr *)&addr, addr_len) < 0) {
    err = errno;
    close(fd);
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)microvmm_negative_errno(err)));
  }
  if (listen(fd, SOMAXCONN) < 0) {
    err = errno;
    close(fd);
    unlink(path);
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)microvmm_negative_errno(err)));
  }

  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(int32_t)fd));
}

lean_obj_res microvmm_host_unix_listener_accept_nonblocking(uint32_t fd_bits) {
  int fd = (int)fd_bits;

  for (;;) {
    int client_fd = accept(fd, NULL, NULL);
    int err;

    if (client_fd < 0) {
      if (errno == EINTR) {
        continue;
      }
      if (errno == EAGAIN || errno == EWOULDBLOCK) {
        return lean_io_result_mk_ok(lean_box_uint32(0));
      }
      return lean_io_result_mk_ok(
          lean_box_uint32((uint32_t)microvmm_negative_errno(errno)));
    }

    err = microvmm_set_nonblocking_cloexec(client_fd);
    if (err != 0) {
      close(client_fd);
      return lean_io_result_mk_ok(
          lean_box_uint32((uint32_t)microvmm_negative_errno(err)));
    }

    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)((int32_t)client_fd + 1)));
  }
}

lean_obj_res microvmm_host_socket_read_u8_nonblocking(uint32_t fd_bits) {
  int fd = (int)fd_bits;

  for (;;) {
    uint8_t byte = 0;
    ssize_t count = recv(fd, &byte, sizeof(byte), 0);

    if (count < 0) {
      if (errno == EINTR) {
        continue;
      }
      if (errno == EAGAIN || errno == EWOULDBLOCK) {
        return lean_io_result_mk_ok(lean_box_uint32(0));
      }
      return lean_io_result_mk_ok(
          lean_box_uint32((uint32_t)microvmm_negative_errno(errno)));
    }
    if (count == 0) {
      return lean_io_result_mk_ok(lean_box_uint32(257));
    }

    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)((int32_t)byte + 1)));
  }
}

lean_obj_res microvmm_host_socket_write_u8_nonblocking(uint32_t fd_bits,
                                                       uint32_t byte_bits) {
  int fd = (int)fd_bits;
  uint8_t byte = (uint8_t)(byte_bits & 0xffU);

  for (;;) {
    ssize_t count = send(fd, &byte, sizeof(byte), MSG_NOSIGNAL);

    if (count < 0) {
      if (errno == EINTR) {
        continue;
      }
      return lean_io_result_mk_ok(
          lean_box_uint32((uint32_t)microvmm_negative_errno(errno)));
    }
    if (count == 0) {
      return lean_io_result_mk_ok(
          lean_box_uint32((uint32_t)microvmm_negative_errno(EIO)));
    }

    return lean_io_result_mk_ok(lean_box_uint32(0));
  }
}

lean_obj_res microvmm_host_unlink_path(b_lean_obj_arg path_obj) {
  const char *path = lean_string_cstr(path_obj);

  if (path == NULL || path[0] == '\0') {
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)microvmm_negative_errno(EINVAL)));
  }
  if (unlink(path) < 0 && errno != ENOENT) {
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)microvmm_negative_errno(errno)));
  }

  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_host_enable_wake_timer(uint32_t interval_usecs_bits) {
  uint32_t interval_usecs = interval_usecs_bits;
  struct sigaction action;
  struct itimerval timer;
  int err;

  if (interval_usecs == 0) {
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)microvmm_negative_errno(EINVAL)));
  }
  if (microvmm_wake_timer_active) {
    return lean_io_result_mk_ok(lean_box_uint32(0));
  }
  if (getitimer(ITIMER_REAL, &microvmm_previous_wake_timer) < 0) {
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)microvmm_negative_errno(errno)));
  }

  memset(&action, 0, sizeof(action));
  action.sa_handler = microvmm_wake_signal_handler;
  sigemptyset(&action.sa_mask);

  if (sigaction(SIGALRM, &action, &microvmm_previous_wake_signal_action) < 0) {
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)microvmm_negative_errno(errno)));
  }

  memset(&timer, 0, sizeof(timer));
  timer.it_interval.tv_sec = (time_t)(interval_usecs / 1000000U);
  timer.it_interval.tv_usec = (suseconds_t)(interval_usecs % 1000000U);
  timer.it_value = timer.it_interval;

  if (setitimer(ITIMER_REAL, &timer, NULL) < 0) {
    err = errno;
    sigaction(SIGALRM, &microvmm_previous_wake_signal_action, NULL);
    return lean_io_result_mk_ok(
        lean_box_uint32((uint32_t)microvmm_negative_errno(err)));
  }

  microvmm_wake_timer_active = 1;
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_host_disable_wake_timer(uint32_t ignored) {
  int err = 0;

  (void)ignored;

  if (!microvmm_wake_timer_active) {
    return lean_io_result_mk_ok(lean_box_uint32(0));
  }
  if (setitimer(ITIMER_REAL, &microvmm_previous_wake_timer, NULL) < 0) {
    err = errno;
  }
  if (sigaction(SIGALRM, &microvmm_previous_wake_signal_action, NULL) < 0 && err == 0) {
    err = errno;
  }

  microvmm_wake_timer_active = 0;
  return lean_io_result_mk_ok(
      lean_box_uint32((uint32_t)microvmm_negative_errno(err)));
}

lean_obj_res microvmm_kvm_get_vcpu_mmap_size(uint32_t fd_bits) {
  int fd = (int)fd_bits;
  int mmap_size = ioctl(fd, KVM_GET_VCPU_MMAP_SIZE, 0);
  int32_t status = mmap_size < 0 ? -(int32_t)errno : (int32_t)mmap_size;

  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_probe_vcpu_run_area(uint32_t vcpu_fd_bits, uint32_t mmap_size_bits) {
  int vcpu_fd = (int)vcpu_fd_bits;
  size_t mmap_size = (size_t)mmap_size_bits;
  long page_size = sysconf(_SC_PAGESIZE);
  void *run_area_ptr;
  int rc;

  if (page_size <= 0 || mmap_size == 0 || (mmap_size % (size_t)page_size) != 0) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  run_area_ptr = mmap(NULL, mmap_size, PROT_READ | PROT_WRITE, MAP_SHARED, vcpu_fd, 0);
  if (run_area_ptr == MAP_FAILED) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)errno)));
  }

  rc = munmap(run_area_ptr, mmap_size);
  if (rc < 0) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)errno)));
  }

  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_alloc_guest_memory(uint64_t size_bits) {
  size_t size = (size_t)size_bits;
  void *guest_memory;

  if ((uint64_t)size != size_bits || size == 0) {
    return lean_io_result_mk_ok(lean_box_uint64(microvmm_encode_pointer_error(EINVAL)));
  }

  guest_memory = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (guest_memory == MAP_FAILED) {
    return lean_io_result_mk_ok(lean_box_uint64(microvmm_encode_pointer_error(errno)));
  }

  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(uintptr_t)guest_memory));
}

lean_obj_res microvmm_kvm_free_guest_memory(uint64_t guest_memory_bits, uint64_t size_bits) {
  void *guest_memory = (void *)(uintptr_t)guest_memory_bits;
  size_t size = (size_t)size_bits;
  int32_t status;

  if ((uint64_t)size != size_bits || guest_memory == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  status = munmap(guest_memory, size) < 0 ? -(int32_t)errno : 0;
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_register_guest_memory(uint32_t vm_fd_bits, uint32_t slot_bits,
                                                uint64_t guest_phys_addr_bits,
                                                uint64_t size_bits,
                                                uint64_t guest_memory_bits) {
  int vm_fd = (int)vm_fd_bits;
  struct kvm_userspace_memory_region memory_region;
  int32_t status;

  memset(&memory_region, 0, sizeof(memory_region));
  memory_region.slot = slot_bits;
  memory_region.guest_phys_addr = guest_phys_addr_bits;
  memory_region.memory_size = size_bits;
  memory_region.userspace_addr = guest_memory_bits;

  status = ioctl(vm_fd, KVM_SET_USER_MEMORY_REGION, &memory_region) < 0 ? -(int32_t)errno : 0;
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_unregister_guest_memory(uint32_t vm_fd_bits, uint32_t slot_bits) {
  int vm_fd = (int)vm_fd_bits;
  struct kvm_userspace_memory_region memory_region;
  int32_t status;

  memset(&memory_region, 0, sizeof(memory_region));
  memory_region.slot = slot_bits;
  status = ioctl(vm_fd, KVM_SET_USER_MEMORY_REGION, &memory_region) < 0 ? -(int32_t)errno : 0;
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_create_irqchip(uint32_t vm_fd_bits) {
  int vm_fd = (int)vm_fd_bits;
  int32_t status = ioctl(vm_fd, KVM_CREATE_IRQCHIP, 0) < 0 ? -(int32_t)errno : 0;

  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_create_pit2(uint32_t vm_fd_bits) {
  int vm_fd = (int)vm_fd_bits;
  struct kvm_pit_config pit_config;
  int32_t status;

  memset(&pit_config, 0, sizeof(pit_config));
  pit_config.flags = KVM_PIT_SPEAKER_DUMMY;
  status = ioctl(vm_fd, KVM_CREATE_PIT2, &pit_config) < 0 ? -(int32_t)errno : 0;
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_set_irq_line(uint32_t vm_fd_bits, uint32_t irq_bits,
                                       uint32_t level_bits) {
  int vm_fd = (int)vm_fd_bits;
  struct kvm_irq_level irq_level;
  int32_t status;

  memset(&irq_level, 0, sizeof(irq_level));
  irq_level.irq = irq_bits;
  irq_level.level = level_bits;
  status = ioctl(vm_fd, KVM_IRQ_LINE, &irq_level) < 0 ? -(int32_t)errno : 0;
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_set_tss_addr(uint32_t vm_fd_bits, uint64_t tss_addr_bits) {
  int vm_fd = (int)vm_fd_bits;
  int32_t status = ioctl(vm_fd, KVM_SET_TSS_ADDR, (unsigned long)tss_addr_bits) < 0 ?
      -(int32_t)errno : 0;

  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_configure_cpuid(uint32_t kvm_fd_bits, uint32_t vcpu_fd_bits) {
  int32_t status = microvmm_negative_errno(
      microvmm_configure_cpuid((int)kvm_fd_bits, (int)vcpu_fd_bits));

  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_alloc_vcpu_state_buffer(uint32_t ignored) {
  struct microvmm_vcpu_state_buffer *buffer;
  (void)ignored;

  buffer = (struct microvmm_vcpu_state_buffer *)malloc(sizeof(*buffer));
  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint64(microvmm_encode_pointer_error(ENOMEM)));
  }

  memset(buffer, 0, sizeof(*buffer));
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(uintptr_t)buffer));
}

lean_obj_res microvmm_kvm_free_vcpu_state_buffer(uint64_t buffer_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;

  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  free(buffer);
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_get_sregs_into_buffer(uint32_t vcpu_fd_bits, uint64_t buffer_bits) {
  int vcpu_fd = (int)vcpu_fd_bits;
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  int32_t status;

  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  status = ioctl(vcpu_fd, KVM_GET_SREGS, &buffer->sregs) < 0 ? -(int32_t)errno : 0;
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_set_sregs_from_buffer(uint32_t vcpu_fd_bits, uint64_t buffer_bits) {
  int vcpu_fd = (int)vcpu_fd_bits;
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  int32_t status;

  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  status = ioctl(vcpu_fd, KVM_SET_SREGS, &buffer->sregs) < 0 ? -(int32_t)errno : 0;
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_vcpu_state_get_cr0(uint64_t buffer_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  uint64_t value = buffer == NULL ? 0 : buffer->sregs.cr0;

  return lean_io_result_mk_ok(lean_box_uint64(value));
}

lean_obj_res microvmm_kvm_vcpu_state_set_cr0(uint64_t buffer_bits, uint64_t value_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  buffer->sregs.cr0 = value_bits;
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_vcpu_state_set_cr3(uint64_t buffer_bits, uint64_t value_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  buffer->sregs.cr3 = value_bits;
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_vcpu_state_set_cr4(uint64_t buffer_bits, uint64_t value_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  buffer->sregs.cr4 = value_bits;
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_vcpu_state_set_efer(uint64_t buffer_bits, uint64_t value_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  buffer->sregs.efer = value_bits;
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_vcpu_state_set_gdt(uint64_t buffer_bits, uint64_t base_bits,
                                             uint32_t limit_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  buffer->sregs.gdt.base = base_bits;
  buffer->sregs.gdt.limit = (uint16_t)limit_bits;
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_vcpu_state_set_idt(uint64_t buffer_bits, uint64_t base_bits,
                                             uint32_t limit_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  buffer->sregs.idt.base = base_bits;
  buffer->sregs.idt.limit = (uint16_t)limit_bits;
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_vcpu_state_set_flat_segment(uint64_t buffer_bits, uint32_t slot_bits,
                                                      uint32_t selector_bits,
                                                      uint32_t type_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  struct kvm_segment *segment;

  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  segment = microvmm_vcpu_segment_slot(buffer, slot_bits);
  if (segment == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  *segment = microvmm_flat_segment((uint16_t)selector_bits, (uint8_t)type_bits);
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_vcpu_state_clear_regs(uint64_t buffer_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  memset(&buffer->regs, 0, sizeof(buffer->regs));
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_vcpu_state_set_rip(uint64_t buffer_bits, uint64_t value_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }
  buffer->regs.rip = value_bits;
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_vcpu_state_set_rsi(uint64_t buffer_bits, uint64_t value_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }
  buffer->regs.rsi = value_bits;
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_vcpu_state_set_rsp(uint64_t buffer_bits, uint64_t value_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }
  buffer->regs.rsp = value_bits;
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_vcpu_state_set_rflags(uint64_t buffer_bits, uint64_t value_bits) {
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }
  buffer->regs.rflags = value_bits;
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_set_regs_from_buffer(uint32_t vcpu_fd_bits, uint64_t buffer_bits) {
  int vcpu_fd = (int)vcpu_fd_bits;
  struct microvmm_vcpu_state_buffer *buffer =
      (struct microvmm_vcpu_state_buffer *)(uintptr_t)buffer_bits;
  int32_t status;

  if (buffer == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  status = ioctl(vcpu_fd, KVM_SET_REGS, &buffer->regs) < 0 ? -(int32_t)errno : 0;
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_prepare_virtio_mmio_entropy_guest(uint64_t guest_memory_bits,
                                                            uint64_t guest_memory_size_bits) {
  void *guest_memory = (void *)(uintptr_t)guest_memory_bits;
  size_t guest_memory_size = (size_t)guest_memory_size_bits;
  int32_t status;

  if ((uint64_t)guest_memory_size != guest_memory_size_bits || guest_memory == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  status = microvmm_negative_errno(
      microvmm_prepare_virtio_rng_guest(guest_memory, guest_memory_size));
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_map_run_area(uint32_t vcpu_fd_bits, uint32_t mmap_size_bits) {
  int vcpu_fd = (int)vcpu_fd_bits;
  size_t mmap_size = (size_t)mmap_size_bits;
  long page_size = sysconf(_SC_PAGESIZE);
  void *run_area_ptr;

  if (page_size <= 0 || mmap_size == 0 || (mmap_size % (size_t)page_size) != 0) {
    return lean_io_result_mk_ok(lean_box_uint64(microvmm_encode_pointer_error(EINVAL)));
  }

  run_area_ptr = mmap(NULL, mmap_size, PROT_READ | PROT_WRITE, MAP_SHARED, vcpu_fd, 0);
  if (run_area_ptr == MAP_FAILED) {
    return lean_io_result_mk_ok(lean_box_uint64(microvmm_encode_pointer_error(errno)));
  }

  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(uintptr_t)run_area_ptr));
}

lean_obj_res microvmm_kvm_unmap_run_area(uint64_t run_area_bits, uint32_t mmap_size_bits) {
  void *run_area_ptr = (void *)(uintptr_t)run_area_bits;
  size_t mmap_size = (size_t)mmap_size_bits;
  int32_t status;

  if (run_area_ptr == NULL || mmap_size == 0) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  status = munmap(run_area_ptr, mmap_size) < 0 ? -(int32_t)errno : 0;
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_run(uint32_t vcpu_fd_bits) {
  int vcpu_fd = (int)vcpu_fd_bits;
  int32_t status = ioctl(vcpu_fd, KVM_RUN, 0) < 0 ? -(int32_t)errno : 0;

  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}

lean_obj_res microvmm_kvm_run_exit_reason(uint64_t run_area_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  return lean_io_result_mk_ok(lean_box_uint32(run == NULL ? 0U : run->exit_reason));
}

lean_obj_res microvmm_kvm_run_io_direction(uint64_t run_area_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  return lean_io_result_mk_ok(lean_box_uint32(run == NULL ? 0U : run->io.direction));
}

lean_obj_res microvmm_kvm_run_io_port(uint64_t run_area_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  return lean_io_result_mk_ok(lean_box_uint32(run == NULL ? 0U : run->io.port));
}

lean_obj_res microvmm_kvm_run_io_size(uint64_t run_area_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  return lean_io_result_mk_ok(lean_box_uint32(run == NULL ? 0U : run->io.size));
}

lean_obj_res microvmm_kvm_run_io_count(uint64_t run_area_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  return lean_io_result_mk_ok(lean_box_uint32(run == NULL ? 0U : run->io.count));
}

lean_obj_res microvmm_kvm_run_io_data_u8(uint64_t run_area_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  if (run == NULL || run->io.size != 1U || run->io.count != 1U) {
    return lean_io_result_mk_ok(lean_box_uint32(0));
  }

  return lean_io_result_mk_ok(lean_box_uint32(*((uint8_t *)run + run->io.data_offset)));
}

lean_obj_res microvmm_kvm_run_io_data_u16(uint64_t run_area_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  if (run == NULL || run->io.size != 2U || run->io.count != 1U) {
    return lean_io_result_mk_ok(lean_box_uint32(0));
  }

  return lean_io_result_mk_ok(lean_box_uint32(
      microvmm_load_u16_le((uint8_t *)run + run->io.data_offset)));
}

lean_obj_res microvmm_kvm_run_io_data_u32(uint64_t run_area_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  if (run == NULL || run->io.size != 4U || run->io.count != 1U) {
    return lean_io_result_mk_ok(lean_box_uint32(0));
  }

  return lean_io_result_mk_ok(lean_box_uint32(
      microvmm_load_u32_le((uint8_t *)run + run->io.data_offset)));
}

lean_obj_res microvmm_kvm_run_set_io_data_u8(uint64_t run_area_bits, uint32_t value_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  if (run == NULL || run->io.size != 1U || run->io.count != 1U) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  *((uint8_t *)run + run->io.data_offset) = (uint8_t)value_bits;
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_run_set_io_data_u16(uint64_t run_area_bits, uint32_t value_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  if (run == NULL || run->io.size != 2U || run->io.count != 1U) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  microvmm_store_u16_le((uint8_t *)run + run->io.data_offset, (uint16_t)value_bits);
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_run_set_io_data_u32(uint64_t run_area_bits, uint32_t value_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  if (run == NULL || run->io.size != 4U || run->io.count != 1U) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  microvmm_store_u32_le((uint8_t *)run + run->io.data_offset, value_bits);
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_run_mmio_phys_addr(uint64_t run_area_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  return lean_io_result_mk_ok(lean_box_uint64(run == NULL ? 0U : run->mmio.phys_addr));
}

lean_obj_res microvmm_kvm_run_mmio_len(uint64_t run_area_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  return lean_io_result_mk_ok(lean_box_uint32(run == NULL ? 0U : run->mmio.len));
}

lean_obj_res microvmm_kvm_run_mmio_is_write(uint64_t run_area_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  return lean_io_result_mk_ok(lean_box_uint32(run == NULL ? 0U : run->mmio.is_write));
}

lean_obj_res microvmm_kvm_run_mmio_data_u32(uint64_t run_area_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;
  return lean_io_result_mk_ok(
      lean_box_uint32(run == NULL ? 0U : microvmm_load_u32_le(run->mmio.data)));
}

lean_obj_res microvmm_kvm_run_set_mmio_data_u32(uint64_t run_area_bits, uint32_t value_bits) {
  struct kvm_run *run = (struct kvm_run *)(uintptr_t)run_area_bits;

  if (run == NULL) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(-(int32_t)EINVAL)));
  }

  microvmm_store_u32_le(run->mmio.data, value_bits);
  return lean_io_result_mk_ok(lean_box_uint32(0));
}

lean_obj_res microvmm_kvm_guest_read_u8_packed(uint64_t guest_memory_bits,
                                               uint64_t guest_memory_size_bits,
                                               uint64_t guest_addr_bits) {
  const uint8_t *guest_memory = (const uint8_t *)(uintptr_t)guest_memory_bits;
  size_t guest_memory_size = (size_t)guest_memory_size_bits;
  uint8_t value = 0;
  int err;

  err = guest_memory == NULL ? EINVAL :
      microvmm_guest_read_bytes(guest_memory, guest_memory_size, guest_addr_bits, &value,
                                sizeof(value));
  return lean_io_result_mk_ok(lean_box_uint64(microvmm_pack_read_result(err, value)));
}

lean_obj_res microvmm_kvm_guest_read_u16_packed(uint64_t guest_memory_bits,
                                                uint64_t guest_memory_size_bits,
                                                uint64_t guest_addr_bits) {
  const uint8_t *guest_memory = (const uint8_t *)(uintptr_t)guest_memory_bits;
  size_t guest_memory_size = (size_t)guest_memory_size_bits;
  uint8_t bytes[2] = {0, 0};
  uint16_t value = 0;
  int err;

  err = guest_memory == NULL ? EINVAL :
      microvmm_guest_read_bytes(guest_memory, guest_memory_size, guest_addr_bits, bytes,
                                sizeof(bytes));
  if (err == 0) {
    value = microvmm_load_u16_le(bytes);
  }

  return lean_io_result_mk_ok(lean_box_uint64(microvmm_pack_read_result(err, value)));
}

lean_obj_res microvmm_kvm_guest_read_u32_packed(uint64_t guest_memory_bits,
                                                uint64_t guest_memory_size_bits,
                                                uint64_t guest_addr_bits) {
  const uint8_t *guest_memory = (const uint8_t *)(uintptr_t)guest_memory_bits;
  size_t guest_memory_size = (size_t)guest_memory_size_bits;
  uint8_t bytes[4] = {0, 0, 0, 0};
  uint32_t value = 0;
  int err;

  err = guest_memory == NULL ? EINVAL :
      microvmm_guest_read_bytes(guest_memory, guest_memory_size, guest_addr_bits, bytes,
                                sizeof(bytes));
  if (err == 0) {
    value = microvmm_load_u32_le(bytes);
  }

  return lean_io_result_mk_ok(lean_box_uint64(microvmm_pack_read_result(err, value)));
}

lean_obj_res microvmm_kvm_guest_write_u8(uint64_t guest_memory_bits,
                                         uint64_t guest_memory_size_bits,
                                         uint64_t guest_addr_bits, uint32_t value_bits) {
  uint8_t *guest_memory = (uint8_t *)(uintptr_t)guest_memory_bits;
  size_t guest_memory_size = (size_t)guest_memory_size_bits;
  uint8_t value = (uint8_t)value_bits;
  int err;

  err = guest_memory == NULL ? EINVAL :
      microvmm_guest_write_bytes(guest_memory, guest_memory_size, guest_addr_bits, &value,
                                 sizeof(value));
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)microvmm_negative_errno(err)));
}

lean_obj_res microvmm_kvm_guest_write_u16(uint64_t guest_memory_bits,
                                          uint64_t guest_memory_size_bits,
                                          uint64_t guest_addr_bits, uint32_t value_bits) {
  uint8_t *guest_memory = (uint8_t *)(uintptr_t)guest_memory_bits;
  size_t guest_memory_size = (size_t)guest_memory_size_bits;
  uint8_t bytes[2];
  int err;

  microvmm_store_u16_le(bytes, (uint16_t)value_bits);
  err = guest_memory == NULL ? EINVAL :
      microvmm_guest_write_bytes(guest_memory, guest_memory_size, guest_addr_bits, bytes,
                                 sizeof(bytes));
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)microvmm_negative_errno(err)));
}

lean_obj_res microvmm_kvm_guest_write_u32(uint64_t guest_memory_bits,
                                          uint64_t guest_memory_size_bits,
                                          uint64_t guest_addr_bits, uint32_t value_bits) {
  uint8_t *guest_memory = (uint8_t *)(uintptr_t)guest_memory_bits;
  size_t guest_memory_size = (size_t)guest_memory_size_bits;
  uint8_t bytes[4];
  int err;

  microvmm_store_u32_le(bytes, value_bits);
  err = guest_memory == NULL ? EINVAL :
      microvmm_guest_write_bytes(guest_memory, guest_memory_size, guest_addr_bits, bytes,
                                 sizeof(bytes));
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)microvmm_negative_errno(err)));
}

lean_obj_res microvmm_kvm_guest_write_byte_array(uint64_t guest_memory_bits,
                                                 uint64_t guest_memory_size_bits,
                                                 uint64_t guest_addr_bits,
                                                 b_lean_obj_arg bytes) {
  uint8_t *guest_memory = (uint8_t *)(uintptr_t)guest_memory_bits;
  size_t guest_memory_size = (size_t)guest_memory_size_bits;
  const uint8_t *src = lean_sarray_cptr((lean_object *)bytes);
  size_t src_size = lean_sarray_size(bytes);
  int err;

  err = guest_memory == NULL ? EINVAL :
      microvmm_guest_write_bytes(guest_memory, guest_memory_size, guest_addr_bits, src, src_size);
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)microvmm_negative_errno(err)));
}

lean_obj_res microvmm_kvm_close(uint32_t fd_bits) {
  int fd = (int)fd_bits;
  int rc = close(fd);
  int32_t status = rc < 0 ? -(int32_t)errno : 0;

  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)status));
}