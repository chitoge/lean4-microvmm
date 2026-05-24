#!/bin/sh
set -eu

export PATH=/usr/sbin:/usr/bin:/sbin:/bin
export HOME=/root
export TERM=vt100
export PS1='microvmm> '

mkdir -p /dev /dev/pts /proc /run /sys /tmp /root

mount -t devtmpfs devtmpfs /dev 2>/dev/null || true
[ -c /dev/console ] || mknod -m 600 /dev/console c 5 1
[ -c /dev/null ] || mknod -m 666 /dev/null c 1 3
[ -c /dev/tty ] || mknod -m 666 /dev/tty c 5 0
[ -c /dev/ttyS0 ] || mknod -m 600 /dev/ttyS0 c 4 64

exec </dev/console >/dev/console 2>&1 || true

mount -t proc proc /proc 2>/dev/null || true
mount -t sysfs sysfs /sys 2>/dev/null || true
mount -t devpts devpts /dev/pts 2>/dev/null || true
mount -t tmpfs tmpfs /run 2>/dev/null || true

wait_for_dir() {
  path=$1
  retries=$2

  while [ "$retries" -gt 0 ]; do
    if [ -d "$path" ]; then
      return 0
    fi
    retries=$((retries - 1))
    [ "$retries" -gt 0 ] || break
    sleep 1
  done

  return 1
}

wait_for_file() {
  path=$1
  retries=$2

  while [ "$retries" -gt 0 ]; do
    if [ -r "$path" ]; then
      return 0
    fi
    retries=$((retries - 1))
    [ "$retries" -gt 0 ] || break
    sleep 1
  done

  return 1
}

wait_for_char() {
  path=$1
  retries=$2

  while [ "$retries" -gt 0 ]; do
    if [ -c "$path" ]; then
      return 0
    fi
    retries=$((retries - 1))
    [ "$retries" -gt 0 ] || break
    sleep 1
  done

  return 1
}

read_trimmed_file() {
  cat "$1" 2>/dev/null || true
}

install_virtio_rng_read_command() {
  cat > /bin/virtio-rng-read <<'EOF'
#!/bin/sh
set -eu

if [ "$#" -ne 1 ]; then
  echo "usage: virtio-rng-read N" >&2
  exit 2
fi

byte_count=$1
case "$byte_count" in
  ''|*[!0-9]*)
    echo "virtio-rng-read: N must be a positive decimal byte count" >&2
    exit 2
    ;;
  0)
    echo "virtio-rng-read: N must be greater than 0" >&2
    exit 2
    ;;
esac

if [ ! -c /dev/hwrng ]; then
  echo "virtio-rng-read: /dev/hwrng is unavailable" >&2
  exit 1
fi

rng_byte_line=$(dd if=/dev/hwrng bs="$byte_count" count=1 2>/dev/null | od -An -tx1 -v 2>/dev/null || true)
set -- $rng_byte_line
if [ "$#" -ne "$byte_count" ]; then
  echo "virtio-rng-read: requested $byte_count bytes, got $# bytes" >&2
  exit 1
fi

printf '%s\n' "$*"
EOF

  chmod 0755 /bin/virtio-rng-read
}

install_virtio_rng_read_command

virtio_verify_ok=1
virtio_pci_bdf=0000:00:01.0
virtio_pci_path=/sys/bus/pci/devices/$virtio_pci_bdf
virtio_vendor_expected=0x1af4
virtio_device_expected=0x1044
virtio_rng_name=virtio_rng
virtio_rng_byte_count=32

virtio_rng_chunks_advance() {
  set -- $1
  if [ "$#" -ne "$virtio_rng_byte_count" ]; then
    return 1
  fi

  chunk0="$1 $2 $3 $4 $5 $6 $7 $8"
  shift 8
  chunk1="$1 $2 $3 $4 $5 $6 $7 $8"
  shift 8
  chunk2="$1 $2 $3 $4 $5 $6 $7 $8"
  shift 8
  chunk3="$1 $2 $3 $4 $5 $6 $7 $8"

  [ "$chunk0" != "$chunk1" ] &&
    [ "$chunk0" != "$chunk2" ] &&
    [ "$chunk0" != "$chunk3" ] &&
    [ "$chunk1" != "$chunk2" ] &&
    [ "$chunk1" != "$chunk3" ] &&
    [ "$chunk2" != "$chunk3" ]
}

# This slice exposes exactly one virtio PCI function at a fixed BDF, so verify that exact sysfs node.
if wait_for_dir "$virtio_pci_path" 5; then
  virtio_vendor=$(read_trimmed_file "$virtio_pci_path/vendor")
  virtio_device=$(read_trimmed_file "$virtio_pci_path/device")
  if [ "$virtio_vendor" = "$virtio_vendor_expected" ] && [ "$virtio_device" = "$virtio_device_expected" ]; then
    echo "MICROVMM_VIRTIO_PCI_SYSFS_OK bdf=$virtio_pci_bdf vendor=$virtio_vendor device=$virtio_device"
  else
    virtio_verify_ok=0
    echo "MICROVMM_VIRTIO_PCI_SYSFS_FAIL bdf=$virtio_pci_bdf vendor=${virtio_vendor:-missing} device=${virtio_device:-missing} expected_vendor=$virtio_vendor_expected expected_device=$virtio_device_expected"
  fi
else
  virtio_verify_ok=0
  echo "MICROVMM_VIRTIO_PCI_SYSFS_FAIL bdf=$virtio_pci_bdf reason=missing_device"
fi

rng_current_path=/sys/class/misc/hw_random/rng_current
rng_available_path=/sys/class/misc/hw_random/rng_available
if [ ! -r "$rng_current_path" ]; then
  rng_current_path=/sys/devices/virtual/misc/hw_random/rng_current
  rng_available_path=/sys/devices/virtual/misc/hw_random/rng_available
fi

if wait_for_file "$rng_current_path" 5 && wait_for_file "$rng_available_path" 5; then
  rng_current=$(read_trimmed_file "$rng_current_path")
  rng_available=$(read_trimmed_file "$rng_available_path")
  case "$rng_current" in
    "$virtio_rng_name"*)
      rng_current_is_virtio=1
      ;;
    *)
      rng_current_is_virtio=0
      ;;
  esac
  case " $rng_available " in
    *" ${virtio_rng_name}"*)
      rng_available_has_virtio=1
      ;;
    *)
      rng_available_has_virtio=0
      ;;
  esac
  if [ "$rng_current_is_virtio" -eq 1 ] && [ "$rng_available_has_virtio" -eq 1 ]; then
    echo "MICROVMM_VIRTIO_RNG_SOURCE_OK source=$virtio_rng_name current=$rng_current available=$rng_available"
  else
    virtio_verify_ok=0
    echo "MICROVMM_VIRTIO_RNG_SOURCE_FAIL current=${rng_current:-missing} available=${rng_available:-missing} expected=$virtio_rng_name"
  fi
else
  virtio_verify_ok=0
  echo "MICROVMM_VIRTIO_RNG_SOURCE_FAIL reason=missing_hw_random_sysfs"
fi

# Keep the wait bounded so a missing hwrng device reports a stable failure marker instead of hanging boot.
# Linux can consume deterministic virtio-rng output before /init reads /dev/hwrng, so the
# guest check validates that the stream advances across four 8-byte chunks instead of assuming
# the first post-boot read still starts at offset 0.
if wait_for_char /dev/hwrng 5; then
  rng_byte_line=$(dd if=/dev/hwrng bs=$virtio_rng_byte_count count=1 2>/dev/null | od -An -tx1 -v 2>/dev/null || true)
  set -- $rng_byte_line
  if [ "$#" -eq "$virtio_rng_byte_count" ]; then
    rng_bytes="$*"
  else
    rng_bytes=
  fi
  if [ -n "$rng_bytes" ] && virtio_rng_chunks_advance "$rng_bytes"; then
    echo "MICROVMM_VIRTIO_RNG_BYTES_OK bytes=$rng_bytes"
  else
    virtio_verify_ok=0
    echo "MICROVMM_VIRTIO_RNG_BYTES_FAIL bytes=${rng_bytes:-missing} expected=distinct_8byte_chunks"
  fi
else
  virtio_verify_ok=0
  echo "MICROVMM_VIRTIO_RNG_BYTES_FAIL reason=missing_dev_hwrng"
fi

if [ "$virtio_verify_ok" -eq 1 ]; then
  echo MICROVMM_VIRTIO_GUEST_VERIFY_OK
else
  echo MICROVMM_VIRTIO_GUEST_VERIFY_FAIL
fi

# Keep the existing host-side readiness gate after verification markers so interactive handoff stays unchanged.
echo MICROVMM_INITRD_READY

if command -v cttyhack >/dev/null 2>&1; then
  exec cttyhack sh -i
fi

exec sh -i