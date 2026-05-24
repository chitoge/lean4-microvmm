#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)

usage() {
  cat <<EOF
Usage: $(basename "$0") [kernel-version] [output-path] [--source-dir PATH]

Build a Linux bzImage for Microvmm.

Source selection order:
  1. --source-dir PATH
  2. LINUX_SOURCE_DIR
  3. LINUX_SUBMODULE_DIR or $repo_root/third_party/linux
  4. Downloaded release tarball under artifacts/kernel/src
EOF
}

resolve_repo_path() {
  case "$1" in
    /*) printf '%s\n' "$1" ;;
    *) printf '%s/%s\n' "$repo_root" "$1" ;;
  esac
}

detect_kernel_version() {
  local makefile_path=$1/Makefile
  [[ -f "$makefile_path" ]] || return 1

  awk '
    $1 == "VERSION" { version = $3 }
    $1 == "PATCHLEVEL" { patchlevel = $3 }
    END {
      if (version == "" || patchlevel == "") {
        exit 1
      }

      printf "%s.%s\n", version, patchlevel
    }
  ' "$makefile_path"
}

kernel_version_arg=
output_path_arg=
source_dir_override=${LINUX_SOURCE_DIR:-}

while (($# > 0)); do
  case "$1" in
    --source-dir)
      if (($# < 2)); then
        printf 'missing value for %s\n' "$1" >&2
        exit 1
      fi
      source_dir_override=$2
      shift 2
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    --)
      shift
      break
      ;;
    -*)
      printf 'unknown option: %s\n' "$1" >&2
      usage >&2
      exit 1
      ;;
    *)
      if [[ -z "$kernel_version_arg" ]]; then
        kernel_version_arg=$1
      elif [[ -z "$output_path_arg" ]]; then
        output_path_arg=$1
      else
        printf 'unexpected argument: %s\n' "$1" >&2
        usage >&2
        exit 1
      fi
      shift
      ;;
  esac
done

if (($# > 0)); then
  printf 'unexpected argument: %s\n' "$1" >&2
  usage >&2
  exit 1
fi

source_dir=
source_mode=

if [[ -n "$source_dir_override" ]]; then
  source_dir=$(resolve_repo_path "$source_dir_override")
  source_mode=override
else
  submodule_source_dir=${LINUX_SUBMODULE_DIR:-"$repo_root/third_party/linux"}
  submodule_source_dir=$(resolve_repo_path "$submodule_source_dir")
  if [[ -f "$submodule_source_dir/Makefile" ]]; then
    source_dir=$submodule_source_dir
    source_mode=submodule
  fi
fi

if [[ -n "$kernel_version_arg" ]]; then
  kernel_version=$kernel_version_arg
elif [[ -n "$source_dir" ]]; then
  kernel_version=$(detect_kernel_version "$source_dir") || {
    printf 'failed to detect kernel version from source tree: %s\n' "$source_dir" >&2
    exit 1
  }
else
  kernel_version=$(uname -r | cut -d. -f1-2)
fi

output_path=${output_path_arg:-"$repo_root/artifacts/kernel/linux-${kernel_version}-microvmm-bzImage"}

case "$output_path" in
  /*) ;;
  *) output_path="$repo_root/$output_path" ;;
esac

series_dir="v${kernel_version%%.*}.x"
tarball_url=${KERNEL_URL:-"https://cdn.kernel.org/pub/linux/kernel/${series_dir}/linux-${kernel_version}.tar.xz"}
cache_dir="$repo_root/artifacts/kernel/cache"
source_root="$repo_root/artifacts/kernel/src"
build_root="$repo_root/artifacts/kernel/build/linux-${kernel_version}"
tarball_path="$cache_dir/linux-${kernel_version}.tar.xz"
if [[ -z "$source_dir" ]]; then
  source_dir="$source_root/linux-${kernel_version}"
  source_mode=tarball
fi
config_path="$output_path.config"
jobs=${JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc 2>/dev/null || echo 1)}

require_tool() {
  if ! command -v "$1" >/dev/null 2>&1; then
    printf 'missing required tool: %s\n' "$1" >&2
    exit 1
  fi
}

require_tool bc
require_tool bison
require_tool flex
require_tool gcc
require_tool install
require_tool make
require_tool perl

mkdir -p "$build_root" "$(dirname -- "$output_path")"

if [[ "$source_mode" == tarball ]]; then
  require_tool curl
  require_tool tar
  require_tool xz

  mkdir -p "$cache_dir" "$source_root"

  if [[ ! -f "$tarball_path" ]]; then
    curl --fail --location --output "$tarball_path" "$tarball_url"
  fi

  if [[ ! -d "$source_dir" ]]; then
    tar -C "$source_root" -xf "$tarball_path"
  fi
elif [[ ! -f "$source_dir/Makefile" ]]; then
  printf 'kernel source tree not found: %s\n' "$source_dir" >&2
  exit 1
fi

make -C "$source_dir" O="$build_root" ARCH=x86_64 x86_64_defconfig >/dev/null

# Keep the guest-side virtio-rng-over-PCI contract explicit instead of inheriting it from
# whatever x86_64_defconfig happens to select on this kernel release.
"$source_dir/scripts/config" --file "$build_root/.config" \
  -d MODULES \
  -d DEBUG_INFO \
  -d DEBUG_KERNEL \
  -d KALLSYMS_ALL \
  -d RANDOMIZE_BASE \
  -d STACK_VALIDATION \
  -d UNWINDER_ORC \
  -e BLK_DEV_INITRD \
  -e BINFMT_ELF \
  -e DEVTMPFS \
  -e DEVTMPFS_MOUNT \
  -e PROC_FS \
  -e PCI \
  -e RD_GZIP \
  -e SERIAL_8250 \
  -e SERIAL_8250_CONSOLE \
  -e SERIAL_8250_DEPRECATED_OPTIONS \
  -e SYSFS \
  -e TMPFS \
  -e TTY \
  -e UNIX \
  -e UNWINDER_FRAME_POINTER \
  -e VT \
  -e VIRTIO \
  -e VIRTIO_MENU \
  -e VIRTIO_PCI \
  -e VIRTIO_PCI_LIB \
  -e HW_RANDOM \
  -e HW_RANDOM_VIRTIO \
  -e KERNEL_GZIP \
  -d KERNEL_BZIP2 \
  -d KERNEL_LZMA \
  -d KERNEL_LZO \
  -d KERNEL_LZ4 \
  -d KERNEL_XZ \
  -d KERNEL_ZSTD \
  --set-str LOCALVERSION "-microvmm" \
  --set-str SYSTEM_TRUSTED_KEYS "" \
  --set-str SYSTEM_REVOCATION_KEYS ""

make -C "$source_dir" O="$build_root" ARCH=x86_64 olddefconfig >/dev/null
make -C "$source_dir" O="$build_root" ARCH=x86_64 -j"$jobs" bzImage

install -m 0644 "$build_root/arch/x86/boot/bzImage" "$output_path"
install -m 0644 "$build_root/.config" "$config_path"

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum "$output_path" | awk '{print $1}' > "$output_path.sha256"
fi

printf 'source %s (%s)\n' "$source_dir" "$source_mode"
printf 'built %s\n' "$output_path"
printf 'config %s\n' "$config_path"
if [[ -f "$output_path.sha256" ]]; then
  printf 'sha256 %s\n' "$(cat "$output_path.sha256")"
fi