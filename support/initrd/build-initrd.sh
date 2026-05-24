#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)

output_path=${1:-"$repo_root/artifacts/initrd/microvmm-initrd.cpio.gz"}
busybox_version=${BUSYBOX_VERSION:-1.38.0}
busybox_base_url=${BUSYBOX_BASE_URL:-https://busybox.net/downloads}
busybox_tarball="busybox-${busybox_version}.tar.bz2"
busybox_tarball_url="${busybox_base_url}/${busybox_tarball}"
busybox_sha_url="${busybox_tarball_url}.sha256"
cache_dir=${BUSYBOX_CACHE_DIR:-"$repo_root/artifacts/initrd/cache"}
dist_dir="$cache_dir/dist"
source_root="$cache_dir/src"
build_root="$cache_dir/build"
tarball_path="$dist_dir/$busybox_tarball"
sha_cache_path="$dist_dir/${busybox_tarball}.sha256"
source_dir="$source_root/busybox-$busybox_version"
build_dir="$build_root/busybox-$busybox_version"
busybox_binary="$build_dir/busybox"
busybox_config_fragment="$repo_root/support/initrd/busybox.config"
init_template="$repo_root/support/initrd/init.busybox.sh"
jobs=${JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc 2>/dev/null || echo 1)}

case "$output_path" in
  *.cpio.gz) ;;
  *)
    printf 'expected output path to end in .cpio.gz\n' >&2
    exit 1
    ;;
esac

require_tool() {
  if ! command -v "$1" >/dev/null 2>&1; then
    printf 'missing required tool: %s\n' "$1" >&2
    exit 1
  fi
}

require_tool cpio
require_tool curl
require_tool find
require_tool gzip
require_tool make
require_tool sort
require_tool sed
require_tool sha256sum
require_tool tar
require_tool touch
require_tool yes

archive_path=${output_path%.gz}
sha_path=${output_path}.sha256
output_dir=$(dirname -- "$output_path")
workdir=$(mktemp -d "${TMPDIR:-/tmp}/microvmm-initrd.XXXXXX")
rootfs_dir=$workdir/rootfs

trap 'rm -rf "$workdir"' EXIT

download_file() {
  local url=$1
  local destination=$2

  curl --fail --location --silent --show-error --output "$destination" "$url"
}

read_sha256_file() {
  awk '{print $1}' "$1"
}

verify_tarball() {
  local expected_sha actual_sha

  expected_sha=$(read_sha256_file "$sha_cache_path")
  actual_sha=$(sha256sum "$tarball_path" | awk '{print $1}')
  if [[ "$actual_sha" != "$expected_sha" ]]; then
    printf 'busybox tarball checksum mismatch: expected %s, got %s\n' "$expected_sha" "$actual_sha" >&2
    exit 1
  fi
}

ensure_busybox_source() {
  mkdir -p "$dist_dir" "$source_root" "$build_root" "$build_dir"

  if [[ ! -f "$tarball_path" ]]; then
    download_file "$busybox_tarball_url" "$tarball_path"
  fi

  if [[ ! -f "$sha_cache_path" ]]; then
    download_file "$busybox_sha_url" "$sha_cache_path"
  fi

  verify_tarball

  if [[ ! -d "$source_dir" ]]; then
    tar -C "$source_root" -xf "$tarball_path"
  fi
}

set_kconfig_value() {
  local config_path=$1
  local key=$2
  local value=$3
  local disabled_pattern="# ${key} is not set"

  if grep -q "^${key}=" "$config_path"; then
    sed -i "s|^${key}=.*|${key}=${value}|" "$config_path"
  elif grep -q "^${disabled_pattern}$" "$config_path"; then
    sed -i "s|^${disabled_pattern}$|${key}=${value}|" "$config_path"
  else
    printf '%s=%s\n' "$key" "$value" >> "$config_path"
  fi
}

disable_kconfig_value() {
  local config_path=$1
  local key=${2%% is not set}
  local disabled_line="# ${key} is not set"

  if grep -q "^${key}=" "$config_path"; then
    sed -i "s|^${key}=.*|${disabled_line}|" "$config_path"
  elif ! grep -q "^${disabled_line}$" "$config_path"; then
    printf '%s\n' "$disabled_line" >> "$config_path"
  fi
}

apply_busybox_config_fragment() {
  local config_path=$1

  while IFS= read -r line || [[ -n "$line" ]]; do
    case "$line" in
      '# CONFIG_'*' is not set')
        disable_kconfig_value "$config_path" "${line#'# '}"
        ;;
      ''|'#'*)
        continue
        ;;
      CONFIG_*=*)
        set_kconfig_value "$config_path" "${line%%=*}" "${line#*=}"
        ;;
      *)
        printf 'unsupported BusyBox config line: %s\n' "$line" >&2
        exit 1
        ;;
    esac
  done < "$busybox_config_fragment"
}

build_busybox() {
  local build_config=$build_dir/.config
  local old_pipefail=0

  make -C "$source_dir" O="$build_dir" defconfig >/dev/null
  apply_busybox_config_fragment "$build_config"
  if set -o | grep -q '^pipefail[[:space:]]*on$'; then
    old_pipefail=1
    set +o pipefail
  fi
  KCONFIG_NOTIMESTAMP=1 \
  SOURCE_DATE_EPOCH=0 \
  KBUILD_BUILD_TIMESTAMP='1970-01-01' \
  KBUILD_BUILD_USER='microvmm' \
  KBUILD_BUILD_HOST='builder' \
  yes '' | make -C "$source_dir" O="$build_dir" oldconfig >/dev/null
  if ((old_pipefail)); then
    set -o pipefail
  fi
  KCONFIG_NOTIMESTAMP=1 \
  SOURCE_DATE_EPOCH=0 \
  KBUILD_BUILD_TIMESTAMP='1970-01-01' \
  KBUILD_BUILD_USER='microvmm' \
  KBUILD_BUILD_HOST='builder' \
  make -C "$source_dir" O="$build_dir" -j"$jobs" busybox >/dev/null
}

install_rootfs() {
  mkdir -p "$rootfs_dir"
  KCONFIG_NOTIMESTAMP=1 \
  SOURCE_DATE_EPOCH=0 \
  KBUILD_BUILD_TIMESTAMP='1970-01-01' \
  KBUILD_BUILD_USER='microvmm' \
  KBUILD_BUILD_HOST='builder' \
  make -C "$source_dir" O="$build_dir" CONFIG_PREFIX="$rootfs_dir" install >/dev/null
}

mkdir -p "$output_dir" "$rootfs_dir" \
  "$rootfs_dir/dev" "$rootfs_dir/proc" "$rootfs_dir/sys" \
  "$rootfs_dir/tmp" "$rootfs_dir/run" "$rootfs_dir/etc"

ensure_busybox_source
build_busybox
install_rootfs

cat > "$rootfs_dir/etc/microvmm-initrd-release" <<'EOF'
MICROVMM_INITRD_READY
EOF

install -m 0755 "$init_template" "$rootfs_dir/init"
chmod 0644 "$rootfs_dir/etc/microvmm-initrd-release"
find "$rootfs_dir" -exec touch -h -d '@0' {} +

(
  cd "$rootfs_dir"
  find . -print0 | LC_ALL=C sort -z | \
    cpio --null -o -H newc --quiet --owner=0:0 --reproducible > "$archive_path"
)

gzip -n -9 < "$archive_path" > "$output_path"
rm -f "$archive_path"

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum "$output_path" | awk '{print $1}' > "$sha_path"
fi

printf 'built %s\n' "$output_path"
if [[ -f "$sha_path" ]]; then
  printf 'sha256 %s\n' "$(cat "$sha_path")"
fi