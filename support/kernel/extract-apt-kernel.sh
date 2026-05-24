#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)

package_name=${1:-"linux-image-$(uname -r)"}
output_dir=${2:-"$repo_root/artifacts/kernel"}
case "$output_dir" in
  /*) ;;
  *) output_dir="$repo_root/$output_dir" ;;
esac
workdir=$(mktemp -d "${TMPDIR:-/tmp}/microvmm-kernel.XXXXXX")

trap 'rm -rf "$workdir"' EXIT

require_tool() {
  if ! command -v "$1" >/dev/null 2>&1; then
    printf 'missing required tool: %s\n' "$1" >&2
    exit 1
  fi
}

require_tool apt
require_tool dpkg-deb
require_tool find
require_tool install
require_tool mktemp

mkdir -p "$output_dir"

(
  cd "$workdir"
  apt download "$package_name" >/dev/null

  deb_path=$(find . -maxdepth 1 -type f -name '*.deb' | LC_ALL=C sort | head -n 1)
  if [[ -z "$deb_path" ]]; then
    printf 'failed to download package: %s\n' "$package_name" >&2
    exit 1
  fi

  extract_dir=$workdir/extracted
  dpkg-deb -x "$deb_path" "$extract_dir"

  kernel_path=$(find "$extract_dir/boot" -maxdepth 1 -type f -name 'vmlinuz-*' | LC_ALL=C sort | head -n 1)
  if [[ -z "$kernel_path" ]]; then
    printf 'package did not contain a bootable kernel image: %s\n' "$package_name" >&2
    exit 1
  fi

  output_path="$output_dir/$(basename "$kernel_path")"
  install -m 0644 "$kernel_path" "$output_path"

  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$output_path" | awk '{print $1}' > "$output_path.sha256"
  fi

  printf 'prepared %s\n' "$output_path"
  if [[ -f "$output_path.sha256" ]]; then
    printf 'sha256 %s\n' "$(cat "$output_path.sha256")"
  fi
)