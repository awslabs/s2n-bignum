#!/usr/bin/env bash
# Install a checksum-pinned official solver archive, not the system package.
set -euo pipefail
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
source "$script_dir/versions.env"
if (( $# != 1 )); then
  printf 'Usage: bash %s NEW_INSTALL_DIRECTORY\n' "$0" >&2
  exit 2
fi
case "$(uname -s)/$(uname -m)" in
  Linux/aarch64|Linux/arm64)
    platform=arm64-glibc-2.38; checksum="$Z3_ARM64_SHA256";;
  Linux/x86_64)
    platform=x64-glibc-2.39; checksum="$Z3_X64_SHA256";;
  *)
    printf '%s\n' 'CI solver setup supports Linux arm64/x64; install the pinned version manually elsewhere' >&2
    exit 1;;
esac
mkdir -- "$1"
directory="$(cd -- "$1" && pwd -P)"
archive="z3-$Z3_VERSION-$platform"
curl --fail --location --retry 3 \
  "https://github.com/Z3Prover/z3/releases/download/z3-$Z3_VERSION/$archive.zip" \
  --output "$directory/release.zip"
printf '%s  %s\n' "$checksum" "$directory/release.zip" | sha256sum --check -
unzip -q "$directory/release.zip" -d "$directory"
solver="$directory/$archive/bin/z3"
test -x "$solver"
# check.py validates the running version before generation. The archive
# checksum is checked here, including on a host needing another loader.
printf 'Pinned solver installed: %s\n' "$solver"
