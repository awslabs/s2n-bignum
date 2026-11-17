#!/usr/bin/env bash
# Build the shared HOL Light revision using its own compiler/package setup.
# Requires initialized opam and HOL Light's platform build dependencies.
set -euo pipefail
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
source "$script_dir/hol-light-version.env"
if (( $# != 1 )); then
  printf 'Usage: bash %s NEW_CHECKOUT_DIRECTORY\n' "$0" >&2
  exit 2
fi
jobs="${HOLLIGHT_BUILD_JOBS:-2}"
if [[ ! "$jobs" =~ ^[1-9][0-9]*$ ]] || (( ${#jobs} > 2 || jobs > 32 )); then
  printf '%s\n' 'HOLLIGHT_BUILD_JOBS must be an integer in 1..32' >&2
  exit 2
fi
# Do not reuse a checkout or switch whose build provenance is unknown.
mkdir -- "$1"
checkout="$(cd -- "$1" && pwd -P)"
git -C "$checkout" init --quiet
git -C "$checkout" remote add origin https://github.com/jrh13/hol-light.git
git -C "$checkout" fetch --depth=1 origin "$HOLLIGHT_COMMIT"
git -C "$checkout" checkout --quiet --detach FETCH_HEAD
test "$(git -C "$checkout" rev-parse HEAD)" = "$HOLLIGHT_COMMIT"
(
  cd "$checkout"
  OPAMJOBS="$jobs" make switch-5
  eval "$(opam env --switch="$checkout" --set-switch)"
  ocamlc -version
  camlp5 -v
  HOLLIGHT_USE_MODULE=1 make -j "$jobs"
)
test -x "$checkout/hol.sh"
test -f "$checkout/hol_lib.cmxa"
