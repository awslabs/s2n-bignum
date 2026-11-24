#!/usr/bin/env bash
# Compile one proof suite's driver and run it in a fresh HOL Light process.
# The generated models must already be in _build/; ci/check.py proofs
# copies them there and audits the log. Sail is not run.
#
# "check-proof.sh arm-base" compiles arm/proofs/base.ml alone, as the
# module Arm_common_base in _build/. While that module is there, each Arm
# suite links it instead of compiling base.ml again. check.py proofs does
# this once per run, in its fresh snapshot. Elsewhere, delete
# _build/arm_common_base.* after changing a file that base.ml loads.
set -euo pipefail
script_dir="$(realpath -- "$(dirname -- "${BASH_SOURCE[0]}")")"
repo_dir="$(realpath -- "$script_dir/../..")"
build_dir="$script_dir/_build"
hol_dir="${HOLDIR:?set HOLDIR to a native-built HOL Light checkout}"
arch="${1:?pass a proof suite, such as rv32 or arm-carry, or arm-base}"
backtrace="${SAIL_HOL_PROOF_BACKTRACE:-1}"
if (( $# != 1 )) || [[ ! "$arch" =~ ^[a-z][a-z0-9-]*$ ]] ||
   [[ "$backtrace" != 0 && "$backtrace" != 1 ]]; then
  printf '%s\n' 'Usage: check-proof.sh SUITE|arm-base' >&2
  exit 2
fi
if [[ "$arch" != arm-base && ! -f "$script_dir/proofs/$arch.ml" ]]; then
  printf '%s\n' "Missing proof driver: proofs/$arch.ml" >&2
  exit 2
fi
export HOLLIGHT_DIR="$hol_dir"
if [[ -d "$hol_dir/_opam/bin" ]]; then
  export PATH="$hol_dir/_opam/bin:$PATH"
  export CAML_LD_LIBRARY_PATH="$hol_dir/_opam/lib/stublibs:$hol_dir/_opam/lib/ocaml/stublibs:$hol_dir/_opam/lib/ocaml${CAML_LD_LIBRARY_PATH:+:$CAML_LD_LIBRARY_PATH}"
fi
cd "$repo_dir"
# logged [-a] LOG COMMAND...: run COMMAND with its output in LOG, appended
# with -a. If it fails, print the end of LOG on stderr, so that the
# caller's log, such as check.py's <suite>-ci-run.log, shows the error.
logged() {
  local append=0
  if [[ "$1" == -a ]]; then append=1; shift; fi
  local log="$1"; shift
  local status=0
  if (( append )); then "$@" >> "$log" 2>&1 || status=$?
  else "$@" > "$log" 2>&1 || status=$?; fi
  if (( status != 0 )); then
    printf '%s exited %d; the end of %s:\n' "$1" "$status" "$log" >&2
    tail -n 40 -- "$log" >&2
    return "$status"
  fi
}
base="$build_dir/arm_common_base"
if [[ "$arch" == arm-base ]]; then
  logged "$build_dir/arm-base-inline.log" \
    bash "$hol_dir/hol.sh" inline-load "$repo_dir/arm/proofs/base.ml" "$base.ml"
  logged "$build_dir/arm-base-build.log" \
    bash "$hol_dir/hol.sh" compile "$base.ml" -o "$base.cmx" -g -w -a
  printf '%s\n' "arm-base: compiled $base.cmx"
  exit 0
fi
linked=()
input="$script_dir/proofs/$arch.ml"
inline_options=()
if [[ "$arch" == arm-* ]]; then
  input="$build_dir/$arch-native-input.ml"
  if [[ -f "$base.cmx" ]]; then
    # Stock inlining handles the body. The linked base initializes before
    # the driver, including its check_axioms call; no theorem heap is reused.
    printf 'open Hol_lib;;\nopen Hol_loader;;\nopen Arm_common_base;;\n' > "$input"
    linked=("$base.cmx")
    inline_options=(-omit-prelude)
  else
    # Standalone use also starts from the full base in a fresh process.
    printf 'loadt "arm/proofs/base.ml";;\n' > "$input"
  fi
  printf 'loadt "tools/sail/proofs/%s.ml";;\n' "$arch" >> "$input"
fi
logged "$build_dir/$arch-inline.log" \
  bash "$hol_dir/hol.sh" inline-load "$input" "$build_dir/$arch-inlined.ml" \
  "${inline_options[@]}"
logged "$build_dir/$arch-build.log" \
  bash "$hol_dir/hol.sh" compile "$build_dir/$arch-inlined.ml" \
  -I "$build_dir" -o "$build_dir/$arch-inlined.cmx" -g -w -a
logged -a "$build_dir/$arch-build.log" \
  bash "$hol_dir/hol.sh" link -g "${linked[@]}" "$build_dir/$arch-inlined.cmx" \
  -o "$build_dir/$arch.native"
# HOL raises Failure during ordinary proof search. With backtraces on,
# every raise walks the native stack, which costs about a tenth of
# claim time. SAIL_HOL_PROOF_BACKTRACE=0 omits them; the CI gate does
# so, and a failing mode can be rerun here to obtain the backtrace.
# A 16M-word minor heap promotes fewer short-lived terms. Neither
# setting changes which code runs or what it proves.
proof_runtime="s=16M"
if (( backtrace )); then
  proof_runtime="b,$proof_runtime"
fi
OCAMLRUNPARAM="$proof_runtime" logged "$build_dir/$arch-proof.log" \
  "$build_dir/$arch.native"
printf '%s\n' "$arch: proof driver finished; its log is $build_dir/$arch-proof.log"
