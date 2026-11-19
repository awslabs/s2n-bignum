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
# Compile $1.ml to $1.cmx with the bytecode build of the native-code
# compiler, as tools/build-proof.sh does. Its stack is OCAMLRUNPARAM's l,
# not the system stack, which a CI runner can limit to 8 MiB, so the large
# quotations of the models compile under any system stack limit. A
# 16M-word minor heap shortens compilation; the code is unchanged. The
# proof executables need no more than an 8 MiB system stack: every suite
# passes under that hard limit.
compile() {
  OCAMLRUNPARAM=l=2000000000,s=16M ocamlopt.byte \
    -pp "camlp5r pa_lexer.cmo pa_extend.cmo q_MLast.cmo -I \"$hol_dir\" pa_j.cmo" \
    -I "$hol_dir" -I "$build_dir" -I +unix -g -c hol_lib.cmxa \
    "$1.ml" -o "$1.cmx" -w -a
}
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
    ocaml "$hol_dir/inline_load.ml" "$repo_dir/arm/proofs/base.ml" "$base.ml"
  logged "$build_dir/arm-base-build.log" compile "$base"
  printf '%s\n' "arm-base: compiled $base.cmx"
  exit 0
fi
linked=()
if [[ "$arch" == arm-* && -f "$base.cmx" ]]; then
  logged "$build_dir/$arch-inline.log" \
    ocaml -I "$hol_dir" "$script_dir/scripts/inline-proof.ml" \
    "$repo_dir/arm/proofs/base.ml" "$script_dir/proofs/$arch.ml" \
    "$build_dir/$arch-inlined.ml"
  linked=("$base.cmx")
else
  logged "$build_dir/$arch-inline.log" \
    ocaml "$hol_dir/inline_load.ml" "$script_dir/proofs/$arch.ml" \
    "$build_dir/$arch-inlined.ml"
fi
logged "$build_dir/$arch-build.log" compile "$build_dir/$arch-inlined"
logged -a "$build_dir/$arch-build.log" \
  ocamlfind ocamlopt -g -package zarith,unix -linkpkg -I "$hol_dir" \
  hol_lib.cmxa "${linked[@]}" "$build_dir/$arch-inlined.cmx" \
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
