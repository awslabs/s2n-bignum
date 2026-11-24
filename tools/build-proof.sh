#!/bin/bash
repo_root=$(cd "$(dirname "$0")/.." && pwd)

# Both the standalone executable and the forked proof plugin finish here.
# Its "Running time:" line is parsed by tools/proof_batch/runner.py (TIMING),
# tools/proof_timing/collect.py (TIMING) and tools/collect-times.sh.
proof_footer() {
  local arch=$1 source=$2 specs spec
  echo 'Hol_lib.check_axioms ();;'
  specs=$(cd "$repo_root" && ./tools/collect-specs.sh "$arch" "$source") || return 1
  for spec in $specs; do
    echo "Printf.printf \"val ${spec} : thm = %s\n\" (string_of_thm ${spec});;"
  done
  echo "let s2n_bignum_build_proof_end_time = Unix.gettimeofday();;"
  echo 'Printf.printf "Running time: %f sec, Start unixtime: %f, End unixtime: %f\n" (s2n_bignum_build_proof_end_time -. s2n_bignum_build_proof_start_time) s2n_bignum_build_proof_start_time s2n_bignum_build_proof_end_time;;'
}

if [ "$#" -eq 3 ] && [ "$1" = "--footer" ]; then
  proof_footer "$2" "$3"
  exit $?
fi

if [ "$#" -ne 3 ]; then
  echo "../tools/build-proof.sh <.ml file path> <hol.sh> <output .native path>"
  echo "This script builds HOL Light proof using OCaml native compiler and puts the "
  echo "output binary at <output .native path>."
  echo ""
  echo "tools/build-proof.sh --footer <arch> <.ml file path>"
  echo "This prints the OCaml footer (axiom check, theorem printout, timing record)"
  echo "that ends every proof build. tools/proof_batch uses it for proof plugins."
  exit 1
fi

# Return the exit code if any statement fails
set -e

s2n_bignum_arch=$(basename "$(pwd)")

cd ..

ml_path_noarch=$1
ml_path=${s2n_bignum_arch}/${ml_path_noarch}
hol_sh_cmd=$2
output_path=${s2n_bignum_arch}/$3

export HOLLIGHT_DIR="$(dirname "$hol_sh_cmd")"
if [ ! -f "${HOLLIGHT_DIR}/hol_lib.cmxa" ]; then
  echo "hol_lib.cmxa does not exist in HOLLIGHT_DIR('${HOLLIGHT_DIR}')."
  echo "Did you compile HOL Light with HOLLIGHT_USE_MODULE set to 1?"
  exit 1
fi


scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
template_ml="$scratch/template.ml"
echo "Generating a template .ml that loads the file...: ${template_ml}"

{
  echo 'let s2n_bignum_build_proof_start_time = Unix.gettimeofday();;'
  echo "loadt \"${ml_path}\";;"
  proof_footer "$s2n_bignum_arch" "$ml_path_noarch"
} > "$template_ml"


if [ -d "${HOLLIGHT_DIR}/_opam" ]; then
  # To use inline_load.ml ... If OCaml version is too old, otherwise, a few String functions fail.
  eval "$(opam env --switch "${HOLLIGHT_DIR}/" --set-switch)"
fi

inlined_prefix="$scratch/proof"
inlined_ml="${inlined_prefix}.ml"
inlined_cmx="${inlined_prefix}.cmx"
ocaml "${HOLLIGHT_DIR}/inline_load.ml" "$template_ml" "$inlined_ml"

# Give a large stack size.
OCAMLRUNPARAM=l=2000000000 \
ocamlopt.byte -pp "$("$hol_sh_cmd" -pp)" -I "${HOLLIGHT_DIR}" -I +unix -c \
    hol_lib.cmxa "$inlined_ml" -o "$inlined_cmx" -w -a
ocamlfind ocamlopt -package zarith,unix -linkpkg hol_lib.cmxa \
    -I "${HOLLIGHT_DIR}" "$inlined_cmx" \
    -o "${output_path}"
