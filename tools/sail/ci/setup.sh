#!/usr/bin/env bash
# Provision one independent CI toolchain in a fresh prefix. Ubuntu packages:
# generation: build-essential git opam m4 pkg-config libgmp-dev z3
# proofs:     build-essential git opam m4 pkg-config libgmp-dev libpcre2-dev xdot
#             (xdot: opam's system dependency of not-ocamlfind, which camlp5
#             needs; opam install --yes does not install it)
#
# Run "bash setup.sh generation" or "bash setup.sh proofs". For local use,
# source the printed environment.sh afterwards. GITHUB_ENV is optional;
# when present it receives the same environment for following workflow steps.
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
# shellcheck source=versions.env
source "$script_dir/versions.env"

if (( $# != 1 )) || [[ "$1" != generation && "$1" != proofs ]]; then
  printf 'Usage: bash %s generation|proofs\n' "$0" >&2
  exit 2
fi
mode="$1"
jobs="${SAIL_HOL_CI_BUILD_JOBS:-2}"
if [[ ! "$jobs" =~ ^[1-9][0-9]*$ ]] || (( ${#jobs} > 2 || jobs > 32 )); then
  printf '%s\n' 'SAIL_HOL_CI_BUILD_JOBS must be an integer in 1..32' >&2
  exit 2
fi
for command in git opam make gcc; do
  if ! command -v "$command" >/dev/null; then
    printf 'Missing provisioning tool: %s\n' "$command" >&2
    exit 1
  fi
done
if [[ "$mode" == generation ]] && ! command -v z3 >/dev/null; then
  printf '%s\n' 'Generation requires z3 on PATH' >&2
  exit 1
fi

if [[ -n "${SAIL_HOL_CI_PREFIX:-}" ]]; then
  # mkdir is deliberately exclusive: do not adopt an old checkout or switch.
  mkdir -- "$SAIL_HOL_CI_PREFIX"
  prefix="$(cd -- "$SAIL_HOL_CI_PREFIX" && pwd -P)"
else
  prefix="$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/sail-hol-$mode.XXXXXX")"
fi
trap 'printf "Provisioning failed; partial prefix retained at %s\n" "$prefix" >&2' ERR

# Do not inherit an active user switch or a different compiler's libraries.
unset OPAMSWITCH OPAM_SWITCH_PREFIX OCAMLPATH CAML_LD_LIBRARY_PATH DUNE_BUILD_DIR
unset SAIL_DIR SAIL_EXE SAIL_BUILD_DIR SAIL_ARM_DIR SAIL_RISCV_DIR
unset SAIL_X86_DIR SAIL_X86_SHINA_DIR SAIL_X86_REMS_DIR
unset SAIL_HOL_PLUGIN SAIL_HOL_BUILD_DIR HOLDIR HOLLIGHT_DIR
export OPAMROOT="$prefix/opam-root"
opam init --bare --no-setup --disable-sandboxing --yes
switch="$prefix/toolchain"
if [[ "$mode" == generation ]]; then
  compiler="$SAIL_OCAML_VERSION"
  read -r -a packages <<< "$SAIL_OPAM_PACKAGES"
else
  compiler="$HOL_OCAML_VERSION"
  read -r -a packages <<< "$HOL_OPAM_PACKAGES"
fi
opam switch create "$switch" "ocaml-base-compiler.$compiler" --no-install --yes --jobs="$jobs"
opam install --switch="$switch" --yes --jobs="$jobs" "${packages[@]}"
eval "$(opam env --switch="$switch" --set-switch)"
if [[ "$(ocamlc -version)" != "$compiler" ]]; then
  printf 'Expected OCaml %s after provisioning\n' "$compiler" >&2
  exit 1
fi

checkout() {
  local url="$1" revision="$2" directory="$3"
  git init --quiet "$directory"
  git -C "$directory" remote add origin "$url"
  git -C "$directory" fetch --depth=1 origin "$revision"
  git -C "$directory" checkout --quiet --detach FETCH_HEAD
  if [[ "$(git -C "$directory" rev-parse HEAD)" != "$revision" ]]; then
    printf 'Unexpected revision in %s\n' "$directory" >&2
    return 1
  fi
}

# Publish an empty OCAMLPATH for proofs as well: sourcing this file locally
# must not retain a Sail library from a caller's different OCaml switch.
export OCAMLPATH=""
environment=(PATH OPAMROOT OPAMSWITCH OPAM_SWITCH_PREFIX CAML_LD_LIBRARY_PATH OCAMLPATH)
if [[ "$mode" == generation ]]; then
  export SAIL_DIR="$prefix/sail"
  export SAIL_ARM_DIR="$prefix/sail-arm"
  export SAIL_RISCV_DIR="$prefix/sail-riscv"
  export SAIL_X86_SHINA_DIR="$prefix/sail-x86"
  export SAIL_X86_REMS_DIR="$prefix/sail-x86-from-acl2"
  checkout https://github.com/rems-project/sail.git "$SAIL_COMMIT" "$SAIL_DIR"
  checkout https://github.com/rems-project/sail-arm.git "$SAIL_ARM_COMMIT" "$SAIL_ARM_DIR"
  checkout https://github.com/riscv/sail-riscv.git "$SAIL_RISCV_COMMIT" "$SAIL_RISCV_DIR"
  checkout https://github.com/shina-lab/sail-x86.git "$SAIL_X86_SHINA_COMMIT" "$SAIL_X86_SHINA_DIR"
  checkout https://github.com/rems-project/sail-x86-from-acl2.git \
    "$SAIL_X86_REMS_COMMIT" "$SAIL_X86_REMS_DIR"
  (
    cd "$SAIL_DIR"
    # Other Sail export targets are not needed. Building the native frontend
    # also supplies its Dune site-data object to the backend's native tests.
    dune build --release --only-packages=libsail,sail_maker,sail -j "$jobs" \
      src/bin/sail.exe libsail.install
    dune install --prefix="$prefix/sail-install" libsail
  )
  export SAIL_BUILD_DIR="$SAIL_DIR/_build/default"
  export SAIL_EXE="$SAIL_BUILD_DIR/src/bin/sail.exe"
  export OCAMLPATH="$prefix/sail-install/lib"
  test -x "$SAIL_EXE"
  test -f "$SAIL_BUILD_DIR/src/bin/.sail.eobjs/native/dune_site__Dune_site_data.cmx"
  ocamlfind query libsail
  "$SAIL_EXE" --version
  environment+=(SAIL_DIR SAIL_EXE SAIL_BUILD_DIR SAIL_ARM_DIR SAIL_RISCV_DIR
               SAIL_X86_SHINA_DIR SAIL_X86_REMS_DIR)
else
  export HOLDIR="$prefix/hol-light"
  checkout https://github.com/jrh13/hol-light.git "$HOL_LIGHT_COMMIT" "$HOLDIR"
  make -C "$HOLDIR" -j "$jobs" HOLLIGHT_USE_MODULE=1 hol.sh hol_lib.cmxa
  test -x "$HOLDIR/hol.sh"
  test -f "$HOLDIR/hol_lib.cmxa"
  environment+=(HOLDIR)
fi

export SAIL_HOL_CI_ENV="$prefix/environment.sh"
environment+=(SAIL_HOL_CI_ENV)
for name in "${environment[@]}"; do
  value="${!name:-}"
  if [[ "$value" == *$'\n'* || "$value" == *$'\r'* ]]; then
    printf 'Cannot publish a multiline environment value: %s\n' "$name" >&2
    exit 1
  fi
  printf 'export %s=%q\n' "$name" "$value" >> "$SAIL_HOL_CI_ENV"
  if [[ -n "${GITHUB_ENV:-}" ]]; then
    printf '%s=%s\n' "$name" "$value" >> "$GITHUB_ENV"
  fi
done
printf 'Source this environment for local checks: %s\n' "$SAIL_HOL_CI_ENV"
