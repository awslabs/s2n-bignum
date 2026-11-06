#!/usr/bin/env bash
# Ask Sail to load and check the external model, then run our HOL exporter.
set -euo pipefail

script_dir="$(realpath -- "$(dirname -- "${BASH_SOURCE[0]}")")"
build_dir="$script_dir/_build"
if (( $# < 2 )); then
  printf 'Usage: %s arm|rv32|x86-rems|x86-shina FAMILY [SAIL-OPTION ...]\n' "$0" >&2
  exit 2
fi
architecture="$1"
family="$2"
shift 2
target_architecture="$architecture"
source_options=()
case "$architecture" in
  arm) target_architecture=aarch64 ;;
  rv32) ;;
  # Each x86 model is compiled separately through the same plugin.
  x86-rems|x86-shina)
    target_architecture=x86
    source_options=(--hol-light-x86-source "${architecture#x86-}")
    ;;
  *)
    printf 'Unknown architecture: %s (expected arm, rv32, x86-rems or x86-shina)\n' \
      "$architecture" >&2
    exit 2
    ;;
esac
selection=()
if [[ "$family" != all ]]; then
  selection=(--hol-light-family "$family")
fi
: "${SAIL_EXE:?set SAIL_EXE to the matching Sail compiler}"
: "${SAIL_DIR:?set SAIL_DIR to its upstream source/library checkout}"
SAIL_EXE="$(realpath -- "$SAIL_EXE")"
SAIL_DIR="$(realpath -- "$SAIL_DIR")"
export SAIL_DIR
plugin="$(realpath -- \
  "${SAIL_HOL_PLUGIN:-$build_dir/sail_plugin_hol_light.cmxs}")"
mkdir -p "$build_dir"
common=(--plugin "$plugin" --hol-light
        --hol-light-architecture "$target_architecture" "${source_options[@]}"
        "${selection[@]}"
        --no-warn --no-color
        -o "$build_dir/$architecture-$family")
# Keep z3 answers between local runs unless the caller chose a file.
memo_given=0
for option in "$@"; do
  [[ "$option" == --memo-z3-path || "$option" == --memo-z3-path=* ]] && memo_given=1
done
if (( ! memo_given )); then
  common+=(--memo-z3-path "$build_dir/$architecture-upstream-smt-cache")
fi

case "$architecture" in
  arm)
    : "${SAIL_ARM_DIR:?set SAIL_ARM_DIR to the upstream Arm model checkout}"
    upstream_dir="$(realpath -- "$SAIL_ARM_DIR/arm-v9.4-a")"
    # Ask upstream Make for its ordered list; do not maintain another list.
    input_text="$(make --no-print-directory -C "$upstream_dir" \
      --eval='hol-light-inputs: ; @printf "%s\n" $(SAIL_SRCS)' \
      hol-light-inputs "SAIL_DIR=$SAIL_DIR")"
    mapfile -t inputs <<< "$input_text"
    if (( ${#inputs[@]} == 0 )) || [[ -z "${inputs[0]}" ]]; then
      printf 'The upstream Arm Makefile returned no Sail inputs\n' >&2
      exit 1
    fi
    # SAIL_ARM_EXCLUDED_INPUTS optionally drops whole files from that list,
    # e.g. instruction files that no selected family depends on. Each must
    # be one of upstream's inputs; the caller checks what they define.
    if [[ -n "${SAIL_ARM_EXCLUDED_INPUTS:-}" ]]; then
      read -r -a excluded <<< "$SAIL_ARM_EXCLUDED_INPUTS"
      for input in "${excluded[@]}"; do
        if [[ " ${inputs[*]} " != *" $input "* ]]; then
          printf 'Excluded Arm input is not an upstream input: %s\n' "$input" >&2
          exit 1
        fi
      done
      kept=()
      for input in "${inputs[@]}"; do
        if [[ " ${excluded[*]} " != *" $input "* ]]; then
          kept+=("$input")
        fi
      done
      inputs=("${kept[@]}")
    fi
    for input in "${inputs[@]}"; do
      if [[ ! -f "$upstream_dir/$input" ]]; then
        printf 'Missing upstream Arm input: %s\n' "$input" >&2
        exit 1
      fi
    done
    cd "$upstream_dir"
    exec "$SAIL_EXE" "${common[@]}" "$@" "${inputs[@]}"
    ;;
  rv32)
    : "${SAIL_RISCV_DIR:?set SAIL_RISCV_DIR to the upstream RISC-V checkout}"
    upstream_dir="$(realpath -- "$SAIL_RISCV_DIR/model")"
    required_version="$(tr -d '[:space:]' < \
      "$SAIL_RISCV_DIR/cmake/sail_required_version.txt")"
    config_file="$(realpath -- \
      "${SAIL_RISCV_CONFIG:-$script_dir/backend/rv32.json}")"
    cd "$upstream_dir"
    exec "$SAIL_EXE" "${common[@]}" --require-version "$required_version" \
      --strict-var --strict-bitvector --strict-exponentials \
      --config "$config_file" "$@" riscv.sail_project I_insts M_insts Zihintpause
    ;;
  x86-shina)
    : "${SAIL_X86_SHINA_DIR:?set SAIL_X86_SHINA_DIR to the shina-lab/sail-x86 checkout}"
    upstream_dir="$(realpath -- "$SAIL_X86_SHINA_DIR/model")"
    if [[ ! -f "$upstream_dir/x86.sail_project" ]]; then
      printf 'Missing upstream x86 project: %s\n' "$upstream_dir" >&2
      exit 1
    fi
    cd "$upstream_dir"
    exec "$SAIL_EXE" "${common[@]}" --require-version 0.20 --all-modules \
      "$@" x86.sail_project
    ;;
  x86-rems)
    : "${SAIL_X86_REMS_DIR:?set SAIL_X86_REMS_DIR to the sail-x86-from-acl2 checkout}"
    upstream_dir="$(realpath -- "$SAIL_X86_REMS_DIR/model")"
    # Ask upstream Make for its ordered list; do not maintain another list.
    input_text="$(make --no-print-directory -C "$upstream_dir" \
      --eval='hol-light-inputs: ; @printf "%s\n" $(ALL_SAILS)' \
      hol-light-inputs "SAIL_DIR=$SAIL_DIR")"
    mapfile -t inputs <<< "$input_text"
    if (( ${#inputs[@]} == 0 )) || [[ -z "${inputs[0]}" ]]; then
      printf 'The upstream REMS x86 Makefile returned no Sail inputs\n' >&2
      exit 1
    fi
    for input in "${inputs[@]}"; do
      if [[ ! -f "$upstream_dir/$input" ]]; then
        printf 'Missing upstream REMS x86 input: %s\n' "$input" >&2
        exit 1
      fi
    done
    cd "$upstream_dir"
    exec "$SAIL_EXE" "${common[@]}" "$@" "${inputs[@]}"
    ;;
esac
