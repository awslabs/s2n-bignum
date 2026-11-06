#!/usr/bin/env bash
# Compile the OCaml backend modules into a plugin loaded by Sail.
# Use the OCaml compiler and libsail library matching the Sail executable.
set -euo pipefail

script_dir="$(realpath -- "$(dirname -- "${BASH_SOURCE[0]}")")"
build_dir="$script_dir/_build"
mkdir -p "$build_dir"
# Run this script inside the OCaml switch providing the matching libsail.
# When Sail was built separately, pass that Dune build directory to match
# its native implementation checksums as well as its module interfaces.
includes=(-I "$build_dir")
if [[ -n "${SAIL_BUILD_DIR:-}" ]]; then
  includes+=(-I "$SAIL_BUILD_DIR/src/lib/.libsail.objs/byte"
            -I "$SAIL_BUILD_DIR/src/lib/.libsail.objs/native")
fi
backend_sources=("$script_dir/build.sh")
for module in entry arm rv32 x86 x86_shina x86_rems sail_plugin_hol_light; do
  backend_sources+=("$script_dir/backend/$module.ml")
done
source_hashes="$(sha256sum "${backend_sources[@]}")"
{
  for module in entry arm rv32 x86 x86_shina x86_rems sail_plugin_hol_light; do
    ocamlfind ocamlopt -g "${includes[@]}" -package libsail \
      -c "$script_dir/backend/$module.ml" -o "$build_dir/$module.cmx"
  done
} > "$build_dir/plugin-build.log" 2>&1
ocamlopt -shared -linkall \
  "$build_dir/entry.cmx" "$build_dir/arm.cmx" "$build_dir/rv32.cmx" \
  "$build_dir/x86.cmx" "$build_dir/x86_shina.cmx" "$build_dir/x86_rems.cmx" \
  "$build_dir/sail_plugin_hol_light.cmx" \
  -o "$build_dir/sail_plugin_hol_light.cmxs" \
  >> "$build_dir/plugin-build.log" 2>&1
if [[ "$(sha256sum "${backend_sources[@]}")" != "$source_hashes" ]]; then
  printf '%s\n' 'Backend sources changed during the plugin build' >&2
  exit 1
fi
printf '%s\n' "$build_dir/sail_plugin_hol_light.cmxs"
