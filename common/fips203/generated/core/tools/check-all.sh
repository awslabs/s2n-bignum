#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#
# Check the whole equivalence development in a fresh HOL Light: load all.ml
# (which never loads stubs.ml), then check.ml verifies that each interface
# lemma is a theorem without hypotheses whose conclusion is its statement,
# and that HOL Light has only its three standard axioms. all.ml also loads the
# properties of the handwritten model (common/fips20[23]/properties/).
#
# Usage: tools/check-all.sh [logfile]
#   HOL_SH     path of HOL Light's hol.sh (default: taken from the nix
#              `hol_light` shell of the mlkem-native checkout $MLKEM_NATIVE,
#              default ~/repos/mlkem-native)
# Writes logfile (default /tmp/fips203-equiv/check-all.log) and
# logfile.manifest (what was checked: file hashes, date, HOL Light path).
# Takes about 9 minutes. Exit status 0 iff the check passed.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
equiv="$here/.."
repo=$(git -C "$here" rev-parse --show-toplevel)
log=${1:-/tmp/fips203-equiv/check-all.log}
mkdir -p "$(dirname "$log")"

if [ -z "${HOL_SH:-}" ]; then
  command -v nix >/dev/null || . /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh
  HOL_SH=$(cd "${MLKEM_NATIVE:-$HOME/repos/mlkem-native}" &&
           nix develop .#hol_light --command bash -c 'command -v hol.sh')
fi

# The files that all.ml loads, in order (stubs.ml must not be among them).
files=$(sed -n 's|^loadt "common/fips203/generated/core/\([^"]*\.ml\)";;|\1|p' "$equiv/all.ml")
if echo "$files" | grep -qx 'stubs.ml'; then
  echo "FAIL: all.ml loads stubs.ml"; exit 1
fi

# Text-level guard (the kernel-level guard is the axioms() check in check.ml).
proofs=$(echo "$files" | grep -vxE 'base.ml|interface.ml|check.ml')
if (cd "$equiv" && grep -nwE 'mk_thm|CHEAT_TAC|new_axiom|new_constant|new_specification|Obj\.magic' $proofs ../fips203_equivalence.ml \
      "$repo"/common/fips202/properties/*.ml "$repo"/common/fips203/properties/*.ml); then
  echo "FAIL: a proof file uses mk_thm, CHEAT_TAC, new_axiom, new_constant, new_specification or Obj.magic"
  exit 1
fi

manifest="$log.manifest"
{
  echo "date: $(date -u +%FT%TZ)"
  echo "hol.sh: $HOL_SH"
  echo "git HEAD: $(git -C "$repo" rev-parse HEAD)"
  echo "sha256 of every loaded file and of the models:"
  (cd "$repo" && sha256sum common/fips202/fips202.ml common/fips202/properties/*.ml \
      common/fips203/fips203.ml common/fips203/properties/*.ml \
      common/fips203/generated/*.ml common/fips203/generated/core/compiler/*.ml \
      $(echo "$files" | sed 's|^|common/fips203/generated/core/|') \
      common/fips203/generated/core/all.ml)
} > "$manifest"

start=$(date +%s)
(cd "$repo" && echo 'loadt "common/fips203/generated/core/all.ml";;' | "$HOL_SH") > "$log" 2>&1 || true
echo "elapsed $(( $(date +%s) - start )) s, log $log, manifest $manifest"

grep -naE 'Exception:|^Error|Failure "' "$log" | head -20 || true
grep -a 'FIPS203-EQUIV-AXIOMS' -A3 "$log" | head -5 || true
if grep -qE '^FIPS203-EQUIV-CHECK-PASSED [0-9]+ lemmas$' "$log"; then
  grep -aE '^FIPS203-EQUIV-(RESULTS|CHECK-PASSED)' "$log"
else
  echo "FAIL: check did not pass"
  exit 1
fi
