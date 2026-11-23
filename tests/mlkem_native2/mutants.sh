#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# A check of the tests themselves: mutants.c forwards the API to the
# reference with one deliberate fault selected by MUTANT, and each fault
# must be caught, by test_api or (for MUTANT 9, the coins left on the
# stack) by test_abi, while the faithful forwarder (MUTANT 0) and the
# harmless changes (4 and 5) must pass.
#
# usage: mutants.sh
set -u
. "$(dirname "$0")/env.sh"
B=$WORK/build/mutants; rm -rf "$B"; mkdir -p "$B"
REF=$WORK/ref/out/libref.a
CCF="$CC -O2 -Wall -Wextra"
st=0
for m in 0 1 2 3 4 5 6 7 8 9; do
  $CCF -DMUTANT=$m -o $B/test_api_$m $T/test_api.c $T/mutants.c $REF ||
    exit 1
  $CCF -DMUTANT=$m -o $B/test_abi_$m $T/test_abi.c $ABI_STUB \
    $T/mutants.c $REF || exit 1
  r=0
  $B/test_api_$m 1000 1 > $B/test_api_$m.log 2>&1 || r=1
  $B/test_abi_$m -x18 > $B/test_abi_$m.log 2>&1 || r=1
  case $m in 0|4|5) want=0;; *) want=1;; esac
  if [ $r = $want ]; then
    echo "  mutant $m: $([ $r = 1 ] && echo caught || echo passes), OK"
  else
    echo "  mutant $m: $([ $r = 1 ] && echo caught || echo passes), FAIL"
    st=1
  fi
done
[ $st = 0 ] && echo "mutants: OK" || echo "mutants: FAIL (logs in $B)"
exit $st
