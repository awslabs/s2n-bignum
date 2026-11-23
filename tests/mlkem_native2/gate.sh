#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# The test gate for a library providing the ML-KEM API: differential
# tests against the reference (test_api, several shards in parallel), the
# KAT hashes, the ACVP and Wycheproof vectors, memcheck (exact-size heap
# buffers), the constant-time check under memcheck, the ABI check and the
# same calls with BTI enforced (on x86_64, the check that every global
# function starts with endbr64 instead).
#
# usage: gate.sh NAME LIBRARY...
#   NAME     results go to WORK/build/NAME
#   LIBRARY  object files or archives providing the mlkem{512,768,1024}_*
#            API; they are linked with the reference library
# environment (and see env.sh):
#   ITER     test_api iterations per shard and level (default 2000)
#   SHARDS   number of test_api shards, with seeds 1..SHARDS (default 8)
#   CTLIBS   the libraries for the constant-time check, if they differ
#            (e.g. a build with declassification hooks); "none" skips it
#   NOX18    if set, x18 changes are warnings in the ABI check
#   NOBTI    if set, skip the BTI check (for libraries built without BTI
#            landing pads, such as compiled C without -mbranch-protection),
#            or on x86_64 the endbr64 check
set -u
. "$(dirname "$0")/env.sh"
NAME=$1; shift
B=$WORK/build/$NAME
REF=$WORK/ref/out/libref.a
REFBTI=$WORK/ref/out_bti/libref.a
LIBS=$(for f in "$@"; do readlink -f "$f"; done)
CT=${CTLIBS:-$LIBS}
ITER=${ITER:-2000}; SHARDS=${SHARDS:-8}
rm -rf "$B"; mkdir -p "$B"
CCF="$CC -O2 -Wall -Wextra"
st=0

$CCF -o $B/test_api $T/test_api.c $LIBS $REF || exit 1
$CCF -o $B/kat $T/kat.c $LIBS $REF || exit 1
$CCF -o $B/test_abi $T/test_abi.c $ABI_STUB $LIBS $REF || exit 1
if [ "$CT" != none ]; then
  $CCF -o $B/test_ct $T/test_ct.c $CT || exit 1
fi
if [ -z "${NOBTI:-}" ] && [ $ARCH = aarch64 ]; then
  $CCF $BTI_FLAGS -o $B/test_api_bti $T/test_api.c $LIBS $REFBTI \
    2> $B/bti_link.log || exit 1
  $CCF $BTI_FLAGS -o $B/test_abi_bti $T/test_abi.c $T/abi_stub.S $LIBS \
    $REFBTI 2>> $B/bti_link.log || exit 1
fi

echo "gate $NAME:"
for s in $(seq 1 $SHARDS); do
  $B/test_api $ITER $s > $B/test_api_$s.log 2>&1 &
done
wait
r=0
for s in $(seq 1 $SHARDS); do
  tail -1 $B/test_api_$s.log | grep -q '^OK' || r=1
done
result "test_api ($SHARDS x $ITER iterations per level)" $r
$T/kat.sh $B/kat > $B/kat.log 2>&1; result "KAT" $?
$T/vectors.sh $NAME $LIBS $REF > $B/vectors.log 2>&1
result "ACVP and Wycheproof" $?
if [ -n "$VALGRIND" ]; then
  TEST_API_HEAP=1 $VALGRIND -q --error-exitcode=1 $B/test_api 20 99 \
    > $B/memcheck.log 2>&1
  result "memcheck (test_api, heap buffers)" $?
  if [ "$CT" != none ]; then
    $VALGRIND -q --error-exitcode=1 $B/test_ct 3 > $B/ct.log 2>&1
    result "constant time (memcheck)" $?
  fi
else
  result "memcheck and constant time (no VALGRIND)" skip
fi
$B/test_abi ${NOX18:+-x18} > $B/abi.log 2>&1; result "ABI" $?
if [ -z "${NOBTI:-}" ] && [ $ARCH = aarch64 ]; then
  r=0
  $B/test_api_bti 50 7 > $B/test_api_bti.log 2>&1 || r=1
  $B/test_abi_bti ${NOX18:+-x18} > $B/abi_bti.log 2>&1 || r=1
  result "BTI enforced (calls through pointers and blr)" $r
elif [ -z "${NOBTI:-}" ]; then
  $T/check_endbr.sh $LIBS > $B/endbr.log 2>&1
  result "endbr64 at every global function" $?
fi
grep -h "matrix polynomials" $B/test_api_[0-9]*.log | \
  awk '{n[$1]+=$4; t[$1]+=$6} END {for (l in n) print "  " l, n[l], "of", \
  t[l], "matrix polynomials needed a 4th block"}' | sort
[ $st = 0 ] && echo "gate $NAME: OK" || echo "gate $NAME: FAIL (logs in $B)"
exit $st
