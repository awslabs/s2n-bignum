#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Build the objects under test with the rules of arm/Makefile (which
# preprocess from stdin, check for x18 and assemble for the SHA3
# extension), or of x86/Makefile on x86_64, and collect them in WORK/obj,
# together with the randomized API in C (randomized.c). With CTFLAGS
# set, e.g. CTFLAGS=-DMLKEM_CT_TESTING, the per-level files are
# preprocessed with those flags too, the same way, and the objects go to
# WORK/obj_ct instead.
#
# On x86_64, with VARIANT=avx512, the objects are those of the AVX-512
# version instead, in WORK/obj_avx512: its API and middle layer with the
# suffix _avx512 removed from their symbols (so that the tests and the
# benchmarks use them as they are), its Keccak-f1600 permutations, and the
# leaves and the constants block of the AVX2 version.
#
# usage: build.sh
set -e
. "$(dirname "$0")/env.sh"
O=$WORK/obj${VARIANT:+_$VARIANT}${CTFLAGS:+_ct}
OBJS=""
if [ "${VARIANT:-}" = avx512 ]; then
  for n in $AVX512_N2_OBJS $AVX512_LEAF_OBJS; do
    OBJS="$OBJS mlkem_native/asm_avx512/$n.o"
  done
  OBJS="$OBJS mlkem_native/asm/mlkem_native2_constants.o"
else
  for n in $NATIVE2_OBJS; do OBJS="$OBJS mlkem_native/asm/$n.o"; done
  for n in $SHA3_OBJS; do OBJS="$OBJS sha3/$n.o"; done
fi
for n in $LEAF_OBJS; do OBJS="$OBJS mlkem/mlkem_$n.o"; done
make -s -C "$REPO/$ARCHDIR" $OBJS
rm -rf "$O"; mkdir -p "$O"
for o in $OBJS; do cp "$REPO/$ARCHDIR/$o" "$O/"; done
if [ "${VARIANT:-}" = avx512 ]; then
  N2=$(for n in $AVX512_N2_OBJS; do echo "$O/$n.o"; done)
  UNSUFFIX=$(nm -g --defined-only $N2 | awk '$3 ~ /_avx512$/ {
    printf " --redefine-sym %s=%s", $3, substr($3, 1, length($3) - 7)}')
  for o in $N2; do objcopy $UNSUFFIX "$o"; done
fi
if [ -n "${CTFLAGS:-}" ]; then
  for L in 512 768 1024; do
    if [ -f "$REPO/$ARCHDIR/mlkem_native/asm/mlkem$L.S" ]; then
      (cd "$REPO/$ARCHDIR" &&
       asm_with mlkem_native/asm/mlkem$L.S "$CTFLAGS" "$O/mlkem$L.o")
    fi
  done
fi
# On x86_64, also the API with the Microsoft x64 ABI (WINDOWS_ABI), its
# symbols renamed with the prefix ms_ so that it links beside the System V
# API (test_abi calls it through abi_call_ms): the code it calls is the
# same System V code
if [ $ARCH = x86_64 ]; then
  for L in 512 768 1024; do
    S=mlkem_native/asm/mlkem$L.S
    [ "${VARIANT:-}" = avx512 ] && S=mlkem_native/asm_avx512/mlkem${L}_avx512.S
    if [ -f "$REPO/x86/$S" ]; then
      (cd "$REPO/x86" && asm_with $S "${CTFLAGS:-}" "$O/win_mlkem$L.tmp" 1)
      args=$(nm -g --defined-only "$O/win_mlkem$L.tmp" |
             awk '{n = $3; if (n ~ /_avx512$/) n = substr(n, 1, length(n) - 7)
                   printf " --redefine-sym %s=ms_%s", $3, n}')
      args="$args $(nm -u "$O/win_mlkem$L.tmp" | awk '$2 ~ /_avx512$/ {
        printf " --redefine-sym %s=%s", $2, substr($2, 1, length($2) - 7)}')"
      objcopy $args "$O/win_mlkem$L.tmp" "$O/ms_mlkem$L.o"
      rm -f "$O/win_mlkem$L.tmp"
    fi
  done
fi
$CC -O2 -Wall -Wextra $CF_CFLAGS -c "$T/randomized.c" \
  -o "$O/mlkem_native2_randomized.o"
echo "built $(ls "$O" | wc -l) objects in $O"
