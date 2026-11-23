#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Build the reference: mlkem-native's portable C (no native backends),
# all three parameter sets, with the namespace prefix "ref" (ref512_dec,
# ref_poly_compress_d10, ref_shake256, ...) so that it links beside the
# library under test, into WORK/ref/out/libref.a, and on AArch64 the same
# with BTI landing pads (for the tests with BTI enforced) in
# WORK/ref/out_bti.
#
# usage: ref.sh
set -e
. "$(dirname "$0")/env.sh"
SRCS=$(cd "$MLKEM_NATIVE/mlkem" && find src -name '*.c' | sort)
VARIANTS=out; [ $ARCH = aarch64 ] && VARIANTS="out out_bti"
for v in $VARIANTS; do
  OUT=$WORK/ref/$v
  EXTRA=; [ $v = out_bti ] && EXTRA=$CF_CFLAGS
  rm -rf "$OUT"; mkdir -p "$OUT"
  for L in 512 768 1024; do
    if [ $L = 512 ]; then ML=MLK_CONFIG_MULTILEVEL_WITH_SHARED
    else ML=MLK_CONFIG_MULTILEVEL_NO_SHARED; fi
    for s in $SRCS; do
      o=$OUT/obj$L/${s%.c}.o; mkdir -p "$(dirname "$o")"
      $CC -O2 -std=c99 -Wall -Wextra -Werror -DMLK_CONFIG_MULTILEVEL_BUILD \
        -D$ML -DMLK_CONFIG_PARAMETER_SET=$L \
        -DMLK_CONFIG_NAMESPACE_PREFIX=ref $EXTRA \
        -I "$MLKEM_NATIVE/mlkem" -c "$MLKEM_NATIVE/mlkem/$s" -o "$o" &
    done
    wait
  done
  ar rcs "$OUT/libref.a" $(find "$OUT" -name '*.o' | sort)
  echo "$OUT/libref.a: $(find "$OUT" -name '*.o' | wc -l) objects," \
    "$(nm "$OUT/libref.a" | grep -c ' T ') global functions"
done
