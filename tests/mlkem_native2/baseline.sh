#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Build mlkem-native's multilevel library with its native backends, as
# its examples/multilevel_build_native does, with the given compiler and
# extra flags (the example already has -O3), into
# WORK/baseline/libmlkem.a, and benchmark it as the baseline for
# bench.sh (WORK/bench/baseline.txt). The numbers in README.md are for
# clang 18 ("baseline.sh clang-18").
#
# usage: baseline.sh [CC [EXTRA_CFLAGS]]   (default clang)
# environment: CORE, as for bench.sh
set -e
. "$(dirname "$0")/env.sh"
BCC=${1:-clang}; EXTRA=${2:-}
OUT=$WORK/baseline
rm -rf "$OUT"; mkdir -p "$OUT/objs"
EX=$MLKEM_NATIVE/examples/multilevel_build_native
CC="$BCC" CFLAGS="$EXTRA" make -s -C "$EX" BUILD_DIR="$OUT/objs" \
  mlkem_objs -j16 > "$OUT/build.log" 2>&1
ar rcs "$OUT/libmlkem.a" $(find "$OUT/objs" -name '*.o' | sort)
echo "baseline: $BCC $EXTRA, $(find "$OUT/objs" -name '*.o' | wc -l) objects"
"$T/bench.sh" baseline "$OUT/libmlkem.a"
