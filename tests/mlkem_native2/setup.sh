#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# One-time setup (see README.md): fetch mlkem-native at the pinned commit
# and the ACVP and Wycheproof vectors that its clients use, and build the
# reference library. With VALGRIND_PATCH set to a patch for valgrind
# 3.28.0 that makes it run the SHA3 instructions BCAX, RAX1 and XAR
# (which it does not yet), also build that valgrind into WORK/valgrind.
#
# usage: setup.sh
set -e
. "$(dirname "$0")/env.sh"
mkdir -p "$WORK"
if [ ! -d "$MLKEM_NATIVE/.git" ]; then
  git clone -q https://github.com/pq-code-package/mlkem-native \
    "$MLKEM_NATIVE"
fi
git -C "$MLKEM_NATIVE" -c advice.detachedHead=false \
  checkout -q $MLKEM_NATIVE_COMMIT
mkdir -p "$VECTORS"
(cd "$VECTORS" && python3 "$T/fetch_vectors.py" "$MLKEM_NATIVE")
"$T/ref.sh"
if [ -n "${VALGRIND_PATCH:-}" ]; then
  P=$(readlink -f "$VALGRIND_PATCH")
  V=valgrind-3.28.0
  cd "$WORK"
  [ -f $V.tar.bz2 ] ||
    curl -sSfLO https://sourceware.org/pub/valgrind/$V.tar.bz2
  echo "9f7a18d128f05d3a80fea53e6953f34aad7200a425ceaee46099a8a798a7dd9c" \
    " $V.tar.bz2" | sha256sum -c --quiet -
  rm -rf $V; tar xjf $V.tar.bz2
  (cd $V && patch -s -p1 < "$P" &&
   ./configure -q --prefix="$WORK/valgrind" && make -s -j16 &&
   make -s install) > "$WORK/valgrind-build.log" 2>&1
  echo "valgrind: $WORK/valgrind/bin/valgrind"
fi
