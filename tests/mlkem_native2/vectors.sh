#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Run the ACVP (v1.1.0.43) and Wycheproof ML-KEM vectors, with
# mlkem-native's own clients and drivers, against a library that provides
# mlkem{512,768,1024}_{keypair_derand,enc_derand,dec,check_pk,check_sk}.
#
# usage: vectors.sh NAME LIBRARY...
#   NAME     the work directory WORK/build/NAME/vectors is (re)made
#   LIBRARY  object files or archives to link the drivers with
set -e
. "$(dirname "$0")/env.sh"
NAME=$1; shift
M=$MLKEM_NATIVE
W=$WORK/build/$NAME/vectors
LIBS=$(for f in "$@"; do readlink -f "$f"; done)
rm -rf "$W"; mkdir -p "$W/test/acvp" "$W/test/wycheproof"
ln -s "$VECTORS/test/acvp/.acvp-data" "$W/test/acvp/.acvp-data"
ln -s "$VECTORS/test/wycheproof/.wycheproof-data" \
  "$W/test/wycheproof/.wycheproof-data"
for L in 512 768 1024; do
  BIN=$W/test/build/mlkem$L/bin; mkdir -p "$BIN"
  for d in acvp wycheproof; do
    $CC -O2 -std=c99 -DMLK_CONFIG_PARAMETER_SET=$L \
      -DMLK_CONFIG_NAMESPACE_PREFIX=mlkem$L -I "$M/mlkem" \
      "$M/test/$d/${d}_mlkem.c" "$T/no_randombytes.c" $LIBS \
      -o "$BIN/${d}_mlkem$L"
  done
done
cd "$W"
st=0
python3 "$M/test/acvp/acvp_client.py" -j 16 > acvp.log 2>&1 || st=1
python3 "$M/test/wycheproof/wycheproof_client.py" > wycheproof.log 2>&1 ||
  st=1
tail -2 acvp.log; tail -2 wycheproof.log
[ $st = 0 ] && echo "vectors $NAME: OK" || echo "vectors $NAME: FAIL"
exit $st
