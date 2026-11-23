#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Compare the SHA-256 of the KAT output of a kat binary (built from kat.c
# against a library under test) with the kat-sha256 values of
# mlkem-native's META.yml.
#
# usage: kat.sh KAT_BINARY
. "$(dirname "$0")/env.sh"
META=$MLKEM_NATIVE/META.yml
st=0
for L in 512 768 1024; do
  want=$(grep -A8 "name: ML-KEM-$L\$" $META | grep -m1 kat-sha256 |
         awk '{print $2}')
  got=$($1 $L | sha256sum | awk '{print $1}')
  if [ -n "$want" ] && [ "$got" = "$want" ]; then echo "KAT ML-KEM-$L: OK"
  else echo "KAT ML-KEM-$L: FAIL (got $got, want $want)"; st=1; fi
done
exit $st
