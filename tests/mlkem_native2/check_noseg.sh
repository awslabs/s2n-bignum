#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# x86_64: check that no instruction of the given objects uses the segment
# register fs or gs (the only ones with a base in 64-bit mode), as the
# stack-protector code that compilers add does: the x86 model of the
# proofs has no segmentation.
#
# usage: check_noseg.sh OBJECT...
st=0; n=0
for o in "$@"; do
  objdump -d -M intel --no-show-raw-insn "$o" > /tmp/noseg.$$ || st=1
  n=$((n + $(grep -c -E '^ +[0-9a-f]+:' /tmp/noseg.$$)))
  if sed -e 's/<[^>]*>//g' /tmp/noseg.$$ | grep -E '^ +[0-9a-f]+:' |
     grep -E '(^|[^a-z0-9_])(fs|gs)([^a-z0-9_]|$)'; then
    echo "$o: uses fs or gs"; st=1
  fi
done
rm -f /tmp/noseg.$$
echo "$n instructions checked"
exit $st
