#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# x86_64: check that every global function of the given objects starts
# with endbr64, the landing pad that indirect branch tracking (IBT, part
# of CET) requires; this stands in for running with IBT enforced, which
# needs a CPU and kernel with CET.
#
# usage: check_endbr.sh OBJECT...
st=0; n=0
for o in "$@"; do
  for f in $(nm -g --defined-only "$o" | awk '$2 == "T" {print $3}'); do
    n=$((n + 1))
    first=$(objdump -d --no-show-raw-insn "$o" |
            awk -v f="<$f>:" '$2 == f {getline; print $2; exit}')
    if [ "$first" != endbr64 ]; then
      echo "$o: $f starts with ${first:-nothing}, not endbr64"; st=1
    fi
  done
done
echo "$n global functions checked"
exit $st
