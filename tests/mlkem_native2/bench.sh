#!/bin/bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Cycles per call of the API functions of a library (bench_api.c, with
# the virtual counter and a measured clock), into WORK/bench/NAME.txt,
# and the comparison with the baseline (WORK/bench/baseline.txt, made by
# baseline.sh) if there is one.
#
# usage: bench.sh NAME LIBRARY...
# environment: CORE, a core to pin the run to with taskset (default none)
set -e
. "$(dirname "$0")/env.sh"
NAME=$1; shift
D=$WORK/bench; mkdir -p "$D"
$CC -O2 -o "$D/bench_$NAME" "$T/bench_api.c" "$@"
${CORE:+taskset -c $CORE} "$D/bench_$NAME" "$NAME" > "$D/$NAME.txt"
if [ -f "$D/baseline.txt" ] && [ "$NAME" != baseline ]; then
  python3 - "$D/baseline.txt" "$D/$NAME.txt" <<'PY'
import sys
def load(f):
    return {l.split()[0]: float(l.split()[1]) for l in open(f)
            if not l.startswith('#')}
b, c = load(sys.argv[1]), load(sys.argv[2])
print('%-26s %9s %9s %7s' % ('function', 'baseline', 'this', 'change'))
for k in c:
    if k in b:
        print('%-26s %9.0f %9.0f %+6.1f%%' % (k, b[k], c[k],
                                              100 * (c[k] - b[k]) / b[k]))
PY
else
  cat "$D/$NAME.txt"
fi
