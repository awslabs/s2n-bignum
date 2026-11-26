#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Share a project's HOL imports between proofs: compile them once as
# sessions declared in a manifest, then run each proof under its session.
. "$(dirname "$0")/../lib.sh"

step "theories.json declares /arithmetic and its child /arithmetic/parity."
cat theories.json

step "Compile the sessions and the proofs. Both proofs share both imports."
python3 build.py "$HOLD"
plan=$(cat modules/plan.json); echo "$plan"
expect '"session": "/arithmetic/parity"' "$plan"
expect '"parent": "/arithmetic/parity"' "$plan"

step "Build the sessions in the daemon in plan order: fork, then load."
hol-d start
python3 - modules/plan.json >sessions.txt <<'PY'
import json, sys
for layer in json.load(open(sys.argv[1]))["layers"]:
    print(layer["parent"], layer["session"], layer["plugin"])
PY
while read -r parent session plugin; do
    hol-d fork "$parent" "${session##*/}"
    hol-d load --public "$session" "modules/$plugin"
done <sessions.txt

step "Run each proof under the parent the plan names for it."
out=$(hol-d run /arithmetic/parity modules/even.cmxs; hol-d run /arithmetic/parity modules/odd.cmxs)
echo "$out"
expect "|- EVEN (twice 2)" "$out"
expect "|- ~ODD (twice 3)" "$out"
