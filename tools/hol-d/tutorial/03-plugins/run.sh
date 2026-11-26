#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Build native plugins, load a shared base once, and run proofs in
# parallel children of the session that holds it.
. "$(dirname "$0")/../lib.sh"

step "Compile base.ml first, so the proofs can read base.cmi."
plugin base zero one wrong

hol-d start
hol-d fork / arithmetic

step "A public load makes Base visible to children and to the prompt."
hol-d load --public /arithmetic base.cmxs

step "Run both proofs in parallel. Each runs in its own forked child."
hol-d run /arithmetic zero.cmxs >zero.out & zero=$!
hol-d run /arithmetic one.cmxs >one.out & one=$!
wait $zero && wait $one
out=$(cat zero.out one.out); echo "$out"
expect "|- twice 0 = 0" "$out"
expect "|- twice 1 = 2" "$out"

step "A failing proof makes run fail; /arithmetic is unaffected."
if out=$(hol-d run /arithmetic wrong.cmxs 2>&1); then exit 1; fi
expect "plugin failed" "$out"

step "At a prompt in a child, open Base to use its names directly."
hol-d fork /arithmetic scratch
out=$(printf '%s\n' 'open Base;;' 'twice;;' | hol-d repl /arithmetic/scratch)
expect "|- forall n. twice n = n + n" "$out"

step "A private load runs the initializer but keeps the module name hidden."
hol-d fork / private
hol-d load --private /private base.cmxs
if out=$(printf '%s\n' 'Base.twice;;' | hol-d repl /private 2>&1); then exit 1; fi
expect "Unbound module Base" "$out"

step "Loading the same module publicly twice discards the leaf."
hol-d fork /arithmetic again
if hol-d load --public /arithmetic/again base.cmxs >/dev/null 2>&1; then exit 1; fi
out=$(hol-d tree)
if grep -q /arithmetic/again <<<"$out"; then exit 1; fi
