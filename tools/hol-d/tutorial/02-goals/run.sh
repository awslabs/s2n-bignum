#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Fork a session, set a goal at its prompt, and try two tactics from that
# same goal in two forked children.
. "$(dirname "$0")/../lib.sh"
hol-d start

step "Fork /work from the root and define a constant at its prompt."
hol-d fork / work
out=$(printf '%s\n' 'let twice = new_definition `twice (n:num) = n + n`;;' |
      hol-d repl /work)
expect "|- forall n. twice n = n + n" "$out"

step "Set a goal. The prompt prints the goal stack."
out=$(printf '%s\n' 'g `!n. twice n = 2 * n`;;' | hol-d repl /work)
expect "twice n = 2 * n" "$out"

step "Fork twice from the open goal. The first fork freezes /work."
hol-d fork /work rewrite
hol-d fork /work arith

step "Each child finishes the proof its own way."
out=$(printf '%s\n' 'e (REWRITE_TAC[twice; MULT_2]);;' 'top_thm();;' |
      hol-d repl /work/rewrite)
expect "|- forall n. twice n = 2 * n" "$out"
out=$(printf '%s\n' 'e (REWRITE_TAC[twice] THEN ARITH_TAC);;' 'top_thm();;' |
      hol-d repl /work/arith)
expect "|- forall n. twice n = 2 * n" "$out"

step "A frozen node refuses a prompt; fork a child to continue from it."
if out=$(hol-d repl /work </dev/null 2>&1); then exit 1; fi
expect "/work is frozen; fork a child to work in" "$out"

step "Piped input reports failed phrases with a failure status."
if out=$(printf '%s\n' 'this_is_unbound;;' | hol-d repl /work/arith 2>&1); then exit 1; fi
expect "Unbound value this_is_unbound" "$out"

step "The tree shows the frozen parent and its two children."
out=$(hol-d tree | awk '{print $1, $3}'); echo "$out"
expect "/work frozen" "$out"
expect "/work/arith idle" "$out"

step "kill --tree removes /work and both children."
hol-d kill --tree /work
out=$(hol-d tree)
if grep -q /work <<<"$out"; then exit 1; fi
