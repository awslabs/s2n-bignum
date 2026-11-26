#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Load HOL source at the prompt instead of a compiled plugin, and see what
# carries over to forked children.
. "$(dirname "$0")/../lib.sh"
hol-d start
hol-d fork / src

step "loadt runs a source file through HOL's loader in the leaf."
out=$(printf '%s\n' 'loadt "base.ml";;' 'twice_two;;' | hol-d repl /src)
expect "|- twice 2 = 4" "$out"

step "A child inherits everything the file defined."
hol-d fork /src child
out=$(printf '%s\n' 'twice;;' | hol-d repl /src/child)
expect "|- forall n. twice n = n + n" "$out"

step "needs skips a file that is already loaded."
out=$(printf '%s\n' 'needs "base.ml";;' 'twice_two;;' | hol-d repl /src/child)
expect "|- twice 2 = 4" "$out"

step "A phrase can span several lines; it runs once it ends with ;;."
out=$(printf '%s\n' 'let three =' '  1 +' '  2;;' | hol-d repl /src/child)
expect "val three : int = 3" "$out"
