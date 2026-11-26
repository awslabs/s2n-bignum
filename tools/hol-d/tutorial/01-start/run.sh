#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Start a daemon, look at its tree and stop it.
. "$(dirname "$0")/../lib.sh"

step "Start the daemon. It prints 'Starting server ...' and then OK."
hol-d start

step "A second start finds the running daemon."
out=$(hol-d start 2>&1)
expect "Server already running" "$out"

step "The tree holds only the frozen root /."
out=$(hol-d tree)
echo "$out"
expect "/ " "$out"
expect "frozen" "$out"

step "Stop the daemon. Afterwards tree reports that none is running."
hol-d stop
if out=$(hol-d tree 2>&1); then exit 1; fi
expect "no daemon" "$out"
