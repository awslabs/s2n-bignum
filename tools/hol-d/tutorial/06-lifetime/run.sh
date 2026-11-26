#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Session lifetime: kill ends a node and the commands it started, and no
# process outlives the daemon, even when it is killed with SIGKILL.
. "$(dirname "$0")/../lib.sh"

# Running commands whose environment holds HOLD_TUTORIAL=$1. (An
# environment marker works with any /bin/sh; dash has no `exec -a`.)
helpers() {
    grep -lsx -z "HOLD_TUTORIAL=$1" /proc/[0-9]*/environ 2>/dev/null || true
}
started() { [ -n "$(helpers "$1")" ]; }
gone() { [ -z "$(helpers "$1")" ]; }

hol-d start
hol-d fork / a
hol-d fork /a b

step "A phrase starts a background command; the prompt returns at once."
printf '%s\n' 'ignore (Sys.command "HOLD_TUTORIAL=b sleep 600 &");;' | hol-d repl /a/b
wait_until started b

step "kill ends the leaf and the command it started."
hol-d kill /a/b
wait_until gone b

step "A busy node and a background command, then SIGKILL of the daemon."
hol-d fork /a c
printf '%s\n' 'ignore (Sys.command "HOLD_TUTORIAL=c sleep 600 &");;' | hol-d repl /a/c
wait_until started c
printf '%s\n' 'Unix.sleep 600;;' | hol-d repl /a/c >/dev/null 2>&1 &
busy() { hol-d tree | grep -q '^/a/c [0-9]* busy$'; }
wait_until busy
hol-d tree
server=$(pgrep -f "server.py $SOCKET ")
kill -9 "$server"
wait_until gone c
nodes_gone() { ! pgrep -f "node.native $server" >/dev/null; }
wait_until nodes_gone
echo "No node or command survived."
