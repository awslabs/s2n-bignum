#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#
# Run a HOL Light server (monadius/hol_server, server2.ml) for the
# equivalence proofs, with files preloaded before the server starts.
#
#   hol-server.sh start PORT [FILE.ml ...]   start; FILEs are loadt'ed first
#   hol-server.sh wait PORT                  block until the server accepts
#   hol-server.sh stop PORT                  kill the server
#   hol-server.sh status PORT                show state and preload errors
#
# FILE paths are relative to the s2n-bignum repository root, which is the
# server's working directory. HOL Light and server2.ml come from the
# mlkem-native `hol_light` nix shell (set MLKEM_NATIVE to its checkout;
# default ~/repos/mlkem-native), or from HOL_SH and HOL_SERVER_SRC if set.
# Logs go to $HOL_EQUIV_LOGDIR (default /tmp/fips203-equiv/hol-PORT.log).

set -euo pipefail

cmd=${1:-}
port=${2:-}
[ -n "$cmd" ] && [ -n "$port" ] || { sed -n '5,17p' "$0"; exit 1; }
shift 2

here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
logdir=${HOL_EQUIV_LOGDIR:-/tmp/fips203-equiv}
mkdir -p "$logdir"
log="$logdir/hol-$port.log"
pidf="$logdir/hol-$port.pid"

port_open() {
  python3 - "$port" <<'EOF'
import socket, sys
# Complete the handshake and say goodbye: a client that just drops the
# connection makes server2.ml leave its accept loop.
try:
    s = socket.create_connection(("127.0.0.1", int(sys.argv[1])), timeout=5)
    buf = b""
    while b"ready:" not in buf:
        chunk = s.recv(4096)
        if not chunk:
            sys.exit(1)
        buf += chunk
    s.sendall(b"#quit\n")
    s.close()
    sys.exit(0)
except OSError:
    sys.exit(1)
EOF
}

alive() { [ -f "$pidf" ] && kill -0 "$(cat "$pidf")" 2>/dev/null; }

preload_errors() {
  grep -naE 'Exception:|^Error|Failure "|Unbound value|Unbound constructor|Characters [0-9]+-[0-9]+:' "$log" | head -20 || true
}

case "$cmd" in
  start)
    if alive; then echo "server on port $port already running (pid $(cat "$pidf"))"; exit 0; fi
    if [ -z "${HOL_SH:-}" ] || [ -z "${HOL_SERVER_SRC:-}" ]; then
      command -v nix >/dev/null || . /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh
      mn=${MLKEM_NATIVE:-$HOME/repos/mlkem-native}
      eval "$(cd "$mn" && nix develop .#hol_light --command bash -c \
        'echo HOL_SH=$(command -v hol.sh); grep -E "^HOL_SERVER_SRC=" "$(command -v hol-server)"')"
    fi
    {
      for f in "$@"; do
        printf 'loadt "%s";;\n' "$f"
      done
      echo 'print_endline "HOL-SERVER-PRELOAD-DONE";;'
      echo '#directory "+unix";;'
      echo '#directory "+threads";;'
      echo '#load "unix.cma";;'
      echo '#load "threads.cma";;'
      printf '#use "%s/server2.ml";;\n' "$HOL_SERVER_SRC"
      # Restart the accept loop if a client disconnects abruptly.
      printf 'let rec fips_serve () = try start ~single_connection:false %s with e -> (Format.printf "[RESTART] %%s@." (Printexc.to_string e); fips_serve ());;\n' "$port"
      echo 'fips_serve ();;'
    } > "$logdir/hol-$port.init.ml"
    # setsid: own process group, so `stop` can kill HOL and the feeder.
    setsid bash -c "cd '$repo' && { cat '$logdir/hol-$port.init.ml'; exec sleep infinity; } | exec '$HOL_SH'" \
      > "$log" 2>&1 < /dev/null &
    echo $! > "$pidf"
    echo "started HOL server on port $port (pid $!, log $log)"
    ;;
  wait)
    while ! port_open; do
      if ! alive; then echo "server on port $port died; see $log"; preload_errors; exit 1; fi
      sleep 2
    done
    echo "server on port $port is ready"
    errs=$(preload_errors)
    if [ -n "$errs" ]; then echo "WARNING: errors while preloading:"; echo "$errs"; exit 1; fi
    ;;
  stop)
    if alive; then
      kill -- -"$(cat "$pidf")" 2>/dev/null || kill "$(cat "$pidf")" 2>/dev/null || true
      echo "stopped server on port $port"
    else
      echo "no server on port $port"
    fi
    rm -f "$pidf"
    ;;
  status)
    if alive; then
      if port_open; then echo "port $port: ready (pid $(cat "$pidf"))";
      else echo "port $port: loading (pid $(cat "$pidf"))"; fi
    else
      echo "port $port: not running"
    fi
    preload_errors
    ;;
  *)
    sed -n '5,17p' "$0"; exit 1;;
esac
