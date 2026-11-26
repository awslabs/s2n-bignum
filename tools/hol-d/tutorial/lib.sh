# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Sourced by each tutorial step. It builds hol-d, gives the step its own
# daemon on a private socket, and stops that daemon when the step ends.
# `hol-d ...` below is the CLI with that socket; `expect` checks output.

set -eu

HOLD=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
: "${HOLDIR:?set HOLDIR to a HOL Light checkout built with HOLLIGHT_USE_MODULE=1}"
if [ -d "$HOLDIR/_opam" ]; then
    eval "$(opam env --switch "$HOLDIR" --set-switch)"
fi
make -s -C "$HOLD" HOLDIR="$HOLDIR"

WORK=$(mktemp -d)
SOCKET=$WORK/socket
hol-d() { python3 "$HOLD/hol-d" --socket "$SOCKET" "$@"; }
trap 'hol-d stop >/dev/null 2>&1 || true; rm -rf "$WORK"' EXIT

# Run a step's commands from a scratch copy of its directory.
cp -R "$(dirname "$0")/." "$WORK/step"
cd "$WORK/step"

# expect PATTERN TEXT: fail the step unless TEXT contains PATTERN.
expect() {
    if ! grep -qF -- "$1" <<<"$2"; then
        printf 'expected %s in:\n%s\n' "$1" "$2" >&2
        exit 1
    fi
}

# Build NAME.cmxs from NAME.ml as the README describes.
plugin() {
    for name in "$@"; do
        "$HOLDIR/hol.sh" compile "$name.ml" -open Hol_lib -I . >/dev/null
        ocamlopt -shared "$name.cmx" -o "$name.cmxs"
    done
}

step() { printf '\n== %s\n' "$*"; }

# wait_until COMMAND...: retry COMMAND for up to 60 s, then fail the step.
wait_until() {
    for _ in $(seq 600); do "$@" && return 0; sleep 0.1; done
    echo "timed out waiting for: $*" >&2
    exit 1
}
