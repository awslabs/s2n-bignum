#!/bin/bash

set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
event_file="$repo_root/common/safety.ml"
allowed_file="$repo_root/x86/allowed_asm"

events="$(
  grep -oE 'EventX86[A-Z0-9_]+' "$event_file" \
    | sed 's/^EventX86//' \
    | tr '[:upper:]' '[:lower:]' \
    | sort -u
)"

failed=0
count=0

for insn in $events; do
  count=$((count + 1))

  if grep -Fxq ": ${insn}\$" "$allowed_file"; then
    echo "ERROR: x86 instruction '$insn' emits a microarchitectural event"
    echo "       but is also present in x86/allowed_asm."
    failed=1
  fi
done

if [ "$failed" -ne 0 ]; then
  exit 1
fi

echo "Event policy check passed for $count x86 event-generating instructions."
