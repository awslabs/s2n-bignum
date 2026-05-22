#!/usr/bin/env python3
"""Decide whether any proof in arch/subdir is affected by changed files.

Prints "true" or "false". Used to gate CI steps.
"""
import json, os, sys
if len(sys.argv) != 5:
    sys.exit("usage: decide-affected.py <arch> <subdir> <deps.json> <changed-files.txt>")
arch, subdir, deps_path, changed_path = sys.argv[1:5]
deps = json.load(open(deps_path))
with open(changed_path) as f:
    changed = {l.strip() for l in f if l.strip()}
if not changed:
    print("true")
    sys.exit(0)
proof_prefix = f"{arch}/proofs/"
for proof, ds in deps.items():
    if not proof.startswith(proof_prefix):
        continue
    stem = os.path.splitext(os.path.basename(proof))[0]
    if not os.path.exists(f"{arch}/{subdir}/{stem}.S"):
        continue
    if changed & set(ds):
        print("true")
        sys.exit(0)
print("false")
