#!/usr/bin/env python3
"""Filter the full proof matrix down to entries affected by changed files.

Args: <all-proofs.json> <proof-deps.json> <changed-files.txt>

  - all-proofs.json: list of {arch, subdir, name} entries.
  - proof-deps.json: {"<arch>/proofs/<name>.ml": [dep paths...], ...}
  - changed-files.txt: one repo-relative path per line; empty = run everything.

Emits a JSON array (single line) of the affected entries.
"""
import json, sys

if len(sys.argv) != 4:
    sys.exit("usage: filter-affected.py <all-proofs.json> <proof-deps.json> <changed-files.txt>")

all_path, deps_path, changed_path = sys.argv[1:4]
all_proofs = json.load(open(all_path))
deps = json.load(open(deps_path))
with open(changed_path) as f:
    changed = {l.strip() for l in f if l.strip()}

if not changed:
    json.dump(all_proofs, sys.stdout)
    sys.stdout.write("\n")
    sys.exit(0)

out = []
for p in all_proofs:
    key = f"{p['arch']}/proofs/{p['name']}.ml"
    ds = deps.get(key)
    if ds is None:
        # Unknown proof → conservatively include
        out.append(p)
        continue
    if changed & set(ds):
        out.append(p)

json.dump(out, sys.stdout)
sys.stdout.write("\n")
