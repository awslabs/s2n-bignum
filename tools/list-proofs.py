#!/usr/bin/env python3
"""List all proof entries as JSON suitable for a GitHub Actions matrix.

Each entry: {arch, subdir, name} — name is the .S/.ml stem.
"""
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
out = []
for arch in ("arm", "x86"):
    proofs = ROOT / arch / "proofs"
    if not proofs.exists(): continue
    for sd in sorted((ROOT / arch).iterdir()):
        if not sd.is_dir() or sd.name in ("proofs","tutorial","armsimulate","allowed_asm"):
            continue
        for s in sorted(sd.glob("*.S")):
            stem = s.stem
            ml = proofs / (stem + ".ml")
            if not ml.exists(): continue
            out.append({"arch": arch, "subdir": sd.name, "name": stem})
json.dump(out, sys.stdout)
sys.stdout.write("\n")
