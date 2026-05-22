#!/usr/bin/env python3
"""Compute the transitive dependency map for s2n-bignum HOL Light proofs.

Each proof file (arm/proofs/*.ml or x86/proofs/*.ml that has a matching .S
under the architecture's subdirectories) is examined for `needs "..."` and
`loadt "..."` lines, and those are followed transitively.

External (HOL Light Library) paths and missing files are pruned.

Output: JSON mapping repo-relative .ml/.S paths to lists of files whose
change can invalidate that proof's outcome.

Used by the CI workflow to decide which proof matrix entries (and which
individual proofs inside them) to run for a given PR.
"""

import json, os, re, sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Match `needs "path/to/file.ml";;` and `loadt "path/to/file.ml";;`
NEED_RE = re.compile(r'^\s*(?:needs|loadt|loads)\s+"([^"]+)"\s*;;')

def load_file_deps(path: Path, cache: dict) -> set:
    """Return the set of repo-relative dep paths reachable from `path`,
    including `path` itself. Cached."""
    key = str(path.relative_to(REPO_ROOT)) if path.is_absolute() else str(path)
    if key in cache:
        return cache[key]
    cache[key] = {key}  # break cycles
    if not path.exists():
        return cache[key]
    deps = {key}
    with path.open() as f:
        for line in f:
            m = NEED_RE.match(line)
            if not m:
                continue
            ref = m.group(1)
            ref_path = REPO_ROOT / ref
            if not ref_path.exists():
                # external / Library / EC / ...
                continue
            deps |= load_file_deps(ref_path, cache)
    cache[key] = deps
    return deps

def main():
    cache = {}
    out = {}
    for arch in ("arm", "x86"):
        proofs_dir = REPO_ROOT / arch / "proofs"
        if not proofs_dir.exists():
            continue
        # Each .S in arch/<subdir>/*.S has a matching .ml in arch/proofs/
        for sd in sorted((REPO_ROOT / arch).iterdir()):
            if not sd.is_dir() or sd.name in ("proofs", "tutorial", "armsimulate", "allowed_asm"):
                continue
            for s in sorted(sd.glob("*.S")):
                ml = proofs_dir / (s.stem + ".ml")
                if not ml.exists():
                    continue
                key = str(ml.relative_to(REPO_ROOT))
                deps = load_file_deps(ml, cache)
                # The .S file itself also invalidates the proof
                deps.add(str(s.relative_to(REPO_ROOT)))
                out[key] = sorted(deps)
    json.dump(out, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")

if __name__ == "__main__":
    main()
