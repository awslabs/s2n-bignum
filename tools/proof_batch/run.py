#!/usr/bin/env python3
"""Check a batch of ARM or x86 proofs with a shared native architecture base."""

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import argparse
from contextlib import contextmanager
import os
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import tempfile
import time

from runner import HOL_D, BuildError, build_batch, run, run_batch


ROOT = Path(__file__).resolve().parents[2]


def positive(value):
    n = int(value)
    if n < 1:
        raise argparse.ArgumentTypeError("expected a positive job count")
    return n


def source_path(arch, name):
    arch_root = ROOT / arch
    path = Path(name)
    if not path.is_absolute() and path.parts[0] == arch:
        path = path.relative_to(arch)
    path = (arch_root / path).resolve().relative_to(arch_root)
    if not (arch_root / path).is_file():
        raise ValueError(f"missing proof source: {arch}/{path}")
    return path


def select_targets(arch, make, requested):
    """Resolve source names or Make targets to canonical .correct log paths."""
    manifest = [Path(p) for p in subprocess.check_output([*make, "batch-targets"], text=True).splitlines()]
    if not manifest or len(manifest) != len(set(manifest)):
        raise ValueError("empty or duplicate Make proof targets")
    if not requested:
        return manifest
    by_source = {proof_source(target): target for target in manifest}
    selected = []
    for target in requested:
        if target.endswith(".ml"):
            name = by_source.get(source_path(arch, target))
        else:
            name = Path(target.removesuffix(".correct") + ".correct")
        if name not in manifest:
            raise ValueError(f"unknown target {target!r}; use an architecture-relative Make target")
        if name in selected:
            raise ValueError(f"duplicate target {target!r}")
        selected.append(name)
    return selected


def proof_source(target):
    if target.parts[0] in ("proofs", "tutorial"):
        return target.with_suffix(".ml")
    return Path("proofs") / target.with_suffix(".ml").name


def module_sources(arch, make, requested):
    """Accept Make targets or proof source paths, including new .ml files."""
    names = [name for name in requested if not name.endswith(".ml")]
    targets = dict(zip(names, select_targets(arch, make, names))) if names else {}
    sources = []
    for name in requested:
        path = proof_source(targets[name]) if name in targets else source_path(arch, name)
        if path != Path("proofs/base.ml"):
            sources.append(path)
    return sources


@contextmanager
def phase(name):
    start = time.monotonic()
    try:
        yield
    finally:
        seconds = time.monotonic() - start
        print(f"{name.capitalize()} wall time: {seconds:.2f}s", flush=True)
        if os.environ.get("GITHUB_OUTPUT"):
            with open(os.environ["GITHUB_OUTPUT"], "a") as stream:
                print(f"{name}_seconds={round(seconds)}", file=stream)


def check(args):
    holdir = args.holdir.resolve()
    if not (holdir / "hol_lib.cmxa").is_file():
        raise ValueError("set HOLDIR to a HOL Light checkout built with HOLLIGHT_USE_MODULE=1")
    switch = holdir / "_opam"
    if switch.is_dir() and Path(os.environ.get("OPAM_SWITCH_PREFIX", ".")).resolve() != switch:
        os.execvp("opam", ["opam", "exec", "--switch", str(holdir), "--",
                           sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]])
    out = args.output.resolve() if args.output else None
    os.chdir(ROOT)
    make = ["make", "-s", "--no-print-directory", "-C", args.arch]
    jobs = args.build_jobs or args.jobs
    inputs = [*make, "-j", str(jobs), "batch-inputs"]
    if args.modules:
        sources = module_sources(args.arch, make, args.targets)
        subprocess.run(inputs, check=True)
        if out:
            out.mkdir(parents=True)
        else:
            out = Path(tempfile.mkdtemp(prefix=f"{args.arch}-modules-"))
        try:
            plan = build_batch(args.arch, sources, out, holdir, jobs, sessions=args.session)
            plan.write(out / "plan.json")
        except BaseException:
            shutil.rmtree(out)
            raise
        for path in plan.layers.values():
            print(out / path)
        for module in plan.proofs.values():
            print(out / module.path)
        print(out / "plan.json")
        return 0
    targets = select_targets(args.arch, make, args.targets)
    sources = [proof_source(t) for t in targets]
    if out:
        out.mkdir(parents=True)  # Each invocation owns a fresh directory.
    else:
        out = Path(tempfile.mkdtemp(prefix="proof-logs-"))
    print(f"Proof logs: {out}", flush=True)
    # Keep the shared base and its plugins together for exactly this invocation.
    with tempfile.TemporaryDirectory(prefix="proof-build-") as scratch:
        with phase("build"):
            subprocess.run(inputs, check=True)
            build_dir = Path(scratch)
            plan = build_batch(args.arch, sources, build_dir, holdir, jobs,
                               names=[str(t.with_suffix("")) for t in targets])
            run("hol-d", ["make", "-C", build_dir, "-f", HOL_D / "Makefile", f"HOLDIR={holdir}"])
            plan.write(out / "plan.json")
            artifacts = list(plan.proofs.values())
            shared = sum(a.parent != "/" for a in artifacts)
            print(f"Built {shared} shared-base and {len(targets) - shared} bare-root proof modules.", flush=True)
            for target, artifact in zip(targets, artifacts):
                if artifact.parent == "/":
                    print(f"Bare HOL root: {target}", flush=True)
        with phase("proof"):
            tasks = [(a, out / args.arch / t) for a, t in zip(artifacts, targets)]
            if not run_batch(build_dir, plan.layers, tasks, args.jobs, out / "base.log"):
                return 1
            if not args.targets:
                subprocess.run(["tools/count-proofs.sh", args.arch, out / args.arch], check=True)
    print(f"Checked {len(targets)} {args.arch} targets.", flush=True)
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("arch", choices=("arm", "x86"))
    parser.add_argument("targets", nargs="*",
                        help="Make target or source such as generic/word_min or proofs/word_min.ml (default: all, "
                             "including tutorials, followed by the theorem inventory check)")
    parser.add_argument("-j", "--jobs", type=positive, default=2, help="concurrent proofs (default 2)")
    parser.add_argument("--build-jobs", type=positive, help="concurrent compilations (defaults to --jobs)")
    parser.add_argument("--holdir", type=Path, default=Path(os.environ.get("HOLDIR", "~/hol-light")).expanduser())
    parser.add_argument("--modules", action="store_true",
                        help="build loadable modules only (accepts .ml sources; defaults to the architecture base)")
    parser.add_argument("--session", action="append", default=[],
                        help="also build this named session and its ancestors with --modules (repeatable)")
    parser.add_argument("--output", type=Path, help="new directory for logs or modules (default: temporary directory)")
    args = parser.parse_intermixed_args()
    if args.session and not args.modules:
        parser.error("--session requires --modules")
    # Unwind the batch and stop its private daemon if Make or CI cancels it.
    for sig in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, lambda signum, _: sys.exit(128 + signum))
    try:
        return check(args)
    except (BuildError, OSError, ValueError, subprocess.CalledProcessError) as error:
        print(error, file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
