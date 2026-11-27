#!/usr/bin/env python3
"""Check a batch of ARM or x86 proofs with a shared native architecture base."""

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import argparse
from contextlib import contextmanager
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

from compiler import BuildError, build_batch
from runner import build_worker, run_batch


ROOT = Path(__file__).resolve().parents[2]


def positive(value):
    n = int(value)
    if n < 1:
        raise argparse.ArgumentTypeError("expected a positive job count")
    return n


def select_targets(make, requested):
    """Return the requested Make targets, or all of them if none are given."""
    manifest = subprocess.check_output([*make, "batch-targets"], text=True).splitlines()
    if not manifest or len(manifest) != len(set(manifest)):
        raise ValueError("empty or duplicate Make proof targets")
    if not requested:
        return [Path(t) for t in manifest]
    selected = []
    for target in requested:
        name = target.removesuffix(".correct") + ".correct"
        if name not in manifest:
            raise ValueError(f"unknown target {target!r}; use an architecture-relative Make target")
        if Path(name) in selected:
            raise ValueError(f"duplicate target {target!r}")
        selected.append(Path(name))
    return selected


def proof_source(target):
    if target.parts[0] in ("proofs", "tutorial"):
        return target.with_suffix(".ml")
    return Path("proofs") / target.with_suffix(".ml").name


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
    targets = select_targets(make, args.targets)
    sources = [str(proof_source(t)) for t in targets]
    jobs = args.build_jobs or args.jobs
    if out:
        out.mkdir(parents=True)  # Each invocation owns a fresh directory.
    else:
        out = Path(tempfile.mkdtemp(prefix="proof-logs-"))
    print(f"Proof logs: {out}", flush=True)
    # Keep the shared base and its plugins together for exactly this invocation.
    with tempfile.TemporaryDirectory(prefix="proof-build-") as scratch:
        with phase("build"):
            subprocess.run([*make, "-j", str(jobs), "batch-inputs"], check=True)
            build_dir = Path(scratch)
            artifacts = build_batch(args.arch, sources, build_dir, holdir, jobs,
                                    names=[str(t.with_suffix("")) for t in targets])
            shared = sum(a.suffix == ".cmxs" for a in artifacts)
            worker = build_worker(build_dir, holdir)
            print(f"Built {shared} shared proofs and {len(targets) - shared} standalone proofs.", flush=True)
            for target, artifact in zip(targets, artifacts):
                if artifact.suffix == ".native":
                    print(f"Standalone: {target}", flush=True)
        with phase("proof"):
            tasks = [(a, out / args.arch / t) for a, t in zip(artifacts, targets)]
            if not run_batch(worker, tasks, args.jobs, out / "base.log"):
                return 1
            if not args.targets:
                subprocess.run(["tools/count-proofs.sh", args.arch, out / args.arch], check=True)
    print(f"Checked {len(targets)} {args.arch} targets.", flush=True)
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("arch", choices=("arm", "x86"))
    parser.add_argument("targets", nargs="*",
                        help="Make target such as generic/word_min[.correct] (default: all, "
                             "including tutorials, followed by the theorem inventory check)")
    parser.add_argument("-j", "--jobs", type=positive, default=2, help="concurrent proofs (default 2)")
    parser.add_argument("--build-jobs", type=positive, help="concurrent compilations (defaults to --jobs)")
    parser.add_argument("--holdir", type=Path, default=Path(os.environ.get("HOLDIR", "~/hol-light")).expanduser())
    parser.add_argument("--output", type=Path, help="new directory for logs (default: temporary directory)")
    args = parser.parse_intermixed_args()
    # Turn SIGTERM and SIGHUP into exceptions, so runner.run_worker kills the worker group.
    for sig in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, lambda signum, _: sys.exit(128 + signum))
    try:
        return check(args)
    except (BuildError, OSError, ValueError, subprocess.CalledProcessError) as error:
        print(error, file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
