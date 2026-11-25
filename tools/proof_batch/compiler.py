"""Compile a batch of HOL Light proofs against one shared architecture base.

The stock flow (tools/build-proof.sh) compiles every proof into its own
executable that re-elaborates the whole architecture model (<arch>/proofs/
base.ml) before the proof itself. This module compiles that base once as an
OCaml module, Proof_base, and turns each proof's remainder into a small native
plugin (.cmxs) that a worker can Dynlink on top of an initialized base.

How a proof becomes a plugin:
  1. HOL Light's inline_load.ml expands base.ml and the proof source, with
     all their `needs`/`loadt` dependencies, into flat OCaml files.
  2. split_prefix accepts the proof only if the expanded base appears in it
     byte-for-byte, and the HOL parser finds no OCaml code before it. The
     remainder is then the proof's own code, and it runs as if it had been
     loaded right after the base.
  3. The plugin source is the HOL prelude (`open Hol_lib;; open
     Hol_loader;;`), then `open Proof_base;;`, a start timestamp, the
     remainder, and the footer from `tools/build-proof.sh --footer`. The
     footer runs the same axiom check, prints the same theorems and writes
     the same timing record as a stock build.
The base itself is compiled with the export_opens.ml ppx, which rewrites each
top-level `open M` after the prelude into `include M`. The names that the
base's opens bring into scope then become part of Proof_base, so the plugin
resolves names as the original proof did.
Proofs that fail step 2 (for example bignum_sqrt_p25519, which loads Jacobi
theory before the base) are built unchanged by tools/build-proof.sh into a
standalone .native.

Usage. This is a library. tools/proof_batch/run.py (via `make -C <arch>
fork-proofs`) drives it:

    from compiler import build_batch
    artifacts = build_batch("arm", ["proofs/word_min.ml", ...],
                            build_dir, holdir, jobs)

Requirements:
  - The current directory is the repository root.
  - The OCaml switch that built HOL Light is active: ocamlfind, camlp5 and
    zarith are on PATH/OCAMLPATH. run.py selects HOLDIR/_opam automatically.
  - holdir is a HOL Light checkout built with HOLLIGHT_USE_MODULE=1.
  - The `make -C <arch> batch-inputs` objects exist, since proofs read them.
  - build_dir is empty. build_batch owns it: it holds proof_base.*, the
    export-opens ppx and the artifacts.

build_batch returns one artifact per target, in order: a .cmxs plugin or a
standalone .native. tools/proof_batch/runner.py builds the worker that links
proof_base.cmx and executes the artifacts.
"""

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import shlex
import subprocess
import threading
import time


PRELUDE = b"open Hol_lib;;\nopen Hol_loader;;\n"
# Lines of a failed step's output to show. The full output can be thousands
# of lines of HOL loader chatter.
OUTPUT_TAIL = 80


class BuildError(Exception):
    """A build step failed. The message names the proof and holds the tool output."""


def run(label, cmd, **kwargs):
    """Run a build step quietly. On failure, raise with its output under label.

    inline_load.ml, camlp5 and build-proof.sh print a lot that only matters
    when a step fails, so their output is captured rather than streamed.
    """
    if "stdout" in kwargs:
        kwargs["stderr"] = subprocess.PIPE
    else:
        kwargs.update(stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    result = subprocess.run(cmd, **kwargs)
    if result.returncode:
        lines = (result.stdout or result.stderr or b"").decode(errors="replace").splitlines()
        shown = "\n".join(lines[-OUTPUT_TAIL:])
        raise BuildError(f"{label}: {shlex.join(map(str, cmd))} failed (exit "
                         f"{result.returncode}), last {OUTPUT_TAIL} lines:\n{shown}")
    return result


def split_prefix(inlined, base, pp):
    """Remove a byte-identical base only if the preceding OCaml AST is empty."""
    if not base.startswith(PRELUDE) or not inlined.startswith(PRELUDE):
        raise ValueError("unexpected HOL Light inline_load.ml prelude")
    body = base[len(PRELUDE):]
    offset = inlined.find(body, len(PRELUDE))
    if offset < 0:
        return None
    # Let the very same HOL parser handle nested comments, quotations and
    # #line directives. Even a single earlier definition or side effect
    # rules out hoisting the base. Accept only the printed empty structure.
    result = subprocess.run(
        ["ocamlc", "-stop-after", "parsing", "-dparsetree", "-pp", pp + " -impl",
         "-impl", "/dev/stdin"],
        input=inlined[len(PRELUDE):offset], stderr=subprocess.PIPE)
    ast = result.stderr.strip().removeprefix(b"* HOL-Light syntax in effect *").strip()
    if result.returncode or ast != b"[]":
        return None
    return inlined[offset + len(body):]


def write_proof(source, suffix, arch, target):
    with source.open("wb") as stream:
        stream.write(PRELUDE + b"open Proof_base;;\n")
        stream.write(b"let s2n_bignum_build_proof_start_time = Unix.gettimeofday ();;\n")
        stream.write(suffix + b"\n")
        stream.flush()
        run(target, ["tools/build-proof.sh", "--footer", arch, target], stdout=stream)


def build_exporter(build_dir):
    """Build the OCaml AST rewrite with the selected compiler's own libraries."""
    obj = build_dir / "export_opens.cmo"
    mapper = build_dir / "export-opens"
    run("export-opens", ["ocamlc", "-I", "+compiler-libs", "-c",
                         Path(__file__).with_name("export_opens.ml"), "-o", obj])
    run("export-opens", ["ocamlc", "-I", "+compiler-libs", "ocamlcommon.cma", obj, "-o", mapper])
    return mapper


def build_batch(arch, targets, build_dir, holdir, jobs, names=None):
    """Return one artifact per proof and compile the shared base for the worker.

    Prints one progress line per compiled proof, labelled with names (default:
    the source paths), then the slowest compiles.
    """
    names = names or targets
    build_dir, holdir = Path(build_dir).resolve(), Path(holdir).resolve()
    if any(build_dir.iterdir()):
        raise ValueError(f"proof compiler requires an empty build directory: {build_dir}")
    env = dict(os.environ, HOLLIGHT_DIR=str(holdir))
    pp = subprocess.check_output([holdir / "hol.sh", "-pp"], text=True, env=env).strip()
    # A proof's top level compiles to one huge initialization function. The
    # native compiler with linear-scan register allocation handles that about
    # 7x faster than ocamlopt.byte with the default graph-colouring allocator
    # (p256_scalarmul: 929 s -> 122 s), and it compiles even the largest
    # plugins (~145K lines) within the default 8 MB stack.
    compiler = ["ocamlopt.opt", "-linscan", "-w", "-a", "-pp", pp, "-I", holdir, "-I", "+unix",
                "-I", build_dir, "-c"]

    def inline(label, source, dest):
        run(label, ["ocaml", holdir / "inline_load.ml", source, dest], env=env)
        return dest.read_bytes()

    base_ml = build_dir / "proof_base.ml"
    base = inline("proofs/base.ml", Path(arch) / "proofs/base.ml", base_ml)

    def prepare(item):
        i, target = item
        source = build_dir / f"proof_{i}.ml"
        inlined = inline(names[i], Path(arch) / target, source)
        suffix = split_prefix(inlined, base, pp)
        if suffix is None:
            source.unlink()
            return None
        write_proof(source, suffix, arch, target)
        return source

    def build_artifact(index, source):
        name = names[index]
        if source is None:
            # Keep the original load order and use a private native output so
            # concurrent batches or a stock Make build can run independently.
            native = build_dir / f"standalone_{index}.native"
            run(name, ["../tools/build-proof.sh", targets[index], holdir / "hol.sh",
                       os.path.relpath(native, arch)], cwd=arch,
                env=dict(env, TMPDIR=str(build_dir)))
            return native
        run(name, [*compiler, source], env=env)
        plugin = source.with_suffix(".cmxs")
        run(name, ["ocamlopt", "-shared", "-I", holdir, "-I", build_dir,
                   source.with_suffix(".cmx"), "-o", plugin])
        for ext in (".ml", ".cmi", ".cmx", ".o"):
            source.with_suffix(ext).unlink()
        return plugin

    lock, done, seconds = threading.Lock(), [0], {}
    width = len(str(len(targets)))

    def compile_proof(item):
        index, source = item
        start = time.monotonic()
        artifact = build_artifact(index, source)
        elapsed = time.monotonic() - start
        kind = "plugin" if source else "standalone"
        with lock:
            done[0] += 1
            seconds[names[index]] = elapsed
            print(f"[{done[0]:>{width}}/{len(targets)}] built {names[index]} "
                  f"({kind}, {elapsed:.1f} s)", flush=True)
        return artifact

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        start = time.monotonic()
        sources = list(pool.map(prepare, enumerate(targets)))
        print(f"Inlined {len(targets)} proof sources ({time.monotonic() - start:.1f} s)", flush=True)
        # The worker links the base even if every selected proof is standalone.
        start = time.monotonic()
        mapper = build_exporter(build_dir)
        run("proofs/base.ml", [*compiler, "-ppx", shlex.quote(str(mapper)), base_ml],
            env=env)
        print(f"Compiled the shared base ({time.monotonic() - start:.1f} s)", flush=True)
        artifacts = list(pool.map(compile_proof, enumerate(sources)))
    print_slowest("compiles", seconds)
    return artifacts


def print_slowest(what, seconds, count=10):
    slowest = sorted(seconds.items(), key=lambda item: -item[1])[:count]
    if slowest:
        print(f"Slowest {what}:", flush=True)
        for name, elapsed in slowest:
            print(f"  {elapsed:8.1f} s  {name}", flush=True)
