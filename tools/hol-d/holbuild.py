"""Compile exact shared HOL import prefixes and each proof's remaining code."""

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import threading
import time

from layers import (BatchPlan, PRELUDE, ProofModule, ancestors, contextual_block,
                    match_prefixes, module_stem, parent_of, read_layers, unit_name)

# Lines of a failed step's output to show. The full output can be thousands
# of lines of HOL loader chatter.
OUTPUT_TAIL = 80


class BuildError(Exception):
    """A build step failed. The message names the proof and holds the tool output."""


def run(label, cmd, **kwargs):
    """Run a build step quietly. On failure, raise with its output under label.

    inline_load.ml and camlp5 print a lot that only matters
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


def prelude(parent):
    return PRELUDE + b"".join(f"open {unit_name(p).capitalize()};;\n".encode()
                              for p in ancestors(parent))


def write_proof_body(stream, target, body):
    stream.write(body)


def build_exporter(build_dir):
    """Build the OCaml AST rewrite with the selected compiler's own libraries."""
    obj = build_dir / "export_opens.cmo"
    mapper = build_dir / "export-opens"
    run("export-opens", ["ocamlc", "-I", "+compiler-libs", "-c",
                         Path(__file__).with_name("export_opens.ml"), "-o", obj])
    run("export-opens", ["ocamlc", "-I", "+compiler-libs", "ocamlcommon.cma", obj, "-o", mapper])
    return mapper


def build_modules(manifest, root, targets, build_dir, holdir, jobs, *, source_dir=Path('.'),
                  names=None, sessions=(), write_body=write_proof_body):
    """Compile a manifest root, shared or requested layers, and the given proof files.

    Targets are relative to source_dir. HOL imports use the current working directory
    and the HOL load path. write_body(stream, target, body) can wrap a proof remainder.
    """
    targets = [Path(t) for t in targets]
    if any(t.is_absolute() for t in targets):
        raise ValueError("proof sources must be relative to source_dir")
    names = targets if names is None else list(names)
    if len(names) != len(targets):
        raise ValueError("expected one display name per proof source")
    build_dir, holdir = Path(build_dir).resolve(), Path(holdir).resolve()
    source_dir = Path(source_dir)
    if any(build_dir.iterdir()):
        raise ValueError(f"proof compiler requires an empty build directory: {build_dir}")
    sources = read_layers(manifest, root)
    base = '/' + root
    required = {base}
    for session in sessions:
        if session not in sources:
            raise ValueError(f"unknown session {session!r}; choose from {', '.join(sources)}")
        required.update(ancestors(session))
    units = [module_stem("_".join(Path(t).with_suffix("").parts)) for t in targets]
    if len(set(units)) != len(units) or set(units).intersection(map(unit_name, sources)):
        raise ValueError("proof sources must have distinct OCaml module names")
    env = dict(os.environ, HOLLIGHT_DIR=str(holdir))
    pp = subprocess.check_output([holdir / "hol.sh", "-pp"], text=True, env=env).strip()
    # A proof's top level compiles to one huge initialization function. The
    # native compiler with linear-scan register allocation keeps compilation
    # time and stack use manageable for large proof plugins.
    compiler = ["ocamlopt.opt", "-linscan", "-w", "-a", "-pp", pp, "-I", holdir, "-I", "+unix",
                "-I", build_dir, "-c"]

    def inline(label, source, dest):
        run(label, ["ocaml", holdir / "inline_load.ml", source, dest], env=env)
        data = dest.read_bytes()
        if not data.startswith(PRELUDE):
            raise ValueError(f"{label}: unexpected HOL Light inliner prelude")
        return data

    def compile_module(name, source, *options):
        run(name, [*compiler, *options, source], env=env)
        plugin = source.with_suffix(".cmxs")
        run(name, ["ocamlopt", "-shared", "-I", holdir, "-I", build_dir,
                   source.with_suffix(".cmx"), "-o", plugin])
        source.unlink()
        source.with_suffix(".o").unlink()
        return plugin

    base_ml = build_dir / (unit_name(base) + '.ml')
    blocks = {base: inline(sources[base], sources[base], base_ml)[len(PRELUDE):]}
    lock, seconds = threading.Lock(), {}
    width = len(str(len(targets)))

    with tempfile.TemporaryDirectory(dir=build_dir) as directory, ThreadPoolExecutor(jobs) as pool:
        scratch = Path(directory)
        wrappers = scratch / "imports"
        wrappers.mkdir()

        def block(session):
            with lock:
                if session not in blocks:
                    blocks[session] = contextual_block(session, sources, wrappers, inline)
                return blocks[session]

        def prepare(target, unit, name):
            flat = scratch / (unit + '.flat')
            data = inline(name, source_dir / target, flat)
            ends = match_prefixes(data, sources, block, pp)
            # Keep only the remainder on disk while counting shared prefixes.
            start = ends.get(base, len(PRELUDE))
            flat.write_bytes(data[start:])
            return {p: offset - start for p, offset in ends.items()}

        start = time.monotonic()
        offsets = list(pool.map(prepare, targets, units, names))
        print(f"Inlined {len(targets)} proof sources ({time.monotonic() - start:.1f} s)", flush=True)
        counts = Counter(p for ends in offsets for p in ends)
        retained = {p for p in sources if p in required or counts[p] >= 2}
        layers = {}
        mapper = build_exporter(scratch)
        for session in sources:
            if session not in retained:
                continue
            start = time.monotonic()
            parent = parent_of(session)
            source = build_dir / (unit_name(session) + '.ml')
            if session != base:
                source.write_bytes(prelude(parent) + block(session))
            # Keep generated ancestor opens private. Only opens from the
            # original HOL source export names at this boundary.
            ppx = shlex.join([str(mapper), *[unit_name(p).capitalize() for p in ancestors(parent)]])
            plugin = compile_module(sources[session], source, "-ppx", ppx)
            layers[session] = plugin.relative_to(build_dir)
            print(f"Compiled {session} ({time.monotonic() - start:.1f} s)", flush=True)

        def compile_proof(target, unit, name, ends):
            parent = max((p for p in ends if p == '/' or p in retained), key=ends.__getitem__)
            source = build_dir / (unit + '.ml')
            if parent == '/':
                source = build_dir / 'root' / source.name
                source.parent.mkdir(exist_ok=True)
            flat = scratch / (unit + '.flat')
            with flat.open('rb') as remainder, source.open('wb') as stream:
                remainder.seek(ends[parent])
                stream.write(prelude(parent))
                write_body(stream, target, remainder.read())
            flat.unlink()
            start = time.monotonic()
            plugin = compile_module(name, source)
            elapsed = time.monotonic() - start
            with lock:
                seconds[name] = elapsed
                print(f"[{len(seconds):>{width}}/{len(targets)}] built {name} "
                      f"({parent}, {elapsed:.1f} s)", flush=True)
            return ProofModule(parent, plugin.relative_to(build_dir))

        artifacts = list(pool.map(compile_proof, targets, units, names, offsets))
    print_slowest("compiles", seconds)
    return BatchPlan(layers, dict(zip(map(str, targets), artifacts)))


def print_slowest(what, seconds, count=10):
    slowest = sorted(seconds.items(), key=lambda item: -item[1])[:count]
    if slowest:
        print(f"Slowest {what}:", flush=True)
        for name, elapsed in slowest:
            print(f"  {elapsed:8.1f} s  {name}", flush=True)
