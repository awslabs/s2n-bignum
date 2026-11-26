"""Build s2n-bignum proof plugins and check them in a batch-owned HOL daemon."""

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import asyncio
from collections import defaultdict, deque
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

HOL_D = Path(__file__).resolve().parents[1] / "hol-d"
sys.path.insert(0, str(HOL_D))
from daemon import owned_server
from holbuild import BuildError, build_modules, print_slowest, run
from layers import ancestors, parent_of


# The same check as the grep in tools/run-proof.sh.
ERROR = re.compile(rb"error:|exception:", re.IGNORECASE)
RETURNED = b"Proof batch plugin returned\n"
SECONDS = rb"[0-9]+\.[0-9]{6}"
TIMING = re.compile(rb"Running time: " + SECONDS + rb" sec, Start unixtime: " +
                    SECONDS + rb", End unixtime: " + SECONDS + rb"\n")


def build_batch(arch, targets, build_dir, holdir, jobs, names=None, sessions=()):
    def write_body(stream, target, body):
        stream.write(b"let s2n_bignum_build_proof_start_time = Unix.gettimeofday ();;\n")
        stream.write(body + b"\n")
        stream.flush()
        run(target, ["tools/build-proof.sh", "--footer", arch, target], stdout=stream)

    return build_modules(Path(__file__).with_name("layers.json"), arch, targets, build_dir,
                         holdir, jobs, source_dir=arch, names=names, sessions=sessions,
                         write_body=write_body)


def log_error(path, *, proof=False, returncode=0):
    """Return the first diagnostic or the reason the command or footer failed."""
    count = 0
    last = b""
    with path.open("rb") as stream:
        for last in stream:
            if ERROR.search(last):
                return last.strip()[:300].decode(errors="replace")
            if last.startswith(b"Running time:"):
                count += 1
    if returncode:
        detail = last[:300].decode(errors="replace").strip()
        return f"hol-d exited {returncode}" + (f": {detail}" if detail else "")
    if proof and (count != 1 or not TIMING.fullmatch(last)):
        return "expected one timing record ending the proof"
    return None


async def command(cli, output, *arguments):
    process = await asyncio.create_subprocess_exec(
        *cli, *arguments, stdout=output, stderr=subprocess.STDOUT)
    try:
        return await process.wait()
    finally:
        if process.returncode is None:
            process.kill()
            await process.wait()


async def run_tree(cli, build_dir, layers, tasks, jobs, log_dir):
    children, proofs = defaultdict(list), defaultdict(list)
    needed = {p for module, _, _ in tasks for p in ancestors(module.parent)}
    for session in layers:
        if session in needed:
            children[parent_of(session)].append(session)
    for task in tasks:
        proofs[task[0].parent].append(task)

    # A session called "ecc.log" can also have children. Escape dots so its
    # directory never occupies the "ecc" sibling's log file.
    logs = {p: log_dir / 'sessions' / (p.lstrip('/').replace('.', '%2E') + '.log') for p in needed}
    errors, seconds = {}, {}
    ready_layers, ready_proofs = deque(), deque()
    completed = 0
    width = len(str(len(tasks)))

    def report(log, error, elapsed=None):
        nonlocal completed
        completed += 1
        name = os.path.relpath(log, log_dir)
        timing = ''
        if elapsed is not None:
            seconds[name] = elapsed
            timing = f' ({elapsed:.1f} s)'
        if error:
            errors[log] = error
        print(f"[{completed:>{width}}/{len(tasks)}] "
              f"{'FAILED' if error else 'ok'} {name}{timing}"
              + (f": {error}" if error else ""), flush=True)

    def release(parent, error=None):
        if error:
            for _, log, _ in proofs[parent]:
                report(log, error)
            for child in children[parent]:
                release(child, error)
        else:
            ready_layers.extend(children[parent])
            ready_proofs.extend(proofs[parent])

    async def initialize(session):
        started = time.monotonic()
        path = logs[session]
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb', buffering=0) as output:
            status = await command(cli, output, 'fork', parent_of(session), session.rsplit('/', 1)[1])
            if status == 0:
                status = await command(cli, output, 'load', '--public', session, build_dir / layers[session])
            error = log_error(path, returncode=status)
            elapsed = time.monotonic() - started
            if error:
                detail = f'{session}: {error} (log {path})'
                print(detail, file=sys.stderr, flush=True)
                release(session, detail)
            else:
                output.write(f'Proof batch session ready: {session} {elapsed:.3f} sec\n'.encode())
                print(f'Initialized {session} ({elapsed:.1f} s)', flush=True)
                release(session)

    async def run_one(module, log, partial):
        started = time.monotonic()
        log.parent.mkdir(parents=True, exist_ok=True)
        with partial.open('xb') as output:
            status = await command(cli, output, 'run', module.parent, build_dir / module.path)
        error = log_error(partial, proof=True, returncode=status)
        report(log, f'{error} (log {partial})' if error else None, time.monotonic() - started)

    release('/')
    running = set()
    while ready_layers or ready_proofs or running:
        # Give prerequisite loads first access to a free slot. Other slots
        # can run ready proofs while another branch initializes.
        while len(running) < jobs and (ready_layers or ready_proofs):
            work = initialize(ready_layers.popleft()) if ready_layers else run_one(*ready_proofs.popleft())
            running.add(asyncio.create_task(work))
        done, running = await asyncio.wait(running, return_when=asyncio.FIRST_COMPLETED)
        for task in done:
            task.result()
    print_slowest('proofs', seconds)
    return errors


def run_batch(build_dir, layers, artifact_logs, jobs, base_log):
    """Publish only after checking the leaf, its ancestors and the daemon exit."""
    tasks = [(module, log, log.with_name(log.name + '.partial')) for module, log in artifact_logs]
    with tempfile.TemporaryDirectory(prefix='hol-d-batch-') as directory, base_log.open('xb', buffering=0) as out:
        socket = Path(directory) / 'socket'
        cli = [sys.executable, HOL_D / 'hol-d', '--socket', socket]
        started = time.monotonic()
        with owned_server(socket, Path.cwd(), build_dir / 'build', out) as server:
            root_error = log_error(base_log)
            if root_error:
                print(f'{base_log}: {root_error}', file=sys.stderr, flush=True)
                return False
            elapsed = time.monotonic() - started
            out.write(f'Proof batch root ready: {elapsed:.3f} sec\n'.encode())
            print(f'Initialized / ({elapsed:.1f} s)', flush=True)
            errors = asyncio.run(run_tree(cli, build_dir, layers, tasks, jobs, base_log.parent))
    root_error = log_error(base_log, returncode=server.returncode)
    if root_error:
        print(f'{base_log}: {root_error}', file=sys.stderr, flush=True)
        return False
    # Session logs hold only their CLI's fork and load output, which
    # initialize() checked before releasing any descendant. Nodes write
    # nothing outside a request, so only the root log can change later.
    for module, log, partial in tasks:
        if log not in errors and not partial.exists():
            errors[log] = 'proof never ran'  # Fail closed.
        if log not in errors:
            with partial.open('ab') as stream:
                stream.write(RETURNED)
            partial.rename(log)
    if errors:
        print(f'{len(errors)} of {len(tasks)} proofs failed:',
              *(f'  {log}: {error}' for log, error in errors.items()), sep='\n', flush=True)
    return not errors
