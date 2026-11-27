"""Execute native proof plugins in children of a warm base."""

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import contextlib
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import threading
import time

from compiler import print_slowest


def build_worker(build_dir: Path, holdir: Path) -> Path:
    """Link the worker with the shared base."""
    worker_source = Path(__file__).resolve().with_name("worker.ml")
    build_dir = build_dir.resolve()
    holdir = holdir.resolve()
    worker = build_dir / "worker.native"
    ocaml = ["ocamlfind", "ocamlopt"]
    subprocess.run(ocaml + ["-package", "unix,dynlink", "-c", worker_source,
                            "-o", "worker.cmx"], cwd=build_dir, check=True)
    # A plugin can refer to library units that the host itself never calls.
    subprocess.run(ocaml + ["-linkall", "-package", "zarith,unix,dynlink", "-linkpkg",
                            "-I", holdir, holdir / "hol_lib.cmxa", "proof_base.cmx",
                            "worker.cmx", "-o", worker], cwd=build_dir, check=True)
    return worker


# The same check as the grep in tools/run-proof.sh.
ERROR = re.compile(rb"error:|exception:", re.IGNORECASE)
RETURNED = b"Proof batch plugin returned\n"
# The footer from proof_footer in tools/build-proof.sh, which also feeds
# tools/proof_timing/collect.py (TIMING). Six decimals: Printf "%f".
SECONDS = rb"[0-9]+\.[0-9]{6}"
TIMING = re.compile(rb"Running time: " + SECONDS + rb" sec, Start unixtime: " +
                    SECONDS + rb", End unixtime: " + SECONDS + rb"\n")


def scan_log(path):
    """Return (timing lines, last line), or None if the log reports an error."""
    last = b""
    timings = []
    with path.open("rb") as stream:
        for last in stream:
            if ERROR.search(last):
                print(f"{path}: {last[:500].decode(errors='replace').strip()}", file=sys.stderr)
                return None
            if last.startswith(b"Running time:"):
                timings.append(last)
    return timings, last


def valid_proof_log(path, plugin):
    """A proof log has no error and exactly one timing record. A plugin must
    then return to the worker. A standalone executable has no such wrapper, so
    its timing record must be the final line."""
    scan = scan_log(path)
    if scan is None:
        return False
    timings, last = scan
    if plugin and last != RETURNED:
        print(f"{path}: proof plugin did not return", file=sys.stderr)
        return False
    if len(timings) != 1 or not TIMING.fullmatch(timings[0]):
        print(f"{path}: expected exactly one proof timing record", file=sys.stderr)
        return False
    if not plugin and last != timings[0]:
        print(f"{path}: expected the timing record on the final line", file=sys.stderr)
        return False
    return True


def first_error(path):
    """The first error line of a log, else its last line, for a progress report."""
    last = ""
    with path.open(errors="replace") as stream:
        for line in stream:
            if ERROR.search(line.encode()):
                return line.strip()[:300]
            last = line.strip() or last
    return last[:300]


def read_status(read_fd, on_status):
    with os.fdopen(read_fd, "r") as stream:
        for line in stream:
            try:
                status, seconds, log = line.rstrip("\n").split("\t")
                on_status(status, float(seconds), log)
            except Exception as error:  # Keep draining, or the worker blocks.
                print(f"Bad proof status line {line!r}: {error}", file=sys.stderr, flush=True)


def run_worker(args, base_log, on_status):
    """Run the worker in its own process group. However it ends, kill the
    group afterwards, so that no proof outlives the batch. That includes
    children of a worker that crashed. Status lines go to on_status."""
    read_fd, write_fd = os.pipe()
    env = dict(os.environ, PROOF_BATCH_STATUS=f"/dev/fd/{write_fd}")
    try:
        with base_log.open("xb") as output:
            process = subprocess.Popen(args, stdout=output, stderr=subprocess.STDOUT,
                                       start_new_session=True, pass_fds=(write_fd,), env=env)
    finally:
        os.close(write_fd)
    reader = threading.Thread(target=read_status, args=(read_fd, on_status), daemon=True)
    reader.start()
    try:
        return process.wait() == 0
    finally:
        with contextlib.suppress(ProcessLookupError):
            os.killpg(process.pid, signal.SIGKILL)
        process.wait()
        reader.join()


def run_batch(worker: Path, artifact_logs, jobs: int, base_log: Path) -> bool:
    """Publish each normally completed, error-free proof at its requested log.

    Supply fresh log paths. Failed proofs keep diagnostics under .partial.
    The worker's own output (startup, then failed-child status lines) goes
    to base_log. Standalone .native files share the concurrency limit with
    .cmxs plugins and are executed directly by a forked child. Prints one
    line per finished proof, then failures and the slowest proofs.
    """
    tasks = []
    for artifact, log in artifact_logs:
        log = log.resolve()
        log.parent.mkdir(parents=True, exist_ok=True)
        tasks.append((artifact.resolve(), log, log.with_name(log.name + ".partial"),
                      log.with_name(log.name + ".partial.exited")))
    by_partial = {str(task[2]): task for task in tasks}
    root = base_log.resolve().parent
    verdicts, reasons, seconds = {}, {}, {}
    width = len(str(len(tasks)))

    def on_status(status, elapsed, partial):
        if status == "ready":
            print(f"Initialized the shared base ({elapsed:.1f} s)", flush=True)
            return
        artifact, log, partial, exited = by_partial[partial]
        name = str(log.relative_to(root))
        seconds[name] = elapsed
        if status == "ok":
            verdicts[log] = valid_proof_log(exited, artifact.suffix == ".cmxs")
            if not verdicts[log]:
                reasons[log] = first_error(exited)
        else:
            verdicts[log] = False
            reasons[log] = f"{status}: {first_error(partial)}"
        word = "ok" if verdicts[log] else "FAILED"
        print(f"[{len(verdicts):>{width}}/{len(tasks)}] {word} {name} ({elapsed:.1f} s)"
              + ("" if verdicts[log] else f": {reasons[log]}"), flush=True)

    args = [worker.resolve(), str(time.time()), str(jobs)]
    for artifact, _, partial, _ in tasks:
        args.extend([artifact, partial])
    try:
        ok = run_worker(args, base_log, on_status)
        base_ok = scan_log(base_log) is not None
        failed = []
        for artifact, log, partial, exited in tasks:
            plugin = artifact.suffix == ".cmxs"
            if exited.exists() and (base_ok or not plugin) and verdicts.get(log):
                exited.rename(log)
            else:
                ok = False
                reason = reasons.get(log) or ("shared base failed" if not base_ok else "did not finish")
                failed.append(f"  {log.relative_to(root)}: {reason} (log {partial})")
        print_slowest("proofs", seconds)
        if failed:
            print(f"{len(failed)} of {len(tasks)} proofs failed:", *failed, sep="\n", flush=True)
        if not base_ok:
            print(f"The shared base reported an error, see {base_log}", flush=True)
        return ok and base_ok
    finally:
        # Also on interruption: leave every unpublished proof where the
        # diagnostics upload and the timing collector look for it.
        for _, _, partial, exited in tasks:
            if exited.exists():
                exited.rename(partial)
