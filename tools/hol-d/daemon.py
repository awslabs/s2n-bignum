"""Start a native HOL supervisor and wait for its root to become ready."""

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

from contextlib import contextmanager
import os
from pathlib import Path
import selectors
import subprocess
import sys


def start_server(path, cwd, build, log, pass_fds=(), owner_fd=None):
    """Caller owns the private socket directory and the returned process."""
    build = build.resolve()
    if not all((build / name).is_file() for name in ("node.native", "holdir")):
        raise ValueError("build hol-d by running make HOLDIR=... in its source directory")
    holdir = (build / "holdir").read_text().strip()
    pp = subprocess.check_output([Path(holdir) / "hol.sh", "-pp"], text=True).strip()
    env = dict(os.environ, HOLLIGHT_DIR=holdir, HOL_D_PP=pp, HOLLIGHT_USE_MODULE="1")
    read_fd, write_fd = os.pipe()
    with os.fdopen(read_fd, "rb") as status, os.fdopen(write_fd, "wb") as ready:
        command = [sys.executable, Path(__file__).with_name("server.py"), path, str(write_fd),
                   build / "node.native"]
        if owner_fd is not None:
            command.append(str(owner_fd))
            pass_fds = (*pass_fds, owner_fd)
        process = subprocess.Popen(
            command, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
            stdout=log, stderr=subprocess.STDOUT, pass_fds=(*pass_fds, write_fd),
            start_new_session=True, umask=0o077)
        ready.close()
        try:
            with selectors.DefaultSelector() as selector:
                selector.register(status, selectors.EVENT_READ)
                while not selector.select(60):
                    size = os.fstat(log.fileno()).st_size
                    print(f"hol-d: waiting for HOL root ({size} bytes in {log.name})",
                          file=sys.stderr, flush=True)
            if status.readline() != b"ready\n":
                raise ValueError(f"daemon initialization failed; see {log.name}")
            return process
        except BaseException:
            process.terminate()
            process.wait()
            raise


@contextmanager
def owned_server(path, cwd, build, log):
    """End the session on scope exit or if its owner dies, including SIGKILL."""
    read_fd, write_fd = os.pipe()
    with os.fdopen(read_fd, "rb") as reader, os.fdopen(write_fd, "wb") as owner:
        process = start_server(path, cwd, build, log, owner_fd=reader.fileno())
        reader.close()
        try:
            yield process
        finally:
            owner.close()
            process.wait()
