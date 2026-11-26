"""Stress hol-d's process lifecycle and concurrency on Linux.

Run with `make -C tools/hol-d/tests HOLDIR=...`. Each group starts its own
daemon on a private socket. Survivors are found by scanning /proc for the
daemon's process groups and for helper commands whose environment holds
HOLD_STRESS=TAG. An environment marker works with any /bin/sh; dash, the
/bin/sh of Ubuntu, has no `exec -a` to rename a command.
"""

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import os
from pathlib import Path
import signal
import socket
import json
import subprocess
import sys
import tempfile
import time

HOLD = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HOLD))
from daemon import owned_server  # noqa: E402

HOLDIR = os.environ["HOLDIR"]
failures = []


def check(name, ok, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ("" if ok or not detail else f": {detail}"), flush=True)
    if not ok:
        failures.append(name)


def processes():
    found = {}
    for entry in Path("/proc").iterdir():
        if entry.name.isdigit():
            try:
                stat = (entry / "stat").read_text()
                command = (entry / "cmdline").read_bytes().replace(b"\0", b" ").decode(errors="replace")
            except OSError:
                continue
            fields = stat[stat.rindex(")") + 2:].split()
            found[int(entry.name)] = dict(state=fields[0], pgid=int(fields[2]), sid=int(fields[3]), cmd=command)
    return found


def live(predicate):
    return {pid for pid, info in processes().items() if info["state"] != "Z" and predicate(info)}


def helpers(tag):
    marker = f"HOLD_STRESS={tag}".encode()

    def marked(pid):
        try:
            return marker in Path(f"/proc/{pid}/environ").read_bytes().split(b"\0")
        except OSError:
            return False
    return {pid for pid, info in processes().items() if info["state"] != "Z" and marked(pid)}


def eventually(probe, seconds=60):
    """Wait for probe() to become true, for example on a slow CI runner."""
    deadline = time.monotonic() + seconds
    while not (result := probe()) and time.monotonic() < deadline:
        time.sleep(0.1)
    return result


def eventually_empty(probe, seconds=8):
    deadline = time.monotonic() + seconds
    while (left := probe()) and time.monotonic() < deadline:
        time.sleep(0.05)
    return left


def background(tag):
    return f'ignore (Sys.command "HOLD_STRESS={tag} sleep 600 &");;\n'


class Daemon:
    def __init__(self):
        self.directory = tempfile.mkdtemp()
        self.socket = f"{self.directory}/socket"
        self.cli("start")

    def command(self, *args):
        return [sys.executable, HOLD / "hol-d", "--socket", self.socket, *map(str, args)]

    def cli(self, *args, input=None, timeout=300):
        return subprocess.run(self.command(*args), input=input, capture_output=True, text=True,
                              timeout=timeout, cwd=self.directory)

    def ok(self, *args, input=None):
        result = self.cli(*args, input=input)
        if result.returncode:
            raise AssertionError(f"hol-d {' '.join(map(str, args))}: {result.stdout}{result.stderr}")
        return result.stdout

    def tree(self):
        # A child that is still being forked has no PID yet and shows None.
        fields = [line.split() for line in self.ok("tree").splitlines()]
        return {f[0]: None if f[1] == "None" else int(f[1]) for f in fields}

    def state(self, path):
        lines = [line.split() for line in self.ok("tree").splitlines()]
        return next((fields[2] for fields in lines if fields[0] == path), None)

    def server(self):
        return next(iter(live(lambda info: f"server.py {self.socket} " in info["cmd"])))

    def remnants(self, groups):
        return live(lambda info: info["pgid"] in groups or info["sid"] in groups)

    def stop(self):
        self.cli("stop")


def build_plugins(directory):
    sources = {
        "good": 'let () = print_endline "good ran";;\nlet () = at_exit (fun () -> print_endline "footer");;\n',
        "bad": 'let () = failwith "deliberate";;\n',
        "badexit": 'let () = at_exit (fun () -> failwith "exit handler");;\n',
        "early": 'let () = exit 0;;\n',
        "helper": 'let () = ignore (Sys.command "HOLD_STRESS=run sleep 600 &");;\n',
        "slow": 'let () = Unix.sleep 600;;\n',
        "worker": ('let () = match Unix.fork () with\n  | 0 -> Unix.sleep 30; exit 0\n'
                   '  | pid -> Unix.kill pid Sys.sigterm; ignore (Unix.waitpid [] pid);'
                   ' print_endline "worker ended";;\n'),
        "quick": 'let () = print_endline "hello";;\n',
    }
    for name, text in sources.items():
        (directory / f"{name}.ml").write_text(text)
        subprocess.run([f"{HOLDIR}/hol.sh", "compile", f"{name}.ml", "-open", "Hol_lib", "-I", "."],
                       cwd=directory, check=True, capture_output=True)
        subprocess.run(["ocamlfind", "ocamlopt", "-package", "unix", "-shared", f"{name}.cmx",
                        "-o", f"{name}.cmxs"], cwd=directory, check=True, capture_output=True)
    return {name: directory / f"{name}.cmxs" for name in sources}


def daemon_death():
    """SIGKILL of the daemon leaves no node, busy node or helper behind."""
    d = Daemon()
    for parent, name in [("/", "a"), ("/a", "b"), ("/a", "c"), ("/a/b", "d")]:
        d.ok("fork", parent, name)
    started = time.monotonic()
    d.ok("repl", "/a/b/d", input=background("d"))
    check("a background command does not hold a request open", time.monotonic() - started < 10)
    busy = subprocess.Popen(d.command("repl", "/a/c"), stdin=subprocess.PIPE, text=True,
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    busy.stdin.write(background("busy").replace(";;", "; Unix.sleep 600;;"))
    busy.stdin.flush()
    # The busy leaf first parses and compiles its phrase, which takes a few
    # seconds on a slow runner, before it starts its helper.
    check("helpers run before the kill", bool(eventually(lambda: helpers("d") and helpers("busy"))))
    tree = d.tree()
    check("each node leads its own process group",
          all(processes()[pid]["pgid"] == pid for pid in tree.values()))
    os.kill(d.server(), signal.SIGKILL)
    left = eventually_empty(lambda: d.remnants(set(tree.values())) | helpers("d") | helpers("busy"))
    check("SIGKILL of the daemon leaves nothing", not left, left)
    busy.kill()
    busy.wait()
    session = Path(d.socket + ".session")
    old = {entry.name for entry in session.glob("node-*")}
    d.ok("start")
    check("the next start replaces the killed daemon's session",
          bool(old) and not old & {entry.name for entry in session.glob("node-*")})
    d.stop()


def removal(plugins):
    """kill, kill --tree, outside SIGKILL, SIGKILL fallbacks and stop."""
    d = Daemon()
    for parent, name in [("/", "a"), ("/a", "b"), ("/a/b", "c"), ("/", "x"), ("/", "t"), ("/", "s")]:
        d.ok("fork", parent, name)
    d.ok("repl", "/a/b/c", input=background("mid"))
    d.ok("repl", "/x", input=background("leaf"))
    check("helpers start in a middle node's leaf and in /x",
          bool(eventually(lambda: helpers("mid") and helpers("leaf"))))
    tree = d.tree()
    os.kill(tree["/a"], signal.SIGKILL)
    left = eventually_empty(lambda: d.remnants({tree["/a"], tree["/a/b"], tree["/a/b/c"]}) | helpers("mid"))
    check("an outside SIGKILL of a middle node ends its subtree and helpers", not left, left)
    check("the supervisor drops the dead subtree", eventually(lambda: "/a" not in d.tree()))
    d.ok("kill", "/x")
    check("kill of a leaf ends its helpers", not eventually_empty(lambda: helpers("leaf")))
    d.ok("repl", "/t", input="Sys.set_signal Sys.sigterm (Sys.Signal_handle (fun _ -> ()));;\n")
    started = time.monotonic()
    d.ok("kill", "/t")
    check("kill falls back to SIGKILL for a node that ignores SIGTERM", time.monotonic() - started < 10)
    d.ok("repl", "/s", input=background("stopped"))
    check("a helper starts in /s", bool(eventually(lambda: helpers("stopped"))))
    os.killpg(d.tree()["/s"], signal.SIGSTOP)
    groups = set(d.tree().values())
    d.stop()
    left = eventually_empty(lambda: d.remnants(groups) | helpers("stopped"))
    check("stop ends a stopped leaf and its stopped helper", not left, left)


def runs(plugins):
    """run outcomes, interrupted runs and parallel runs."""
    d = Daemon()
    d.ok("fork", "/", "r")
    result = d.cli("run", "/r", plugins["good"])
    check("run reports success and captures exit-handler output",
          result.returncode == 0 and result.stdout.rstrip().endswith("footer"), result)
    for name in ("bad", "badexit", "early"):
        check(f"run of {name} fails", d.cli("run", "/r", plugins[name]).returncode != 0)
    started = time.monotonic()
    result = d.cli("run", "/r", plugins["helper"])
    check("run with a background helper returns promptly",
          result.returncode == 0 and time.monotonic() - started < 10, result)
    check("the run child's helper ends with it", not eventually_empty(lambda: helpers("run")))
    result = d.cli("run", "/r", plugins["worker"])
    check("a plugin can stop a worker it forked", "worker ended" in result.stdout, result)
    slow = subprocess.Popen(d.command("run", "/r", plugins["slow"]),
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    def run_children():
        return [path for path in d.tree() if path.startswith("/r/run-")]
    started = eventually(run_children)
    slow.send_signal(signal.SIGINT)
    slow.wait()
    check("interrupting run removes its child",
          bool(started) and eventually(lambda: not run_children()))
    for _ in range(5):
        with socket.socket(socket.AF_UNIX) as client:
            client.connect(d.socket)
            client.sendall(json.dumps({"cmd": "run", "path": "/", "plugin": str(plugins["quick"])}).encode() + b"\n")
            client.shutdown(socket.SHUT_WR)
            client.recv(4096)
    check("runs still work after clients disconnect mid-fork",
          all(d.cli("run", "/", plugins["quick"]).returncode == 0 for _ in range(3)))
    jobs = [subprocess.Popen(d.command("run", "/", plugins["quick"]), stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT) for _ in range(40)]
    outputs = [job.communicate()[0] for job in jobs]
    check("40 parallel runs succeed", all(j.returncode == 0 and b"hello" in o for j, o in zip(jobs, outputs)))
    d.stop()


def prompts():
    """Concurrent prompts in siblings, queued phrases, detaches and input edge cases."""
    d = Daemon()
    d.ok("fork", "/", "dec")
    d.ok("repl", "/dec", input="let dec n = n + 1;;\n")
    names = [f"s{i}" for i in range(48)]
    for name in names:
        d.ok("fork", "/dec", name)
    sessions = [subprocess.Popen(d.command("repl", f"/dec/{name}"), stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT) for name in names]
    outputs = [s.communicate(f"dec {i};;\n".encode())[0] for i, s in enumerate(sessions)]
    check("48 concurrent phrases in sibling leaves succeed",
          all(s.returncode == 0 and f"int = {i + 1}".encode() in o
              for i, (s, o) in enumerate(zip(sessions, outputs))))
    d.ok("fork", "/", "p")
    prompt = subprocess.Popen(d.command("repl", "/p"), stdin=subprocess.PIPE, text=True,
                              stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    prompt.stdin.write("Unix.sleep 3;; let z = 1;;\n")
    prompt.stdin.flush()
    eventually(lambda: d.state("/p") == "busy")
    forked = d.cli("fork", "/p", "q")
    check("fork reports busy while phrases are queued", forked.returncode != 0 and "busy" in forked.stderr)
    prompt.stdin.close()
    prompt.wait()
    d.ok("fork", "/", "dd")
    attached = subprocess.Popen(d.command("repl", "/dd"), stdin=subprocess.PIPE, text=True,
                                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    eventually(lambda: d.state("/dd") == "attached")
    d.ok("fork", "/dd", "child")
    _, error = attached.communicate("let late = 1;;\n")
    check("a fork detaches an attached prompt with an error",
          attached.returncode == 1 and "frozen by a fork" in error, error)
    d.ok("fork", "/", "u")
    result = subprocess.run(d.command("repl", "/u"), input=b'let s = "caf\xe9";;\nString.length s;;\n',
                            capture_output=True)
    check("prompt input that is not UTF-8 reaches OCaml as bytes", b"int = 4" in result.stdout, result)
    text = "let big = [\n" + "".join(f"  {i};\n" for i in range(5000)) + "  0];;\nList.length big;;\n"
    started = time.monotonic()
    result = d.cli("repl", "/u", input=text)
    check("a 5000-line phrase is read in linear time",
          "int = 5001" in result.stdout and time.monotonic() - started < 30, result.stderr)
    d.stop()


def startup():
    """Session directories and unexpected root death."""
    directory = Path(tempfile.mkdtemp())
    (directory / "socket.session").mkdir()
    (directory / "socket.session" / "keep").write_text("precious")
    result = subprocess.run([sys.executable, HOLD / "hol-d", "--socket", directory / "socket", "start"],
                            capture_output=True, text=True)
    check("start refuses to replace a directory hol-d did not create",
          result.returncode != 0 and (directory / "socket.session" / "keep").exists(), result)
    directory = Path(tempfile.mkdtemp())
    with open(directory / "log", "wb") as log, \
            owned_server(directory / "socket", directory, HOLD / "build", log) as server:
        tree = subprocess.run([sys.executable, HOLD / "hol-d", "--socket", directory / "socket", "tree"],
                              capture_output=True, text=True).stdout
        os.kill(int(tree.split()[1]), signal.SIGKILL)
        # Leaving the block closes the owner pipe, which would request a
        # stop. Wait for the supervisor to notice the root's death first.
        eventually(lambda: server.poll() is not None)
    check("the supervisor exits 1 after the root dies unexpectedly", server.returncode == 1, server.returncode)


def main():
    plugins = build_plugins(Path(tempfile.mkdtemp()))
    groups = [("daemon death", daemon_death), ("removal", lambda: removal(plugins)),
              ("runs", lambda: runs(plugins)), ("prompts", prompts), ("startup", startup)]
    for name, group in groups:
        try:
            group()
        except Exception as error:  # Report and continue with the next group.
            check(f"{name} group completes", False, repr(error))
    print(f"{'FAILED: ' + ', '.join(failures) if failures else 'all checks passed'}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
