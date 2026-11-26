"""Supervise forked native HOL processes. All tree mutations run on one event loop."""

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

import asyncio
import base64
import contextlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import uuid

from phrases import split_phrases


class SessionError(Exception):
    pass


# How long remove() waits after SIGTERM before it sends SIGKILL.
GRACE_SECONDS = 5


async def first(*awaitables):
    """Return the result of whichever awaitable finishes first."""
    tasks = [asyncio.ensure_future(a) for a in awaitables]
    try:
        done, _ = await asyncio.wait(tasks, return_when=asyncio.FIRST_COMPLETED)
        return next(iter(done)).result()
    finally:
        # Cancel the tasks made for coroutines, but leave given futures
        # pending: request() may still await its output connection.
        for task, awaitable in zip(tasks, awaitables):
            if task is not awaitable:
                task.cancel()


class Client:
    def __init__(self, writer):
        self.writer = writer

    async def send(self, **message):
        if not self.writer.is_closing():
            self.writer.write(json.dumps(message).encode() + b"\n")
            try:
                await self.writer.drain()
            except ConnectionError:
                self.writer.close()

    async def output(self, data):
        await self.send(output=base64.b64encode(data).decode("ascii"))


class Node:
    def __init__(self, path, parent):
        self.path = path
        self.parent = parent
        self.writer = None  # Control channel, once the node connects.
        self.replies = asyncio.Queue()
        self.reports = 0  # Control lines other than "reaped" so far.
        self.dead = asyncio.Event()
        self.reaped = asyncio.Event()
        self.exit_status = None
        self.children = {}
        self.forking = None  # The child of an F request in flight.
        self.pid = None
        self.pidfd = None
        self.frozen = parent is None
        self.busy = False
        self.client = None
        self.pending = ""
        self.interfaces = []
        self.killed = False  # Whether remove() signalled the node while it ran
        self.temp = None  # The node's private temporary directory

    def publish_interface(self, plugin, directory):
        # Adding plugin.parent would expose unrelated private modules and
        # their .cmx optimizations to the native toplevel compiler.
        view = Path(tempfile.mkdtemp(dir=directory))
        self.interfaces.append(view)
        shutil.copyfile(plugin.with_suffix(".cmi"), view / plugin.with_suffix(".cmi").name)
        native = plugin.with_suffix(".cmx")
        if native.is_file():
            shutil.copyfile(native, view / native.name)
        return os.fsencode(view) + b"\0" + os.fsencode(plugin)

    @property
    def state(self):
        if self.dead.is_set():
            return "exited"
        if self.busy or self.pending:
            return "busy"
        if self.frozen:
            return "frozen"
        return "attached" if self.client else "idle"

    def set_pid(self, pid):
        self.pid = pid
        with contextlib.suppress(AttributeError, OSError):
            # Some kernels and container filters refuse pidfd_open. Then
            # signal() falls back to the PID.
            self.pidfd = os.pidfd_open(pid)

    def signal(self, number=signal.SIGTERM):
        """By default, ask the node to end itself, its subtree and its commands."""
        # Without a pidfd, a reaped PID may already belong to another process.
        if self.pid is None or self.dead.is_set() or self.reaped.is_set():
            return
        with contextlib.suppress(ProcessLookupError):
            if self.pidfd is not None:
                signal.pidfd_send_signal(self.pidfd, number)
            else:
                os.kill(self.pid, number)

    def send(self, tag, token, payload=b""):
        self.writer.write(f"{tag} {token} {len(payload)}\n".encode() + payload)

    def exited(self):
        if self.killed:
            # remove() signalled the live node: kill, stop or the loss of
            # its parent, rather than a failure of the node itself.
            return SessionError(f"{self.path} was killed (hol-d kill, stop or loss of its parent)")
        return SessionError(f"{self.path} exited")

    async def reply(self):
        if self.replies.empty() and self.dead.is_set():
            raise self.exited()
        value = await self.replies.get()
        if value is None:
            raise self.exited()
        return value


class Supervisor:
    def __init__(self, directory):
        self.directory = directory
        self.address = str(Path(directory) / "nodes")
        self.expected = {}  # token -> (kind, future of the node's connection)
        self.root = Node("/", None)
        self.nodes = {"/": self.root}
        self.lock = asyncio.Lock()
        self.tasks = set()
        self.stopped = asyncio.Event()
        self.stopping = False  # Removing the root was requested.
        self.failed = False  # The root ended without such a request.
        self.process = None

    def spawn(self, coroutine):
        # asyncio keeps only weak task references.
        task = asyncio.ensure_future(coroutine)
        self.tasks.add(task)
        task.add_done_callback(self.tasks.discard)

    def expect(self, kind):
        token = uuid.uuid4().hex
        future = asyncio.get_running_loop().create_future()
        self.expected[token] = (kind, future)
        return token, future

    async def accept(self, listener):
        # Each node connects once for control ("n") and once per request
        # for its output ("o"), naming a token the supervisor chose.
        loop = asyncio.get_running_loop()
        while True:
            connection, _ = await loop.sock_accept(listener)
            self.spawn(self.introduce(connection))

    async def introduce(self, connection):
        loop = asyncio.get_running_loop()
        greeting = b""
        with contextlib.suppress(OSError):
            while len(greeting) < 34 and (data := await loop.sock_recv(connection, 34 - len(greeting))):
                greeting += data
        kind, future = self.expected.pop(greeting[1:33].decode(errors="replace"), (None, None))
        if future is None or greeting[:1].decode() != kind:
            connection.close()
        else:
            future.set_result(connection)

    async def attach(self, node, connection):
        reader, node.writer = await asyncio.open_connection(sock=connection)
        self.spawn(self.monitor(node, reader))

    async def monitor(self, node, reader):
        try:
            while line := await reader.readline():
                message = line.decode().rstrip("\n")
                if message.startswith("reaped "):
                    _, pid, status = message.split()
                    for child in node.children.values():
                        if child.pid == int(pid):
                            child.exit_status = int(status)
                            child.reaped.set()
                            if child.writer is None:  # Died before connecting.
                                child.dead.set()
                                child.replies.put_nowait(None)
                else:
                    node.reports += 1
                    if message.startswith("ready ") and len(message.split()) == 3:
                        node.temp = message.split()[2]
                    if message.startswith("forked ") and node.forking:
                        # Record the PID before handling a "reaped" line
                        # buffered behind this one.
                        node.forking.set_pid(int(message.split()[1]))
                    node.replies.put_nowait(message)
        except (OSError, ValueError) as error:
            print(f"hol-d: {node.path} control channel failed: {error}", file=sys.stderr, flush=True)
        finally:
            node.writer.close()  # A node that is still running sees EOF and ends.
            node.dead.set()
            node.replies.put_nowait(None)
            if node is self.root and not self.stopping:
                # A batch must not trust results after an unexplained end.
                print("hol-d: the HOL root exited unexpectedly", file=sys.stderr, flush=True)
                self.failed = True
            async with self.lock:
                if self.nodes.get(node.path) is node:
                    await self.remove(node)

    async def start(self, host):
        token, connected = self.expect("n")
        # The root leads its own session. Each node it forks leads its own.
        self.process = subprocess.Popen([host, token], stdin=subprocess.DEVNULL,
                                        env=dict(os.environ, TMPDIR=self.directory, HOL_D_NODES=self.address),
                                        start_new_session=True)
        self.root.set_pid(self.process.pid)
        exited = asyncio.to_thread(self.process.wait)
        connection = await first(connected, exited)
        if not isinstance(connection, socket.socket):
            raise SessionError("HOL initialization failed")
        await self.attach(self.root, connection)
        if (await self.root.reply()).split()[:2] != ["ready", str(self.process.pid)]:
            raise SessionError("HOL initialization failed")
        if self.root.pidfd is None:
            print("hol-d: pidfd_open unavailable, signalling process IDs", file=sys.stderr, flush=True)

    def find(self, path):
        if path not in self.nodes:
            raise SessionError(f"unknown session {path}")
        return self.nodes[path]

    async def fork(self, parent, name):
        if not re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_.-]*", name):
            raise SessionError("name must be one path component starting with a letter, digit or _")
        async with self.lock:
            if self.nodes.get(parent.path) is not parent or parent.dead.is_set():
                raise SessionError("parent exited")
            if parent.busy or parent.pending:
                raise SessionError(f"{parent.path} is busy")
            path = parent.path.rstrip("/") + "/" + name
            if path in self.nodes:
                raise SessionError(f"{path} already exists")
            child = Node(path, parent)
            child.busy = True
            parent.children[path] = self.nodes[path] = child
            parent.busy = True
            parent.forking = child
            token, connected = self.expect("n")
            try:
                parent.send("F", token)
                # Consume the reply even if the client disconnects, so a
                # later fork cannot read this one's stale "forked" line.
                reply = await asyncio.shield(parent.reply())
                if not reply.startswith("forked "):
                    raise SessionError(reply)
                parent.frozen = True
                self.detach(parent, frozen=True)
                connection = await first(connected, child.dead.wait(), parent.dead.wait())
                if not isinstance(connection, socket.socket):
                    raise SessionError("child exited before connecting")
                await self.attach(child, connection)
                if (await child.reply()).split()[:2] != ["ready", str(child.pid)]:
                    raise SessionError("child did not become ready")
                child.busy = False
                return child
            except BaseException:
                await self.remove(child)
                raise
            finally:
                self.expected.pop(token, None)
                parent.forking = None
                parent.busy = False

    @staticmethod
    def detach(node, frozen=False):
        if node.client:
            # Tell a script that input after this point was not evaluated.
            reason = "was frozen by a fork; prompt detached" if frozen else "exited"
            message = {"error": f"{node.path} {reason}"}
            node.client.writer.write(json.dumps(message).encode() + b"\n")
            node.client.writer.close()
            node.client = None
        node.pending = ""

    async def remove(self, node):
        # Caller holds the lock, so no fork is in flight. Each node ends its
        # own subtree on SIGTERM. Signal every live node anyway in case a
        # parent died without doing so.
        subtree, pending = [], [node]
        while pending:
            subtree.append(pending.pop())
            pending.extend(subtree[-1].children.values())
        for each in subtree:
            if each.pid is not None and not each.dead.is_set():
                each.killed = True
            each.signal()
        for each in subtree:
            if each.writer is not None:
                try:
                    # Control EOF: the process has exited.
                    await asyncio.wait_for(each.dead.wait(), GRACE_SECONDS)
                except asyncio.TimeoutError:
                    # Stuck in a long C call, or a phrase replaced the SIGTERM
                    # handler. Kill its whole group: its parent may be gone, and
                    # the live node still reserves the group ID.
                    if not each.reaped.is_set():
                        with contextlib.suppress(ProcessLookupError):
                            os.killpg(each.pid, signal.SIGKILL)
                    each.signal(signal.SIGKILL)
                    await each.dead.wait()
            if each.parent is not None and each.pid is not None:
                # Keep the node until its parent reports the exit status,
                # which a one-shot run needs, or the parent ends as well.
                await first(each.reaped.wait(), each.parent.dead.wait())
        if node is self.root:
            await asyncio.to_thread(self.process.wait)
        for each in reversed(subtree):
            self.detach(each)
            for directory in each.interfaces:
                shutil.rmtree(directory)
            if each.temp and re.fullmatch(r"node-[0-9]+-[0-9a-f]+", each.temp):
                shutil.rmtree(Path(self.directory) / each.temp, ignore_errors=True)
            if each.pidfd is not None:
                os.close(each.pidfd)
            self.nodes.pop(each.path, None)
            if each.parent:
                each.parent.children.pop(each.path, None)
        if node is self.root:
            self.stopped.set()

    async def request(self, node, tag, payload, client):
        """Run one command in node and stream its output to client."""
        loop = asyncio.get_running_loop()
        token, connected = self.expect("o")
        owner = not node.busy  # repl holds busy across a chunk of phrases.
        node.busy = True
        output = None
        try:
            reports = node.reports
            node.send(tag, token, payload)
            output = await first(connected, node.dead.wait())
            if not isinstance(output, socket.socket):
                output = None
                # A short-lived child can exit before its output connection
                # is accepted. It reports only after connecting, so a report
                # means the connection is still waiting to be introduced.
                if node.reports == reports:
                    raise SessionError(f"{node.path} exited")
                output = await connected
            output.setblocking(False)

            async def pump():
                while data := await loop.sock_recv(output, 16384):
                    await client.output(data)

            # A command started in the background, such as "cmd &", can
            # inherit the output socket and keep it open. End the request
            # at the node's report instead of at EOF. A one-shot child then
            # exits, and its parent reports the status.
            streaming = asyncio.ensure_future(pump())
            try:
                reply = await node.reply()
                if tag == "R" and reply == "ok":
                    # The child's own EOF can come first. Its parent reports
                    # the exit status, unless the parent died as well.
                    await first(node.reaped.wait(), node.parent.dead.wait())
                    reply = "ok" if node.exit_status == 0 else f"exit status {node.exit_status}"
            finally:
                streaming.cancel()
                with contextlib.suppress(asyncio.CancelledError):
                    await streaming
                with contextlib.suppress(BlockingIOError, OSError):
                    while data := output.recv(16384):
                        await client.output(data)
            if reply != "ok":
                raise SessionError({"E": "phrase failed", "R": f"plugin failed ({reply})"}
                                   .get(tag, "load failed; leaf discarded"))
        finally:
            self.expected.pop(token, None)
            if output is not None:
                output.close()
            if owner:
                node.busy = False

    async def run_plugin(self, parent, plugin, client):
        child = await self.fork(parent, "run-" + uuid.uuid4().hex)
        try:
            # Success means the initializer returned and the child then
            # exited with status 0, after its exit handlers.
            await self.request(child, "R", os.fsencode(plugin), client)
        finally:
            async with self.lock:
                if self.nodes.get(child.path) is child:
                    await self.remove(child)

    async def repl(self, node, reader, client):
        node.client = client
        failed = False
        try:
            await client.send(prompt=True)
            while node.client is client and (line := await reader.readline()):
                text = json.loads(line)["line"]
                if node.busy or node.frozen:
                    raise SessionError(f"{node.path} is {node.state}")
                if node.pending and ";;" not in text and "*)" not in text:
                    # Text without either cannot end a phrase or a comment.
                    # Skip rescanning a long unfinished phrase on each line.
                    node.pending += text
                    continue
                phrases, node.pending = split_phrases(node.pending + text)
                # A diagnostic send can yield to the event loop. Stay busy
                # between phrases so that a fork cannot freeze this node
                # while later phrases of the same input are still queued.
                node.busy = True
                try:
                    for phrase in phrases:
                        try:
                            # The CLI passes undecodable input bytes as
                            # surrogates. Hand OCaml the original bytes.
                            await self.request(node, "E", phrase.encode(errors="surrogateescape"), client)
                        except SessionError as error:
                            if node.dead.is_set():
                                raise
                            failed = True
                            await client.send(diagnostic=str(error))
                finally:
                    node.busy = False
                if not node.pending:
                    await client.send(prompt=True)
            if node.pending:
                raise SessionError("incomplete phrase")
            if failed:
                raise SessionError("one or more phrases failed")
        finally:
            if node.client is client:
                node.client = None
                node.pending = ""

    @staticmethod
    async def until_disconnect(reader, work):
        """Cancel work, and thereby discard its child, if the client leaves.

        After its request the client sends nothing, so any read completes
        only at EOF, for example after Ctrl-C."""
        task = asyncio.ensure_future(work)
        gone = asyncio.ensure_future(reader.read())
        try:
            await asyncio.wait({task, gone}, return_when=asyncio.FIRST_COMPLETED)
            if not task.done():
                task.cancel()
                with contextlib.suppress(asyncio.CancelledError):
                    await task
                raise SessionError("client disconnected")
            return task.result()
        finally:
            gone.cancel()
            if not task.done():
                task.cancel()

    async def handle(self, reader, writer):
        client = Client(writer)
        try:
            request = json.loads(await reader.readline())
            cmd = request["cmd"]
            node = self.find(request.get("path", "/"))
            if cmd in ("run", "load"):
                plugin = Path(request["plugin"])
                if plugin.suffix != ".cmxs" or not plugin.is_file():
                    raise SessionError(f"expected a native plugin: {plugin}")
            if cmd == "tree":
                text = "".join(f"{n.path} {n.pid} {n.state}\n" for _, n in sorted(self.nodes.items()))
                await client.output(text.encode())
            elif cmd == "fork":
                child = await self.fork(node, request["name"])
                await client.output(f"{child.path} {child.pid}\n".encode())
            elif cmd == "run":
                await self.until_disconnect(reader, self.run_plugin(node, plugin, client))
            elif cmd in ("kill", "stop"):
                async with self.lock:
                    node = self.find(node.path)
                    if cmd == "kill" and not request["tree"] and (node.children or node is self.root):
                        raise SessionError("use kill --tree to remove a parent or /")
                    self.stopping |= node is self.root
                    await self.remove(node)
            elif cmd in ("load", "repl"):
                if node.state != "idle":
                    hint = "; fork a child to work in" if node.frozen else ""
                    raise SessionError(f"{node.path} is {node.state}{hint}")
                if cmd == "load":
                    public = request["public"]
                    if public and not plugin.with_suffix(".cmi").is_file():
                        raise SessionError(f"public load requires {plugin.with_suffix('.cmi')}")
                    payload = node.publish_interface(plugin, self.directory) if public else os.fsencode(plugin)
                    try:
                        await self.request(node, "P" if public else "L", payload, client)
                    except (SessionError, OSError):
                        node.busy = True  # The node ends itself after a failed load.
                        async with self.lock:
                            if self.nodes.get(node.path) is node:
                                await self.remove(node)
                        raise
                else:
                    await self.repl(node, reader, client)
            elif cmd != "start":
                raise SessionError("unknown command")
            await client.send(done=True)
        except (SessionError, ValueError, KeyError, TypeError, OSError) as error:
            await client.send(error=str(error))
        finally:
            writer.close()


async def serve(path, startup, directory, host, owner_fd):
    supervisor = Supervisor(directory)
    loop = asyncio.get_running_loop()
    listener = socket.socket(socket.AF_UNIX)
    listener.bind(supervisor.address)
    listener.listen(64)
    listener.setblocking(False)
    supervisor.spawn(supervisor.accept(listener))
    starting = asyncio.create_task(supervisor.start(host))

    def stop():
        supervisor.stopping = True
        supervisor.stopped.set()
        starting.cancel()  # The root may still be initializing.

    for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        loop.add_signal_handler(sig, stop)
    if owner_fd is not None:
        def owner_exited():
            loop.remove_reader(owner_fd)
            stop()
        loop.add_reader(owner_fd, owner_exited)
    try:
        try:
            await starting
        except asyncio.CancelledError:
            if supervisor.stopped.is_set():
                return
            raise
        server = await asyncio.start_unix_server(supervisor.handle, path, limit=2 ** 21)
        os.chmod(path, 0o600)
        try:
            startup.write(b"ready\n")
            startup.close()
            await supervisor.stopped.wait()
            supervisor.stopping = True
            async with supervisor.lock:
                if "/" in supervisor.nodes:
                    await supervisor.remove(supervisor.root)
        finally:
            # Unlike leaving "async with server", close() does not wait for
            # clients that are still connected.
            server.close()
            Path(path).unlink(missing_ok=True)
    finally:
        # Normally remove() has already ended every node. Otherwise the root
        # ends the tree on SIGTERM, and idle nodes also end at control EOF.
        if supervisor.process and supervisor.process.poll() is None:
            supervisor.process.terminate()
            supervisor.process.wait()
    return supervisor.failed


if __name__ == "__main__":
    # Keep node sockets and temporary files next to the daemon's socket. Only
    # one daemon starts per socket, so this also clears a killed daemon's,
    # but never a directory that hol-d did not create.
    directory = sys.argv[1] + ".session"
    marker = os.path.join(directory, ".hol-d-session")
    if os.path.lexists(directory):
        if os.path.islink(directory) or not os.path.isfile(marker):
            sys.exit(f"hol-d: {directory} exists and was not created by hol-d")
        shutil.rmtree(directory)
    os.mkdir(directory, 0o700)
    open(marker, "x").close()
    try:
        owner = int(sys.argv[4]) if len(sys.argv) > 4 else None
        failed = asyncio.run(serve(sys.argv[1], os.fdopen(int(sys.argv[2]), "wb"), directory, sys.argv[3], owner))
    finally:
        shutil.rmtree(directory, ignore_errors=True)
    sys.exit(1 if failed else 0)
