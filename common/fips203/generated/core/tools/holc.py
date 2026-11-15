#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
"""Send one command to a HOL Light server (monadius/hol_server, server2.ml).

Usage:
  holc.py -p PORT 'g `1 + 1 = 2`;;'
  holc.py -p PORT -f some_file.ml      # send the whole file as one command
  echo 'e ARITH_TAC;;' | holc.py -p PORT
  holc.py -p PORT --interrupt           # interrupt the running command

The command text is sent as one line (escaped as server2.ml expects), so a
file with many phrases is evaluated in one go. To evaluate a file phrase by
phrase with HOL's own loader, send `loadt "path/relative/to/repo/root.ml";;`
instead.

Output: the server's stdout and stderr, then `RESULT: ...` or `ERROR: ...`.
Exit status: 0 on success, 1 on an OCaml/HOL error, 2 on timeout (after the
command was interrupted), 3 if the server cannot be reached.
"""

import argparse
import socket
import sys
import time


def ocaml_escape(s):
    out = []
    for ch in s:
        o = ord(ch)
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\t":
            out.append("\\t")
        elif ch == "\r":
            out.append("\\r")
        elif o < 32 or o == 127:
            out.append("\\%03d" % o)
        else:
            out.append(ch)
    return "".join(out)


def ocaml_unescape(s):
    # Inverse of OCaml's String.escaped.
    out = bytearray()
    b = s.encode("latin-1", errors="replace")
    i = 0
    n = len(b)
    simple = {ord("n"): 10, ord("t"): 9, ord("r"): 13, ord("b"): 8,
              ord("\\"): 92, ord('"'): 34, ord("'"): 39, ord(" "): 32}
    while i < n:
        c = b[i]
        if c == 92 and i + 1 < n:
            d = b[i + 1]
            if d in simple:
                out.append(simple[d])
                i += 2
                continue
            if 48 <= d <= 57 and i + 3 < n + 1:
                try:
                    out.append(int(b[i + 1:i + 4].decode()) & 255)
                    i += 4
                    continue
                except ValueError:
                    pass
            if d == ord("x") and i + 3 < n + 1:
                try:
                    out.append(int(b[i + 2:i + 4].decode(), 16))
                    i += 4
                    continue
                except ValueError:
                    pass
        out.append(c)
        i += 1
    return out.decode("utf-8", errors="replace")


def clip(text, limit):
    if limit <= 0 or len(text) <= limit:
        return text
    half = limit // 2
    return (text[:half] + "\n... [%d characters omitted] ...\n" %
            (len(text) - 2 * half) + text[-half:])


class Conn:
    def __init__(self, port, host="127.0.0.1", connect_timeout=10.0):
        self.sock = socket.create_connection((host, port), timeout=connect_timeout)
        self.sock.settimeout(None)
        self.buf = b""

    def readline(self, deadline=None):
        while b"\n" not in self.buf:
            if deadline is not None:
                left = deadline - time.time()
                if left <= 0:
                    raise TimeoutError
                self.sock.settimeout(left)
            else:
                self.sock.settimeout(None)
            try:
                chunk = self.sock.recv(1 << 20)
            except socket.timeout:
                raise TimeoutError
            if not chunk:
                raise EOFError("server closed the connection")
            self.buf += chunk
        line, self.buf = self.buf.split(b"\n", 1)
        return line.decode("latin-1")

    def send(self, text):
        self.sock.sendall((text + "\n").encode("utf-8"))

    def wait_ready(self, deadline=None):
        while True:
            line = self.readline(deadline)
            if line.startswith("ready:"):
                return


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("-p", "--port", type=int, required=True)
    ap.add_argument("-f", "--file", help="send the contents of this file")
    ap.add_argument("-t", "--timeout", type=float, default=600.0,
                    help="seconds before the command is interrupted (default 600)")
    ap.add_argument("-m", "--max-output", type=int, default=30000,
                    help="clip stdout/result to this many characters (0: no limit)")
    ap.add_argument("--interrupt", action="store_true",
                    help="only send $interrupt to the server")
    ap.add_argument("command", nargs="?", help="command text (default: stdin)")
    args = ap.parse_args()

    try:
        conn = Conn(args.port)
    except OSError as e:
        print("holc: cannot connect to port %d: %s" % (args.port, e), file=sys.stderr)
        return 3

    if args.interrupt:
        conn.send("$interrupt")
        return 0

    if args.file:
        with open(args.file) as fh:
            text = fh.read()
    elif args.command is not None:
        text = args.command
    else:
        text = sys.stdin.read()
    text = text.strip()
    if not text:
        print("holc: empty command", file=sys.stderr)
        return 1

    # Another client may be connected; the forkless server then queues us
    # until it disconnects, so allow a generous wait for the first prompt.
    try:
        conn.wait_ready(deadline=time.time() + max(args.timeout, 60.0))
    except (TimeoutError, EOFError) as e:
        print("holc: server on port %d never became ready (%s)" %
              (args.port, type(e).__name__), file=sys.stderr)
        return 3

    conn.send(ocaml_escape(text))
    deadline = time.time() + args.timeout
    stdout_parts, stderr_parts = [], []
    result, ok, timed_out = None, None, False
    while result is None:
        try:
            line = conn.readline(None if timed_out else deadline)
        except TimeoutError:
            timed_out = True
            conn.send("$interrupt")
            deadline = None
            continue
        except EOFError as e:
            print("holc: %s" % e, file=sys.stderr)
            return 3
        tag, _, payload = line.partition(":")
        payload = ocaml_unescape(payload)
        if tag == "stdout":
            stdout_parts.append(payload)
        elif tag == "stderr":
            stderr_parts.append(payload)
        elif tag == "result":
            result, ok = payload, True
        elif tag == "rerror":
            result, ok = payload, False
    try:
        conn.send("#quit")
    except OSError:
        pass

    out = "".join(stdout_parts).strip("\n")
    err = "".join(stderr_parts).strip("\n")
    if out:
        print(clip(out, args.max_output))
    if err:
        print(clip(err, args.max_output), file=sys.stderr)
    if timed_out:
        print("TIMEOUT: interrupted after %.0f s" % args.timeout)
        return 2
    print(("RESULT: " if ok else "ERROR: ") + clip(result.strip(), args.max_output))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
