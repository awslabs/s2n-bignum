# Forkable HOL Light sessions

`hol-d` is a daemon managing multiple HOL Light processes. Processes are
organized in a tree and can be forked, amended, and be either interactive
(REPL) or batch builds. This allows you to organize large batch builds
efficiently, as well as manage multiple threads of interactive proof
exploration with maximal sharing and minimal context reloading.

`hol-d` is independent of s2n-bignum. Any HOL Light project can use it
with its own sources and native modules.

## Usage

### Run a batch from a shared theory

Assume you have a precompiled OCaml module, `base.cmxs`, that defines
`twice n = n + n` on natural numbers. The `.cmxs` extension identifies a
native plugin that a running OCaml process can load. Two more plugins,
`zero.cmxs` and `one.cmxs`, prove `twice 0 = 0` and `twice 1 = 2`.
The **Build and load native modules** section below shows how to build
all three. With `hol-d` on your `PATH`, run these commands from the
directory containing the plugins.

```sh
# Start the daemon and wait for the root HOL session (/) to be ready.
hol-d start

# Fork a child named /arithmetic from the root.
hol-d fork / arithmetic

# Load the base once. Future children of /arithmetic can use its definitions.
hol-d load --public /arithmetic base.cmxs

# Run each proof in its own child. xargs runs both in parallel and waits for them.
printf '%s\n' zero.cmxs one.cmxs | xargs -n 1 -P 2 hol-d run /arithmetic
```

Each proof plugin prints its theorem. `hol-d run` streams that output
and returns a failure status if the proof fails. `/arithmetic` stays
available after both children exit.

### Explore an open goal from a batch-built base

Fork the same `/arithmetic` session and attach to its new child.

```sh
hol-d fork /arithmetic scratch
hol-d repl /arithmetic/scratch
```

At the prompt, open the compiled base and set a goal.

```ocaml
open Base;;
g `!n. twice n = 2 * n`;;
```

In another terminal, fork twice from that open goal. One child uses the
library theorem `MULT_2`. The other uses an arithmetic tactic. Both
`top_thm()` calls print `|- forall n. twice n = 2 * n`.

```sh
hol-d fork /arithmetic/scratch rewrite
hol-d fork /arithmetic/scratch tactic
printf '%s\n' 'e (REWRITE_TAC[twice; MULT_2]);;' 'top_thm();;' |
    hol-d repl /arithmetic/scratch/rewrite
printf '%s\n' 'e (REWRITE_TAC[twice] THEN ARITH_TAC);;' 'top_thm();;' |
    hol-d repl /arithmetic/scratch/tactic
hol-d tree
```

The first fork freezes `scratch` and detaches its prompt. Fork it again
to try another tactic from the original goal. `hol-d kill --tree /arithmetic`
removes the example's sessions. `hol-d stop` shuts down the whole daemon.

## Build and start

Use a native HOL Light checkout built with `HOLLIGHT_USE_MODULE=1` and its OCaml switch.
Set `HOLDIR` to that checkout. If it has a local switch, activate it with
`eval "$(opam env --switch "$HOLDIR" --set-switch)"` before building and
starting the daemon. The native prompt invokes this toolchain to evaluate
phrases. The supervisor and CLI use Python 3.9 or newer on Unix.

```sh
# Build in the directory containing this README.
make
export PATH="$PWD:$PATH"
```

From the directory your HOL sources use for relative paths, start the daemon.

```sh
hol-d start
```

`start` prints `Starting server ...` immediately and `OK` with the elapsed
time once HOL is ready. It then returns to the shell. A second `start`
on that socket reports `Server already running ... OK` and returns.
`hol-d tree` lists the running sessions and reports when no daemon is running.

## Working at the prompt

The first successful fork freezes the parent and detaches its prompt, which
then exits with a failure status. A frozen
parent can produce more children even after all its earlier children exit.
The root starts frozen. Each leaf accepts one prompt or plugin load at a time.
A fork during evaluation, while later phrases of the same input wait, or
during an unfinished multiline phrase reports `busy`. A `;;` inside an open
`struct` or `sig` continues the phrase. Anywhere else, including an
unclosed `begin`, it ends the phrase and OCaml reports any syntax error.
End a prompt with EOF (Ctrl-D) and use `repl` to reattach. Disconnecting
discards unfinished input. A submitted phrase runs to completion unless the
node is killed. Piped input returns a failure status if any phrase failed.
A command that a phrase starts in the background, such as
`Sys.command "cmd &"`, does not delay the prompt. It ends with its node, or
earlier if it writes output after its phrase has returned.

The prompt opens `Hol_lib` and `Hol_loader`, installs HOL goal and theorem
printers, and supports `needs` and `loadt` for HOL source. The HOL
preprocessor prints `* HOL-Light syntax in effect *` before each result.
End phrases with
`;;`. The native loader skips HOL's bytecode-only `update_database.ml`
theorem-search index. Interactive OCaml `#` directives and terminal input
from inside tactics are outside the prompt protocol. Each phrase starts with
HOL's default lexer settings: a switch such as `unset_jrh_lexer;;` typed at
the prompt does not carry over to the next phrase, while switches inside a
file loaded with `loadt` apply to the rest of that file. Keep forkable code
single-domain and single-threaded. Native plugins and HOL phrases execute
with your account's permissions.

## Build and load native modules

The HOL Light toolchain compiles your `.ml` files and OCaml links them
into `.cmxs` plugins. `hol-d` loads those finished plugins. To build the
three modules used above, run the following in an empty directory with
the same OCaml switch used to build the daemon.

```sh
cat > base.ml <<'ML'
let twice = new_definition `twice (n:num) = n + n`;;
ML
cat > zero.ml <<'ML'
let twice_zero = prove (`twice 0 = 0`, REWRITE_TAC[Base.twice; ADD_CLAUSES]);;
let () = print_thm twice_zero; print_newline ();;
ML
cat > one.ml <<'ML'
let twice_one = prove (`twice 1 = 2`, REWRITE_TAC[Base.twice] THEN ARITH_TAC);;
let () = print_thm twice_one; print_newline ();;
ML

(
    set -e
    for name in base zero one; do
        "$HOLDIR/hol.sh" compile "$name.ml" -open Hol_lib -I .
        ocamlopt -shared "$name.cmx" -o "$name.cmxs"
    done
)
```

Build `base` first so the proof compiler can read `base.cmi`. To use
`Base.twice` at the prompt, load `base.cmxs` with `--public`, even when
you started the daemon in the build directory. A public load copies the
neighboring `.cmi` and optional `.cmx` into a branch-specific interface
directory that forked children inherit. A private load also runs the
initializer. The leaf and its future children inherit the resulting HOL
state, while the OCaml module name stays hidden. Any failed load, including
a second public load of the same module, discards its leaf.

To try source directly, fork a fresh leaf, attach with `hol-d repl`, and
enter `loadt "base.ml";;`. This uses HOL's source loader.

### Compile proofs with shared imports

A project can supply a JSON manifest that maps root names to trees of
HOL imports. Each layer's `source` is a literal path as it appears in a
HOL `needs` call. Each key under `children` adds one component to the
session path, and its layer loads after its parent's. For example, a
project might write `theories.json` as follows.

```json
{
  "arithmetic": {
    "source": "lib/numbers.ml",
    "children": {"parity": {"source": "lib/parity.ml"}}
  }
}
```

With the directory containing `hol-d` on `PYTHONPATH`, run the following
Python from the project's HOL working directory. Suppose `even.ml` and
`odd.ml` each begin with `needs "lib/numbers.ml";;` followed by
`needs "lib/parity.ml";;` on the next line.

```python
import os
from pathlib import Path
from holbuild import build_modules

out = Path("modules")
out.mkdir()
plan = build_modules("theories.json", "arithmetic", ["even.ml", "odd.ml"],
                     out, os.environ["HOLDIR"], jobs=2)
plan.write(out / "plan.json")
```

The compiler compares each proof's inlined imports with the selected
root and its descendants. It builds the selected root, children shared
by at least two proofs, and any sessions explicitly requested through
`sessions` (for example, `sessions=["/arithmetic/parity"]`). Here both
proofs can run under `/arithmetic/parity`. A proof with executable code
before its first matching import runs under `/`. The plan lists the
public plugins in load order and the parent to pass to `hol-d run` for
each proof. [Layer compiler](holbuild.py)

## Socket selection and lifetime

The socket selects the daemon. You can reconnect from any directory.
A new daemon inherits the directory where it was started. Relative paths
in HOL code follow the ordinary working directory and HOL loader rules.
The CLI resolves plugin paths supplied to `load` and `run` from the
calling shell. `--start-if-needed` starts a missing daemon for any command.

The default socket is `$XDG_RUNTIME_DIR/hol-d/socket`, with
`/tmp/hol-d-<uid>/socket` as the fallback. To start a separate daemon,
choose a socket in a directory you own with mode `0700`. Supply the same
path on later commands. The socket has mode `0600`. Next to it,
`PATH.lock` serializes startup, `PATH.log` contains startup diagnostics,
and `PATH.session` holds the daemon's temporary files. The next `start`
removes a session left by a killed daemon. Socket paths can be at most
93 bytes long. If the socket file is deleted while its daemon
runs, `start` waits for that daemon's lock; end the daemon with `kill` on
the `server.py` process that names the socket.

```sh
sock=$(mktemp -d)/socket
hol-d --socket "$sock" start
hol-d --socket "$sock" tree
hol-d --socket "$sock" stop
```

`kill PATH` terminates a leaf, including a busy one. `kill --tree PATH`
removes descendants before their parents. `stop` and `kill --tree /` close
the whole daemon. `hol-d run` removes its child if the command is
interrupted. The supervisor serializes forks with tree removal and removes
descendants after a parent exits unexpectedly.

Each node leads its own process group, which also holds the compilers and
other commands it starts. A node ends on SIGTERM, which `kill` and `stop`
send, or when its control channel closes. Either way it first sends SIGTERM
to each child's group, so the child ends its own subtree, and then kills
its own group. If the daemon dies, even by SIGKILL, every idle node sees
EOF, and busy leaves are ended by their frozen parents. No node or command
it started outlives the daemon.

Limits:

- A node handles SIGTERM between OCaml operations, which is immediate in
  practice. If a node has not ended 5 seconds later, for example inside a
  long `Sys.command` or after a phrase replaced the SIGTERM handler, the
  supervisor sends SIGKILL. Its parent then kills what remains of its
  group. Other commands wait for the removal meanwhile.
- The root cannot see its control channel close while it initializes. If
  the daemon dies during those first seconds, the root ends right after.
- A node killed from outside with SIGKILL, for example by the OOM killer,
  skips its own cleanup. Its parent then kills what remains of its group,
  and the supervisor ends its subtree.
- A node that ignores SIGTERM, for example after a phrase replaced the
  handler, or one stopped with SIGSTOP, survives the daemon's own death.
  `kill` and `stop` reach it through the fallback above. A stopped node
  that is being forked from also blocks `kill` and `stop` until it resumes.
- A phrase that replaces the node with `Unix.exec*` ends the session as far
  as hol-d is concerned. The new program ends when its parent node ends.
- A command that leaves its process group, for example with `setsid`, is
  outside these guarantees.

## Tutorial and tests

[`tutorial/`](tutorial) walks through the commands above in numbered
steps, from starting a daemon to sharing a project's imports and the
lifetime guarantees. Each step's `run.sh` is commented and checks its own
output. `make -C tutorial HOLDIR=...` runs them all, and
`make -C tutorial 03-plugins` runs one. [`tests/`](tests) stress process
cleanup and concurrency on Linux with `make -C tests HOLDIR=...`, with the
HOL Light OCaml switch active. The [hol-d workflow](../../.github/workflows/hol-d.yml)
runs both for pull requests that change hol-d.

## Integration with s2n-bignum

From the s2n-bignum repository root, run a batch or build modules to
load into an interactive daemon.

```sh
make -C arm fork-proofs PROOFS="generic/word_min generic/word_max"
make -C arm proof-modules PROOFS=proofs/word_min.ml MODULE_DIR=/tmp/my-arm-modules
```

`fork-proofs` starts its own daemon, runs the selected proofs, publishes
their checked logs and stops the daemon. The ARM and x86 CI jobs invoke
this target with the full proof selection. `proof-modules` writes the
architecture base, proof plugins and a `plan.json` that names the parent
for each plugin. Use a fresh `MODULE_DIR` and start the interactive daemon
from the repository root so the compiled proofs can open their assembly
objects. [CI proof action](../../.github/actions/proofs/action.yml) ·
[Proof module builder](../proof_batch/README.md#build-modules-for-an-interactive-session)
