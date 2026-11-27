# Checking several HOL Light proofs together

The stock `make proofs` flow builds each of the ~360 proof targets per
architecture into its own executable. Each one compiles and initializes the
same architecture model (`proofs/base.ml`) before its proof starts. On ARM
that initialization alone takes about a minute, while a proof such as
`word_min` then needs under a second. Across all targets this adds up to
roughly six CPU-hours of repeated setup per architecture.

The batch runner compiles the HOL Light architecture base once, initializes
it once in a parent process, then forks a child to check each eligible proof.
CI and local `make fork-proofs` use it.

Proofs that need a different base use the standalone builder
(`tools/build-proof.sh`). Every proof, shared or standalone, ends with the same
footer that `build-proof.sh` generates. It runs `Hol_lib.check_axioms ()`,
prints each proved `*_SUBROUTINE_CORRECT`/`*_SAFE` theorem, and writes the
`Running time:` record that CI checks and collects.

[CI proof action](../../.github/actions/proofs/action.yml) · [Make rules](proofs.mk) ·
[Proof builder](../build-proof.sh)

## Run locally

From the s2n-bignum repository root, with `HOLDIR` set (see [Prerequisites](#prerequisites)):

```bash
# Check selected proofs. Targets are Make proof targets relative to the arch directory.
make -C arm fork-proofs PROOFS="generic/word_min generic/bignum_add"
make -C x86 fork-proofs PROOFS="p384/bignum_nonzero_6 tutorial/safety" PROOF_JOBS=4

# Check every proof target and tutorial, then the architecture's complete
# theorem-name inventory (what CI runs).
make -C x86 fork-proofs BUILD_JOBS=4 PROOF_JOBS=8
```

| Variable | Meaning | Default |
|---|---|---|
| `PROOFS` | Targets to check | all targets and tutorials |
| `PROOF_JOBS` | Concurrent proofs | 2 |
| `BUILD_JOBS` | Concurrent compilations | `PROOF_JOBS` |
| `PROOF_OUTPUT` | Fresh directory for the logs | a new temporary directory |

The launcher prints the log directory, one line per proof as it compiles and as it finishes
(`[ 57/361] ok generic/word_min (0.8 s)`, or `FAILED` with the first error line), the slowest
compiles and proofs, and the build and proof wall times. Build tools' own output is shown only
for a step that fails. The batch runner
publishes a log such as `arm/generic/word_min.correct` only after it has validated the proof. A
failed proof makes Make fail. Its diagnostics are in `<target>.correct.partial`, or in `base.log`
if the shared base failed. Compiled proofs are temporary. Make reuses assembly objects across
invocations.

### Prerequisites

- Linux, Python 3.9 or newer, GNU Make and an assembler for the target architecture. The worker
  needs POSIX `fork()` and native OCaml Dynlink. macOS has `fork()` but is untested; native Windows
  is unsupported.
- A native HOL Light checkout built with `HOLLIGHT_USE_MODULE=1`, with `HOLDIR` pointing at it.
  [CI toolchain setup](../../.github/actions/setup-hol-light/action.yml)
- The OCaml toolchain that built it. If the checkout has a local opam switch (`$HOLDIR/_opam`), the
  launcher selects it. Otherwise, activate the same OCaml, Camlp5, Zarith and `ocamlfind` packages
  yourself.

## How it works

**Build the executable and plugins.** The expanded architecture `proofs/base.ml` becomes
`proof_base.ml`. Compiling it with `ocamlopt -c` produces `proof_base.cmi` (the interface),
`proof_base.cmx` (native linking metadata), and `proof_base.o` (machine code). The linker
combines the base, HOL Light, and the compiled worker driver into `worker.native`.
Each eligible proof is compiled against the base interface and linked into a `.cmxs` plugin
with `ocamlopt -shared`. Both builds finish before the worker starts.
[Compiler](compiler.py) · [Link order](runner.py)

**Run the base initialization.** When Python starts `worker.native`, OCaml initializes
`Hol_lib` and then evaluates all of `Proof_base`'s top-level bindings and setup expressions.
That is when the base's theorem values are computed and its setup calls take effect. After
both modules finish initializing, OCaml reaches the final `let ()` in `worker.ml`. The driver
prints `Proof batch base ready:` and calls `run_pool` with the jobs passed in `Sys.argv`.
Python captures the worker's own output in `base.log`: startup, then a status line for each failed child.
[Worker startup](worker.ml)

**Run each proof in a child.** The parent keeps the initialized base in memory while it
schedules and waits for children. Each `Unix.fork` gives a child a copy-on-write view of that
state. In the child, `Dynlink.loadfile_private` loads the precompiled `.cmxs` and immediately
runs its top-level proof code. References to `Hol_lib` and `Proof_base` use the values the
child inherited. Changes to that state stay in the child.
[Worker](worker.ml)

```
BUILD (run.py → compiler.py, runner.build_worker)

  <arch>/proofs/base.ml ──inline + compile──► proof_base.{cmx,o} ─┐
  hol_lib.cmxa ───────────────────────────────────────────────────┼─ link ─► worker.native
  worker.ml ──────────────────────────────────────────────────────┘

  proof.ml
       │ inline_load
       ▼
  base prefix + remainder
       │
       ├─ prefix == base ──► remainder + footer ─ocamlopt -shared─► proof_i.cmxs
       └─ otherwise ───────► tools/build-proof.sh ────────────────► standalone_i.native

RUN (runner.run_batch → worker.native)

  worker.native: initialize Hol_lib + Proof_base, then enter worker.ml ──► base.log
       │
       ├─ Unix.fork ─► child: Dynlink.loadfile_private proof_1.cmxs ─► proof, footer, exit
       ├─ Unix.fork ─► child: Dynlink.loadfile_private proof_2.cmxs ─► ...
       └─ Unix.fork ─► child: Unix.execv standalone_k.native ─────────► ...
              (at most PROOF_JOBS children at once; each child's output → <target>.correct.partial)
       │
       waitpid: exit 0 ─► rename to .partial.exited
       │
  runner.py: no errors, one timing record, plugin returned ─► rename to <target>.correct
```

The diagram simplifies the checks. If `base.log` contains an error, the supervisor rejects every plugin
proof. Standalone proofs do not depend on the shared base. A plugin must print
`Proof batch plugin returned` after its footer, which shows that the proof ran to completion and
did not call `exit` early. A standalone proof has no such trailer, so its timing record must be its
final line. When the worker exits, or the supervisor is interrupted, the supervisor kills the
worker's whole process group, so no proof keeps running.

The fork acts as an in-memory checkpoint. The pinned HOL distribution also ships
`make-checkpoint.sh`, which starts an interactive `hol.sh` under DMTCP and writes a restartable
image. The native fork fits the existing compiled proof path and needs no image distribution,
restart service or on-disk cache invalidation. Its setup cost recurs at the next invocation.

### Code map

1. The Make target `fork-proofs` calls the Python script `run.py`. Its `check()` function selects
   the targets, asks Make to build the full set of batch inputs, and runs both phases.
   [`proofs.mk`](proofs.mk) · [`run.py`](run.py)
2. The Python function `build_batch()` in `compiler.py` expands the sources and calls
   `split_prefix()` to decide which proofs can use the shared base. It compiles those proofs as
   plugins and calls `build-proof.sh` for the rest. Both paths use the shell function
   `proof_footer()`. [`compiler.py`](compiler.py) · [`build-proof.sh`](../build-proof.sh)
3. The Python function `build_worker()` in `runner.py` links the base into the worker. After
   initialization, the OCaml function `run_pool` in `worker.ml` forks the children. In each child,
   `run_child` loads a plugin or executes a standalone proof. [`runner.py`](runner.py) ·
   [`worker.ml`](worker.ml)
4. The Python function `run_batch()` in `runner.py` starts the worker and calls
   `valid_proof_log()` before publishing `.correct` files. [`runner.py`](runner.py)

### Which proofs can share a base?

The compiler feeds the architecture's `proofs/base.ml` and each original proof to the pinned HOL
`inline_load.ml`. It accepts the split only if the expanded base is byte-identical and the HOL
parser finds no executable OCaml before it. This includes the loader's transitive `needs` handling
and digest updates. An OCaml AST rewrite re-exports names introduced by simple top-level `open`
statements at their original location, preserving shadowing for the separate proof module. ARM's
base needs this for `Compute`. The exporter rejects unsupported forms.
[Prefix handling](compiler.py) · [Open handling](export_opens.ml)

For example, `bignum_sqrt_p25519` starts from a base that loads Jacobi theory
before the standard `proofs/base.ml`, so it uses the standalone builder. The
launcher lists the fallbacks at the end of the build phase.

The compiler reads and inlines each complete source to establish eligibility. The launcher,
`run.py`, takes its target list from the architecture Makefile (`batch-targets`) and has Make
build the full set of inputs (`batch-inputs`), including x86 Windows ABI objects and tutorial
helpers. Some proofs read other routines' objects transitively.
[Make integration](proofs.mk)

## CI verification and timing history

`fork-proofs` with no `PROOFS` selection checks every Make proof target and tutorial, then runs the
existing theorem inventory check. Each child must exit successfully. Each plugin must also return
to the worker after printing its timing footer. [Inventory check](../count-proofs.sh)

The proof action uses the same target for PRs and mainline baselines. It records build and run wall
time including tutorials, preserves available failure diagnostics, and collects per-proof results
from confirmed logs. Standalone timers include the architecture model. Shared timers start after it
has initialized, so per-proof deltas against a baseline from the stock flow overstate the
improvement. Phase wall times remain comparable.
[Timing collector](../proof_timing/collect.py) · [Timing report](../proof_timing/report.py)
