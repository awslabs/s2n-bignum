# Checking several HOL Light proofs together

The stock `make proofs` flow builds each of the ~360 proof targets per
architecture into its own executable. Each one compiles and initializes the
same architecture model (`proofs/base.ml`) before its proof starts. On ARM
that initialization alone takes about a minute, while a proof such as
`word_min` then needs under a second. Across all targets this adds up to
roughly six CPU-hours of repeated setup per architecture.

The batch runner starts a private `hol-d` and loads the architecture model
once. Proofs that share further ordered imports can fork from a deeper session,
such as `/arm/ecc/jacobian/nistp256`.
Proofs with a different initialization order run in children of the bare HOL
root. Both paths run the original axiom check, print the specification theorems
and write the timing record consumed by CI.

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
| `PROOF_JOBS` | Concurrent proof executions and shared session initializations | 2 |
| `BUILD_JOBS` | Concurrent compilations | `PROOF_JOBS` |
| `PROOF_OUTPUT` | Fresh directory for the logs | a new temporary directory |

The launcher prints the log directory, one line per proof as it compiles and as it finishes
(`[ 57/361] ok arm/generic/word_min.correct (0.8 s)`, or `FAILED` with the first error line), the slowest
compiles and proofs, and the build and proof wall times. Build tools' own output is shown only
for a step that fails. The batch runner
publishes a log such as `arm/generic/word_min.correct` only after it has validated the proof. A
failed proof makes Make fail. Its diagnostics are in `<target>.correct.partial`. Shared load
diagnostics are in `sessions/<session>.log`, and root startup output is in `base.log`.
Compiled proofs are temporary. Make reuses assembly objects across invocations.

### Prerequisites

- Linux, Python 3.9 or newer, GNU Make and an assembler for the target architecture. `hol-d`
  needs POSIX `fork()` and native OCaml Dynlink. macOS has `fork()` but is untested; native Windows
  is unsupported.
- A native HOL Light checkout built with `HOLLIGHT_USE_MODULE=1`, with `HOLDIR` pointing at it.
  [CI toolchain setup](../../.github/actions/setup-hol-light/action.yml)
- The OCaml toolchain that built it. If the checkout has a local opam switch (`$HOLDIR/_opam`), the
  launcher selects it. Otherwise, activate the same OCaml, Camlp5, Zarith and `ocamlfind` packages
  yourself.

## How it works

`run.py` asks Make for the architecture's inputs and proof targets. The build
phase compiles the native `hol-d` host and the same architecture and proof
modules you can request with `make proof-modules`. Each batch owns its build
directory and socket, so concurrent builds can use separate HOL checkouts.
[Make targets](proofs.mk) · [Layer compiler](../hol-d/holbuild.py)

The compiler writes `plan.json` in the output directory. It lists shared
sessions in load order, each session's parent and public plugin, and the
parent and plugin for each proof source. Both Make targets use the same plan
for the same selection. The proof phase starts the daemon, forks `/arm` or
`/x86` when needed, and publicly loads `proof_base.cmxs` there. Each deeper
session forks its initialized parent and loads one more public module.
`hol-d run PARENT PLUGIN` forks one child, loads the plugin privately, streams
its output and waits for its exit. Success requires both initializer return
and a clean exit, including exit handlers, reported by the child's parent. Session loads and proofs
share one `PROOF_JOBS` limit. Ready shared loads have priority when a slot
opens. Other slots can run proofs on ready branches. The batch shuts down
its daemon on completion or interruption.
[Batch runner](runner.py) · [Daemon commands](../hol-d/README.md)

The runner publishes `.correct` only for a successful command whose log
ends with its single valid timing line and passes the existing error scan.
It appends `Proof batch plugin returned` to that log. `base.log` records root
initialization. `sessions/arm/ecc.log`, for example, records the ECC load and
elapsed time. A session error disqualifies its descendants. Other branches
continue. Unconfirmed runs retain their `.partial` logs.

### Build modules for an interactive session

From the repository root, choose a fresh output directory. Omit `MODULE_DIR`
to let Make select one and print the paths. With no `PROOFS` or `SESSIONS`, this builds just
`proof_base.cmxs`. You can pass existing Make targets or architecture-relative
`.ml` paths, including a new source before it has a Make target.

```sh
make -C arm proof-modules PROOFS="proofs/word_min.ml" MODULE_DIR=/tmp/my-arm-modules
hol-d --start-if-needed fork / arm
hol-d load --public /arm /tmp/my-arm-modules/proof_base.cmxs
hol-d run /arm /tmp/my-arm-modules/proofs_word_min.cmxs
```

To build a particular session even for a single proof, pass its absolute
session name in `SESSIONS`. This also builds all its ancestors. With the
repository root as the current directory and a fresh daemon, for example,

```sh
make -C arm proof-modules SESSIONS=/arm/ecc PROOFS=proofs/edwards25519_encode.ml MODULE_DIR=/tmp/ecc-modules
hol-d --start-if-needed fork / arm
hol-d load --public /arm /tmp/ecc-modules/proof_base.cmxs
hol-d fork /arm ecc
hol-d load --public /arm/ecc /tmp/ecc-modules/proof_ecc.cmxs
hol-d run /arm/ecc /tmp/ecc-modules/proofs_edwards25519_encode.cmxs
```

Omit `PROOFS` to build just the requested shared sessions. At a prompt in a
child of `/arm/ecc`, `open Proof_base;; open Proof_ecc;;` brings both sets
of names into scope in their original order.

The module directory includes the `.cmi` and `.cmx` files for public loads.
Generated module filenames use lowercase letters and replace dots and
hyphens in the source or session name with underscores. Use `plan.json`
to look up the plugin built for a particular source.
At an interactive prompt in a child of `/arm`, enter `open Proof_base;;` to
use names such as `arm` directly.
Modules in its `root/` subdirectory include their own model and use `hol-d run /`.
To build and check a registered source in one command, use
`make -C arm fork-proofs PROOFS=proofs/word_min.ml`.

### Which imports can share a session?

The batch runner passes this repository's `layers.json` and the selected
architecture to the hol-d layer compiler. The `arm` root loads
`arm/proofs/base.ml` and the `x86` root loads `x86/proofs/base.ml`. Each
root spells out its own tree. Each node's `source` is the HOL file to load,
and each key under `children` adds one component to the session path. For
example, `nistp256` under `/arm/ecc/jacobian` loads `EC/nistp256.ml`. Add a
child under the session whose imports must run first, in both trees if both
architectures need it.
[Layer declarations](layers.json) · [Manifest format](../hol-d/README.md#compile-proofs-with-shared-imports)

For each edge the compiler expands the import in its ancestors' load context.
It shares the deepest matching prefix used by at least two selected proofs.
A single-use import stays in the proof unless explicitly requested with
`SESSIONS` for `proof-modules`. The architecture base is always available.
An intervening tactic, definition or other expression ends sharing at the
previous matched edge. Repeated `loadt` operations remain in source order.
[Prefix matching](../hol-d/layers.py)

The compiler feeds each original proof to the pinned HOL `inline_load.ml`. It
expands each session's import in a wrapper that first loads the session's
ancestors. A proof shares a session only if that expansion appears
byte-identical right after the parent's, with no executable OCaml between
them according to the HOL parser. The expansion includes the loader's
transitive `needs` handling and digest updates. An OCaml AST rewrite
re-exports names introduced by simple top-level `open` statements at their
original location, preserving shadowing for the separate modules. ARM's base
needs this for `Compute`. The exporter rejects unsupported forms.
[Open handling](../hol-d/export_opens.ml)

For example, `bignum_sqrt_p25519` starts from a base that loads Jacobi theory
before the standard `proofs/base.ml`, so its plugin contains the complete inlined
proof. The launcher lists these bare-root targets at the end of the build phase.

The compiler reads and inlines each complete source to establish eligibility. The launcher,
`run.py`, takes its target list from the architecture Makefile (`batch-targets`) and has Make
build the full set of inputs (`batch-inputs`), including x86 Windows ABI objects and tutorial
helpers. Some proofs read other routines' objects transitively.
[Make integration](proofs.mk)

## CI verification and timing history

`fork-proofs` with no `PROOFS` selection checks every Make proof target and tutorial, then runs the
existing theorem inventory check. Each child must exit successfully. Each plugin must also return
from initialization after printing its timing footer. [Inventory check](../count-proofs.sh)

The proof action uses the same target for PRs and mainline baselines. It records build and run wall
time including tutorials, preserves available failure diagnostics, and collects per-proof results
from confirmed logs. Bare-root timers include the architecture model. Shared timers start after their selected parent
has initialized, so per-proof deltas against a baseline from the stock flow overstate the
improvement. Phase wall times remain comparable.
[Timing collector](../proof_timing/collect.py) · [Timing report](../proof_timing/report.py)
