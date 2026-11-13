# CI

CI runs two checks, and neither reads the other's output. The
**generation** check builds Sail and the plugin, regenerates every model
and context file, and compares them byte for byte with the
checked-in files in [generated/](../generated/README.md). The **proof**
check runs every proof suite on those checked-in models, each in a fresh
HOL Light kernel, and audits the logs; it does not install or run Sail.

## Jobs

The workflow `.github/workflows/ci.yml` has three Sail jobs:

| Job | Runs | Keeps |
| --- | --- | --- |
| `sail-hol-generation` | `setup.sh generation`, then `check.py generate`, on the CodeBuild runner, with the default 16 workers per compiler process | logs and fresh models on failure |
| `sail-hol-proofs` | `setup.sh proofs`, then `check.py proofs`, on the CodeBuild runner, with `SAIL_HOL_PROOF_JOBS=16` (the variable's own default is 4) | all logs, also of passing runs |
| `sail-hol` | passes only if both others passed; this is the one to require | |

### Time and memory

Measured on a 64-core machine:

- Generation takes about 700 s with 16 workers per compiler process and
  peaks at about 33 GiB of memory, with the four compiler processes
  and the test shards running together. The one-off
  `setup.sh generation` build comes on top.
- The full proof check takes about 550 s with `--jobs 16`.
- One small suite, such as `check.py proofs arm-hints`, takes about
  95 s, including the compiled Arm base that every Arm suite links.

To check one claim without the full runs, run the proof check on its
suite, or read the files in [generated/](../generated/README.md) and
[statements/](../statements/README.md) directly: the checked-in models
and statements are in the tree, and the proof check needs HOL Light but
not Sail.

## Commands

```sh
bash tools/sail/ci/setup.sh generation|proofs   # then source environment.sh
python3 tools/sail/ci/check.py generate
python3 tools/sail/ci/check.py proofs [--jobs N] [SUITE ...]
python3 tools/sail/ci/check.py refresh [--from-directory DIR]
python3 tools/sail/ci/check.py refresh-statements --from-directory DIR \
  [SUITE ...]
```

`setup.sh` builds one toolchain in a fresh directory at the revisions in
[versions.env](versions.env) and writes its paths to `environment.sh`
there. Use a separate shell for each toolchain. `proofs SUITE ...` checks
only the named suites, with the same audit. `refresh` replaces
`generated/` with fresh models; `refresh-statements` records
`statements/` from the logs of a proof run
([below](#refreshing-the-checked-in-files)). CI never runs
either.

## Scripts

| Tool | What it does | Needs |
| --- | --- | --- |
| `ci/setup.sh proofs` or `generation` | builds a toolchain in a new directory and writes its `environment.sh` | network |
| `ci/check.py proofs [SUITE ...]` | proves and audits the suites on the models in `generated/` | proof toolchain |
| `ci/check.py generate` | builds the plugin, runs the unit tests, regenerates every model and report and compares them with `generated/` | generation toolchain |
| `ci/check.py refresh [--from-directory DIR]` | the same generation, then replaces the models and reports in `generated/` | generation toolchain |
| `ci/check.py refresh-statements --from-directory DIR [SUITE ...]` | records `statements/` from the logs of a proof run in `DIR` | a finished proof run |
| `build.sh` | builds the plugin into `_build/` | generation toolchain |
| `run.sh ARCH FAMILY [SAIL-OPTION ...]` | runs Sail with the plugin on one family, such as `run.sh arm carry`, and writes `_build/arm-carry.ml`, `.translation-log` and `arm.context`; `--hol-light-quote-sources` also copies the Sail source into the model | generation toolchain |
| `check-proof.sh SUITE` | compiles and runs one suite's driver on the models in `_build/`: those `run.sh` wrote, or copies of `generated/` | proof toolchain |

`_build/` is scratch space: `run.sh`, `check-proof.sh` and both checks
write there, Git ignores it, and it can be deleted at any time.

## Refreshing the checked-in files

This is the one description of the procedure; the other pages link here.

`check.py generate` only checks: it regenerates every model and context
file into a directory under `_build/ci/`, compares them with
`generated/` and fails on any difference, printing that directory. It
never writes to `generated/`. To replace the checked-in files, use
`check.py refresh`, which runs the same generation and then installs the
result:

```sh
source $HOME/sail-hol-generation/environment.sh
python3 tools/sail/ci/check.py refresh
git diff --stat tools/sail/generated     # review what changed
```

After a failed `check.py generate`, `check.py refresh --from-directory
DIR` installs the files it already produced in `DIR` instead of
generating again. Then run `check.py proofs`. A theorem statement that
changes on purpose fails the proof check, as intended; record it from
the artifacts directory that the failed run prints, naming the changed
suites:

```sh
python3 tools/sail/ci/check.py proofs arm-carry
python3 tools/sail/ci/check.py refresh-statements \
  --from-directory <proof artifacts directory> arm-carry
```

`refresh-statements` audits each suite's log before it records it, and
you review the diff of `statements/`. Without suite names, both commands
cover every suite, but a failing suite stops the suites that have not
started yet, and their logs are then missing.

## Reading the Sail sources

A reference such as `src/instrs64.sail:194` in a model is relative to a
checkout of the pinned upstream model
([generated/README.md](../generated/README.md#source-checkouts)).
`bash tools/sail/ci/setup.sh generation` clones every source at its
pinned commit from [versions.env](versions.env) into the toolchain
prefix: `sail`, `sail-arm`, `sail-riscv`, `sail-x86` (shina) and
`sail-x86-from-acl2` (REMS), and `environment.sh` exports their paths.
To read one source without the toolchain, clone it and check out the
commit from `versions.env`:

```sh
git clone https://github.com/rems-project/sail-arm
git -C sail-arm checkout f5bf6c3
```

A permalink also works, for example
`https://github.com/rems-project/sail-arm/blob/f5bf6c3/arm-v9.4-a/src/instrs64.sail#L194`.

## Inputs

[versions.env](versions.env) pins Sail, HOL Light, the four model
checkouts (sail-arm, sail-riscv, shina-lab/sail-x86 and
rems-project/sail-x86-from-acl2), both OCaml compilers and the listed
opam packages. Other opam dependencies come from the opam repository at
setup time; a change there can make a check fail, not pass on a
different model. This HOL Light pin is separate from `HOLLIGHT_COMMIT`
in the workflow, which the other s2n-bignum jobs use. `setup.sh` clears
inherited Sail and OCaml settings before it builds. Only generation
fetches the models.

## Generation

`check.py generate`:

1. builds the plugin;
2. runs, all at once: the unit test files that need Sail but not HOL
   Light (`UNIT_TESTS`), the backend tests in shards (one per core, at
   most 24), and one compiler process for each of Arm, RV32, shina and
   REMS;
3. checks that the regenerated set is exactly the registered models with
   their reports and has every root with its argument types
   (`validate_models`), compares each file byte for byte with
   `generated/`, and checks that `generated/` did not change meanwhile.

Each compiler process translates its families in up to
`SAIL_HOL_GENERATION_JOBS` forked workers and writes files only after
every family has succeeded. It starts with an empty private z3 answer
file (`--memo-z3-path`), so no answer is reused between runs. Sail gives
z3 one second per question; a slow machine can therefore change a model,
which the comparison then rejects. `run.sh`, run by hand, keeps a local
answer file in `_build/` unless given one.

The Arm run omits upstream's A32, T32, SVE and SME instruction files
(`ARM_EXCLUDED_INPUTS`), which roughly halves Sail's type check. It
refuses to run if those files define anything but their own functions and
decoder clauses (`check_arm_exclusions`), and fails if an Arm model's
translation log names one of their decoders (`check_arm_outputs`).

## Proofs

`check.py proofs`:

1. checks the checked-in models and their roots (`validate_models`);
2. copies the files tracked by Git into a fresh snapshot, with the models
   in `tools/sail/_build/`, and runs `check_proof_sources` on it;
3. compiles `arm/proofs/base.ml` once (`check-proof.sh arm-base`) if an
   Arm suite is selected; each Arm suite links it;
4. runs the suites, largest model first, each through `check-proof.sh`
   in a fresh kernel, with the caller's environment minus `SAIL_*`
   settings, `HOLLIGHT_LOAD_PATH` and `LD_PRELOAD`. A suite that runs
   for an hour (`PROOF_TIMEOUT`) fails; after a failure, suites not yet
   started are not run;
5. audits each suite's log against `statements/`, and checks at the end
   that neither the sources nor the snapshot changed.

### Checking the proof logs

CI does not inspect HOL theorems. It reads each suite's log and requires:

- every expected theorem name exactly once, and no other line of the
  form `SAIL_HL_<RV32|ARM|X86>_..._<EQ|DIFF|EXACT>`;
- after each name, a statement that starts with `|- ` at column 0, so
  the theorem has no hypotheses, equal byte for byte to the suite's
  record in `statements/`;
- each recorded statement to mention exactly the generated roots that its
  name refers to, and to contain no part that HOL's printer elided (it
  prints a subterm nested more than 100 boxes deep as `.`);
- the suite's completion marker exactly once.

HOL Light prints neither types nor the difference between a variable and
a constant of the same name. The root types are checked separately in the
model files (`validate_models` in [ci/check.py](check.py)), for every
root of every architecture, and an extra root is refused.

A driver that printed a statement it had not proved would pass this
audit. Before any proof runs, `check_proof_sources` in
[ci/check.py](check.py) makes that harder. It is a text check against
accidents and lazy subversion, not a guarantee. It scans every file under
`proofs/` and `generated/` except README.md and refuses, outside comments:

- `new_axiom`, `mk_thm`, `CHEAT_TAC` and a definition of `check_axioms`;
- changes to the parsing interface, printers or overload priorities
  (`override_interface` and its relatives, `install_user_printer`,
  `prioritize_*`, `parse_as_infix` and the other `(un)parse_as_*`,
  `set_ellipsis_text`, `set_max_boxes`, `the_interface :=`,
  `.contents <-`), and `Obj`;
- `print_thm` and `string_of_thm` anywhere but
  [proofs/report.ml](../proofs/report.ml), whose `sail_hl_report` refuses a
  theorem with hypotheses or free variables before printing it.

It also requires each driver, with the files it loads, to have a line
that starts with `check_axioms ();;` after the last load and before the
completion marker. A load directive is recognised with or without a space
before its file name.

## Logs

Each check works in a new directory under `tools/sail/_build/ci/`.

- Generation, `generation-*/`: `backend-build.log`, one log per unit test
  file, `backend-tests-NN.log` per shard, `<architecture>-generation.log`
  per compiler process, and the fresh files in `models/`. The run ends
  with `All N regenerated HOL files and the 4 context files match
  byte-for-byte.` and the directory of the fresh files.
- Proofs, `proofs-*/tools/sail/_build/`: per suite `<suite>-ci-run.log`
  (the output of `check-proof.sh`), `<suite>-proof.log` (the kernel's
  output, which is audited) and the inline and build logs of
  `check-proof.sh`; `arm-base-*.log` for the compiled Arm base.
  After each suite the run prints
  `<suite>: N/N theorems equal statements/<suite>.txt`, and it ends with
  `K of M suites passed: T/T theorems equal statements/.` and the
  artifacts directory.

Each command that the controller starts is printed with a leading `+`.

## Environment variables

`setup.sh` writes the toolchain paths to `environment.sh`; the others are
optional.

| Variable | Read by | Meaning and default |
| --- | --- | --- |
| `SAIL_EXE`, `SAIL_DIR`, `SAIL_BUILD_DIR` | generation | Sail executable, checkout and build directory |
| `SAIL_ARM_DIR`, `SAIL_RISCV_DIR`, `SAIL_X86_SHINA_DIR`, `SAIL_X86_REMS_DIR` | generation | the four model checkouts |
| `HOLDIR` | proofs | HOL Light checkout; `check-proof.sh` puts its `_opam/bin` first on `PATH` if present |
| `SAIL_HOL_CI_PREFIX` | `setup.sh` | directory to create, which must not exist; default a new directory under `$RUNNER_TEMP`, `$TMPDIR` or `/tmp` |
| `SAIL_HOL_CI_BUILD_JOBS` | `setup.sh` | build jobs, 1 to 32; default 2 |
| `SAIL_HOL_GENERATION_JOBS` | `check.py generate` | forked translation workers per compiler process, 1 to 64; default 16 |
| `SAIL_HOL_PROOF_JOBS` | `check.py proofs` | default for `--jobs`, 1 to 64; default 4 |
| `SAIL_HOL_PROOF_BACKTRACE` | `check-proof.sh` | 0 omits OCaml backtraces; `check.py` sets 0; default 1 |
| `SAIL_RISCV_CONFIG` | `run.sh` | RV32 configuration; default `backend/rv32.json` |

`check.py` sets `SAIL_HOL_PLUGIN`, `SAIL_HOL_BUILD_DIR` and
`SAIL_ARM_EXCLUDED_INPUTS` for the processes it starts.

[test_ci.py](../tests/test_ci.py) tests the controller with fake models
and logs; it runs neither Sail nor HOL Light.
