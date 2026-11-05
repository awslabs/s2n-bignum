# CI

CI runs two checks, and neither reads the other's output. The
**generation** check builds Sail and the plugin, regenerates every model
and its dependency report, and compares them byte for byte with the
checked-in files in [generated/](../generated/README.md). The **proof**
check runs every proof suite on those checked-in models, each in a fresh
HOL Light kernel, and audits the logs; it does not install or run Sail.

## Jobs

The workflow `.github/workflows/ci.yml` has three Sail jobs:

| Job | Runs | Keeps |
| --- | --- | --- |
| `sail-hol-generation` | `setup.sh generation`, then `check.py generate`, on a four-core runner with `SAIL_HOL_GENERATION_JOBS=4` | logs and fresh models on failure |
| `sail-hol-proofs` | `setup.sh proofs`, then `check.py proofs`, with `SAIL_HOL_PROOF_JOBS=16` | all logs, also of passing runs |
| `sail-hol` | passes only if both others passed; this is the one to require | |

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
([statements/README.md](../statements/README.md#updating)). CI never runs
either.

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
report names one of their decoders (`check_arm_outputs`).

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

[TRUST.md](../TRUST.md#checking-the-proof-logs) lists what the source
check and the log audit require, and what they do not establish.

## Logs

Each check works in a new directory under `tools/sail/_build/ci/`.

- Generation, `generation-*/`: `backend-build.log`, one log per unit test
  file, `backend-tests-NN.log` per shard, `<architecture>-generation.log`
  per compiler process, and the fresh files in `models/`. The run ends
  with `All N regenerated HOL files and their dependency reports match
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
| `SAIL_HOL_PROOF_FORKS` | `check.py proofs`, drivers | forked processes per large suite, 1 to 64; `check.py` sets 4 unless given |
| `SAIL_HOL_PROOF_BACKTRACE` | `check-proof.sh` | 0 omits OCaml backtraces; `check.py` sets 0; default 1 |
| `SAIL_RISCV_CONFIG` | `run.sh` | RV32 configuration; default `backend/rv32.json` |

`check.py` sets `SAIL_HOL_PLUGIN`, `SAIL_HOL_BUILD_DIR` and
`SAIL_ARM_EXCLUDED_INPUTS` for the processes it starts.

[test_ci.py](../tests/test_ci.py) tests the controller with fake models
and logs; it runs neither Sail nor HOL Light.
