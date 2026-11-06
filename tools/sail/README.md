# Checking s2n-bignum's instruction models against Sail

s2n-bignum's proofs rest on HOL Light models of AArch64, RV32IM and x86
instructions. This directory compares those models with independent
architecture specifications written in
[Sail](https://github.com/rems-project/sail): sail-arm, sail-riscv, and
for x86 both shina-lab's sail-x86 ("shina") and REMS's
sail-x86-from-acl2 ("REMS"). A plugin for the Sail compiler exports
selected Sail instruction bodies as HOL Light definitions. Hand-written
HOL Light proofs then show, for each instruction form, that the exported
relation and s2n-bignum's relation permit the same final states, or show
where they differ. The kernel checks every proof.
The export from Sail, the loading of the exported models, the lists of
required forms and the check of the proof logs are trusted:
[TRUST.md](TRUST.md) lists everything the results rely on.

To run the checks or regenerate the models, see
[How to use](#how-to-use).

## Terms

- A **form** is one width, lane layout, addressing mode or alias of an
  instruction that needs its own theorem, such as ADC at 64 bits. This is
  an architectural notion.
- A **suite**, such as `arm-carry`, is the name for a group of model
  correspondence proofs relating to a set of forms. It has a generated
  model `generated/<suite>.ml`, a proof `proofs/<suite>.ml` and the
  statements of its theorems in `statements/<suite>.txt`.
- An **entry**, a notion of the Sail export, is a row of an architecture
  table in [backend/](backend/) that defines one form on the Sail side,
  as a call of an upstream Sail function. Many forms share one function:
  ADC, ADCS, SBC and SBCS at 32 and 64 bits all call the same execute
  function, and the entry fixes the arguments that pick one of them (the
  width, and flags for "set flags" and "subtract") and passes the rest,
  such as register fields, as HOL parameters. The exporter translates the
  entry's call into a HOL relation, the **root** of that form.
- An **interpretation**, also a notion of the Sail export, replaces a
  Sail function or register that the exporter does not translate by a
  fixed meaning in s2n-bignum's state. For example, Sail's register read
  `X_read(n, 64)` becomes `read (XREG n) s`, s2n-bignum's register `n`. A
  **cut** is an interpretation of a function whose Sail body exists and
  is dropped.

## How it works

```text
 pinned Sail models                         s2n-bignum's relations
 (sail-arm, sail-riscv, shina, REMS)        (arm/, riscv/, x86/proofs/)
          |                                            |
          | Sail compiler with the plugin              |
          | (backend/: translator and tables)          |
          v                                            |
 generated/<suite>.ml                                  |
 generated/<suite>.dependencies                        |
          |                                            |
          +--------------------+-----------------------+
                               |
                               | HOL Light runs proofs/<suite>.ml
                               v
                 log of the theorems the kernel proved
                               |
                               | compared with statements/<suite>.txt
                               v
                         suite passes or fails

 check.py generate: reruns the left column and requires generated/
                    to come out byte for byte the same (trusted step)
 check.py proofs:   runs the rest for every suite, in fresh kernels
                    (kernel-checked step)
```

The two checks are independent: the proof check reads only the
checked-in files in `generated/`, and needs HOL Light but not Sail.

## How to use

Each check needs its own toolchain, which `ci/setup.sh` builds at the
pinned revisions. Prerequisites on Ubuntu: `build-essential git opam m4
pkg-config libgmp-dev`, plus `libpcre2-dev` for the proof check and `z3`
for generation; Python 3.9 or later. Use a new shell for each toolchain.

### Running the two checks

```sh
# Proof check: needs HOL Light, not Sail.
SAIL_HOL_CI_PREFIX=$HOME/sail-hol-proofs \
  bash tools/sail/ci/setup.sh proofs
source $HOME/sail-hol-proofs/environment.sh
python3 tools/sail/ci/check.py proofs --jobs 16
python3 tools/sail/ci/check.py proofs arm-carry   # one suite

# Generation check: regenerate every model, compare with generated/.
SAIL_HOL_CI_PREFIX=$HOME/sail-hol-generation \
  bash tools/sail/ci/setup.sh generation
source $HOME/sail-hol-generation/environment.sh
python3 tools/sail/ci/check.py generate
```

### Checking one claim

Work backwards from a theorem to the Sail code it is about. For
`SAIL_HL_ARM_ADC64_EQ`:

1. **Statement**: [statements/arm-carry.txt](statements/arm-carry.txt)
   gives exactly what is proved.
2. **Proof**: [proofs/arm-carry.ml](proofs/arm-carry.ml) states and
   proves it.
3. **Model**: `sail_hl_ARM_5fADC64` in
   [generated/arm-carry.ml](generated/arm-carry.ml) is the root. Before
   it the file quotes its entry as "Selected Sail call", and before each
   definition it names the Sail code that definition came from by
   `filename:line`; [generated/README.md](generated/README.md) says how
   to read a model.
4. **Entry**: the `carry` table in [backend/arm.ml](backend/arm.ml)
   builds the entry: which upstream function, with which fixed
   arguments.
5. **Assumptions**:
   [generated/arm-carry.dependencies](generated/arm-carry.dependencies)
   lists every helper translated and every interpretation used in the
   file, such as `primitive-contract X_read`;
   [TRUST.md](TRUST.md#interpretations) gives each interpretation's
   meaning.

### Regenerating `generated/`

`check.py generate` only checks: it regenerates every model and
dependency report into a directory under `_build/ci/`, compares them
with `generated/` and fails on any difference, printing that directory.
It never writes to `generated/`. To replace the checked-in files, use
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
changes on purpose fails the proof check; record it with
`check.py refresh-statements --from-directory DIR [SUITE ...]`, using
the artifacts directory that the failed run prints, and review the diff
of `statements/`.

### Tools

| Tool | What it does | Needs |
| --- | --- | --- |
| `ci/setup.sh proofs` or `generation` | builds a toolchain in a new directory and writes its `environment.sh` | network |
| `ci/check.py proofs [SUITE ...]` | proves and audits the suites on the models in `generated/` | proof toolchain |
| `ci/check.py generate` | builds the plugin, runs the unit tests, regenerates every model and report and compares them with `generated/` | generation toolchain |
| `ci/check.py refresh [--from-directory DIR]` | the same generation, then replaces the models and reports in `generated/` | generation toolchain |
| `ci/check.py refresh-statements --from-directory DIR [SUITE ...]` | records `statements/` from the logs of a proof run in `DIR` | a finished proof run |
| `build.sh` | builds the plugin into `_build/` | generation toolchain |
| `run.sh ARCH FAMILY [SAIL-OPTION ...]` | runs Sail with the plugin on one family, such as `run.sh arm carry`, and writes `_build/arm-carry.ml` and `.dependencies`; `--hol-light-quote-sources` also copies the Sail source into the model | generation toolchain |
| `check-proof.sh SUITE` | compiles and runs one suite's driver on the models in `_build/`: those `run.sh` wrote, or copies of `generated/` | proof toolchain |

[ci/README.md](ci/README.md) describes the options and logs.

## What is proved

We use the add-with-carry instruction ADC to illustrate the shape of the
theorems we prove. AArch64 `ADC` adds two registers and the carry flag.
The theorem for its 64-bit form, in
[statements/arm-carry.txt](statements/arm-carry.txt), is

```text
|- forall d n m s t.
       sail_hl_ARM_5fADC64 d n m s t <=>
       arm_ADC (XREG' d) (XREG' n) (XREG' m) s t
```

- `arm_ADC` is s2n-bignum's relation, from
  [arm/proofs/instruction.ml](../../arm/proofs/instruction.ml). It holds
  when `t` is a final state that ADC permits from the initial state `s`.
- `sail_hl_ARM_5fADC64` is the root exported from Sail (`_5f` escapes
  `_`). Its entry in [backend/arm.ml](backend/arm.ml) is

  ```text
  ARM_ADC64(d, n, m) = execute_aarch64_instrs_integer_arithmetic_add_sub_carry(
    UInt(d), 64, UInt(m), UInt(n), false, false)
  ```

  The upstream function's parameters are `d`, `datasize`, `m`, `n`,
  `setflags` and `sub_op`, so the two `false` arguments select ADC without
  flags. The generated model quotes the entry before the root, with "v0
  is d, v1 is n, v2 is m".
- `d`, `n` and `m` are the 5-bit fields Rd, Rn and Rm of the encoding, in
  the order in which s2n-bignum's decoder passes them
  ([arm/proofs/decode.ml](../../arm/proofs/decode.ml), `arm_adcop`).
  `XREG' d` is the 64-bit register that field names; register 31 reads
  zero and ignores writes.

The theorem says that the two relations permit exactly the same final
states, for every register field, including 31 and equal fields, and
every initial state.

Not every theorem has this shape. In general, each theorem's name ends
in one of four kinds:

- `_EQ`: the relations agree, as for ADC. Most theorems have this form.
- `_SAFE_EQ`: some s2n-bignum relations have a safety guard, a condition
  such as an aligned stack pointer outside which they permit every final
  state. The theorem states that the guard can hold and that the
  relations agree wherever it does.
- `_DIFF`: where the models differ, states that one relation permits and
  the other rejects.
- `_EXACT`: for the shina forms that differ, exactly which final states
  shina permits, in terms of s2n-bignum's relation.

[statements/README.md](statements/README.md) gives the exact statement
of each kind and the number of theorems of each.

| Sail model, pinned commit | Compared with s2n-bignum | Result |
| --- | --- | --- |
| [sail-arm](https://github.com/rems-project/sail-arm) `f5bf6c3` | all 221 public definitions in `arm/proofs/instruction.ml`, as 1,404 forms | all agree; the 246 memory forms within s2n-bignum's safety guards |
| [sail-riscv](https://github.com/riscv/sail-riscv) `cd3f185` | all 48 RV32IM definitions in `riscv/proofs/instruction.ml`, as 50 forms | 48 agree, the 13 halfword and word accesses, branches and jumps within s2n-bignum's alignment guards; ECALL and EBREAK differ: Sail always traps, s2n-bignum permits every final state |
| [shina-lab/sail-x86](https://github.com/shina-lab/sail-x86) `1829cb6` | 205 register forms of 68 of the 156 x86 instruction definitions in `x86/proofs/x86.ml`: 28 scalar and 40 AVX2 integer instructions, listed in [x86_forms.py](scripts/x86_forms.py) | 199 agree; the 6 RCL and RCR forms at 8 and 16 bits differ |
| [REMS sail-x86-from-acl2](https://github.com/rems-project/sail-x86-from-acl2) `0c6c023` | the 119 of those forms that this model implements | 100 agree; 19 differ |

The Sail compiler is at `3df5403`. [ci/versions.env](ci/versions.env)
pins all five commits for both checks. The 156 x86 definitions are the
`x86_*` definitions other than the 20 `x86_Exception_*` ones.

## What is not proved

- That the export preserves the meaning of the Sail code. The
  translator, the instruction tables and the interpretations of
  registers, memory and platform calls are trusted
  ([TRUST.md](TRUST.md#interpretations)).
- That the form lists are complete. They are written by hand in
  [coverage.py](scripts/coverage.py) and
  [x86_forms.py](scripts/x86_forms.py) and were compared with
  `arm/proofs/decode.ml` by review; CI checks only the set of public
  definition names.
- That the s2n-bignum side of each statement is the right one. The
  drivers choose it, for example `arm_TBL2 (QREG' d) (QREG' n)
  (QREG' (word_add n (word 1)))` for two consecutive table registers.
- That the Sail and s2n-bignum decoders agree. The comparisons start
  from execute bodies, or from selected decoder paths.
- Equivalence of whole platforms: privilege levels, address translation,
  exceptions, and processor features beyond the configured ones.
- Anything about states outside a safety guard: Arm memory forms with an
  unaligned SP, overlapping writeback or equal load destinations; RV32
  halfword and word accesses at unaligned addresses; branches, JAL and
  JALR with unaligned targets.
- Equality of fault outcomes or memory access events. A reached Arm
  fault permits every final state, and the Arm memory theorems erase the
  event lists.
- Arm FPSR and branch-target (BType) behaviour: the exports omit those
  writes.
- Arm branch-target canonicalisation: `BranchTo` sets PC to the target
  as given, without upstream's top-byte-ignore adjustment.
- REMS's RIP update: the comparisons reset RIP and observe every other
  component.
- x86 memory operands, instruction decoding, and the x86 instruction
  definitions not in `x86_forms.py`, among them MOV, LEA, CMOV, BT, BTC,
  BTR, BTS, PUSH and POP.
- Agreement for the forms that differ. For REMS the `_DIFF` theorems
  show only that at least these differences exist; no exact relation is
  proved.
- That s2n-bignum's safety guards hold for the operands a program uses.
  The proofs show only that each guard holds for some operands and state.

## Coverage

CI requires a theorem for every form that
[scripts/coverage.py](scripts/coverage.py) and
[scripts/x86_forms.py](scripts/x86_forms.py) list:

- AArch64 and RV32IM: every public instruction definition, that is every
  name that `arm/proofs/instruction.ml` or `riscv/proofs/instruction.ml`
  binds with `let` or `and` to `define` or `new_definition`. `check.py`
  compares these names with the instructions in coverage.py
  (`ARM_FAMILIES`, `RV32`) and fails if one is missing, so a new
  s2n-bignum instruction model fails CI until it is covered. The forms of
  each definition (widths, lane sizes, addressing modes, aliases) are
  listed by hand and were compared with `arm/proofs/decode.ml` by review;
  [docs/ARM-COVERAGE-MAP.md](docs/ARM-COVERAGE-MAP.md) gives each Arm
  definition's Sail source and forms.
- x86: only the register forms listed in x86_forms.py. A new definition
  in `x86/proofs/x86.ml` is not required automatically.

### When s2n-bignum gains an instruction model

For a new Arm definition `arm_FOO`, CI reports "aarch64 public
instruction inventory differs; missing ['arm_FOO']". To cover it:

1. Find the Sail function that executes the instruction, and add an
   entry for each form to the table in [backend/arm.ml](backend/arm.ml):
   the call with the fixed arguments that select the form, and the
   register fields in the order s2n-bignum's decoder passes them.
2. List the instruction and its forms in a family of `ARM_FAMILIES` in
   coverage.py. A new family is a new suite, with its own
   `generated/arm-<family>.ml`, `proofs/arm-<family>.ml` and
   `statements/arm-<family>.txt`.
3. Run `build.sh` and `run.sh arm <family>`, and read the new root and
   its `.dependencies` in `_build/`. If the Sail body reaches something
   the exporter does not translate, the run stops; an interpretation for
   it is a `contracts` row in the table with its case in the translator,
   and [TRUST.md](TRUST.md#interpretations) must describe it.
4. Add the theorem to the suite's driver in `proofs/`, and run
   `check-proof.sh arm-<family>` on the model in `_build/` until it
   passes.
5. Regenerate `generated/`, run the proof check and record the new
   statements, as in [How to use](#how-to-use). Update the counts that
   tests and documents pin: the catalogue fingerprint in
   `tests/test_entry_catalogue.py`, the form counts in
   `tests/test_coverage.py` and `tests/test_ci.py`, the table under
   [What is proved](#what-is-proved) and the coverage map.

RV32 works the same way with [backend/rv32.ml](backend/rv32.ml), the
`RV32` table in coverage.py and `proofs/rv32.ml`. x86 uses the form
names in [backend/x86.ml](backend/x86.ml), entries in
[backend/x86_shina.ml](backend/x86_shina.ml) and
[backend/x86_rems.ml](backend/x86_rems.ml), x86_forms.py and the x86
drivers in `proofs/`.

## Model findings

The comparisons showed three errors in s2n-bignum's relations and one
open question:

| Finding | Status | Details |
| --- | --- | --- |
| `arm_LDP` required a load for `LDP XZR, XZR`, although equal destinations are constrained unpredictable | `arm_LDP` and `ARM_EXEC_CONV` corrected by this work; the decoder accepts the instruction, but no s2n-bignum function contains it, so no proof of s2n-bignum code depended on it | [Arm model differences](docs/ARM-DISCREPANCIES.md#duplicate-load-destinations) |
| 8- and 16-bit `x86_SHL` and `x86_SHR` fixed CF where it is undefined | corrected by two x86 model commits in this series, which awslabs/s2n-bignum#484 also contains; no decodable s2n-bignum code is affected | [x86 guide](docs/X86.md#shift-corrections) |
| 16-bit `x86_SHLD` and `x86_SHRD` fixed the result and flags for counts above 16 | as above | as above |
| 8- and 16-bit `x86_RCL` and `x86_RCR` leave OF undefined at whole-cycle counts, where shina keeps it | open: Intel's manual is ambiguous. s2n-bignum permits a superset of shina's final states (`_EXACT`), so this cannot invalidate a proof about s2n-bignum code | [divergences](docs/X86-DIVERGENCES.md#rcl-rcr-full-cycle-of) |

The REMS forms that differ are not counted as errors in s2n-bignum;
[X86-DIVERGENCES.md](docs/X86-DIVERGENCES.md) classifies them.
