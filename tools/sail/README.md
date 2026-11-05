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
[What it rests on](#what-it-rests-on) lists everything the results rely
on.

A suggested reading order:

1. This page up to "What is not proved": [Terms](#terms),
   [What is proved](#what-is-proved), [Checking one
   claim](#checking-one-claim) and [What is not
   proved](#what-is-not-proved).
2. [statements/README.md](statements/README.md): the kinds of theorem
   and the notation of the statements.
3. One statement in `statements/arm-carry.txt` and its proof in
   `proofs/arm-carry.ml`.
4. [generated/README.md](generated/README.md), then the root
   `sail_hl_ARM_5fADC64` in `generated/arm-carry.ml`.
5. [What it rests on](#what-it-rests-on), the
   [interpretations](backend/README.md#interpretations), then
   `generated/arm.context`.
6. [backend/README.md](backend/README.md) for the translator, and
   [Model differences](#model-differences) for what the comparison found.

To run the checks or regenerate the models, see
[How to use](#how-to-use). To add an instruction, see
[CONTRIBUTING.md](CONTRIBUTING.md).

## Terms

- A **form** is one width, lane layout, addressing mode or alias of an
  instruction that needs its own theorem, such as ADC at 64 bits. This is
  an architectural notion.
- A **suite**, such as `arm-carry`, is the name for a group of model
  correspondence proofs relating to a set of forms. It has a generated
  model `generated/<suite>.ml`, a proof `proofs/<suite>.ml` and the
  statements of its theorems in `statements/<suite>.txt`.
- A **family** is the group of instructions that one run of the exporter
  translates together, as in `run.sh arm carry` and `ARM_FAMILIES` in
  [coverage.py](scripts/coverage.py). For Arm, a family and its suite
  coincide (`arm-<family>`). RV32 has one suite, `rv32`, whose models
  are `rv32.ml` and `rv32-control.ml`. x86 has the suites
  `x86-arithmetic`, `x86-shift` and `x86-vector` for shina and
  `x86-rems-arithmetic` and `x86-rems-shift` for REMS.
- An **entry**, a notion of the Sail export, is a row of an architecture
  table in [backend/](backend/) that defines one form on the Sail side,
  as a call of an upstream Sail function. Many forms share one function:
  ADC, ADCS, SBC and SBCS at 32 and 64 bits all call the same execute
  function, and the entry fixes the arguments that pick one of them (the
  width, and flags for "set flags" and "subtract") and passes the rest,
  such as register fields, as HOL parameters. The exporter translates the
  entry's call into a HOL relation, the **root** of that form.
- A **root parameter** is a parameter of a root. The first ones are the
  entry's fields, in the entry's order. For Arm that is the order in
  which s2n-bignum's decoder passes them. For RV32 it is the order of
  Sail's `execute_*` function, as in `execute_RTYPE(rs2, rs1, rd, op)`,
  while the statements quantify over `rd rs1 rs2`, s2n-bignum's order.
  Before the fields come the component parameters `reg_<R>`, one for
  each Sail register that has no fixed meaning; a theorem holds for every
  value of them.
- An **interpretation**, also a notion of the Sail export, replaces a
  Sail function or register that the exporter does not translate by a
  fixed meaning in s2n-bignum's state. For example, Sail's register read
  `X_read(n, 64)` becomes `read (XREG n) s`, s2n-bignum's register `n`. A
  **cut** is an interpretation of a function whose Sail body exists and
  is dropped.
- A **z3 decision** is a question that the Sail compiler or the exporter
  asked z3 during translation, such as whether a conditional is always
  true or an assertion always holds. The model keeps the answer and not
  the question: it has no code for the branch or check that z3 removed.
  Some removed code is listed in a model's header
  ([generated/README.md](generated/README.md#assumptions)).
- `ASSIGNS entirety s` is s2n-bignum's relation that holds between `s`
  and every state. A theorem that says a relation "is `ASSIGNS entirety`"
  says that it permits every final state.
- s2n-bignum's notation in statements: `XREG' d` is the 64-bit register
  that the 5-bit field `d` names, `QREG' d` the 128-bit vector register,
  `registers :> element d` the x86 register `d`, and `GPR8 (Gpr d
  Lower_8)` the low byte of x86 register `d`.
  [statements/README.md](statements/README.md#variables-and-constants)
  lists them.
- Names are escaped: the plugin writes every character other than a
  letter or digit as `_` and two hex digits. So `sail_hl_ARM_5fADC64`
  is the root `ARM_ADC64` (`_5f` is `_`), and a definition shared by the
  models of the `arm-carry` suite starts with
  `sail_hl_shared_arm_2dcarry_` (`_2d` is `-`)
  ([names](backend/README.md#names)).

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
- `sail_hl_ARM_5fADC64` is the root exported from Sail. Its entry in
  [backend/arm.ml](backend/arm.ml) is

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
- `_SAFE_EQ`: agreement wherever s2n-bignum's safety guard holds (a
  condition on the initial state, such as an aligned stack pointer), a
  proof that the guard can hold, and the fact that s2n-bignum's relation
  is `ASSIGNS entirety` outside it. The exact shape is in
  [statements/README.md](statements/README.md#kinds).
- `_DIFF`: where the models differ, states that one relation permits and
  the other rejects.
- `_EXACT`: for the shina forms that differ, exactly which final states
  shina permits, in terms of s2n-bignum's relation.

[statements/README.md](statements/README.md) gives the exact statement
of each kind and the number of theorems of each.

| Sail model, pinned commit | Compared with s2n-bignum | Theorems | Result |
| --- | --- | ---: | --- |
| [sail-arm](https://github.com/rems-project/sail-arm) `f5bf6c3` | all 221 public definitions in `arm/proofs/instruction.ml`, as 1,404 forms | 1,404 | all agree; the 246 memory forms within s2n-bignum's safety guards |
| [sail-riscv](https://github.com/riscv/sail-riscv) `cd3f185` | all 48 RV32IM definitions in `riscv/proofs/instruction.ml`, as 50 forms | 50 | 48 of the 50 forms agree: the halfword and word accesses at every address, because the interpretation of `vmem_read` and `vmem_write` copies Sail's alignment test by hand and permits every final state for a misaligned access, as s2n-bignum does, so this does not check s2n-bignum's alignment guard against Sail; the 8 branches and jumps within s2n-bignum's alignment guards; ECALL and EBREAK differ: Sail has no successful outcome, s2n-bignum permits every final state |
| [shina-lab/sail-x86](https://github.com/shina-lab/sail-x86) `1829cb6` | 205 register forms of 68 of the 156 x86 instruction definitions in `x86/proofs/x86.ml`: 28 scalar and 40 AVX2 integer instructions, listed in [x86_forms.py](scripts/x86_forms.py) | 211 | 199 agree; the 6 RCL and RCR forms at 8 and 16 bits differ (each has an `_EXACT` and a `_DIFF` theorem) |
| [REMS sail-x86-from-acl2](https://github.com/rems-project/sail-x86-from-acl2) `0c6c023` | the 119 of those forms that this model implements | 119 | 100 agree; 19 differ |
| [Sail compiler](https://github.com/rems-project/sail) `3df5403` | runs the plugin; not itself compared | | |

[ci/versions.env](ci/versions.env) pins all five commits for both
checks. The 156 x86 definitions are the `x86_*` definitions other than
the 20 `x86_Exception_*` ones.

The 48 RV32IM definitions give 50 forms because s2n-bignum's single
definition `riscv_FENCE` serves FENCE, FENCE.TSO and PAUSE: the
FENCE.TSO and PAUSE theorems compare with `riscv_FENCE`
([coverage.py](scripts/coverage.py), `RV32`).

Five forms agree because their only effects are interpreted. Arm NOP
changes no state, and Arm BTI c changes only the branch-type state that
the export omits (`BTypeNext`, `BTypeCompatible`). RV32 FENCE, FENCE.TSO
and PAUSE call `sail_barrier`, which is interpreted as no change. For
these forms the theorem shows only that s2n-bignum changes nothing
else.

### What it rests on

Each theorem compares two HOL relations on machine states: one generated
from a Sail model, one from s2n-bignum. Nothing proves that the
generated relation means what the Sail code means. An error in any link
below can give a valid theorem about the wrong model. [What is not
proved](#what-is-not-proved) lists what is not claimed at all.

1. **HOL Light's kernel** checks every theorem in
   [statements/](statements/README.md), at the commit in
   [ci/versions.env](ci/versions.env). Each suite calls `check_axioms ()`
   after its last load, which fails if any axiom other than `INFINITY_AX`,
   `SELECT_AX` and `ETA_AX` exists. For a `_SAFE_EQ` theorem the kernel
   also checks that the guard holds for some operands and state, and that
   outside it s2n-bignum's relation is `ASSIGNS entirety`
   ([shape](statements/README.md#kinds)); `sail_hl_report`
   ([proofs/report.ml](proofs/report.ml)) refuses a `_SAFE_EQ` theorem
   whose conjuncts do not have this shape about one guard. Two caveats.
   Both sides use s2n-bignum's own state components (`XREG`, `QREG`,
   `SP`, `PC`, the flags, `memory :> bytes`, `events`, `riscv_gpr`, x86
   `registers :> element`), so an error in one of them would not show as
   a difference; the main ones are listed under "Taken from s2n-bignum,
   not checked" in the [interpretations](backend/README.md#interpretations).
   And the Sail proofs run on a different HOL Light from s2n-bignum's
   other jobs: `ci/versions.env` pins `HOL_LIGHT_COMMIT` for them, while
   `HOLLIGHT_COMMIT` in `.github/workflows/ci.yml` serves the rest. So
   library definitions that s2n-bignum's relations use, such as `word_sx`,
   `iword` and `aligned`, are those of this HOL Light. The risk is low,
   but the two pins are not tied together.
2. **The Sail compiler and z3.** The Sail frontend parses, typechecks and
   rewrites the upstream models at the commits in `ci/versions.env`; the
   Arm run omits upstream's A32, T32, SVE and SME files
   ([ci/README.md](ci/README.md#generation)). z3 answers the numeric
   questions of Sail and of the translator, and a wrong answer could, for
   example, drop a reachable branch. Its version is not pinned (CI
   installs the Ubuntu package), so the byte comparison of the generation
   check catches a change in answers between versions, not an error that
   both make. Sail gives z3 one second per question, so a slow machine
   can change the output, which the comparison then rejects. A wrong
   answer that removed an assertion only makes the generated relation
   permit more than Sail does; a wrong branch decision can change it in
   both directions. A model's header lists only the source code that z3
   removed; other z3-dependent choices appear only in the untracked
   translation log ([generated/README.md](generated/README.md#assumptions)).
3. **The translator**, with its binding simplification and its mapping
   of Sail primitives to HOL operations. Signedness and overflow of each
   primitive are written by hand. The simplification replaces a HOL term
   by an equal one and is tested on random terms. Details, and what the
   translator refuses, are in the [backend guide](backend/README.md).
4. **The architecture tables and the interpretations.** The tables
   select each form: the upstream function, its fixed arguments and the
   operand order. Sail typechecks every selected call, so an entry cannot
   pass the wrong types, but it can swap two operands of the same type or
   fix the wrong constant; the "Selected Sail call" comment before each
   root shows the call. The interpretations replace upstream functions
   and registers by fixed HOL meanings. The
   [interpretations](backend/README.md#interpretations) section says why
   each is acceptable and what it loses, and the generated `.context`
   files list each one with its replacement term.
5. **The scope lists.** Which theorems CI requires
   ([scripts/coverage.py](scripts/coverage.py),
   [scripts/x86_forms.py](scripts/x86_forms.py)) and what their
   right-hand sides say are written by hand. The "every public
   definition" claims rest on these lists matching s2n-bignum's decoder.
   CI checks only the set of public names; the form lists were compared
   with the clauses of `arm/proofs/decode.ml` by review, which is how the
   scalar `SHL Dd, Dn, #amount` form was found missing. The drivers'
   choice of the s2n-bignum side is not checked either
   (see [Coverage](#coverage) and [What is not proved](#what-is-not-proved)).
6. **Loading the model files.** The drivers replace some HOL functions
   while a model loads, to make loading faster. Each loader decides which
   term is defined, so an error in one gives valid theorems about another
   model ([proofs/README.md](proofs/README.md#loading-and-running)).
7. **The audit of the proof logs.** CI reads each suite's log, not HOL
   theorems, and compares it with `statements/`. A driver that printed a
   statement it had not proved would pass the audit; a text check of the
   sources makes this harder, but only against accidents and lazy
   subversion ([ci/README.md](ci/README.md#checking-the-proof-logs)).

## Checking one claim

Work backwards from a theorem to the Sail code it is about. The first
example is Arm; RV32 and x86 follow.

### Arm: `SAIL_HL_ARM_ADC64_EQ`

1. **Statement**: [statements/arm-carry.txt](statements/arm-carry.txt)
   gives exactly what is proved. To find the suite of another
   definition, see the [coverage
   map](docs/ARM-COVERAGE-MAP.md#which-suite-holds-a-definition).
2. **Proof**: [proofs/arm-carry.ml](proofs/arm-carry.ml) states and
   proves it.
3. **Model**: `sail_hl_ARM_5fADC64` in
   [generated/arm-carry.ml](generated/arm-carry.ml) is the root. Before
   it the file quotes its entry as "Selected Sail call", and before each
   definition it names the Sail code that definition came from by
   `filename:line`, here `src/instrs64.sail:194` in sail-arm;
   [generated/README.md](generated/README.md) says how to read a model.
   [ci/README.md](ci/README.md#reading-the-sail-sources) says how to
   check out the Sail sources at the pinned commits, or link to one line
   of them.
4. **Entry**: the `carry` table in [backend/arm.ml](backend/arm.ml)
   builds the entry: which upstream function, with which fixed
   arguments.
5. **Assumptions**: [generated/arm.context](generated/arm.context)
   lists the configuration of the Arm run and each interpretation its
   models use, such as `X_read`, with the HOL term that replaces it;
   [Interpretations](backend/README.md#interpretations) says what each
   one loses. A
   model whose header comment lists source code that z3 removed, as
   [generated/arm-addsub.ml](generated/arm-addsub.ml) does, shows that
   part of what z3 decided; arm-carry has none. The header is not the
   whole list: other choices that depend on z3, such as helper
   preconditions, the sign of a REMS shift amount and specialization
   widths, are only in the untracked translation log. z3 is trusted for
   all numeric questions, and its version is not pinned.

### RV32: `SAIL_HL_RV32_ADD_EQ`

1. **Statement**: [statements/rv32.txt](statements/rv32.txt), the only
   RV32 statement file:

   ```text
   |- forall rd rs1 rs2 s t.
          sail_hl_rv_5fRTYPE_5fADD rs2 rs1 rd s t <=>
          riscv_ADD (riscv_gpr rd) (riscv_gpr rs1) (riscv_gpr rs2) s t
   ```

   The root takes its fields in Sail's order, `rs2 rs1 rd` (the order
   of `execute_RTYPE`), and the statement quantifies over `rd rs1 rs2`.
2. **Proof**: [proofs/rv32.ml](proofs/rv32.ml) builds the theorem from
   a table row that pairs the root `sail_hl_rv_5fRTYPE_5fADD` with
   s2n-bignum's `riscv_ADD`.
3. **Model**: `sail_hl_rv_5fRTYPE_5fADD` in
   [generated/rv32.ml](generated/rv32.ml). Its "Selected Sail call" is
   `rv_RTYPE_ADD(rs2, rs1, rd) = execute_RTYPE(Regidx(rs2), Regidx(rs1),
   Regidx(rd), ADD)`, with "v0 is rs2, v1 is rs1, v2 is rd", which gives
   the mapping from root parameters to fields. The root calls a shared
   definition of `execute_RTYPE`, whose source is
   `extensions/I/base_insts.sail:237` in sail-riscv. The branches, JAL,
   JALR, ECALL and EBREAK are in `generated/rv32-control.ml`.
4. **Entry**: [backend/rv32.ml](backend/rv32.ml). The entries
   `rv_RTYPE_ADD` to `rv_RTYPE_AND` are built by one loop over the
   operation names, so search for `execute_RTYPE`, not for `ADD`.
5. **Assumptions**: [generated/rv32.context](generated/rv32.context).

### x86 (shina): `SAIL_HL_X86_ADD64_RR_EQ`

1. **Statement**:
   [statements/x86-arithmetic.txt](statements/x86-arithmetic.txt). The
   instruction ADD is in the `arithmetic` suite; the shift and rotate
   instructions are in `x86-shift` and the AVX2 ones in `x86-vector`
   (the [counts table](statements/README.md#counts) lists them):

   ```text
   |- forall d m s t.
          sail_hl_X86_5fADD64_5fRR d m s t <=>
          x86_ADD (registers :> element d) (registers :> element m) s t
   ```

   The statement is about two 64-bit registers named by the 4-bit fields
   `d` and `m`, and compares with `x86_ADD` from `x86/proofs/x86.ml`.
2. **Proof**: [proofs/x86-arithmetic.ml](proofs/x86-arithmetic.ml)
   loads the model and the claims. The claim for ADD, with the other
   ALU instructions, comes from the table `SAIL_HL_X86_GPR_OPERATIONS`
   in [proofs/x86-gpr-claims.ml](proofs/x86-gpr-claims.ml), not from
   `x86-arithmetic.ml` itself.
3. **Model**: `sail_hl_X86_5fADD64_5fRR` in
   [generated/x86-arithmetic.ml](generated/x86-arithmetic.ml). Its
   "Selected Sail call" is `X86_ADD64_RR(d, m) = exec_alu_reg_rm(ALU_ADD,
   struct GPRRef { gpr_idx = unsigned(d); has_rex = true },
   RM_reg(struct GPRRef { gpr_idx = unsigned(m); has_rex = true }), 64)`,
   with "v0 is d, v1 is m". The Sail source of `exec_alu_reg_rm` is
   `insn_alu.sail:66` in shina's sail-x86.
4. **Entry**: the `alu` list in
   [backend/x86_shina.ml](backend/x86_shina.ml). Names such as
   `X86_ADD64_RR` are built by loops over operations and widths, so
   search for `exec_alu_reg_rm`, not for `ADD64`.
5. **Assumptions**:
   [generated/x86-shina.context](generated/x86-shina.context). For REMS
   use `x86-rems-*` in place of `x86-*`,
   [backend/x86_rems.ml](backend/x86_rems.ml) and
   [generated/x86-rems.context](generated/x86-rems.context).

### Where to look

| | Arm | RV32 | x86, shina | x86, REMS |
| --- | --- | --- | --- | --- |
| Required forms (trusted) | `ARM_FAMILIES` in [coverage.py](scripts/coverage.py) | `RV32` in coverage.py | [x86_forms.py](scripts/x86_forms.py) | x86_forms.py (`REMS_BODIES`) |
| Statements | `statements/arm-<suite>.txt` | `statements/rv32.txt` | `statements/x86-{arithmetic,shift,vector}.txt` | `statements/x86-rems-{arithmetic,shift}.txt` |
| Proof | `proofs/arm-<suite>.ml` | `proofs/rv32.ml` | `proofs/x86-<suite>.ml`, with the claims files `x86-gpr-claims.ml`, `x86-multiply-claims.ml`, `x86-rcl-rcr-claims.ml` | `proofs/x86-rems-<suite>.ml` |
| Model | `generated/arm-<suite>.ml` | `generated/rv32.ml`, `rv32-control.ml` | `generated/x86-<suite>.ml` | `generated/x86-rems-<suite>.ml` |
| Entries | [backend/arm.ml](backend/arm.ml) | [backend/rv32.ml](backend/rv32.ml) | [backend/x86_shina.ml](backend/x86_shina.ml), form names in [x86.ml](backend/x86.ml) | [backend/x86_rems.ml](backend/x86_rems.ml) |
| Context | `arm.context` | `rv32.context` | `x86-shina.context` | `x86-rems.context` |
| Suite of a definition | [coverage map](docs/ARM-COVERAGE-MAP.md#which-suite-holds-a-definition) | one suite | [counts](statements/README.md#counts) | [counts](statements/README.md#counts) |

## What is not proved

- That the export preserves the meaning of the Sail code. The
  translator, the instruction tables and the interpretations of
  registers, memory and platform calls are trusted
  ([interpretations](backend/README.md#interpretations)).
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
  branches, JAL and JALR with unaligned targets.
- s2n-bignum's alignment guard on RV32 halfword and word accesses. The
  interpretation of `vmem_read` and `vmem_write` copies Sail's
  `is_aligned_addr` test by hand and, for a misaligned address, permits
  every final state in place of Sail's `plat_misaligned_exception`,
  whose outcome (proceed, access fault or misaligned exception) the
  platform chooses (`memory.misaligned` and the PMA regions). The
  theorems compare s2n-bignum's guard with that copy, not with Sail's
  code. With the default configuration Sail performs a misaligned access,
  about which s2n-bignum claims nothing.
- Events, which s2n-bignum's constant-time and memory-safety claims rest
  on. No event in any theorem is evidence from Sail: every event's
  presence, kind and size comes from an interpretation written to
  s2n-bignum's convention (Arm `BranchTo`, `BranchNotTaken` and
  `Mem_*`; RV32 `vmem_*` and the jump after `Retire_Success`), or, for
  the RV32 division event, from the statement itself. The Arm memory
  theorems erase the event lists. Where the other theorems keep
  events, they show only that the values fed into an event, such as a
  branch target or an RV32 address, agree with Sail's.
- Equality of fault outcomes. A reached Arm fault permits every final
  state.
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
  [docs/ARM-COVERAGE-MAP.md](docs/ARM-COVERAGE-MAP.md) gives the suite
  and forms of each Arm definition, grouped by profile.
- x86: only the register forms listed in x86_forms.py. A new definition
  in `x86/proofs/x86.ml` is not required automatically.

To cover a new instruction model, see [CONTRIBUTING.md](CONTRIBUTING.md).

## Model differences

The comparisons showed three errors in s2n-bignum's relations and two
open questions:

| Finding | Status | Details |
| --- | --- | --- |
| `arm_LDP` required a load for `LDP XZR, XZR`, although equal destinations are constrained unpredictable | corrected in awslabs/s2n-bignum#484 (`arm_LDP` and its stepping conversion); the decoder accepts the instruction, but no s2n-bignum function contains it, so no proof of s2n-bignum code depended on it | [Arm model differences](docs/ARM-DISCREPANCIES.md#duplicate-load-destinations) |
| 8- and 16-bit `x86_SHL` and `x86_SHR` fixed CF where it is undefined | corrected in awslabs/s2n-bignum#484; no decodable s2n-bignum code is affected | [x86 guide](docs/X86.md#shift-corrections) |
| 16-bit `x86_SHLD` and `x86_SHRD` fixed the result and flags for counts above 16 | as above | as above |
| 8- and 16-bit `x86_RCL` and `x86_RCR` leave OF undefined at whole-cycle counts, where shina keeps it | open: Intel's manual is ambiguous. s2n-bignum permits a superset of shina's final states (`_EXACT`), so this cannot invalidate a proof about s2n-bignum code | [x86 model differences](docs/X86-DIVERGENCES.md#rcl-and-rcr-at-whole-cycle-counts) |
| REMS `ROL` and `ROR` at masked count 0 leave OF undefined, where s2n-bignum preserves it | open: Intel's Operation pseudocode and its Flags Affected text disagree. REMS permits more final states than s2n-bignum, which is the direction in which a proof about s2n-bignum code could rely on behaviour that the REMS model does not guarantee | [x86 model differences](docs/X86-DIVERGENCES.md#rems-rol-and-ror-leave-of-undefined-at-count-zero) |

The other REMS forms that differ are not counted as errors in
s2n-bignum; [X86-DIVERGENCES.md](docs/X86-DIVERGENCES.md) classifies
them.

## How it works

```text
 pinned Sail models                         s2n-bignum's relations
 (sail-arm, sail-riscv, shina, REMS)        (arm/, riscv/, x86/proofs/)
          |                                            |
          | Sail compiler with the plugin              |
          | (backend/: translator and tables)          |
          v                                            |
 generated/<suite>.ml                                  |
 generated/<run>.context                               |
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

## Layout

| Path | What it holds |
| --- | --- |
| [backend/](backend/README.md) | the Sail plugin: the translator `sail_plugin_hol_light.ml`, the instruction tables per architecture, `entry.ml` |
| [generated/](generated/README.md) | the checked-in HOL models and the `<run>.context` files |
| [proofs/](proofs/README.md) | HOL Light proofs: one driver per suite, shared lemma files, loaders and `report.ml` |
| [statements/](statements/README.md) | the recorded statement of every theorem |
| [scripts/](scripts/README.md) | `coverage.py` and `x86_forms.py`, the lists of required forms (trusted), and `inline-proof.ml` |
| [ci/](ci/README.md) | `check.py`, `setup.sh` and `versions.env` |
| [docs/](docs/) | model differences and per-architecture notes |
| `tests/` | unit tests of the plugin and the tooling |
| `build.sh`, `run.sh`, `check-proof.sh` | build the plugin, run it on one family, run one suite's proof ([ci/README.md](ci/README.md#scripts)) |
| `_build/` | scratch output of the scripts and checks; Git ignores it and it can be deleted |
| [CONTRIBUTING.md](CONTRIBUTING.md) | how to add an instruction |

## How to use

Each check needs its own toolchain, which `ci/setup.sh` builds at the
pinned revisions. Prerequisites on Ubuntu: `build-essential git opam m4
pkg-config libgmp-dev`, plus `libpcre2-dev` and `xdot` (a system
dependency that opam needs to build camlp5) for the proof check and `z3`
for generation; Python 3.9 or later. Use a new shell for each toolchain.

The generated models and the statements are in the tree, so you can
audit a claim by reading, as in [Checking one claim](#checking-one-claim),
without running anything. The proof check needs HOL Light but not Sail.

Resources, measured on a 64-core machine: generation takes about 700 s
with 16 workers per compiler process and peaks at about 33 GiB of
memory; the full proof check takes about 550 s with `--jobs 16`; one
small suite such as `arm-hints` takes about 95 s, including the Arm base
that every Arm suite links ([ci/README.md](ci/README.md#time-and-memory)).

### Quick check of one suite

```sh
SAIL_HOL_CI_PREFIX=$HOME/sail-hol-proofs \
  bash tools/sail/ci/setup.sh proofs
source $HOME/sail-hol-proofs/environment.sh
python3 tools/sail/ci/check.py proofs arm-hints
```

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

`check.py generate` only checks, and never writes to `generated/`. To
replace the checked-in models or statements after an intended change,
follow [Refreshing the checked-in
files](ci/README.md#refreshing-the-checked-in-files). The tools, their
options, the logs and the environment variables are in
[ci/README.md](ci/README.md).
