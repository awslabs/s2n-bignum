# Generated HOL models

Each `<suite>.ml` here holds the HOL Light definitions exported from Sail
for one suite; the RV32 suite has two, `rv32.ml` and `rv32-control.ml`
(the branches, JAL, JALR, ECALL and EBREAK). They come from the Sail
models pinned in [ci/versions.env](../ci/versions.env), through the
[plugin](../backend/README.md). Each generation run, one per
architecture and x86 source, also writes a context file, `<run>.context`
([below](#assumptions)). The generation check regenerates all of them and
compares them byte for byte with these files; the proof check loads the
models into HOL Light ([CI](../ci/README.md)).

Do not edit these files by hand. After an intended change to a source or
to the plugin, run `ci/check.py refresh`, review the diff of the models
and reports, then run both checks.

## Reading a model

Each root is a `new_definition` named as described in the
[plugin guide](../backend/README.md#names): the plugin writes every
character other than a letter or digit as `_` and two hex digits, so
`sail_hl_ARM_5fADC64` is the root `ARM_ADC64` (`_5f` is `_`), and
`sail_hl_shared_arm_2dcarry_...` is a definition shared by the models of
the `arm-carry` suite (`_2d` is `-`). Applied to its parameters it
is `\(s:<state>) (t:<state>). ...`, which holds when `t` is a final state
that the Sail code permits from `s`. The parameters are any component
parameters (`reg_PSTATE`, a branch's `reg__5fPC`, REMS's flags and RIP),
then the entry's fields. Before each definition the file gives:

- the Sail declarations and bodies it came from, as
  `(* Sail source "<name>", "<path>:<line>" *)`, including top-level
  values (`"<name> global"`). For a root, the list covers the sources of
  every helper that the root reaches, not only of the root's own
  function, so it can be several lines long. The source text itself is not copied; the
  exporter's `--hol-light-quote-sources` option adds it, for reading a
  model beside its source;
- for a root, its entry, as `(* Selected Sail call`, followed by the HOL
  parameter that holds each field, such as "v0 is d, v1 is n, v2 is m";
- for a shared definition, its `Width policy`: `polymorphic` if it was
  exported for every word width, `specialized` if for fixed widths;
- where they apply, the assumptions the definition uses
  (`Source assumptions:`), each supplied input (`Source input boundary:`)
  and a notice when Arm FPSR or BType writes are omitted.

The translator binds each evaluated Sail value with `let`, in Sail's
evaluation order, and drops the bindings the definition does not use
([plugin guide](../backend/README.md#relation-interface)). The variable
numbers `v0`, `v1`, ... therefore have gaps.

A stateful shared definition takes the instruction's initial state
`entry` as well as the current state `s`, so that reads of the
instruction's PC see its value before any write. A model with shared
definitions ends by rebinding each root's OCaml name to a theorem that
the kernel derives from its definition, with the shared definitions
unfolded and numerals reduced (`let ... = CONV_RULE ...`). Proofs that use
the name get that theorem; the constant is unchanged.

## Source checkouts

Source paths are relative to the model root of the pinned checkout:

| Models | Checkout and root | Example path |
| --- | --- | --- |
| `arm-*.ml` | sail-arm, `arm-v9.4-a/` | `src/v8_base.sail` |
| `rv32*.ml` | sail-riscv, `model/` | `extensions/I/base_insts.sail` |
| `x86-arithmetic.ml`, `x86-shift.ml`, `x86-vector.ml` (shina) | shina-lab/sail-x86, `model/` | `insn_alu.sail` |
| `x86-rems-*.ml` | sail-x86-from-acl2, `model/` | `rotates_spec.sail`, given with a varying number of leading `./`, such as `././././rotates_spec.sail` |
| any | Sail, `lib/` | `sail/lib/vector.sail`, and `corelib.sail` from `lib/core/` |

The definitions also translate Sail compiler-library helpers.

## Assumptions

What the models rest on beyond the translation of the Sail code is in
two places.

The context file of a run, `arm.context`, `rv32.context`,
`x86-shina.context` or `x86-rems.context`, holds what the whole run
shares:

- **Configuration**: the facts fixed for the run, such as the Arm
  features taken as implemented and the RV32 extensions taken as off.
- **Interpretations**: each Sail call or construct that the translator
  did not translate but replaced by a fixed HOL term, once for the run,
  with that term on the line below:

  ```text
  X_read(a, 64)
    ~> read (XREG (num_of_int a)) s
  AArch64_SPAlignmentFault()
    ~> every final state
  ```

  `a`, `b`, ... stand for the call's arguments, `s` for the state before
  it, `s'` for the state after it and `s0` for the state at the start of
  the instruction. Two conventions help in reading an entry:

  - A term of the form `s' = ...` is a state change: the call has an
    effect, and the term gives the state after it. Any other term is a
    value: the call returns it. So `read (XREG ...) s` is what
    `X_read` returns, and `s' = s` says that a call changes nothing.
  - One Sail call can appear more than once with different terms. The
    terms then differ in the state they read: `s`, the state at the
    call, or `s0`, the entry state. For example, `BranchNotTaken(a, b)`
    appears with `read reg__5fPC s` and with `read reg__5fPC s0`. The
    `s` form arises when the current state is still the entry state, so
    that `s` and `s0` are the same state; the `s0` form arises when it
    is not.

  A literal argument is shown by its value, so a call whose literal
  arguments select different terms, such as the register width of
  `X_read`, has one entry for each. The term is printed from the one the
  translator emitted into the models, with let-bound names replaced by
  their values and without type annotations.
  [interpretations](../backend/README.md#interpretations) says what each
  interpretation loses. Sail library primitives with their exact meaning, such as
  `add_bits`, are left out.

The context file of a model is the one of its run: `arm-*.ml` use
`arm.context`, `rv32.ml` and `rv32-control.ml` use `rv32.context`,
`x86-arithmetic.ml`, `x86-shift.ml` and `x86-vector.ml` use
`x86-shina.context`, and `x86-rems-*.ml` use `x86-rems.context`.

A comment at the top of a model, after its first line, holds what is
specific to it. A model with nothing specific has no such comment (35 of
the 76 models have one), and then only its run's context file applies.
Sail source text in it is quoted as `{sail_source|...|sail_source}`, as
in the model's other comments:

- **Supplied inputs** (x86): instruction bytes that the body would fetch,
  supplied as root parameters instead.
- **Removed by a z3 decision**: each conditional that z3 decided and
  each assertion that z3 proved during translation, as its source text,
  with its `file:line`, the function it is in, what the model keeps, and
  the forms from which it was reached:

  ```text
     Removed by a z3 decision (on the paths where each was made)
       {sail_source|assert(constraint(('N > 0 & 'amount >= 0)))|sail_source}
         at src/v8_base.sail:35864, in ShiftReg
         z3 proves it, so the model has no check here
         reached from arm_ADD32_SHIFT arm_ADD64_SHIFT
  ```

  If z3 were wrong, the model would permit a normal outcome where Sail
  stops, so the generated relation would permit more than Sail does; a
  wrong decision about a conditional can change it in both directions.
  The translator copies code along each path, so a decision
  applies on the paths where it was made. A condition whose translation
  is already a constant, such as a test of an argument that the entry
  fixes or of the configuration, is not listed: it follows from the
  entry and the configuration like any other translated code. The
  translation log lists those too.

This list is not the whole of z3's footprint. The header lists only
source code that z3 removed. Other choices that depend on z3's answers
select the emitted term without leaving a trace in the header: the
preconditions of helpers that the translator proved
(`proved-numeric-argument-fact`), whether a REMS shift amount is known
to be nonnegative (which decides between `word_shl` and an unknown word)
and the widths at which a helper is specialized. They appear only in the
untracked translation log (below). z3 is trusted for all numeric
questions ([What it rests on](../README.md#what-it-rests-on)),
and its version is not pinned: the generation check's byte comparison
catches a change in z3's answers between versions, not an error that
both versions make.

The translator refuses to write a model if an interpretation that it
registered has no recorded Sail call and term, so no registered
interpretation can reach a model unlisted. The check works on the names
that the translator registers when it applies a cut or an interpreted
construct. It cannot see a translator case that applied an
interpretation without registering it; reading each case guards against
that.

Generation also writes `<suite>.translation-log`, which is not checked
in: every choice the translator made, one record per line, including
the helpers it translated and shared and the numeric facts it proved.
The backend tests read it, and it helps when debugging the translator.
