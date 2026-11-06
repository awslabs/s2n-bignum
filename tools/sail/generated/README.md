# Generated HOL models

Each `<suite>.ml` here holds the HOL Light definitions exported from Sail
for one suite; the RV32 suite has two, `rv32.ml` and `rv32-control.ml`
(BNE and JALR). They come from the Sail models pinned in
[ci/versions.env](../ci/versions.env), through the
[plugin](../backend/README.md). Beside each model, `<suite>.dependencies`
is the dependency report that generation wrote with it. The generation
check regenerates both and compares them byte for byte with these files;
the proof check loads the models into HOL Light ([CI](../ci/README.md)).

Do not edit these files by hand. After an intended change to a source or
to the plugin, run `ci/check.py refresh`, review the diff of the models
and reports, then run both checks.

## Reading a model

Each root is a `new_definition` named as described in the
[plugin guide](../backend/README.md#names). Applied to its parameters it
is `\(s:<state>) (t:<state>). ...`, which holds when `t` is a final state
that the Sail code permits from `s`. The parameters are any component
parameters (`reg_PSTATE`, a branch's `reg__5fPC`, REMS's flags and RIP),
then the entry's fields. Before each definition the file gives:

- the Sail declarations and bodies it came from, as
  `(* Sail source "<name>", "<path>:<line>" *)`, including top-level
  values (`"<name> global"`). The source text itself is not copied; the
  exporter's `--hol-light-quote-sources` option adds it, for reading a
  model beside its source;
- for a root, its entry, as `(* Selected Sail call`, followed by the HOL
  parameter that holds each field, such as "v0 is d, v1 is n, v2 is m";
- for a shared definition, its `Width policy`: `polymorphic` if it was
  exported for every word width, `specialized` if for fixed widths;
- where they apply, the assumptions the definition uses
  (`Source assumptions:`), each supplied input (`Source input boundary:`)
  and a notice when Arm FPSR or BType writes are omitted.

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

## Dependency reports

A report lists what its whole model file relies on, not each theorem: one
record per line, grouped by kind. The last column says which part
of [TRUST.md](../TRUST.md) the record belongs to.

| Records | Meaning | Trusted as |
| --- | --- | --- |
| `root` | an exported root | instruction tables |
| `inlined`, `inlined-global`, `inlined-mapping` | an upstream function, top-level value or mapping that was translated | translator |
| `shared-function`, `specialization-required` | a shared definition and the widths it fixes; an attempt to share that failed, with the reason | translator |
| `primitive-contract` | a cut, primitive or interpretation given a fixed HOL meaning, such as `X_read`, `add_atom` or `Arm-FPSR-write-exclusion` | interpretations, primitive mapping |
| `configured-assumption`, `used-assumption` | the facts the table fixes for the whole run, and those that this file's translation used | interpretations |
| `disabled-extension` | an extension treated as off: RV32 `Ext_Zca` and `Ext_Zicfilp`, Arm `Arm-GCS` and `Arm-SPE-sampling` | interpretations |
| `successful-check` | a check or access assumed to succeed, such as `Arm-AdvSIMD-enabled-access` | interpretations |
| `statically-proved-assertion`, `proved-numeric-argument-fact` | an assertion, with its source location, or a precondition of a call, proved with z3 during translation | z3, translator |
| `guarded-assertion` | an assertion kept in the relation, which permits no final state where it fails, with its source location | translator |
| `statically-selected-branch` | a conditional at a source location that the translator decided, and the branch it kept (`then` or `else`) | z3, translator |
| `unobserved-undefined-local`, `unrolled-static-loop` | an unknown that is never read; a loop expanded with fixed bounds | translator |
| `source-input-boundary` | a supplied input: the fetch it replaces, its parameter and source span | interpretations |
| `state-computation`, `state-computation-root`, `normal-retirement-only`, `normal-retirement-root` | how the roots end: with a computed final state, or (the RV32 branches, jumps, ECALL and EBREAK) only by successful retirement | translator, interpretations |
