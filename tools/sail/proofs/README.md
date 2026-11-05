# Proof files

Every file here is OCaml run by HOL Light. Each suite, named as in
[statements/](../statements/README.md), has one driver
`proofs/<suite>.ml`, which holds the suite's proof.
[check-proof.sh](../check-proof.sh) compiles a driver with the files it
loads and runs it in a fresh kernel; `ci/check.py proofs` does this for
every suite and audits the logs ([TRUST.md](../TRUST.md)).

## Drivers

Each driver has, in this order:

1. a comment that says what the suite proves;
2. its loads: s2n-bignum's `arm/proofs/base.ml`,
   `riscv/proofs/base.ml` or `x86/proofs/base.ml`,
   [report.ml](report.ml), the loaders and shared files it uses, and the
   model from `_build/<suite>.ml` (some of these through a shared file);
3. the lemmas, tactics and claims of the suite;
4. `check_axioms ();;`;
5. the line that prints its completion marker.

Small suites state their theorems literally; larger ones build names and
statements from tables. An Arm or x86 theorem name is `SAIL_HL_`, the
root's entry name with `arm_` written as `ARM_`, and the kind, as in
`SAIL_HL_ARM_LDR64_GPR_UIMM_SAFE_EQ` for `arm_LDR64_GPR_UIMM`; RV32 names
use the instruction, as in `SAIL_HL_RV32_ADD_EQ`. To find where a suite
builds its names, search its files for `"SAIL_HL_`. The drivers load the
models from `_build/`, where `ci/check.py proofs` copies
[generated/](../generated/README.md); to run `check-proof.sh` directly,
copy them yourself.

[report.ml](report.ml) defines `sail_hl_report`, the only code that prints
a theorem; `check_proof_sources` refuses theorem printing anywhere else.
It refuses a theorem with hypotheses or free variables, then prints the
name and the statement.

## Shared files

| File | Used by | Holds |
| --- | --- | --- |
| [arm-lemmas.ml](arm-lemmas.ml) | many Arm suites | word, flag and state-component facts |
| [arm-shift-lemmas.ml](arm-shift-lemmas.ml) | arm-bitfield, arm-crypto-bitwise, arm-shift, arm-logical-lemmas.ml | Sail's ROR helper as a word rotation |
| [arm-logical-lemmas.ml](arm-logical-lemmas.ml) | arm-addsub, arm-logical | the shifted-register operand; defines `sail_hl_arm_logical_kind` |
| [arm-branch-state-lemmas.ml](arm-branch-state-lemmas.ml) | arm-branch-conditional, arm-branch-unconditional-lemmas.ml | PC and event component laws |
| [arm-branch-unconditional-lemmas.ml](arm-branch-unconditional-lemmas.ml) | arm-branch-basic, arm-branch-absolute-execute | offset facts and the branch tactic |
| [arm-vector-duplicate-lemmas.ml](arm-vector-duplicate-lemmas.ml) | DUP, INS, FMOV, FCSEL, TBL and saturating-narrow suites | lane extraction and register writes |
| [arm-vector-model-parameters.ml](arm-vector-model-parameters.ml) | vector suites whose roots take configuration components | builds a claim's left side, quantifying every such component with its exact type |
| [arm-vector-multiply-long-support.ml](arm-vector-multiply-long-support.ml) | several vector suites | lane packing of products and widened values |
| [arm-vector-pair-add-support.ml](arm-vector-pair-add-support.ml), [arm-vector-permute-support.ml](arm-vector-permute-support.ml) | the pairwise-add suites; TRN, UZP and ZIP | proof steps for those suites |
| [arm-memory-support.ml](arm-memory-support.ml) | the six arm-memory suites | everything they share: `sail_hl_arm_memory_observed`, the guard and claim builder, the tactics; each suite holds its own forms and tactic |
| [x86-gpr-lemmas.ml](x86-gpr-lemmas.ml), [x86-arithmetic-lemmas.ml](x86-arithmetic-lemmas.ml) | x86-arithmetic, x86-shift, x86-rems-* | flag, register-view and write-ordering facts |
| [x86-gpr-claims.ml](x86-gpr-claims.ml), [x86-multiply-claims.ml](x86-multiply-claims.ml) | x86-arithmetic (gpr claims also through x86-rems-lemmas.ml) | the ALU, unary and multiply claims |
| [x86-rcl-rcr-claims.ml](x86-rcl-rcr-claims.ml) | x86-shift | the six `_DIFF` theorems, derived from `_EXACT` |
| [x86-rems-lemmas.ml](x86-rems-lemmas.ml), [x86-rems-shift-lemmas.ml](x86-rems-shift-lemmas.ml) | x86-rems-arithmetic, x86-rems-shift | defines `sail_hl_x86_core`; normalization of REMS bodies |
| [x86-vector-lemmas.ml](x86-vector-lemmas.ml) | x86-vector, x86-arithmetic-lemmas.ml | integer-to-word identities and a normalizer for lane loops |
| [tuple-apply-conv.ml](tuple-apply-conv.ml) | arm-addsub, arm-memory-support.ml, x86-vector-lemmas.ml, x86-rems-lemmas.ml | a conversion for paired `let` bindings |

## Loading and running

These files change how a model loads or how a suite runs, not what it
proves. Each is trusted; [TRUST.md](../TRUST.md#from-model-file-to-kernel-term)
lists their users.

- [fresh-model.ml](fresh-model.ml) defines each generated equation with
  `new_basic_definition`, without HOL's search for an equal earlier
  definition.
- [arm-memory-model-loader.ml](arm-memory-model-loader.ml) records the
  memory models' equations so that the claims can find a root by name.
- [proof-fork.ml](proof-fork.ml) proves the claims of the largest suites
  in `SAIL_HOL_PROOF_FORKS` forked processes (`ci/check.py` sets 4) and
  prints their output in order. It does not check that each claim runs
  in exactly one child; the log audit does, by requiring each theorem
  exactly once.
