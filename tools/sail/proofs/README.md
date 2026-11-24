# Proof files

Every file here is OCaml run by HOL Light. Each suite, named as in
[statements/](../statements/README.md), has one driver
`proofs/<suite>.ml`, which holds the suite's proof.
[check-proof.sh](../check-proof.sh) compiles a driver with the files it
loads and runs it in a fresh kernel; `ci/check.py proofs` does this for
every suite and audits the logs ([how](../ci/README.md#checking-the-proof-logs)).

## Drivers

Each driver has, in this order:

1. a comment that says what the suite proves;
2. its loads: `riscv/proofs/base.ml` or `x86/proofs/base.ml` for those
   architectures, [report.ml](report.ml), the loaders and shared files it
   uses, and the
   model from `_build/<suite>.ml` (some of these through a shared file);
3. the lemmas, tactics and claims of the suite;
4. `check_axioms ();;`;
5. the line that prints its completion marker.

Arm drivers expect `arm/proofs/base.ml` to be loaded first, either by the
native template or explicitly in an interactive session as described
[below](#loading-and-running).

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
| [arm-memory-support.ml](arm-memory-support.ml) | the eight arm-memory suites | everything they share: `sail_hl_arm_memory_observed`, the guard and claim builder, the tactics; each suite holds its own forms and tactic |
| [x86-gpr-lemmas.ml](x86-gpr-lemmas.ml), [x86-arithmetic-lemmas.ml](x86-arithmetic-lemmas.ml) | x86-arithmetic, x86-shift, x86-rems-* | flag, register-view and write-ordering facts |
| [x86-gpr-claims.ml](x86-gpr-claims.ml), [x86-multiply-claims.ml](x86-multiply-claims.ml) | x86-arithmetic (gpr claims also through x86-rems-lemmas.ml) | the ALU, unary and multiply claims |
| [x86-rcl-rcr-claims.ml](x86-rcl-rcr-claims.ml) | x86-shift | the six `_DIFF` theorems, derived from `_EXACT` |
| [x86-rems-lemmas.ml](x86-rems-lemmas.ml), [x86-rems-shift-lemmas.ml](x86-rems-shift-lemmas.ml) | x86-rems-arithmetic, x86-rems-shift | defines `sail_hl_x86_core`; normalization of REMS bodies |
| [x86-scalar-lemmas.ml](x86-scalar-lemmas.ml) | x86-move, x86-select, x86-bit | the tactic for roots that keep their decoder steps |
| [x86-select-lemmas.ml](x86-select-lemmas.ml) | x86-select | the conditional-move, set, extension and byte-swap facts, and the select tactic |
| [x86-count-lemmas.ml](x86-count-lemmas.ml) | x86-count | Sail's branchless popcount, ctz and clz as `word_popcount`, `word_ctz` and `word_clz`, and the facts for the scan statements and the POPCNT event |
| [x86-avx2-lemmas.ml](x86-avx2-lemmas.ml) | x86-avx2, x86-sse | lane facts and tactics for byte shuffles, blends and element inserts |
| [x86-sse-lemmas.ml](x86-sse-lemmas.ml) | x86-sse, x86-aes | `SIMD128_SSE` as a read of the low 128 bits and a `word_insert` into the 512-bit register, and the statement of an SSE form |
| [x86-aes-lemmas.ml](x86-aes-lemmas.ml) | x86-aes | the evaluator that proves a byte function equal to a table in 256 cases, and the packing of sixteen bytes |
| [x86-vector-lemmas.ml](x86-vector-lemmas.ml) | x86-vector, x86-avx2, x86-sse, x86-aes, x86-arithmetic-lemmas.ml | integer-to-word identities, a normalizer for lane loops and the tactic that compares a generated vector root with s2n-bignum |
| [tuple-apply-conv.ml](tuple-apply-conv.ml) | arm-addsub, arm-memory-support.ml, x86-vector-lemmas.ml, x86-rems-lemmas.ml | a conversion for paired `let` bindings |

## Loading and running

These files change how a model loads or how a suite runs, not what it
proves. Each is trusted: a loader decides which term is defined, so an
error in one gives valid theorems about another model.

- `ci/check.py proofs` copies `generated/` to `_build/`, where the
  drivers load it, and checks afterwards that neither copy changed.
- [check-proof.sh](../check-proof.sh) expands each driver and the files it
  loads into one OCaml source and compiles it. `ci/check.py proofs` first
  compiles `arm/proofs/base.ml` once with `check-proof.sh arm-base`.
  Arm drivers contain proof bodies, not a base load. With the compiled
  base present, a small native template opens `Hol_lib`, `Hol_loader`
  and `Arm_common_base`; stock `inline_load.ml -omit-prelude` expands
  the body, and `hol.sh compile/link` build it with the base module.
  Without the compiled base, the template loads the full base first.
  Each linked module initializes in the new proof process.
  Interactive use loads the base before a driver, for example:

  ```ocaml
  loadt "arm/proofs/base.ml";; loadt "tools/sail/proofs/arm-carry.ml";;
  ```

- Loaders replace HOL functions while a model loads, to make loading
  faster. Each is defined before the model it loads.
  - [fresh-model.ml](fresh-model.ml) defines each equation with
    `new_basic_definition`, without HOL's search for an equal earlier
    definition, and evaluates the model's final rewrite by value. Used by
    arm-addsub, arm-vector-poly, arm-vector-table,
    arm-vector-multiply-accumulate-long, the arm-memory suites, the shina
    suites other than x86-arithmetic and x86-shift, and the REMS suites.
  - [arm-memory-model-loader.ml](arm-memory-model-loader.ml) records the
    memory models' equations so that the claims can find a root by name;
    used by the arm-memory suites.
  - Local versions in a driver: `REWRITE_RULE` in arm-vector-poly.ml;
    `REWRITE_RULE` and `CONV_RULE` that return the theorem unchanged in
    x86-rems-arithmetic.ml and x86-rems-shift.ml; `new_definition` in
    the drivers of the shina suites that use fresh-model.ml.
