# What is trusted

Each theorem here compares two HOL relations on machine states: one
generated from a Sail model, one from s2n-bignum. HOL Light's kernel
checks that comparison. Nothing proves that the generated relation means
what the Sail code means; that rests on the parts listed on this page,
as do the choice of what to compare and the check of the proof logs. An
error in any of them can give a valid theorem about the wrong model. The
[README](README.md#what-is-not-proved) lists what is not claimed at all.

## What the kernel checks

- Every theorem in [statements/](statements/README.md), by HOL Light at
  the commit in [ci/versions.env](ci/versions.env). Each suite calls HOL
  Light's `check_axioms ()` after its last load. It fails if any axiom
  other than `INFINITY_AX`, `SELECT_AX` and `ETA_AX` exists.
- That each safety guard holds for some operands and state: this is the
  first conjunct of each `_SAFE_EQ` theorem.
- s2n-bignum's relations (`arm/proofs/instruction.ml`,
  `riscv/proofs/instruction.ml`, `x86/proofs/x86.ml`) are what is being
  checked. The interpretations below are written in s2n-bignum's own
  state components, such as `XREG`, `QREG`, `SP`, `PC`, the flags,
  `memory :> bytes`, `events`, `riscv_gpr` and x86 `registers :> element`.
  Both sides use the same definitions, so an error in one of these
  components would not show as a difference.

## From Sail source to generated model

| Component | Role | Where |
| --- | --- | --- |
| Sail frontend | Parses, typechecks and rewrites the upstream model; computes effects | Sail at the commit in `ci/versions.env` |
| z3 | Answers Sail's and the translator's numeric questions; a wrong answer could, for example, drop a reachable branch. Sail gives it one second per question, so a slow machine can change the output, which the byte comparison then rejects | not pinned: CI installs the Ubuntu package; `check.py generate` gives each compiler process a fresh, empty answer file |
| Upstream checkouts | The models compared | `ci/versions.env`; the Arm run omits upstream's A32, T32, SVE and SME files ([ci/README.md](ci/README.md#generation)) |
| Translator | Turns checked Sail bodies into HOL definitions | [backend/sail_plugin_hol_light.ml](backend/sail_plugin_hol_light.ml), [backend/entry.ml](backend/entry.ml); [guide](backend/README.md) |
| Primitive mapping | Gives each Sail primitive, such as `add_atom` or `sub_bits`, a HOL operation; signedness and overflow are written by hand | the primitive cases of `call` in the translator |
| Instruction tables | Select each form: upstream function, fixed arguments, operand order. Some entries compute with fields (an encoded shift plus one, LSL's immr and imms). For shina's INC, DEC, SHLD and SHRD the entry reads the registers, calls the upstream helper and writes its result; for MUL and one-operand IMUL it reads the source and the helper writes. Upstream's dispatch code for these forms is not compared | [arm.ml](backend/arm.ml), [rv32.ml](backend/rv32.ml), [x86_shina.ml](backend/x86_shina.ml), [x86_rems.ml](backend/x86_rems.ml), [x86.ml](backend/x86.ml); each generated root quotes its entry as "Selected Sail call" |
| Interpretations | Replace upstream functions and registers by fixed HOL meanings | the next section |

Sail typechecks every selected call, so an entry cannot pass the wrong
types. It can still swap two operands of the same type or fix the wrong
constant. The "Selected Sail call" comment before each root shows the
call and which HOL parameter holds which source field.

## Interpretations

A **cut** removes the body of a named upstream function and gives the
translator's HOL meaning instead. The table files list the cuts:
`contracts` and `faults` in [arm.ml](backend/arm.ml), `contracts` in
[rv32.ml](backend/rv32.ml), [x86_shina.ml](backend/x86_shina.ml) and
[x86_rems.ml](backend/x86_rems.ml). Some names are interpreted without a
cut; the table files list those too, with the translator case that
handles them. The rows marked "in the proofs", and the instantiations of
`_PC` and of REMS's `rflags` and `rip`, are choices made in the proof
drivers. A register with no row becomes a component parameter
`reg_<name>`, which each theorem quantifies, so nothing is assumed about
its value.

| Interpretation | HOL meaning | What is lost |
| --- | --- | --- |
| Sail `undefined` (all sources) | a fresh value of its type, chosen independently at each evaluation and bound existentially | nothing, if Sail's `undefined` means "any value" |
| assertion, `exit()` (all sources) | a false assertion or `exit()` permits no final state | executions in which an assertion fails |
| Arm `X_read`, `X_set` | s2n-bignum's `XREG` and `WREG`; register 31 reads zero and ignores writes; a W write clears the upper half | nothing beyond s2n-bignum's own registers |
| Arm `V_read`, `V_set` | `DREG` and `QREG`, the low 128 bits of each vector register; a narrower write clears the rest | SVE state above bit 127; the setter's vector-length and SVE checks |
| Arm `SP_read`, `SP_set` | HOL `SP`, the active stack pointer | which of `SP_EL0` to `SP_EL3` is active; the inactive ones |
| Arm `CheckFPEnabled64`, `CheckFPAdvSIMDEnabled64`, `AArch64_CheckFPAdvSIMDEnabled` | succeed and change no state; the argument is evaluated | the permission checks and traps inside them |
| Arm `BranchTo`, `BranchNotTaken` | `BranchTo` writes the target to `PC` as given; both append an `EventJump` from the instruction's PC | upstream's `AArch64_BranchAddr`, which with top-byte-ignore replaces bits 63 to 56 of the target from bit 55, and the BRBE and SPE branch hooks. Branches agree on targets that Sail would change |
| Arm `IsFeatureImplemented` | true for `FEAT_AA64EL0`, `FEAT_PMULL`, `FEAT_AFP` and `FEAT_SME` (`Arm.assumptions`), false for `FEAT_GCS`; `FEAT_LSE2` reads the quantified `reg_FlatHaveLSE2`; any other feature stops generation | processors without these features or with GCS |
| Arm initial `PSTATE.nRW = 0`, `PSTATE.SM = 0` (`Arm.assumptions`) | non-streaming AArch64 execution; a write that could change them stops generation | AArch32 and streaming mode |
| Arm `PSTATE` (no cut) | N, Z, C, V are the HOL flags; EL, BTYPE and nRW come from the quantified `reg_PSTATE`; the other fields are dropped; a write of the whole of `PSTATE` stops generation | the dropped fields |
| Arm `SCTLR_read__1` | the quantified `reg_SCTLR_5fread_5f_5f1`, which decides SP alignment checks | nothing |
| Arm `CreateAccDescGPR`, `CreateAccDescASIMD` | return the quantified `reg_FlatAccDescGPR` or `reg_FlatAccDescASIMD`, change no state and never fault; the arguments are evaluated | the checks and state updates inside them |
| Arm `Mem_read`, `Mem_set`, `Mem_read__1`, `Mem_set__1` | read or write 1, 2, 4, 8 or 16 bytes of `memory` at the 64-bit address and append an `EventLoad` or `EventStore`; they always succeed | address translation, permissions, tag checks, aborts, device memory, atomicity |
| Arm `BigEndian` | false; the argument is evaluated | big-endian accesses |
| Arm `EndOfInstruction` | ends the instruction at the state reached | nothing |
| Arm `AArch64_SPAlignmentFault` and `throw(Error_Undefined())` | permit every final state; any other fault stops generation | the fault and what it preserves: a theorem can hold although Sail faults |
| Arm `SPESampleInFlight` (no cut) | false | statistical profiling |
| Arm writes to `FPSR`, `BTypeNext`, `BTypeCompatible` (no cut) | omitted; the value is still computed, and reads use quantified components | FPSR, including the saturation flag QC, branch-target metadata, and any later code that reads them |
| Arm `_PC` (no cut) | the instruction's entry PC, read through a component parameter and never written. The statements of the arm-address and branch suites instantiate it as `PC :> evaluate (\pc. word_sub pc (word 4))`, because s2n-bignum runs an instruction after PC has advanced by 4 | nothing, if Sail's `_PC` is the address of the instruction |
| RV32 configuration | [rv32.json](backend/rv32.json): 32-bit registers, all 32 integer registers | RV64 and the E extension |
| RV32 `rX_bits`, `wX_bits` | s2n-bignum's `riscv_gpr`, where register 0 is a read-only zero | nothing beyond s2n-bignum's own registers |
| RV32 `get_arch_pc`, `get_next_pc`, `set_next_pc`, `PC` | `get_arch_pc` is `riscv_instruction_pc` of the entry state, HOL `PC` minus 4; `get_next_pc` reads and `set_next_pc` writes HOL `PC`; a direct write to `PC` stops generation | nothing, if s2n-bignum's PC convention holds |
| RV32 `vmem_read`, `vmem_write` | read or write 1, 2 or 4 bytes of `memory` (`bytes8`, `bytes16`, `bytes32`) at `X(rs1) + offset`, computed by the translator, and append an `EventLoad` or `EventStore` of that size; they always succeed, at any address | Sail's address code (`ext_data_get_addr`, `transform_effective_address`), translation, PMP, misaligned-access traps |
| RV32 `currentlyEnabled` | false for `Ext_Zca` and `Ext_Zicfilp`; any other extension stops generation | compressed instructions and landing pads |
| RV32 `trap`, `exception_context`, `ExecutionResult` | the branches, JAL, JALR, ECALL and EBREAK keep the result's constructor; only `Retire_Success` is a normal outcome, and the translator then appends an `EventJump` from the instruction's PC to the new `PC`. The other roots drop the result. A trap context keeps only its cause's constructor and `excinfo`: ECALL's other context fields and EBREAK's `Brk_Software` are evaluated and dropped | trap outcomes: the relation permits no final state there, so ECALL and EBREAK permit none at all |
| RV32 `sail_barrier`, `generate_event` | change no state; the argument is evaluated | ordering between harts and devices; the event callback |
| RV32 `is_fiom_active` | the quantified `reg_is_5ffiom_5factive`, which decides for FENCE whether its I/O bits imply memory bits | nothing |
| RV32 `quot_round_zero`, `rem_round_zero` (no cut) | for a divisor `d` proved nonzero, `if x < &0 then --(--x div d) else x div d`, and the same with `rem`: Sail rounds toward zero, HOL's `div` and `rem` are Euclidean | nothing |
| shina `GPR` array | element `i` is `registers :> element (iword i)`, with `i` proved in 0 to 15; the upstream helpers keep their slices, high-byte selection and upper-half clearing | nothing beyond s2n-bignum's own registers |
| shina `CF`, `PF`, `AF`, `ZF`, `SF`, `OF` | the HOL Boolean flags | nothing |
| shina `read_simd`, `write_simd` | `SIMD128` and `SIMD256`; a write clears the register's bits up to 511 | nothing for the registers 0 to 15 that the encodings reach |
| shina assumptions | `cur_mode = LongMode`; `has_adx = true` for ADCX and ADOX; `has_bmi2 = true` for MULX | other modes; processors without ADX or BMI2 |
| x86 supplied inputs | bytes that the body would fetch (ModR/M, immediate, count, prefixes) become root parameters (`Entry.input_lift`) | the fetch, its faults and its state changes, such as `decode_pos` |
| REMS `read_gpr`, `write_gpr` | `registers :> element (word i)`; before the cut the translator checks that the bodies use x86 register numbering and that `write_gpr` does nothing but its update and its log; `log_register_writes = false` | REMS's register-write log |
| REMS entries | each passes `Mode_64bit`, a synthetic instruction span starting at 0, its prefixes, REX byte, opcode and a register-direct ModR/M byte | other modes and encodings |
| REMS `rflags`, `rip` | root parameters; the statements instantiate them as `rflags :> bottom_32` and `RIP` | nothing |
| REMS throws | a throw permits no final state | nothing for an `_EQ` theorem, which shows the throw unreachable |
| REMS shift by a negative amount | an unknown word of the result width | Sail backends disagree on these shifts; the wide-count REMS `_DIFF` theorems rest on this choice ([X86-DIVERGENCES.md](docs/X86-DIVERGENCES.md#rems-rotate-wide-count)) |
| REMS `undefined` of a refined integer type | a choice within the refinement; a choice outside it permits no final state | nothing |
| REMS integer recursion | unfolded while one argument shrinks and none grows; past fixed limits generation stops | nothing |
| REMS RIP, in the proofs | the statements compare `sail_hl_x86_core`, which resets RIP to its entry value after the body | REMS's RIP update |
| RV32 division events, in the proofs | the DIV, DIVU, REM and REMU statements compare Sail's relation followed by `riscv_event_div`, the `EventRISCVDIV` operand event that s2n-bignum records because division latency may depend on the operands | nothing about registers or PC; the event itself has no Sail counterpart to check against |
| Arm memory events, in the proofs | the statements compare `sail_hl_arm_memory_observed`, which erases the event list of both final states | the access events: Sail emits one per lane, s2n-bignum one per instruction |

## Scope of the claims

Which theorems CI requires, and what their right-hand sides say, is
written by hand:

- [scripts/coverage.py](scripts/coverage.py) (`ARM_FAMILIES`, `RV32`)
  and [scripts/x86_forms.py](scripts/x86_forms.py) list the required
  forms; [ci/check.py](ci/check.py) derives the theorem names from them.
  The "every public definition" claims rest on these lists matching
  s2n-bignum's decoder. CI checks only the set of public names: those
  bound by `let` or `and` to `define` or `new_definition` in
  `arm/proofs/instruction.ml` and `riscv/proofs/instruction.ml`. The form
  lists were compared with the clauses of `arm/proofs/decode.ml` by
  review, which is how the scalar `SHL Dd, Dn, #amount` form was found
  missing; no check derives them from `decode.ml`.
- The drivers choose the s2n-bignum side of each statement, for example
  `arm_TBL2 (QREG' d) (QREG' n) (QREG' (word_add n (word 1)))` for two
  consecutive table registers. These instances are not checked against
  the decoder; reviewers can read them in `statements/`.

## From model file to kernel term

- `ci/check.py proofs` copies `generated/` to `_build/`, where the
  drivers load it, and checks afterwards that neither copy changed.
- [check-proof.sh](check-proof.sh) expands each driver and the files it
  loads into one OCaml source and compiles it. `ci/check.py proofs` first
  compiles `arm/proofs/base.ml` once with `check-proof.sh arm-base`.
  While that compiled base exists, an Arm suite is expanded with
  [scripts/inline-proof.ml](scripts/inline-proof.ml), which leaves
  `base.ml` out, and linked with it; otherwise HOL Light's
  `inline_load.ml` expands everything.
- Loaders replace HOL functions while a model loads, to make loading
  faster. They decide which term is defined, so an error in one gives
  valid theorems about another model. Each is defined before the model
  it loads.
  - [fresh-model.ml](proofs/fresh-model.ml) defines each equation with
    `new_basic_definition`, without HOL's search for an equal earlier
    definition, and evaluates the model's final rewrite by value. Used by
    arm-addsub, arm-vector-poly, arm-vector-table,
    arm-vector-multiply-accumulate-long, the arm-memory suites,
    x86-vector, x86-rems-arithmetic and x86-rems-shift.
  - [arm-memory-model-loader.ml](proofs/arm-memory-model-loader.ml)
    records the memory models' equations; used by the arm-memory
    suites.
  - Local versions in a driver: `REWRITE_RULE` in arm-vector-poly.ml;
    `REWRITE_RULE` and `CONV_RULE` that return the theorem unchanged in
    x86-rems-arithmetic.ml and x86-rems-shift.ml; `new_definition` in
    x86-vector.ml.
- [proof-fork.ml](proofs/proof-fork.ml) proves the claims of the largest
  suites in forked processes and prints their output in order. It is
  trusted to pass each child's lines on unchanged, and to print one
  completion marker only if every child printed its own.

## Checking the proof logs

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
model files (`validate_models` in [ci/check.py](ci/check.py)), for every
root of every architecture, and an extra root is refused.

A driver that printed a statement it had not proved would pass this
audit. Before any proof runs, `check_proof_sources` in
[ci/check.py](ci/check.py) makes that harder. It is a text check against
accidents and lazy subversion, not a guarantee. It scans every file under
`proofs/` and `generated/` except README.md and refuses, outside comments:

- `new_axiom`, `mk_thm`, `CHEAT_TAC` and a definition of `check_axioms`;
- changes to the parsing interface, printers or overload priorities
  (`override_interface` and its relatives, `install_user_printer`,
  `prioritize_*`, `parse_as_infix` and the other `(un)parse_as_*`,
  `set_ellipsis_text`, `set_max_boxes`, `the_interface :=`,
  `.contents <-`), and `Obj`;
- `print_thm` and `string_of_thm` anywhere but
  [proofs/report.ml](proofs/report.ml), whose `sail_hl_report` refuses a
  theorem with hypotheses or free variables before printing it.

It also requires each driver, with the files it loads, to have a line
that starts with `check_axioms ();;` after the last load and before the
completion marker. A load directive is recognised with or without a space
before its file name.
