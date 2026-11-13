# Theorem statements

One file per proof suite, `<suite>.txt`, records every theorem that
`ci/check.py proofs` requires from that suite: its name, its statement as
HOL Light prints it (the `|- ` line and the indented lines that continue
it), and a blank line. CI compares each printed statement with this
record byte for byte, so a weakened statement, or one form's theorem
printed under another form's name, fails. Changing a statement means
changing these files. HOL Light prints no types;
[the log audit](../ci/README.md#checking-the-proof-logs) says what the
comparison does not establish.

## Counts

| Files | Source model | Theorems | Kinds |
| --- | --- | ---: | --- |
| `arm-*.txt` (69 files) | sail-arm | 1,404 | 1,158 `_EQ`; 246 `_SAFE_EQ`, one per memory form |
| `rv32.txt` | sail-riscv | 50 | 40 `_EQ`; 8 `_SAFE_EQ`, for the branches and jumps; 2 `_DIFF`, for ECALL and EBREAK |
| `x86-arithmetic.txt` | shina | 84 | 84 `_EQ` |
| `x86-shift.txt` | shina | 47 | 35 `_EQ`; 6 `_EXACT` and 6 `_DIFF`, for RCL and RCR at 8 and 16 bits |
| `x86-vector.txt` | shina | 80 | 80 `_EQ` |
| `x86-rems-arithmetic.txt` | REMS | 78 | 78 `_EQ` |
| `x86-rems-shift.txt` | REMS | 41 | 22 `_EQ`; 19 `_DIFF` |
| 75 files | | 1,784 | 1,497 `_EQ`, 254 `_SAFE_EQ`, 6 `_EXACT`, 27 `_DIFF` |

Every theorem compares a generated relation with s2n-bignum's. REMS and
shina are not compared with each other.

Which instructions each x86 file holds (the forms are in
[x86_forms.py](../scripts/x86_forms.py)):

- `x86-arithmetic.txt`: ADD, ADC, ADCX, ADOX, SUB, SBB, CMP, INC, DEC,
  NEG, MUL, one-operand IMUL, three-operand IMUL, MULX, AND, OR, XOR,
  NOT and TEST. Theorem names use `MUL`, `IMUL1`, `IMUL` and `MULX` for
  s2n-bignum's `MUL2`, `IMUL2`, `IMUL3` and `MULX4`.
- `x86-shift.txt`: SHL, SHR, SAR, SHLD, SHRD, ROL, ROR, RCL and RCR.
- `x86-vector.txt`: the 40 AVX2 integer instructions that
  `x86_forms.py` lists as `VECTOR` (VPADDB, VPSUBQ, VPMULLW, VPAND and
  so on), at 128 and 256 bits.
- `x86-rems-arithmetic.txt` and `x86-rems-shift.txt`: the same scalar
  instructions as shina's arithmetic and shift files, less those that
  REMS does not implement (ADCX, ADOX, MULX and all vector forms).
- `rv32.txt`: every RV32IM instruction, from `rv32.ml` and
  `rv32-control.ml`. The `arm-*.txt` files are listed by suite and
  definition in the
  [coverage map](../docs/ARM-COVERAGE-MAP.md#which-suite-holds-a-definition).

## Kinds

In the shapes below, `R` is a generated relation applied to its
parameters and `H` is s2n-bignum's relation applied to the operands. Both
hold of an initial state `s` and a final state `t` when the instruction
permits `t` from `s`.

- `_EQ`: `|- forall fields s t. R s t <=> H s t`. The two relations
  permit exactly the same final states, for every field and every initial
  state. For REMS the left side is
  `sail_hl_x86_core (R (rflags :> bottom_32) RIP fields) s t`. For RV32
  DIV, DIVU, REM and REMU it is
  `(R ,, (\u. riscv_event_div x y u u)) s t`, where `x` and `y` are the
  two source registers read in `s`:
  Sail's relation, then the division event appended to the events it
  produced. The event is the operand event that s2n-bignum records for a
  division, which Sail does not model; because it extends the events of
  Sail's final state, an event that Sail's relation recorded would stay
  visible. The RV32 halfword and word
  accesses are `_EQ` although s2n-bignum guards them with alignment: the
  interpretation of `vmem_read` and `vmem_write` copies Sail's
  `is_aligned_addr` test by hand and permits every final state when it
  fails, in place of Sail's platform-chosen outcome. So these theorems do
  not check the guard against Sail's code
  ([interpretations](../backend/README.md#interpretations)).
- `_SAFE_EQ`: `|- (exists fields s. G) /\
  (forall fields s t. G ==> (R s t <=> H s t)) /\
  (forall fields s. ~G ==> H s = ASSIGNS entirety s)`. This is the one
  full description of the shape; other pages link here.
  `ASSIGNS entirety s` is s2n-bignum's relation that holds between `s`
  and every state `t`, so `H s = ASSIGNS entirety s` says that `H`
  permits every final state from `s`. `G` is
  s2n-bignum's safety guard, a condition on the fields and the initial
  state, read from its definition in the kernel: SP alignment, writeback
  overlap and distinct destinations for Arm memory, and the alignment of
  the target for RV32 branches and jumps. The first conjunct shows that
  the guard can hold, so the second is not vacuous. The third states the
  boundary: from an initial state outside the guard, s2n-bignum permits
  every final state. Together, every final state that the generated
  relation permits, s2n-bignum permits too (for the Arm memory forms,
  up to the event lists). What Sail does outside the guard is not
  compared. For Arm memory, the second conjunct wraps both
  sides in `sail_hl_arm_memory_observed`, which erases the event lists.
- `_EXACT`, for the six shina forms that differ from s2n-bignum: RCL and
  RCR at 8 and 16 bits. Instead of agreement, the theorem states exactly
  which final states shina permits, in terms of s2n-bignum's relation.
  They differ only in OF, and only when the masked count rotates the
  operand and CF through a whole cycle (9, 18 or 27 at 8 bits, 17 at 16
  bits): there s2n-bignum permits any value of OF, while shina keeps the
  old one. So shina permits exactly the final states that s2n-bignum
  permits and that, at those counts, leave OF unchanged; this is a subset
  of what s2n-bignum permits. For RCL at 8 bits:

  ```text
  |- forall d count s t.
         sail_hl_X86_5fRCL8_5fRI d count s t <=>
         x86_RCL (GPR8 (Gpr d Lower_8)) (val count MOD 32) s t /\
         (val count MOD 32 = 9 \/
          val count MOD 32 = 18 \/
          val count MOD 32 = 27
          ==> (read OF t <=> read OF s))
  ```

- `_DIFF`: a closed counterexample to `_EQ`. For shina it follows from
  `_EXACT`, for example

  ```text
  |- forall d s.
         x86_RCL (GPR8 (Gpr d Lower_8)) 9 s (write OF (~read OF s) s) /\
         ~sail_hl_X86_5fRCL8_5fRI d (word 9) s (write OF (~read OF s) s)
  ```

  with count 17 at 16 bits. For REMS it is
  `|- forall s. C1 /\ ... /\ Cn`, one conjunct per finding,
  each of the form `A i f /\ ~B i f`: one relation permits final state `f`
  from initial state `i` and the other does not. The register values and
  counts are fixed, and `i` and `f` are built from `s` with
  `sail_hl_x86_rems_diff_initial`. A `_DIFF` theorem shows that at least
  these differences exist. It does not say what the other relation
  permits instead, and no exact relation is proved for the 19 REMS forms
  that differ. For RV32 ECALL and EBREAK it holds for every final state,
  `|- forall s t. riscv_EBREAK s t /\ ~sail_hl_rv_5fEBREAK s t`: they
  have no successful outcome in Sail, and s2n-bignum permits every
  final state.

CI also requires each statement to mention exactly the generated roots
that its name refers to.

## Names

Theorems are named `SAIL_HL_<ARM|RV32|X86>_<form>_<kind>`, and REMS
names start `SAIL_HL_X86_REMS_`. `ci/check.py` derives the required names
from [coverage.py](../scripts/coverage.py) (`arm_instruction_variants`,
`RV32`) and [x86_forms.py](../scripts/x86_forms.py), not from the proof
files. The part of a name after the instruction gives the form:

| Part | Meaning |
| --- | --- |
| `32`, `64`, `128`; `8`, `16` for x86 | register or operand width |
| `VEC128E16` | a 128-bit vector of 16-bit lanes; `VEC64E64` is the one-lane scalar form |
| `_LO`, `_HI` | the lower or upper half of a source (the `2` forms), or of an index range |
| `_IMM`, `_SHIFT`, `_EXT_UXTB_<n>` | immediate, shifted-register and extended-register operands; `<n>` is the extended operand's left shift |
| `_GPR_`, `_SIMD_` | general or SIMD&FP transfer registers |
| `_POST`, `_PRE`, `_OFFSET` | post-indexed, pre-indexed and signed-offset immediate addressing |
| `_UIMM`, `_UNSCALED` | unsigned scaled immediate (LDR/STR), signed unscaled immediate (LDUR/STUR) |
| `_REG0`, `_REGS` | register offset, unshifted or shifted by the access size |
| `_SIMD_LD1_E8_NO`, `_POSTI`, `_POSTR` | the LD1 (or LD2, LD3, LD1R) structure encoding with 8-bit lanes, without writeback, or post-incremented by an immediate or a register |
| `_RR`, `_R`, `_RI`, `_RRI`, `_RRR` | x86 register operands and an immediate count |
| `_LEGACY` | an x86 byte form without REX, whose registers include AH to BH |

Store roots that use a structure encoding keep `LD` in their name: for
example `arm_STP128_SIMD_LD1_E16_POSTR` is s2n-bignum's two-register STP
through the ST1 encoding.

The constants on the left, such as `sail_hl_ARM_5fADC64`, are the
generated relations in [generated/](../generated/README.md). The plugin
writes every character other than a letter or digit as `_` and two hex
digits, so `_5f` is `_` and `_2d` is `-`
([names](../backend/README.md#names)). The carry, logical,
AES, SHA2 and crypto-bitwise families name their roots `ARM_...`, the
others `arm_...`; theorem names use `ARM_` for both.

## Variables and constants

A statement's variables are named after the fields of the instruction
encoding, as the table entry names them, and the generated root takes
them by position. Before each root, the model's "Selected Sail call"
gives the correspondence: "v0 is d, v1 is n, v2 is m" in
`generated/arm-carry.ml` means that the statement's `d n m` are the
entry's `d n m`. The width of an immediate field, and so the range a
theorem covers, is in the same comment: for
`SAIL_HL_ARM_SRI_VEC128E16_EQ`, `amount : bitvector(4)`, passed as
`unsigned(amount) + 1`, covers shifts 1 to 16.

A variable named `reg_<R>` is a state component standing for a Sail
register, or register-valued call, that the exporter gives no fixed
meaning. The theorem holds for every such component. In the Arm
statements they are `reg_PSTATE`, `reg_FPCR`, `reg_FPSR`,
`reg_SCTLR_5fread_5f_5f1` (the SCTLR value that decides SP alignment
checks), `reg_FlatAccDescGPR` and `reg_FlatAccDescASIMD` (the memory
access descriptors) and `reg_FlatHaveLSE2` (LSE2 availability); in the
RV32 statements `reg_is_5ffiom_5factive` (FENCE's I/O-implies-memory
setting) and `reg_cur_5fprivilege` (the privilege level that chooses
ECALL's cause).

Some root parameters are instantiated instead:

- Sail's `_PC`, in the 33 statements of arm-address, arm-branch-basic,
  arm-branch-absolute-execute and arm-branch-conditional, is
  `PC :> evaluate (\pc. word_sub pc (word 4))`, because s2n-bignum runs
  an instruction after PC has advanced by 4.
- REMS's `rflags` and `rip` are `rflags :> bottom_32` and `RIP`.

s2n-bignum's RV32 model has the same PC convention:
`riscv_instruction_pc s` is `read PC s` minus 4, so BNE's not-taken
target is `read PC s`.

These constants are defined in proof files and change what a statement
means:

| Constant | Meaning | Defined in |
| --- | --- | --- |
| `sail_hl_arm_memory_observed R s t` | some final state of `R` from `s` equals `t` once both event lists are erased | [arm-memory-support.ml](../proofs/arm-memory-support.ml) |
| `sail_hl_x86_core R s t` | some final state of `R` from `s`, with RIP reset to its value in `s`, is `t` | [x86-rems-lemmas.ml](../proofs/x86-rems-lemmas.ml) |
| `sail_hl_x86_rems_diff_initial x s` | `s` with register 0 set to `x` and CF and OF clear | [x86-rems-shift.ml](../proofs/x86-rems-shift.ml) |
| `sail_hl_arm_logical_kind` | maps Sail's shift-type constructors to s2n-bignum's LSL, LSR, ASR and ROR | [arm-logical-lemmas.ml](../proofs/arm-logical-lemmas.ml) |

s2n-bignum's own notation, as the statements use it:

| Notation | Meaning |
| --- | --- |
| `XREG' d`, `WREG' d` | the 64-bit or low 32-bit general register that the 5-bit field `d` names; register 31 reads zero and ignores writes; a write to `WREG'` clears the upper half. Defined in [arm/proofs/decode.ml](../../../arm/proofs/decode.ml) |
| `XREG_SP n` | register `n` of `registers`, where 31 is the stack pointer instead of zero |
| `QREG' d`, `DREG' d` | the 128-bit or low 64-bit vector register that `d` names |
| `GPR8 (Gpr d Lower_8)` | the low byte of x86 register `d`; `Gpr` pairs a register number with the part of it (`Lower_8`, `Upper_8`, `Lower_16`, `Lower_32`, `Full_64`) that an instruction uses. `GPR16` and `GPR32` name the wider parts. Defined in [x86/proofs/x86.ml](../../../x86/proofs/x86.ml) |
| `riscv_gpr rd` | RV32 register `rd`; register 0 reads zero and ignores writes |
| `ASSIGNS entirety s` | holds between `s` and every state |

HOL Light does not print binder types. The definitions on each side fix
them; a register field, for example, is a `5 word`.

To find a theorem's proof, open `proofs/<suite>.ml`
([proofs/README.md](../proofs/README.md)). Larger suites build the names
and statements from tables, so these files are the only place where the
statements appear in full.

## Updating

Record changed statements only from an audited proof run, with
`check.py refresh-statements`. The procedure, with the commands, is in
[ci/README.md](../ci/README.md#refreshing-the-checked-in-files).
