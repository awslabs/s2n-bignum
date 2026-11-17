# Arm memory contracts

This page describes what is specific to the Arm load and store forms:
which forms are compared, how the memory interpretations act on them,
and what their theorems say. The interpretations themselves (flat
`Mem_read` and `Mem_set`, the access-descriptor factories, `BigEndian`,
the stack pointer, the FP enable checks and faults) are described once,
with what each loses, in
[interpretations](../backend/README.md#interpretations).

## Forms

The forms cover the public memory definitions that s2n-bignum's
[decoder](../../../arm/proofs/decode.ml) produces: LDR, STR, LDRB, STRB,
LDRH, STRH, LDRSB, LDRSH, LDP, STP, LDP3, STP3, LDP4, STP4,
LD1_LANE, ST1_LANE, LD2, ST2, LD3, ST3 and LD1R.

| Suite | Forms |
| --- | --- |
| arm-memory-single | LDR and STR: W32 and X64 with pre- and post-indexed imm9, scaled imm12, UXTX register offset unshifted or shifted, and unscaled imm9; B8 and H16 with imm12, S32 with imm12 and unscaled, D64 with pre, post, imm12 and unscaled, Q128 with all six; one-register LD1/ST1, D64 and Q128, 8- to 64-bit lanes, no offset or post-increment by immediate or register. LDRB/STRB and LDRH/STRH use W32; LDRSB/LDRSH use W32 or X64. All narrow scalar forms have pre, post, imm12, unscaled, and UXTW/SXTW offsets with either S bit. Halfword and signed-load forms also have both UXTX offsets; LDRB/STRB have only unshifted UXTX |
| arm-memory-pair | LDP and STP: W32, X64, D64 and Q128 with pre, post and signed offset; two-register Q128 LD1/ST1, four lane sizes, the three LD1 addressing modes |
| arm-memory-three | LDP3 and STP3, the three-register LD1/ST1: D64 and Q128, four lane sizes, the three LD1 addressing modes |
| arm-memory-four | LDP4 and STP4, the four-register LD1/ST1: D64 and Q128, four lane sizes, the three LD1 addressing modes |
| arm-memory-lane | LD1_LANE and ST1_LANE: one 32-bit lane in Q128, no offset or post-increment by immediate or register; one symbolic two-bit index covers all four lanes |
| arm-memory-structure2 | LD2 and ST2 without writeback or with immediate post-increment: D64 with 8- to 32-bit lanes, Q128 with 8- to 64-bit lanes |
| arm-memory-structure3 | LD3 and ST3, the same lanes, post-increment by immediate or register |
| arm-memory-replicate | LD1R, D64 and Q128, four lane sizes, immediate post-increment |

[statements/](../statements/README.md) lists every form by name. Every
register field is five bits, including 31 and overlapping fields.
Structure registers are consecutive modulo 32. A post-register form keeps
every Rm value: 31 selects the immediate increment, not XZR. D64 with
64-bit lanes is reserved for LD2, ST2, LD3 and ST3, so those forms are
absent in both decoders.

The forms are those of the current s2n-bignum decoder, not every Arm
memory instruction or every instance of a generic HOL definition. Scalar
byte and halfword accesses transfer 8 or 16 bits independently of the
destination width. A signed W32 load sign-extends to 32 bits and clears
the physical X register's high 32 bits; an X64 load sign-extends to 64.
UXTW/SXTW offsets read only the low 32 bits of Rm, then extend and
optionally shift by zero for byte accesses or one for halfwords. Both
byte S encodings are retained even though they compute the same shift.
LDPSW remains absent from s2n-bignum's decoder.

Whole-register SIMD loads clear all bits above the selected B/H/S/D
view. Single-lane loads instead preserve the other 96 bits of Q128.

## How the interpretations apply

The Sail decoders and execute bodies are translated as they are: register
selection, address calculation, lane loops, writeback, the SP alignment
check and the constrained-unpredictable choices. The interpretations
replace only the platform below them.

- The interpretation emits one event per source access: four lane reads
  produce four `EventLoad`s, not one whole-register read.
- The pair accessors keep their `ispair` and `highestAddressfirst`
  arguments, which do not change the bytes stored.
- GPR pairs keep both `HaveLSE2Ext()` paths, a joined access and two
  separate accesses; `reg_FlatHaveLSE2` decides between them, and each
  theorem holds for both values.
- The access descriptor is a value of Sail's full `AccessDescriptor`
  record, read from `reg_FlatAccDescGPR` or `reg_FlatAccDescASIMD`. The
  translator checks the declared record, its field types and enums. Every
  argument of the factory is evaluated, with its effects.
- The GPR execute body computes `privileged = PSTATE.EL != EL0`, so the
  translation needs EL, which comes from `reg_PSTATE`.
- `CheckSPAlignment` keeps its body and reads SCTLR through the
  quantified `reg_SCTLR_5fread_5f_5f1`; alignment checking is neither
  forced on nor off.
- `ConstrainUnpredictable` keeps its body, which returns `undefined`, so
  every choice that the caller's assertion allows remains possible.
- Unknown values in the decoders, such as `__UNKNOWN_integer()` or an
  undefined `MemOp` local, are existential choices of their type.

## Proofs

Each form has one theorem, `_SAFE_EQ`, whose shape
[statements/README.md](../statements/README.md#kinds) describes. For
these forms both sides of the second conjunct are wrapped in
`sail_hl_arm_memory_observed`.

`G` is the safety guard of the instantiated s2n-bignum definition, read
from its equation in the kernel (`SAIL_HL_ARM_MEMORY_GUARD` in
[arm-memory-support.ml](../proofs/arm-memory-support.ml)): SP alignment
when the base is SP, no overlap between writeback and the transfer
registers, and for LDP distinct destinations. Outside `G` s2n-bignum
permits every final state, as the third conjunct states; what Sail does
there is not compared. The guard is s2n-bignum's own, not a list of
convenient inputs.

`sail_hl_arm_memory_observed R s t` holds when some final state of `R`
from `s` equals `t` once both event lists are erased. Every register,
flag, PC and memory byte is still compared.

The first conjunct shows that the guard can hold, so the second is not
vacuous. The claim builder proves it by giving the register fields
distinct indices below 31, so that the base is not SP and no transfer
register overlaps it or another, and deciding that instance with
s2n-bignum's component conversions. This shows only that some operands
and state satisfy the guard. That it holds for the operands of a given
program is what s2n-bignum's proofs of that program establish.

[arm-memory-support.ml](../proofs/arm-memory-support.ml) holds the code
that the eight suites share; each `arm-memory-<suite>.ml` lists its forms
and its tactic. A reached SP alignment fault would permit every final
state on the Sail side, so inside the guard the theorems also show that
Sail does not reach it.

The duplicate-destination error in `arm_LDP` is described in
[ARM-DISCREPANCIES.md](ARM-DISCREPANCIES.md#duplicate-load-destinations).
