# AArch64 forms

The AArch64 comparison covers every public definition in
`arm/proofs/instruction.ml`. A **form** is one width, lane layout,
addressing mode or alias of a definition that needs its own theorem; a
**profile** below describes the forms that a group of definitions needs.
They follow what s2n-bignum's decoder, `arm/proofs/decode.ml`, produces,
not every encoding that Arm or Sail has.

## Where the forms are listed

- `ARM_FAMILIES` in [scripts/coverage.py](../scripts/coverage.py) lists,
  for each family, its public definitions and the forms each needs, with
  the argument types of each generated root. CI derives the required
  theorem names from it and checks that the families together list every
  public definition once. To find a definition's family, search the file
  for its name, such as `"ADC"`; the suite is `arm-<family>`.
- `statements/arm-<family>.txt` lists every form by theorem name
  ([naming](../statements/README.md#names)).
- In `generated/arm-<family>.ml`, the "Selected Sail call" before each
  root gives the upstream function and arguments that select the form;
  `backend/arm.ml` builds these calls.

W32 and X64 are 32- and 64-bit integer registers, D64 and Q128 64- and
128-bit vector registers, and E8 to E64 the lane width. **G** means both
W32 and X64. Every register field is five bits, and theorems include
register 31 and overlapping operands.

A form covers only the decoded domain. Several s2n-bignum definitions
accept more than an encoding can express, and the statements instantiate
them as the decoder does:

- `arm_TBL`, `arm_LD3` and `arm_ST3` are defined only for one list shape
  (`[Rn]`, `[Rt1;Rt2;Rt3]`).
- `arm_TBL2`, `arm_TBL3`, `arm_LDP4`, `arm_STP4`, `arm_LD2`, `arm_ST2`,
  `arm_LD3` and `arm_ST3` take independent register components; the
  encodings use consecutive registers modulo 32, and so do the
  statements.
- `arm_LDR`, `arm_STR`, `arm_LDP` and `arm_STP` serve several GPR, SIMD
  and structure encodings, each a separate form.

## Scalar and branch profiles

- **CARRY**: G; ADC, ADCS, SBC, SBCS; the carry input is the C flag. NGC
  and NGCS fix the first source to register 31.
- **ADDSUB**: G; immediate imm12 shifted by 0 or 12; shifted register
  with LSL, LSR or ASR (not ROR) by 0 to width minus 1; extended register
  with UXTB, UXTH, UXTW, UXTX, SXTB, SXTH, SXTW or SXTX and shift 0 to 4.
  At X64 the source is an X register for UXTX and SXTX, a W register
  otherwise. Immediate and extended forms allow SP as base and, without
  flags, as destination.
- **LOGIC**: G; AND, ANDS, EOR, ORR, MOV and TST with immediate and
  shifted-register forms; BIC, BICS, EON, ORN and MVN shifted-register
  only. Shifts are LSL, LSR, ASR or ROR by less than the width. An
  immediate form takes the mask as an arbitrary word, which includes every
  encodable mask, but does not cover `DecodeBitMasks`. Non-flag immediate
  forms allow SP as destination.
- **VARIABLE**: G; LSLV, LSRV, ASRV, RORV; the amount is the low bits of
  the second register.
- **BITFIELD**: G; BFM, SBFM, UBFM through the Sail decoders, including
  `DecodeBitMasks`; the aliases ASR, LSR and LSL with the decoder's
  immr and imms (`imms = width - 1` for ASR and LSR; for LSL
  `immr = -amount mod width`, `imms = width - 1 - amount`).
- **COMPARE**: G; CCMN and CCMP with a register or zero-extended imm5
  operand, all sixteen conditions and every four-bit fallback NZCV. One
  theorem per width covers both operand kinds.
- **SELECT**: G; CSEL, CSINC, CSINV, CSNEG, all sixteen conditions, and
  the aliases CINC, CINV, CNEG, CSET and CSETM. AL and NV are both true;
  an alias inverts the low condition bit.
- **EXTRACT**: G; EXTR by 0 to width minus 1; ROR with both sources
  equal.
- **MOVEWIDE**: MOVN, MOVZ, MOVK; imm16 at position 0 or 16 (W32) or 0,
  16, 32 or 48 (X64). MOVK keeps the other bits.
- **MUL**: G; MADD, MSUB; MUL and MNEG with accumulator register 31.
- **MULLONG**: UMADDL, UMSUBL with an X64 accumulator and W32 sources;
  UMULL and UMNEGL with accumulator XZR.
- **MULHIGH**: SMULH, UMULH, X64.
- **COUNT, REVERSE**: G; CLZ, REV.
- **PCREL**: ADR and ADRP, X64, signed imm21; ADRP shifts it by 12 and
  adds the page of the instruction's PC.
- **BRANCH**: B and BL with signed imm26 times four; B.cond with signed
  imm19 times four, all sixteen conditions and the eighteen alias names
  (BEQ to BNV); CBZ and CBNZ at W32 and X64; TBZ and TBNZ with bits 0 to
  31 at W32 and 32 to 63 at X64, signed imm14 times four; RET with an X
  register and no PAC. Taken and not-taken paths both append s2n-bignum's
  jump event. The statements read Sail's `_PC` as HOL `PC` minus 4
  ([TRUST.md](../TRUST.md#interpretations)).
- **ABSOLUTE**: `arm_BL_ABSOLUTE` is an s2n-bignum helper for a BL to an
  arbitrary 64-bit target, not an encoded instruction. Its theorem uses
  BL's execute body with offset `target - (PC - 4)`.
- **HINT**: the exact NOP and `BTI c` encodings.

## Memory profiles

[ARM-MEMORY-CONTRACTS.md](ARM-MEMORY-CONTRACTS.md#forms) lists the
memory forms per suite. Every memory theorem holds under s2n-bignum's
safety guard and erases the access events.

## SIMD profiles

- **U**: D64 with E8, E16, E32 and Q128 with E8 to E64: ABS, ADD, SUB,
  CMGT, CMHI, CMGE, CMLE (zero), USHL, TRN1, TRN2, ZIP1, ZIP2 and the
  shifts below. **U3** omits E64: MUL, MLA, MLS, SMAX, UMAX, UMIN,
  URHADD. Most D64 results clear the upper half of the Q register.
- **REV, CNT**: REV32 at Q128 with E8 and E16, REV64 at Q128 with E8 to
  E32; CNT at D64 and Q128.
- **BITS**: AND, BIC, ORR, EOR, BIT, BIF and MOV at D64 and Q128 without
  lanes. BIC_VEC also has a modified-immediate form with 16-bit lanes
  shifted by 0 or 8, and ORR_VEC one with 32-bit lanes and shift 0.
- **DUP**: D64 and Q128, E8 to E64, except E64 at D64. DUP_ELEM selects
  any lane of a Q128 source; DUP_ELEM_SCALAR writes one lane as a
  scalar; DUP_GEN takes the low bits of a general register.
- **INSERT**: Q128, E8 to E64, every destination and source lane; INS_GEN
  reads a W register for E8 to E32 and an X register for E64. The other
  lanes are kept.
- **UMOV**: lane 32 to a W register and lane 64 to an X register, every
  lane index; s2n-bignum's decoder has no 8- or 16-bit form.
- **FPBITS**: FCSEL at 32 and 64 bits, all sixteen conditions,
  zero-extended into Q128; FMOV_FtoI from the low 32 bits to W32 and
  from the low or high 64 bits to X64; FMOV_ItoF from X64 to the low or
  high 64 bits. These move bits; no floating-point arithmetic is
  compared.
- **EXT**: D64 by 0 to 7 bytes, Q128 by 0 to 15.
- **MODIMM**: MOVI at D64 and Q128 takes the expanded 64-bit immediate,
  as `arm_MOVI` does, for every value. This includes every encodable
  pattern but does not cover `AdvSIMDExpandImm`.
- **MULV**: MLA, MLS, MUL at U3, and by element with E16 and E32.
- **LONG**: Q128 result from E8 to E32 sources, the low source half
  without `2` and the high half with it; for SADDW, SSUBW and USUBW one
  operand is already double width.
- **LONGMUL**: LONG for SMULL, UMULL, SMLAL, SMLSL, UMLAL and UMLSL;
  also by element with E16 and E32 for UMULL, SMLAL and UMLSL and their
  `2` forms, as the HOL decoder has them. Sail has more by-element forms.
- **DOUBLING**: SQDMULH and SQRDMULH at D64 and Q128, E16 and E32, vector
  and by element. They set `FPSR.QC`, which is not compared
  ([ARM-DISCREPANCIES.md](ARM-DISCREPANCIES.md#saturation)).
- **SHLEFT**: U; SHL and SLI with immediate 0 to lane width minus 1.
  SHL also has the scalar `SHL Dd, Dn, #amount`, its VEC64E64 form.
  **SHRIGHT**: U; SSHR, SRSHR, USHR, USRA and SRI with immediate 1 to lane
  width.
- **SHLONG**: SSHLL and USHLL, low or high source half, immediate 0 to
  narrow lane width minus 1.
- **NARROW**: SHRN, RSHRN, SQSHRUN and SQRSHRUN with result lanes E8 to
  E32 and right shift 1 to the result lane width. Without `2` the result
  goes to the low half and the high half is cleared; with `2` it goes to
  the high half and the low half is kept. SQSHRUN and SQRSHRUN saturate
  and set `FPSR.QC`.
- **EXTRACTNARROW**: XTN and XTN2, the same halves as NARROW without a
  shift.
- **REDUCE**: ADDV, UADDLV and UMAXV at D64 with E8 and E16, and at Q128
  with E8 to E32.
- **PAIRADD**: UADALP at D64 and Q128, E8 to E32; UADDLP at Q128 only, as
  in the HOL decoder.
- **PERMUTE**: TRN1, TRN2, ZIP1, ZIP2 at U; UZP1 and UZP2 at Q128 only,
  E8 to E64.
- **TABLE**: TBL, TBL2 and TBL3 at D64 and Q128 with one, two or three
  consecutive Q128 table registers; an out-of-range index gives zero.
- **POLY**: PMUL with E8 at D64 and Q128; PMULL and PMULL2 with E8 or E64
  sources and a Q128 result, under `FEAT_PMULL`.
- **CRYPTO**: Q128. AESE, AESD, AESMC, AESIMC; SHA256H, SHA256H2,
  SHA256SU0, SHA256SU1, SHA512H, SHA512H2, SHA512SU0, SHA512SU1; EOR3,
  BCAX, RAX1, and XAR by 0 to 63.
