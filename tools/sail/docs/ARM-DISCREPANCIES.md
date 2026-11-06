# Arm model differences

This page records the differences between Sail's Arm model and
s2n-bignum's that the comparison found or had to account for. Each
interpretation it mentions, with its HOL meaning and what it loses, is in
[TRUST.md](../TRUST.md#interpretations); this page gives only what is
specific to the instructions concerned. Sources are cited as files under
`arm-v9.4-a/src` of the sail-arm checkout pinned in
[ci/versions.env](../ci/versions.env). s2n-bignum's definitions are in
[instruction.ml](../../../arm/proofs/instruction.ml).

## Duplicate load destinations

This was an error in s2n-bignum, now corrected.

`LDP XZR, XZR, [X0]` (opcode `0xa9407c1f`) loads into two zero
registers. The original `arm_LDP` treated it as safe, because two
read-only zero-register destinations are orthogonal components. It
therefore required a 16-byte load event and rejected an unchanged state.
Arm permits a NOP for equal load destinations, including XZR.

The corrected `arm_LDP` also requires `~(Rt1 = Rt2)`. Equal destinations
now take its existing `ASSIGNS entirety` branch, which permits every
final state: both a NOP and a load whose writes to XZR have no effect.
This over-approximates Arm's constrained choices; it does not claim that
the architecture permits arbitrary corruption. Distinct destinations keep
their load, writeback and event. s2n-bignum's decoder accepts LDP with
equal destinations, but no s2n-bignum function contains one, so no proof
of s2n-bignum code depended on the old behaviour. The Sail theorems are about
`arm_LDP` itself, over every register field. Under the old guard
`LDP XZR, XZR` was inside it, where Sail permits outcomes that the old
`arm_LDP` rejected, so the relations could not agree.

The Sail pair decoder tests `t == t2`, including `t == t2 == 31`
(`instrs64.sail:31834`). It asserts that `ConstrainUnpredictable`
returns `Constraint_UNKNOWN`, `Constraint_UNDEF` or `Constraint_NOP`.
The NOP branch calls `EndOfInstruction`, which throws
`Error_ExceptionTaken` before the memory access (`builtins.sail:51`).
`ConstrainUnpredictable` has a body: it returns `__UNKNOWN_Constraint()`
(`stubs.sail:140`), which is `undefined` (`v8_base.sail:2038`). No file
chooses NOP. The finding is that the decoder admits the NOP branch under
this unresolved choice, not that an emulator would choose it.

Arm's September 2026 A64 ASL release confirms the permission: the shared
decode in `ldp_gen.xml` tests `t == t2` without an exception for XZR and
admits UNKNOWN, UNDEFINED and NOP. The UNKNOWN choice reads memory and
then replaces both results with arbitrary values, which the X-register
setter discards for register 31; so a load with no register update is
also permitted. The archive came from the link on Arm's
[manual service](https://documentation-service.arm.com/documentation/ddi0487/latest)
([A64 instruction XML](https://developer.arm.com/-/cdn-downloads/permalink/Exploration-Tools-A64-ISA/ISA_A64/ISA_A64_xml_A_profile-2026-09_md.tar.gz),
SHA256
`62917cba0da668deb6c28005231f4b94d1044cd52dbe4a4729fcc26d1642d827`). It
is inspection evidence, not an input to the checks. The pinned Sail tree
derives from an older ASL snapshot, so this confirms the rule, not the
exact text.

[arm-memory-pair.ml](../proofs/arm-memory-pair.ml) checks s2n-bignum's
symbolic execution after the fix: `ARM_EXEC_CONV` takes the unsafe branch
for `arm_LDP XZR XZR X0 No_Offset` and executes
`arm_LDP X1 X2 X0 No_Offset`. This is a regression check of s2n-bignum,
not a theorem about Sail. Equal destinations now lie outside the guard
of the pair theorems, so no theorem says anything about them
([memory notes](ARM-MEMORY-CONTRACTS.md#proofs)).

## Access events

Sail structure accesses perform one access per lane, and pair loads can
perform two eight-byte accesses, where s2n-bignum records one combined
access. The event lists therefore differ even when every byte agrees. The
memory theorems erase both final event lists and observe everything else
([TRUST.md](../TRUST.md#interpretations)). They do not claim that the
traces agree, or that admitting each lane's access admits their combined
range.

## Saturation

Sail's saturating narrowing and doubling-multiply instructions set
`FPSR.QC` (bit 27 of the 64-bit `FPSR_Type`, `v8_base.sail:2766`) when a
lane saturates. s2n-bignum's state has no FPSR. The exports omit FPSR
writes; the saturating calculations, FPSR reads and other effects remain,
and the theorems quantify the FPSR read component. This affects the
public definitions SQSHRUN, SQSHRUN2, SQRSHRUN and SQRSHRUN2, proved in
[arm-vector-saturating-narrow.ml](../proofs/arm-vector-saturating-narrow.ml),
and SQDMULH_VEC and SQRDMULH_VEC, proved in
[arm-vector-doubling.ml](../proofs/arm-vector-doubling.ml). Their
theorems include saturating inputs, every legal shift, lane and register
overlap. They do not cover FPSR or code that reads it later.

## Branch metadata

Sail's BTI decoder updates `BTypeCompatible` and its execute body sets
`BTypeNext`; RET sets `BTypeNext = 0` before its indirect branch.
s2n-bignum's state has neither register, and `arm_BTI` is a no-op. The
exports omit both writes; the calculations, reads and assertions remain.
The RET theorem covers every encoded register, including XZR; disabled
GCS skips its PCR and PSTATE queries, and the RET decoder selects no PAC.
The BTI theorem covers the exact `BTI c` encoding that s2n-bignum's
decoder accepts, with its PSTATE component quantified. Neither shows that
hardware preserves the metadata or that branch protection agrees.

## Cosimulation

s2n-bignum's AArch64 cosimulation could not have found the duplicate-LDP
difference. Its [state vector](../../../arm/proofs/simulator.ml) holds
X0-X30, NZCV, Q0-Q31 and 256 bytes of scratch memory, but no access
events, FPSR or branch metadata, and its pair-memory generator forces
distinct destination registers. A concrete backend also picks one of the
permitted constrained-unpredictable outcomes, so a passing comparison
does not show that the permitted sets agree.

## Configuration

The exports keep these calculations and assertions under the processor
facts of `Arm.assumptions`:

- ADDV's `Reduce` computes an FP-control selection before the integer
  addition (`v8_base.sail:30824`). With AFP available it calls
  `UsingAArch32`, which checks `PSTATE.nRW` (`v8_base.sail:4026`); the
  facts `FEAT_AA64EL0` and `nRW = 0` satisfy that check, and FPCR stays
  arbitrary ([arm-vector-add-reduce.ml](../proofs/arm-vector-add-reduce.ml)).
- FMOV evaluates `FPCR_read` and `IsMerging` before selecting a move
  (`instrs64.sail:14256`). `IsMerging` can query SME and `PSTATE.SM`
  (`v8_base.sail:16708`); the facts `FEAT_SME` and `SM = 0` select
  non-streaming execution. `__get_FPCR` masks FPCR using
  implementation-defined answers (`v8_base.sail:3561`) that the loaded
  `ImpDefBool` body supplies; the backend does not invent them
  ([arm-vector-fpbits.ml](../proofs/arm-vector-fpbits.ml) quantifies
  FPCR).
- PMULL's decoder checks `HaveBit128PMULLExt` for 64-bit lanes
  (`instrs64.sail:39761`), which queries `FEAT_PMULL`
  (`v8_base.sail:12561`). The fact `FEAT_PMULL` permits those forms;
  [arm-vector-poly.ml](../proofs/arm-vector-poly.ml) covers both lane
  sizes and both halves. A processor without the feature is not covered.
