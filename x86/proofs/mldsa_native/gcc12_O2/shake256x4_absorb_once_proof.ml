(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_shake256x4_absorb_once (see                           *)
(* shake256x4_absorb_once_spec.ml): that of mldsa_shake128x4_absorb_once     *)
(* (see shake128x4_absorb_once_proof.ml), with the rate 136 of SHAKE256 for  *)
(* the rate 168 of SHAKE128: the code differs only in that constant.         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/shake256x4_absorb_once_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_memset.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The memset of the 800 bytes *)
(* of the context, which may not be aligned, is inlined as zero quadword     *)
(* stores at its start and end and a REP STOSQ of 99 quadwords in between    *)
(* (see MEMSET_PREP_TAC in utils/mldsa_native_keccak.ml), and the seventh    *)
(* argument of mld_keccak_absorb_once_x4 is pushed on the stack. The frame   *)
(* of 416 bytes is at stackpointer, with the slot of that argument at        *)
(* stackpointer + 392 and the return address of the call below it.           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN

  (*** The memset of the context ***)

  X86_STEPS_TAC EXEC (1--12) THEN
  MEMSET_PREP_TAC THEN
  MEMSET_STEP_TAC EXEC 13 THEN
  MEMSET_DONE_TAC `st:int64` 800 "s13" THEN

  (*** The call of mld_keccak_absorb_once_x4 with the rate 136 ***)

  X86_STEPS_TAC EXEC (14--21) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_ABSORB"
   [`read RDI s`; `136`; `read RDX s`; `read RCX s`; `read R8 s`;
    `read R9 s`; `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`st:int64`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`;
    `mlen:num`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`] 22 THEN
  X86_STEPS_TAC EXEC (23--24) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
