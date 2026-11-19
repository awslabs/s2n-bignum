(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a message into a SHAKE128 context: the proof (see             *)
(* shake128_absorb_spec.ml).                                                 *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/shake128_absorb_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

let SHAKE_ZX_WORD_SMALL = prove
 (`!x. x < 2 EXP 32 ==> word_zx(word x:int64):int32 = word x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`]);;

let SHAKE_POS_SMALL = prove
 (`!pos inlen S M. SND(mld_keccak_absorb 168 S pos inlen M) < 2 EXP 32`,
  REWRITE_TAC[mld_keccak_absorb] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[SND] THEN REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`pos + inlen`; `168`] MOD_LT_EQ) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The function loads the      *)
(* position, calls keccak_absorb with the rate 168 and stores the position   *)
(* that it returns. The frame is the 16 bytes of the function and the 288    *)
(* of keccak_absorb below them.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_OS_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_ABSORB" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `ctx:int64`; `src:int64`; `inlen:num`;
    `S:1600 word`; `pos:num`; `M:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 304 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--7) THEN
  ARGS_64_TAC [`pos:num`] THEN
  KECCAK_STATE_AT_TAC `ctx:int64` THEN
  REMOVE_THEN "H_ABSORB" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mldsa_native_libmldsa_gcc12_Os_mc,EXEC,
      0x0,mldsa_native_libmldsa_gcc12_Os_mc,safety_th)
     [`e:(uarch_event)list`; `read X0 s`; `pos:num`; `168`; `read X3 s`;
      `inlen:num`; `S:1600 word`; `M:num`; `pc:num`; `read SP s`;
      `read X30 s`] 8 THENL
     [EXISTS_E2_TAC
       (ref [`ctx:int64`; `src:int64`; `inlen:num`; `pos:num`; `pc:num`;
             `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC "H_ABSORB" safety_th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC EXEC (9--11) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SHAKE_ZX_WORD_SMALL THEN REWRITE_TAC[SHAKE_POS_SMALL];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
