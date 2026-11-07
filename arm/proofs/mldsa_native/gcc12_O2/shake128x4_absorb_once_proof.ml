(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_shake128x4_absorb_once (see                           *)
(* shake128x4_absorb_once_spec.ml): that of the same code in the gcc12_O2    *)
(* image of mlkem-native (proofs/mlkem_native/gcc12_O2), with the names      *)
(* changed.                                                                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/shake128x4_absorb_once_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset at the address mf in  *)
(* the GOT entry, with its code and data in the region (ea,el). The result   *)
(* is as for mld_keccak_absorb_once on each message, with r = 168 and p =    *)
(* 0x1F as in shake128 in common/fips202.ml. The stack is the 304 bytes used *)
(* by mld_keccak_absorb_once_x4, which include the 64 of the function before *)
(* the tail call.                                                            *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ABSORB_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLDSA_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`;
    `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 304 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--24) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Zeroing the context with memset ***)

  ARM_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC (1--13) THEN
  LIBC_PLT_TAC MLDSA_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC 13 THEN
  LIBC_CALL_TAC "H_MEMSET" MLDSA_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 18 THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEMSET_ZERO_BYTES o
    check (fun th -> is_forall(concl th) && free_in `st:int64` (concl th) &&
                     free_in `bytes8:int64->(int64->byte,byte)component`
                             (concl th))) THEN

  (*** The tail call of mld_keccak_absorb_once_x4 ***)

  ARM_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC (19--30) THEN
  LOCAL_ABSORB_X4_TAC
   [`read X0 s`; `168`; `read X2 s`; `read X3 s`; `read X4 s`; `read X5 s`;
    `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 31 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
