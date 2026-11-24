(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the proof (see          *)
(* compute_pack_t0_t1_65_spec.ml).                                           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/compute_pack_t0_t1_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;

let CPT65_EXEC = MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_OS_EXEC;;

let CPT65_MEXP_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_FULL;;

let CPT65_ROW_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_FULL;;

(* ------------------------------------------------------------------------- *)
(* The frame of 32896 bytes is at stackpointer + 5088 (the 5088 bytes below  *)
(* it are those of mldsa65_polyvec_matrix_expand_eager), with the saved      *)
(* registers at stackpointer + 5088, the canary at stackpointer + 37976 and  *)
(* the buffers, aligned to 32 bytes, at stackpointer + 5184 or + 5200: the   *)
(* matrix and then the polynomials t1k and t0k. Polynomial k of t, as the    *)
(* code computes it.                                                         *)
(* ------------------------------------------------------------------------- *)

(*** Replace the value of a 64-bit register, a sum with a product of the  ***)
(*** loop counter, by the address that the assumptions use.                ***)

let CPT_REG_TAC (reg:term) (tm:term) =
  let rd = `read:(armstate,int64)component->armstate->int64` in
  FIRST_ASSUM(fun th ->
    try let l,r = dest_eq(concl th) in
        if rator l = mk_comb(rd,reg)
        then SUBGOAL_THEN (mk_eq(r,tm)) SUBST_ALL_TAC THENL
              [CONV_TAC WORD_RULE; ALL_TAC]
        else NO_TAC
    with Failure _ -> NO_TAC);;

let CPT65_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 5215 5184 5200;;

let CPT65_PACK_T1 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`5`; `mld_polyeta_unpack_4`; `128`] MLD_COMPUTE_T_PACK_T1);;

let CPT65_PACK_T0 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`5`; `mld_polyeta_unpack_4`; `128`] MLD_COMPUTE_T_PACK_T0);;

let CPT65_ALLOWED =
  [`pc:num`; `pkt1:int64`; `t0:int64`; `s1hat:int64`; `s2:int64`;
   `rho:int64`; `r:num`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let CPT65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc CPT65_EXEC name ilist
   CPT65_ALLOWED n;;

let CPT65_LOOP_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc CPT65_EXEC name ilist
   (`i:num`::CPT65_ALLOWED) n;;

let CPT65_INVARIANT b =
  let t = subst
   [mk_small_numeral b,`b:num`; mk_small_numeral(b + 30720),`b1:num`;
    mk_small_numeral(b + 31744),`b2:num`]
   `\i s. read X19 s = word_add stackpointer (word b2) /\
          read X20 s = word_add stackpointer (word b) /\
          read X21 s = word i /\
          read X22 s = word_add stackpointer (word b1) /\
          read X23 s = t0 /\
          read X24 s = pkt1 /\
          read X25 s = s2 /\
          read X26 s = s1hat /\
          read X27 s = word 416 /\
          read X28 s = word 320 /\
          read SP s = word_add stackpointer (word 5088) /\
          read (memory :> bytes64 (word_add stackpointer (word 5088))) s =
            x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5096))) s =
            x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5104))) s =
            x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5112))) s =
            x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5120))) s =
            x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5128))) s =
            x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5136))) s =
            x25_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5144))) s =
            x26_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5152))) s =
            x27_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5160))) s =
            x28_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5168))) s =
            returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 37976))) s =
            canary /\
          read (memory :> bytes64
                 (word_add (word pc) (word got_stack_chk_guard))) s =
            guard /\
          read (memory :> bytes64 guard) s = canary /\
          read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
            mf /\
          read (memory :> bytes (ea,el)) s = ev /\
          (!j. j < 7680
               ==> read (memory :> bytes32
                          (word_add stackpointer (word(b + 4 * j)))) s =
                   mld_polyvec_matrix_expand 5 r j) /\
          (!j. j < 1280
               ==> read(memory :> bytes32(word_add s1hat (word(4 * j)))) s =
                   sh j) /\
          (!j. j < 768
               ==> read(memory :> bytes8(word_add s2 (word j))) s = s2b j) /\
          (!j. j < 320 * i
               ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                   mld_polyvec_pack 320 mld_polyt1_pack
                    (mld_polyvec_map mld_poly_power2round_hi
                      (mld_compute_t 5 mld_polyeta_unpack_4 128 r sh s2b)) j) /\
          (!j. j < 416 * i
               ==> read(memory :> bytes8(word_add t0 (word j))) s =
                   mld_polyvec_pack 416 mld_polyt0_pack
                    (mld_polyvec_map mld_poly_power2round_lo
                      (mld_compute_t 5 mld_polyeta_unpack_4 128 r sh s2b)) j)`
  in t;;

(* ------------------------------------------------------------------------- *)
(* The three parts of the loop proof, in each case of the stack alignment:   *)
(* the prologue with the expansion of the matrix, the loop body for row i,   *)
(* and the zeroing of the buffers, the check of the canary and the return.   *)
(* ------------------------------------------------------------------------- *)

let CPT65_PROLOGUE_TAC =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC CPT65_EXEC (1--6) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC CPT65_EXEC (7--11) THEN
  MEXP_BUFFER_TAC CPT65_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC CPT65_EXEC (12--30) THEN
  CPT65_CALL_TAC "H_MEXP"
   [`read X0 s`; `read X1 s`; `r:num`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 31 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT65_ACC =
  `mld_polyvec_pointwise_acc_montgomery 5
    (\j. mld_polyvec_matrix_expand 5 r (1280 * i + j)) (sh:num->int32)`;;

let CPT65_UNPACK = `mld_polyeta_unpack_4 (\j. (s2b:num->byte)(128 * i + j))`;;

let CPT65_ADD =
  mk_comb(mk_comb(`mld_poly_add`,mk_comb(`mld_poly_invntt_tomont`,CPT65_ACC)),
          CPT65_UNPACK);;

let CPT65_CADDQ =
  mk_comb(`mld_poly_caddq`,mk_comb(`mld_poly_reduce`,CPT65_ADD));;

let CPT65_JOIN_TAC pth =
  MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[pth]];;

let CPT65_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC CPT65_EXEC (1--4) THEN
  SUBGOAL_THEN
   `word_zx(word_zx(word i:int64):int32):int64 = word i`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC WORD_ZX_ZX_SMALL THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC CPT65_EXEC (5--5) THEN
  CPT65_LOOP_CALL_TAC "H_ROW"
   [`read X0 s`; `read X1 s`; `read X2 s`; `mld_polyvec_matrix_expand 5 r`;
    `sh:num->int32`; `i:num`; `pc:num`; `read X30 s`] 6 THEN
  ARM_STEPS_TAC CPT65_EXEC (7--8) THEN
  CPT65_LOOP_CALL_TAC "H_INV"
   [`read X0 s`; CPT65_ACC; `pc:num`; `read X30 s`] 9 THEN
  ARM_STEPS_TAC CPT65_EXEC (10--12) THEN
  CPT_REG_TAC `X1` `word_add s2 (word(128 * i)):int64` THEN
  VEC_SLICE_TAC
   `!j. j < 128
        ==> read(memory :> bytes8(word_add s2 (word(128 * i + j)))) s12 =
            (s2b:num->byte)(128 * i + j)` THEN
  CPT65_LOOP_CALL_TAC "H_UNPACK"
   [`read X0 s`; `read X1 s`; `\j. (s2b:num->byte)(128 * i + j)`; `pc:num`;
    `read X30 s`] 13 THEN
  ARM_STEPS_TAC CPT65_EXEC (14--16) THEN
  CPT65_LOOP_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; mk_comb(`mld_poly_invntt_tomont`,CPT65_ACC);
    CPT65_UNPACK; `pc:num`; `read X30 s`] 17 THEN
  ARM_STEPS_TAC CPT65_EXEC (18--19) THEN
  CPT65_LOOP_CALL_TAC "H_RED"
   [`read X0 s`; CPT65_ADD; `pc:num`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC CPT65_EXEC (21--22) THEN
  CPT65_LOOP_CALL_TAC "H_CADDQ"
   [`read X0 s`; mk_comb(`mld_poly_reduce`,CPT65_ADD); `pc:num`;
    `read X30 s`] 23 THEN
  ARM_STEPS_TAC CPT65_EXEC (24--27) THEN
  CPT65_LOOP_CALL_TAC "H_P2R"
   [`read X0 s`; `read X1 s`; CPT65_CADDQ; `pc:num`; `read X30 s`] 28 THEN
  ARM_STEPS_TAC CPT65_EXEC (29--29) THEN
  CPT_REG_TAC `X0` `word_add pkt1 (word(320 * i)):int64` THEN
  ARM_STEPS_TAC CPT65_EXEC (30--31) THEN
  CPT65_LOOP_CALL_TAC "H_T1"
   [`read X0 s`; `read X1 s`; mk_comb(`mld_poly_power2round_hi`,CPT65_CADDQ);
    `pc:num`; `read X30 s`] 32 THEN
  ARM_STEPS_TAC CPT65_EXEC (33--36) THEN
  CPT_REG_TAC `X0` `word_add t0 (word(416 * i)):int64` THEN
  CPT65_LOOP_CALL_TAC "H_T0"
   [`read X0 s`; `read X1 s`; mk_comb(`mld_poly_power2round_lo`,CPT65_CADDQ);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 37 THEN
  ARM_STEPS_TAC CPT65_EXEC (38--39) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CPT65_JOIN_TAC CPT65_PACK_T1 THEN NO_TAC) THEN
  TRY(CPT65_JOIN_TAC CPT65_PACK_T0 THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT65_ZERO_TAC n len =
  CPT65_CALL_TAC "H_ZERO"
   [`read X0 s`; mk_small_numeral len; `pc:num`; `read SP s`;
    `read X30 s`] n;;

let CPT65_EPILOGUE_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC CPT65_EXEC (1--3) THEN CPT65_ZERO_TAC 4 1024 THEN
  ARM_STEPS_TAC CPT65_EXEC (5--7) THEN CPT65_ZERO_TAC 8 1024 THEN
  ARM_STEPS_TAC CPT65_EXEC (9--11) THEN CPT65_ZERO_TAC 12 30720 THEN
  ARM_STEPS_TAC CPT65_EXEC (13--13) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC CPT65_EXEC (14--30) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT65_CASE_TAC b =
  ENSURES_EVENTS_WHILE_UP2_TAC `6`
   `pc + mld_compute_pack_t0_t165_loop1`
   `pc + mld_compute_pack_t0_t165_loop1_exit`
   (CPT65_INVARIANT b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; CPT65_PROLOGUE_TAC; CPT65_BODY_TAC; CPT65_EPILOGUE_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP CPT65_MEXP_FULL th) "H_MEXP") THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MP (SPEC_ALL MLDSA_NATIVE_ZEROIZE_4_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)
     "H_ZERO") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT65_ROW_FULL "H_ROW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_CADDQ_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL_INPLACE
   "H_P2R" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYT1_PACK_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_T1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_T0" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pkt1:int64) (t0:int64) (s1hat:int64) (s2:int64) (rho:int64) (r:num)
     (guard:int64) (mf:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     if aligned 32 stackpointer
     then APPEND
           (f_ev_epil_a pkt1 t0 s1hat s2 rho r guard mf pc stackpointer
                        returnaddress)
           (APPEND
             (ENUMERATEL 6
               (\i. f_ev_loop_a pkt1 t0 s1hat s2 rho r guard mf pc
                                stackpointer returnaddress i))
             (f_ev_prol_a pkt1 t0 s1hat s2 rho r guard mf pc stackpointer
                          returnaddress))
     else APPEND
           (f_ev_epil_u pkt1 t0 s1hat s2 rho r guard mf pc stackpointer
                        returnaddress)
           (APPEND
             (ENUMERATEL 6
               (\i. f_ev_loop_u pkt1 t0 s1hat s2 rho r guard mf pc
                                stackpointer returnaddress i))
             (f_ev_prol_u pkt1 t0 s1hat s2 rho r guard mf pc stackpointer
                          returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst CPT65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 37984):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28) THEN
  PAR_THENL (ASM_CASES_TAC `aligned 32 (stackpointer:int64)`)
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    CPT65_CASE_TAC 5184;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    CPT65_CASE_TAC 5200]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;
