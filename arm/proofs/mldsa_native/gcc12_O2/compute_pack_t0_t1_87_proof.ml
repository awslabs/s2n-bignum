(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the proof (see          *)
(* compute_pack_t0_t1_87_spec.ml).                                           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/compute_pack_t0_t1_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;

let CPT87_EXEC = MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_EXEC;;

let CPT87_MEXP_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL;;

let CPT87_ROW_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL;;

(* ------------------------------------------------------------------------- *)
(* The frame of 32880 bytes is at stackpointer + 5056 (the 5056 bytes below  *)
(* it are those of mldsa65_polyvec_matrix_expand_eager), with the saved      *)
(* registers at stackpointer + 5056, the canary at stackpointer + 37928 and  *)
(* the buffers, aligned to 32 bytes, at stackpointer + 5152 or + 5136: the   *)
(* matrix and then the polynomials t1k and t0k. Polynomial k of t, as the    *)
(* code computes it.                                                         *)
(* ------------------------------------------------------------------------- *)

let CPT87_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 5167 5152 5136;;

let CPT87_PACK_T1 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`7`; `mld_polyeta_unpack_2`; `96`] MLD_COMPUTE_T_PACK_T1);;

let CPT87_PACK_T0 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`7`; `mld_polyeta_unpack_2`; `96`] MLD_COMPUTE_T_PACK_T0);;

let CPT87_ALLOWED =
  [`pc:num`; `pkt1:int64`; `t0:int64`; `s1hat:int64`; `s2:int64`;
   `rho:int64`; `r:num`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let CPT87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc CPT87_EXEC name ilist
   CPT87_ALLOWED n;;

let CPT87_LOOP_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc CPT87_EXEC name ilist
   (`i:num`::CPT87_ALLOWED) n;;

let CPT87_INVARIANT b =
  let t = subst
   [mk_small_numeral b,`b:num`; mk_small_numeral(b + 57344),`b1:num`;
    mk_small_numeral(b + 58368),`b2:num`]
   `\i s. read X19 s = word_add stackpointer (word b2) /\
          read X20 s = word_add stackpointer (word b1) /\
          read X21 s = word i /\
          read X22 s = word_add s2 (word(96 * i)) /\
          read X23 s = s1hat /\
          read X24 s = word_add t0 (word(416 * i)) /\
          read X25 s = word_add pkt1 (word(320 * i)) /\
          read X26 s = word_add stackpointer (word b) /\
          read SP s = word_add stackpointer (word 5056) /\
          read (memory :> bytes64 (word_add stackpointer (word 5056))) s =
            x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5064))) s =
            x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5072))) s =
            x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5080))) s =
            x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5088))) s =
            x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5096))) s =
            x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5104))) s =
            x25_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5112))) s =
            x26_init /\
          read (memory :> bytes64 (word_add stackpointer (word 5120))) s =
            returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 64552))) s =
            canary /\
          read (memory :> bytes64
                 (word_add (word pc) (word got_stack_chk_guard))) s =
            guard /\
          read (memory :> bytes64 guard) s = canary /\
          read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
            mf /\
          read (memory :> bytes (ea,el)) s = ev /\
          (!j. j < 14336
               ==> read (memory :> bytes32
                          (word_add stackpointer (word(b + 4 * j)))) s =
                   mld_polyvec_matrix_expand 7 r j) /\
          (!j. j < 1792
               ==> read(memory :> bytes32(word_add s1hat (word(4 * j)))) s =
                   sh j) /\
          (!j. j < 768
               ==> read(memory :> bytes8(word_add s2 (word j))) s = s2b j) /\
          (!j. j < 320 * i
               ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                   mld_polyvec_pack 320 mld_polyt1_pack
                    (mld_polyvec_map mld_poly_power2round_hi
                      (mld_compute_t 7 mld_polyeta_unpack_2 96 r sh s2b)) j) /\
          (!j. j < 416 * i
               ==> read(memory :> bytes8(word_add t0 (word j))) s =
                   mld_polyvec_pack 416 mld_polyt0_pack
                    (mld_polyvec_map mld_poly_power2round_lo
                      (mld_compute_t 7 mld_polyeta_unpack_2 96 r sh s2b)) j)`
  in t;;

(* ------------------------------------------------------------------------- *)
(* The three parts of the loop proof, in each case of the stack alignment:   *)
(* the prologue with the expansion of the matrix, the loop body for row i,   *)
(* and the zeroing of the buffers, the check of the canary and the return.   *)
(* ------------------------------------------------------------------------- *)

let CPT87_PROLOGUE_TAC =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC CPT87_EXEC (1--6) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC CPT87_EXEC (7--17) THEN
  MEXP_BUFFER_TAC CPT87_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC CPT87_EXEC (18--26) THEN
  CPT87_CALL_TAC "H_MEXP"
   [`read X0 s`; `read X1 s`; `r:num`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 27 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT87_ACC =
  `mld_polyvec_pointwise_acc_montgomery 7
    (\j. mld_polyvec_matrix_expand 7 r (1792 * i + j)) (sh:num->int32)`;;

let CPT87_UNPACK = `mld_polyeta_unpack_2 (\j. (s2b:num->byte)(96 * i + j))`;;

let CPT87_ADD =
  mk_comb(mk_comb(`mld_poly_add`,mk_comb(`mld_poly_invntt_tomont`,CPT87_ACC)),
          CPT87_UNPACK);;

let CPT87_CADDQ =
  mk_comb(`mld_poly_caddq`,mk_comb(`mld_poly_reduce`,CPT87_ADD));;

let CPT87_JOIN_TAC pth =
  MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[pth]];;

let CPT87_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC CPT87_EXEC (1--5) THEN
  SUBGOAL_THEN
   `word_zx(word_zx(word i:int64):int32):int64 = word i /\
    word_zx(word_add (word_zx(word i:int64):int32) (word 1)):int64 =
    word(i + 1)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WORD_ZX_ZX_SMALL; MATCH_MP_TAC WORD_ZX_ADD_SMALL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CPT87_LOOP_CALL_TAC "H_ROW"
   [`read X0 s`; `read X1 s`; `read X2 s`; `mld_polyvec_matrix_expand 7 r`;
    `sh:num->int32`; `i:num`; `pc:num`; `read X30 s`] 6 THEN
  ARM_STEPS_TAC CPT87_EXEC (7--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP WORD_ZX_ADD_SMALL
     (ARITH_RULE `i < 8 ==> i + 1 < 2 EXP 32`
       |> C MP (ASSUME `i < 8`))]) THEN
  CPT87_LOOP_CALL_TAC "H_INV"
   [`read X0 s`; CPT87_ACC; `pc:num`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC CPT87_EXEC (11--13) THEN
  VEC_SLICE_TAC
   `!j. j < 96
        ==> read(memory :> bytes8(word_add s2 (word(96 * i + j)))) s13 =
            (s2b:num->byte)(96 * i + j)` THEN
  CPT87_LOOP_CALL_TAC "H_UNPACK"
   [`read X0 s`; `read X1 s`; `\j. (s2b:num->byte)(96 * i + j)`; `pc:num`;
    `read X30 s`] 14 THEN
  ARM_STEPS_TAC CPT87_EXEC (15--18) THEN
  CPT87_LOOP_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; mk_comb(`mld_poly_invntt_tomont`,CPT87_ACC);
    CPT87_UNPACK; `pc:num`; `read X30 s`] 19 THEN
  ARM_STEPS_TAC CPT87_EXEC (20--21) THEN
  CPT87_LOOP_CALL_TAC "H_RED"
   [`read X0 s`; CPT87_ADD; `pc:num`; `read X30 s`] 22 THEN
  ARM_STEPS_TAC CPT87_EXEC (23--24) THEN
  CPT87_LOOP_CALL_TAC "H_CADDQ"
   [`read X0 s`; mk_comb(`mld_poly_reduce`,CPT87_ADD); `pc:num`;
    `read X30 s`] 25 THEN
  ARM_STEPS_TAC CPT87_EXEC (26--29) THEN
  CPT87_LOOP_CALL_TAC "H_P2R"
   [`read X0 s`; `read X1 s`; CPT87_CADDQ; `pc:num`; `read X30 s`] 30 THEN
  ARM_STEPS_TAC CPT87_EXEC (31--33) THEN
  CPT87_LOOP_CALL_TAC "H_T1"
   [`read X0 s`; `read X1 s`; mk_comb(`mld_poly_power2round_hi`,CPT87_CADDQ);
    `pc:num`; `read X30 s`] 34 THEN
  ARM_STEPS_TAC CPT87_EXEC (35--38) THEN
  CPT87_LOOP_CALL_TAC "H_T0"
   [`read X0 s`; `read X1 s`; mk_comb(`mld_poly_power2round_lo`,CPT87_CADDQ);
    `pc:num`; `read X30 s`] 39 THEN
  ARM_STEPS_TAC CPT87_EXEC (40--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CPT87_JOIN_TAC CPT87_PACK_T1 THEN NO_TAC) THEN
  TRY(CPT87_JOIN_TAC CPT87_PACK_T0 THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT87_MEMSET_TAC n =
  LIBC_PLT_TAC CPT87_EXEC n THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" CPT87_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref CPT87_ALLOWED) (n + 5);;

let CPT87_EPILOGUE_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC CPT87_EXEC (1--4) THEN CPT87_MEMSET_TAC 4 THEN
  ARM_STEPS_TAC CPT87_EXEC (10--13) THEN CPT87_MEMSET_TAC 13 THEN
  ARM_STEPS_TAC CPT87_EXEC (19--22) THEN CPT87_MEMSET_TAC 22 THEN
  ARM_STEPS_TAC CPT87_EXEC (28--28) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC CPT87_EXEC (29--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT87_CASE_TAC b =
  ENSURES_EVENTS_WHILE_UP2_TAC `8`
   `pc + mld_compute_pack_t0_t187_loop1`
   `pc + mld_compute_pack_t0_t187_loop1_exit`
   (CPT87_INVARIANT b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; CPT87_PROLOGUE_TAC; CPT87_BODY_TAC; CPT87_EPILOGUE_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP CPT87_MEXP_FULL th) "H_MEXP") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT87_ROW_FULL "H_ROW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_INPLACE
   "H_P2R" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_T1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_T0" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pkt1:int64) (t0:int64) (s1hat:int64) (s2:int64) (rho:int64) (r:num)
     (guard:int64) (mf:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     if aligned 32 stackpointer
     then APPEND
           (f_ev_epil_a pkt1 t0 s1hat s2 rho r guard mf pc stackpointer
                        returnaddress)
           (APPEND
             (ENUMERATEL 8
               (\i. f_ev_loop_a pkt1 t0 s1hat s2 rho r guard mf pc
                                stackpointer returnaddress i))
             (f_ev_prol_a pkt1 t0 s1hat s2 rho r guard mf pc stackpointer
                          returnaddress))
     else APPEND
           (f_ev_epil_u pkt1 t0 s1hat s2 rho r guard mf pc stackpointer
                        returnaddress)
           (APPEND
             (ENUMERATEL 8
               (\i. f_ev_loop_u pkt1 t0 s1hat s2 rho r guard mf pc
                                stackpointer returnaddress i))
             (f_ev_prol_u pkt1 t0 s1hat s2 rho r guard mf pc stackpointer
                          returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst CPT87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 64560):int64)` THEN
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
     (mk_const(r,[]))) (19--26) THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    CPT87_CASE_TAC 5152;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    CPT87_CASE_TAC 5136]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
