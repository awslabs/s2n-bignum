(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the proof (see          *)
(* compute_pack_t0_t1_44_spec.ml).                                           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/compute_pack_t0_t1_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/lazy_eq_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;

let CPT44_EXEC = MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_EXEC;;

let CPT44_EXP_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;;

let CPT44_ROW_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;;

(* ------------------------------------------------------------------------- *)
(* The frame of 3216 bytes is at stackpointer + 1552 (the 1552 bytes below   *)
(* it are those of mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy),    *)
(* with the saved registers at stackpointer + 1552, the canary at            *)
(* stackpointer + 4760 and the buffers, aligned to 32 bytes, at stackpointer *)
(* + 1632 or + 1648: the matrix sampled on demand (the polynomial cur and    *)
(* rho), and then the polynomials t0k and t1k. Polynomial k of t, as the     *)
(* code computes it (mld_compute_t_lazy).                                    *)
(* ------------------------------------------------------------------------- *)

let CPT44_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 1663 1632 1648;;

let CPT44_PACK_T1 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`4`; `mld_polyeta_unpack_2`; `96`] MLD_COMPUTE_T_LAZY_PACK_T1);;

let CPT44_PACK_T0 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`4`; `mld_polyeta_unpack_2`; `96`] MLD_COMPUTE_T_LAZY_PACK_T0);;

let CPT44_ALLOWED =
  [`pc:num`; `pkt1:int64`; `t0:int64`; `s1hat:int64`; `s2:int64`;
   `rho:int64`; `r:num`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let CPT44_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc CPT44_EXEC name
   ilist CPT44_ALLOWED n;;

let CPT44_LOOP_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc CPT44_EXEC name
   ilist (`i:num`::CPT44_ALLOWED) n;;

let CPT44_INVARIANT b =
  let t = subst
   [mk_small_numeral b,`b:num`; mk_small_numeral(b + 1024),`b0:num`;
    mk_small_numeral(b + 1056),`b1:num`; mk_small_numeral(b + 2080),`b2:num`]
   `\i s. read X19 s = word_add stackpointer (word b2) /\
          read X20 s = word_add stackpointer (word b1) /\
          read X21 s = word i /\
          read X22 s = word_add s2 (word(96 * i)) /\
          read X23 s = s1hat /\
          read X24 s = word_add t0 (word(416 * i)) /\
          read X25 s = word_add pkt1 (word(320 * i)) /\
          read X26 s = word_add stackpointer (word b) /\
          read SP s = word_add stackpointer (word 1552) /\
          read (memory :> bytes64 (word_add stackpointer (word 1552))) s =
            x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 1560))) s =
            x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 1568))) s =
            x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 1576))) s =
            x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 1584))) s =
            x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 1592))) s =
            x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 1600))) s =
            x25_init /\
          read (memory :> bytes64 (word_add stackpointer (word 1608))) s =
            x26_init /\
          read (memory :> bytes64 (word_add stackpointer (word 1616))) s =
            returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 4760))) s =
            canary /\
          read (memory :> bytes64
                 (word_add (word pc) (word got_stack_chk_guard))) s =
            guard /\
          read (memory :> bytes64 guard) s = canary /\
          read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
            mf /\
          read (memory :> bytes (ea,el)) s = ev /\
          read (memory :> bytes (word_add stackpointer (word b0),32)) s = r /\
          (!j. j < 1024
               ==> read(memory :> bytes32(word_add s1hat (word(4 * j)))) s =
                   sh j) /\
          (!j. j < 384
               ==> read(memory :> bytes8(word_add s2 (word j))) s = s2b j) /\
          (!j. j < 320 * i
               ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                   mld_polyvec_pack 320 mld_polyt1_pack
                    (mld_polyvec_map mld_poly_power2round_hi
                      (mld_compute_t_lazy 4 mld_polyeta_unpack_2 96 r sh s2b)) j) /\
          (!j. j < 416 * i
               ==> read(memory :> bytes8(word_add t0 (word j))) s =
                   mld_polyvec_pack 416 mld_polyt0_pack
                    (mld_polyvec_map mld_poly_power2round_lo
                      (mld_compute_t_lazy 4 mld_polyeta_unpack_2 96 r sh s2b)) j)`
  in t;;

(* ------------------------------------------------------------------------- *)
(* The three parts of the loop proof, in each case of the stack alignment:   *)
(* the prologue with the copy of rho into the matrix structure, the loop     *)
(* body for row i, and the zeroing of the buffers, the check of the canary   *)
(* and the return.                                                           *)
(* ------------------------------------------------------------------------- *)

let CPT44_PROLOGUE_TAC b =
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC CPT44_EXEC (1--5) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC CPT44_EXEC (6--13) THEN
  MEXP_BUFFER_TAC CPT44_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC CPT44_EXEC (14--23) THEN
  MLD_LAZY_RHO_BYTES_TAC "s23" THEN
  CPT44_CALL_TAC "H_EXP"
   [`read X0 s`; `read X1 s`; MLD_LAZY_RHO_BYTES "s23"; `pc:num`;
    `read X30 s`] 24 THEN
  MLD_LAZY_RHO_COPY_TAC (MEXP_SP(b + 1024)) "s24" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT44_ROW = `mld_polyvec_matrix_row_lazy 4 r (sh:num->int32) i`;;

let CPT44_UNPACK = `mld_polyeta_unpack_2 (\j. (s2b:num->byte)(96 * i + j))`;;

let CPT44_ADD =
  mk_comb(mk_comb(`mld_poly_add`,mk_comb(`mld_poly_invntt_tomont`,CPT44_ROW)),
          CPT44_UNPACK);;

let CPT44_CADDQ =
  mk_comb(`mld_poly_caddq`,mk_comb(`mld_poly_reduce`,CPT44_ADD));;

let CPT44_JOIN_TAC pth =
  MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[pth]];;

let CPT44_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC CPT44_EXEC (1--5) THEN
  SUBGOAL_THEN
   `word_zx(word_zx(word i:int64):int32):int64 = word i /\
    word_zx(word_add (word_zx(word i:int64):int32) (word 1)):int64 =
    word(i + 1)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WORD_ZX_ZX_SMALL; MATCH_MP_TAC WORD_ZX_ADD_SMALL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CPT44_LOOP_CALL_TAC "H_ROW"
   [`read X0 s`; `read X1 s`; `read X2 s`; `r:num`; `sh:num->int32`;
    `i:num`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 6 THEN
  ARM_STEPS_TAC CPT44_EXEC (7--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP WORD_ZX_ADD_SMALL
     (ARITH_RULE `i < 4 ==> i + 1 < 2 EXP 32`
       |> C MP (ASSUME `i < 4`))]) THEN
  CPT44_LOOP_CALL_TAC "H_INV"
   [`read X0 s`; CPT44_ROW; `pc:num`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC CPT44_EXEC (11--13) THEN
  VEC_SLICE_TAC
   `!j. j < 96
        ==> read(memory :> bytes8(word_add s2 (word(96 * i + j)))) s13 =
            (s2b:num->byte)(96 * i + j)` THEN
  CPT44_LOOP_CALL_TAC "H_UNPACK"
   [`read X0 s`; `read X1 s`; `\j. (s2b:num->byte)(96 * i + j)`; `pc:num`;
    `read X30 s`] 14 THEN
  ARM_STEPS_TAC CPT44_EXEC (15--18) THEN
  CPT44_LOOP_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; mk_comb(`mld_poly_invntt_tomont`,CPT44_ROW);
    CPT44_UNPACK; `pc:num`; `read X30 s`] 19 THEN
  ARM_STEPS_TAC CPT44_EXEC (20--21) THEN
  CPT44_LOOP_CALL_TAC "H_RED"
   [`read X0 s`; CPT44_ADD; `pc:num`; `read X30 s`] 22 THEN
  ARM_STEPS_TAC CPT44_EXEC (23--24) THEN
  CPT44_LOOP_CALL_TAC "H_CADDQ"
   [`read X0 s`; mk_comb(`mld_poly_reduce`,CPT44_ADD); `pc:num`;
    `read X30 s`] 25 THEN
  ARM_STEPS_TAC CPT44_EXEC (26--29) THEN
  CPT44_LOOP_CALL_TAC "H_P2R"
   [`read X0 s`; `read X1 s`; CPT44_CADDQ; `pc:num`; `read X30 s`] 30 THEN
  ARM_STEPS_TAC CPT44_EXEC (31--33) THEN
  CPT44_LOOP_CALL_TAC "H_T1"
   [`read X0 s`; `read X1 s`; mk_comb(`mld_poly_power2round_hi`,CPT44_CADDQ);
    `pc:num`; `read X30 s`] 34 THEN
  ARM_STEPS_TAC CPT44_EXEC (35--38) THEN
  CPT44_LOOP_CALL_TAC "H_T0"
   [`read X0 s`; `read X1 s`; mk_comb(`mld_poly_power2round_lo`,CPT44_CADDQ);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 39 THEN
  ARM_STEPS_TAC CPT44_EXEC (40--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CPT44_JOIN_TAC CPT44_PACK_T1 THEN NO_TAC) THEN
  TRY(CPT44_JOIN_TAC CPT44_PACK_T0 THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT44_MEMSET_TAC n =
  LIBC_PLT_TAC CPT44_EXEC n THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" CPT44_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref CPT44_ALLOWED) (n + 5);;

let CPT44_EPILOGUE_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC CPT44_EXEC (1--4) THEN CPT44_MEMSET_TAC 4 THEN
  ARM_STEPS_TAC CPT44_EXEC (10--13) THEN CPT44_MEMSET_TAC 13 THEN
  ARM_STEPS_TAC CPT44_EXEC (19--22) THEN CPT44_MEMSET_TAC 22 THEN
  ARM_STEPS_TAC CPT44_EXEC (28--28) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC CPT44_EXEC (29--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT44_CASE_TAC b =
  ENSURES_EVENTS_WHILE_UP2_TAC `4`
   `pc + mld_compute_pack_t0_t144_loop1`
   `pc + mld_compute_pack_t0_t144_loop1_exit`
   (CPT44_INVARIANT b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; CPT44_PROLOGUE_TAC b; CPT44_BODY_TAC; CPT44_EPILOGUE_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, with t as the code computes *)
(* it (mld_compute_t_lazy) and without the bound on s1hat: the statement of  *)
(* the FULL theorem with these changes (MLD_LAZY_FULL0 of                    *)
(* utils/mldsa_native_lazy_matrix.ml).                                       *)
(* ------------------------------------------------------------------------- *)

let CPT44_FULL0 = prove
 (MLD_LAZY_FULL0
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP CPT44_ROW_FULL th) "H_ROW") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT44_EXP_FULL "H_EXP" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_ADD_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_INPLACE
   "H_P2R" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_T1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_T0" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pkt1:int64) (t0:int64) (s1hat:int64) (s2:int64) (rho:int64) (r:num)
     (guard:int64) (mf:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     if aligned 32 stackpointer
     then APPEND
           (f_ev_epil_a pkt1 t0 s1hat s2 rho r guard mf pc stackpointer
                        returnaddress)
           (APPEND
             (ENUMERATEL 4
               (\i. f_ev_loop_a pkt1 t0 s1hat s2 rho r guard mf pc
                                stackpointer returnaddress i))
             (f_ev_prol_a pkt1 t0 s1hat s2 rho r guard mf pc stackpointer
                          returnaddress))
     else APPEND
           (f_ev_epil_u pkt1 t0 s1hat s2 rho r guard mf pc stackpointer
                        returnaddress)
           (APPEND
             (ENUMERATEL 4
               (\i. f_ev_loop_u pkt1 t0 s1hat s2 rho r guard mf pc
                                stackpointer returnaddress i))
             (f_ev_prol_u pkt1 t0 s1hat s2 rho r guard mf pc stackpointer
                          returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst CPT44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 4768):int64)` THEN
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
  PAR_THENL (ASM_CASES_TAC `aligned 32 (stackpointer:int64)`)
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    CPT44_CASE_TAC 1632;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    CPT44_CASE_TAC 1648]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, with t = mld_compute_t for  *)
(* s1hat within the bound (MLD_LAZY_COMPUTE_T_PACK, with the bound of the    *)
(* unpacked coefficients of s2).                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  MLD_LAZY_FULL_OF_FULL0_TAC CPT44_FULL0
   (MP_TAC(SPECL [`4`; `4`; `mld_polyeta_unpack_2`; `96`; `r:num`; `sh:num->int32`;
                  `s2b:num->byte`] MLD_LAZY_COMPUTE_T_PACK) THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[MLD_LAZY_ETA_UNPACK_BOUND];
      CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN STRIP_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC (MP (SPEC_ALL CPT44_FULL0) th)));;
