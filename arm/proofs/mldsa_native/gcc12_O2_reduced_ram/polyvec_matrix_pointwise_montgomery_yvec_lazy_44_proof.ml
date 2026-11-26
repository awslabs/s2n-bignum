(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The product w = A y of signing, with A sampled on demand and y sampled    *)
(* polynomial by polynomial: the proof (see                                  *)
(* polyvec_matrix_pointwise_montgomery_yvec_lazy_44_spec.ml).                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_yvec_lazy_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;

let YVL44_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_EXEC;;

let YVL44_G = `mld_poly_uniform_gamma1_17`;;

(* ------------------------------------------------------------------------- *)
(* The events (MLD_LAZY_YVEC_TEMPLATE of                                     *)
(* common/fips204/properties/mldsa_native_lazy_matrix.ml): the prologue, the *)
(* first column, the loop over the columns 1, ..., 3, each with the loop     *)
(* over the 4 rows, and the epilogue. The buffer of the seed, which the code *)
(* aligns to 32 bytes in its frame, is the variable buf                      *)
(* (MLD_LAZY_BUFFER_SETUP_TAC), which MLD_LAZY_UNBUF_TAC expands at the end  *)
(* of each part, and the events of the samplings of the entries depend on    *)
(* their seeds, functions of rho and the indices.                            *)
(* ------------------------------------------------------------------------- *)

let YVL44_TEMPLATE = MLD_LAZY_YVEC_TEMPLATE 4 4;;

let YVL44_ALLOWED =
  [`pc:num`; `w:int64`; `mat:int64`; `y:int64`; `scratch:int64`; `r:num`;
   `rp:int64`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `buf:int64`];;

let YVL44_CALL_TAC vars name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc YVL44_EXEC name
   ilist (vars @ YVL44_ALLOWED) n;;

(* ------------------------------------------------------------------------- *)
(* The invariants, with the frame of utils/mldsa_native_lazy_matrix.ml       *)
(* (MLD_LAZY_INV_FRAME). The column j is counted in W22 and the row i in     *)
(* W19, with the address of row i of w in X21, and the buffer of the seed is *)
(* at X20. From loop2, a row of the first column (W22 = 0) takes the path at *)
(* +0x110, which samples entry (i,0) into row i of w and multiplies it with  *)
(* scratch, and a row of another column samples entry (i,j) into the         *)
(* polynomial cur at mat, multiplies it with scratch and adds it to row i of *)
(* w; both paths join at join1, before the test of the inner loop, whose     *)
(* exit is loop2_exit. At loop1 for column l + 1 (OUTER), w holds the sums   *)
(* for the columns up to l; at loop2 for row i (INNER), polynomial l + 1 of  *)
(* the transform of y is in scratch and the rows before i also have the      *)
(* products for column l + 1; and the same for the first column (J1_0,       *)
(* INNER0).                                                                  *)
(* ------------------------------------------------------------------------- *)

let YVL44_YHAT = MLD_LAZY_INV_YHAT "mld_poly_uniform_gamma1_17";;

let YVL44_YH = parse_term YVL44_YHAT;;

let YVL44_FRAME = MLD_LAZY_INV_FRAME "X20";;

let YVL44_OUTER = parse_term
 ("\\l s. " ^ YVL44_FRAME ^ " /\\ read X22 s = word(l + 1) /\\ " ^
  MLD_LAZY_INV_W YVL44_YHAT "1024" "l");;

let YVL44_J1_0 = parse_term
 ("\\s. " ^ YVL44_FRAME ^ " /\\ read X22 s = word 0");;

let YVL44_INNER0 = parse_term
 ("\\i s. " ^ YVL44_FRAME ^ " /\\ read X22 s = word 0 /\\ " ^
  "read X19 s = word i /\\ read X21 s = word_add w (word(1024 * i)) /\\ " ^
  MLD_LAZY_INV_SCRATCH YVL44_YHAT "0" ^ " /\\ " ^
  MLD_LAZY_INV_DONE YVL44_YHAT "0");;

let YVL44_INNER = parse_term
 ("\\i s. " ^ YVL44_FRAME ^ " /\\ read X22 s = word(l + 1) /\\ " ^
  "read X19 s = word i /\\ read X21 s = word_add w (word(1024 * i)) /\\ " ^
  MLD_LAZY_INV_SCRATCH YVL44_YHAT "(l + 1)" ^ " /\\ " ^
  MLD_LAZY_INV_DONE YVL44_YHAT "(l + 1)" ^ " /\\ " ^
  MLD_LAZY_INV_REST YVL44_YHAT "1024" "l");;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, the template, the saved registers, the    *)
(* canary, the buffer, and the termination of the samplings of the entries.  *)
(* ------------------------------------------------------------------------- *)

let YVL44_SETUP_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th)
     "H_G1") THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th)
     "H_UNIF") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_NTT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_ADD_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_VRED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_VINV" THEN
  CONCRETIZE_F_EVENTS_TAC YVL44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst YVL44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1568):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--26) THEN
  MLD_LAZY_BUFFER_SETUP_TAC 4096 THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[mld_matrix_terminates] o check
    (can (term_match [] `mld_matrix_terminates k l r`) o concl));;

(* ------------------------------------------------------------------------- *)
(* The prologue: rho is loaded as two 128-bit halves and stored to the       *)
(* buffer, whose address the AND gives at step 6, and the canary is stored   *)
(* in the frame.                                                             *)
(* ------------------------------------------------------------------------- *)

let YVL44_PROLOGUE_TAC =
  FULL_INIT_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match []
      `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o
    concl)) THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add mat (word 1024)) (word 16):int64 =
                          word_add mat (word 1040)`] THEN
  STRIP_TAC THEN MLD_LAZY_RBOUND_TAC "s0" THEN
  ARM_STEPS_TAC YVL44_EXEC (1--6) THEN MLD_LAZY_BUFFER_REG_TAC `X20` THEN
  ARM_STEPS_TAC YVL44_EXEC (7--13) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC YVL44_EXEC (14--20) THEN
  MP_TAC(SPECL [`buf:int64`; `r:num`; `s20:armstate`]
               (CONV_RULE NUM_REDUCE_CONV MLD_BYTES_32_OF_HALVES)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MLD_LAZY_UNBUF_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The first column: the sampling of polynomial 0 of y into scratch, from    *)
(* rho'' and the nonce kappa, and its NTT; the rows i (entry (i,0) is        *)
(* sampled into row i of w and multiplied by scratch); and the end of the    *)
(* column.                                                                   *)
(* ------------------------------------------------------------------------- *)

let YVL44_COL0_INIT_TAC =
  REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC YVL44_EXEC (1--7) THEN
  YVL44_CALL_TAC [] "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 8 THEN
  MLD_LAZY_YVEC_Y_TAC YVL44_G 0 THEN
  ARM_STEPS_TAC YVL44_EXEC (9--10) THEN
  YVL44_CALL_TAC [] "H_NTT"
   [`read X0 s`; MLD_LAZY_YVEC_Y YVL44_G 0; `pc:num`; `read X30 s`] 11 THEN
  MLD_LAZY_YVEC_YHAT_TAC YVL44_G 0 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN
  MLD_LAZY_UNBUF_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let YVL44_COL0_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `i < 256 /\ i < 4294967296 /\ i < 18446744073709551616 /\
                i + 1 < 2 EXP 32`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC YVL44_EXEC (1--5) THEN
  MLD_LAZY_YVEC_SEED_TAC `0` "s5" THEN
  MLD_LAZY_TERM_TAC
   `mld_rej_uniform_terminates
     (mld_shake128_stream 34 (mld_matrix_seed r i 0))` THEN
  ARM_STEPS_TAC YVL44_EXEC [6] THEN
  YVL44_CALL_TAC [`i:num`] "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]) THEN
  ARM_STEPS_TAC YVL44_EXEC (8--10) THEN
  YVL44_CALL_TAC [`i:num`] "H_PW"
   [`read X0 s`; `read X1 s`; `mld_matrix_entry r i 0`;
    mk_comb(mk_comb(`mld_poly_of`,YVL44_YH),`0`);
    `pc:num`; `read X30 s`] 11 THEN
  ARM_STEPS_TAC YVL44_EXEC (12--16) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP WORD_ZX_ADD_SMALL (ASSUME `i + 1 < 2 EXP 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MLD_LAZY_JOIN_TAC [mld_lazy_acc] THEN NO_TAC) THEN
  REWRITE_TAC[NOT_LT] THEN
  MLD_LAZY_UNBUF_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let YVL44_COL0_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ARM_STEPS_TAC YVL44_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  MLD_LAZY_UNBUF_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The other columns l + 1: the sampling of polynomial l + 1 of y, with the  *)
(* nonce kappa + l + 1, and its NTT; the rows i (entry (i,l + 1) is sampled  *)
(* into cur, multiplied by scratch and added to row i of w); and the end of  *)
(* the column with the test of the outer loop. The events so far are         *)
(* generalized at the start of each part (MLD_LAZY_GEN_OLD_TAC).             *)
(* ------------------------------------------------------------------------- *)

let YVL44_COL_INIT_TAC =
  let vars = [`l:num`; `old:(uarch_event)list`] in
  REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC YVL44_EXEC (1--7) THEN
  YVL44_CALL_TAC vars "H_G1"
   [`read X0 s`; `read X1 s`; `RP:num`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 8 THEN
  MLD_LAZY_YVEC_YJ_TAC YVL44_G `l + 1` THEN
  ARM_STEPS_TAC YVL44_EXEC (9--10) THEN
  YVL44_CALL_TAC vars "H_NTT"
   [`read X0 s`;
    `mld_poly_of (mld_sign_y mld_poly_uniform_gamma1_17 RP (val(kappa:int16)))
                 (l + 1)`;
    `pc:num`; `read X30 s`] 11 THEN
  MLD_LAZY_YVEC_YHATJ_TAC YVL44_G `l + 1` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN
  MLD_LAZY_UNBUF_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

let YVL44_COL_BODY_TAC =
  let vars = [`i:num`; `l:num`; `old2:(uarch_event)list`] in
  let yacc = mk_abs(`q:num`,list_mk_comb(`mld_lazy_acc`,
                [`r:num`; `q:num`; YVL44_YH; `l:num`])) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MLD_LAZY_GEN_OLD_TAC "old2" THEN FULL_INIT_TAC THEN
  SUBGOAL_THEN `i < 256 /\ i < 4294967296 /\ i < 18446744073709551616 /\
                i + 1 < 2 EXP 32 /\ l + 1 < 256 /\ l + 1 < 4294967296 /\
                l + 1 < 18446744073709551616 /\ l + 1 < 2 EXP 32`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC YVL44_EXEC (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP MLD_LAZY_VAL_ZX
                               (ASSUME `l + 1 < 2 EXP 32`);
                              ADD_EQ_0; ARITH_EQ]) THEN
  ARM_STEPS_TAC YVL44_EXEC (3--5) THEN
  MLD_LAZY_YVEC_SEED_TAC `l + 1` "s5" THEN
  MLD_LAZY_TERM_TAC
   `mld_rej_uniform_terminates
     (mld_shake128_stream 34 (mld_matrix_seed r i (l + 1)))` THEN
  ARM_STEPS_TAC YVL44_EXEC [6] THEN
  YVL44_CALL_TAC vars "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i (l + 1)`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]) THEN
  ARM_STEPS_TAC YVL44_EXEC (8--10) THEN
  YVL44_CALL_TAC vars "H_PW"
   [`read X0 s`; `read X1 s`; `mld_matrix_entry r i (l + 1)`;
    mk_comb(mk_comb(`mld_poly_of`,YVL44_YH),`l + 1`);
    `pc:num`; `read X30 s`] 11 THEN
  ARM_STEPS_TAC YVL44_EXEC (12--13) THEN
  MLD_LAZY_ROW_TAC yacc
   (subst [YVL44_YH,`yh:num->int32`]
     `!c. c < 256
          ==> read (memory :> bytes32 (word_add w (word(1024 * i + 4 * c))))
                s13 =
              mld_lazy_acc r i yh l c`) THEN
  VEC_REST_TAC (subst [yacc,`f:num->num->int32`]
   `!j. 256 * (i + 1) <= j /\ j < 1024
        ==> read(memory :> bytes32(word_add w (word(4 * j)))) s13 =
            mld_polyvec f j`) THEN
  ARM_STEPS_TAC YVL44_EXEC [14] THEN
  YVL44_CALL_TAC vars "H_ADD"
   [`read X0 s`; `read X1 s`;
    list_mk_comb(`mld_lazy_acc`,[`r:num`; `i:num`; YVL44_YH; `l:num`]);
    list_mk_comb(`mld_poly_pointwise_montgomery`,
      [`mld_matrix_entry r i (l + 1)`;
       mk_comb(mk_comb(`mld_poly_of`,YVL44_YH),`l + 1`)]);
    `pc:num`; `read X30 s`] 15 THEN
  ARM_STEPS_TAC YVL44_EXEC (16--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP WORD_ZX_ADD_SMALL (ASSUME `i + 1 < 2 EXP 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MLD_LAZY_JOIN_TAC [MLD_LAZY_ACC_ADD1] THEN NO_TAC) THEN
  REWRITE_TAC[NOT_LT] THEN
  MLD_LAZY_UNBUF_TAC THEN VERIF_EVENTS_TAC [`old2:(uarch_event)list`];;

let YVL44_COL_EXIT_TAC =
  REWRITE_TAC[] THEN MLD_LAZY_GEN_OLD_TAC "old2" THEN FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  SUBGOAL_THEN `(l + 1) + 1 < 2 EXP 32` ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC YVL44_EXEC (1--1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP WORD_ZX_ADD_SMALL (ASSUME `(l + 1) + 1 < 2 EXP 32`)]) THEN
  ARM_STEPS_TAC YVL44_EXEC (2--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN
  SUBGOAL_THEN `((l + 1) + 1 = 4) <=> ~(l + 1 < 3)` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  MLD_LAZY_UNBUF_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The epilogue: the zeroing of the buffer, the reduction of the vector of   *)
(* the sums and its inverse NTT, which is the product                        *)
(* (mld_polyvec_matrix_yvec_lazy), the check of the canary, and the          *)
(* restoring of the registers and the return.                                *)
(* ------------------------------------------------------------------------- *)

let YVL44_EPILOGUE_TAC =
  let wv = MLD_LAZY_YVEC_W YVL44_G 4 in
  REWRITE_TAC[] THEN MLD_LAZY_GEN_OLD_TAC "old" THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC YVL44_EXEC (1--5) THEN
  YVL44_CALL_TAC [`old:(uarch_event)list`] "H_VRED"
   [`read X0 s`; wv; `pc:num`; `read SP s`; `read X30 s`] 6 THEN
  ARM_STEPS_TAC YVL44_EXEC (7--8) THEN
  YVL44_CALL_TAC [`old:(uarch_event)list`] "H_VINV"
   [`read X0 s`; mk_comb(`mld_polyvec_map mld_poly_reduce`,wv);
    `pc:num`; `read SP s`; `read X30 s`] 9 THEN
  ARM_STEPS_TAC YVL44_EXEC [10] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC YVL44_EXEC (11--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MLD_LAZY_YVEC_POST_TAC;
    MLD_LAZY_UNBUF_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`]];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the loop over the  *)
(* columns 1, ..., 3, after the prologue and the first column, each column   *)
(* as the loop over the rows, whose initialization samples the polynomial of *)
(* y for the column.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  YVL44_SETUP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `3`
   `pc + mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_loop1`
   `pc + mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_loop1_exit`
   YVL44_OUTER THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The prologue and the first column ***)

    REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_loop1`
     YVL44_J1_0 THEN
    CONJ_TAC THENL
     [YVL44_PROLOGUE_TAC;
      ENSURES_EVENTS_WHILE_UP2_TAC `4`
       `pc + mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_loop2`
       `pc + mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_loop2_exit`
       YVL44_INNER0 THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC; YVL44_COL0_INIT_TAC; YVL44_COL0_BODY_TAC;
        YVL44_COL0_EXIT_TAC]];

    (*** The other columns ***)

    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    MLD_LAZY_EVENTS_REASSOC_TAC (GSYM APPEND_ASSOC) THEN
    MLD_LAZY_GEN_OLD_TAC "old" THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `4`
     `pc + mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_loop2`
     `pc + mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_loop2_exit`
     YVL44_INNER THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; YVL44_COL_INIT_TAC; YVL44_COL_BODY_TAC;
      YVL44_COL_EXIT_TAC];

    (*** The epilogue ***)

    YVL44_EPILOGUE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
