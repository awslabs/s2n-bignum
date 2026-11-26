(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The product w = invNTT(A * NTT(y)) of signing, with the entries of A and  *)
(* the polynomials of y sampled on demand: the proof (see                    *)
(* polyvec_matrix_pointwise_montgomery_yvec_lazy_44_spec.ml).                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_yvec_lazy_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;
needs "x86/proofs/utils/mldsa_native_lazy_matrix.ml";;

let YV44_EXEC =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_EXEC;;

(*** An address in the code that has no label ***)

let YV44_PC off =
  mk_comb(mk_comb(`(+):num->num->num`,`pc:num`),
          mk_small_numeral
           (layout "mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy" +
            off));;

(* ------------------------------------------------------------------------- *)
(* The events (utils/mldsa_native_lazy_matrix.ml): the prologue, the first   *)
(* column, the loop over the columns 1, 2 and 3, each with the loop over the *)
(* 4 rows, and the epilogue. The code aligns its frame to 32 bytes, so that  *)
(* the addresses in it are at fixed offsets from bot                         *)
(* (utils/mldsa_native_realign.ml), which REALIGN_UNBOT_TAC expands at the   *)
(* end of each part, and the events of the samplings of the entries depend   *)
(* on their seeds, functions of rho and the indices.                         *)
(* ------------------------------------------------------------------------- *)

let YV44_TEMPLATE = LAZY_YVEC_TEMPLATE "4" "4";;

let YV44_ALLOWED =
  [`pc:num`; `w:int64`; `mat:int64`; `y:int64`; `scratch:int64`; `rp:int64`;
   `rho:num`; `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

let YV44_CALL_TAC vars name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc YV44_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   (vars @ YV44_ALLOWED) n;;

(* ------------------------------------------------------------------------- *)
(* The frame of 1670 bytes below the return address: the six registers that  *)
(* the function saves (k = 1622, so that the AND of the stack pointer is of  *)
(* word_add stackpointer (word 1622) after                                   *)
(* REPEAT_GEN_AND_OFFSET_STACKPTR_TAC), and the aligned part (bot,1591),     *)
(* with RSP at bot + 1495 after the SUB, the addresses of y, w and the       *)
(* buffer kept at bot + 1503, bot + 1511 and bot + 1519, the buffer of 64    *)
(* bytes at bot + 1527 (rho, and the bytes j and i of the seed of entry      *)
(* (i,j) at bot + 1559 and bot + 1560), and the stacks of the callees, with  *)
(* their return addresses, below RSP. The column l is counted in R14, with   *)
(* the polynomial of the structure at R12 and scratch at R13, and the row i  *)
(* in R15, with its address in RBX. The invariants: at join1 for column      *)
(* l + 1 (OUTER), w holds the sums for the columns up to l; after the NTT of *)
(* polynomial l + 1 of y into scratch (MID); and at join2 for row i          *)
(* (INNER), the rows before i also have the products for column l + 1; and   *)
(* the same for the first column (J1_0, MID0, INNER0).                       *)
(* ------------------------------------------------------------------------- *)

let YV44_YHAT = LAZY_YVEC_YHAT "mld_poly_uniform_gamma1_17";;

let YV44_REGS c =
  "read R12 s = mat /\\ read R13 s = scratch /\\ read R14 s = word " ^ c;;

let YV44_OUTER = parse_term
 ("\\l s. " ^ LAZY_YVEC_FRAME ^ " /\\ " ^ YV44_REGS "(l + 1)" ^ " /\\ " ^
  LAZY_YVEC_W YV44_YHAT "1024" "l");;

let YV44_J1_0 = parse_term
 ("\\s. " ^ LAZY_YVEC_FRAME ^ " /\\ " ^ YV44_REGS "0");;

let YV44_MID0 = parse_term
 ("\\s. " ^ LAZY_YVEC_FRAME ^ " /\\ " ^ YV44_REGS "0" ^
  " /\\ read R15 s = word 0 /\\ " ^ LAZY_YVEC_SCRATCH YV44_YHAT "0");;

let YV44_INNER0 = parse_term
 ("\\i s. " ^ LAZY_YVEC_FRAME ^ " /\\ " ^ YV44_REGS "0" ^
  " /\\ read R15 s = word i /\\ " ^
  "read RBX s = word_add w (word(1024 * i)) /\\ " ^
  LAZY_YVEC_SCRATCH YV44_YHAT "0" ^ " /\\ " ^ LAZY_YVEC_DONE YV44_YHAT "0");;

let YV44_MID = parse_term
 ("\\s. " ^ LAZY_YVEC_FRAME ^ " /\\ " ^ YV44_REGS "(l + 1)" ^
  " /\\ read R15 s = word 0 /\\ " ^ LAZY_YVEC_SCRATCH YV44_YHAT "(l + 1)" ^
  " /\\ " ^ LAZY_YVEC_W YV44_YHAT "1024" "l");;

let YV44_INNER = parse_term
 ("\\i s. " ^ LAZY_YVEC_FRAME ^ " /\\ " ^ YV44_REGS "(l + 1)" ^
  " /\\ read R15 s = word i /\\ " ^
  "read RBX s = word_add w (word(1024 * i)) /\\ " ^
  LAZY_YVEC_SCRATCH YV44_YHAT "(l + 1)" ^ " /\\ " ^
  LAZY_YVEC_DONE YV44_YHAT "(l + 1)" ^ " /\\ " ^
  LAZY_YVEC_REST YV44_YHAT "1024" "l");;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, the template, the realigned frame, with   *)
(* the alignment of RSP for the aligned stores to the buffer, the saved      *)
(* registers, and the termination of the samplings of the entries.           *)
(* ------------------------------------------------------------------------- *)

let YV44_SETUP_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_G1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_UNI" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_PWM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_ADD_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_VRED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_VINV" THEN
  CONCRETIZE_F_EVENTS_TAC YV44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst YV44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 1622 THEN REALIGN_FRAME_TAC 1670 1622 THEN
  REALIGN_NONOV_TAC 1591
   [`w:int64,4096`; `mat:int64,1024`; `scratch:int64,1024`;
    `word_add mat (word 1024):int64,32`; `y:int64,16`; `rp:int64,64`;
    `word pc:int64,libmldsa_size`;
    `word_add stackpointer (word 1622):int64,48`;
    `word_add stackpointer (word 1670):int64,8`] THEN
  REALIGN_ALIGNED_TAC [1495] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[mld_matrix_terminates] o check
   (can (term_match [] `mld_matrix_terminates 4 4 rho`) o concl));;

(* ------------------------------------------------------------------------- *)
(* The prologue: rho is loaded as two 128-bit words into the YMM registers   *)
(* named at the start, so that the facts for their new low halves are kept,  *)
(* and stored to the buffer, and RSP gets the value of the AND after step    *)
(* 11.                                                                       *)
(* ------------------------------------------------------------------------- *)

let YV44_PROLOGUE_TAC =
  FULL_INIT_TAC THEN LAZY_RHO_PREP_TAC THEN
  X86_STEPS_TAC YV44_EXEC (1--11) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC YV44_EXEC (12--20) THEN
  LAZY_RHO_STORED_TAC `word_add bot (word 1527):int64` `s20:x86state` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The sampling of polynomial c of y into scratch, from rhoprime and the     *)
(* nonce kappa + c, and its NTT, as polynomial c of YHAT.                    *)
(* ------------------------------------------------------------------------- *)

let YV44_POLY_Y_TAC vars c =
  let g1c = subst [c,`c:num`]
   `mld_poly_of (mld_polyvec
     (\j. mld_poly_uniform_gamma1_17 rhoprime (word(kappa + j)))) c` in
  FULL_INIT_TAC THEN
  X86_STEPS_TAC YV44_EXEC (1--8) THEN
  YV44_CALL_TAC vars "H_G1"
   [`read RDI s`; `read RSI s`; `rhoprime:num`; `read RDX s`] 9 THEN
  LAZY_NONCE_TAC c THEN
  X86_STEPS_TAC YV44_EXEC (10--11) THEN
  SUBGOAL_THEN
   (subst [g1c,`x:num->int32`]
     `!i. i < 256
          ==> read(memory :> bytes32(word_add scratch (word(4 * i)))) s11 =
              (x:num->int32) i`)
   ASSUME_TAC THENL
   [SIMP_TAC[MLD_POLY_OF_POLYVEC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  YV44_CALL_TAC vars "H_NTT" [`read RDI s`; g1c] 12 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP] THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The first column: the setting of the row pointer, the rows i (with the    *)
(* branch to join4: entry (i,0) is sampled into row i of w and multiplied by *)
(* scratch), and the end of the column.                                      *)
(* ------------------------------------------------------------------------- *)

let YV44_COL0_INIT_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC YV44_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let YV44_COL0_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `i < 256 /\ i + 1 < 2 EXP 32` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC YV44_EXEC (1--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP LAZY_BYTE_64 (ASSUME `i < 256`)]) THEN
  MP_TAC(SPECL [`word_add bot (word 1527):int64`; `rho:num`; `i:num`; `0`;
                `s6:x86state`] LAZY_SEED) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC] THEN
  MLD_LAZY_TERM_TAC
   `mld_rej_uniform_terminates
     (mld_shake128_stream 34 (mld_matrix_seed rho i 0))` THEN
  X86_STEPS_TAC YV44_EXEC (7--7) THEN
  YV44_CALL_TAC [`i:num`] "H_UNI"
   [`read RDI s`; `read RSI s`; `mld_matrix_seed rho i 0`] 8 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]) THEN
  X86_STEPS_TAC YV44_EXEC (9--11) THEN
  YV44_CALL_TAC [`i:num`] "H_PWM"
   [`read RDI s`; `read RSI s`; `mld_matrix_entry rho i 0`;
    mk_comb(mk_comb(`mld_poly_of`,parse_term YV44_YHAT),`0`)] 12 THEN
  X86_STEPS_TAC YV44_EXEC (13--17) THEN
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
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let YV44_COL0_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  X86_STEPS_TAC YV44_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The other columns l + 1: the setting of the row pointer, the rows i       *)
(* (entry (i,l + 1) is sampled into the polynomial of the structure,         *)
(* multiplied by scratch and added to row i of w), and the end of the column *)
(* with the test of the outer loop. The events so far are generalized at the *)
(* start of each part (MLD_LAZY_GEN_OLD_TAC).                                *)
(* ------------------------------------------------------------------------- *)

let YV44_COL_INIT_TAC =
  MLD_LAZY_GEN_OLD_TAC "old2" THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC YV44_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let YV44_COL_BODY_TAC =
  let vars = [`i:num`; `l:num`; `old2:(uarch_event)list`] in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MLD_LAZY_GEN_OLD_TAC "old2" THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `i < 256 /\ i + 1 < 2 EXP 32 /\ l + 1 < 256 /\ l + 1 < 2 EXP 32`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC YV44_EXEC (1--1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP MLD_LAZY_VAL_ZX
                               (ASSUME `l + 1 < 2 EXP 32`);
                              ADD_EQ_0; ARITH_EQ]) THEN
  X86_STEPS_TAC YV44_EXEC (2--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP LAZY_BYTE_64 (ASSUME `l + 1 < 256`);
    MATCH_MP LAZY_BYTE_64 (ASSUME `i < 256`)]) THEN
  MP_TAC(SPECL [`word_add bot (word 1527):int64`; `rho:num`; `i:num`;
                `l + 1`; `s6:x86state`] LAZY_SEED) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MLD_LAZY_TERM_TAC
   `mld_rej_uniform_terminates
     (mld_shake128_stream 34 (mld_matrix_seed rho i (l + 1)))` THEN
  X86_STEPS_TAC YV44_EXEC (7--7) THEN
  YV44_CALL_TAC vars "H_UNI"
   [`read RDI s`; `read RSI s`; `mld_matrix_seed rho i (l + 1)`] 8 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]) THEN
  X86_STEPS_TAC YV44_EXEC (9--11) THEN
  YV44_CALL_TAC vars "H_PWM"
   [`read RDI s`; `read RSI s`; `mld_matrix_entry rho i (l + 1)`;
    mk_comb(mk_comb(`mld_poly_of`,parse_term YV44_YHAT),`l + 1`)] 12 THEN
  X86_STEPS_TAC YV44_EXEC (13--14) THEN
  MLD_LAZY_ROW_TAC
   (parse_term("\\r. mld_lazy_acc rho r " ^ YV44_YHAT ^ " l"))
   (parse_term
     ("!c. c < 256 ==> read (memory :> bytes32 (word_add w " ^
      "(word(1024 * i + 4 * c)))) s14 = mld_lazy_acc rho i " ^ YV44_YHAT ^
      " l c")) THEN
  VEC_REST_TAC (parse_term
   ("!j. 256 * (i + 1) <= j /\\ j < 1024
         ==> read(memory :> bytes32(word_add w (word(4 * j)))) s14 =
             mld_polyvec (\\r. mld_lazy_acc rho r " ^ YV44_YHAT ^
             " l) j")) THEN
  ASSUME_TAC(MP (SPECL [`w:int64`; `i:num`] LAZY_ALIGNED_ROW)
                (ASSUME `aligned 16 (w:int64)`)) THEN
  X86_STEPS_TAC YV44_EXEC (15--15) THEN
  YV44_CALL_TAC vars "H_ADD"
   [`read RDI s`; `read RSI s`;
    parse_term("mld_lazy_acc rho i " ^ YV44_YHAT ^ " l");
    parse_term("mld_poly_pointwise_montgomery (mld_matrix_entry rho i " ^
               "(l + 1)) (mld_poly_of " ^ YV44_YHAT ^ " (l + 1))")] 16 THEN
  X86_STEPS_TAC YV44_EXEC (17--17) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP WORD_ZX_ADD_SMALL (ASSUME `i + 1 < 2 EXP 32`)]) THEN
  X86_STEPS_TAC YV44_EXEC (18--20) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(MLD_LAZY_JOIN_TAC [MLD_LAZY_ACC_ADD1] THEN NO_TAC) THEN
  REWRITE_TAC[NOT_LT] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_TAC [`old2:(uarch_event)list`];;

let YV44_COL_EXIT_TAC =
  REWRITE_TAC[] THEN MLD_LAZY_GEN_OLD_TAC "old2" THEN FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  SUBGOAL_THEN `(l + 1) + 1 < 2 EXP 32` ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC YV44_EXEC (1--1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP WORD_ZX_ADD_SMALL (ASSUME `(l + 1) + 1 < 2 EXP 32`)]) THEN
  X86_STEPS_TAC YV44_EXEC (2--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN
  SUBGOAL_THEN `((l + 1) + 1 = 4) <=> ~(l + 1 < 3)` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

(* ------------------------------------------------------------------------- *)
(* The epilogue: the zeroing of the buffer, the reduction of the vector of   *)
(* the sums and its inverse NTT, which is the product                        *)
(* (mld_polyvec_matrix_yvec_lazy, for y = mld_sign_y), and the restoring of  *)
(* the registers and the return.                                             *)
(* ------------------------------------------------------------------------- *)

let YV44_EPILOGUE_TAC =
  REWRITE_TAC[] THEN MLD_LAZY_GEN_OLD_TAC "old" THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC YV44_EXEC (1--9) THEN
  YV44_CALL_TAC [`old:(uarch_event)list`] "H_VRED"
   [`read RDI s`;
    parse_term("mld_polyvec (\\r. mld_lazy_acc rho r " ^ YV44_YHAT ^ " 3)")]
   10 THEN
  X86_STEPS_TAC YV44_EXEC (11--12) THEN
  YV44_CALL_TAC [`old:(uarch_event)list`] "H_VINV"
   [`read RDI s`;
    parse_term("mld_polyvec_map mld_poly_reduce (mld_polyvec (\\r. " ^
               "mld_lazy_acc rho r " ^ YV44_YHAT ^ " 3))")] 13 THEN
  X86_STEPS_TAC YV44_EXEC (14--21) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[mld_polyvec_matrix_yvec_lazy; mld_sign_y] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the loop over the  *)
(* columns 1, 2 and 3, after the prologue and the first column, each column  *)
(* as the sampling of its polynomial of y and the loop over the rows.        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  YV44_SETUP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `3`
   `pc + mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_join1`
   (YV44_PC 0xc7) YV44_OUTER THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The prologue and the first column ***)

    REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_join1`
     YV44_J1_0 THEN
    CONJ_TAC THENL
     [YV44_PROLOGUE_TAC;
      MLD_LAZY_EVENTS_REASSOC_TAC (GSYM APPEND_ASSOC) THEN
      ENSURES_EVENTS_SEQUENCE_TAC
       `pc +
        mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_after_mldsa_poly_ntt`
       YV44_MID0 THEN
      CONJ_TAC THENL
       [YV44_POLY_Y_TAC [] `0`;
        ENSURES_EVENTS_WHILE_UP2_TAC `4`
         `pc + mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_join2`
         (YV44_PC 0xbd) YV44_INNER0 THEN
        REPEAT CONJ_TAC THENL
         [ARITH_TAC; YV44_COL0_INIT_TAC; YV44_COL0_BODY_TAC;
          YV44_COL0_EXIT_TAC]]];

    (*** The other columns ***)

    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    MLD_LAZY_EVENTS_REASSOC_TAC LAZY_APPEND_REASSOC3 THEN
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc +
      mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_after_mldsa_poly_ntt`
     YV44_MID THEN
    CONJ_TAC THENL
     [MLD_LAZY_GEN_OLD_TAC "old" THEN
      YV44_POLY_Y_TAC [`l:num`; `old:(uarch_event)list`] `l + 1`;
      MLD_LAZY_GEN_OLD_TAC "old" THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `4`
       `pc + mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy_join2`
       (YV44_PC 0xbd) YV44_INNER THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC; YV44_COL_INIT_TAC; YV44_COL_BODY_TAC; YV44_COL_EXIT_TAC]];

    (*** The epilogue ***)

    YV44_EPILOGUE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
