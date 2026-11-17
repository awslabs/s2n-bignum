(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The product w = invNTT(A * NTT(y)) of signing, with the entries of A and  *)
(* the polynomials of y sampled on demand: the proof (see                    *)
(* polyvec_matrix_pointwise_montgomery_yvec_lazy_87_spec.ml).                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_yvec_lazy_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;
needs "x86/proofs/utils/mldsa_native_lazy_rr.ml";;

let YV87_EXEC =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_EXEC;;

(*** An address in the code that has no label ***)

let YV87_PC off =
  mk_comb(mk_comb(`(+):num->num->num`,`pc:num`),
          mk_small_numeral
           (layout "mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy" +
            off));;

(* ------------------------------------------------------------------------- *)
(* The events (utils/mldsa_native_lazy_rr.ml): the prologue, the first       *)
(* column, the loop over the columns 1, ..., 6, each with the loop over the  *)
(* 8 rows, and the epilogue. The code aligns its frame to 32 bytes, so that  *)
(* the addresses in it are at fixed offsets from bot                         *)
(* (utils/mldsa_native_realign.ml), which REALIGN_UNBOT_TAC expands at the   *)
(* end of each part, and the events of the samplings of the entries depend   *)
(* on their seeds, functions of rho and the indices.                         *)
(* ------------------------------------------------------------------------- *)

let YV87_TEMPLATE = LAZY_YVEC_TEMPLATE "7" "8";;

let YV87_ALLOWED =
  [`pc:num`; `w:int64`; `mat:int64`; `y:int64`; `scratch:int64`; `rp:int64`;
   `rho:num`; `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

let YV87_CALL_TAC vars name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc YV87_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   (vars @ YV87_ALLOWED) n;;

(* ------------------------------------------------------------------------- *)
(* The frame of 1670 bytes below the return address: the six registers that  *)
(* the function saves (k = 1622, so that the AND of the stack pointer is of  *)
(* word_add stackpointer (word 1622) after                                   *)
(* REPEAT_GEN_AND_OFFSET_STACKPTR_TAC), and the aligned part (bot,1591),     *)
(* with RSP at bot + 1495 after the SUB, the addresses of y, w and the       *)
(* buffer kept at bot + 1503, bot + 1511 and bot + 1519, the buffer of 64    *)
(* bytes at bot + 1527 (rho, and the bytes j and i of the seed of entry      *)
(* (i,j) at bot + 1559 and bot + 1560), and the stacks of the callees, with  *)
(* their return addresses, below RSP. The column l is counted in R12, with   *)
(* the polynomial of the structure at R13 and scratch at R14, and the row i  *)
(* in R15, with its address in RBX. The invariants: at join1 for column      *)
(* l + 1 (OUTER), w holds the sums for the columns up to l; after the NTT of *)
(* polynomial l + 1 of y into scratch (MID); and at join4 for row i          *)
(* (INNER), the rows before i also have the products for column l + 1; and   *)
(* the same for the first column (J1_0, MID0, INNER0).                       *)
(* ------------------------------------------------------------------------- *)

let YV87_YHAT = LAZY_YVEC_YHAT "mld_poly_uniform_gamma1_19";;

let YV87_REGS c =
  "read R13 s = mat /\\ read R14 s = scratch /\\ read R12 s = word " ^ c;;

let YV87_OUTER = parse_term
 ("\\l s. " ^ LAZY_YVEC_FRAME ^ " /\\ " ^ YV87_REGS "(l + 1)" ^ " /\\ " ^
  LAZY_YVEC_W YV87_YHAT "2048" "l");;

let YV87_J1_0 = parse_term
 ("\\s. " ^ LAZY_YVEC_FRAME ^ " /\\ " ^ YV87_REGS "0");;

let YV87_MID0 = parse_term
 ("\\s. " ^ LAZY_YVEC_FRAME ^ " /\\ " ^ YV87_REGS "0" ^
  " /\\ read R15 s = word 0 /\\ " ^ LAZY_YVEC_SCRATCH YV87_YHAT "0");;

let YV87_INNER0 = parse_term
 ("\\i s. " ^ LAZY_YVEC_FRAME ^ " /\\ " ^ YV87_REGS "0" ^
  " /\\ read R15 s = word i /\\ " ^
  "read RBX s = word_add w (word(1024 * i)) /\\ " ^
  LAZY_YVEC_SCRATCH YV87_YHAT "0" ^ " /\\ " ^ LAZY_YVEC_DONE YV87_YHAT "0");;

let YV87_MID = parse_term
 ("\\s. " ^ LAZY_YVEC_FRAME ^ " /\\ " ^ YV87_REGS "(l + 1)" ^
  " /\\ read R15 s = word 0 /\\ " ^ LAZY_YVEC_SCRATCH YV87_YHAT "(l + 1)" ^
  " /\\ " ^ LAZY_YVEC_W YV87_YHAT "2048" "l");;

let YV87_INNER = parse_term
 ("\\i s. " ^ LAZY_YVEC_FRAME ^ " /\\ " ^ YV87_REGS "(l + 1)" ^
  " /\\ read R15 s = word i /\\ " ^
  "read RBX s = word_add w (word(1024 * i)) /\\ " ^
  LAZY_YVEC_SCRATCH YV87_YHAT "(l + 1)" ^ " /\\ " ^
  LAZY_YVEC_DONE YV87_YHAT "(l + 1)" ^ " /\\ " ^
  LAZY_YVEC_REST YV87_YHAT "2048" "l");;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, the template, the realigned frame, with   *)
(* the alignment of RSP for the aligned stores to the buffer, the saved      *)
(* registers, and the termination of the samplings of the entries.           *)
(* ------------------------------------------------------------------------- *)

let YV87_SETUP_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
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
    MLDSA_NATIVE_POLYVECK_REDUCE_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_VRED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_VINV" THEN
  CONCRETIZE_F_EVENTS_TAC YV87_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst YV87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 1622 THEN REALIGN_FRAME_TAC 1670 1622 THEN
  REALIGN_NONOV_TAC 1591
   [`w:int64,8192`; `mat:int64,1024`; `scratch:int64,1024`;
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
   (can (term_match [] `mld_matrix_terminates 8 7 rho`) o concl));;

(* ------------------------------------------------------------------------- *)
(* The prologue: rho is loaded as two 128-bit words into the YMM registers   *)
(* named at the start, so that the facts for their new low halves are kept,  *)
(* and stored to the buffer, and RSP gets the value of the AND after step    *)
(* 11; a NOP aligns join1.                                                   *)
(* ------------------------------------------------------------------------- *)

let YV87_PROLOGUE_TAC =
  FULL_INIT_TAC THEN LAZY_RHO_PREP_TAC THEN
  X86_STEPS_TAC YV87_EXEC (1--11) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC YV87_EXEC (12--21) THEN
  LAZY_RHO_STORED_TAC `word_add bot (word 1527):int64` `s21:x86state` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The sampling of polynomial c of y into scratch, from rhoprime and the     *)
(* nonce kappa + c, and its NTT, as polynomial c of YHAT.                    *)
(* ------------------------------------------------------------------------- *)

let YV87_POLY_Y_TAC vars c =
  let g1c = subst [c,`c:num`]
   `mld_poly_of (mld_polyvec
     (\j. mld_poly_uniform_gamma1_19 rhoprime (word(kappa + j)))) c` in
  FULL_INIT_TAC THEN
  X86_STEPS_TAC YV87_EXEC (1--8) THEN
  YV87_CALL_TAC vars "H_G1"
   [`read RDI s`; `read RSI s`; `rhoprime:num`; `read RDX s`] 9 THEN
  LAZY_NONCE_TAC c THEN
  X86_STEPS_TAC YV87_EXEC (10--11) THEN
  SUBGOAL_THEN
   (subst [g1c,`x:num->int32`]
     `!i. i < 256
          ==> read(memory :> bytes32(word_add scratch (word(4 * i)))) s11 =
              (x:num->int32) i`)
   ASSUME_TAC THENL
   [SIMP_TAC[MLD_POLY_OF_POLYVEC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  YV87_CALL_TAC vars "H_NTT" [`read RDI s`; g1c] 12 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP] THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The first column: the setting of the row pointer and the jump to join4,   *)
(* the rows i (without the branch to join2: entry (i,0) is sampled into row  *)
(* i of w and multiplied by scratch), and the end of the column.             *)
(* ------------------------------------------------------------------------- *)

let YV87_COL0_INIT_TAC =
  FULL_INIT_TAC THEN X86_STEPS_TAC YV87_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let YV87_COL0_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `i < 256 /\ i + 1 < 2 EXP 32` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC YV87_EXEC (1--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP LAZY_BYTE_64 (ASSUME `i < 256`)]) THEN
  MP_TAC(SPECL [`word_add bot (word 1527):int64`; `rho:num`; `i:num`; `0`;
                `s6:x86state`] LAZY_SEED) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC] THEN
  LAZY_TERM_TAC
   `mld_rej_uniform_terminates
     (mld_shake128_stream 34 (mld_matrix_seed rho i 0))` THEN
  X86_STEPS_TAC YV87_EXEC (7--7) THEN
  YV87_CALL_TAC [`i:num`] "H_UNI"
   [`read RDI s`; `read RSI s`; `mld_matrix_seed rho i 0`] 8 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]) THEN
  X86_STEPS_TAC YV87_EXEC (9--11) THEN
  YV87_CALL_TAC [`i:num`] "H_PWM"
   [`read RDI s`; `read RSI s`; `mld_matrix_entry rho i 0`;
    mk_comb(mk_comb(`mld_poly_of`,parse_term YV87_YHAT),`0`)] 12 THEN
  X86_STEPS_TAC YV87_EXEC (13--17) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP WORD_ZX_ADD_SMALL (ASSUME `i + 1 < 2 EXP 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(LAZY_JOIN_TAC [mld_lazy_acc] THEN NO_TAC) THEN
  REWRITE_TAC[NOT_LT] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let YV87_COL0_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  X86_STEPS_TAC YV87_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The other columns l + 1: the setting of the row pointer and the jump to   *)
(* join4, the rows i (with the branch to join2: entry (i,l + 1) is sampled   *)
(* into the polynomial of the structure, multiplied by scratch and added to  *)
(* row i of w), and the end of the column with the test of the outer loop.   *)
(* The events so far are generalized at the start of each part               *)
(* (LAZY_GEN_OLD_TAC).                                                       *)
(* ------------------------------------------------------------------------- *)

let YV87_COL_INIT_TAC =
  LAZY_GEN_OLD_TAC "old2" THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC YV87_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let YV87_COL_BODY_TAC =
  let vars = [`i:num`; `l:num`; `old2:(uarch_event)list`] in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  LAZY_GEN_OLD_TAC "old2" THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `i < 256 /\ i + 1 < 2 EXP 32 /\ l + 1 < 256 /\ l + 1 < 2 EXP 32`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC YV87_EXEC (1--1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP LAZY_VAL_ZX (ASSUME `l + 1 < 2 EXP 32`);
                              ADD_EQ_0; ARITH_EQ]) THEN
  X86_STEPS_TAC YV87_EXEC (2--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP LAZY_BYTE_64 (ASSUME `l + 1 < 256`);
    MATCH_MP LAZY_BYTE_64 (ASSUME `i < 256`)]) THEN
  MP_TAC(SPECL [`word_add bot (word 1527):int64`; `rho:num`; `i:num`;
                `l + 1`; `s6:x86state`] LAZY_SEED) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  LAZY_TERM_TAC
   `mld_rej_uniform_terminates
     (mld_shake128_stream 34 (mld_matrix_seed rho i (l + 1)))` THEN
  X86_STEPS_TAC YV87_EXEC (7--7) THEN
  YV87_CALL_TAC vars "H_UNI"
   [`read RDI s`; `read RSI s`; `mld_matrix_seed rho i (l + 1)`] 8 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]) THEN
  X86_STEPS_TAC YV87_EXEC (9--11) THEN
  YV87_CALL_TAC vars "H_PWM"
   [`read RDI s`; `read RSI s`; `mld_matrix_entry rho i (l + 1)`;
    mk_comb(mk_comb(`mld_poly_of`,parse_term YV87_YHAT),`l + 1`)] 12 THEN
  X86_STEPS_TAC YV87_EXEC (13--14) THEN
  LAZY_ROW_TAC
   (parse_term("\\r. mld_lazy_acc rho " ^ YV87_YHAT ^ " r l"))
   (parse_term
     ("!c. c < 256 ==> read (memory :> bytes32 (word_add w " ^
      "(word(1024 * i + 4 * c)))) s14 = mld_lazy_acc rho " ^ YV87_YHAT ^
      " i l c")) THEN
  VEC_REST_TAC (parse_term
   ("!j. 256 * (i + 1) <= j /\\ j < 2048
         ==> read(memory :> bytes32(word_add w (word(4 * j)))) s14 =
             mld_polyvec (\\r. mld_lazy_acc rho " ^ YV87_YHAT ^
             " r l) j")) THEN
  ASSUME_TAC(MP (SPECL [`w:int64`; `i:num`] LAZY_ALIGNED_ROW)
                (ASSUME `aligned 16 (w:int64)`)) THEN
  X86_STEPS_TAC YV87_EXEC (15--15) THEN
  YV87_CALL_TAC vars "H_ADD"
   [`read RDI s`; `read RSI s`;
    parse_term("mld_lazy_acc rho " ^ YV87_YHAT ^ " i l");
    parse_term("mld_poly_pointwise_montgomery (mld_matrix_entry rho i " ^
               "(l + 1)) (mld_poly_of " ^ YV87_YHAT ^ " (l + 1))")] 16 THEN
  X86_STEPS_TAC YV87_EXEC (17--17) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP WORD_ZX_ADD_SMALL (ASSUME `i + 1 < 2 EXP 32`)]) THEN
  X86_STEPS_TAC YV87_EXEC (18--20) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(LAZY_JOIN_TAC [MLD_LAZY_ACC_ADD1] THEN NO_TAC) THEN
  REWRITE_TAC[NOT_LT] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_TAC [`old2:(uarch_event)list`];;

let YV87_COL_EXIT_TAC =
  REWRITE_TAC[] THEN LAZY_GEN_OLD_TAC "old2" THEN FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  SUBGOAL_THEN `(l + 1) + 1 < 2 EXP 32` ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC YV87_EXEC (1--1) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP WORD_ZX_ADD_SMALL (ASSUME `(l + 1) + 1 < 2 EXP 32`)]) THEN
  X86_STEPS_TAC YV87_EXEC (2--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN
  SUBGOAL_THEN `((l + 1) + 1 = 7) <=> ~(l + 1 < 6)` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

(* ------------------------------------------------------------------------- *)
(* The epilogue: the zeroing of the buffer, the reduction of the vector of   *)
(* the sums, which is the product (LAZY_POLYVEC_REDUCE), its inverse NTT,    *)
(* and the restoring of the registers and the return.                        *)
(* ------------------------------------------------------------------------- *)

let YV87_EPILOGUE_TAC =
  let red = CONV_RULE NUM_REDUCE_CONV (SPEC `7` LAZY_POLYVEC_REDUCE) in
  REWRITE_TAC[] THEN LAZY_GEN_OLD_TAC "old" THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC YV87_EXEC (1--9) THEN
  YV87_CALL_TAC [`old:(uarch_event)list`] "H_VRED"
   [`read RDI s`;
    parse_term("mld_polyvec (\\r. mld_lazy_acc rho " ^ YV87_YHAT ^ " r 6)")]
   10 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[red]) THEN
  X86_STEPS_TAC YV87_EXEC (11--12) THEN
  YV87_CALL_TAC [`old:(uarch_event)list`] "H_VINV"
   [`read RDI s`;
    parse_term("mld_polyvec_matrix_pointwise_montgomery_lazy 7 rho " ^
               YV87_YHAT)] 13 THEN
  X86_STEPS_TAC YV87_EXEC (14--21) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[mld_yvec_lazy_w] THEN
  REALIGN_UNBOT_TAC THEN VERIF_EVENTS_TAC [`old:(uarch_event)list`];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the loop over the  *)
(* columns 1, ..., 6, after the prologue and the first column, each column   *)
(* as the sampling of its polynomial of y and the loop over the rows.        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  YV87_SETUP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6`
   `pc + mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy_join1`
   (YV87_PC 0xfe) YV87_OUTER THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The prologue and the first column ***)

    REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy_join1`
     YV87_J1_0 THEN
    CONJ_TAC THENL
     [YV87_PROLOGUE_TAC;
      LAZY_EVENTS_REASSOC_TAC (GSYM APPEND_ASSOC) THEN
      ENSURES_EVENTS_SEQUENCE_TAC
       `pc +
        mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy_after_mldsa_poly_ntt`
       YV87_MID0 THEN
      CONJ_TAC THENL
       [YV87_POLY_Y_TAC [] `0`;
        ENSURES_EVENTS_WHILE_UP2_TAC `8`
         `pc + mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy_join4`
         `pc + mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy_join5`
         YV87_INNER0 THEN
        REPEAT CONJ_TAC THENL
         [ARITH_TAC; YV87_COL0_INIT_TAC; YV87_COL0_BODY_TAC;
          YV87_COL0_EXIT_TAC]]];

    (*** The other columns ***)

    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    LAZY_EVENTS_REASSOC_TAC LAZY_APPEND_REASSOC3 THEN
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc +
      mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy_after_mldsa_poly_ntt`
     YV87_MID THEN
    CONJ_TAC THENL
     [LAZY_GEN_OLD_TAC "old" THEN
      YV87_POLY_Y_TAC [`l:num`; `old:(uarch_event)list`] `l + 1`;
      LAZY_GEN_OLD_TAC "old" THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `8`
       `pc + mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy_join4`
       `pc + mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy_join5`
       YV87_INNER THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC; YV87_COL_INIT_TAC; YV87_COL_BODY_TAC; YV87_COL_EXIT_TAC]];

    (*** The epilogue ***)

    YV87_EPILOGUE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
