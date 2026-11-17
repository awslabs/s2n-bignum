(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Product of a row of the matrix with a vector, in the NTT domain, with the *)
(* entries sampled on demand: the proof (see                                 *)
(* polyvec_matrix_pointwise_montgomery_row_lazy_65_spec.ml).                 *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;
needs "x86/proofs/utils/mldsa_native_lazy_rr.ml";;

let RL65_EXEC =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The events: the prologue, with the first entry, the loop over the columns *)
(* 1, ..., 4, and the epilogue. The code aligns its frame to 32 bytes, so    *)
(* that the addresses in it are at fixed offsets from bot                    *)
(* (utils/mldsa_native_realign.ml), which REALIGN_UNBOT_TAC expands at the   *)
(* end of each part, and the events of the samplings depend on their seeds,  *)
(* functions of rho, i and the column.                                       *)
(* ------------------------------------------------------------------------- *)

let RL65_TEMPLATE =
 `\(t:int64) (mat:int64) (v:int64) (rho:num) (i:num) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   APPEND (f_ev_epil t mat v rho i pc stackpointer returnaddress)
    (APPEND
      (ENUMERATEL 4
        (\k. f_ev_loop t mat v rho i pc stackpointer returnaddress k))
      (f_ev_prol t mat v rho i pc stackpointer returnaddress))
   :(uarch_event)list`;;

let RL65_ALLOWED =
  [`pc:num`; `t:int64`; `mat:int64`; `v:int64`; `rho:num`; `i:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

let RL65_CALL_TAC vars name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc RL65_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   (vars @ RL65_ALLOWED) n;;

(* ------------------------------------------------------------------------- *)
(* The frame of 1670 bytes below the return address: the six registers that  *)
(* the function saves (k = 1622, so that the AND of the stack pointer is of  *)
(* word_add stackpointer (word 1622) after                                   *)
(* REPEAT_GEN_AND_OFFSET_STACKPTR_TAC), and the aligned part (bot,1591),     *)
(* with RSP at bot + 1495 after the SUB, the byte i kept at bot + 1526, the  *)
(* buffer of 64 bytes at bot + 1527 (rho, and the bytes j and i of the seed  *)
(* at bot + 1559 and bot + 1560), and the stack of mldsa_poly_uniform, with  *)
(* its return address, below RSP. The invariant of the loop over the         *)
(* columns k + 1 for k < 4: t holds the sum of the products of the columns   *)
(* up to k, mld_lazy_acc rho y i k.                                          *)
(* ------------------------------------------------------------------------- *)

let RL65_INV =
 `\k s.
    read RSP s = word_add bot (word 1495) /\
    read RBP s = word_add stackpointer (word 1662) /\
    read (memory :> bytes64 (word_add stackpointer (word 1670))) s =
    returnaddress /\
    read (memory :> bytes64 (word_add stackpointer (word 1662))) s =
    rbp_init /\
    read (memory :> bytes64 (word_add stackpointer (word 1654))) s =
    r15_init /\
    read (memory :> bytes64 (word_add stackpointer (word 1646))) s =
    r14_init /\
    read (memory :> bytes64 (word_add stackpointer (word 1638))) s =
    r13_init /\
    read (memory :> bytes64 (word_add stackpointer (word 1630))) s =
    r12_init /\
    read (memory :> bytes64 (word_add stackpointer (word 1622))) s =
    rbx_init /\
    read R12 s = mat /\ read R13 s = t /\
    read R14 s = word_add bot (word 1527) /\
    read R15 s = word(k + 1) /\
    read RBX s = word_add v (word(1024 * (k + 1))) /\
    ~read DF s /\
    read (memory :> bytes(word_add bot (word 1527),32)) s = rho /\
    read (memory :> bytes8(word_add bot (word 1526))) s = word i /\
    (!j. j < 1280
         ==> read (memory :> bytes32 (word_add v (word(4 * j)))) s = y j) /\
    (!j. j < 256
         ==> read (memory :> bytes32 (word_add t (word(4 * j)))) s =
             mld_lazy_acc rho y i k j)`;;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, the template, the realigned frame, with   *)
(* the alignment of RSP for the aligned stores to the buffer, the saved      *)
(* registers, and the termination of the samplings of the entries.           *)
(* ------------------------------------------------------------------------- *)

let RL65_SETUP_TAC =
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
    MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_RED" THEN
  CONCRETIZE_F_EVENTS_TAC RL65_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst RL65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 1622 THEN REALIGN_FRAME_TAC 1670 1622 THEN
  REALIGN_NONOV_TAC 1591
   [`t:int64,1024`; `mat:int64,1024`; `word_add mat (word 1024):int64,32`;
    `v:int64,5120`; `word pc:int64,libmldsa_size`;
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
   (can (term_match [] `mld_matrix_terminates 6 5 rho`) o concl)) THEN
  SUBGOAL_THEN `i < 256` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The prologue: rho is loaded as two 128-bit words into the YMM registers   *)
(* named at the start, so that the facts for their new low halves are kept,  *)
(* and stored to the buffer, with the bytes 0 and i after it, and RSP gets   *)
(* the value of the AND after step 12. Then entry (i,0) is sampled into t    *)
(* and multiplied by polynomial 0 of y.                                      *)
(* ------------------------------------------------------------------------- *)

let RL65_PROLOGUE_TAC =
  FULL_INIT_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match []
     `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o concl))
  THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rho < 2 EXP 256` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check
     (can (term_match []
       `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o
      concl)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    MP_TAC(ISPECL [`word_add mat (word 1024):int64`; `32`;
                   `read memory (s0:x86state)`] READ_BYTES_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SAMPLING_GHOST_REGS_TAC [`YMM1`; `YMM2`] "s0" THEN
  X86_STEPS_TAC RL65_EXEC (1--12) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC RL65_EXEC (13--22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAMPLING_SUBWORD_JOIN_128;
                              MATCH_MP LAZY_BYTE_64 (ASSUME `i < 256`)]) THEN
  MP_TAC(SPECL [`word_add bot (word 1527):int64`; `rho:num`; `s22:x86state`]
               LAZY_RHO_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`word_add bot (word 1527):int64`; `rho:num`; `i:num`; `0`;
                `s22:x86state`] LAZY_SEED) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC] THEN
  LAZY_TERM_TAC
   `mld_rej_uniform_terminates
     (mld_shake128_stream 34 (mld_matrix_seed rho i 0))` THEN
  X86_STEPS_TAC RL65_EXEC (23--23) THEN
  RL65_CALL_TAC [] "H_UNI"
   [`read RDI s`; `read RSI s`; `mld_matrix_seed rho i 0`] 24 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]) THEN
  X86_STEPS_TAC RL65_EXEC (25--28) THEN
  VEC_SLICE_TAC
   `!j. j < 256
        ==> read(memory :> bytes32(word_add v (word(4 * j)))) s28 =
            (y:num->int32) j` THEN
  RL65_CALL_TAC [] "H_PWM"
   [`read RDI s`; `read RSI s`; `mld_matrix_entry rho i 0`;
    `y:num->int32`] 29 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; mld_lazy_acc; MLD_POLY_OF_0] THEN
  ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The body of the loop for column k + 1, with the loop test: the bytes k +  *)
(* 1 and i (reloaded from the stack) after rho in the buffer, the sampling   *)
(* of entry (i,k + 1) into the polynomial of the structure, its product with *)
(* polynomial k + 1 of y, and its addition to t.                             *)
(* ------------------------------------------------------------------------- *)

let RL65_BODY_TAC =
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `k + 1 < 256 /\ (k + 1) + 1 < 2 EXP 32` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC RL65_EXEC (1--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP LAZY_BYTE_64 (ASSUME `k + 1 < 256`);
    MATCH_MP LAZY_BYTE_ZX (ASSUME `i < 256`);
    MATCH_MP WORD_ZX_ADD_SMALL (ASSUME `(k + 1) + 1 < 2 EXP 32`)]) THEN
  MP_TAC(SPECL [`word_add bot (word 1527):int64`; `rho:num`; `i:num`;
                `k + 1`; `s6:x86state`] LAZY_SEED) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  LAZY_TERM_TAC
   `mld_rej_uniform_terminates
     (mld_shake128_stream 34 (mld_matrix_seed rho i (k + 1)))` THEN
  X86_STEPS_TAC RL65_EXEC (7--7) THEN
  RL65_CALL_TAC [`k:num`] "H_UNI"
   [`read RDI s`; `read RSI s`; `mld_matrix_seed rho i (k + 1)`] 8 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM mld_matrix_entry]) THEN
  X86_STEPS_TAC RL65_EXEC (9--12) THEN
  VEC_SLICE_TAC
   `!j. j < 256
        ==> read(memory :> bytes32
                  (word_add v (word(1024 * (k + 1) + 4 * j)))) s12 =
            (y:num->int32)(256 * (k + 1) + j)` THEN
  RL65_CALL_TAC [`k:num`] "H_PWM"
   [`read RDI s`; `read RSI s`; `mld_matrix_entry rho i (k + 1)`;
    `\j. (y:num->int32)(256 * (k + 1) + j)`] 13 THEN
  X86_STEPS_TAC RL65_EXEC (14--16) THEN
  RL65_CALL_TAC [`k:num`] "H_ADD"
   [`read RDI s`; `read RSI s`; `mld_lazy_acc rho y i k`;
    `mld_poly_pointwise_montgomery (mld_matrix_entry rho i (k + 1))
      (\j. (y:num->int32)(256 * (k + 1) + j))`] 17 THEN
  X86_STEPS_TAC RL65_EXEC (18--19) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MLD_LAZY_ACC_ADD1; mld_poly_of] THEN
  ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* After the loop: the reduction of t, the zeroing of the buffer, and the    *)
(* restoring of the registers and the return.                                *)
(* ------------------------------------------------------------------------- *)

let RL65_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC RL65_EXEC (1--2) THEN
  RL65_CALL_TAC [] "H_RED" [`read RDI s`; `mld_lazy_acc rho y i 4`] 3 THEN
  X86_STEPS_TAC RL65_EXEC (4--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mld_polyvec_matrix_row_lazy] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  RL65_SETUP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `4`
   `pc + mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy_loop1`
   `pc + mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy_loop1_exit`
   RL65_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; RL65_PROLOGUE_TAC; RL65_BODY_TAC; RL65_EXIT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
