(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the proof (see          *)
(* compute_pack_t0_t1_65_spec.ml).                                           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/compute_pack_t0_t1_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;
needs "x86/proofs/utils/mldsa_native_top.ml";;
needs "x86/proofs/utils/mldsa_native_wrap.ml";;

let CPT65_EXEC = MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame of 38053 bytes below the return address: the six registers that *)
(* the function saves (k = 38005 bytes below the return address, so that the *)
(* AND of the stack pointer is of word_add stackpointer (word 38005) after   *)
(* REPEAT_GEN_AND_OFFSET_STACKPTR_TAC), and the aligned part (bot,37974) of  *)
(* utils/mldsa_native_realign.ml, with RSP at bot + 5174 after the SUB, the  *)
(* spills of s1hat, the address of the matrix and the row counter at bot +   *)
(* 5182, + 5190 and + 5202, the polynomials of t and t1 at bot + 5206 and +  *)
(* 6230, the matrix at bot + 7254 up to the AND, and the stacks of the       *)
(* callees below RSP. Polynomial k of t, as the code computes it.            *)
(* ------------------------------------------------------------------------- *)

let CPT65_PACK_T1 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`5`; `mld_polyeta_unpack_4`; `128`] MLD_COMPUTE_T_PACK_T1);;

let CPT65_PACK_T0 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`5`; `mld_polyeta_unpack_4`; `128`] MLD_COMPUTE_T_PACK_T0);;

let CPT65_ALLOWED =
  [`pc:num`; `pkt1:int64`; `t0:int64`; `s1hat:int64`; `s2:int64`;
   `rho:int64`; `r:num`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let CPT65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc CPT65_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   CPT65_ALLOWED n;;

let CPT65_LOOP_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc CPT65_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   (`i:num`::CPT65_ALLOWED) n;;

(* ------------------------------------------------------------------------- *)
(* The invariant of the loop over the 6 rows, for i rows done: the frame,    *)
(* the counter in RAX, the buffers and the matrix, the inputs, and the       *)
(* packed polynomials of t1 and t0 so far. The direction flag, the GOT entry *)
(* of memset and the region (ea,el) are kept for the zeroing at the end.     *)
(* ------------------------------------------------------------------------- *)

let CPT65_INVARIANT =
 `\i s. read RSP s = word_add bot (word 5174) /\
        read RBP s = word_add stackpointer (word 38045) /\
        read (memory :> bytes64 (word_add stackpointer (word 38045))) s =
        rbp_init /\
        read (memory :> bytes64 (word_add stackpointer (word 38037))) s =
        r15_init /\
        read (memory :> bytes64 (word_add stackpointer (word 38029))) s =
        r14_init /\
        read (memory :> bytes64 (word_add stackpointer (word 38021))) s =
        r13_init /\
        read (memory :> bytes64 (word_add stackpointer (word 38013))) s =
        r12_init /\
        read (memory :> bytes64 (word_add stackpointer (word 38005))) s =
        rbx_init /\
        read (memory :> bytes64 (word_add stackpointer (word 38053))) s =
        returnaddress /\
        read RAX s = word i /\
        read RBX s = word_add bot (word 5206) /\
        read R12 s = word_add bot (word 6230) /\
        read R13 s = word_add t0 (word(416 * i)) /\
        read R14 s = word_add pkt1 (word(320 * i)) /\
        read R15 s = word_add s2 (word(128 * i)) /\
        read (memory :> bytes64 (word_add bot (word 5182))) s = s1hat /\
        read (memory :> bytes64 (word_add bot (word 5190))) s =
        word_add bot (word 7254) /\
        ~read DF s /\
        read (memory :> bytes64 (word(pc + got_memset))) s = mf /\
        read (memory :> bytes(ea,el)) s = ev /\
        (!j. j < 7680
             ==> read (memory :> bytes32
                        (word_add bot (word(7254 + 4 * j)))) s =
                 mld_polyvec_matrix_expand 5 r j) /\
        (!j. j < 1280
             ==> read(memory :> bytes32(word_add s1hat (word(4 * j)))) s =
                 sh j) /\
        (!j. j < 768
             ==> read(memory :> bytes8(word_add s2 (word j))) s =
                 s2b j) /\
        (!j. j < 320 * i
             ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                 mld_polyvec_pack 320 mld_polyt1_pack
                  (mld_polyvec_map mld_poly_power2round_hi
                    (mld_compute_t 5 mld_polyeta_unpack_4 128 r sh s2b)) j) /\
        (!j. j < 416 * i
             ==> read(memory :> bytes8(word_add t0 (word j))) s =
                 mld_polyvec_pack 416 mld_polyt0_pack
                  (mld_polyvec_map mld_poly_power2round_lo
                    (mld_compute_t 5 mld_polyeta_unpack_4 128 r sh s2b)) j)`;;

(* ------------------------------------------------------------------------- *)
(* The prologue, with the expansion of the matrix; RSP gets the value of the *)
(* AND after step 12.                                                        *)
(* ------------------------------------------------------------------------- *)

let CPT65_PROLOGUE_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC CPT65_EXEC (1--12) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC CPT65_EXEC (13--20) THEN
  CPT65_CALL_TAC "H_MEXP" [`read RDI s`; `read RSI s`; `r:num`] 21 THEN
  X86_STEPS_TAC CPT65_EXEC (22--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

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

(* ------------------------------------------------------------------------- *)
(* The body of the loop for row i, with the loop test. The counter is kept   *)
(* as 32 bits on the stack across the calls.                                 *)
(* ------------------------------------------------------------------------- *)

let CPT65_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC CPT65_EXEC (1--5) THEN
  SUBGOAL_THEN `word_zx(word_zx(word i:int64):int32):int64 = word i`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC WORD_ZX_ZX_SMALL THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC CPT65_EXEC (6--6) THEN
  CPT65_LOOP_CALL_TAC "H_ROW"
   [`read RDI s`; `read RSI s`; `read RDX s`;
    `mld_polyvec_matrix_expand 5 r`; `sh:num->int32`; `i:num`] 7 THEN
  X86_STEPS_TAC CPT65_EXEC (8--9) THEN
  CPT65_LOOP_CALL_TAC "H_INV" [`read RDI s`; CPT65_ACC] 10 THEN
  X86_STEPS_TAC CPT65_EXEC (11--14) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_M128]) THEN
  VEC_SLICE_TAC
   `!j. j < 128
        ==> read(memory :> bytes8(word_add s2 (word(128 * i + j)))) s14 =
            (s2b:num->byte)(128 * i + j)` THEN
  CPT65_LOOP_CALL_TAC "H_UNPACK"
   [`read RDI s`; `read RSI s`; `\j. (s2b:num->byte)(128 * i + j)`] 15 THEN
  X86_STEPS_TAC CPT65_EXEC (16--18) THEN
  CPT65_LOOP_CALL_TAC "H_ADD"
   [`read RDI s`; `read RSI s`; mk_comb(`mld_poly_invntt_tomont`,CPT65_ACC);
    CPT65_UNPACK] 19 THEN
  X86_STEPS_TAC CPT65_EXEC (20--21) THEN
  CPT65_LOOP_CALL_TAC "H_RED" [`read RDI s`; CPT65_ADD] 22 THEN
  X86_STEPS_TAC CPT65_EXEC (23--24) THEN
  CPT65_LOOP_CALL_TAC "H_CADDQ"
   [`read RDI s`; mk_comb(`mld_poly_reduce`,CPT65_ADD)] 25 THEN
  X86_STEPS_TAC CPT65_EXEC (26--29) THEN
  CPT65_LOOP_CALL_TAC "H_P2R" [`read RDI s`; `read RSI s`; CPT65_CADDQ] 30 THEN
  X86_STEPS_TAC CPT65_EXEC (31--34) THEN
  CPT65_LOOP_CALL_TAC "H_T1"
   [`read RDI s`; `read RSI s`;
    mk_comb(`mld_poly_power2round_hi`,CPT65_CADDQ)] 35 THEN
  X86_STEPS_TAC CPT65_EXEC (36--39) THEN
  CPT65_LOOP_CALL_TAC "H_T0"
   [`read RDI s`; `read RSI s`;
    mk_comb(`mld_poly_power2round_lo`,CPT65_CADDQ)] 40 THEN
  X86_STEPS_TAC CPT65_EXEC (41--42) THEN
  SUBGOAL_THEN
   `word_zx(word_zx(word i:int64):int32):int64 = word i /\
    word_zx(word_add (word_zx(word i:int64):int32) (word 1)):int64 =
    word(i + 1)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WORD_ZX_ZX_SMALL; MATCH_MP_TAC WORD_ZX_ADD_SMALL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC CPT65_EXEC (43--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  W32_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CPT65_JOIN_TAC CPT65_PACK_T1 THEN NO_TAC) THEN
  TRY(CPT65_JOIN_TAC CPT65_PACK_T0 THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The zeroing of the two polynomials with REP STOSQ and of the matrix with  *)
(* memset, through its PLT stub, and the return.                             *)
(* ------------------------------------------------------------------------- *)

let CPT65_EPILOGUE_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC CPT65_EXEC (1--12) THEN
  LIBC_PLT_TAC CPT65_EXEC (layout "plt_memset") (layout "got_memset") 12
  THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" CPT65_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref CPT65_ALLOWED) 14 THEN
  X86_STEPS_TAC CPT65_EXEC (15--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let CPT65_SETUP_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_MEXP" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_ROW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_INPLACE
   "H_P2R" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_T1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_T0" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pkt1:int64) (t0:int64) (s1hat:int64) (s2:int64) (rho:int64) (r:num)
     (mf:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
     APPEND
      (f_ev_epil pkt1 t0 s1hat s2 rho r mf pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL 6
          (\i. f_ev_loop pkt1 t0 s1hat s2 rho r mf pc stackpointer
                         returnaddress i))
        (f_ev_prol pkt1 t0 s1hat s2 rho r mf pc stackpointer
                   returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst CPT65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 38005 THEN REALIGN_FRAME_TAC 38053 38005 THEN
  REALIGN_NONOV_TAC 37974
   [`pkt1:int64,1920`; `t0:int64,2496`; `s1hat:int64,5120`; `s2:int64,768`;
    `rho:int64,32`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `ea:int64,el:num`;
    `word_add stackpointer (word 38005):int64,48`;
    `word_add stackpointer (word 38053):int64,8`] THEN
  REALIGN_ALIGNED_TAC [5206; 6230] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  CPT65_SETUP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6`
   `pc + mld_compute_pack_t0_t165_loop1`
   `pc + mld_compute_pack_t0_t165_loop1_exit`
   CPT65_INVARIANT THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; CPT65_PROLOGUE_TAC; CPT65_BODY_TAC; CPT65_EPILOGUE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
