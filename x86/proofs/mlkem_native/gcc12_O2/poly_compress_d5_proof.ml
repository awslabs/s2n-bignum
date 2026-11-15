(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/poly_compress_d5_spec.ml";;


let COMPRESS_D5_ARITH = prove
 (COMPRESS_D5_ARITH_STMT,
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let COMPRESS_D5_FIELD = prove
 (COMPRESS_D5_FIELD_STMT,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[WORD_JOIN_SIGN_SMALL; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[WORD_SHL_MUL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_RULE
   `word_mul (word_sub (word_mul (word_sub (word_mul (word_add
      (word_mul x (word 4)) x) (word 64)) (word_add (word_mul x (word 4)) x))
      (word 64)) x) (word 64):int32 =
    word_mul x (word 1290176)`] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
              VAL_WORD; DIMINDEX_32; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`;
    ARITH_RULE `y < 3329 ==> y * 1290176 < 4294967296`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 134217728 * 32`; GSYM DIV_MOD] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ADD_SYM] THEN
  ASM_SIMP_TAC[COMPRESS_D5_ARITH]);;

let BYTES_OF_NUM_5 = prove
 (BYTES_OF_NUM_5_STMT,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(n DIV 4294967296) MOD 256 = n DIV 4294967296`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `n < 2 EXP 40` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 256`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 65536`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 16777216`; `256`] DIVISION) THEN
  REWRITE_TAC[DIV_DIV; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let VAL_JOIN_5X8 = prove
 (VAL_JOIN_5X8_STMT,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`u0:5 word`; `u1:5 word`; `u2:5 word`; `u3:5 word`;
    `u4:5 word`; `u5:5 word`; `u6:5 word`; `u7:5 word`] THEN
  REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun k ->
    SPEC_TAC(mk_comb(`val:5 word->num`,mk_var("u"^string_of_int k,`:5 word`)),
             mk_var("n"^string_of_int k,`:num`))) (0--7) THEN
  REPEAT STRIP_TAC THEN REPEAT MOD_LT_ASM_TAC THEN ARITH_TAC);;

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN

  (*** The loop, over groups of 8 coefficients ***)

  ENSURES_WHILE_UP_TAC `32` `pc + mlkem_poly_compress_d5_loop1` `pc + mlkem_poly_compress_d5_loop1_test`
   `\i s. read RCX s = word_add a (word(16 * i)) /\
          read RDX s = word_add r (word(5 * i)) /\
          read RSI s = word_add r (word 160) /\
          read XMM2 s = word 0x00000000000000000400000004000000 /\
          read XMM3 s = word 0 /\
          read XMM4 s = word 0x000000000000000000ff00ff00ff00ff /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          ((!j. j < 256 ==> val(x j) < 3329)
           ==> read(memory :> bytes(r,5 * i)) s =
               nsum {j | j < 8 * i}
                (\j. ((64 * val(x j) + 3329) DIV 6658) MOD 32 *
                     2 EXP (5 * j)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the registers, with the vectors of       ***)
    (*** constants from the image                                        ***)

    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE (layout "mlkem_poly_compress_d5" + 0x16) (layout "mlkem_poly_compress_d5_const2") 64)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE (layout "mlkem_poly_compress_d5" + 0x23) (layout "mlkem_poly_compress_d5_const1") 64)) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[XMM2; XMM3; XMM4; READ_ZEROTOP_128] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                NSUM_CLAUSES_NUMSEG_LT; READ_MEMORY_BYTES_TRIVIAL] THEN
    REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST;

    (*** The loop body, for eight coefficients and five bytes ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
    GHOST_INTRO_TAC `ymm7_init:int256` `read YMM7` THEN
    GHOST_INTRO_TAC `ymm8_init:int256` `read YMM8` THEN
    GHOST_INTRO_TAC `ymm9_init:int256` `read YMM9` THEN
    GHOST_INTRO_TAC `ymm10_init:int256` `read YMM10` THEN
    GHOST_INTRO_TAC `ymm11_init:int256` `read YMM11` THEN
    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top2" `YMM2` THEN
    XMM_EXISTSTOP_TAC "top3" `YMM3` THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    COMPRESS_D5_LOADS_TAC THEN
    MAP_EVERY (fun k ->
      X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--77) THEN
    COMPRESS_D5_TIDY_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (78--124) THEN

    (*** The new bytes as parts of the join of the 5-bit fields ***)

    D5_PACK_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[XMM2; XMM3; XMM4; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
      CONV_TAC WORD_RULE;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE
     `5 * (i + 1) = ((((5 * i + 1) + 1) + 1) + 1) + 1`] THEN
    REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN
    REWRITE_TAC[ARITH_RULE `(5 * i + 1) + 1 = 5 * i + 2`;
                ARITH_RULE `(5 * i + 2) + 1 = 5 * i + 3`;
                ARITH_RULE `(5 * i + 3) + 1 = 5 * i + 4`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INST_TYPE [`:40`,`:M`; `:8`,`:N`] VAL_WORD_SUBWORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_1] THEN
    MP_TAC(SPEC (mk_comb(`val:40 word->num`,d5_join)) BYTES_OF_NUM_5) THEN
    MP_TAC(ISPEC d5_join VAL_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MP th)) THEN
    REWRITE_TAC[VAL_JOIN_5X8] THEN

    (*** The compression of each coefficient ***)

    MAP_EVERY (fun jt ->
      MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
        (SPEC (mk_comb(`x:num->int16`,jt)) COMPRESS_D5_FIELD)) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (can (term_match []
                `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o concl)) THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) compress_d5_indices THEN

    (*** The new values in the number for the output ***)

    REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`; NSUM_LT_ADD] THEN
    REWRITE_TAC[NUMSEG_LT; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUM_RING;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add r (word (5 * i)))
                     (word_add r (word 160)):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 5 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit, restoring the registers, and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--2) THEN
    PTR_DECIDE_RIP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (3--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (is_imp o concl))]);;

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 32
            (\i. f_ev_loop a r pc stackpointer returnaddress i))
          (f_ev_prol a r pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `a:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_compress_d5_loop1` `pc + mlkem_poly_compress_d5_loop1_exit`
   `\i s. read RCX s = word_add a (word(16 * i)) /\
          read RDX s = word_add r (word(5 * i)) /\
          read RSI s = word_add r (word 160) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--9) THEN
    REWRITE_TAC[MULT_0; WORD_ADD_0; WORD_VAL_ADD_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--3) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--126) THEN
  SUBGOAL_THEN
   `~(val(word_add (word_add r (word (5 * i))) (word 5):int64) =
      val(word_add r (word 160):int64)) <=> i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 5 * i + 5 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun _ -> CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`;
                ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) (1--2) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
