(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/poly_compress_d11_spec.ml";;


let COMPRESS_D11_ARITH = prove
 (COMPRESS_D11_ARITH_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`4096 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(4096 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(4096 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(4294967296 + v * 5284526080) - q * 8589934592` THEN
  ASM_ARITH_TAC);;

let COMPRESS_D11_FIELD = prove
 (COMPRESS_D11_FIELD_STMT,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[WORD_JOIN_SIGN_SMALL; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  SUBGOAL_THEN `val(word_zx(y:int16):int32) < 2147483648` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`] THEN
    UNDISCH_TAC `val(y:int16) < 3329` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_JOIN_SIGN_SMALL_64] THEN
  REWRITE_TAC[WORD_SHL_MUL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_RULE
   `word_mul (word_sub (word_mul (word_sub (word_mul (word_sub (word_mul
      (word_sub (word_mul (word_add (word_mul x (word 4)) x) (word 64))
      (word_add (word_mul x (word 4)) x)) (word 64)) x) (word 8)) x)
      (word 16)) x) (word 2048):int64 =
    word_mul x (word 5284526080)`] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
              VAL_WORD; DIMINDEX_64; DIMINDEX_32; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`;
    ARITH_RULE `y < 3329 ==> y < 18446744073709551616`;
    ARITH_RULE `y < 3329 ==> y * 5284526080 < 18446744073709551616`;
    ARITH_RULE `y < 3329
                ==> y * 5284526080 + 4294967296 < 18446744073709551616`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ADD_SYM] THEN
  ASM_SIMP_TAC[COMPRESS_D11_ARITH]);;

let VAL_JOIN_11X8 = prove
 (VAL_JOIN_11X8_STMT,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`u0:11 word`; `u1:11 word`; `u2:11 word`; `u3:11 word`;
    `u4:11 word`; `u5:11 word`; `u6:11 word`; `u7:11 word`] THEN
  REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun k ->
    SPEC_TAC(mk_comb(`val:11 word->num`,
                     mk_var("u"^string_of_int k,`:11 word`)),
             mk_var("n"^string_of_int k,`:num`))) (0--7) THEN
  REPEAT STRIP_TAC THEN REPEAT MOD_LT_ASM_TAC THEN ARITH_TAC);;

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 24 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN

  (*** The loop, over groups of 8 coefficients ***)

  ENSURES_WHILE_UP_TAC `32` `pc + mlkem_poly_compress_d11_loop1` `pc + mlkem_poly_compress_d11_loop1_test`
   `\i s. read RSI s = word_add a (word(16 * i)) /\
          read RCX s = word_add r (word(11 * i)) /\
          read RDI s = word_add r (word 352) /\
          read XMM3 s = word 0x00000001000000000000000100000000 /\
          read XMM4 s = word 0 /\
          read XMM5 s = word 0 /\
          read XMM6 s = word 0x07ff07ff07ff07ff07ff07ff07ff07ff /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          ((!j. j < 256 ==> val(x j) < 3329)
           ==> read(memory :> bytes(r,11 * i)) s =
               nsum {j | j < 8 * i}
                (\j. ((4096 * val(x j) + 3329) DIV 6658) MOD 2048 *
                     2 EXP (11 * j)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the registers, with the vectors of       ***)
    (*** constants from the image                                        ***)

    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC (layout "mlkem_poly_compress_d11" + 0x19) (layout "mlkem_poly_compress_d11_const1") THEN
    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC (layout "mlkem_poly_compress_d11" + 0x26) (layout "mlkem_poly_compress_d11_const2") THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE (layout "mlkem_poly_compress_d11" + 0x19) (layout "mlkem_poly_compress_d11_const1") 128)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE (layout "mlkem_poly_compress_d11" + 0x26) (layout "mlkem_poly_compress_d11_const2") 128)) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[XMM3; XMM4; XMM5; XMM6; READ_ZEROTOP_128] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                NSUM_CLAUSES_NUMSEG_LT; READ_MEMORY_BYTES_TRIVIAL] THEN
    REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST;

    (*** The loop body, for eight coefficients and eleven bytes ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MAP_EVERY (fun n ->
      GHOST_INTRO_TAC (mk_var("ymm"^string_of_int n^"_init",`:int256`))
       (mk_comb(`read:(x86state,int256)component->x86state->int256`,
                mk_const("YMM"^string_of_int n,[])))) [0;1;2;7;8;9] THEN
    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top3" `YMM3` THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    XMM_EXISTSTOP_TAC "top5" `YMM5` THEN
    XMM_EXISTSTOP_TAC "top6" `YMM6` THEN
    MP_TAC(SPECL [`a:int64`; `s0:x86state`; `x:num->int16`; `i:num`]
                 READ_MEMORY_BYTES128_JOIN_16) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `aligned 16 (word_add a (word (16 * i)):int64)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC ALIGNED_WORD_ADD THEN
      ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    MAP_EVERY (fun k ->
      X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--88) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (89--156) THEN

    (*** The new bytes as parts of the join of the 11-bit fields ***)

    D11_PACK_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[XMM3; XMM4; XMM5; XMM6; READ_ZEROTOP_128] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
      CONV_TAC WORD_RULE;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`word_add r (word(11 * i)):int64`; `11`;
                  mk_comb(`val:88 word->num`,d11_join); `s156:x86state`]
                 READ_MEMORY_BYTES_OF_BYTES8) THEN
    ANTS_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_CLAUSES;
                  WORD_ADD_0] THEN
      ASM_REWRITE_TAC[WORD_SUBWORD_BYTE] THEN CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPEC d11_join VAL_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    SIMP_TAC[MOD_LT] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[VAL_JOIN_11X8] THEN

    (*** The compression of each coefficient ***)

    MAP_EVERY (fun jt ->
      MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
        (SPEC (mk_comb(`x:num->int16`,jt)) COMPRESS_D11_FIELD)) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (can (term_match []
                `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o concl)) THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) compress_d11_indices THEN

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
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add r (word 352))
                     (word_add r (word (11 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 11 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit, restoring the registers, and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (1--2) THEN
    PTR_DECIDE_RIP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (3--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (is_imp o concl))]);;

let MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
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
  WORD_FORALL_OFFSET_TAC 24 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_compress_d11_loop1` `pc + mlkem_poly_compress_d11_loop1_exit`
   `\i s. read RSI s = word_add a (word(16 * i)) /\
          read RCX s = word_add r (word(11 * i)) /\
          read RDI s = word_add r (word 352) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC (layout "mlkem_poly_compress_d11" + 0x19) (layout "mlkem_poly_compress_d11_const1") THEN
    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC (layout "mlkem_poly_compress_d11" + 0x26) (layout "mlkem_poly_compress_d11_const2") THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (1--10) THEN
    REWRITE_TAC[MULT_0; WORD_ADD_0; WORD_VAL_ADD_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (1--4) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `aligned 16 (word_add a (word (16 * i)):int64)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ALIGNED_WORD_ADD THEN
    ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_EXEC (1--158) THEN
  SUBGOAL_THEN
   `~(val(word_add r (word 352):int64) =
      val(word_add (word_add r (word (11 * i))) (word 11):int64)) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 11 * i + 11 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun _ -> CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`;
                ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) (1--2) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
