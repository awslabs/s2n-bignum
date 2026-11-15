(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/poly_decompress_d11_spec.ml";;


let D11_BYTES = prove
 (D11_BYTES_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `352`; `n:num`; `11 * i + j`; `s:x86state`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (11 * i + j) = 88 * i + 8 * j`]);;

let D11_HALF = prove
 (D11_HALF_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `352`; `n:num`; `11 * i`; `s:x86state`]
                READ_MEMORY_BYTES16_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EXP; DIV_1; ARITH_RULE `2 EXP 16 = 65536`] THEN
  REWRITE_TAC[ARITH_RULE `8 * 11 * i = 88 * i`]);;

let D11D_LANE = prove
 (D11D_LANE_STMT,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_USHR; VAL_WORD_ADD;
              VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1] THEN
  MP_TAC(ISPEC `f:11 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:11 word)`,`v:num`) THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v MOD 65536 = v /\ v MOD 4294967296 = v`
   (fun th -> REWRITE_TAC[th])
  THENL [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `v < 2048 ==> v * 3329 < 4294967296 /\ v * 3329 + 1024 < 4294967296`] THEN
  SUBGOAL_THEN `(v * 3329 + 1024) DIV 2048 < 65536 /\
                (3329 * v + 1024) DIV 2048 < 65536`
   (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;

let D11D_FIELD = prove
 (D11D_FIELD_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 11 11 = 11`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 8 ==> 11 * k + 11 <= 88`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2048 = 2 EXP 11`] THEN
  REWRITE_TAC[ARITH_RULE `88 * i + 11 * k = 11 * (8 * i + k)`]);;

let WORD_JOIN_MULHU_MULLO = prove
 (WORD_JOIN_MULHU_MULLO_STMT,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `word_mul x y:int16 =
    word_subword (word_mul (word_zx x:int32) (word_zx y:int32)) (0,16)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
                DIMINDEX_16; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
    MP_TAC(ISPEC `x:int16` VAL_BOUND) THEN
    MP_TAC(ISPEC `y:int16` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(x:int16) MOD 4294967296 = val x /\
                  val(y:int16) MOD 4294967296 = val y`
     (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `4294967296 = 65536 * 65536`; MOD_MOD];
    SPEC_TAC(`word_mul (word_zx x:int32) (word_zx y:int32)`,`p:int32`) THEN
    BITBLAST_TAC]);;

let WORD_JOIN_MULHU_MULLO_3329 = prove
 (WORD_JOIN_MULHU_MULLO_3329_STMT,
  GEN_TAC THEN
  MP_TAC(SPECL [`x:int16`; `word 3329:int16`] WORD_JOIN_MULHU_MULLO) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_MUL_SYM]);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + mlkem_poly_decompress_d11_loop1` `pc + mlkem_poly_decompress_d11_loop1_test`
   `\i s. read RDI s = word_add a (word(11 * i)) /\
          read RBX s = word_add r (word(16 * i)) /\
          read RBP s = word_add a (word 352) /\
          read XMM4 s = word 0x0d010d010d010d010d010d010d010d01 /\
          read XMM3 s = word 0x00000400000004000000040000000400 /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
          returnaddress /\
          read (memory :> bytes(a,352)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (11 * j)) MOD 2 EXP 11 + 1024)
                        DIV 2048))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vectors of constants from the image,  ***)
    (*** and saving the registers                                       ***)

    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC (layout "mlkem_poly_decompress_d11" + 0x8) (layout "mlkem_poly_decompress_d11_const1") THEN
    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC (layout "mlkem_poly_decompress_d11" + 0x10) (layout "mlkem_poly_decompress_d11_const2") THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE (layout "mlkem_poly_decompress_d11" + 0x8) (layout "mlkem_poly_decompress_d11_const1") 128)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE (layout "mlkem_poly_decompress_d11" + 0x10) (layout "mlkem_poly_decompress_d11_const2") 128)) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[XMM3; XMM4; READ_ZEROTOP_128] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    CONJ_TAC THEN CONV_TAC WORD_BLAST;

    (*** The loop body, for eleven bytes and eight coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top3" `YMM3` THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    MAP_EVERY (fun j ->
      MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
       (SPECL [`a:int64`; `n:num`; `i:num`; `s0:x86state`;
               mk_small_numeral j] D11_BYTES)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) (1--10) THEN
    MP_TAC(SPECL [`a:int64`; `n:num`; `i:num`; `s0:x86state`] D11_HALF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC `w:88 word = word(n DIV 2 EXP (88 * i))` THEN
    SUBGOAL_THEN `aligned 16 (word_add r (word (16 * i)):int64)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC ALIGNED_WORD_ADD THEN
      ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    MAP_EVERY (fun k ->
      X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--88) THEN
    FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match []
        `read (memory :> bytes128 (word_add r (word (16 * i)))) s = x`) o
             concl)) THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC
      (map2 D11_LANE_RULE (0--7) (CONJUNCTS th))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[XMM3; XMM4; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 8 * (i + 1) <=>
      j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
      j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
      j = 8 * i + 7`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * 8 * i = 16 * i`;
                ARITH_RULE `2 * (8 * i + 1) = 16 * i + 2`;
                ARITH_RULE `2 * (8 * i + 2) = 16 * i + 4`;
                ARITH_RULE `2 * (8 * i + 3) = 16 * i + 6`;
                ARITH_RULE `2 * (8 * i + 4) = 16 * i + 8`;
                ARITH_RULE `2 * (8 * i + 5) = 16 * i + 10`;
                ARITH_RULE `2 * (8 * i + 6) = 16 * i + 12`;
                ARITH_RULE `2 * (8 * i + 7) = 16 * i + 14`] THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "w" THEN
    MAP_EVERY (fun k ->
      MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
       (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D11D_FIELD)
           (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                          (mk_small_numeral k) `8`))))) THEN
      DISCH_THEN SUBST1_TAC) (0--7) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word 352))
                     (word_add a (word (11 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 11 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit, restoring the registers, and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (1--2) THEN
    PTR_DECIDE_RIP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (3--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
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
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_decompress_d11_loop1` `pc + mlkem_poly_decompress_d11_loop1_exit`
   `\i s. read RDI s = word_add a (word(11 * i)) /\
          read RBX s = word_add r (word(16 * i)) /\
          read RBP s = word_add a (word 352) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
          returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC (layout "mlkem_poly_decompress_d11" + 0x8) (layout "mlkem_poly_decompress_d11_const1") THEN
    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC (layout "mlkem_poly_decompress_d11" + 0x10) (layout "mlkem_poly_decompress_d11_const2") THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (1--10) THEN
    REWRITE_TAC[MULT_0; WORD_ADD_0; WORD_VAL_ADD_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (1--5) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `aligned 16 (word_add r (word (16 * i)):int64)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ALIGNED_WORD_ADD THEN
    ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (1--90) THEN
  SUBGOAL_THEN
   `~(val(word_add a (word 352):int64) =
      val(word_add (word_add a (word (11 * i))) (word 11):int64)) <=>
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
   [REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`;
                ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) (1--2) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
