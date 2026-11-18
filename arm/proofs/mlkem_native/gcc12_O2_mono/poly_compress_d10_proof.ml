(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_compress_d10_spec.ml";;


let COMPRESS_D10_ARITH = prove
 (COMPRESS_D10_ARITH_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2048 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(2048 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(2048 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(4294967296 + v * 2642263040) - q * 8589934592` THEN
  ASM_ARITH_TAC);;

let WORD_SX_SMALL_64 = prove
 (WORD_SX_SMALL_64_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SX_ZX_GEN; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~bit 15 (y:int16)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[BIT_VAL] THEN
    ASM_SIMP_TAC[DIV_LT; ARITH_RULE `2 EXP 15 = 32768`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[WORD_OR_0]]);;

let COMPRESS_D10_FIELD = prove
 (COMPRESS_D10_FIELD_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SX_SMALL_64; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_64; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 18446744073709551616`;
    ARITH_RULE `y < 3329
                ==> 4294967296 + y * 2642263040 < 18446744073709551616`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[COMPRESS_D10_ARITH]);;

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

let VAL_JOIN_10X4 = prove
 (VAL_JOIN_10X4_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`u0:10 word`; `u1:10 word`; `u2:10 word`; `u3:10 word`] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1024 * val(u1:10 word) + val(u0:10 word) < 1048576`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1048576 * val(u2:10 word) +
                1024 * val(u1:10 word) + val(u0:10 word) < 1073741824`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1073741824 * val(u3:10 word) +
                1048576 * val(u2:10 word) +
                1024 * val(u1:10 word) + val(u0:10 word) < 1099511627776`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [ASM_ARITH_TAC; ARITH_TAC]);;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN

  (*** The outer loop, over groups of 4 coefficients ***)

  ENSURES_WHILE_UP_TAC `64` `pc + mlk_poly_compress_d10_c_loop1`
   `pc + mlk_poly_compress_d10_c_loop1_test`
   `\i s. read X4 s = word_add r (word(5 * i)) /\
          read X3 s = word(4 * i + 4) /\
          read X6 s = a /\
          read X7 s = word 4294967296 /\
          read X8 s = word 2642263040 /\
          read X12 s = word_add stackpointer (word 16) /\
          read SP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          canary /\
          read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
          guard /\
          read (memory :> bytes64 guard) s = canary /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          ((!j. j < 256 ==> val(x j) < 3329)
           ==> read(memory :> bytes(r,5 * i)) s =
               nsum {j | j < 4 * i}
                (\j. ((2048 * val(x j) + 3329) DIV 6658) MOD 1024 *
                     2 EXP (10 * j)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the return address and the stack guard ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (2--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                NSUM_CLAUSES_NUMSEG_LT; READ_MEMORY_BYTES_TRIVIAL];

    (*** The loop body, for four coefficients and five bytes ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun jt ->
      FIRST_ASSUM(MP_TAC o SPEC jt o check (is_forall o concl)) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i < 64` THEN ARITH_TAC; DISCH_TAC])
     (butlast d10_indices) THEN
    COMPRESS_D10_BODY_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `4 * (i + 1) + 4 = (4 * i + 4) + 4`] THEN
      WORD_SMALL_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    (*** The new bytes as parts of the join of the 10-bit fields ***)

    MAP_EVERY D10_PACK_TAC (0--4) THEN
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
    MP_TAC(SPEC (mk_comb(`val:40 word->num`,d10_join)) BYTES_OF_NUM_5) THEN
    MP_TAC(ISPEC d10_join VAL_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MP th)) THEN
    REWRITE_TAC[VAL_JOIN_10X4] THEN

    (*** The compression of each coefficient ***)

    MAP_EVERY (fun jt ->
      MP_TAC(SPEC (mk_comb(`x:num->int16`,jt)) COMPRESS_D10_FIELD) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (can (term_match []
                `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o concl)) THEN
        UNDISCH_TAC `i < 64` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) (butlast d10_indices) THEN

    (*** The new values in the number for the output ***)

    REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`; NSUM_LT_ADD] THEN
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
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit, the check of the stack guard and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (2--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (4--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (is_imp o concl))]);;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (guard:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a r guard pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 64
            (\i. f_ev_loop a r guard pc stackpointer returnaddress i))
          (f_ev_prol a r guard pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE;
              SOME_FLAGS;
              fst MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mlk_poly_compress_d10_c_loop1`
   `pc + mlk_poly_compress_d10_c_loop1_exit`
    `\i s. read X4 s = word_add r (word(5 * i)) /\
           read X3 s = word(4 * i + 4) /\
           read X6 s = a /\
           read X12 s = word_add stackpointer (word 16) /\
           read SP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           read (memory :> bytes64 (word_add stackpointer (word 24))) s =
           canary /\
           read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
           guard /\
           read (memory :> bytes64 guard) s = canary` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (2--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (2--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  COMPRESS_D10_BODY_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (49--50) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(val(word_sub
           (word_zx (word_zx (word_add (word_zx (word (4 * i + 4):int64):int32)
                                       (word 4)):int64):int32)
           (word 260):int32) = 0) <=>
    i + 1 < 64`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 64 ==> 4 * i + 4 < 18446744073709551616 /\
                 4 * i + 4 < 4294967296 /\
                 (4 * i + 4) + 4 < 4294967296 /\
                 (4 * i + 4) + 4 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) + 4 = (4 * i + 4) + 4`] THEN
    WORD_SMALL_TAC;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
