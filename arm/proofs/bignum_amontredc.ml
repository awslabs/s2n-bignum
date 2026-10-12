(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Almost-Montgomery reduction of arbitrary bignum.                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_amontredc.o";;
 ****)

let bignum_amontredc_mc =
  define_assert_from_elf "bignum_amontredc_mc" "arm/generic/bignum_amontredc.o"
[
  0xb4000980;       (* arm_CBZ X0 (word 304) *)
  0xf940008d;       (* arm_LDR X13 X4 (Immediate_Offset (word 0)) *)
  0xd37ef5a6;       (* arm_LSL X6 X13 (rvalue (word 2)) *)
  0xcb0601a6;       (* arm_SUB X6 X13 X6 *)
  0xd27f00c6;       (* arm_EOR X6 X6 (rvalue (word 2)) *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0x9b061da7;       (* arm_MADD X7 X13 X6 X7 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0x9b0618e6;       (* arm_MADD X6 X7 X6 X6 *)
  0x9b087d07;       (* arm_MUL X7 X8 X8 *)
  0x9b061906;       (* arm_MADD X6 X8 X6 X6 *)
  0x9b077ce8;       (* arm_MUL X8 X7 X7 *)
  0x9b0618e6;       (* arm_MADD X6 X7 X6 X6 *)
  0x9b061906;       (* arm_MADD X6 X8 X6 X6 *)
  0xeb00005f;       (* arm_CMP X2 X0 *)
  0x9a822008;       (* arm_CSEL X8 X0 X2 Condition_CS *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xb4000108;       (* arm_CBZ X8 (word 32) *)
  0xf867786d;       (* arm_LDR X13 X3 (Shiftreg_Offset X7 3) *)
  0xf827782d;       (* arm_STR X13 X1 (Shiftreg_Offset X7 3) *)
  0x910004e7;       (* arm_ADD X7 X7 (rvalue (word 1)) *)
  0xeb0800ff;       (* arm_CMP X7 X8 *)
  0x54ffff83;       (* arm_BCC (word 2097136) *)
  0xeb0000ff;       (* arm_CMP X7 X0 *)
  0x540000a2;       (* arm_BCS (word 20) *)
  0xf827783f;       (* arm_STR XZR X1 (Shiftreg_Offset X7 3) *)
  0x910004e7;       (* arm_ADD X7 X7 (rvalue (word 1)) *)
  0xeb0000ff;       (* arm_CMP X7 X0 *)
  0x54ffffa3;       (* arm_BCC (word 2097140) *)
  0xaa1f03ee;       (* arm_MOV X14 XZR *)
  0xb40005c5;       (* arm_CBZ X5 (word 184) *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xf940002b;       (* arm_LDR X11 X1 (Immediate_Offset (word 0)) *)
  0x9b067d69;       (* arm_MUL X9 X11 X6 *)
  0xf940008d;       (* arm_LDR X13 X4 (Immediate_Offset (word 0)) *)
  0x9b0d7d2c;       (* arm_MUL X12 X9 X13 *)
  0x9bcd7d2a;       (* arm_UMULH X10 X9 X13 *)
  0xab0c016b;       (* arm_ADDS X11 X11 X12 *)
  0xd2800028;       (* arm_MOV X8 (rvalue (word 1)) *)
  0xd100040d;       (* arm_SUB X13 X0 (rvalue (word 1)) *)
  0xb40001ad;       (* arm_CBZ X13 (word 52) *)
  0xf868788d;       (* arm_LDR X13 X4 (Shiftreg_Offset X8 3) *)
  0xf868782b;       (* arm_LDR X11 X1 (Shiftreg_Offset X8 3) *)
  0x9b0d7d2c;       (* arm_MUL X12 X9 X13 *)
  0xba0a016b;       (* arm_ADCS X11 X11 X10 *)
  0x9bcd7d2a;       (* arm_UMULH X10 X9 X13 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0xab0c016b;       (* arm_ADDS X11 X11 X12 *)
  0xd100050c;       (* arm_SUB X12 X8 (rvalue (word 1)) *)
  0xf82c782b;       (* arm_STR X11 X1 (Shiftreg_Offset X12 3) *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xcb00010d;       (* arm_SUB X13 X8 X0 *)
  0xb5fffead;       (* arm_CBNZ X13 (word 2097108) *)
  0xba0e014a;       (* arm_ADCS X10 X10 X14 *)
  0x9a1f03ee;       (* arm_ADC X14 XZR XZR *)
  0x8b070108;       (* arm_ADD X8 X8 X7 *)
  0xeb02011f;       (* arm_CMP X8 X2 *)
  0x54000082;       (* arm_BCS (word 16) *)
  0xf868786d;       (* arm_LDR X13 X3 (Shiftreg_Offset X8 3) *)
  0xab0d014a;       (* arm_ADDS X10 X10 X13 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xd1000408;       (* arm_SUB X8 X0 (rvalue (word 1)) *)
  0xf828782a;       (* arm_STR X10 X1 (Shiftreg_Offset X8 3) *)
  0x910004e7;       (* arm_ADD X7 X7 (rvalue (word 1)) *)
  0xeb0500ff;       (* arm_CMP X7 X5 *)
  0x54fffbe3;       (* arm_BCC (word 2097020) *)
  0xcb0e03ee;       (* arm_NEG X14 X14 *)
  0xeb1f03e8;       (* arm_NEGS X8 XZR *)
  0xf868782d;       (* arm_LDR X13 X1 (Shiftreg_Offset X8 3) *)
  0xf868788b;       (* arm_LDR X11 X4 (Shiftreg_Offset X8 3) *)
  0x8a0e016b;       (* arm_AND X11 X11 X14 *)
  0xfa0b01ad;       (* arm_SBCS X13 X13 X11 *)
  0xf828782d;       (* arm_STR X13 X1 (Shiftreg_Offset X8 3) *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xcb00010d;       (* arm_SUB X13 X8 X0 *)
  0xb5ffff2d;       (* arm_CBNZ X13 (word 2097124) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_AMONTREDC_EXEC = ARM_MK_EXEC_RULE bignum_amontredc_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** This actually works mod 32 but if anything this is more convenient ***)

let WORD_NEGMODINV_SEED_LEMMA_16 = prove
 (`!a x:int64.
        ODD a /\
        word_xor (word_sub (word a) (word_shl (word a) 2)) (word 2) = x
        ==> (a * val x + 1 == 0) (mod 16)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONG; MOD_0] THEN
  TRANS_TAC EQ_TRANS
   `(val(word a:int64) MOD 16 * val(x:int64) MOD 16 + 1) MOD 16` THEN
  REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`] THEN CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    REWRITE_TAC[VAL_MOD; NUMSEG_LT; ARITH_EQ; ARITH]] THEN
  SUBGOAL_THEN `bit 0 (word a:int64)` MP_TAC THENL
   [ASM_REWRITE_TAC[BIT_LSB_WORD];
    EXPAND_TAC "x" THEN POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit 1 (word a:int64)`;`bit 2 (word a:int64)`;`bit 3 (word a:int64)`] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_AMONTREDC_CORRECT = time prove
 (`!k z r x m p a n pc.
        nonoverlapping (word pc,0x134) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val r) (z,8 * val k)) /\
        val p < 2 EXP 61 /\ val r < 2 EXP 61
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_amontredc_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k; z; r; x; m; p] s /\
                  bignum_from_memory (x,val r) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = word(pc + 0x130) /\
                  (ODD n
                   ==> (bignum_from_memory (z,val k) s ==
                        inverse_mod n (2 EXP (64 * val p)) *
                        lowdigits a (val k + val p)) (mod n)))
             (MAYCHANGE [PC; X6; X7; X8; X9; X10; X11; X12; X13; X14] ,,
              MAYCHANGE [memory :> bytes(z,8 * val k)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `nx:num` THEN X_GEN_TAC `x:int64` THEN
  X_GEN_TAC `m:int64` THEN W64_GEN_TAC `p:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  BIGNUM_TERMRANGE_TAC `nx:num` `a:num` THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ODD];
    ALL_TAC] THEN

  (*** Initial word-level modular inverse ***)

  ENSURES_SEQUENCE_TAC `pc + 0x38`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word nx /\
        read X3 s = x /\
        read X4 s = m /\
        read X5 s = word p /\
        bignum_from_memory (x,nx) s = a /\
        bignum_from_memory (m,k) s = n /\
        (ODD n ==> (n * val(read X6 s) + 1 == 0) (mod (2 EXP 64)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `bignum_from_memory(m,k) s0 = highdigits n 0` MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC LAND_CONV[BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[GSYM DIMINDEX_64; WORD_MOD_SIZE] THEN
      REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC] THEN
    ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--5) THEN
    SUBGOAL_THEN `ODD n ==> (n * val (read X6 s5) + 1 == 0) (mod 16)`
    MP_TAC THENL [ASM_SIMP_TAC[WORD_NEGMODINV_SEED_LEMMA_16]; ALL_TAC] THEN
    REABBREV_TAC `x0 = read X6 s5` THEN DISCH_TAC THEN
    ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (6--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG] THEN
    SUBST1_TAC(ARITH_RULE `2 EXP 64 = 16 EXP (2 EXP 4)`) THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    SPEC_TAC(`16`,`e:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUMBER_RULE;
    GHOST_INTRO_TAC `w:num` `\s. val(read X6 s)` THEN
    REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64]] THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  VAL_INT64_TAC `w:num` THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_1)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Initialization of the output buffer ***)

  ENSURES_SEQUENCE_TAC `pc + 0x78`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word nx /\
        read X3 s = x /\
        read X4 s = m /\
        read X5 s = word p /\
        bignum_from_memory (word_add x (word (8 * k)),nx - k) s =
        highdigits a k /\
        bignum_from_memory (m,k) s = n /\
        read X6 s = word w /\
        bignum_from_memory (z,k) s = lowdigits a k /\
        read X14 s = word 0` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `nx = 0` THENL
     [UNDISCH_THEN `nx = 0` SUBST_ALL_TAC THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
       `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
      ENSURES_WHILE_UP_TAC `k:num` `pc + 0x64` `pc + 0x6c`
       `\i s. read X0 s = word k /\
              read X1 s = z /\
              read X2 s = word 0 /\
              read X3 s = x /\
              read X4 s = m /\
              read X5 s = word p /\
              bignum_from_memory (m,k) s = n /\
              read X6 s = word w /\
              read X7 s = word i /\
              bignum_from_memory (z,i) s = 0` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--4) THEN
        ASM_REWRITE_TAC[LE; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL];
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
        ARITH_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--2);
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--3) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[LOWDIGITS_TRIVIAL] THEN
        REWRITE_TAC[LE; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; SUB_0] THEN
        REWRITE_TAC[HIGHDIGITS_TRIVIAL]];
      ALL_TAC] THEN

    (*** Copyloop ***)

    ENSURES_WHILE_UP_TAC `MIN k nx` `pc + 0x48` `pc + 0x54`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = word nx /\
            read X3 s = x /\
            read X4 s = m /\
            read X5 s = word p /\
            bignum_from_memory (m,k) s = n /\
            read X6 s = word w /\
            read X7 s = word i /\
            read X8 s = word(MIN k nx) /\
            bignum_from_memory(word_add x (word(8 * i)),nx - i) s =
            highdigits a i /\
            bignum_from_memory (z,i) s = lowdigits a i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `MIN a b = 0 <=> a = 0 \/ b = 0`];
      ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--4) THEN
      MATCH_MP_TAC(TAUT `q /\ (q ==> p) /\ r ==> p /\ q /\ r`) THEN
      CONJ_TAC THENL [REWRITE_TAC[MIN] THEN MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0] THEN
      REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; HIGHDIGITS_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      DISCH_THEN SUBST1_TAC THEN VAL_INT64_TAC `MIN k nx` THEN
      ASM_REWRITE_TAC[ARITH_RULE `MIN a b = 0 <=> a = 0 \/ b = 0`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `i:num < nx /\ i < k` STRIP_ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
      VAL_INT64_TAC `MIN k nx` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    (*** Now consider the cases again ***)

    ASM_CASES_TAC `k:num <= nx` THENL
     [ASM_SIMP_TAC[ARITH_RULE `k <= nx ==> MIN k nx = k`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
      ASM_SIMP_TAC[ARITH_RULE `nx < k ==> MIN k nx = nx`]] THEN

    (*** Padloop following copyloop ***)

    ENSURES_WHILE_AUP_TAC `nx:num` `k:num` `pc + 0x64` `pc + 0x6c`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = word nx /\
            read X3 s = x /\
            read X4 s = m /\
            read X5 s = word p /\
            bignum_from_memory (m,k) s = n /\
            read X6 s = word w /\
            read X7 s = word i /\
            bignum_from_memory (z,i) s = lowdigits a i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--4) THEN
      ASM_REWRITE_TAC[GSYM NOT_LT];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      SIMP_TAC[VAL_WORD_0; LOWDIGITS_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THEN
      MATCH_MP_TAC(NUM_RING `d = 0 ==> a = e * d + a`) THEN
      MATCH_MP_TAC BIGDIGIT_ZERO THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * nx)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `nx:num <= i` THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--2);
      ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--3) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_SIMP_TAC[ARITH_RULE `nx < k ==> nx - k = 0`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC HIGHDIGITS_ZERO THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * nx)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `nx:num < k` THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** Another semi-degenerate case p = 0, where we're done after init ***)

  ASM_CASES_TAC `p = 0` THENL
   [UNDISCH_THEN `p = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC [1] THEN DISCH_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; INVERSE_MOD_1; EXP; ADD_CLAUSES; CONG_REFL];
    ALL_TAC] THEN

  (*** Setup of the main loop, and corrective ending ***)

  ENSURES_WHILE_UP_TAC `p:num` `pc + 0x80` `pc + 0x100`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X2 s = word nx /\
          read X3 s = x /\
          read X4 s = m /\
          read X5 s = word p /\
          read X6 s = word w /\
          read X7 s = word i /\
          bignum_from_memory (m,k) s = n /\
          bignum_from_memory(word_add x (word(8 * (k + i))),nx - (k + i)) s =
          highdigits a (k + i) /\
          ?q r. q < 2 EXP (64 * i) /\ r < 2 EXP (64 * i) /\
                2 EXP (64 * i) *
                (2 EXP (64 * k) * val(read X14 s) +
                 bignum_from_memory(z,k) s) +
                r =
                q * n + lowdigits a (k + i) /\
                (ODD n ==> r = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; VAL_WORD_0] THEN
    REPEAT(EXISTS_TAC `0`) THEN ARITH_TAC;

    ALL_TAC; (*** This is the main loop invariant: save for later ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** This is the corrective subtraction part.... ***)

    GHOST_INTRO_TAC `cout:num` `\s. val(read X14 s)` THEN
    GHOST_INTRO_TAC `mm:num` `bignum_from_memory(z,k)` THEN
    BIGNUM_TERMRANGE_TAC `k:num` `mm:num` THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:num`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `cout < 2` MP_TAC THENL
     [SUBGOAL_THEN `q * n + lowdigits a (k + p) < 2 EXP (64 * (k + p)) * 2`
      MP_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `x < e /\ y < e ==> x + y < e * 2`) THEN
        REWRITE_TAC[LOWDIGITS_BOUND] THEN
        REWRITE_TAC[ARITH_RULE `64 * (k + p) = 64 * p + 64 * k`] THEN
        ASM_SIMP_TAC[LT_MULT2; EXP_ADD];
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
        REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
        REWRITE_TAC[ARITH_RULE `64 * k + 64 * p = 64 * (p + k)`] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
         `a + b:num < c ==> a < c`)) THEN
        REWRITE_TAC[GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
        REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
      GEN_REWRITE_TAC LAND_CONV [NUM_AS_BITVAL_ALT]] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:bool` SUBST_ALL_TAC) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN
    ENSURES_WHILE_UP_TAC `k:num` `pc + 0x110` `pc + 0x128`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X4 s = m /\
            read X14 s = word_neg(word(bitval c)) /\
            read X8 s = word i /\
            bignum_from_memory (word_add z (word(8 * i)),k - i) s =
            highdigits mm i /\
            bignum_from_memory (word_add m (word(8 * i)),k - i) s =
            highdigits n i /\
            &(bignum_from_memory(z,i) s):real =
            &2 pow (64 * i) * &(bitval(~read CF s)) +
            &(lowdigits mm i) - &(bitval c) * &(lowdigits n i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUB_LZERO; SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; BITVAL_CLAUSES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTREDC_EXEC [4] (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM WORD_ADD] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[WORD_ADD; WORD_NEG_NEG; VAL_WORD_BITVAL; WORD_BITVAL_EQ_0;
                  LOWDIGITS_CLAUSES; WORD_NEG_EQ_0; BITVAL_BOUND; NOT_LT] THEN
      REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_REWRITE_TAC[NOT_LT] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND; VAL_WORD_0;
               BITVAL_CLAUSES; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
      REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RING;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      DISCH_TAC THEN UNDISCH_TAC `ODD n ==> r = 0` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])] THEN
   FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
     `e * x:num = q * n + ab
      ==> (i * e == 1) (mod n) /\ (y == x) (mod n)
          ==> (y == i * ab) (mod n)`)) THEN
   ASM_REWRITE_TAC[INVERSE_MOD_LMUL_EQ; COPRIME_REXP; COPRIME_2] THEN
   REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
   MATCH_MP_TAC(INTEGER_RULE
    `x = (e - n) * c + m ==> (x:int == e * c + m) (mod n)`) THEN
   MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow (64 * k)` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC(INT_ARITH
      `&0 <= x /\ x < e /\ &0 <= y /\ y < e ==> abs(x - y:int) < e`) THEN
     ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; INT_OF_NUM_SUB; LT_IMP_LE; LE_0] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND] THEN
     UNDISCH_TAC
      `2 EXP (64 * p) * (2 EXP (64 * k) * bitval c + mm) =
      q * n + lowdigits a (k + p)` THEN
     ASM_CASES_TAC `c:bool` THEN
     ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; BITVAL_CLAUSES] THEN
     ASM_SIMP_TAC[ARITH_RULE `n:num < e ==> ((e - n) + m < e <=> m < n)`] THEN
     DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
      `e * (d + m):num = qn + ab ==> ab < e * d ==> e * m < qn`)) THEN
     REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM EXP_ADD)] THEN
     REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; LOWDIGITS_BOUND] THEN
     REWRITE_TAC[GSYM NOT_LE; CONTRAPOS_THM] THEN
     ASM_SIMP_TAC[LE_MULT2; LT_IMP_LE];
     REWRITE_TAC[INTEGER_RULE
      `(z:int == (e - n) * c + m) (mod e) <=> (z + n * c == m) (mod e)`] THEN
     REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
     REWRITE_TAC[REAL_CONGRUENCE; EXP_EQ_0; ARITH_EQ] THEN
     ASM_SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES; LOWDIGITS_SELF] THEN
     REWRITE_TAC[real_sub; GSYM REAL_ADD_ASSOC] THEN
     REWRITE_TAC[REAL_FIELD
      `(&2 pow n * x + y) / &2 pow n = x + y / &2 pow n`] THEN
     REAL_INTEGER_TAC]] THEN

  (*** Start on the main outer loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cout:num` `\s. val(read X14 s)` THEN
  GHOST_INTRO_TAC `z1:num` `bignum_from_memory(z,k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z1:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` (X_CHOOSE_THEN `r:num`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  (*** The initial prelude of the Montgomery reduction ***)

  ABBREV_TAC `q0 = (w * z1) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `q0 < 2 EXP 64 /\ val(word q0:int64) = q0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL];
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xa0`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word nx /\
        read X3 s = x /\
        read X4 s = m /\
        read X5 s = word p /\
        read X6 s = word w /\
        read X7 s = word i /\
        bignum_from_memory (m,k) s = n /\
        bignum_from_memory (word_add x (word (8 * (k + i))),nx - (k + i)) s =
        highdigits a (k + i) /\
        read X14 s = word cout /\
        bignum_from_memory (z,k) s = z1 /\
        read X9 s = word q0 /\
        read X8 s = word 1 /\
        read X13 s = word(k - 1) /\
        2 EXP 64 * (bitval(read CF s) + val(read X10 s)) + val(read X11 s) =
        q0 * bigdigit n 0 + bigdigit z1 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(m,k) s0 = highdigits n 0 /\
      bignum_from_memory(z,k) s0 = highdigits z1 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_AMONTREDC_EXEC [4;6] (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
      ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[ADD_CLAUSES; DIMINDEX_64; VAL_WORD] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM];
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Break at "montend" to share the end reasoning ***)

  GHOST_INTRO_TAC `r0:num` `\s. val(read X11 s)` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  ENSURES_SEQUENCE_TAC `pc + 0xd4`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word nx /\
        read X3 s = x /\
        read X4 s = m /\
        read X5 s = word p /\
        read X6 s = word w /\
        read X7 s = word i /\
        bignum_from_memory (m,k) s = n /\
        bignum_from_memory (word_add x (word (8 * (k + i))),nx - (k + i)) s =
        highdigits a (k + i) /\
        read X14 s = word cout /\
        read X9 s = word q0 /\
        read X8 s = word k /\
        2 EXP (64 * k) * (bitval(read CF s) + val(read X10 s)) +
        2 EXP 64 * bignum_from_memory (z,k - 1) s +
        r0 =
        lowdigits z1 k + q0 * lowdigits n k` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      REWRITE_TAC[LOWDIGITS_1] THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** The Montgomery reduction loop ***)

    VAL_INT64_TAC `k - 1` THEN

    ENSURES_WHILE_AUP_TAC `1` `k:num` `pc + 0xa4` `pc + 0xcc`
     `\j s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = word nx /\
            read X3 s = x /\
            read X4 s = m /\
            read X5 s = word p /\
            read X6 s = word w /\
            read X7 s = word i /\
            bignum_from_memory (m,k) s = n /\
            bignum_from_memory
             (word_add x (word (8 * (k + i))),nx - (k + i)) s =
            highdigits a (k + i) /\
            read X14 s = word cout /\
            read X9 s = word q0 /\
            read X8 s = word j /\
            bignum_from_memory(word_add z (word (8 * j)),k - j) s =
            highdigits z1 j /\
            bignum_from_memory(word_add m (word (8 * j)),k - j) s =
            highdigits n j /\
            2 EXP (64 * j) * (bitval(read CF s) + val(read X10 s)) +
            2 EXP 64 * bignum_from_memory(z,j-1) s + r0 =
            lowdigits z1 j + q0 * lowdigits n j` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0 \/ k = 1)`];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k <= 1 <=> k = 0 \/ k = 1`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      ASM_REWRITE_TAC[GSYM highdigits; BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LOWDIGITS_1] THEN ARITH_TAC;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`j:num`; `j - 1`] THEN
      SUBGOAL_THEN `word_sub (word j) (word 1):int64 = word(j - 1)`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read X10` THEN
      MP_TAC(GENL [`x:int64`; `a:num`]
       (ISPECL [`x:int64`; `k - j:num`; `a:num`; `j:num`]
          BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      UNDISCH_THEN `val(word q0:int64) = q0` (K ALL_TAC) THEN
      SUBGOAL_THEN `nonoverlapping (word_add z (word (8 * (j - 1))):int64,8)
                                   (word_add x (word (8 * (k + i))),
                                    8 * (nx - (k + i)))`
      MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
       [ASM_CASES_TAC `nx - (k + i) = 0` THEN
        ASM_SIMP_TAC[MULT_CLAUSES; NONOVERLAPPING_MODULO_TRIVIAL] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SUB_EQ_0; NOT_LE]) THEN
        FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
         [ALL_TAC;
          GEN_REWRITE_TAC LAND_CONV [NONOVERLAPPING_MODULO_SYM] THEN
          MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
              NONOVERLAPPING_MODULO_SUBREGIONS) THEN
          CONJ_TAC THEN CONTAINED_TAC] THEN
        SUBGOAL_THEN
         `word_add z (word (8 * (k + i))):int64 =
          word_add (word_add z (word(8 * (j - 1))))
                   (word(8 + 8 * ((k + i) - j)))`
        SUBST1_TAC THENL
         [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
          NONOVERLAPPING_TAC];
        DISCH_TAC] THEN
      ABBREV_TAC `j' = j - 1` THEN
      SUBGOAL_THEN `j = j' + 1` SUBST_ALL_TAC THENL
       [EXPAND_TAC "j'" THEN UNDISCH_TAC `1 <= j` THEN ARITH_TAC;
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(j' + 1) + 1 = j' + 2`]) THEN
      REWRITE_TAC[ARITH_RULE `(j' + 1) + 1 = j' + 2`] THEN
      ARM_ACCSTEPS_TAC BIGNUM_AMONTREDC_EXEC [3;4;6;7] (1--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(n + 2) - 1 = n + 1`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `j' + 2 = (j' + 1) + 1` MP_TAC THENL
       [ARITH_TAC; DISCH_THEN SUBST_ALL_TAC] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ONCE_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      GEN_REWRITE_TAC RAND_CONV
       [ARITH_RULE `(e * d1 + d0) + c * (e * a1 + a0):num =
                    e * (c * a1 + d1) + d0 + c * a0`] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (j + 1) = 64 * j + 64`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      GEN_REWRITE_TAC LAND_CONV
         [TAUT `p /\ q /\ r /\ s <=> p /\ r /\ q /\ s`] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC REAL_RING;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MAP_EVERY VAL_INT64_TAC [`j:num`; `j - 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_AMONTREDC_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0]];

    ALL_TAC] THEN

  SUBGOAL_THEN `cout < 2` MP_TAC THENL
   [SUBGOAL_THEN `q * n + lowdigits a (k + i) < 2 EXP (64 * (k + i)) * 2`
    MP_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `x < e /\ y < e ==> x + y < e * 2`) THEN
      REWRITE_TAC[LOWDIGITS_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `64 * (k + p) = 64 * p + 64 * k`] THEN
      ASM_SIMP_TAC[LT_MULT2; EXP_ADD];
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
      REWRITE_TAC[ARITH_RULE `64 * k + 64 * p = 64 * (p + k)`] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `a + b:num < c ==> a < c`)) THEN
      REWRITE_TAC[GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    GEN_REWRITE_TAC LAND_CONV [NUM_AS_BITVAL_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `tc:bool` SUBST_ALL_TAC)] THEN

  (*** Just case split over the "off the end" and share remainder ***)

  ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GHOST_INTRO_TAC `hin:int64` `read X10` THEN
  VAL_INT64_TAC `k - 1` THEN
  SUBGOAL_THEN `word_sub (word k) (word 1):int64 = word(k - 1)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`];
    ALL_TAC] THEN
  VAL_INT64_TAC `k + i:num` THEN
  MP_TAC(WORD_RULE `word_add (word k) (word i):int64 = word(k + i)`) THEN
  DISCH_TAC THEN

  ASM_CASES_TAC `nx:num <= k + i` THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC BIGNUM_AMONTREDC_EXEC [1] (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `nx <= k + i ==> nx - (k + i + 1) = 0`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN CONV_TAC SYM_CONV THEN
       REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
       MATCH_MP_TAC HIGHDIGITS_ZERO THEN
       TRANS_TAC LTE_TRANS `2 EXP (64 * nx)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `nx:num <= k + i` THEN
      ARITH_TAC;
      ALL_TAC];

    SUBGOAL_THEN `nonoverlapping (word_add z (word (8 * (k - 1))):int64,8)
                                 (word_add x (word (8 * (k + i))),
                                  8 * (nx - (k + i)))`
    MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
       [ALL_TAC;
        GEN_REWRITE_TAC LAND_CONV [NONOVERLAPPING_MODULO_SYM] THEN
        MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
            NONOVERLAPPING_MODULO_SUBREGIONS) THEN
        CONJ_TAC THEN CONTAINED_TAC] THEN
      SUBGOAL_THEN
       `word_add z (word (8 * (k + i))):int64 =
        word_add (word_add z (word(8 * (k - 1))))
                 (word(8 + 8 * ((k + i) - k)))`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
        NONOVERLAPPING_TAC];
      DISCH_TAC] THEN

    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[SUB_EQ_0] THEN
    REWRITE_TAC[ARITH_RULE `n - (k + i) - 1 = n - (k + i + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `(k + i) + 1 = k + i + 1`] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC BIGNUM_AMONTREDC_EXEC [1;7;8] (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]] THEN

  (MAP_EVERY EXISTS_TAC
    [`2 EXP (64 * i) * q0 + q`;
     `2 EXP (64 * i) * r0 + r`] THEN
   GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
    [REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
     CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE
      `q1 < e /\ q0 < ee /\ (q1 < e ==> (q1 + 1) * ee <= e * ee)
       ==> ee * q1 + q0 < ee * e`) THEN
     ASM_REWRITE_TAC[LE_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ] THEN
     ASM_REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`];
     ALL_TAC] THEN
   CONJ_TAC THENL
    [ALL_TAC;
     DISCH_THEN(fun th ->
       REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th))) THEN
     ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     ASM_REWRITE_TAC[EXP_LT_0; ARITH_EQ] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
      `ee * x + e * y + r = z
       ==> e divides ee /\ (z == 0) (mod e)
           ==> (r == 0) (mod e)`)) THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
       UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
       UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM)] THEN
     REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
     REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
      `(n * w + 1 == 0) (mod e) ==> (z + (w * z) * n == 0) (mod e)`) THEN
     ASM_REWRITE_TAC[]] THEN
   SUBGOAL_THEN `8 * k = 8 * ((k - 1) + 1)` SUBST1_TAC THENL
    [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES]] THEN
   REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
   ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
   REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD] THEN
   REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
   SUBGOAL_THEN `(i + 1) + (k - 1) = i + k` SUBST1_TAC THENL
    [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES] THEN
   REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE `k + i + 1 = (k + i) + 1`]) THEN
  REWRITE_TAC[ARITH_RULE `64 * (k + i) = 64 * k + 64 * i`; EXP_ADD] THENL
   [REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
    SUBGOAL_THEN `bigdigit a (k + i) = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC BIGDIGIT_ZERO THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * nx)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `nx:num <= k + i` THEN
      ARITH_TAC;
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `2 EXP (64 * k) * x + y = z`) o concl))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; VAL_WORD_BITVAL; ADD_CLAUSES] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC REAL_RING;

    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check
     (can (term_match [] `2 EXP (64 * k) * x + y = z`) o concl))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; VAL_WORD_BITVAL; ADD_CLAUSES;
                 BIGDIGIT_BOUND] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC REAL_RING]);;

let BIGNUM_AMONTREDC_SUBROUTINE_CORRECT = time prove
 (`!k z r x m p a n pc returnaddress.
        nonoverlapping (word pc,0x134) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val r) (z,8 * val k)) /\
        val p < 2 EXP 61 /\ val r < 2 EXP 61
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_amontredc_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k; z; r; x; m; p] s /\
                  bignum_from_memory (x,val r) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = returnaddress /\
                  (ODD n
                   ==> (bignum_from_memory (z,val k) s ==
                        inverse_mod n (2 EXP (64 * val p)) *
                        lowdigits a (val k + val p)) (mod n)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC
    BIGNUM_AMONTREDC_EXEC BIGNUM_AMONTREDC_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* The main loop runs p times, so p is public as well as the sizes. *)

let amontredc_full_spec,amontredc_public_vars =
  mk_safety_spec ~extra_public_vars:[`p:int64`] ~keep_maychanges:false
    (assoc "bignum_amontredc" subroutine_signatures)
    BIGNUM_AMONTREDC_SUBROUTINE_CORRECT BIGNUM_AMONTREDC_EXEC;;

(* The trace witness in the proof follows the control flow of the code, which
   is that of bignum_montredc without the compare loop:
   - k = 0: CBZ X0 at 0x00 jumps to the RET at 0x130.
   - Prologue 0x00-0x44 and buffer initialization 0x48-0x70 as in
     bignum_montredc: r = 0 zero-fills k words (padA), k <= r copies k words
     (copyB) and 0 < r < k copies r words and zero-fills k - r words (copyC,
     padC).
   - Main nest: CBZ X5 at 0x78 jumps to the RET at 0x130 if p = 0; else the
     outer loop 0x80-0x104 runs p times. Its body is oprol 0x80-0xa0, whose
     CBZ X13 at 0xa0 skips the inner loop if k = 1, the inner loop 0xa4-0xd0
     (12 instructions) over k - 1 words and oepil 0xd4-0x104, which loads
     x[k + i] only if k + i < r (oepilL, else oepilN by the BCS at 0xe4).
   - Correction 0x108-0x130: the mask by NEG at 0x108, NEGS at 0x10c, the
     masked-subtract loop 0x110-0x12c over k words and the RET at 0x130.
   The case k = 1 has its own arm, as its outer loop has no inner loop. All
   accesses use Shiftreg_Offset X_ 3, i.e. word_shl (word i) 3 = word(8 * i). *)

(* Discharge a leg whose postcondition trace is APPEND <new events> <carried
   trace>, where the carried trace contains unresolved f_ev metavariables:
   bind the f_ev of the leg with FULL_UNIFY_F_EVENTS_TAC, and split the
   memaccess_inbounds goal with MEMACCESS_INBOUNDS_APPEND into the new
   (concrete) part and the carried part, which is folded back to the
   assumption about e2 after normalizing val(word k) = k and APPEND_ASSOC. *)

let BIGNUM_AMONTREDC_CARRIED_DISCHARGE_TAC =
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC] THEN
  REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
  GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
  CONJ_TAC THENL
   [DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word k:int64) = k`]) THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
    ((W(fun (asl,w) ->
       let e2th = snd(List.find (fun (_,th) -> let c=concl th in
           is_eq c && (try fst(dest_var(lhs c))="e2" with _->false)) asl) in
       GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV) [GSYM e2th]) THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC)
     ORELSE DISCHARGE_MEMACCESS_INBOUNDS_TAC)];;

(* MIN n 0 = 0, used after the substitution r := 0 in the r = 0 arm. *)

let BIGNUM_AMONTREDC_MIN_N0 = prove
 (`!n:num. MIN n 0 = 0`, GEN_TAC THEN REWRITE_TAC[MIN; LE] THEN ARITH_TAC);;

(* The trace shape expected by ENSURES_EVENTS_WHILE_UP2_TAC for a loop with
   empty prologue and epilogue, and the reassociation of the postcondition
   trace after ENUMERATEL_ADD1 in a loop body. *)

let BIGNUM_AMONTREDC_WHILE_WRAP = prove
 (`!n f b:(uarch_event)list.
     APPEND (ENUMERATEL n f) b =
     APPEND (APPEND [] (APPEND (ENUMERATEL n f) [])) b`,
  REWRITE_TAC[APPEND; APPEND_NIL]);;

let BIGNUM_AMONTREDC_BODY_REASSOC = METIS[APPEND_ASSOC]
  `(exists e2. P e2 /\ e2 = APPEND (APPEND fresh enumc) tail /\ Q e2) <=>
   (exists e2. P e2 /\ e2 = APPEND fresh (APPEND enumc tail:(uarch_event)list) /\
               Q e2)`;;

(* Close a leg that adds no events, such as the empty pre- or post-leg of a
   loop: after the rewrites ths (e.g. reducing the invariant to iteration 0),
   simulate the steps, apply asm_tac and take the carried trace e2 as the
   witness. *)

let BIGNUM_AMONTREDC_NOEVENT_LEG_TAC (ths:thm list) (asm_tac:tactic) steps =
  REWRITE_TAC ths THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
    BIGNUM_AMONTREDC_EXEC steps THEN
  asm_tac THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_eq c && (try fst(dest_var(lhs c))="e2" with _ -> false)
    then EXISTS_TAC(lhs c) else NO_TAC) THEN
  ASM_REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL; GSYM APPEND_ASSOC];;

let BIGNUM_AMONTREDC_PRE_LEG_TAC =
  BIGNUM_AMONTREDC_NOEVENT_LEG_TAC
    [SUB_0; MULT_CLAUSES; ADD_0; ENUMERATEL; CONJUNCT1 APPEND; APPEND_NIL]
    (ASM_REWRITE_TAC[]);;

let BIGNUM_AMONTREDC_POST_LEG_TAC =
  BIGNUM_AMONTREDC_NOEVENT_LEG_TAC [CONJUNCT1 APPEND; APPEND_NIL] ALL_TAC [];;

(* Close the empty post-leg of a loop of the buffer initialization. The
   carried assumptions are normalized to the forms in the goal and used
   directly: rewriting with all assumptions would also expand e2 in the
   memaccess_inbounds conjunct with the assumption e2 = ..., which the
   carried memaccess_inbounds assumption about e2 then no longer matches. *)

let BIGNUM_AMONTREDC_INIT_POST_LEG_TAC =
  REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
    BIGNUM_AMONTREDC_EXEC [] THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 APPEND; APPEND_NIL; GSYM APPEND_ASSOC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word k:int64) = k`]) THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_eq c && (try fst(dest_var(lhs c))="e2" with _ -> false)
    then EXISTS_TAC(lhs c) else NO_TAC) THEN
  REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM MATCH_ACCEPT_TAC ORELSE ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM MATCH_ACCEPT_TAC ORELSE
    ASM_REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL; GSYM APPEND_ASSOC];
    FIRST_ASSUM MATCH_ACCEPT_TAC];;

(* Close the leading conjuncts of a postcondition other than its trace part,
   each with the first of the tactics tacs that applies. *)

let BIGNUM_AMONTREDC_PEEL_TAC (tacs:tactic list) =
  REPEAT(W(fun (asl,w) -> if is_conj w && not(is_exists w)
    then CONJ_TAC THENL [FIRST tacs; ALL_TAC]
    else NO_TAC));;

(* Prove the equivalence eq for the loop-back condition of the steps just
   simulated by tac, and rewrite the assumptions and the goal with it. *)

let BIGNUM_AMONTREDC_BACKEDGE_TAC (eq:term) (tac:tactic) =
  SUBGOAL_THEN eq ASSUME_TAC THENL [tac; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME eq]) THEN REWRITE_TAC[ASSUME eq];;

(* The copy loop 0x48-0x58 of the buffer initialization over n = MIN k r
   words, whose pre-leg is the prologue. *)

let BIGNUM_AMONTREDC_COPY_LOOP_TAC (n:term) =
  ENSURES_EVENTS_WHILE_UP2_TAC n `pc + 0x48` `pc + 0x5c`
   `\j s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
          read X4 s = m /\ read X5 s = word p /\ read X7 s = word j /\
          read X8 s = word(MIN k r) /\ read X30 s = returnaddress` THEN
  REWRITE_TAC[LT_NZ] THEN
  CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* pre-leg: the prologue (17 steps) and CBZ X8 not taken *)
    REWRITE_TAC[SUB_0; MULT_CLAUSES; ADD_0; ENUMERATEL; CONJUNCT1 APPEND; APPEND_NIL] THEN
    SUBGOAL_THEN `~(val(word(MIN k r):int64) = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_AMONTREDC_EXEC (1--18) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    BIGNUM_AMONTREDC_PEEL_TAC
      [REFL_TAC; CONV_TAC WORD_RULE; ASM_REWRITE_TAC[]] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* body: LDR x[j], STR z[j], ADD, CMP, BCC (5 steps) *)
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `j:num < k /\ j < r` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
     [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_shl (word j:int64) 3 = word(8 * j)` ASSUME_TAC THENL
     [REWRITE_TAC[WORD_SHL_WORD] THEN REWRITE_TAC[ARITH_RULE `2 EXP 3 * m = 8 * m`] THEN
      CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `8 * j + 8 <= 8 * k /\ 8 * j + 8 <= 8 * r` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_AMONTREDC_EXEC (1--5) THEN
    SUBGOAL_THEN `val(word_add (word j) (word 1):int64) = j + 1` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word(MIN k r):int64) = MIN k r` ASSUME_TAC THENL
     [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    BIGNUM_AMONTREDC_PEEL_TAC
      [REFL_TAC;
       ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN REWRITE_TAC[];
       CONV_TAC WORD_RULE; ASM_REWRITE_TAC[]] THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV)))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    BIGNUM_AMONTREDC_INIT_POST_LEG_TAC];;

let BIGNUM_AMONTREDC_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e k z r x m p pc returnaddress.
           nonoverlapping (word pc,308) (z,8 * val k) /\
           nonoverlapping (m,8 * val k) (z,8 * val k) /\
           (x = z \/ nonoverlapping (x,8 * val r) (z,8 * val k)) /\
           val p < 2 EXP 61 /\
           val r < 2 EXP 61
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) bignum_amontredc_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [k; z; r; x; m; p] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x m z k r p pc returnaddress /\
                         memaccess_inbounds e2
                         [x,val r * 8; m,val k * 8; z,val k * 8]
                         [z,val k * 8]))
               (\s s'. true)`,
  ASSERT_CONCL_TAC amontredc_full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (m:int64) (z:int64) (k:int64) (r:int64) (p:int64) (pc:num) (returnaddress:int64).
      if val k = 0 then f_ev_k0 x m z k r p pc returnaddress
      else if val k = 1 then
        APPEND
          (if val p = 0 then f_ev1_p0tail x m z k r p pc returnaddress
           else APPEND (f_ev1_tail x m z k r p pc returnaddress)
                  (APPEND
                    (ENUMERATEL (val p)
                      (\i. if 1 + i < val r
                           then f_ev1_bodyL x m z k r p pc returnaddress i
                           else f_ev1_bodyN x m z k r p pc returnaddress i))
                    (f_ev1_mainpre x m z k r p pc returnaddress)))
          (if val r = 0 then f_ev1_startA x m z k r p pc returnaddress
           else f_ev1_startB x m z k r p pc returnaddress)
      else
        APPEND
          (if val p = 0 then f_ev_p0tail x m z k r p pc returnaddress
           else APPEND (f_ev_ret x m z k r p pc returnaddress)
                  (APPEND
                    (ENUMERATEL (val k) (\j. f_ev_msub x m z k r p pc returnaddress j))
                    (APPEND
                      (ENUMERATEL (val p)
                        (\i. APPEND
                               (APPEND
                                 (if val k + i < val r
                                  then f_ev_oepilL x m z k r p pc returnaddress i
                                  else f_ev_oepilN x m z k r p pc returnaddress i)
                                 (ENUMERATEL (val k - 1)
                                   (\j. f_ev_inner x m z k r p pc returnaddress i j)))
                               (f_ev_oprol x m z k r p pc returnaddress i)))
                      (f_ev_mainpre x m z k r p pc returnaddress))))
          (if val r = 0 then
             APPEND (ENUMERATEL (val k) (\j. f_ev_padA x m z k r p pc returnaddress j))
                    (f_ev_padApre x m z k r p pc returnaddress)
           else if val k <= val r then
             APPEND (f_ev_copyBpost x m z k r p pc returnaddress)
               (APPEND (ENUMERATEL (val k) (\j. f_ev_copyB x m z k r p pc returnaddress j))
                       (f_ev_copyBpre x m z k r p pc returnaddress))
           else
             APPEND (ENUMERATEL (val k - val r) (\j. f_ev_padC x m z k r p pc returnaddress j))
               (APPEND (f_ev_padCpre x m z k r p pc returnaddress)
                 (APPEND (ENUMERATEL (val r) (\j. f_ev_copyC x m z k r p pc returnaddress j))
                         (f_ev_copyCpre x m z k r p pc returnaddress))))
      :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC (* e *) THEN
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `r:num` THEN X_GEN_TAC `x:int64` THEN
  X_GEN_TAC `m:int64` THEN W64_GEN_TAC `p:num` THEN
  MAP_EVERY X_GEN_TAC [`pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** k=0: CBZ@0x00 -> RET@0x130. 2 steps ***)
  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_AMONTREDC_EXEC (1--2) THEN
    CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `8 * k < 2 EXP 64` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] NONOVERLAPPING_IMP_SMALL_2)) THEN
    ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN

  (*** k=1 arm: inner loop skipped (CBZ X13@0xa0 taken, X13=k-1=0). bufinit: r=0 -> 22 steps
       (startA); r>=1 -> MIN(1,r)=1, copy 1 iter, BCS taken: 25 steps (startB). Then p=0: MOV X14,
       CBZ X5 taken -> RET@0x130 (3 steps); p>0: outer WHILE over p with straight-line body
       (oprol 9 + oepil 13/10), then the corrective for k=1: NEG,NEGS,msub-iter(8),RET = 11 steps. ***)
  ASM_CASES_TAC `k = 1` THENL
   [ASM_REWRITE_TAC[] THEN
    (* SEQUENCE 0x74 at bufinit end: e2 = APPEND rest st *)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x74`
     `\s. read X0 s = word 1 /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
          read X4 s = m /\ read X5 s = word p /\ read X30 s = returnaddress` THEN
    CONJ_TAC THENL
     [(* startA/B *)
      ASM_CASES_TAC `r = 0` THENL
       [(* startA: 22 steps. CBZ X8 taken (MIN(1,0)=0); zerofill 1 iter. *)
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(if val(word 1:int64) <= val(word 0:int64) then word 1 else word 0):int64 = word 0`
        ASSUME_TAC THENL
         [REWRITE_TAC[VAL_WORD_0; VAL_WORD_1] THEN
          CONV_TAC(ONCE_DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
          BIGNUM_AMONTREDC_EXEC (1--22) THEN
        CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
        (* startB: 25 steps. r>=1: MIN(1,r)=1, copy 1 iter, CMP/BCS taken. *)
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `0 < r /\ 1 <= r /\ 8 <= 8 * r` STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(if val(word 1:int64) <= val(word r:int64) then word 1 else word r):int64 = word 1`
        ASSUME_TAC THENL
         [ASM_REWRITE_TAC[VAL_WORD_1] THEN
          COND_CASES_TAC THEN REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
          ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
          BIGNUM_AMONTREDC_EXEC (1--25) THEN
        CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `p = 0` THENL
     [(* p=0: MOV X14, CBZ X5 taken -> RET@0x130. 3 steps. *)
      ASM_REWRITE_TAC[] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
        BIGNUM_AMONTREDC_EXEC (1--3) THEN
      BIGNUM_AMONTREDC_CARRIED_DISCHARGE_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(val(word p:int64) = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    (* main nest for k=1 then tail. reassoc to tl++(mn++st); SEQUENCE 0x108. *)
    REWRITE_TAC[METIS[APPEND_ASSOC]
      `(exists e2. P e2 /\ e2 = APPEND (APPEND tl mn) st /\ Q e2)
       <=> (exists e2. P e2 /\ e2 = APPEND tl (APPEND mn st) /\ Q e2)`] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x108`
     `\s. read X0 s = word 1 /\ read X1 s = z /\ read X4 s = m /\ read X30 s = returnaddress` THEN
    CONJ_TAC THENL
     [(* main nest k=1 *)
      (* mainpre SEQUENCE 0x80: 3 steps *)
      REWRITE_TAC[METIS[APPEND_ASSOC]
        `(exists e2. P e2 /\ e2 = APPEND (APPEND enum mainpre) carr /\ Q e2)
         <=> (exists e2. P e2 /\ e2 = APPEND enum (APPEND mainpre carr) /\ Q e2)`] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x80`
       `\s. read X0 s = word 1 /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
            read X4 s = m /\ read X5 s = word p /\ read X7 s = word 0 /\ read X30 s = returnaddress` THEN
      CONJ_TAC THENL
       [ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
          BIGNUM_AMONTREDC_EXEC (1--3) THEN
        BIGNUM_AMONTREDC_CARRIED_DISCHARGE_TAC;
        ALL_TAC] THEN
      (* outer WHILE_UP2 p 0x80/0x108 with straight-line body *)
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV)
        [BIGNUM_AMONTREDC_WHILE_WRAP] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `p:num` `pc + 0x80` `pc + 0x108`
       `\i s. read X0 s = word 1 /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
              read X4 s = m /\ read X5 s = word p /\ read X7 s = word i /\ read X30 s = returnaddress` THEN
      REWRITE_TAC[LT_NZ] THEN
      CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [(* pre-leg 0-step *)
        BIGNUM_AMONTREDC_PRE_LEG_TAC [];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [(* body i: oprol 9 (CBZ taken) + oepil 13/10 by 1+i<r *)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
        REWRITE_TAC[ENUMERATEL_ADD1] THEN
        REWRITE_TAC[BIGNUM_AMONTREDC_BODY_REASSOC] THEN
        SUBGOAL_THEN `1 + i < 2 EXP 64 /\ val(word i:int64) = i /\ val(word(1 + i):int64) = 1 + i`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THEN TRY (IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]) THEN
          SIMPLE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `word_add (word 1:int64) (word i) = word(1 + i)` ASSUME_TAC THENL
         [CONV_TAC WORD_RULE; ALL_TAC] THEN
        SUBGOAL_THEN `word_sub (word 1:int64) (word 1) = word 0` ASSUME_TAC THENL
         [CONV_TAC WORD_RULE; ALL_TAC] THEN
        SUBGOAL_THEN `word_add (word i:int64) (word 1) = word(i + 1)` ASSUME_TAC THENL
         [CONV_TAC WORD_RULE; ALL_TAC] THEN
        SUBGOAL_THEN `val(word(i + 1):int64) = i + 1` ASSUME_TAC THENL
         [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `word_shl (word 0:int64) 3 = word(8 * 0)` ASSUME_TAC THENL
         [CONV_TAC WORD_RULE; ALL_TAC] THEN
        ASM_CASES_TAC `1 + i < r` THENL
         [(* bodyL: with x[1+i] load. 22 steps *)
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `word_shl (word(1 + i):int64) 3 = word(8 * (1 + i))` ASSUME_TAC THENL
           [REWRITE_TAC[WORD_SHL_WORD] THEN REWRITE_TAC[ARITH_RULE `2 EXP 3 * m = 8 * m`] THEN
            CONV_TAC WORD_RULE; ALL_TAC] THEN
          SUBGOAL_THEN `8 * (1 + i) + 8 <= 8 * r` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `(val(word r:int64) <= val(word(1 + i):int64)) = F` ASSUME_TAC THENL
           [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `~(r <= 1 + i)` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
            BIGNUM_AMONTREDC_EXEC (1--22) THEN
          BIGNUM_AMONTREDC_BACKEDGE_TAC
            `(val(word(i + 1):int64) < val(word p:int64)) <=> (i + 1 < p)`
            (ASM_REWRITE_TAC[]) THEN
          BIGNUM_AMONTREDC_PEEL_TAC
            [COND_CASES_TAC THEN REWRITE_TAC[]; CONV_TAC WORD_RULE; ASM_REWRITE_TAC[]] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;
          (* bodyN: skip load. 19 steps *)
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `(val(word r:int64) <= val(word(1 + i):int64)) = T` ASSUME_TAC THENL
           [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `r <= 1 + i` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
            BIGNUM_AMONTREDC_EXEC (1--19) THEN
          BIGNUM_AMONTREDC_BACKEDGE_TAC
            `(val(word(i + 1):int64) < val(word p:int64)) <=> (i + 1 < p)`
            (ASM_REWRITE_TAC[]) THEN
          BIGNUM_AMONTREDC_PEEL_TAC
            [COND_CASES_TAC THEN REWRITE_TAC[]; CONV_TAC WORD_RULE; ASM_REWRITE_TAC[]] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC];
        (* post-leg 0-step at 0x108 *)
        BIGNUM_AMONTREDC_POST_LEG_TAC];
      ALL_TAC] THEN
    (* tail: corrective k=1 straight-line: NEG, NEGS, msub-iter (8), RET = 11 steps. *)
    SUBGOAL_THEN `word_shl (word 0:int64) 3 = word(8 * 0)` ASSUME_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `8 * 0 + 8 <= 8 * 1` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_add (word 0:int64) (word 1) = word 1` ASSUME_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `word_sub (word 1:int64) (word 1) = word 0` ASSUME_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `val(word 0:int64) = 0` ASSUME_TAC THENL [REWRITE_TAC[VAL_WORD_0]; ALL_TAC] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_AMONTREDC_EXEC (1--11) THEN
    BIGNUM_AMONTREDC_CARRIED_DISCHARGE_TAC;
    ALL_TAC] THEN

  (*** general k>=2 ***)
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 <= k /\ 1 <= k /\ 0 < k /\ ~(k - 1 = 0) /\ 1 < k` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (* SEQUENCE 0x74: CONJ1 = blockA (prologue + 3-way buffer-init), CONJ2 = the rest. *)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x74`
   `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
        read X4 s = m /\ read X5 s = word p /\ read X30 s = returnaddress` THEN
  CONJ_TAC THENL
   [(* blockA 0x0->0x74: prologue (17 instr 0x00..0x40 incl CBZ@0 nt) + CBZ X8@0x44 + 3-way bufinit.
       CSEL X8 = MIN(k,r) via Condition_CS on CMP X2(=r) X0(=k): X8 = if r>=k then k else r. *)
    SUBGOAL_THEN `(if k <= r then word k else word r):int64 = word(MIN k r)` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `MIN k r = if k <= r then k else r`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `r = 0` THENL
     [(* padA (r = 0): MIN k r = 0, so the CBZ X8 at 0x44 skips the copy loop; then the zero-fill
         WHILE k 0x64/0x74. Substitute r := 0 (the x read-range becomes x,0*8, i.e. empty). Each leg
         normalizes the carried read-events assumption (CONS_TO_APPEND + GSYM APPEND_ASSOC) before
         discharging, as in the bignum_copy pad loop. *)
      UNDISCH_THEN `(if k <= r then word k else word r):int64 = word(MIN k r)` (K ALL_TAC) THEN
      SUBST1_TAC(ASSUME `r = 0`) THEN
      REWRITE_TAC[BIGNUM_AMONTREDC_MIN_N0] THEN RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_AMONTREDC_MIN_N0]) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(k <= 0) /\ val(word 0:int64) = 0` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD_0] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV)
        [prove(`APPEND (ENUMERATEL n f) b:(uarch_event)list =
                APPEND [] (APPEND (ENUMERATEL n f) b)`,
               REWRITE_TAC[CONJUNCT1 APPEND])] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x64` `pc + 0x74`
       `\j s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word 0 /\ read X3 s = x /\
              read X4 s = m /\ read X5 s = word p /\ read X7 s = word j /\
              read X30 s = returnaddress` THEN
      REWRITE_TAC[LT_NZ] THEN
      CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [(* pre-leg: prologue 0x0..0x40 (17) + CBZ X8 taken (1) = 18 steps to 0x64 *)
        REWRITE_TAC[SUB_0; MULT_CLAUSES; ADD_0; ENUMERATEL; CONJUNCT1 APPEND; APPEND_NIL] THEN
        ASM_REWRITE_TAC[] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
          BIGNUM_AMONTREDC_EXEC (1--18) THEN
        ASM_REWRITE_TAC[] THEN
        CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
        RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV)))) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [(* padA body: STR z[X7],ADD,CMP,BCC = 4 steps, as the bignum_copy pad loop. *)
        X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN `j:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
         [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `word_shl (word j:int64) 3 = word(8 * j)` ASSUME_TAC THENL
         [REWRITE_TAC[WORD_SHL_WORD] THEN REWRITE_TAC[ARITH_RULE `2 EXP 3 * m = 8 * m`] THEN
          CONV_TAC WORD_RULE; ALL_TAC] THEN
        SUBGOAL_THEN `8 * j + 8 <= 8 * k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
          BIGNUM_AMONTREDC_EXEC (1--4) THEN
        SUBGOAL_THEN `val(word_add (word j) (word 1):int64) = j + 1` ASSUME_TAC THENL
         [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64] THEN
          IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        BIGNUM_AMONTREDC_PEEL_TAC
          [REFL_TAC;
           ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN REWRITE_TAC[];
           CONV_TAC WORD_RULE; ASM_REWRITE_TAC[]] THEN
        RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV)))) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
        (* padA post-leg: 0 steps at 0x74 *)
        BIGNUM_AMONTREDC_INIT_POST_LEG_TAC];
      ALL_TAC] THEN
    (* r != 0 *)
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(MIN k r = 0) /\ 0 < MIN k r /\ MIN k r <= k /\ MIN k r <= r /\
                  val(word(MIN k r):int64) = MIN k r` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY (IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]) THEN
      SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `k <= r:num` THENL
     [(* copyB: MIN=k; copy WHILE k 0x48/0x5c; then copyBpost = CMP X7 X0, BCS taken -> 0x74 (2 steps) *)
      ASM_REWRITE_TAC[] THEN
      (* the SIM resolves the CSEL X8 to `word k` (via k<=r) but the invariant says word(MIN k r):
         record MIN k r = k so ASM_REWRITE can close `word k = word(MIN k r)` (copyC has MIN k r = r). *)
      SUBGOAL_THEN `MIN k r = k` ASSUME_TAC THENL
       [REWRITE_TAC[MIN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      (* ONCE only: the RHS is itself an instance of the LHS pattern, so a plain REWRITE_TAC
         re-applies forever (TOP_DEPTH_CONV) -> Stack overflow. *)
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV) [prove(
        `APPEND post (APPEND enum pre):(uarch_event)list =
         APPEND post (APPEND [] (APPEND enum pre))`,
        REWRITE_TAC[CONJUNCT1 APPEND])] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x5c`
       `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
            read X4 s = m /\ read X5 s = word p /\ read X7 s = word k /\
            read X30 s = returnaddress` THEN
      CONJ_TAC THENL
       [(* copy loop block: pre-leg = prologue+CBZ-nt (18 steps) to 0x48, WHILE k 0x48/0x5c *)
        BIGNUM_AMONTREDC_COPY_LOOP_TAC `k:num`;
        ALL_TAC] THEN
      (* copyBpost: CMP X7 X0 (X7=k), BCS taken (k>=k) -> 0x74. 2 steps. *)
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
        BIGNUM_AMONTREDC_EXEC (1--2) THEN
      BIGNUM_AMONTREDC_CARRIED_DISCHARGE_TAC;
      ALL_TAC] THEN
    (* copyC/padC: 0 < r < k. MIN=r. copy r then CMP/BCS nt then pad k-r. *)
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `r < k:num /\ MIN k r = r /\ 0 < k - r /\ ~(k - r = 0)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    (* padC WHILE (k-r) 0x64/0x74; its pre-leg = everything up to 0x64:
       prologue(17)+CBZ-nt(1)+copy r iters+CMP(1)+BCS-nt(1). Structure: SEQUENCE 0x5c first. *)
    (* SEQUENCE 0x5c: back = padE++padpre (2nd leg), front = [] ++ (copyE ++ copypre) (1st-leg
       WHILE shape: empty epilogue, prologue copypre). ONCE only: the RHS re-matches the LHS. *)
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV) [prove(
      `APPEND padE (APPEND padpre (APPEND copyE copypre)):(uarch_event)list =
       APPEND (APPEND padE padpre) (APPEND [] (APPEND copyE copypre))`,
      REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL; GSYM APPEND_ASSOC])] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x5c`
     `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
          read X4 s = m /\ read X5 s = word p /\ read X7 s = word r /\
          read X30 s = returnaddress` THEN
    CONJ_TAC THENL
     [(* copy block: pre-leg 18 steps + copy WHILE r 0x48/0x5c *)
      BIGNUM_AMONTREDC_COPY_LOOP_TAC `r:num`;
      ALL_TAC] THEN
    (* padC: CMP X7 X0 BCS-nt (r<k) 2 steps = padCpre, then pad WHILE (k-r) 0x64/0x74 *)
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV)
      [prove(
        `APPEND (APPEND padE padpre) rest:(uarch_event)list =
         APPEND (APPEND [] (APPEND padE [])) (APPEND padpre rest)`,
        REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL; GSYM APPEND_ASSOC])] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x64`
     `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
          read X4 s = m /\ read X5 s = word p /\ read X7 s = word r /\
          read X30 s = returnaddress` THEN
    CONJ_TAC THENL
     [(* padCpre: CMP, BCS-nt. 2 steps. cond: val(word k) <= val(word r) false *)
      SUBGOAL_THEN `(val(word k:int64) <= val(word r:int64)) = F` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
        BIGNUM_AMONTREDC_EXEC (1--2) THEN
      BIGNUM_AMONTREDC_CARRIED_DISCHARGE_TAC;
      ALL_TAC] THEN
    (* pad WHILE (k-r) 0x64/0x74, X7 = r + j *)
    ENSURES_EVENTS_WHILE_UP2_TAC `k - r:num` `pc + 0x64` `pc + 0x74`
     `\j s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
            read X4 s = m /\ read X5 s = word p /\ read X7 s = word(r + j) /\
            read X30 s = returnaddress` THEN
    REWRITE_TAC[LT_NZ] THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [(* pre-leg 0-step: X7 = word r = word(r+0) *)
      BIGNUM_AMONTREDC_NOEVENT_LEG_TAC
        [SUB_0; ADD_0; ENUMERATEL; CONJUNCT1 APPEND; APPEND_NIL]
        (ASM_REWRITE_TAC[]) [];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [(* padC body: STR z[r+j], ADD, CMP, BCC (4 steps); loop-back condition
           r + j + 1 < k, with X7 = word((r + j) + 1). *)
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `r + j < k /\ val(word(r + j):int64) = r + j` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [SIMPLE_ARITH_TAC; IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `word_shl (word(r + j):int64) 3 = word(8 * (r + j))` ASSUME_TAC THENL
       [REWRITE_TAC[WORD_SHL_WORD] THEN REWRITE_TAC[ARITH_RULE `2 EXP 3 * m = 8 * m`] THEN
        CONV_TAC WORD_RULE; ALL_TAC] THEN
      SUBGOAL_THEN `8 * (r + j) + 8 <= 8 * k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
        BIGNUM_AMONTREDC_EXEC (1--4) THEN
      SUBGOAL_THEN `val(word_add (word(r + j)) (word 1):int64) = (r + j) + 1` ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64] THEN
        IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `r + (j + 1) = (r + j) + 1`] THEN
      (* each closer all-or-nothing (THEN NO_TAC): a closer that only REWRITES still "succeeds"
         inside FIRST, leaving a residual conjunct that then hits DISCHARGE's dest_exists. The PC
         closer needs the backedge-cond equivalence (r+j)+1 < k <=> j+1 < k-r (as bignum_copy). *)
      BIGNUM_AMONTREDC_PEEL_TAC
        [REFL_TAC;
         (ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
         REWRITE_TAC[ARITH_RULE `(r + j) + 1 < k <=> j + 1 < k - r`] THEN NO_TAC);
         CONV_TAC WORD_RULE; (ASM_REWRITE_TAC[] THEN NO_TAC)] THEN
      RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV)))) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      (* padC post-leg: 0 steps at 0x74 *)
      BIGNUM_AMONTREDC_INIT_POST_LEG_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `k < 2 EXP 61` ASSUME_TAC THENL
   [UNDISCH_TAC `8 * k < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `p = 0` THENL
   [(* p=0: MOV X14, CBZ X5 taken -> RET@0x130. 3 steps; no correction. *)
    ASM_REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_AMONTREDC_EXEC (1--3) THEN
    BIGNUM_AMONTREDC_CARRIED_DISCHARGE_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(val(word p:int64) = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  (* SEQUENCE 0x108: CONJ1 = main nest 0x74->0x108, CONJ2 = corrective. *)
  REWRITE_TAC[METIS[APPEND_ASSOC]
    `(exists e2. P e2 /\ e2 = APPEND (APPEND ret (APPEND msub mn)) bf /\ Q e2)
     <=> (exists e2. P e2 /\ e2 = APPEND (APPEND ret msub) (APPEND mn bf) /\ Q e2)`] THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x108`
   `\s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\ read X30 s = returnaddress` THEN
  CONJ_TAC THENL
   [(* mainpre SEQUENCE 0x80: MOV X14, CBZ X5 nt, MOV X7=0. 3 steps. *)
    REWRITE_TAC[METIS[APPEND_ASSOC]
      `(exists e2. P e2 /\ e2 = APPEND (APPEND enum mainpre) carr /\ Q e2)
       <=> (exists e2. P e2 /\ e2 = APPEND enum (APPEND mainpre carr) /\ Q e2)`] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x80`
     `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
          read X4 s = m /\ read X5 s = word p /\ read X7 s = word 0 /\ read X30 s = returnaddress` THEN
    CONJ_TAC THENL
     [ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
        BIGNUM_AMONTREDC_EXEC (1--3) THEN
      BIGNUM_AMONTREDC_CARRIED_DISCHARGE_TAC;
      ALL_TAC] THEN
    (* outer WHILE_UP2 p 0x80/0x108 *)
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_AMONTREDC_WHILE_WRAP] THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `p:num` `pc + 0x80` `pc + 0x108`
     `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
            read X4 s = m /\ read X5 s = word p /\ read X7 s = word i /\ read X30 s = returnaddress` THEN
    REWRITE_TAC[LT_NZ] THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [(* outer pre-leg 0-step *)
      BIGNUM_AMONTREDC_PRE_LEG_TAC [];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [(* OUTER BODY per i *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
      REWRITE_TAC[ENUMERATEL_ADD1] THEN
      REWRITE_TAC[METIS[APPEND_ASSOC]
        `(exists e2. P e2 /\ e2 = APPEND (APPEND (APPEND (APPEND oe ie) op) enum) carried /\ Q e2)
         <=> (exists e2. P e2 /\ e2 = APPEND (APPEND oe ie) (APPEND op (APPEND enum carried)) /\ Q e2)`] THEN
      SUBGOAL_THEN `k + i < 2 EXP 64 /\ val(word i:int64) = i /\ val(word(k + i):int64) = k + i`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THEN TRY (IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]) THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      (* oprol SEQUENCE 0xa4: 9 steps incl CBZ@0xa0 nt (k>=2) *)
      ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xa4`
       `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
            read X4 s = m /\ read X5 s = word p /\ read X7 s = word i /\
            read X8 s = word 1 /\ read X30 s = returnaddress` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `~(val(word_sub (word k:int64) (word 1)) = 0)` ASSUME_TAC THENL
         [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[VAL_WORD_1] THEN SIMPLE_ARITH_TAC;
          ALL_TAC] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
          BIGNUM_AMONTREDC_EXEC (1--9) THEN
        BIGNUM_AMONTREDC_CARRIED_DISCHARGE_TAC;
        ALL_TAC] THEN
      (* inner | oepil: SEQUENCE 0xd4 *)
      REWRITE_TAC[METIS[APPEND_ASSOC]
        `(exists e2. P e2 /\ e2 = APPEND (APPEND oe ie) rest /\ Q e2)
         <=> (exists e2. P e2 /\ e2 = APPEND oe (APPEND ie rest) /\ Q e2)`] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xd4`
       `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
            read X4 s = m /\ read X5 s = word p /\ read X7 s = word i /\
            read X8 s = word(1 + (k - 1)) /\ read X30 s = returnaddress` THEN
      CONJ_TAC THENL
       [(* inner WHILE_UP2 (k-1) 0xa4/0xd4 *)
        GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV)
          [BIGNUM_AMONTREDC_WHILE_WRAP] THEN
        ENSURES_EVENTS_WHILE_UP2_TAC `k - 1` `pc + 0xa4` `pc + 0xd4`
         `\j s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word r /\ read X3 s = x /\
                read X4 s = m /\ read X5 s = word p /\ read X7 s = word i /\
                read X8 s = word(1 + j) /\ read X30 s = returnaddress` THEN
        REWRITE_TAC[LT_NZ] THEN
        CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL
         [(* inner pre-leg 0-step *)
          BIGNUM_AMONTREDC_NOEVENT_LEG_TAC
            [SUB_0; ADD_0; ENUMERATEL; CONJUNCT1 APPEND; APPEND_NIL]
            (ASM_REWRITE_TAC[ARITH_RULE `1 + 0 = 1`]) [];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [(* inner body: 12 steps 0xa4..0xd0 *)
          X_GEN_TAC `j:num` THEN STRIP_TAC THEN
          REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
          REWRITE_TAC[ENUMERATEL_ADD1] THEN
          REWRITE_TAC[BIGNUM_AMONTREDC_BODY_REASSOC] THEN
          SUBGOAL_THEN `1 + j < k /\ val(word(1 + j):int64) = 1 + j` STRIP_ASSUME_TAC THENL
           [CONJ_TAC THENL
             [SIMPLE_ARITH_TAC;
              IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC];
            ALL_TAC] THEN
          SUBGOAL_THEN `word_shl (word(1 + j):int64) 3 = word(8 * (1 + j))` ASSUME_TAC THENL
           [REWRITE_TAC[WORD_SHL_WORD] THEN REWRITE_TAC[ARITH_RULE `2 EXP 3 * m = 8 * m`] THEN
            CONV_TAC WORD_RULE; ALL_TAC] THEN
          SUBGOAL_THEN `8 * (1 + j) + 8 <= 8 * k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `word_sub (word(1 + j):int64) (word 1) = word j` ASSUME_TAC THENL
           [SUBGOAL_THEN `(j:num) = (1 + j) - 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
            GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
            COND_CASES_TAC THENL
             [REWRITE_TAC[ARITH_RULE `(1 + j) - 1 = j`]; POP_ASSUM MP_TAC THEN SIMPLE_ARITH_TAC];
            ALL_TAC] THEN
          SUBGOAL_THEN `word_shl (word j:int64) 3 = word(8 * j)` ASSUME_TAC THENL
           [REWRITE_TAC[WORD_SHL_WORD] THEN REWRITE_TAC[ARITH_RULE `2 EXP 3 * m = 8 * m`] THEN
            CONV_TAC WORD_RULE; ALL_TAC] THEN
          SUBGOAL_THEN `8 * j + 8 <= 8 * k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
            BIGNUM_AMONTREDC_EXEC (1--12) THEN
          BIGNUM_AMONTREDC_BACKEDGE_TAC
            `(~(val (word_sub (word_add (word (1 + j)) (word 1)) (word k:int64)) = 0)) <=>
             (j + 1 < k - 1)`
            (SUBGOAL_THEN `word_add (word (1 + j):int64) (word 1) = word((1 + j) + 1)`
             SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
             SUBGOAL_THEN `val(word((1 + j) + 1):int64) = (1 + j) + 1` ASSUME_TAC THENL
              [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
             REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC) THEN
          CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
          CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;
          (* inner post-leg 0-step at 0xd4 *)
          BIGNUM_AMONTREDC_POST_LEG_TAC];
        ALL_TAC] THEN
      (* OEPIL leg 0xd4 -> (0x80|0x108): 13 steps (k+i<r, x-load) or 10 steps (skip). *)
      (* Rewrite with this equation without keeping it as an assumption: an
         assumption rewritten with itself becomes `T`, and a `T` assumption
         makes the final rewriting with the assumptions in ASSEMBLER_SIMPLIFY_TAC
         loop (Stack overflow) at the next simulation step with a `T` in the
         state, here the BCS at 0xe4. *)
      SUBGOAL_THEN `word(1 + (k - 1)):int64 = word k`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
       [AP_TERM_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `word_add (word k:int64) (word i) = word(k + i)` ASSUME_TAC THENL
       [CONV_TAC WORD_RULE; ALL_TAC] THEN
      SUBGOAL_THEN `word_sub (word k:int64) (word 1) = word(k - 1)` ASSUME_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
         [REFL_TAC; POP_ASSUM MP_TAC THEN SIMPLE_ARITH_TAC]; ALL_TAC] THEN
      SUBGOAL_THEN `word_shl (word(k - 1):int64) 3 = word(8 * (k - 1))` ASSUME_TAC THENL
       [REWRITE_TAC[WORD_SHL_WORD] THEN REWRITE_TAC[ARITH_RULE `2 EXP 3 * m = 8 * m`] THEN
        CONV_TAC WORD_RULE; ALL_TAC] THEN
      SUBGOAL_THEN `val(word(k - 1):int64) = k - 1 /\ 8 * (k - 1) + 8 <= 8 * k` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `word_add (word i:int64) (word 1) = word(i + 1)` ASSUME_TAC THENL
       [CONV_TAC WORD_RULE; ALL_TAC] THEN
      SUBGOAL_THEN `val(word(i + 1):int64) = i + 1` ASSUME_TAC THENL
       [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `k + i < r` THENL
       [(* oepilL: with x[k+i] load, 13 steps *)
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `word_shl (word(k + i):int64) 3 = word(8 * (k + i))` ASSUME_TAC THENL
         [REWRITE_TAC[WORD_SHL_WORD] THEN REWRITE_TAC[ARITH_RULE `2 EXP 3 * m = 8 * m`] THEN
          CONV_TAC WORD_RULE; ALL_TAC] THEN
        SUBGOAL_THEN `8 * (k + i) + 8 <= 8 * r` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(val(word r:int64) <= val(word(k + i):int64)) = F` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        (* num-form too (the SIM strips val; as in the k=1 bodyL): resolves the BCS@0xe4 by rewriting *)
        SUBGOAL_THEN `~(r <= k + i)` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
          BIGNUM_AMONTREDC_EXEC (1--13) THEN
        BIGNUM_AMONTREDC_BACKEDGE_TAC
          `(val(word(i + 1):int64) < val(word p:int64)) <=> (i + 1 < p)`
          (ASM_REWRITE_TAC[]) THEN
        (* adaptive all-or-nothing peel: the SIM may already close X7, leaving 1 or 2 leading conjuncts *)
        BIGNUM_AMONTREDC_PEEL_TAC
          [REFL_TAC; (COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC);
           CONV_TAC WORD_RULE; (ASM_REWRITE_TAC[] THEN NO_TAC)] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
        (* oepilN: skip x load, 10 steps *)
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(val(word r:int64) <= val(word(k + i):int64)) = T` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `r <= k + i` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
          BIGNUM_AMONTREDC_EXEC (1--10) THEN
        BIGNUM_AMONTREDC_BACKEDGE_TAC
          `(val(word(i + 1):int64) < val(word p:int64)) <=> (i + 1 < p)`
          (ASM_REWRITE_TAC[]) THEN
        (* adaptive all-or-nothing peel: the SIM may already close X7, leaving 1 or 2 leading conjuncts *)
        BIGNUM_AMONTREDC_PEEL_TAC
          [REFL_TAC; (COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC);
           CONV_TAC WORD_RULE; (ASM_REWRITE_TAC[] THEN NO_TAC)] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC];
      (* outer post-leg 0-step at 0x108 *)
      BIGNUM_AMONTREDC_POST_LEG_TAC];
    ALL_TAC] THEN
  (*** corrective 0x108->RET: SEQUENCE 0x130 (mask+msub | RET); msub WHILE_UP2 k 0x110/0x130
       (pre-leg NEG,NEGS 2 steps), RET leg. ***)
  (* postcondition only: the carried precondition trace (main nest ++ bufinit) has the same
     APPEND (APPEND _ _) _ shape and must stay unchanged for the SEQUENCE split. *)
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV) [METIS[APPEND_ASSOC]
    `(exists e2. P e2 /\ e2 = APPEND (APPEND ret msub) carried /\ Q e2)
     <=> (exists e2. P e2 /\ e2 = APPEND ret (APPEND msub carried) /\ Q e2)`] THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x130`
   `\s. read X30 s = returnaddress` THEN
  CONJ_TAC THENL
   [(* mask NEG X14 + NEGS X8 (2 instr, no events) + msub WHILE_UP2 k 0x110/0x130 *)
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_AMONTREDC_WHILE_WRAP] THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x110` `pc + 0x130`
     `\j s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\
            read X8 s = word j /\ read X30 s = returnaddress` THEN
    REWRITE_TAC[LT_NZ] THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [(* pre-leg: NEG,NEGS 2 steps no events *)
      BIGNUM_AMONTREDC_PRE_LEG_TAC (1--2);
      ALL_TAC] THEN
    CONJ_TAC THENL
     [(* msub body: 8 steps LDR,LDR,AND,SBCS,STR,ADD,SUB,CBNZ *)
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
      REWRITE_TAC[ENUMERATEL_ADD1] THEN
      REWRITE_TAC[BIGNUM_AMONTREDC_BODY_REASSOC] THEN
      SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
       [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `word_shl (word j:int64) 3 = word(8 * j)` ASSUME_TAC THENL
       [REWRITE_TAC[WORD_SHL_WORD] THEN REWRITE_TAC[ARITH_RULE `2 EXP 3 * m = 8 * m`] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      SUBGOAL_THEN `8 * j + 8 <= 8 * k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(j + 1 = k <=> ~(j + 1 < k))` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
        BIGNUM_AMONTREDC_EXEC (1--8) THEN
      BIGNUM_AMONTREDC_BACKEDGE_TAC
        `(~(val (word_sub (word_add (word j) (word 1)) (word k:int64)) = 0)) <=>
         (j + 1 < k)`
        (SUBGOAL_THEN `word_add (word j:int64) (word 1) = word(j + 1)` SUBST1_TAC THENL
          [CONV_TAC WORD_RULE; ALL_TAC] THEN
         SUBGOAL_THEN `val(word(j + 1):int64) = j + 1` ASSUME_TAC THENL
          [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
         REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC) THEN
      CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      (* msub post-leg: 0-step at 0x130 *)
      BIGNUM_AMONTREDC_POST_LEG_TAC];
    ALL_TAC] THEN
  (* RET leg 0x130->returnaddress, 1 step. *)
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
    BIGNUM_AMONTREDC_EXEC (1--1) THEN
  BIGNUM_AMONTREDC_CARRIED_DISCHARGE_TAC);;
