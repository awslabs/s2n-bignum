(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo n_256k1, the order of the secp256k1 curve.               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/secp256k1/bignum_mod_n256k1.o";;
 ****)

let bignum_mod_n256k1_mc =
  define_assert_from_elf "bignum_mod_n256k1_mc" "arm/secp256k1/bignum_mod_n256k1.o"
[
  0xf100103f;       (* arm_CMP X1 (rvalue (word 4)) *)
  0x540006a3;       (* arm_BCC (word 212) *)
  0xd1001021;       (* arm_SUB X1 X1 (rvalue (word 4)) *)
  0xd37df027;       (* arm_LSL X7 X1 (rvalue (word 3)) *)
  0x8b0200e7;       (* arm_ADD X7 X7 X2 *)
  0xa94118e5;       (* arm_LDP X5 X6 X7 (Immediate_Offset (iword (&16))) *)
  0xa94010e3;       (* arm_LDP X3 X4 X7 (Immediate_Offset (iword (&0))) *)
  0xd297d7ec;       (* arm_MOV X12 (rvalue (word 48831)) *)
  0xf2a5f92c;       (* arm_MOVK X12 (word 12233) 16 *)
  0xf2d42e6c;       (* arm_MOVK X12 (word 41331) 32 *)
  0xf2e805ac;       (* arm_MOVK X12 (word 16429) 48 *)
  0xd28bf88d;       (* arm_MOV X13 (rvalue (word 24516)) *)
  0xf2aa16ed;       (* arm_MOVK X13 (word 20663) 16 *)
  0xf2c4632d;       (* arm_MOVK X13 (word 8985) 32 *)
  0xf2e8aa2d;       (* arm_MOVK X13 (word 17745) 48 *)
  0xab0c0067;       (* arm_ADDS X7 X3 X12 *)
  0xba0d0088;       (* arm_ADCS X8 X4 X13 *)
  0xd280002b;       (* arm_MOV X11 (rvalue (word 1)) *)
  0xba0b00a9;       (* arm_ADCS X9 X5 X11 *)
  0xba1f00ca;       (* arm_ADCS X10 X6 XZR *)
  0x9a873063;       (* arm_CSEL X3 X3 X7 Condition_CC *)
  0x9a883084;       (* arm_CSEL X4 X4 X8 Condition_CC *)
  0x9a8930a5;       (* arm_CSEL X5 X5 X9 Condition_CC *)
  0x9a8a30c6;       (* arm_CSEL X6 X6 X10 Condition_CC *)
  0xb4000361;       (* arm_CBZ X1 (word 108) *)
  0xb10004ce;       (* arm_ADDS X14 X6 (rvalue (word 1)) *)
  0xda9f31ce;       (* arm_CSINV X14 X14 XZR Condition_CC *)
  0x9b0e7d87;       (* arm_MUL X7 X12 X14 *)
  0x9b0e7da8;       (* arm_MUL X8 X13 X14 *)
  0x9bce7d89;       (* arm_UMULH X9 X12 X14 *)
  0xab090108;       (* arm_ADDS X8 X8 X9 *)
  0x9bce7da9;       (* arm_UMULH X9 X13 X14 *)
  0x9a1f0129;       (* arm_ADC X9 X9 XZR *)
  0xab0e0129;       (* arm_ADDS X9 X9 X14 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0xcb0e00c6;       (* arm_SUB X6 X6 X14 *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xf861784e;       (* arm_LDR X14 X2 (Shiftreg_Offset X1 3) *)
  0xab0701c7;       (* arm_ADDS X7 X14 X7 *)
  0xba080068;       (* arm_ADCS X8 X3 X8 *)
  0xba090089;       (* arm_ADCS X9 X4 X9 *)
  0xba0a00aa;       (* arm_ADCS X10 X5 X10 *)
  0x9a1f00cb;       (* arm_ADC X11 X6 XZR *)
  0x8a0c016e;       (* arm_AND X14 X11 X12 *)
  0xeb0e00e3;       (* arm_SUBS X3 X7 X14 *)
  0x8a0d016e;       (* arm_AND X14 X11 X13 *)
  0xfa0e0104;       (* arm_SBCS X4 X8 X14 *)
  0x9240016e;       (* arm_AND X14 X11 (rvalue (word 1)) *)
  0xfa0e0125;       (* arm_SBCS X5 X9 X14 *)
  0xda1f0146;       (* arm_SBC X6 X10 XZR *)
  0xb5fffce1;       (* arm_CBNZ X1 (word 2097052) *)
  0xa9001003;       (* arm_STP X3 X4 X0 (Immediate_Offset (iword (&0))) *)
  0xa9011805;       (* arm_STP X5 X6 X0 (Immediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xb4ffff21;       (* arm_CBZ X1 (word 2097124) *)
  0xf9400043;       (* arm_LDR X3 X2 (Immediate_Offset (word 0)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffec0;       (* arm_BEQ (word 2097112) *)
  0xf9400444;       (* arm_LDR X4 X2 (Immediate_Offset (word 8)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffe60;       (* arm_BEQ (word 2097100) *)
  0xf9400845;       (* arm_LDR X5 X2 (Immediate_Offset (word 16)) *)
  0x17fffff1        (* arm_B (word 268435396) *)
];;

let BIGNUM_MOD_N256K1_EXEC = ARM_MK_EXEC_RULE bignum_mod_n256k1_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let n_256k1 = new_definition `n_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141`;;

let n256k1longredlemma = prove
 (`!n. n < 2 EXP 64 * n_256k1
       ==> let q = MIN (n DIV 2 EXP 256 + 1) (2 EXP 64 - 1) in
           q < 2 EXP 64 /\
           q * n_256k1 <= n + n_256k1 /\
           n < q * n_256k1 + n_256k1`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[n_256k1] THEN ARITH_TAC);;

let BIGNUM_MOD_N256K1_CORRECT = time prove
 (`!z k x n pc.
      nonoverlapping (word pc,0x10c) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n256k1_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read PC s = word (pc + 0xd4) /\
                bignum_from_memory (z,4) s = n MOD n_256k1)
          (MAYCHANGE [PC; X1; X3; X4; X5; X6; X7; X8; X9;
                      X10; X11; X12; X13; X14] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X_GEN_TAC `z:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Case split over the k < 4 case, which is a different path ***)

  ASM_CASES_TAC `k < 4` THENL
   [SUBGOAL_THEN `n MOD n_256k1 = n` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * k)` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP (64 * 3)` THEN
      ASM_REWRITE_TAC[LE_EXP; n_256k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
   REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
   BIGNUM_DIGITIZE_TAC "n_" `read(memory :> bytes(x,8 * 4)) s0` THEN
   FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
    `k < 4 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`)) THEN
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
   EXPAND_TAC "n" THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
   ASM_REWRITE_TAC[] THENL
    [ARM_STEPS_TAC BIGNUM_MOD_N256K1_EXEC (1--9);
     ARM_STEPS_TAC BIGNUM_MOD_N256K1_EXEC (1--12);
     ARM_STEPS_TAC BIGNUM_MOD_N256K1_EXEC (1--15);
     ARM_STEPS_TAC BIGNUM_MOD_N256K1_EXEC (1--17)] THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
   ARITH_TAC;
   FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LT])] THEN

  (*** Initial 4-digit modulus ***)

  ENSURES_SEQUENCE_TAC `pc + 0x60`
   `\s. bignum_from_memory(x,k) s = n /\
        read X0 s = z /\
        read X2 s = x /\
        read X1 s = word(k - 4) /\
        read X12 s = word 0x402DA1732FC9BEBF /\
        read X13 s = word 0x4551231950B75FC4 /\
        bignum_of_wordlist[read X3 s; read X4 s; read X5 s; read X6 s] =
        (highdigits n (k - 4)) MOD n_256k1` THEN
  CONJ_TAC THENL
   [ABBREV_TAC `j = k - 4` THEN VAL_INT64_TAC `j:num` THEN
    SUBGOAL_THEN `word_sub (word k) (word 4):int64 = word j` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `k - 4 = j`)) THEN
      REWRITE_TAC[WORD_SUB] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[highdigits] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_DIV] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    SUBST1_TAC(SYM(ASSUME `k - 4 = j`)) THEN
    ASM_SIMP_TAC[ARITH_RULE `4 <= k ==> k - (k - 4) = 4`] THEN
    ABBREV_TAC `m = bignum_from_memory(word_add x (word (8 * j)),4) s0` THEN
    SUBGOAL_THEN `m < 2 EXP (64 * 4)` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND]; ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV)) THEN
    BIGNUM_DIGITIZE_TAC "m_"
     `read (memory :> bytes (word_add x (word(8 * j)),8 * 4)) s0` THEN
    ARM_STEPS_TAC BIGNUM_MOD_N256K1_EXEC (1--5) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_shl (word j) 3) x = word_add x (word(8 * j))`]) THEN
    ARM_ACCSTEPS_TAC BIGNUM_MOD_N256K1_EXEC [16;17;19;20] (6--20) THEN
    SUBGOAL_THEN `carry_s20 <=> n_256k1 <= m` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[n_256k1; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    ARM_STEPS_TAC BIGNUM_MOD_N256K1_EXEC (21--24) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s24" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
    ANTS_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP (64 * 4)` THEN
      ASM_REWRITE_TAC[n_256k1] THEN CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THENL
     [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
      UNDISCH_TAC `m < 2 EXP (64 * 4)` THEN REWRITE_TAC[n_256k1] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; n_256k1] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Finish off the k = 4 case which is now just the writeback ***)

  FIRST_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o MATCH_MP (ARITH_RULE
   `4 <= k ==> k = 4 \/ 4 < k`))
  THENL
   [GHOST_INTRO_TAC `d0:int64` `read X3` THEN
    GHOST_INTRO_TAC `d1:int64` `read X4` THEN
    GHOST_INTRO_TAC `d2:int64` `read X5` THEN
    GHOST_INTRO_TAC `d3:int64` `read X6` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_N256K1_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `0 < k - 4 /\ ~(k - 4 = 0)` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Setup of loop invariant ***)

  ENSURES_WHILE_DOWN_TAC `k - 4` `pc + 0x64` `pc + 0xc8`
   `\i s. bignum_from_memory(x,k) s = n /\
          read X0 s = z /\
          read X2 s = x /\
          read X1 s = word i /\
          read X12 s = word 0x402DA1732FC9BEBF /\
          read X13 s = word 0x4551231950B75FC4 /\
          bignum_of_wordlist[read X3 s; read X4 s; read X5 s; read X6 s] =
          (highdigits n i) MOD n_256k1` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [VAL_INT64_TAC `k - 4` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_N256K1_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_N256K1_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    GHOST_INTRO_TAC `d0:int64` `read X3` THEN
    GHOST_INTRO_TAC `d1:int64` `read X4` THEN
    GHOST_INTRO_TAC `d2:int64` `read X5` THEN
    GHOST_INTRO_TAC `d3:int64` `read X6` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MOD_N256K1_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN

  (*** Mathematics of main loop with decomposition and quotient estimate ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `m1:int64` `read X3` THEN
  GHOST_INTRO_TAC `m2:int64` `read X4` THEN
  GHOST_INTRO_TAC `m3:int64` `read X5` THEN
  GHOST_INTRO_TAC `m4:int64` `read X6` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m0:int64 = word(bigdigit n i)` THEN
  ABBREV_TAC `m = bignum_of_wordlist[m0; m1; m2; m3; m4]` THEN
  SUBGOAL_THEN `m < 2 EXP 64 * n_256k1` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MP_TAC(SPEC `m0:int64` VAL_BOUND_64) THEN
    ASM_REWRITE_TAC[n_256k1] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `highdigits n i MOD n_256k1 = m MOD n_256k1` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[HIGHDIGITS_STEP] THEN
    EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    EXPAND_TAC "m0" THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC MOD_DOWN_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `m:num` n256k1longredlemma) THEN ASM_REWRITE_TAC[] THEN
  LET_TAC THEN STRIP_TAC THEN

  (*** The computation of the quotient estimate q ***)

  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  ARM_ACCSTEPS_TAC BIGNUM_MOD_N256K1_EXEC [1] (1--2) THEN

  FIRST_X_ASSUM(MP_TAC o SPEC `word q:int64` o MATCH_MP (MESON[]
   `!q. read X14 s = q' ==> q' = q ==> read X14 s = q`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "q" THEN
    EXPAND_TAC "m" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    BOOL_CASES_TAC `carry_s1:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; MULT_CLAUSES] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THENL
     [REWRITE_TAC[ARITH_RULE
       `MIN (2 EXP 64 + a) (2 EXP 64 - 1) = 2 EXP 64 - 1`] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      SIMP_TAC[VAL_BOUND_64; WORD_VAL; ARITH_RULE
       `a < 2 EXP 64 ==> MIN a (2 EXP 64 - 1) = a`]];
    DISCH_TAC THEN VAL_INT64_TAC `q:num`] THEN

  (*** The next digit in the current state ***)

  SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `x:int64`; `s2:armstate`; `i:num`]
        BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  DISCH_THEN(MP_TAC o AP_TERM `word:num->int64` o SYM) THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN DISCH_TAC THEN

  (*** A bit of fiddle to make the accumulation tactics work ***)

  ABBREV_TAC `w:int64 = word q` THEN
  UNDISCH_THEN `val(w:int64) = q` (SUBST_ALL_TAC o SYM) THEN
  ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC o end_itlist CONJ) THEN

  (*** Subtraction of q * n_256k1 ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_N256K1_EXEC
    [3;4;5;6;7;8;9;10;11] (3--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word (i + 1)) (word 1):int64 = word i`]) THEN

  (*** Remove spurious accumulator entries created from rvalue expressions ***)
  REPEAT(FIRST_X_ASSUM(fun th ->
    if free_in `sum_s5:int64` (concl th) ||
       free_in `sum_s7:int64` (concl th) ||
       free_in `sum_s10:int64` (concl th)
    then ALL_TAC else failwith "keep")) THEN

  ARM_ACCSTEPS_TAC BIGNUM_MOD_N256K1_EXEC [14;15;16;17;18] (13--18) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN

  SUBGOAL_THEN
   `sum_s18:int64 = word_neg(word(bitval(m < val(w:int64) * n_256k1))) /\
    &(bignum_of_wordlist[sum_s14; sum_s15; sum_s16; sum_s17]) =
        if m < val w * n_256k1 then &m - &(val w * n_256k1) + &2 pow 256
        else &m - &(val w * n_256k1)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MASK_AND_VALUE_FROM_CARRY_LT THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`val(w:int64) * n_256k1 <= m + n_256k1`;
        `m < val(w:int64) * n_256k1 + n_256k1`] THEN
      REWRITE_TAC[n_256k1; GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES]] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV)] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES; n_256k1] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    REPEAT(MATCH_MP_TAC INTEGER_ADD THEN CONJ_TAC) THEN
    TRY REAL_INTEGER_TAC THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_N256K1_EXEC [20;22;24;25] (19--25) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(w:int64)`; `256`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b <=> m < val(w:int64) * n_256k1` THEN
  REWRITE_TAC[REAL_ARITH
   `m - s - (w - b) * n:real = (m - w * n) + (b * n - s)`] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (MESON[REAL_ADD_RID]
   `x = (if p then y + z else y) ==> x = y + (if p then z else &0)`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; n_256k1] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `x:real = y + z <=> y = x - z`] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REAL_INTEGER_TAC);;

let BIGNUM_MOD_N256K1_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc returnaddress.
      nonoverlapping (word pc,0x10c) (z,32)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_mod_n256k1_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,4) s = n MOD n_256k1)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MOD_N256K1_EXEC
    BIGNUM_MOD_N256K1_CORRECT);;
