(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extended Montgomery reduction of arbitrary bignum.                        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_emontredc.o";;
 ****)

let bignum_emontredc_mc =
  define_assert_from_elf "bignum_emontredc_mc" "arm/generic/bignum_emontredc.o"
[
  0xb4000460;       (* arm_CBZ X0 (word 140) *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xf9400029;       (* arm_LDR X9 X1 (Immediate_Offset (word 0)) *)
  0x9b037d26;       (* arm_MUL X6 X9 X3 *)
  0xf940004b;       (* arm_LDR X11 X2 (Immediate_Offset (word 0)) *)
  0x9b0b7cca;       (* arm_MUL X10 X6 X11 *)
  0x9bcb7cc8;       (* arm_UMULH X8 X6 X11 *)
  0xf9000026;       (* arm_STR X6 X1 (Immediate_Offset (word 0)) *)
  0xab0a013f;       (* arm_CMN X9 X10 *)
  0xd2800025;       (* arm_MOV X5 (rvalue (word 1)) *)
  0xd100040b;       (* arm_SUB X11 X0 (rvalue (word 1)) *)
  0xb400018b;       (* arm_CBZ X11 (word 48) *)
  0xf865784b;       (* arm_LDR X11 X2 (Shiftreg_Offset X5 3) *)
  0xf8657829;       (* arm_LDR X9 X1 (Shiftreg_Offset X5 3) *)
  0x9b0b7cca;       (* arm_MUL X10 X6 X11 *)
  0xba080129;       (* arm_ADCS X9 X9 X8 *)
  0x9bcb7cc8;       (* arm_UMULH X8 X6 X11 *)
  0x9a1f0108;       (* arm_ADC X8 X8 XZR *)
  0xab0a0129;       (* arm_ADDS X9 X9 X10 *)
  0xf8257829;       (* arm_STR X9 X1 (Shiftreg_Offset X5 3) *)
  0x910004a5;       (* arm_ADD X5 X5 (rvalue (word 1)) *)
  0xcb0000ab;       (* arm_SUB X11 X5 X0 *)
  0xb5fffecb;       (* arm_CBNZ X11 (word 2097112) *)
  0xba070108;       (* arm_ADCS X8 X8 X7 *)
  0x9a1f03e7;       (* arm_ADC X7 XZR XZR *)
  0xf860782b;       (* arm_LDR X11 X1 (Shiftreg_Offset X0 3) *)
  0xab0b0108;       (* arm_ADDS X8 X8 X11 *)
  0x9a1f00e7;       (* arm_ADC X7 X7 XZR *)
  0xf8207828;       (* arm_STR X8 X1 (Shiftreg_Offset X0 3) *)
  0x91002021;       (* arm_ADD X1 X1 (rvalue (word 8)) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54fffc43;       (* arm_BCC (word 2097032) *)
  0xaa0703e0;       (* arm_MOV X0 X7 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_EMONTREDC_EXEC = ARM_MK_EXEC_RULE bignum_emontredc_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_EMONTREDC_CORRECT = time prove
 (`!k z m w a n pc.
        nonoverlapping (word pc,0x90) (z,8 * 2 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * 2 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k; z; m; w] s /\
                  bignum_from_memory (z,2 * val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = word(pc + 0x8c) /\
                  ((n * val w + 1 == 0) (mod (2 EXP 64))
                   ==> n * bignum_from_memory (z,val k) s + a =
                       2 EXP (64 * val k) *
                       (2 EXP (64 * val k) * val(C_RETURN s) +
                        bignum_from_memory
                          (word_add z (word(8 * val k)),val k) s)))
             (MAYCHANGE [PC; X0; X1; X4; X5; X6; X7; X8; X9; X10; X11] ,,
              MAYCHANGE [memory :> bytes(z,8 * 2 * val k)] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `m:int64`] THEN
  W64_GEN_TAC `w:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `2 * k` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Degenerate k = 0 case ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_EXEC [1] THEN
    REWRITE_TAC[MULT_CLAUSES; CONG] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Get a basic bound on k from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN

  (*** The outer loop setup with start and end ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0xc` `pc + 0x80`
   `\i s. read X0 s = word k /\
          read X1 s = word_add z (word(8 * i)) /\
          read X2 s = m /\
          read X3 s = word w /\
          bignum_from_memory (m,k) s = n /\
          read X4 s = word i /\
          bignum_from_memory(word_add z (word(8 * (k + i))),
                             2 * k - (k + i)) s =
          highdigits a (k + i) /\
          ?r. r < 2 EXP (64 * i) /\
              2 EXP (64 * i) *
              (2 EXP (64 * k) * val(read X7 s) +
               bignum_from_memory(word_add z (word(8 * i)),k) s) + r =
              bignum_from_memory(z,i) s * n + lowdigits a (k + i) /\
              ((n * w + 1 == 0) (mod (2 EXP 64)) ==> r = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:armstate`]
        HIGHDIGITS_BIGNUM_FROM_MEMORY) THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:armstate`]
        LOWDIGITS_BIGNUM_FROM_MEMORY) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `MIN (2 * k) k = k /\ 2 * k - k = k`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(ASSUME_TAC o SYM)) THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `2 * k - k = k`] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; VAL_WORD_0; EXP] THEN
    EXISTS_TAC `0` THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES; MULT_CLAUSES];
    ALL_TAC; (*** This is the main loop invariant: save for later ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_EXEC (1--2);
    GHOST_INTRO_TAC `cout:int64` `read X7` THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_EXEC (1--3) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `r:num` MP_TAC) THEN
    ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; GSYM MULT_2] THEN REWRITE_TAC[MULT_SYM]] THEN

  (*** Start on the main outer loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `cout:num` `\s. val(read X7 s)` THEN
  GHOST_INTRO_TAC `z1:num`
   `bignum_from_memory(word_add z (word (8 * i)),k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z1:num` THEN
  GHOST_INTRO_TAC `q:num` `bignum_from_memory (z,i)` THEN
  BIGNUM_TERMRANGE_TAC `i:num` `q:num` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN

  (*** The initial prelude of the Montgomery reduction ***)

  ABBREV_TAC `q0 = (w * z1) MOD 2 EXP 64` THEN
  SUBGOAL_THEN `q0 < 2 EXP 64 /\ val(word q0:int64) = q0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q0" THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL];
    ALL_TAC] THEN

  (*** Rebase some things at z' = z + 8 * i ***)

  ABBREV_TAC `z':int64 = word_add z (word (8 * i))` THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN

  SUBGOAL_THEN
   `word_add z (word (8 * (k + i))):int64 = word_add z' (word(8 * k)) /\
    word_add z (word (8 * (k + i + 1))) = word_add z' (word(8 * (k + 1))) /\
    word_add z (word (8 * (i + 1))):int64 = word_add z' (word(8 * 1))`
  (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
    [EXPAND_TAC "z'" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `n - (k + i + 1) = n - (k + i) - 1`] THEN
  REWRITE_TAC[ARITH_RULE `2 * k - (k + i) = 2 * k - i - k`] THEN

  ABBREV_TAC `p = 2 * k - i` THEN
  SUBGOAL_THEN `~(p = 0) /\ 0 < p /\ k < p` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN UNDISCH_TAC `i:num < k` THEN ARITH_TAC; ALL_TAC] THEN

  SUBGOAL_THEN
   `nonoverlapping (z',8 * p) (z:int64,8 * i) /\
    nonoverlapping (z',8 * p) (m,8 * k) /\
    nonoverlapping (z',8 * p) (word pc,144)`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "z'" THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE [PC; X0; X1; X4; X5; X6; X7; X8; X9; X10; X11] ,,
    MAYCHANGE [memory :> bytes (z',8 * p)] ,,
    MAYCHANGE [NF; ZF; CF; VF] ,,
    MAYCHANGE [events]` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0x30`
   `\s. read X0 s = word k /\
        read X1 s = z' /\
        read X2 s = m /\
        read X3 s = word w /\
        bignum_from_memory (m,k) s = n /\
        bignum_from_memory (z,i) s = q /\
        read X4 s = word i /\
        bignum_from_memory (word_add z' (word (8 * k)),p - k) s =
        highdigits a (k + i) /\
        read X7 s = word cout /\
        bignum_from_memory(word_add z' (word 8),k - 1) s = highdigits z1 1 /\
        read (memory :> bytes64 z') s = word q0 /\
        read X5 s = word 1 /\
        read X6 s = word q0 /\
        read X11 s = word(k - 1) /\
        ?r0. r0 < 2 EXP 64 /\
             2 EXP 64 * (bitval(read CF s) + val(read X8 s)) + r0 =
             q0 * bigdigit n 0 + bigdigit z1 0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `bignum_from_memory(m,k) s0 = highdigits n 0 /\
      bignum_from_memory(z',k) s0 = highdigits z1 0`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES];
      GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
       [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; ADD_CLAUSES] THEN
      STRIP_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_EXEC [4;7] (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC(TAUT `k /\ (k ==> q) ==> k /\ q`) THEN CONJ_TAC THENL
     [UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
      ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
      REWRITE_TAC[GSYM LOWDIGITS_1; lowdigits; MULT_CLAUSES] THEN
      REWRITE_TAC[ADD_CLAUSES; DIMINDEX_64; VAL_WORD] THEN
      CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM];
      DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= k <=> ~(k = 0)`] THEN
    EXISTS_TAC `val(sum_s7:int64)` THEN REWRITE_TAC[VAL_BOUND_64] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Break at "montend" to share the end reasoning ***)

  GHOST_INTRO_TAC `carin:bool` `read CF` THEN
  GHOST_INTRO_TAC `mulin:int64` `read X8` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r0:num` STRIP_ASSUME_TAC) THEN

  ENSURES_SEQUENCE_TAC `pc + 0x60`
   `\s. read X0 s = word k /\
        read X1 s = z' /\
        read X2 s = m /\
        read X3 s = word w /\
        bignum_from_memory (m,k) s = n /\
        bignum_from_memory (z,i) s = q /\
        read X4 s = word i /\
        bignum_from_memory (word_add z' (word (8 * k)),p - k) s =
        highdigits a (k + i) /\
        read X7 s = word cout /\
        read (memory :> bytes64 z') s = word q0 /\
        read X5 s = word k /\
        read X6 s = word q0 /\
        2 EXP (64 * k) * (bitval(read CF s) + val(read X8 s)) +
        bignum_from_memory(z',k) s + r0 =
        q0 + lowdigits z1 k + q0 * lowdigits n k` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 1` THENL
     [UNDISCH_THEN `k = 1` SUBST_ALL_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_EMONTREDC_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SING] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `a + b + c:num = (a + c) + b`] THEN
      ASM_REWRITE_TAC[LOWDIGITS_1] THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** The Montgomery reduction loop ***)

    VAL_INT64_TAC `k - 1` THEN

    ENSURES_WHILE_AUP_TAC `1` `k:num` `pc + 0x34` `pc + 0x58`
     `\j s. read X0 s = word k /\
            read X1 s = z' /\
            read X2 s = m /\
            read X3 s = word w /\
            bignum_from_memory (m,k) s = n /\
            bignum_from_memory (z,i) s = q /\
            read X4 s = word i /\
            bignum_from_memory (word_add z' (word (8 * k)),p - k) s =
            highdigits a (k + i) /\
            read X7 s = word cout /\
            bignum_from_memory (word_add z' (word (8 * j)),k - j) s =
            highdigits z1 j /\
            bignum_from_memory (word_add m (word (8 * j)),k - j) s =
            highdigits n j /\
            read (memory :> bytes64 z') s = word q0 /\
            read X5 s = word j /\
            read X6 s = word q0 /\
            2 EXP (64 * j) * (bitval(read CF s) + val(read X8 s)) +
            bignum_from_memory(z',j) s + r0 =
            q0 + lowdigits z1 j + q0 * lowdigits n j` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0 \/ k = 1)`];
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_EMONTREDC_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k <= 1 <=> k = 0 \/ k = 1`] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[MULT_CLAUSES]; ALL_TAC] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_SING] THEN
      ASM_REWRITE_TAC[GSYM highdigits; BIGNUM_FROM_MEMORY_BYTES] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LOWDIGITS_1] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `a + b + c:num = (a + c) + b`] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `hin:int64` `read X8` THEN
      MP_TAC(GENL [`x:int64`; `a:num`]
       (ISPECL [`x:int64`; `k - j:num`; `a:num`; `j:num`]
          BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      UNDISCH_THEN `val(word q0:int64) = q0` (K ALL_TAC) THEN
      SUBGOAL_THEN
       `nonoverlapping (word_add z' (word (8 * j)):int64,8)
                       (word_add z' (word (8 * k)),8 * (p - k))`
      MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
       [SUBGOAL_THEN `word_add z' (word (8 * k)):int64 =
                    word_add (word_add z' (word (8 * j)))
                             (word(8 + 8 * ((k - j) - 1)))`
        SUBST1_TAC THENL
         [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
          NONOVERLAPPING_TAC];
        DISCH_TAC] THEN
      ABBREV_TAC `z'':int64 = word_add z' (word (8 * k))` THEN
      ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_EXEC [3;4;6;7] (1--9) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; GSYM WORD_ADD] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ONCE_REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      GEN_REWRITE_TAC RAND_CONV
       [ARITH_RULE `q + (e * d1 + d0) + c * (e * a1 + a0):num =
                    e * (c * a1 + d1) + q + d0 + c * a0`] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (j + 1) = 64 * j + 64`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      GEN_REWRITE_TAC LAND_CONV
         [TAUT `k /\ q /\ r /\ s <=> k /\ r /\ q /\ s`] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DECARRY_RULE o CONJUNCTS) THEN
      ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC REAL_RING;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN VAL_INT64_TAC `j:num` THEN
      ARM_SIM_TAC BIGNUM_EMONTREDC_EXEC (1--2);
      ARM_SIM_TAC BIGNUM_EMONTREDC_EXEC (1--2)];
    ALL_TAC] THEN

  SUBGOAL_THEN `cout < 2` MP_TAC THENL
   [SUBGOAL_THEN `q * n + lowdigits a (k + i) < 2 EXP (64 * (k + i)) * 2`
    MP_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `x < e /\ y < e ==> x + y < e * 2`) THEN
      REWRITE_TAC[LOWDIGITS_BOUND] THEN
      REWRITE_TAC[ARITH_RULE `64 * (k + i) = 64 * i + 64 * k`] THEN
      ASM_SIMP_TAC[LT_MULT2; EXP_ADD];
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
      REWRITE_TAC[ARITH_RULE `64 * k + 64 * i = 64 * (i + k)`] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `a + b:num < c ==> a < c`)) THEN
      REWRITE_TAC[GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    GEN_REWRITE_TAC LAND_CONV [NUM_AS_BITVAL_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `tc:bool` SUBST_ALL_TAC)] THEN

  ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
  GHOST_INTRO_TAC `cin:bool` `read CF` THEN
  GHOST_INTRO_TAC `hin:int64` `read X8` THEN
  GHOST_INTRO_TAC `z2:num` `bignum_from_memory (z',k)` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `z2:num` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  ARM_ACCSIM_TAC BIGNUM_EMONTREDC_EXEC [1;2;4;5] (1--8) THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  EXISTS_TAC `2 EXP (64 * i) * r0 + r` THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXP_ADD; ARITH_RULE `64 * (i + 1) = 64 * i + 64`] THEN
    MATCH_MP_TAC(ARITH_RULE
      `q1 < e /\ q0 < ee /\ (q1 < e ==> (q1 + 1) * ee <= e * ee)
       ==> ee * q1 + q0 < ee * e`) THEN
     ASM_REWRITE_TAC[LE_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ] THEN
     ASM_REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`];
     ALL_TAC] THEN
  CONJ_TAC THENL
    [ALL_TAC;
     DISCH_THEN(fun th ->
       REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
       ASSUME_TAC th) THEN
     ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     ASM_REWRITE_TAC[EXP_LT_0; ARITH_EQ] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
      `ee * x + w + r = q + z
       ==> e divides ee /\ (w == q) (mod e) /\ (z == 0) (mod e)
           ==> (r == 0) (mod e)`)) THEN
     REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
       UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
       EXPAND_TAC "z2" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
       ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
       ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
       CONV_TAC NUMBER_RULE;
       UNDISCH_THEN `(w * z1) MOD 2 EXP 64 = q0` (SUBST1_TAC o SYM) THEN
       REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
       REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC(NUMBER_RULE
        `(n * w + 1 == 0) (mod e) ==> (z + (w * z) * n == 0) (mod e)`) THEN
       ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN `8 * k = 8 * ((k - 1) + 1)` SUBST1_TAC THENL
   [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES]] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM LEFT_ADD_DISTRIB] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 1 + k - 1 = k`] THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
  SUBGOAL_THEN `(i + 1) + (k - 1) = i + k` SUBST1_TAC THENL
   [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES] THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; ARITH_RULE `k + i + 1 = (k + i) + 1`] THEN
  REWRITE_TAC[ARITH_RULE `64 * (k + i) = 64 * k + 64 * i`; EXP_ADD] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check
   (can (term_match [] `2 EXP (64 * k) * x + y = z`) o concl))) THEN
  UNDISCH_TAC `read (memory :> bytes (z',8 * k)) s8 = z2` THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [BIGNUM_FROM_MEMORY_EXPAND] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; VAL_WORD_BITVAL; ADD_CLAUSES;
               BIGDIGIT_BOUND] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC REAL_RING);;

let BIGNUM_EMONTREDC_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc returnaddress.
        nonoverlapping (word pc,0x90) (z,8 * 2 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * 2 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k; z; m; w] s /\
                  bignum_from_memory (z,2 * val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = returnaddress /\
                  ((n * val w + 1 == 0) (mod (2 EXP 64))
                   ==> n * bignum_from_memory (z,val k) s + a =
                       2 EXP (64 * val k) *
                       (2 EXP (64 * val k) * val(C_RETURN s) +
                        bignum_from_memory
                          (word_add z (word(8 * val k)),val k) s)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(z,8 * 2 * val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_EMONTREDC_EXEC BIGNUM_EMONTREDC_CORRECT);;
(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof (ported from bignum_mul nested).     *)
(* ------------------------------------------------------------------------- *)
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;
let emontredc_full_spec,emontredc_public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_emontredc" subroutine_signatures)
    BIGNUM_EMONTREDC_SUBROUTINE_CORRECT
    BIGNUM_EMONTREDC_EXEC;;
let BIGNUM_EMONTREDC_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e k z m w pc returnaddress.
           nonoverlapping (word pc,144) (z,8 * 2 * val k) /\
           nonoverlapping (m,8 * val k) (z,8 * 2 * val k)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) bignum_emontredc_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [k; z; m; w] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events m z k pc returnaddress /\
                         memaccess_inbounds e2
                         [z,(2 * val k) * 8; m,val k * 8]
                         [z,(2 * val k) * 8]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (z,8 * 2 * val k)])`,
  ASSERT_CONCL_TAC emontredc_full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m:int64) (z:int64) (k:int64) (pc:num) (returnaddress:int64).
      if val k = 0 then
        f_ev_k0 m z k pc returnaddress
      else if val k = 1 then
        f_ev_k1 m z k pc returnaddress
      else
        APPEND
          (f_ev_outer_post m z k pc returnaddress)
          (APPEND
            (ENUMERATEL (val k)
              (\i.
                APPEND
                  (APPEND
                    (f_ev_outer_epil m z k pc returnaddress i)
                    (APPEND
                      (f_ev_inner_post m z k pc returnaddress i)
                      (APPEND
                        (ENUMERATEL (val k - 1)
                          (\j. f_ev_inner_inv m z k pc returnaddress i j))
                        (f_ev_inner_pre m z k pc returnaddress i))))
                  (f_ev_outer_prol m z k pc returnaddress i)))
            (f_ev_outer_pre m z k pc returnaddress))
      :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC (* e *) THEN
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `m:int64`; `w:int64`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_EMONTREDC_EXEC (1--2) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `8 * 2 * k < 2 EXP 64 /\ 8 * k < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [EVERY_ASSUM(fun th -> try MP_TAC (MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] NONOVERLAPPING_IMP_SMALL_2) th) with Failure _ -> ALL_TAC) THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  (*** k=1 top-level case: single outer iteration, montloop skipped (CBZ@0x30 taken->0x60),
       STRAIGHT-LINE (no loop) 0x0->RET. Keeps the general arm free of the k=1-vs-k>1 CBZ branch
       (which, inside the per-iteration witness, is incompatible with outer-prol's DISCHARGE_MEMACCESS). ***)
  ASM_CASES_TAC `k = 1` THENL
   [
    ASM_REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_EMONTREDC_EXEC (1--25) THEN
    CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  (*** General arm k>=2: collapse the witness `else if val k=1` to the general branch. ***)
  SUBGOAL_THEN `~(val(word k:int64) = 1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (*** Outer loop setup. NB UP2 exit = fall-through PC AFTER the backedge BCC (0x84->0xc),
       i.e. 0x88 (MOV X0 X7) - NOT correctness's plain-UP pc2=0x80 (the CMP). The UP2 event
       tactic folds the backedge into the body, so pc2 must be past it. (cf. bignum_mul SAFE:
       correctness 0x78 -> SAFE UP2 0x80, "+8"). ***)
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0xc` `pc + 0x88`
   `\i s. read X0 s = word k /\
          read X1 s = word_add z (word(8 * i)) /\
          read X2 s = m /\
          read X3 s = w /\
          read X4 s = word i /\
          read X30 s = returnaddress` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* outer pre: 0x0 -> 0xc, 3 steps (CBZ-not-taken, MOV X7, MOV X4) *)
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_EMONTREDC_EXEC (1--3) THEN
    ASM_REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    (* outer body *)
    ALL_TAC;
    (* outer post: 0x88 reached with i=k; 2 steps (MOV X0 X7, RET) -> PC=returnaddress. *)
    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_EMONTREDC_EXEC (1--2) THEN
    CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  (*** Outer loop invariant ***)
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[ENUMERATEL_ADD1] THEN
  REWRITE_TAC[METIS[APPEND_ASSOC]
      `(exists e2. P e2 /\
        e2 = APPEND (APPEND (APPEND a f_ev_outer_prol) enumc) tail /\ Q e2)
       <=>
       (exists e2. P e2 /\
        e2 = APPEND a (APPEND f_ev_outer_prol (APPEND enumc tail)) /\ Q e2)`] THEN
  (*** Outer prologue: 0xc -> 0x34 (ABSORBS the CBZ X11@0x30 not-taken, since k>=2 => k-1>=1).
       This makes the inner-loop pre-leg 0 steps (f_ev_inner_pre:=[]), avoiding the inner-pre
       memaccess/unify issues entirely. ***)
  SUBGOAL_THEN `~(val(word(k - 1):int64) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x34`
   `\s. read X0 s = word k /\
        read X1 s = word_add z (word(8 * i)) /\
        read X2 s = m /\
        read X3 s = w /\
        read X4 s = word i /\
        read X5 s = word 1 /\
        read X11 s = word(k - 1) /\
        read X30 s = returnaddress` THEN
  SUBGOAL_THEN `word_sub (word k) (word 1):int64 = word(k - 1)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
     [REFL_TAC; POP_ASSUM MP_TAC THEN SIMPLE_ARITH_TAC]; ALL_TAC] THEN
  CONJ_TAC THENL
   [
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_EMONTREDC_EXEC (1--10) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  (*** Outer epilogue break at 0x60 ***)
  REWRITE_TAC[] THEN
  REWRITE_TAC[METIS[APPEND_ASSOC]
      `(exists e2. P e2 /\ e2 = APPEND (APPEND f_ev_outer_epil a) tail /\ Q e2)
       <=>
       (exists e2. P e2 /\ e2 = APPEND f_ev_outer_epil (APPEND a tail) /\ Q e2)`] THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x60`
   `\s. read X0 s = word k /\
        read X1 s = word_add z (word(8 * i)) /\
        read X2 s = m /\
        read X3 s = w /\
        read X4 s = word i /\
        read X30 s = returnaddress` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    (* outer epilogue 0x60 -> {0xc if i+1<k else 0x88}: ...,CMP X4 X0,BCC = 10 steps (madd-style). *)
    SUBGOAL_THEN `word_add (word_add z (word(8 * i))) (word 8):int64 =
                  word_add z (word(8 * (i + 1)))` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_EMONTREDC_EXEC (1--10) THEN
    CONJ_TAC THENL
     [MAP_EVERY VAL_INT64_TAC [`i:num`;`1`] THEN
      IMP_REWRITE_TAC[VAL_WORD_ADD;DIMINDEX_64;MOD_LT;GSYM COND_RAND] THEN
      SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    (* z'[k] computed write/read at word_add(word_add z(8*i))(8*k): normalize to word_add z(8*(i+k))
       so DISCHARGE_CONCRETE sees a single base+offset. in-bounds needs 8*(i+k)+8 <= 2k*8 i.e. i<k. *)
    SUBGOAL_THEN `word_add (word_add z (word(8 * i))) (word(8 * k)):int64 =
                  word_add z (word(8 * (i + k)))` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `8 * (i + k) = 8 * i + 8 * k`] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ] THEN
    REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
    REWRITE_TAC[CONJUNCT2 APPEND] THEN
    CONV_TAC ((RATOR_CONV o RATOR_CONV o RAND_CONV) CONS_TO_APPEND_CONV) THEN
    GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
    CONJ_TAC THENL
     [DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC;
      DISCHARGE_MEMACCESS_INBOUNDS_TAC]] THEN
  (*** Montgomery inner loop setup (k>=2, both k=0 and k=1 handled top-level). Loop-top 0x34 =
       prologue-SEQUENCE end, so inner-pre is 0 steps. ***)
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `0 < k - 1 /\ 1 < k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k - 1` `pc + 0x34` `pc + 0x60`
   `\j s. read X0 s = word k /\
          read X1 s = word_add z (word(8 * i)) /\
          read X2 s = m /\
          read X3 s = w /\
          read X4 s = word i /\
          read X5 s = word(1 + j) /\
          read X30 s = returnaddress` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* count *)
    SIMPLE_ARITH_TAC;
    (* inner precond: loop-top 0x34 reached by prologue SEQUENCE -> 0 steps. f_ev_inner_pre:=[]. *)
    REWRITE_TAC[SUB_0; ADD_0; ENUMERATEL; CONJUNCT1 APPEND; APPEND_NIL] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_EMONTREDC_EXEC [] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 + 0 = 1`] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    (* inner body *)
    ALL_TAC;
    (* inner postcond: exit 0x60 = outer-epil SEQUENCE boundary -> 0 steps. f_ev_inner_post:=[]
       (e_back, no exit events - SUB+CBNZ folded into body). f_ev_inner_pre already []; collapse the
       trailing APPEND _ [] then bare DISCHARGE (NIL case: APPEND (f_ev) l = l). *)
    REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_EMONTREDC_EXEC [] THEN
    REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND] THEN
    (* e_back f_ev_inner_post must be []: RHS `APPEND (APPEND f_ev_inner_post ENUM) REST`; GSYM
       APPEND_ASSOC -> `APPEND f_ev_inner_post (APPEND ENUM REST)` = `APPEND f_ev_inner_post LHS`,
       then FULL_UNIFY NIL case `l = APPEND (f_ev) l` assigns f_ev_inner_post:=[]. *)
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  (*** Inner loop body: 0x34 -> {0x34 if j+1<k-1 else 0x60}, index j, reads m[1+j], z'[1+j].
       11 steps THROUGH the SUB(0x58)+CBNZ(0x5c) backedge. ***)
  REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ENUMERATEL_ADD1] THEN
  (* reassoc so the fresh f_ev_inner_inv is the peelable head (tail = ENUMERATEL j ++ rest). *)
  REWRITE_TAC[METIS[APPEND_ASSOC]
      `(exists e2. P e2 /\
        e2 = APPEND (APPEND fresh enumc) tail /\ Q e2)
       <=>
       (exists e2. P e2 /\
        e2 = APPEND fresh (APPEND enumc tail) /\ Q e2)`] THEN
  SUBGOAL_THEN `1 + j < k /\ val(word(1 + j):int64) = 1 + j` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [SIMPLE_ARITH_TAC; IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j + 1 = k - 1 <=> ~(j + 1 < k - 1))` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word_add z (word(8 * i))) (word(8 * (1 + j))):int64 =
                word_add z (word(8 * (i + (1 + j))))` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * (i + (1 + j)) = 8 * i + 8 * (1 + j)`] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false BIGNUM_EMONTREDC_EXEC (1--11) THEN
  (* Normalise SIM's X5 = word_add (word(1+j)) (word 1) to word((1+j)+1). *)
  SUBGOAL_THEN `word_add (word(1 + j):int64) (word 1) = word((1 + j) + 1)` ASSUME_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* CBNZ cond-equivalence: ~(val(word_sub (word((1+j)+1)) (word k))=0) <=> j+1<k-1 *)
  SUBGOAL_THEN
   `(~(val(word_sub (word((1 + j) + 1):int64) (word k)) = 0) <=> j + 1 < k - 1)`
   ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    MAP_EVERY VAL_INT64_TAC [`(1 + j) + 1`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* PC conjunct (its own branch): SIM cond -> j+1<k-1 (asm equiv), then GSYM COND_RAND pulls word
     out so both sides are word(if j+1<k-1 then..); REFL. Keeps the e2 single (no goal-wide COND lift). *)
  CONJ_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM COND_RAND] THEN
    ASM_REWRITE_TAC[] THEN REFL_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ] THEN
  REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
  REWRITE_TAC[CONJUNCT2 APPEND] THEN
  CONV_TAC ((RATOR_CONV o RATOR_CONV o RAND_CONV) CONS_TO_APPEND_CONV) THEN
  GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
  CONJ_TAC THENL
   [DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC;
    DISCHARGE_MEMACCESS_INBOUNDS_TAC]);;
