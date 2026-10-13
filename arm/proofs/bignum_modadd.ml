(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Modular addition of bignums.                                              *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_modadd.o";;
 ****)

let bignum_modadd_mc =
  define_assert_from_elf "bignum_modadd_mc" "arm/generic/bignum_modadd.o"
[
  0xab1f0006;       (* arm_ADDS X6 X0 XZR *)
  0x540003c0;       (* arm_BEQ (word 120) *)
  0xab1f03e5;       (* arm_ADDS X5 XZR XZR *)
  0xf8656847;       (* arm_LDR X7 X2 (Register_Offset X5) *)
  0xf8656868;       (* arm_LDR X8 X3 (Register_Offset X5) *)
  0xba0800e7;       (* arm_ADCS X7 X7 X8 *)
  0xf8256827;       (* arm_STR X7 X1 (Register_Offset X5) *)
  0x910020a5;       (* arm_ADD X5 X5 (rvalue (word 8)) *)
  0xd10004c6;       (* arm_SUB X6 X6 (rvalue (word 1)) *)
  0xb5ffff46;       (* arm_CBNZ X6 (word 2097128) *)
  0x9a9f37e9;       (* arm_CSET X9 Condition_CS *)
  0xaa0003e6;       (* arm_MOV X6 X0 *)
  0xeb1f03e5;       (* arm_NEGS X5 XZR *)
  0xf8656827;       (* arm_LDR X7 X1 (Register_Offset X5) *)
  0xf8656888;       (* arm_LDR X8 X4 (Register_Offset X5) *)
  0xfa0800ff;       (* arm_SBCS XZR X7 X8 *)
  0x910020a5;       (* arm_ADD X5 X5 (rvalue (word 8)) *)
  0xd10004c6;       (* arm_SUB X6 X6 (rvalue (word 1)) *)
  0xb5ffff66;       (* arm_CBNZ X6 (word 2097132) *)
  0xfa1f0129;       (* arm_SBCS X9 X9 XZR *)
  0xaa2903e9;       (* arm_ORN X9 XZR X9 *)
  0xaa0003e6;       (* arm_MOV X6 X0 *)
  0xeb1f03e5;       (* arm_NEGS X5 XZR *)
  0xf8656827;       (* arm_LDR X7 X1 (Register_Offset X5) *)
  0xf8656888;       (* arm_LDR X8 X4 (Register_Offset X5) *)
  0x8a090108;       (* arm_AND X8 X8 X9 *)
  0xfa0800e7;       (* arm_SBCS X7 X7 X8 *)
  0xf8256827;       (* arm_STR X7 X1 (Register_Offset X5) *)
  0x910020a5;       (* arm_ADD X5 X5 (rvalue (word 8)) *)
  0xd10004c6;       (* arm_SUB X6 X6 (rvalue (word 1)) *)
  0xb5ffff26;       (* arm_CBNZ X6 (word 2097124) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MODADD_EXEC = ARM_MK_EXEC_RULE bignum_modadd_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MODADD_CORRECT = prove
 (`!k z x y m a b n pc.
        nonoverlapping (word pc,0x80) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_modadd_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = word(pc + 0x7c) /\
                  bignum_from_memory (z,val k) s = (a + b) MOD n)
             (MAYCHANGE [PC; X5; X6; X7; X8; X9] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `m:int64`] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`;` n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (BIGNUM_TERMRANGE_TAC `k:num`) [`a:num`; `b:num`; `n:num`] THEN

  (*** Deal with degenerate case k = 0 first ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`))) THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; ADD_CLAUSES; MOD_0] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODADD_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  MP_TAC(ASSUME
   `nonoverlapping_modulo (2 EXP 64) (pc,128) (val(z:int64),8 * k)`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** First addition, addloop ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0xc` `pc + 0x24`
    `\i s. read X0 s = word k /\
           read X1 s = z /\
           read X2 s = x /\
           read X3 s = y /\
           read X4 s = m /\
           bignum_from_memory (m,k) s = n /\
           read X5 s = word(8 * i) /\
           read X6 s = word(k - i) /\
           bignum_from_memory (word_add x (word(8 * i)),k - i) s =
           highdigits a i /\
           bignum_from_memory (word_add y (word(8 * i)),k - i) s =
           highdigits b i /\
           2 EXP (64 * i) * bitval(read CF s) + bignum_from_memory(z,i) s =
           lowdigits a i + lowdigits b i` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODADD_EXEC (1--3) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cin:bool` `read CF` THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     ARM_ACCSTEPS_TAC BIGNUM_MODADD_EXEC [3] (1--6) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [CONV_TAC WORD_RULE;
       REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
       GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
       ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
       REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
     ONCE_REWRITE_TAC[ARITH_RULE
      `(a' + a) + (b' + b):num = (a' + b') + a + b`] THEN
     FIRST_X_ASSUM(fun th ->
       GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
     ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
     SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
     REWRITE_TAC[ARITH_RULE `64 * (n + 1) = 64 * n + 64`; EXP_ADD] THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC REAL_RING;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODADD_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN
     VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** Comparison operation "cmploop" ***)

  GHOST_INTRO_TAC `hi:bool` `read CF` THEN
  GHOST_INTRO_TAC `lo:num` `bignum_from_memory(z,k)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `lo:num` THEN

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x34` `pc + 0x48`
    `\i s. read X0 s = word k /\
           read X1 s = z /\
           read X4 s = m /\
           bignum_from_memory (z,k) s = lo /\
           bignum_from_memory (m,k) s = n /\
           read X5 s = word(8 * i) /\
           read X6 s = word(k - i) /\
           read X9 s = word(bitval hi) /\
           bignum_from_memory (word_add z (word(8 * i)),k - i) s =
           highdigits lo i /\
           bignum_from_memory (word_add m (word(8 * i)),k - i) s =
           highdigits n i /\
           (read CF s <=> lowdigits n i <= lowdigits lo i)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODADD_EXEC (1--4) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; LE_REFL; COND_SWAP] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; GSYM WORD_BITVAL];

     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cin:bool` `read CF` THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     ARM_STEPS_TAC BIGNUM_MODADD_EXEC (1--5) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [CONV_TAC WORD_RULE;
       REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
       GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
       ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
       REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
     SIMP_TAC[LEXICOGRAPHIC_LE; LOWDIGITS_BOUND] THEN
     SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
     POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN ARITH_TAC;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODADD_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN
     VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** Masked subtraction operation "subloop" ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x5c` `pc + 0x78`
    `\i s. read X0 s = word k /\
           read X1 s = z /\
           read X4 s = m /\
           read X5 s = word(8 * i) /\
           read X6 s = word(k - i) /\
           read X9 s = word_neg(word(bitval(n <= a + b))) /\
           bignum_from_memory (word_add z (word(8 * i)),k - i) s =
           highdigits lo i /\
           bignum_from_memory (word_add m (word(8 * i)),k - i) s =
           highdigits n i /\
           &(bignum_from_memory(z,i) s):real =
           &2 pow (64 * i) * &(bitval(~read CF s)) +
           &(lowdigits lo i) - &(bitval(n <= a + b)) * &(lowdigits n i)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODADD_EXEC (1--5) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BITVAL_CLAUSES] THEN
     CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
     SUBGOAL_THEN
      `n <= a + b <=>
       2 EXP (64 * k) * 0 + n <= 2 EXP (64 * k) * bitval hi + lo`
     SUBST1_TAC THENL
      [ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES];
       ASM_SIMP_TAC[LEXICOGRAPHIC_LE; EXP_LT_0; ARITH_EQ; GSYM NOT_LE]] THEN
     MAP_EVERY ASM_CASES_TAC [`hi:bool`; `n:num <= lo`] THEN
     ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
     CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
     CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP (ARITH_RULE
      `e * c + lo:num = a + b
       ==> !n. e * 1 <= e * c /\ n < e /\ n <= lo /\ a < n /\ b < n
               ==> F`)) THEN
     ASM_REWRITE_TAC[BITVAL_CLAUSES; LE_REFL];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cin:bool` `read CF` THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     ARM_ACCSTEPS_TAC BIGNUM_MODADD_EXEC [4] (1--7) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
      [CONV_TAC WORD_RULE;
       REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
       GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
       ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
       REWRITE_TAC[NOT_LT];
       REWRITE_TAC[LOWDIGITS_CLAUSES]] THEN
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
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODADD_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN
     VAL_INT64_TAC `k - i:num` THEN ASM_REWRITE_TAC[SUB_EQ_0; NOT_LE];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** The finale ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_MODADD_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOD_CASES; ARITH_RULE `m < p /\ n < p ==> m + n < 2 * p`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_ADD; GSYM NOT_LT] THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * k`; `&0:real`] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES; BIGNUM_FROM_MEMORY_BOUND; LE_0] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; INTEGER_CLOSED] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`a:num < n`; `b:num < n`; `n < 2 EXP (64 * k)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `2 EXP (64 * k) * bitval hi + lo = a + b` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; GSYM REAL_OF_NUM_CLAUSES]] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
   `e * c + lo:real = a + b ==> lo = e * --c + a + b`)) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  REWRITE_TAC[real_sub; GSYM REAL_ADD_ASSOC] THEN
  REWRITE_TAC[REAL_FIELD
   `(&2 pow e * h + l) / &2 pow e = h + l / &2 pow e`] THEN
  REAL_INTEGER_TAC);;

let BIGNUM_MODADD_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc returnaddress.
        nonoverlapping (word pc,0x80) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_modadd_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = returnaddress /\
                  bignum_from_memory (z,val k) s = (a + b) MOD n)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_MODADD_EXEC BIGNUM_MODADD_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let modadd_full_spec,modadd_public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_modadd" subroutine_signatures)
    BIGNUM_MODADD_SUBROUTINE_CORRECT
    BIGNUM_MODADD_EXEC;;

(* Canonical form of the loops' back-branch condition: the down-counter
   CBNZ at each loop tail jumps back iff k-(i+1) is nonzero, i.e. iff i+1<k.
   Used to align the recorded EventJump targets of already-processed loops
   with the i+1<k form produced by ENSURES_EVENTS_WHILE_UP2_TAC. *)

let BIGNUM_MODADD_JUMPC = ARITH_RULE `~(k - (i + 1) = 0) <=> i + 1 < k`;;

(* Discharge for the later loops, which first canonicalizes the (concrete)
   trace in both the goal and the memaccess assumptions. The earlier loops'
   back-branch EventJumps are recorded by ENSURES_EVENTS_WHILE_UP2_TAC as an
   applied lambda carrying `val(word k)`; beta-reducing, then rewriting
   `val(word k) = k` (supplied as vwk, also under the ENUMERATEL lambdas) and
   BIGNUM_MODADD_JUMPC brings them into the same `i + 1 < k` form as the freshly
   simulated head, so DISCHARGE_MEMACCESS_INBOUNDS_TAC can match them. *)

let BIGNUM_MODADD_DISCHARGE_TAC vwk =
  GEN_DISCHARGE_SAFETY_PROPERTY_TAC
   (CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV GEN_BETA_CONV)) THEN
    CONV_TAC(TOP_DEPTH_CONV(REWR_CONV vwk)) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV(REWR_CONV vwk))) THEN
    CONV_TAC(TOP_DEPTH_CONV(REWR_CONV BIGNUM_MODADD_JUMPC)) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV(REWR_CONV BIGNUM_MODADD_JUMPC))));;

(* The function skips all three loops to the return when k = 0; otherwise it
   runs three sequential k-iteration loops (add, compare, masked subtract).
   Each case is proved as its own lemma to avoid sharing the f_events
   metavariable, then the two are combined. *)

let BIGNUM_MODADD_SAFE_K0 = prove
 (`exists f_events.
       forall e k z x y m pc returnaddress.
           nonoverlapping (word pc,128) (z,8 * val k) /\
           nonoverlapping (m,8 * val k) (z,8 * val k) /\
           (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
           (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k)) /\
           val k = 0
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) bignum_modadd_mc /\
                    read PC s = word pc /\ read X30 s = returnaddress /\
                    C_ARGUMENTS [k; z; x; y; m] s /\ read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2. read events s = APPEND e2 e /\
                        e2 = f_events x y m z k pc returnaddress /\
                        memaccess_inbounds e2
                          [x,val k * 8; y,val k * 8; m,val k * 8; z,val k * 8]
                          [z,val k * 8])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bignum (z,val k)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (y:int64) (m:int64) (z:int64) (k:int64) (pc:num) (returnaddress:int64).
      f_ev_k0 x y m z k pc returnaddress :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN X_GEN_TAC `e:(uarch_event)list` THEN
  W64_GEN_TAC `k:num` THEN MAP_EVERY X_GEN_TAC [`z:int64`;`x:int64`;`y:int64`;`m:int64`] THEN
  MAP_EVERY X_GEN_TAC [`pc:num`;`returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_MODADD_EXEC; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
    BIGNUM_MODADD_EXEC (1--3) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let BIGNUM_MODADD_SAFE_KGT = prove
 (`exists f_events.
       forall e k z x y m pc returnaddress.
           nonoverlapping (word pc,128) (z,8 * val k) /\
           nonoverlapping (m,8 * val k) (z,8 * val k) /\
           (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
           (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k)) /\
           ~(val k = 0)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) bignum_modadd_mc /\
                    read PC s = word pc /\ read X30 s = returnaddress /\
                    C_ARGUMENTS [k; z; x; y; m] s /\ read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2. read events s = APPEND e2 e /\
                        e2 = f_events x y m z k pc returnaddress /\
                        memaccess_inbounds e2
                          [x,val k * 8; y,val k * 8; m,val k * 8; z,val k * 8]
                          [z,val k * 8])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bignum (z,val k)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (y:int64) (m:int64) (z:int64) (k:int64) (pc:num) (returnaddress:int64).
      APPEND (APPEND (APPEND
            (APPEND (f_ev_s3_post x y m z k pc returnaddress)
               (APPEND (ENUMERATEL (val k) (f_ev_s3_loop x y m z k pc returnaddress))
                       (f_ev_s3_pre x y m z k pc returnaddress)))
            (APPEND (ENUMERATEL (val k) (f_ev_s2_loop x y m z k pc returnaddress))
                    (f_ev_s2_pre x y m z k pc returnaddress)))
          (APPEND (ENUMERATEL (val k) (f_ev_s1_loop x y m z k pc returnaddress))
                  (f_ev_s1_pre x y m z k pc returnaddress)))
        (f_ev_begin x y m z k pc returnaddress) :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN X_GEN_TAC `e:(uarch_event)list` THEN
  W64_GEN_TAC `k:num` THEN MAP_EVERY X_GEN_TAC [`z:int64`;`x:int64`;`y:int64`;`m:int64`] THEN
  MAP_EVERY X_GEN_TAC [`pc:num`;`returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES;
              fst BIGNUM_MODADD_EXEC; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `8 * k < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [EVERY_ASSUM(fun th -> try MP_TAC (MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      NONOVERLAPPING_IMP_SMALL_2) th) with Failure _ -> ALL_TAC) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k <= 0)` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  (* Skip the initial ADDS/BEQ/ADDS preamble to the first loop head. *)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xc`
   `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = x /\ read X3 s = y /\
        read X4 s = m /\ read X5 s = word 0 /\ read X6 s = word k /\
        read X30 s = returnaddress` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_MODADD_EXEC (1--3) THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  (* addloop: pc+0xc .. pc+0x28 *)
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0xc` `pc + 0x28`
   `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = x /\ read X3 s = y /\
          read X4 s = m /\ read X5 s = word(8 * i) /\ read X6 s = word(k - i) /\
          read X30 s = returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[SUB_0; MULT_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_MODADD_EXEC [] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `i:num` THEN REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_MODADD_EXEC (1--7) THEN
    SUBGOAL_THEN `word_sub (word(k - i):int64) (word 1) = word(k - (i + 1))` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= k - i <=> i < k`]; ALL_TAC] THEN
    SUBGOAL_THEN `val(word(k - (i + 1)):int64) = k - (i + 1)` ASSUME_TAC THENL
     [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `k - (i + 1) = 0 <=> ~(i + 1 < k)`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [GSYM APPEND_ASSOC] THEN
  (* cmploop: pc+0x34 .. pc+0x4c (preceded by 3-instr glue) *)
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x34` `pc + 0x4c`
   `\i s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\
          read X5 s = word(8 * i) /\ read X6 s = word(k - i) /\
          read X30 s = returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[SUB_0; MULT_CLAUSES; ADD_0] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_MODADD_EXEC (1--3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_MODADD_JUMPC]) THEN REWRITE_TAC[BIGNUM_MODADD_JUMPC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `i:num` THEN REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_MODADD_EXEC (1--6) THEN
    SUBGOAL_THEN `word_sub (word(k - i):int64) (word 1) = word(k - (i + 1))` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= k - i <=> i < k`]; ALL_TAC] THEN
    SUBGOAL_THEN `val(word(k - (i + 1)):int64) = k - (i + 1)` ASSUME_TAC THENL
     [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `k - (i + 1) = 0 <=> ~(i + 1 < k)`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN CONV_TAC WORD_RULE;
      BIGNUM_MODADD_DISCHARGE_TAC (ASSUME `val(word k:int64) = k`)];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [GSYM APPEND_ASSOC] THEN
  (* subloop: pc+0x5c .. pc+0x7c (preceded by 4-instr glue), then final RET *)
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x5c` `pc + 0x7c`
   `\i s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\
          read X5 s = word(8 * i) /\ read X6 s = word(k - i) /\
          read X30 s = returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[SUB_0; MULT_CLAUSES; ADD_0] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_MODADD_EXEC (1--4) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_MODADD_JUMPC]) THEN REWRITE_TAC[BIGNUM_MODADD_JUMPC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `i:num` THEN REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_MODADD_EXEC (1--8) THEN
    SUBGOAL_THEN `word_sub (word(k - i):int64) (word 1) = word(k - (i + 1))` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `k - (i + 1) = k - i - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= k - i <=> i < k`]; ALL_TAC] THEN
    SUBGOAL_THEN `val(word(k - (i + 1)):int64) = k - (i + 1)` ASSUME_TAC THENL
     [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `k - (i + 1) = 0 <=> ~(i + 1 < k)`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN CONV_TAC WORD_RULE;
      BIGNUM_MODADD_DISCHARGE_TAC (ASSUME `val(word k:int64) = k`)];
    REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k <= 0) ==> k - k = 0`] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      BIGNUM_MODADD_EXEC (1--1) THEN
    SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    BIGNUM_MODADD_DISCHARGE_TAC (ASSUME `val(word k:int64) = k`)]);;

let BIGNUM_MODADD_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e k z x y m pc returnaddress.
           nonoverlapping (word pc,128) (z,8 * val k) /\
           nonoverlapping (m,8 * val k) (z,8 * val k) /\
           (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
           (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k))
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) bignum_modadd_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [k; z; x; y; m] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x y m z k pc returnaddress /\
                         memaccess_inbounds e2
                         [x,val k * 8; y,val k * 8; m,val k * 8; z,val k * 8]
                         [z,val k * 8]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bignum (z,val k)])`,
  ASSERT_CONCL_TAC modadd_full_spec THEN
  X_CHOOSE_TAC
    `fk0:int64->int64->int64->int64->int64->num->int64->(uarch_event)list`
    BIGNUM_MODADD_SAFE_K0 THEN
  X_CHOOSE_TAC
    `fkg:int64->int64->int64->int64->int64->num->int64->(uarch_event)list`
    BIGNUM_MODADD_SAFE_KGT THEN
  EXISTS_TAC
   `\(x:int64) (y:int64) (m:int64) (z:int64) (k:int64) (pc:num) (returnaddress:int64).
      (if val k = 0 then fk0 x y m z k pc returnaddress
       else fkg x y m z k pc returnaddress):(uarch_event)list` THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`;`k:int64`;`z:int64`;`x:int64`;`y:int64`;`m:int64`;
    `pc:num`;`returnaddress:int64`] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `val(k:int64) = 0` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL
        [`e:(uarch_event)list`;`k:int64`;`z:int64`;`x:int64`;`y:int64`;`m:int64`;
         `pc:num`;`returnaddress:int64`]
        (check(fun th -> free_in
          `fk0:int64->int64->int64->int64->int64->num->int64->(uarch_event)list`
          (concl th)) th))) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL
        [`e:(uarch_event)list`;`k:int64`;`z:int64`;`x:int64`;`y:int64`;`m:int64`;
         `pc:num`;`returnaddress:int64`]
        (check(fun th -> free_in
          `fkg:int64->int64->int64->int64->int64->num->int64->(uarch_event)list`
          (concl th)) th))) THEN
    ASM_REWRITE_TAC[]]);;
