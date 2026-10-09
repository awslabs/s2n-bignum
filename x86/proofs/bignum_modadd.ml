(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Modular addition of bignums.                                              *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_modadd.o";;
 ****)

let bignum_modadd_mc =
  define_assert_from_elf "bignum_modadd_mc" "x86/generic/bignum_modadd.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x5a;              (* JE (Imm8 (word 90)) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x49; 0x89; 0xfa;        (* MOV (% r10) (% rdi) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4a; 0x8b; 0x04; 0xca;  (* MOV (% rax) (Memop Quadword (%%% (rdx,3,r9))) *)
  0x4a; 0x13; 0x04; 0xc9;  (* ADC (% rax) (Memop Quadword (%%% (rcx,3,r9))) *)
  0x4a; 0x89; 0x04; 0xce;  (* MOV (Memop Quadword (%%% (rsi,3,r9))) (% rax) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0xff; 0xca;        (* DEC (% r10) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0x49; 0x83; 0xd3; 0x00;  (* ADC (% r11) (Imm8 (word 0)) *)
  0x49; 0x89; 0xfa;        (* MOV (% r10) (% rdi) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4a; 0x8b; 0x04; 0xce;  (* MOV (% rax) (Memop Quadword (%%% (rsi,3,r9))) *)
  0x4b; 0x1b; 0x04; 0xc8;  (* SBB (% rax) (Memop Quadword (%%% (r8,3,r9))) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0xff; 0xca;        (* DEC (% r10) *)
  0x75; 0xf0;              (* JNE (Imm8 (word 240)) *)
  0x49; 0x83; 0xdb; 0x00;  (* SBB (% r11) (Imm8 (word 0)) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4b; 0x8b; 0x04; 0xc8;  (* MOV (% rax) (Memop Quadword (%%% (r8,3,r9))) *)
  0x4c; 0x21; 0xd8;        (* AND (% rax) (% r11) *)
  0x49; 0xf7; 0xda;        (* NEG (% r10) *)
  0x4a; 0x19; 0x04; 0xce;  (* SBB (Memop Quadword (%%% (rsi,3,r9))) (% rax) *)
  0x4d; 0x19; 0xd2;        (* SBB (% r10) (% r10) *)
  0x49; 0xff; 0xc1;        (* INC (% r9) *)
  0x49; 0x39; 0xf9;        (* CMP (% r9) (% rdi) *)
  0x72; 0xe7;              (* JB (Imm8 (word 231)) *)
  0xc3                     (* RET *)
];;

let bignum_modadd_tmc = define_trimmed "bignum_modadd_tmc" bignum_modadd_mc;;

let BIGNUM_MODADD_EXEC = X86_MK_CORE_EXEC_RULE bignum_modadd_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MODADD_CORRECT = prove
 (`!k z x y m a b n pc.
        nonoverlapping (word pc,0x60) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_modadd_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = word(pc + 0x5f) /\
                  bignum_from_memory (z,val k) s = (a + b) MOD n)
             (MAYCHANGE [RIP; RAX; R9; R10; R11] ,,
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
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  MP_TAC(ASSUME
   `nonoverlapping_modulo (2 EXP 64) (pc,96) (val(z:int64),8 * k)`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** First addition, addloop ***)

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0xe` `pc + 0x20`
    `\i s. (read RDI s = word k /\
            read RSI s = z /\
            read RDX s = x /\
            read RCX s = y /\
            read R8 s = m /\
            bignum_from_memory (m,k) s = n /\
            read R9 s = word i /\
            read R10 s = word(k - i) /\
            read R11 s = word 0 /\
            bignum_from_memory (word_add x (word(8 * i)),k - i) s =
            highdigits a i /\
            bignum_from_memory (word_add y (word(8 * i)),k - i) s =
            highdigits b i /\
            2 EXP (64 * i) * bitval(read CF s) + bignum_from_memory(z,i) s =
            lowdigits a i + lowdigits b i) /\
           (read ZF s <=> i = k)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--5) THEN
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
     X86_ACCSTEPS_TAC BIGNUM_MODADD_EXEC [2] (1--5) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WORD_ADD] THEN REPEAT CONJ_TAC THENL
      [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
       GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
       ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
       REWRITE_TAC[LOWDIGITS_CLAUSES];
       REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
       VAL_INT64_TAC `k - i:num` THEN
       ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_1] THEN ARITH_TAC] THEN
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
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** Comparison operation "cmploop" ***)

  GHOST_INTRO_TAC `hi:bool` `read CF` THEN
  GHOST_INTRO_TAC `lo:num` `bignum_from_memory(z,k)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `lo:num` THEN

  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x2c` `pc + 0x3a`
    `\i s. (read RDI s = word k /\
            read RSI s = z /\
            read R8 s = m /\
            bignum_from_memory (z,k) s = lo /\
            bignum_from_memory (m,k) s = n /\
            read R9 s = word i /\
            read R10 s = word(k - i) /\
            read R11 s = word(bitval hi) /\
            bignum_from_memory (word_add z (word(8 * i)),k - i) s =
            highdigits lo i /\
            bignum_from_memory (word_add m (word(8 * i)),k - i) s =
            highdigits n i /\
            (read CF s <=> lowdigits lo i < lowdigits n i)) /\
           (read ZF s <=> i = k)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--4) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; LT_REFL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0];
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     GHOST_INTRO_TAC `cin:bool` `read CF` THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--4) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WORD_ADD] THEN REPEAT CONJ_TAC THENL
      [REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
       GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
       ASM_REWRITE_TAC[ARITH_RULE `1 <= p - n <=> n < p`];
       REWRITE_TAC[LOWDIGITS_CLAUSES];
       REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
       VAL_INT64_TAC `k - i:num` THEN
       ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_1] THEN ARITH_TAC] THEN
     SIMP_TAC[LEXICOGRAPHIC_LT; LOWDIGITS_BOUND] THEN
     SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
     POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bitval] THEN ARITH_TAC;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC [1] THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** Masked subtraction operation "subloop" ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x46` `pc + 0x5a`
    `\i s. read RDI s = word k /\
           read RSI s = z /\
           read R8 s = m /\
           read R9 s = word i /\
           val(word_neg(read R10 s)) <= 1 /\
           read R11 s = word_neg(word(bitval(n <= a + b))) /\
           bignum_from_memory (word_add z (word(8 * i)),k - i) s =
           highdigits lo i /\
           bignum_from_memory (word_add m (word(8 * i)),k - i) s =
           highdigits n i /\
           &(bignum_from_memory(z,i) s):real =
           &2 pow (64 * i) * &(val(word_neg(read R10 s))) +
           &(lowdigits lo i) - &(bitval(n <= a + b)) * &(lowdigits n i)` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--4) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0] THEN
     REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
     ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
     REWRITE_TAC[WORD_NEG_0; VAL_WORD_0; LE_0] THEN
     CONV_TAC REAL_RAT_REDUCE_CONV THEN
     ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
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
     GHOST_INTRO_TAC `cval:num` `\s. val(word_neg(read R10 s))` THEN
     GLOBALIZE_PRECONDITION_TAC THEN
     FIRST_X_ASSUM(X_CHOOSE_THEN `cin:bool` SUBST_ALL_TAC o
       GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
     REWRITE_TAC[VAL_EQ_BITVAL] THEN
     REWRITE_TAC[WORD_RULE `word_neg x:int64 = y <=> x = word_neg y`] THEN
     GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
      [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
     ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
     REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
     ENSURES_INIT_TAC "s0" THEN
     X86_ACCSTEPS_TAC BIGNUM_MODADD_EXEC [4] (1--6) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
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
     ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[LOWDIGITS_SELF; HIGHDIGITS_ZERO; SUB_REFL] THEN
     REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL]] THEN

  (*** The finale ***)

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
  ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MODADD_EXEC (1--2) THEN
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

let BIGNUM_MODADD_NOIBT_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_modadd_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modadd_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s = (a + b) MOD n)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_modadd_tmc BIGNUM_MODADD_CORRECT);;

let BIGNUM_MODADD_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_modadd_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modadd_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s = (a + b) MOD n)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODADD_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_modadd_windows_mc = define_from_elf
   "bignum_modadd_windows_mc" "x86/generic/bignum_modadd.obj";;

let bignum_modadd_windows_tmc = define_trimmed "bignum_modadd_windows_tmc" bignum_modadd_windows_mc;;

let BIGNUM_MODADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_modadd_windows_tmc); (x,8 * val k); (y,8 * val k); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_modadd_windows_tmc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modadd_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s = (a + b) MOD n)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_modadd_windows_tmc bignum_modadd_tmc
    BIGNUM_MODADD_CORRECT);;

let BIGNUM_MODADD_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!k z x y m a b n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_modadd_windows_mc); (x,8 * val k); (y,8 * val k); (m,8 * val k)] /\
        nonoverlapping (word pc,LENGTH bignum_modadd_windows_mc) (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping(x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping(y,8 * val k) (z,8 * val k)) /\
        a < n /\ b < n
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_modadd_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [k;z;x;y;m] s /\
                  bignum_from_memory (x,val k) s = a /\
                  bignum_from_memory (y,val k) s = b /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  bignum_from_memory (z,val k) s = (a + b) MOD n)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* (specs generated with generate_four_variants_of_x86_safety_specs)         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_modadd" subroutine_signatures)
    BIGNUM_MODADD_CORRECT
    BIGNUM_MODADD_EXEC;;

(* Close the non-event conjuncts of a postcondition after simulation. *)

let BIGNUM_MODADD_PEEL_TAC =
  REPEAT(W(fun (asl,w) ->
    if is_conj w then
      CONJ_TAC THENL
       [FIRST[(REWRITE_TAC[COND_ID] THEN NO_TAC);
              (GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN ASM_REWRITE_TAC[] THEN
               NO_TAC);
              (ASM_REWRITE_TAC[] THEN NO_TAC);
              (ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN NO_TAC);
              (REWRITE_TAC[WORD_SHL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
               CONV_TAC WORD_RULE THEN NO_TAC);
              (REWRITE_TAC[SUB_0] THEN CONV_TAC WORD_RULE)];
        ALL_TAC]
    else NO_TAC));;

let BIGNUM_MODADD_CLOSE_TAC =
  BIGNUM_MODADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let BIGNUM_MODADD_POST_REASSOC_TAC =
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV)
   [METIS[APPEND_ASSOC]
     `(exists e2. P e2 /\ e2 = APPEND (APPEND (x:(uarch_event)list) y) z /\ Q e2) <=>
      (exists e2. P e2 /\ e2 = APPEND x (APPEND y z) /\ Q e2)`];;

(* Reduce the conditionals `if p then a else b` of the goal according to an
   assumption p or ~p, without rewriting with p itself. *)

let BIGNUM_MODADD_COND_TAC (p:term) =
  let prove_tac = REWRITE_TAC[EQ_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC in
  (SUBGOAL_THEN (mk_iff(p,`T`)) (fun th -> REWRITE_TAC[th; COND_CLAUSES]) THENL
    [prove_tac THEN NO_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_iff(p,`F`)) (fun th -> REWRITE_TAC[th; COND_CLAUSES]) THENL
    [prove_tac THEN NO_TAC; ALL_TAC]);;

(* Discharge a leg whose postcondition trace is fully concrete (e.g. after a
   zero-step leg): instantiate e2 with the witness, then close the trace
   equation by APPEND normalization and memaccess_inbounds from the carried
   assumption, after normalizing val(word v) = v. *)

let BIGNUM_MODADD_CONCRETE_DISCHARGE_TAC : tactic =
  let is_valfact th =
    let c = concl th in
    is_eq c &&
    (try let v,a = dest_comb (lhs c) in
         name_of v = "val" && rand a = rhs c with Failure _ -> false) in
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  W(fun (a,w) ->
      let e2v, body = dest_exists w in
      let wit = rhs (find (fun c -> is_eq c && lhs c = e2v) (conjuncts body)) in
      EXISTS_TAC wit) THEN
  REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC;
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
    ASSUM_LIST(fun ths ->
      let vths = filter is_valfact ths in
      let nths = filter (fun th -> let c = concl th in
                           is_neg c && is_eq (dest_neg c)) ths in
      let rws = vths @ nths @ [COND_CLAUSES; APPEND_NIL; CONJUNCT1 APPEND;
                               GSYM APPEND_ASSOC] in
      RULE_ASSUM_TAC(REWRITE_RULE rws) THEN REWRITE_TAC rws) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC];;

(* Facts for an up-counting loop with index register word e (e an expression
   in the loop variable v), whose backward branch compares e + 1 with bnd;
   cnt is the iteration count. *)

let BIGNUM_MODADD_UPFACTS_TAC (v:term) (e:term) (bnd:term) (cnt:term) =
  let e1 = mk_binary "+" (e,`1`) in
  let wd t = mk_comb(`word:num->int64`,t) in
  let mkval t = mk_eq(mk_icomb(`val:int64->num`,wd t),t) in
  SUBGOAL_THEN (list_mk_conj
    [mkval e; mkval e1;
     mk_eq(list_mk_comb(`word_add:int64->int64->int64`,[wd e; `word 1:int64`]),
           wd e1);
     mk_iff(mk_binary "<" (e1,bnd), mk_binary "<" (mk_binary "+" (v,`1`),cnt))])
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      CONV_TAC WORD_RULE;
      SIMPLE_ARITH_TAC];
    ALL_TAC];;

(* Facts for a down-counting register holding word (c - v), decremented
   before a test of zero. *)

let BIGNUM_MODADD_DOWNFACTS_TAC (v:term) (c:term) =
  let sub t = subst [c,`c:num`; v,`j:num`] t in
  SUBGOAL_THEN (sub `word_sub (word (c - j)) (word 1):int64 = word (c - (j + 1)) /\
                     val (word (c - j):int64) = c - j /\
                     val (word (c - (j + 1)):int64) = c - (j + 1) /\
                     (~(c - (j + 1) = 0) <=> j + 1 < c)`)
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN (sub `c - j = (c - (j + 1)) + 1`) SUBST1_TAC THENL
       [SIMPLE_ARITH_TAC; CONV_TAC WORD_RULE];
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      SIMPLE_ARITH_TAC];
    ALL_TAC];;

let BIGNUM_MODADD_SAFE = time prove
 (`exists f_events.
       forall e k z x y m a b n pc.
           nonoverlapping (word pc,96) (z,8 * val k) /\
           nonoverlapping (m,8 * val k) (z,8 * val k) /\
           (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
           (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k)) /\
           a < n /\
           b < n
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) (BUTLAST bignum_modadd_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [k; z; x; y; m] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + 95) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x y m z k pc /\
                         memaccess_inbounds e2
                         [x,val k * 8; y,val k * 8; m,val k * 8; z,val k * 8]
                         [z,val k * 8]))
               (MAYCHANGE [RIP; RAX; R9; R10; R11] ,,
                MAYCHANGE SOME_FLAGS ,,
                MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bignum (z,val k)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (y:int64) (m:int64) (z:int64) (k:int64) (pc:num).
      if val k = 0 then f_ev_k0 x y m z k pc
      else
       APPEND
        (APPEND
          (APPEND []
            (APPEND (ENUMERATEL (val k) (f_ev_l3 x y m z k pc))
                    (f_ev_p3 x y m z k pc)))
          (APPEND []
            (APPEND (ENUMERATEL (val k) (f_ev_l2 x y m z k pc))
                    (f_ev_p2 x y m z k pc))))
        (APPEND []
          (APPEND (ENUMERATEL (val k) (f_ev_l1 x y m z k pc))
                  (f_ev_p1 x y m z k pc))) :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `y:int64`; `m:int64`;
    `a:num`; `b:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The degenerate case k = 0 ***)

  ASM_CASES_TAC `k = 0` THENL
   [BIGNUM_MODADD_COND_TAC `k = 0` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k = 0`)) THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_MODADD_EXEC (1--2) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  BIGNUM_MODADD_COND_TAC `k = 0` THEN

  (*** The addition loop ***)

  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x22`
   `\s. read RDI s = word k /\ read RSI s = z /\ read RDX s = x /\
        read RCX s = y /\ read R8 s = m` THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0xe` `pc + 0x22`
     `\i s. read RDI s = word k /\ read RSI s = z /\ read RDX s = x /\
            read RCX s = y /\ read R8 s = m /\
            read R9 s = word i /\ read R10 s = word (k - i)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_MODADD_EXEC (1--5) THEN
      BIGNUM_MODADD_CLOSE_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      BIGNUM_MODADD_UPFACTS_TAC `i:num` `i:num` `k:num` `k:num` THEN
      BIGNUM_MODADD_DOWNFACTS_TAC `i:num` `k:num` THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_MODADD_EXEC (1--6) THEN
      BIGNUM_MODADD_CLOSE_TAC;
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_MODADD_EXEC [] THEN
      BIGNUM_MODADD_PEEL_TAC THEN BIGNUM_MODADD_CONCRETE_DISCHARGE_TAC];
    ALL_TAC] THEN

  (*** The comparison loop ***)

  BIGNUM_MODADD_POST_REASSOC_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x3c`
   `\s. read RDI s = word k /\ read RSI s = z /\ read RDX s = x /\
        read RCX s = y /\ read R8 s = m` THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x2c` `pc + 0x3c`
     `\i s. read RDI s = word k /\ read RSI s = z /\ read RDX s = x /\
            read RCX s = y /\ read R8 s = m /\
            read R9 s = word i /\ read R10 s = word (k - i)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_MODADD_EXEC (1--3) THEN
      BIGNUM_MODADD_CLOSE_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      BIGNUM_MODADD_UPFACTS_TAC `i:num` `i:num` `k:num` `k:num` THEN
      BIGNUM_MODADD_DOWNFACTS_TAC `i:num` `k:num` THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_MODADD_EXEC (1--5) THEN
      BIGNUM_MODADD_CLOSE_TAC;
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_MODADD_EXEC [] THEN
      BIGNUM_MODADD_PEEL_TAC THEN BIGNUM_MODADD_CONCRETE_DISCHARGE_TAC];
    ALL_TAC] THEN

  (*** The masked correction loop ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x46` `pc + 0x5f`
   `\i s. read RDI s = word k /\ read RSI s = z /\ read R8 s = m /\
          read R9 s = word i` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_MODADD_EXEC (1--3) THEN
    BIGNUM_MODADD_CLOSE_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BIGNUM_MODADD_UPFACTS_TAC `i:num` `i:num` `k:num` `k:num` THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_MODADD_EXEC (1--8) THEN
    BIGNUM_MODADD_CLOSE_TAC;
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false BIGNUM_MODADD_EXEC [] THEN
    BIGNUM_MODADD_PEEL_TAC THEN BIGNUM_MODADD_CONCRETE_DISCHARGE_TAC]);;

(* Has no "word_sub stackpointer (word ..)"; stackofs is None *)
let BIGNUM_MODADD_NOIBT_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e k z x y m a b n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_modadd_tmc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k)) /\
        a < n /\
        b < n
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_modadd_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [k; z; x; y; m] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events x y m z k pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [x,val k * 8; y,val k * 8; m,val k * 8; z,val k * 8;
                       stackpointer,8]
                      [z,val k * 8; stackpointer,0]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum (z,val k)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_modadd_tmc BIGNUM_MODADD_SAFE THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let BIGNUM_MODADD_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e k z x y m a b n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_modadd_mc) (z,8 * val k) /\
        nonoverlapping (stackpointer,8) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k)) /\
        a < n /\
        b < n
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_modadd_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [k; z; x; y; m] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events x y m z k pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [x,val k * 8; y,val k * 8; m,val k * 8; z,val k * 8;
                       stackpointer,8]
                      [z,val k * 8; stackpointer,0]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum (z,val k)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODADD_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MODADD_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e k z x y m a b n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [word pc,LENGTH bignum_modadd_windows_tmc; x,8 * val k; y,8 * val k;
         m,8 * val k] /\
        nonoverlapping (word pc,LENGTH bignum_modadd_windows_tmc)
        (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k)) /\
        a < n /\
        b < n
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_modadd_windows_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [k; z; x; y; m] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events x y m z k pc (word_sub stackpointer (word 16))
                      returnaddress /\
                      memaccess_inbounds e2
                      [x,val k * 8; y,val k * 8; m,val k * 8; z,val k * 8;
                       word_add stackpointer (word 40),8;
                       word_sub stackpointer (word 16),24]
                      [z,val k * 8; word_sub stackpointer (word 16),16]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bignum (z,val k);
              memory :> bytes (word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_modadd_windows_tmc bignum_modadd_tmc BIGNUM_MODADD_SAFE THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let BIGNUM_MODADD_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e k z x y m a b n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [word pc,LENGTH bignum_modadd_windows_mc; x,8 * val k; y,8 * val k;
         m,8 * val k] /\
        nonoverlapping (word pc,LENGTH bignum_modadd_windows_mc)
        (z,8 * val k) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * val k) /\
        (x = z \/ nonoverlapping (x,8 * val k) (z,8 * val k)) /\
        (y = z \/ nonoverlapping (y,8 * val k) (z,8 * val k)) /\
        a < n /\
        b < n
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_modadd_windows_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [k; z; x; y; m] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events x y m z k pc (word_sub stackpointer (word 16))
                      returnaddress /\
                      memaccess_inbounds e2
                      [x,val k * 8; y,val k * 8; m,val k * 8; z,val k * 8;
                       word_add stackpointer (word 40),8;
                       word_sub stackpointer (word 16),24]
                      [z,val k * 8; word_sub stackpointer (word 16),16]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bignum (z,val k);
              memory :> bytes (word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MODADD_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
