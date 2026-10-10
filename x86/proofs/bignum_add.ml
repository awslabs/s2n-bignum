(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of bignums.                                                      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_add.o";;
 ****)

let bignum_add_mc =
  define_assert_from_elf "bignum_add_mc" "x86/generic/bignum_add.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x48; 0x39; 0xd7;        (* CMP (% rdi) (% rdx) *)
  0x48; 0x0f; 0x42; 0xd7;  (* CMOVB (% rdx) (% rdi) *)
  0x4c; 0x39; 0xc7;        (* CMP (% rdi) (% r8) *)
  0x4c; 0x0f; 0x42; 0xc7;  (* CMOVB (% r8) (% rdi) *)
  0x4c; 0x39; 0xc2;        (* CMP (% rdx) (% r8) *)
  0x72; 0x47;              (* JB (Imm8 (word 71)) *)
  0x48; 0x29; 0xd7;        (* SUB (% rdi) (% rdx) *)
  0x4c; 0x29; 0xc2;        (* SUB (% rdx) (% r8) *)
  0x48; 0xff; 0xc2;        (* INC (% rdx) *)
  0x4d; 0x85; 0xc0;        (* TEST (% r8) (% r8) *)
  0x74; 0x25;              (* JE (Imm8 (word 37)) *)
  0x4a; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r10))) *)
  0x4b; 0x13; 0x04; 0xd1;  (* ADC (% rax) (Memop Quadword (%%% (r9,3,r10))) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0xff; 0xc8;        (* DEC (% r8) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0xeb; 0x0f;              (* JMP (Imm8 (word 15)) *)
  0x4a; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r10))) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x75; 0x43;              (* JNE (Imm8 (word 67)) *)
  0xc3;                    (* RET *)
  0x4c; 0x29; 0xc7;        (* SUB (% rdi) (% r8) *)
  0x49; 0x29; 0xd0;        (* SUB (% r8) (% rdx) *)
  0x48; 0x85; 0xd2;        (* TEST (% rdx) (% rdx) *)
  0x74; 0x14;              (* JE (Imm8 (word 20)) *)
  0x4a; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (rcx,3,r10))) *)
  0x4b; 0x13; 0x04; 0xd1;  (* ADC (% rax) (Memop Quadword (%%% (r9,3,r10))) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0x4b; 0x8b; 0x04; 0xd1;  (* MOV (% rax) (Memop Quadword (%%% (r9,3,r10))) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x49; 0xff; 0xc8;        (* DEC (% r8) *)
  0x75; 0xec;              (* JNE (Imm8 (word 236)) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x83; 0xd0; 0x00;  (* ADC (% rax) (Imm8 (word 0)) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x75; 0x01;              (* JNE (Imm8 (word 1)) *)
  0xc3;                    (* RET *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0xeb; 0x04;              (* JMP (Imm8 (word 4)) *)
  0x4a; 0x89; 0x04; 0xd6;  (* MOV (Memop Quadword (%%% (rsi,3,r10))) (% rax) *)
  0x49; 0xff; 0xc2;        (* INC (% r10) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xf4;              (* JNE (Imm8 (word 244)) *)
  0xc3                     (* RET *)
];;

let bignum_add_tmc = define_trimmed "bignum_add_tmc" bignum_add_mc;;

let BIGNUM_ADD_EXEC = X86_MK_EXEC_RULE bignum_add_tmc;;

(* ------------------------------------------------------------------------- *)
(* Common tactic for slightly different standard and Windows variants.       *)
(* ------------------------------------------------------------------------- *)

let tac execth cleanpost offset =
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `m:num` THEN MAP_EVERY X_GEN_TAC [`x:int64`; `a:num`] THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`y:int64`; `b:num`] THEN
  X_GEN_TAC `pc:num` THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN

  (*** Remove redundancy in the conclusion ***)

  ENSURES_POSTCONDITION_TAC cleanpost THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:x86state` THEN MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[lowdigits; MOD_LT] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP (64 * p)`) THEN
    SIMP_TAC[MOD_MULT_ADD; MOD_LT; BIGNUM_FROM_MEMORY_BOUND] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Reshuffle to handle clamping and just assume m <= p and n <= p ***)

  ENSURES_SEQUENCE_TAC (offset 0x11)
   `\s. read RDI s = word p /\
        read RSI s = z /\
        read RDX s = word(MIN m p) /\
        read RCX s = x /\
        read R8 s = word(MIN n p) /\
        read R9 s = y /\
        read R10 s = word 0 /\
        bignum_from_memory(x,MIN m p) s = lowdigits a p /\
        bignum_from_memory(y,MIN n p) s = lowdigits b p` THEN
  CONJ_TAC THENL
   [X86_SIM_TAC execth (1--5) THEN
    ASM_REWRITE_TAC[lowdigits; REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
        (GSYM BIGNUM_FROM_MEMORY_MOD)] THEN
    GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV) [GSYM COND_RAND] THEN
    CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC)] THEN
  SUBGOAL_THEN
   `lowdigits (a + b) p = lowdigits (lowdigits a p + lowdigits b p) p`
  SUBST1_TAC THENL
   [REWRITE_TAC[lowdigits] THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w n. w = z \/
          nonoverlapping_modulo (2 EXP 64) (val w,8 * n) (val z,8 * p)
          ==> w:int64 = z \/
              nonoverlapping_modulo (2 EXP 64)
                 (val w,8 * MIN n p) (val z,8 * p)`
   (fun th -> DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP th)))
  THENL
   [POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
    DISCH_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`p < 2 EXP 64`; `val(word p:int64) = p`] THEN
  SUBGOAL_THEN `MIN m p < 2 EXP 64 /\ MIN n p < 2 EXP 64` MP_TAC THENL
   [ASM_ARITH_TAC; POP_ASSUM_LIST(K ALL_TAC)] THEN
  MP_TAC(ARITH_RULE `MIN m p <= p /\ MIN n p <= p`) THEN
  MAP_EVERY SPEC_TAC
   [`lowdigits a p`,`a:num`; `lowdigits b p`,`b:num`;
    `MIN m p`,`m:num`; `MIN n p`,`n:num`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
  MAP_EVERY VAL_INT64_TAC [`m:num`; `n:num`] THEN
  BIGNUM_RANGE_TAC "m" "a" THEN BIGNUM_RANGE_TAC "n" "b" THEN

  (*** Get a basic bound on p from the nonoverlapping assumptions ***)

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_RIGHT_ALT)) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; DISCH_TAC] THEN

  (*** Case split following the initial branch, m >= n case then m < n ***)

  ASM_CASES_TAC `n:num <= m` THENL
   [SUBGOAL_THEN `~(m:num < n)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `b < 2 EXP (64 * m)` ASSUME_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC (offset 0x49)
     `\s. read RDI s = word(p - m) /\
          read RSI s = z /\
          read RDX s = word(m - n + 1) /\
          read RCX s = x /\
          read R9 s = y /\
          read R10 s = word n /\
          bignum_from_memory (word_add x (word(8 * n)),m - n) s =
          highdigits a n /\
          2 EXP (64 * n) * bitval(read CF s) + bignum_from_memory(z,n) s =
          lowdigits a n + lowdigits b n` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `n = 0` THENL
       [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[SUB_0] THEN X86_SIM_TAC execth (1--7) THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      ENSURES_WHILE_PUP_TAC `n:num` (offset 0x24) (offset 0x36)
       `\i s. (read RDI s = word(p - m) /\
               read RSI s = z /\
               read RDX s = word(m - n + 1) /\
               read RCX s = x /\
               read R9 s = y /\
               read R8 s = word(n - i) /\
               read R10 s = word i /\
               bignum_from_memory (word_add x (word(8 * i)),m - i) s =
               highdigits a i /\
               bignum_from_memory (word_add y (word(8 * i)),n - i) s =
               highdigits b i /\
               2 EXP (64 * i) * bitval(read CF s) + bignum_from_memory(z,i) s =
               lowdigits a i + lowdigits b i) /\
              (read ZF s <=> i = n)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUB_0] THEN X86_SIM_TAC execth (1--7) THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_ADD; WORD_SUB];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[] THEN X86_SIM_TAC execth [1];
        X86_SIM_TAC execth (1--2)] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `i:num < m` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS])) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN STRIP_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - (i + 1) = n - i - 1`] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < n ==> (i + 1 = n <=> n - i - 1 = 0)`] THEN
      CONJ_TAC THENL
       [ALL_TAC; VAL_INT64_TAC `n - i - 1` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM ACCUMULATE_ADC; ARITH_RULE
       `(t * e) * x + z + t * y:num = t * (e * x + y) + z`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC (offset 0x57)
     `\s. read RDI s = word(p - m) /\
          read RSI s = z /\
          read R10 s = word m /\
          2 EXP (64 * m) * val(read RAX s) + bignum_from_memory(z,m) s =
          lowdigits a m + lowdigits b m` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `m:num = n` THENL
       [UNDISCH_THEN `m:num = n` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
        GHOST_INTRO_TAC `cin:bool` `read CF` THEN
        X86_SIM_TAC execth (1--4) THEN
        ASM_REWRITE_TAC[VAL_WORD_BITVAL];
        ALL_TAC] THEN
      SUBGOAL_THEN `n < m /\ 0 < m - n /\ ~(m - n = 0)` STRIP_ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `m - n:num` THEN
      ENSURES_WHILE_PUP_TAC `m - n:num` (offset 0x3a) (offset 0x4c)
       `\i s. (read RDI s = word(p - m) /\
               read RSI s = z /\
               read RCX s = x /\
               read RDX s = word(m - n - i) /\
               read R10 s = word(n + i) /\
               bignum_from_memory(word_add x (word(8 * (n + i))),
                                  m - (n + i)) s =
               highdigits a (n + i) /\
               2 EXP (64 * (n + i)) * bitval(read CF s) +
               bignum_from_memory(z,n + i) s =
               lowdigits a (n + i) + lowdigits b (n + i)) /\
              (read ZF s <=> i = m - n)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUB_0] THEN X86_SIM_TAC execth (1--2) THEN
        ASM_REWRITE_TAC[ADD_CLAUSES] THEN
        REWRITE_TAC[VAL_EQ; WORD_RULE
         `word(a + 1):int64 = word 1 <=> word a:int64 = word 0`] THEN
        CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
        ASM_REWRITE_TAC[GSYM VAL_EQ_0];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[] THEN X86_SIM_TAC execth [1];
        ASM_SIMP_TAC[ARITH_RULE `n:num <= m ==> n + m - n = m`] THEN
        GHOST_INTRO_TAC `cin:bool` `read CF` THEN
        X86_SIM_TAC execth (1--3) THEN
        ASM_REWRITE_TAC[VAL_WORD_BITVAL]] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `n:num < m
        ==> (i < m - n <=> n + i < m) /\ (i = m - n <=> n + i = m)`] THEN
      REWRITE_TAC[ARITH_RULE `m - n - i:num = m - (n + i)`] THEN
      REWRITE_TAC[ARITH_RULE `n + i + 1 = (n + i) + 1`] THEN
      X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `n <= n + j`) THEN
      SPEC_TAC(`n + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS]) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - (i + 1) = n - i - 1`] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < n ==> (i + 1 = n <=> n - i - 1 = 0)`] THEN
      CONJ_TAC THENL
       [ALL_TAC; VAL_INT64_TAC `m - i - 1` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM ACCUMULATE_ADC_0; ADD_CLAUSES; ARITH_RULE
       `(t * e) * x + z + t * y:num = t * (e * x + y) + z`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
      MATCH_MP_TAC(NUM_RING `b = 0 ==> x = e * b + x`) THEN
      MATCH_MP_TAC BIGDIGIT_ZERO THEN TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ASM_CASES_TAC `m:num = p` THENL
     [UNDISCH_THEN `m:num = p` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      X86_SIM_TAC execth (1--2) THEN ASM_REWRITE_TAC[] THEN
      BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `0 < p - m /\ ~(p - m = 0)` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `p - m:num` THEN
    ENSURES_SEQUENCE_TAC (offset 0xac)
     `\s. read RDI s = word(p - m) /\
          read RSI s = z /\
          read R10 s = word m /\
          read RAX s = word 0 /\
          bignum_from_memory(z,m + 1) s = a + b` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN ASM_REWRITE_TAC[] THEN
      GHOST_INTRO_TAC `d:int64` `read RAX` THEN
      X86_SIM_TAC execth (1--5) THEN
      GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
      BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `p = m + 1` THENL
     [UNDISCH_THEN `p = m + 1` SUBST_ALL_TAC THEN REWRITE_TAC[ADD_SUB2] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
      X86_SIM_TAC execth (1--3) THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `0 < p - (m + 1) /\ ~(p - (m + 1) = 0) /\ ~(p - m = 1) /\ m + 1 <= p`
    STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ENSURES_WHILE_PUP_TAC `p - (m + 1):num` (offset 0xa8) (offset 0xb2)
     `\i s. (read RDI s = word(p - (m + 1) - i) /\
             read R10 s = word((m + 1) + i) /\
             read RSI s = z /\
             read RAX s = word 0 /\
             bignum_from_memory(z,(m + 1) + i) s = a + b) /\
            (read ZF s <=> i = p - (m + 1))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUB_0] THEN X86_SIM_TAC execth (1--3) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; VAL_WORD_1] THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
      REWRITE_TAC[ARITH_RULE `p - (m + 1) = p - m - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      X86_SIM_TAC execth [1];
      ASM_SIMP_TAC[ARITH_RULE `0 < m - n ==> n + m - n = m`] THEN
      X86_SIM_TAC execth [1] THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES]] THEN
    X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `m + 1 <= (m + 1) + j`) THEN
    REWRITE_TAC[ARITH_RULE
     `p - (m + 1) - (j + 1) = p - ((m + 1) + (j + 1))`] THEN
    REWRITE_TAC[ARITH_RULE `p - (m + 1) - j = p - ((m + 1) + j)`] THEN
    REWRITE_TAC[ARITH_RULE `(m + 1) + (j + 1) = ((m + 1) + j) + 1`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `0 < p - (m + 1)
      ==> (j + 1 = p - (m + 1) <=> ((m + 1) + j) + 1 = p) /\
          (j < p - (m + 1) <=> (m + 1) + j < p) /\
          (j = p - (m + 1) <=> (m + 1) + j = p)`] THEN
    SPEC_TAC(`(m + 1) + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    X86_SIM_TAC execth (1--3) THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `p - (i + 1) = p - i - 1`] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < n ==> 1 <= n - i`];
      DISCH_THEN SUBST1_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < p ==> (i + 1 = p <=> p - i = 1)`] THEN
    REWRITE_TAC[VAL_EQ] THEN MATCH_MP_TAC WORD_EQ_IMP THEN
    REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;

    (**** The other branch, very similar mutatis mutandis ***)

    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
    SUBGOAL_THEN `m:num <= n` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `a < 2 EXP (64 * n)` ASSUME_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC (offset 0x7c)
     `\s. read RDI s = word(p - n) /\
          read RSI s = z /\
          read R8 s = word(n - m) /\
          read R9 s = y /\
          read RCX s = x /\
          read R10 s = word m /\
          bignum_from_memory (word_add y (word(8 * m)),n - m) s =
          highdigits b m /\
          2 EXP (64 * m) * bitval(read CF s) + bignum_from_memory(z,m) s =
          lowdigits a m + lowdigits b m` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `m = 0` THENL
       [UNDISCH_THEN `m = 0` SUBST_ALL_TAC THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        X86_SIM_TAC execth (1--6) THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      ENSURES_WHILE_PUP_TAC `m:num` (offset 0x68) (offset 0x7a)
       `\i s. (read RDI s = word(p - n) /\
               read RSI s = z /\
               read R8 s = word(n - m) /\
               read R9 s = y /\
               read RCX s = x /\
               read RDX s = word(m - i) /\
               read R10 s = word i /\
               bignum_from_memory (word_add y (word(8 * i)),n - i) s =
               highdigits b i /\
               bignum_from_memory (word_add x (word(8 * i)),m - i) s =
               highdigits a i /\
               2 EXP (64 * i) * bitval(read CF s) + bignum_from_memory(z,i) s =
               lowdigits a i + lowdigits b i) /\
              (read ZF s <=> i = m)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUB_0] THEN X86_SIM_TAC execth (1--6) THEN
        ASM_REWRITE_TAC[LOWDIGITS_0; HIGHDIGITS_0; BITVAL_CLAUSES] THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
        ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
        ASM_REWRITE_TAC[WORD_ADD; WORD_SUB];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        X86_SIM_TAC execth [1];
        X86_SIM_TAC execth [1]] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS])) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN STRIP_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `m - (i + 1) = m - i - 1`] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < m ==> 1 <= m - i`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < m ==> (i + 1 = m <=> m - i - 1 = 0)`] THEN
      CONJ_TAC THENL
       [ALL_TAC; VAL_INT64_TAC `m - i - 1` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM ACCUMULATE_ADC; ARITH_RULE
       `(t * e) * y + z + t * x:num = t * (e * y + x) + z`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN ARITH_TAC;
      ALL_TAC] THEN

    ENSURES_SEQUENCE_TAC (offset 0x99)
     `\s. read RDI s = word(p - n) /\
          read RSI s = z /\
          read R10 s = word n /\
          2 EXP (64 * n) * val(read RAX s) + bignum_from_memory(z,n) s =
          lowdigits a n + lowdigits b n` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `~(m = n) /\ 0 < n - m /\ ~(n - m = 0)`
      STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `n - m:num` THEN
      ENSURES_WHILE_PUP_TAC `n - m:num` (offset 0x7c) (offset 0x8e)
       `\i s. (read RDI s = word(p - n) /\
               read RSI s = z /\
               read R9 s = y /\
               read R8 s = word(n - m - i) /\
               read R10 s = word(m + i) /\
               bignum_from_memory(word_add y (word(8 * (m + i))),
                                  n - (m + i)) s =
               highdigits b (m + i) /\
               2 EXP (64 * (m + i)) * bitval(read CF s) +
               bignum_from_memory(z,m + i) s =
               lowdigits a (m + i) + lowdigits b (m + i)) /\
              (read ZF s <=> i = n - m)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; SUB_0] THEN
        ENSURES_INIT_TAC "s0" THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
        ASM_REWRITE_TAC[WORD_RULE `word_sub (word(m + 1)) (word 1) = word m`];
        ALL_TAC; (*** Main loop invariant ***)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        ASM_REWRITE_TAC[] THEN X86_SIM_TAC execth [1];
        ASM_SIMP_TAC[ARITH_RULE `m:num <= n ==> m + n - m = n`] THEN
        GHOST_INTRO_TAC `cin:bool` `read CF` THEN ASM_REWRITE_TAC[] THEN
        X86_SIM_TAC execth (1--3) THEN
        ASM_REWRITE_TAC[VAL_WORD_BITVAL]] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `m:num < n
        ==> (i < n - m <=> m + i < n) /\ (i = n - m <=> m + i = n)`] THEN
      REWRITE_TAC[ARITH_RULE `n - m - i:num = n - (m + i)`] THEN
      REWRITE_TAC[ARITH_RULE `m + i + 1 = (m + i) + 1`] THEN
      X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `m <= m + j`) THEN
      SPEC_TAC(`m + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      VAL_INT64_TAC `i:num` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN ENSURES_INIT_TAC "s0" THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [ONCE_REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]
       BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS]) THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN STRIP_TAC THEN
      X86_STEPS_TAC execth (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[ARITH_RULE `m - (i + 1) = m - i - 1`] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `i < m ==> 1 <= m - i`];
        DISCH_THEN SUBST1_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < m ==> (i + 1 = m <=> m - i - 1 = 0)`] THEN
      CONJ_TAC THENL
       [ALL_TAC; VAL_INT64_TAC `n - i - 1` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`; EXP_ADD] THEN
      REWRITE_TAC[GSYM ACCUMULATE_ADC_0; ADD_CLAUSES; ARITH_RULE
       `(t * e) * y + z + t * x:num = t * (e * y + x) + z`] THEN
      ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; VAL_WORD_BITVAL] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
      MATCH_MP_TAC(NUM_RING `a = 0 ==> x + y + z = e * a + y + x + z`) THEN
      MATCH_MP_TAC BIGDIGIT_ZERO THEN TRANS_TAC LTE_TRANS `2 EXP (64 * m)` THEN
      ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_MULT_LCANCEL];
      ALL_TAC] THEN

    ASM_CASES_TAC `n:num = p` THENL
     [UNDISCH_THEN `n:num = p` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      X86_SIM_TAC execth (1--2) THEN
      BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `0 < p - n /\ ~(p - n = 0)` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    VAL_INT64_TAC `p - n:num` THEN
    ENSURES_SEQUENCE_TAC (offset 0xac)
     `\s. read RDI s = word(p - n) /\
          read RSI s = z /\
          read R10 s = word n /\
          read RAX s = word 0 /\
          bignum_from_memory(z,n + 1) s = a + b` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN ASM_REWRITE_TAC[] THEN
      GHOST_INTRO_TAC `d:int64` `read RAX` THEN
      X86_SIM_TAC execth (1--5) THEN
      GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
      BINOP_TAC THEN MATCH_MP_TAC LOWDIGITS_SELF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `p = n + 1` THENL
     [UNDISCH_THEN `p = n + 1` SUBST_ALL_TAC THEN REWRITE_TAC[ADD_SUB2] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
      X86_SIM_TAC execth (1--3) THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `0 < p - (n + 1) /\ ~(p - (n + 1) = 0) /\ ~(p - n = 1) /\ n + 1 <= p`
    STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ENSURES_WHILE_PUP_TAC `p - (n + 1):num` (offset 0xa8) (offset 0xb2)
     `\i s. (read RDI s = word(p - (n + 1) - i) /\
             read R10 s = word((n + 1) + i) /\
             read RSI s = z /\
             read RAX s = word 0 /\
             bignum_from_memory(z,(n + 1) + i) s = a + b) /\
            (read ZF s <=> i = p - (n + 1))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUB_0] THEN
      X86_SIM_TAC execth (1--3) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; VAL_WORD_1] THEN
      ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ_1] THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
      REWRITE_TAC[ARITH_RULE `p - (n + 1) = p - n - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ASM_REWRITE_TAC[] THEN X86_SIM_TAC execth [1];
      ASM_SIMP_TAC[ARITH_RULE `0 < n - m ==> m + n - m = n`] THEN
      X86_SIM_TAC execth [1] THEN
      REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES]] THEN
    X_GEN_TAC `j:num` THEN MP_TAC(ARITH_RULE `n + 1 <= (n + 1) + j`) THEN
    REWRITE_TAC[ARITH_RULE
     `p - (n + 1) - (j + 1) = p - ((n + 1) + (j + 1))`] THEN
    REWRITE_TAC[ARITH_RULE `p - (n + 1) - j = p - ((n + 1) + j)`] THEN
    REWRITE_TAC[ARITH_RULE `(n + 1) + (j + 1) = ((n + 1) + j) + 1`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `0 < p - (n + 1)
      ==> (j + 1 = p - (n + 1) <=> ((n + 1) + j) + 1 = p) /\
          (j < p - (n + 1) <=> (n + 1) + j < p) /\
          (j = p - (n + 1) <=> (n + 1) + j = p)`] THEN
    SPEC_TAC(`(n + 1) + j:num`,`i:num`) THEN REPEAT STRIP_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    X86_SIM_TAC execth (1--3) THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `p - (i + 1) = p - i - 1`] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < m ==> 1 <= m - i`];
      DISCH_THEN SUBST1_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < p ==> (i + 1 = p <=> p - i = 1)`] THEN
    REWRITE_TAC[VAL_EQ] THEN MATCH_MP_TAC WORD_EQ_IMP THEN
    REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness of standard ABI version.                                      *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_ADD_CORRECT = prove
 (`!p z m x a n y b pc.
        nonoverlapping (word pc,0xb5) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_add_tmc /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [p;z;m;x;n;y] s /\
                  bignum_from_memory (x,val m) s = a /\
                  bignum_from_memory (y,val n) s = b)
             (\s. (read RIP s = word(pc + 0x5c) \/
                   read RIP s = word(pc + 0x9e) \/
                   read RIP s = word(pc + 0xb4)) /\
                  bignum_from_memory (z,val p) s =
                  (a + b) MOD 2 EXP (64 * val p) /\
                  2 EXP (64 * val p) * val(C_RETURN s) +
                  bignum_from_memory (z,val p) s =
                  lowdigits a (val p) + lowdigits b (val p))
             (MAYCHANGE [RIP; RAX; RDI; RDX; R8; R10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  tac BIGNUM_ADD_EXEC
   `\s. (read RIP s = word(pc + 0x5c) \/
         read RIP s = word(pc + 0x9e) \/
         read RIP s = word(pc + 0xb4)) /\
        2 EXP (64 * p) * val(read RAX s) +
        bignum_from_memory (z,p) s = lowdigits a p + lowdigits b p`
   (curry mk_comb `(+) (pc:num)` o mk_small_numeral));;

let BIGNUM_ADD_NOIBT_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc stackpointer returnaddress.
      ALL (nonoverlapping (z,8 * val p)) [(word pc,LENGTH bignum_add_tmc); (stackpointer,8)] /\
      (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
      (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_add_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [p;z;m;x;n;y] s /\
                bignum_from_memory (x,val m) s = a /\
                bignum_from_memory (y,val n) s = b)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val p) s =
                (a + b) MOD 2 EXP (64 * val p) /\
                2 EXP (64 * val p) * val(C_RETURN s) +
                bignum_from_memory (z,val p) s =
                lowdigits a (val p) + lowdigits b (val p))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bignum(z,val p)])`,
  X86_ADD_RETURN_NOSTACK_TAC BIGNUM_ADD_EXEC BIGNUM_ADD_CORRECT);;

let BIGNUM_ADD_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc stackpointer returnaddress.
      ALL (nonoverlapping (z,8 * val p)) [(word pc,LENGTH bignum_add_mc); (stackpointer,8)] /\
      (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
      (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_add_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [p;z;m;x;n;y] s /\
                bignum_from_memory (x,val m) s = a /\
                bignum_from_memory (y,val n) s = b)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val p) s =
                (a + b) MOD 2 EXP (64 * val p) /\
                2 EXP (64 * val p) * val(C_RETURN s) +
                bignum_from_memory (z,val p) s =
                lowdigits a (val p) + lowdigits b (val p))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bignum(z,val p)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_ADD_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_add_windows_mc = define_from_elf
   "bignum_add_windows_mc" "x86/generic/bignum_add.obj";;

let bignum_add_windows_tmc = define_trimmed "bignum_add_windows_tmc" bignum_add_windows_mc;;

let BIGNUM_ADD_WINDOWS_CORRECT = prove
 (`!p z m x a n y b pc.
        nonoverlapping (word pc,0xd3) (z,8 * val p) /\
        (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_add_windows_tmc /\
                  read RIP s = word(pc + 0x18) /\
                  C_ARGUMENTS [p;z;m;x;n;y] s /\
                  bignum_from_memory (x,val m) s = a /\
                  bignum_from_memory (y,val n) s = b)
             (\s. (read RIP s = word(pc + 0x74) \/
                   read RIP s = word(pc + 0xb8) \/
                   read RIP s = word(pc + 0xd0)) /\
                  bignum_from_memory (z,val p) s =
                  (a + b) MOD 2 EXP (64 * val p) /\
                  2 EXP (64 * val p) * val(C_RETURN s) +
                  bignum_from_memory (z,val p) s =
                  lowdigits a (val p) + lowdigits b (val p))
             (MAYCHANGE [RIP; RAX; RDI; RDX; R8; R10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val p)])`,
  tac (X86_MK_EXEC_RULE bignum_add_windows_tmc)
   `\s. (read RIP s = word(pc + 0x74) \/
         read RIP s = word(pc + 0xb8) \/
         read RIP s = word(pc + 0xd0)) /\
        2 EXP (64 * p) * val(read RAX s) +
        bignum_from_memory (z,p) s = lowdigits a p + lowdigits b p`
   (curry mk_comb `(+) (pc:num)` o mk_small_numeral o
    (fun n -> if n < 0x5c then n + 24
              else if n < 0x9e then n + 26
              else n + 28)));;

let BIGNUM_ADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc stackpointer returnaddress.
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,LENGTH bignum_add_windows_tmc); (x,8 * val m); (y,8 * val n)] /\
      ALL (nonoverlapping (z,8 * val p))
          [(word pc,LENGTH bignum_add_windows_tmc); (word_sub stackpointer (word 16),24)] /\
      (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
      (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_add_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [p;z;m;x;n;y] s /\
                bignum_from_memory (x,val m) s = a /\
                bignum_from_memory (y,val n) s = b)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val p) s =
                (a + b) MOD 2 EXP (64 * val p) /\
                2 EXP (64 * val p) * val(WINDOWS_C_RETURN s) +
                bignum_from_memory (z,val p) s =
                lowdigits a (val p) + lowdigits b (val p))
           (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bignum(z,val p);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  REWRITE_TAC[WINDOWS_ABI_STACK_THM] THEN
  GEN_X86_ADD_RETURN_STACK_TAC (X86_MK_EXEC_RULE bignum_add_windows_tmc)
    BIGNUM_ADD_WINDOWS_CORRECT
    `[RDI; RSI]` 16 (8,3));;

let BIGNUM_ADD_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!p z m x a n y b pc stackpointer returnaddress.
      ALL (nonoverlapping (word_sub stackpointer (word 16),16))
          [(word pc,LENGTH bignum_add_windows_mc); (x,8 * val m); (y,8 * val n)] /\
      ALL (nonoverlapping (z,8 * val p))
          [(word pc,LENGTH bignum_add_windows_mc); (word_sub stackpointer (word 16),24)] /\
      (x = z \/ nonoverlapping(x,8 * val m) (z,8 * val p)) /\
      (y = z \/ nonoverlapping(y,8 * val n) (z,8 * val p))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_add_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [p;z;m;x;n;y] s /\
                bignum_from_memory (x,val m) s = a /\
                bignum_from_memory (y,val n) s = b)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,val p) s =
                (a + b) MOD 2 EXP (64 * val p) /\
                2 EXP (64 * val p) * val(WINDOWS_C_RETURN s) +
                bignum_from_memory (z,val p) s =
                lowdigits a (val p) + lowdigits b (val p))
           (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bignum(z,val p);
                       memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_ADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* (specs generated with generate_four_variants_of_x86_safety_specs)         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(* Close the non-event conjuncts of a postcondition after simulation. *)

let BIGNUM_ADD_PEEL_TAC =
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

let BIGNUM_ADD_CLOSE_TAC =
  BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let BIGNUM_ADD_POST_REASSOC_TAC =
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV)
   [METIS[APPEND_ASSOC]
     `(exists e2. P e2 /\ e2 = APPEND (APPEND (x:(uarch_event)list) y) z /\ Q e2) <=>
      (exists e2. P e2 /\ e2 = APPEND x (APPEND y z) /\ Q e2)`];;

(* Reduce the conditionals `if p then a else b` of the goal according to an
   assumption p or ~p, without rewriting with p itself. *)

let BIGNUM_ADD_COND_TAC (p:term) =
  let prove_tac = REWRITE_TAC[EQ_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC in
  (SUBGOAL_THEN (mk_iff(p,`T`)) (fun th -> REWRITE_TAC[th; COND_CLAUSES]) THENL
    [prove_tac THEN NO_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_iff(p,`F`)) (fun th -> REWRITE_TAC[th; COND_CLAUSES]) THENL
    [prove_tac THEN NO_TAC; ALL_TAC]);;

(* Facts for an up-counting loop with index register word e (e an expression
   in the loop variable v), whose backward branch compares e + 1 with bnd;
   cnt is the iteration count. *)

let BIGNUM_ADD_UPFACTS_TAC (v:term) (e:term) (bnd:term) (cnt:term) =
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

let BIGNUM_ADD_DOWNFACTS_TAC (v:term) (c:term) =
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

(* Rewrite the postcondition trace to APPEND <head> <precondition trace> when
   a loop is entered from the post-leg of the previous loop. *)

let BIGNUM_ADD_CARRY_REASSOC_TAC : tactic = fun (asl,w) ->
  let _,args = strip_comb w in
  let pre = el 1 args and post = el 2 args in
  let e2v = `e2:(uarch_event)list` in
  let find_rhs t = rhs (find_term (fun u -> is_eq u && lhs u = e2v) t) in
  let pre_rhs = find_rhs pre and post_rhs = find_rhs post in
  let x0 = lhand (lhand post_rhs) in
  let eq = mk_eq(post_rhs,
    mk_binop `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list`
      x0 pre_rhs) in
  let th = prove(eq, REWRITE_TAC[APPEND_ASSOC]) in
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV) [th] (asl,w);;

(* Reorder the postcondition conjuncts so that the trace part comes last
   (after ENSURES_PRESERVED_TAC / ENSURES_EXISTING_PRESERVED_TAC add more). *)

let BIGNUM_ADD_EXISTS_LAST_TAC =
  let conv tm =
    let cs = conjuncts tm in
    let ex,others = partition is_exists cs in
    if ex = [] || others = [] then REFL tm
    else CONJ_ACI_RULE (mk_eq(tm,list_mk_conj(others @ ex))) in
  CONV_TAC(RATOR_CONV(RAND_CONV(ABS_CONV conv)));;

let BIGNUM_ADD_SAFE = time prove
 (`exists f_events.
       forall e p z m x n y pc.
           nonoverlapping (word pc,181) (z,8 * val p) /\
           (x = z \/ nonoverlapping (x,8 * val m) (z,8 * val p)) /\
           (y = z \/ nonoverlapping (y,8 * val n) (z,8 * val p))
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) bignum_add_tmc /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [p; z; m; x; n; y] s /\
                    read events s = e)
               (\s.
                    (read RIP s = word (pc + 92) \/ read RIP s = word (pc + 158) \/ read RIP s = word (pc + 180)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x y z p n m pc /\
                         memaccess_inbounds e2
                         [x,val m * 8; y,val n * 8; z,val p * 8]
                         [z,val p * 8]))
               (MAYCHANGE [RIP; RAX; RDI; RDX; R8; R10] ,,
                MAYCHANGE SOME_FLAGS ,,
                MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bignum (z,val p)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (y:int64) (z:int64) (p:int64) (n:int64) (m:int64) (pc:num).
      if MIN (val m) (val p) < MIN (val n) (val p) then
        APPEND
         (APPEND
           (if val p = MIN (val n) (val p) then f_ev_b3s x y z p n m pc
            else APPEND
                  (if val p = MIN (val n) (val p) + 1 then f_ev_b4s x y z p n m pc
                   else APPEND (f_ev_b4q x y z p n m pc)
                         (APPEND (ENUMERATEL (val p - MIN (val n) (val p) - 1)
                                             (f_ev_b4l x y z p n m pc))
                                 (f_ev_b4p x y z p n m pc)))
                  (f_ev_b3t x y z p n m pc))
           (APPEND (f_ev_b2q x y z p n m pc)
             (APPEND (ENUMERATEL (MIN (val n) (val p) - MIN (val m) (val p))
                                 (f_ev_b2l x y z p n m pc))
                     (f_ev_b2p x y z p n m pc))))
         (if MIN (val m) (val p) = 0 then f_ev_b1s x y z p n m pc
          else APPEND (f_ev_b1q x y z p n m pc)
                (APPEND (ENUMERATEL (MIN (val m) (val p)) (f_ev_b1l x y z p n m pc))
                        (f_ev_b1p x y z p n m pc)))
      else
        APPEND
         (APPEND
           (if val p = MIN (val m) (val p) then f_ev_a3s x y z p n m pc
            else APPEND
                  (if val p = MIN (val m) (val p) + 1 then f_ev_a4s x y z p n m pc
                   else APPEND (f_ev_a4q x y z p n m pc)
                         (APPEND (ENUMERATEL (val p - MIN (val m) (val p) - 1)
                                             (f_ev_a4l x y z p n m pc))
                                 (f_ev_a4p x y z p n m pc)))
                  (f_ev_a3t x y z p n m pc))
           (if MIN (val m) (val p) = MIN (val n) (val p) then f_ev_a2s x y z p n m pc
            else APPEND (f_ev_a2q x y z p n m pc)
                  (APPEND (ENUMERATEL (MIN (val m) (val p) - MIN (val n) (val p))
                                      (f_ev_a2l x y z p n m pc))
                          (f_ev_a2p x y z p n m pc))))
         (if MIN (val n) (val p) = 0 then f_ev_a1s x y z p n m pc
          else APPEND (f_ev_a1q x y z p n m pc)
                (APPEND (ENUMERATEL (MIN (val n) (val p)) (f_ev_a1l x y z p n m pc))
                        (f_ev_a1p x y z p n m pc))) :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `m:num` THEN X_GEN_TAC `x:int64` THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`y:int64`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(if p < m then word p else word m):int64 = word (MIN m p) /\
    (if p < n then word p else word n):int64 = word (MIN n p) /\
    val (word (MIN m p):int64) = MIN m p /\
    val (word (MIN n p):int64) = MIN n p`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC];
    ALL_TAC] THEN

  ASM_CASES_TAC `MIN m p < MIN n p` THENL
   [BIGNUM_ADD_COND_TAC `MIN m p < MIN n p` THEN
    SUBGOAL_THEN
     `word_sub (word p) (word (MIN n p)):int64 = word (p - MIN n p) /\
      val (word (p - MIN n p):int64) = p - MIN n p /\
      word_sub (word (MIN n p)) (word (MIN m p)):int64 =
      word (MIN n p - MIN m p) /\
      val (word (MIN n p - MIN m p):int64) = MIN n p - MIN m p /\
      ~(MIN n p - MIN m p = 0) /\
      MIN m p + (MIN n p - MIN m p) = MIN n p`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [IMP_REWRITE_TAC[WORD_SUB2] THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
        IMP_REWRITE_TAC[WORD_SUB2] THEN UNDISCH_TAC `MIN m p < MIN n p` THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
        UNDISCH_TAC `MIN m p < MIN n p` THEN ARITH_TAC;
        UNDISCH_TAC `MIN m p < MIN n p` THEN ARITH_TAC];
      ALL_TAC] THEN

    (*** Branch B: the common part of x and y ***)

    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x7c`
     `\s. read RSI s = z /\ read RCX s = x /\ read R9 s = y /\
          read RDI s = word (p - MIN n p) /\
          read R8 s = word (MIN n p - MIN m p) /\ read R10 s = word (MIN m p)` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `MIN m p = 0` THENL
       [BIGNUM_ADD_COND_TAC `MIN m p = 0` THEN
        SUBGOAL_THEN `0 < MIN n p` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`MIN m p = 0`; `MIN m p < MIN n p`] THEN ARITH_TAC;
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--11) THEN
        BIGNUM_ADD_CLOSE_TAC;
        ALL_TAC] THEN
      BIGNUM_ADD_COND_TAC `MIN m p = 0` THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `MIN m p` `pc + 0x68` `pc + 0x7c`
       `\i s. read RSI s = z /\ read RCX s = x /\ read R9 s = y /\
              read RDI s = word (p - MIN n p) /\
              read R8 s = word (MIN n p - MIN m p) /\
              read RDX s = word (MIN m p - i) /\ read R10 s = word i` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--11) THEN
        BIGNUM_ADD_CLOSE_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        BIGNUM_ADD_UPFACTS_TAC `i:num` `i:num` `MIN m p` `MIN m p` THEN
        BIGNUM_ADD_DOWNFACTS_TAC `i:num` `MIN m p` THEN
        SUBGOAL_THEN `i < m /\ i < n /\ i < p` STRIP_ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`i < MIN m p`; `MIN m p < MIN n p`] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--6) THEN
        BIGNUM_ADD_CLOSE_TAC;
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC [] THEN
        BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      ALL_TAC] THEN

    (*** Branch B: the rest of y ***)

    BIGNUM_ADD_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x90`
     `\s. read RSI s = z /\ read RDI s = word (p - MIN n p) /\
          read R10 s = word (MIN n p)` THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_WHILE_UP2_TAC `MIN n p - MIN m p` `pc + 0x7c` `pc + 0x90`
       `\i s. read RSI s = z /\ read R9 s = y /\
              read RDI s = word (p - MIN n p) /\
              read R8 s = word ((MIN n p - MIN m p) - i) /\
              read R10 s = word (MIN m p + i)` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC [] THEN
        BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        BIGNUM_ADD_DOWNFACTS_TAC `i:num` `MIN n p - MIN m p` THEN
        SUBGOAL_THEN
         `val (word (MIN m p + i):int64) = MIN m p + i /\
          word_add (word (MIN m p + i)) (word 1):int64 = word (MIN m p + (i + 1)) /\
          MIN m p + i < n /\ MIN m p + i < p`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            MAP_EVERY UNDISCH_TAC [`i < MIN n p - MIN m p`; `p < 2 EXP 64`] THEN
            ARITH_TAC;
            REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
            UNDISCH_TAC `i < MIN n p - MIN m p` THEN ARITH_TAC;
            UNDISCH_TAC `i < MIN n p - MIN m p` THEN ARITH_TAC];
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--6) THEN
        BIGNUM_ADD_CLOSE_TAC;
        BIGNUM_ADD_CARRY_REASSOC_TAC THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC [] THEN
        BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      ALL_TAC] THEN

    (*** Branch B: the return, or the carry word and the zero padding of z ***)

    ASM_CASES_TAC `p = MIN n p` THENL
     [BIGNUM_ADD_COND_TAC `p = MIN n p` THEN
      SUBGOAL_THEN `p - MIN n p = 0` ASSUME_TAC THENL
       [UNDISCH_TAC `p = MIN n p` THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = MIN n p`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--4) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    BIGNUM_ADD_COND_TAC `p = MIN n p` THEN
    SUBGOAL_THEN
     `~(p - MIN n p = 0) /\ MIN n p < p /\ val (word (MIN n p + 1):int64) = MIN n p + 1 /\ word_add (word (MIN n p)) (word 1):int64 = word (MIN n p + 1)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `~(p = MIN n p)` THEN ARITH_TAC;
        UNDISCH_TAC `~(p = MIN n p)` THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`~(p = MIN n p)`; `p < 2 EXP 64`] THEN ARITH_TAC;
        REWRITE_TAC[GSYM WORD_ADD]];
      ALL_TAC] THEN
    BIGNUM_ADD_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xac`
     `\s. read RSI s = z /\ read RDI s = word (p - MIN n p) /\
          read R10 s = word (MIN n p)` THEN
    CONJ_TAC THENL
     [X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--7) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `p = MIN n p + 1` THENL
     [BIGNUM_ADD_COND_TAC `p = MIN n p + 1` THEN
      SUBGOAL_THEN `word_sub (word (p - MIN n p)) (word 1):int64 = word 0`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `p - MIN n p = 1` SUBST1_TAC THENL
         [UNDISCH_TAC `p = MIN n p + 1` THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV];
        ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = MIN n p + 1`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--3) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    BIGNUM_ADD_COND_TAC `p = MIN n p + 1` THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `p - MIN n p - 1` `pc + 0xac` `pc + 0xac`
     `\i s. read RSI s = z /\ read RDI s = word ((p - MIN n p) - i) /\
            read R10 s = word (MIN n p + i)` THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(p = MIN n p + 1)` THEN UNDISCH_TAC `~(p = MIN n p)` THEN ARITH_TAC;
      REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC [] THEN
      BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `word_sub (word ((p - MIN n p) - i)) (word 1):int64 =
        word ((p - MIN n p) - (i + 1)) /\
        val (word ((p - MIN n p) - (i + 1)):int64) = (p - MIN n p) - (i + 1) /\
        ~((p - MIN n p) - (i + 1) = 0) /\
        val (word (MIN n p + (i + 1)):int64) = MIN n p + (i + 1) /\
        word_add (word (MIN n p + i)) (word 1):int64 = word (MIN n p + (i + 1)) /\
        MIN n p + (i + 1) < p`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
           [AP_TERM_TAC THEN UNDISCH_TAC `i < p - MIN n p - 1` THEN ARITH_TAC;
            UNDISCH_TAC `i < p - MIN n p - 1` THEN ARITH_TAC];
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
          UNDISCH_TAC `i < p - MIN n p - 1` THEN ARITH_TAC;
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          MAP_EVERY UNDISCH_TAC [`i < p - MIN n p - 1`; `p < 2 EXP 64`] THEN ARITH_TAC;
          REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
          UNDISCH_TAC `i < p - MIN n p - 1` THEN ARITH_TAC];
        ALL_TAC] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--4) THEN
      BIGNUM_ADD_CLOSE_TAC;
      SUBGOAL_THEN
       `word_sub (word ((p - MIN n p) - (p - MIN n p - 1))) (word 1):int64 = word 0`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `(p - MIN n p) - (p - MIN n p - 1) = 1` SUBST1_TAC THENL
         [UNDISCH_TAC `~(p = MIN n p)` THEN UNDISCH_TAC `MIN n p < p` THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV];
        ALL_TAC] THEN
      BIGNUM_ADD_CARRY_REASSOC_TAC THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--3) THEN
      BIGNUM_ADD_CLOSE_TAC];
    BIGNUM_ADD_COND_TAC `MIN m p < MIN n p` THEN
    SUBGOAL_THEN
     `word_sub (word p) (word (MIN m p)):int64 = word (p - MIN m p) /\
      val (word (p - MIN m p):int64) = p - MIN m p /\
      word_sub (word (MIN m p)) (word (MIN n p)):int64 =
      word (MIN m p - MIN n p) /\
      word_add (word (MIN m p - MIN n p)) (word 1):int64 =
      word (MIN m p - MIN n p + 1) /\
      MIN n p + (MIN m p - MIN n p) = MIN m p`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [IMP_REWRITE_TAC[WORD_SUB2] THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
        IMP_REWRITE_TAC[WORD_SUB2] THEN UNDISCH_TAC `~(MIN m p < MIN n p)` THEN
        ARITH_TAC;
        REWRITE_TAC[GSYM WORD_ADD];
        UNDISCH_TAC `~(MIN m p < MIN n p)` THEN ARITH_TAC];
      ALL_TAC] THEN

    (*** Branch A: the common part of x and y ***)

    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x49`
     `\s. read RSI s = z /\ read RCX s = x /\ read R9 s = y /\
          read RDI s = word (p - MIN m p) /\
          read RDX s = word (MIN m p - MIN n p + 1) /\
          read R10 s = word (MIN n p)` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `MIN n p = 0` THENL
       [BIGNUM_ADD_COND_TAC `MIN n p = 0` THEN
        SUBGOAL_THEN `~(MIN m p < 0)` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--12) THEN
        BIGNUM_ADD_CLOSE_TAC;
        ALL_TAC] THEN
      BIGNUM_ADD_COND_TAC `MIN n p = 0` THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `MIN n p` `pc + 0x24` `pc + 0x38`
       `\i s. read RSI s = z /\ read RCX s = x /\ read R9 s = y /\
              read RDI s = word (p - MIN m p) /\
              read RDX s = word (MIN m p - MIN n p + 1) /\
              read R8 s = word (MIN n p - i) /\ read R10 s = word i` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--12) THEN
        BIGNUM_ADD_CLOSE_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        BIGNUM_ADD_UPFACTS_TAC `i:num` `i:num` `MIN n p` `MIN n p` THEN
        BIGNUM_ADD_DOWNFACTS_TAC `i:num` `MIN n p` THEN
        SUBGOAL_THEN `i < m /\ i < n /\ i < p` STRIP_ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`i < MIN n p`; `~(MIN m p < MIN n p)`] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--6) THEN
        BIGNUM_ADD_CLOSE_TAC;
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--1) THEN
        BIGNUM_ADD_CLOSE_TAC];
      ALL_TAC] THEN

    (*** Branch A: the rest of x ***)

    BIGNUM_ADD_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x4e`
     `\s. read RSI s = z /\ read RDI s = word (p - MIN m p) /\
          read R10 s = word (MIN m p)` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `MIN m p = MIN n p` THENL
       [BIGNUM_ADD_COND_TAC `MIN m p = MIN n p` THEN
        SUBGOAL_THEN `MIN m p - MIN n p + 1 = 1` ASSUME_TAC THENL
         [UNDISCH_TAC `MIN m p = MIN n p` THEN ARITH_TAC; ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--2) THEN
        BIGNUM_ADD_CLOSE_TAC;
        ALL_TAC] THEN
      BIGNUM_ADD_COND_TAC `MIN m p = MIN n p` THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `MIN m p - MIN n p` `pc + 0x49` `pc + 0x49`
       `\i s. read RSI s = z /\ read RCX s = x /\
              read RDI s = word (p - MIN m p) /\
              read RDX s = word ((MIN m p - MIN n p + 1) - i) /\
              read R10 s = word (MIN n p + i)` THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `~(MIN m p = MIN n p)` THEN
        UNDISCH_TAC `~(MIN m p < MIN n p)` THEN ARITH_TAC;
        REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC [] THEN
        BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN
         `word_sub (word ((MIN m p - MIN n p + 1) - i)) (word 1):int64 =
          word (MIN m p - MIN n p - i) /\
          val (word (MIN m p - MIN n p - i):int64) = MIN m p - MIN n p - i /\
          ~(MIN m p - MIN n p - i = 0) /\
          (MIN m p - MIN n p + 1) - (i + 1) = MIN m p - MIN n p - i /\
          val (word (MIN n p + i):int64) = MIN n p + i /\
          word_add (word (MIN n p + i)) (word 1):int64 = word (MIN n p + (i + 1)) /\
          MIN n p + i < m /\ MIN n p + i < p`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THENL
           [IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
             [AP_TERM_TAC THEN UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC;
              UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC];
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
            UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC;
            UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC;
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            MAP_EVERY UNDISCH_TAC [`i < MIN m p - MIN n p`; `p < 2 EXP 64`] THEN
            ARITH_TAC;
            REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
            UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC;
            UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC];
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--6) THEN
        BIGNUM_ADD_CLOSE_TAC;
        SUBGOAL_THEN `(MIN m p - MIN n p + 1) - (MIN m p - MIN n p) = 1`
        ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        BIGNUM_ADD_CARRY_REASSOC_TAC THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--2) THEN
        BIGNUM_ADD_CLOSE_TAC];
      ALL_TAC] THEN

    (*** Branch A: the return, or the carry word and the zero padding of z ***)

    ASM_CASES_TAC `p = MIN m p` THENL
     [BIGNUM_ADD_COND_TAC `p = MIN m p` THEN
      SUBGOAL_THEN `p - MIN m p = 0` ASSUME_TAC THENL
       [UNDISCH_TAC `p = MIN m p` THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = MIN m p`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--4) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    BIGNUM_ADD_COND_TAC `p = MIN m p` THEN
    SUBGOAL_THEN
     `~(p - MIN m p = 0) /\ MIN m p < p /\ val (word (MIN m p + 1):int64) = MIN m p + 1 /\ word_add (word (MIN m p)) (word 1):int64 = word (MIN m p + 1)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `~(p = MIN m p)` THEN ARITH_TAC;
        UNDISCH_TAC `~(p = MIN m p)` THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`~(p = MIN m p)`; `p < 2 EXP 64`] THEN ARITH_TAC;
        REWRITE_TAC[GSYM WORD_ADD]];
      ALL_TAC] THEN
    BIGNUM_ADD_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xac`
     `\s. read RSI s = z /\ read RDI s = word (p - MIN m p) /\
          read R10 s = word (MIN m p)` THEN
    CONJ_TAC THENL
     [X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--7) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `p = MIN m p + 1` THENL
     [BIGNUM_ADD_COND_TAC `p = MIN m p + 1` THEN
      SUBGOAL_THEN `word_sub (word (p - MIN m p)) (word 1):int64 = word 0`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `p - MIN m p = 1` SUBST1_TAC THENL
         [UNDISCH_TAC `p = MIN m p + 1` THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV];
        ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = MIN m p + 1`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--3) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    BIGNUM_ADD_COND_TAC `p = MIN m p + 1` THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `p - MIN m p - 1` `pc + 0xac` `pc + 0xac`
     `\i s. read RSI s = z /\ read RDI s = word ((p - MIN m p) - i) /\
            read R10 s = word (MIN m p + i)` THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(p = MIN m p + 1)` THEN UNDISCH_TAC `~(p = MIN m p)` THEN ARITH_TAC;
      REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC [] THEN
      BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `word_sub (word ((p - MIN m p) - i)) (word 1):int64 =
        word ((p - MIN m p) - (i + 1)) /\
        val (word ((p - MIN m p) - (i + 1)):int64) = (p - MIN m p) - (i + 1) /\
        ~((p - MIN m p) - (i + 1) = 0) /\
        val (word (MIN m p + (i + 1)):int64) = MIN m p + (i + 1) /\
        word_add (word (MIN m p + i)) (word 1):int64 = word (MIN m p + (i + 1)) /\
        MIN m p + (i + 1) < p`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
           [AP_TERM_TAC THEN UNDISCH_TAC `i < p - MIN m p - 1` THEN ARITH_TAC;
            UNDISCH_TAC `i < p - MIN m p - 1` THEN ARITH_TAC];
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
          UNDISCH_TAC `i < p - MIN m p - 1` THEN ARITH_TAC;
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          MAP_EVERY UNDISCH_TAC [`i < p - MIN m p - 1`; `p < 2 EXP 64`] THEN ARITH_TAC;
          REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
          UNDISCH_TAC `i < p - MIN m p - 1` THEN ARITH_TAC];
        ALL_TAC] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--4) THEN
      BIGNUM_ADD_CLOSE_TAC;
      SUBGOAL_THEN
       `word_sub (word ((p - MIN m p) - (p - MIN m p - 1))) (word 1):int64 = word 0`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `(p - MIN m p) - (p - MIN m p - 1) = 1` SUBST1_TAC THENL
         [UNDISCH_TAC `~(p = MIN m p)` THEN UNDISCH_TAC `MIN m p < p` THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV];
        ALL_TAC] THEN
      BIGNUM_ADD_CARRY_REASSOC_TAC THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--3) THEN
      BIGNUM_ADD_CLOSE_TAC]]);;

(* Has no "word_sub stackpointer (word ..)"; stackofs is None *)
let BIGNUM_ADD_NOIBT_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e p z m x n y pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * val p))
        [word pc,LENGTH bignum_add_tmc; stackpointer,8] /\
        (x = z \/ nonoverlapping (x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping (y,8 * val n) (z,8 * val p))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_add_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [p; z; m; x; n; y] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events x y z p n m pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [x,val m * 8; y,val n * 8; z,val p * 8; stackpointer,8]
                      [z,val p * 8; stackpointer,0]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum (z,val p)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (y:int64) (z:int64) (p:int64) (n:int64) (m:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      if MIN (val m) (val p) < MIN (val n) (val p) then
        APPEND
         (APPEND
           (if val p = MIN (val n) (val p) then f_ev_b3s x y z p n m pc stackpointer returnaddress
            else APPEND
                  (if val p = MIN (val n) (val p) + 1 then f_ev_b4s x y z p n m pc stackpointer returnaddress
                   else APPEND (f_ev_b4q x y z p n m pc stackpointer returnaddress)
                         (APPEND (ENUMERATEL (val p - MIN (val n) (val p) - 1)
                                             (f_ev_b4l x y z p n m pc stackpointer returnaddress))
                                 (f_ev_b4p x y z p n m pc stackpointer returnaddress)))
                  (f_ev_b3t x y z p n m pc stackpointer returnaddress))
           (APPEND (f_ev_b2q x y z p n m pc stackpointer returnaddress)
             (APPEND (ENUMERATEL (MIN (val n) (val p) - MIN (val m) (val p))
                                 (f_ev_b2l x y z p n m pc stackpointer returnaddress))
                     (f_ev_b2p x y z p n m pc stackpointer returnaddress))))
         (if MIN (val m) (val p) = 0 then f_ev_b1s x y z p n m pc stackpointer returnaddress
          else APPEND (f_ev_b1q x y z p n m pc stackpointer returnaddress)
                (APPEND (ENUMERATEL (MIN (val m) (val p)) (f_ev_b1l x y z p n m pc stackpointer returnaddress))
                        (f_ev_b1p x y z p n m pc stackpointer returnaddress)))
      else
        APPEND
         (APPEND
           (if val p = MIN (val m) (val p) then f_ev_a3s x y z p n m pc stackpointer returnaddress
            else APPEND
                  (if val p = MIN (val m) (val p) + 1 then f_ev_a4s x y z p n m pc stackpointer returnaddress
                   else APPEND (f_ev_a4q x y z p n m pc stackpointer returnaddress)
                         (APPEND (ENUMERATEL (val p - MIN (val m) (val p) - 1)
                                             (f_ev_a4l x y z p n m pc stackpointer returnaddress))
                                 (f_ev_a4p x y z p n m pc stackpointer returnaddress)))
                  (f_ev_a3t x y z p n m pc stackpointer returnaddress))
           (if MIN (val m) (val p) = MIN (val n) (val p) then f_ev_a2s x y z p n m pc stackpointer returnaddress
            else APPEND (f_ev_a2q x y z p n m pc stackpointer returnaddress)
                  (APPEND (ENUMERATEL (MIN (val m) (val p) - MIN (val n) (val p))
                                      (f_ev_a2l x y z p n m pc stackpointer returnaddress))
                          (f_ev_a2p x y z p n m pc stackpointer returnaddress))))
         (if MIN (val n) (val p) = 0 then f_ev_a1s x y z p n m pc stackpointer returnaddress
          else APPEND (f_ev_a1q x y z p n m pc stackpointer returnaddress)
                (APPEND (ENUMERATEL (MIN (val n) (val p)) (f_ev_a1l x y z p n m pc stackpointer returnaddress))
                        (f_ev_a1p x y z p n m pc stackpointer returnaddress))) :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `m:num` THEN X_GEN_TAC `x:int64` THEN
  W64_GEN_TAC `n:num` THEN
  MAP_EVERY X_GEN_TAC
   [`y:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[fst BIGNUM_ADD_EXEC; ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(if p < m then word p else word m):int64 = word (MIN m p) /\
    (if p < n then word p else word n):int64 = word (MIN n p) /\
    val (word (MIN m p):int64) = MIN m p /\
    val (word (MIN n p):int64) = MIN n p`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC];
    ALL_TAC] THEN

  ASM_CASES_TAC `MIN m p < MIN n p` THENL
   [BIGNUM_ADD_COND_TAC `MIN m p < MIN n p` THEN
    SUBGOAL_THEN
     `word_sub (word p) (word (MIN n p)):int64 = word (p - MIN n p) /\
      val (word (p - MIN n p):int64) = p - MIN n p /\
      word_sub (word (MIN n p)) (word (MIN m p)):int64 =
      word (MIN n p - MIN m p) /\
      val (word (MIN n p - MIN m p):int64) = MIN n p - MIN m p /\
      ~(MIN n p - MIN m p = 0) /\
      MIN m p + (MIN n p - MIN m p) = MIN n p`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [IMP_REWRITE_TAC[WORD_SUB2] THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
        IMP_REWRITE_TAC[WORD_SUB2] THEN UNDISCH_TAC `MIN m p < MIN n p` THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
        UNDISCH_TAC `MIN m p < MIN n p` THEN ARITH_TAC;
        UNDISCH_TAC `MIN m p < MIN n p` THEN ARITH_TAC];
      ALL_TAC] THEN

    (*** Branch B: the common part of x and y ***)

    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x7c`
     `\s. read RSI s = z /\ read RCX s = x /\ read R9 s = y /\
          read RDI s = word (p - MIN n p) /\
          read R8 s = word (MIN n p - MIN m p) /\ read R10 s = word (MIN m p) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `MIN m p = 0` THENL
       [BIGNUM_ADD_COND_TAC `MIN m p = 0` THEN
        SUBGOAL_THEN `0 < MIN n p` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`MIN m p = 0`; `MIN m p < MIN n p`] THEN ARITH_TAC;
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--11) THEN
        BIGNUM_ADD_CLOSE_TAC;
        ALL_TAC] THEN
      BIGNUM_ADD_COND_TAC `MIN m p = 0` THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `MIN m p` `pc + 0x68` `pc + 0x7c`
       `\i s. read RSI s = z /\ read RCX s = x /\ read R9 s = y /\
              read RDI s = word (p - MIN n p) /\
              read R8 s = word (MIN n p - MIN m p) /\
              read RDX s = word (MIN m p - i) /\ read R10 s = word i /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--11) THEN
        BIGNUM_ADD_CLOSE_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        BIGNUM_ADD_UPFACTS_TAC `i:num` `i:num` `MIN m p` `MIN m p` THEN
        BIGNUM_ADD_DOWNFACTS_TAC `i:num` `MIN m p` THEN
        SUBGOAL_THEN `i < m /\ i < n /\ i < p` STRIP_ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`i < MIN m p`; `MIN m p < MIN n p`] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--6) THEN
        BIGNUM_ADD_CLOSE_TAC;
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC [] THEN
        BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      ALL_TAC] THEN

    (*** Branch B: the rest of y ***)

    BIGNUM_ADD_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x90`
     `\s. read RSI s = z /\ read RDI s = word (p - MIN n p) /\
          read R10 s = word (MIN n p) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress` THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_WHILE_UP2_TAC `MIN n p - MIN m p` `pc + 0x7c` `pc + 0x90`
       `\i s. read RSI s = z /\ read R9 s = y /\
              read RDI s = word (p - MIN n p) /\
              read R8 s = word ((MIN n p - MIN m p) - i) /\
              read R10 s = word (MIN m p + i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC [] THEN
        BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        BIGNUM_ADD_DOWNFACTS_TAC `i:num` `MIN n p - MIN m p` THEN
        SUBGOAL_THEN
         `val (word (MIN m p + i):int64) = MIN m p + i /\
          word_add (word (MIN m p + i)) (word 1):int64 = word (MIN m p + (i + 1)) /\
          MIN m p + i < n /\ MIN m p + i < p`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            MAP_EVERY UNDISCH_TAC [`i < MIN n p - MIN m p`; `p < 2 EXP 64`] THEN
            ARITH_TAC;
            REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
            UNDISCH_TAC `i < MIN n p - MIN m p` THEN ARITH_TAC;
            UNDISCH_TAC `i < MIN n p - MIN m p` THEN ARITH_TAC];
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--6) THEN
        BIGNUM_ADD_CLOSE_TAC;
        BIGNUM_ADD_CARRY_REASSOC_TAC THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC [] THEN
        BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      ALL_TAC] THEN

    (*** Branch B: the return, or the carry word and the zero padding of z ***)

    ASM_CASES_TAC `p = MIN n p` THENL
     [BIGNUM_ADD_COND_TAC `p = MIN n p` THEN
      SUBGOAL_THEN `p - MIN n p = 0` ASSUME_TAC THENL
       [UNDISCH_TAC `p = MIN n p` THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = MIN n p`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--5) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    BIGNUM_ADD_COND_TAC `p = MIN n p` THEN
    SUBGOAL_THEN
     `~(p - MIN n p = 0) /\ MIN n p < p /\ val (word (MIN n p + 1):int64) = MIN n p + 1 /\ word_add (word (MIN n p)) (word 1):int64 = word (MIN n p + 1)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `~(p = MIN n p)` THEN ARITH_TAC;
        UNDISCH_TAC `~(p = MIN n p)` THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`~(p = MIN n p)`; `p < 2 EXP 64`] THEN ARITH_TAC;
        REWRITE_TAC[GSYM WORD_ADD]];
      ALL_TAC] THEN
    BIGNUM_ADD_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xac`
     `\s. read RSI s = z /\ read RDI s = word (p - MIN n p) /\
          read R10 s = word (MIN n p) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress` THEN
    CONJ_TAC THENL
     [X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--7) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `p = MIN n p + 1` THENL
     [BIGNUM_ADD_COND_TAC `p = MIN n p + 1` THEN
      SUBGOAL_THEN `word_sub (word (p - MIN n p)) (word 1):int64 = word 0`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `p - MIN n p = 1` SUBST1_TAC THENL
         [UNDISCH_TAC `p = MIN n p + 1` THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV];
        ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = MIN n p + 1`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--4) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    BIGNUM_ADD_COND_TAC `p = MIN n p + 1` THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `p - MIN n p - 1` `pc + 0xac` `pc + 0xac`
     `\i s. read RSI s = z /\ read RDI s = word ((p - MIN n p) - i) /\
            read R10 s = word (MIN n p + i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress` THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(p = MIN n p + 1)` THEN UNDISCH_TAC `~(p = MIN n p)` THEN ARITH_TAC;
      REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC [] THEN
      BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `word_sub (word ((p - MIN n p) - i)) (word 1):int64 =
        word ((p - MIN n p) - (i + 1)) /\
        val (word ((p - MIN n p) - (i + 1)):int64) = (p - MIN n p) - (i + 1) /\
        ~((p - MIN n p) - (i + 1) = 0) /\
        val (word (MIN n p + (i + 1)):int64) = MIN n p + (i + 1) /\
        word_add (word (MIN n p + i)) (word 1):int64 = word (MIN n p + (i + 1)) /\
        MIN n p + (i + 1) < p`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
           [AP_TERM_TAC THEN UNDISCH_TAC `i < p - MIN n p - 1` THEN ARITH_TAC;
            UNDISCH_TAC `i < p - MIN n p - 1` THEN ARITH_TAC];
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
          UNDISCH_TAC `i < p - MIN n p - 1` THEN ARITH_TAC;
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          MAP_EVERY UNDISCH_TAC [`i < p - MIN n p - 1`; `p < 2 EXP 64`] THEN ARITH_TAC;
          REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
          UNDISCH_TAC `i < p - MIN n p - 1` THEN ARITH_TAC];
        ALL_TAC] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--4) THEN
      BIGNUM_ADD_CLOSE_TAC;
      SUBGOAL_THEN
       `word_sub (word ((p - MIN n p) - (p - MIN n p - 1))) (word 1):int64 = word 0`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `(p - MIN n p) - (p - MIN n p - 1) = 1` SUBST1_TAC THENL
         [UNDISCH_TAC `~(p = MIN n p)` THEN UNDISCH_TAC `MIN n p < p` THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV];
        ALL_TAC] THEN
      BIGNUM_ADD_CARRY_REASSOC_TAC THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--4) THEN
      BIGNUM_ADD_CLOSE_TAC];
    BIGNUM_ADD_COND_TAC `MIN m p < MIN n p` THEN
    SUBGOAL_THEN
     `word_sub (word p) (word (MIN m p)):int64 = word (p - MIN m p) /\
      val (word (p - MIN m p):int64) = p - MIN m p /\
      word_sub (word (MIN m p)) (word (MIN n p)):int64 =
      word (MIN m p - MIN n p) /\
      word_add (word (MIN m p - MIN n p)) (word 1):int64 =
      word (MIN m p - MIN n p + 1) /\
      MIN n p + (MIN m p - MIN n p) = MIN m p`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [IMP_REWRITE_TAC[WORD_SUB2] THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
        IMP_REWRITE_TAC[WORD_SUB2] THEN UNDISCH_TAC `~(MIN m p < MIN n p)` THEN
        ARITH_TAC;
        REWRITE_TAC[GSYM WORD_ADD];
        UNDISCH_TAC `~(MIN m p < MIN n p)` THEN ARITH_TAC];
      ALL_TAC] THEN

    (*** Branch A: the common part of x and y ***)

    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x49`
     `\s. read RSI s = z /\ read RCX s = x /\ read R9 s = y /\
          read RDI s = word (p - MIN m p) /\
          read RDX s = word (MIN m p - MIN n p + 1) /\
          read R10 s = word (MIN n p) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `MIN n p = 0` THENL
       [BIGNUM_ADD_COND_TAC `MIN n p = 0` THEN
        SUBGOAL_THEN `~(MIN m p < 0)` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--12) THEN
        BIGNUM_ADD_CLOSE_TAC;
        ALL_TAC] THEN
      BIGNUM_ADD_COND_TAC `MIN n p = 0` THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `MIN n p` `pc + 0x24` `pc + 0x38`
       `\i s. read RSI s = z /\ read RCX s = x /\ read R9 s = y /\
              read RDI s = word (p - MIN m p) /\
              read RDX s = word (MIN m p - MIN n p + 1) /\
              read R8 s = word (MIN n p - i) /\ read R10 s = word i /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--12) THEN
        BIGNUM_ADD_CLOSE_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        BIGNUM_ADD_UPFACTS_TAC `i:num` `i:num` `MIN n p` `MIN n p` THEN
        BIGNUM_ADD_DOWNFACTS_TAC `i:num` `MIN n p` THEN
        SUBGOAL_THEN `i < m /\ i < n /\ i < p` STRIP_ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`i < MIN n p`; `~(MIN m p < MIN n p)`] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--6) THEN
        BIGNUM_ADD_CLOSE_TAC;
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--1) THEN
        BIGNUM_ADD_CLOSE_TAC];
      ALL_TAC] THEN

    (*** Branch A: the rest of x ***)

    BIGNUM_ADD_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x4e`
     `\s. read RSI s = z /\ read RDI s = word (p - MIN m p) /\
          read R10 s = word (MIN m p) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `MIN m p = MIN n p` THENL
       [BIGNUM_ADD_COND_TAC `MIN m p = MIN n p` THEN
        SUBGOAL_THEN `MIN m p - MIN n p + 1 = 1` ASSUME_TAC THENL
         [UNDISCH_TAC `MIN m p = MIN n p` THEN ARITH_TAC; ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--2) THEN
        BIGNUM_ADD_CLOSE_TAC;
        ALL_TAC] THEN
      BIGNUM_ADD_COND_TAC `MIN m p = MIN n p` THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `MIN m p - MIN n p` `pc + 0x49` `pc + 0x49`
       `\i s. read RSI s = z /\ read RCX s = x /\
              read RDI s = word (p - MIN m p) /\
              read RDX s = word ((MIN m p - MIN n p + 1) - i) /\
              read R10 s = word (MIN n p + i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress` THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `~(MIN m p = MIN n p)` THEN
        UNDISCH_TAC `~(MIN m p < MIN n p)` THEN ARITH_TAC;
        REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC [] THEN
        BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN
         `word_sub (word ((MIN m p - MIN n p + 1) - i)) (word 1):int64 =
          word (MIN m p - MIN n p - i) /\
          val (word (MIN m p - MIN n p - i):int64) = MIN m p - MIN n p - i /\
          ~(MIN m p - MIN n p - i = 0) /\
          (MIN m p - MIN n p + 1) - (i + 1) = MIN m p - MIN n p - i /\
          val (word (MIN n p + i):int64) = MIN n p + i /\
          word_add (word (MIN n p + i)) (word 1):int64 = word (MIN n p + (i + 1)) /\
          MIN n p + i < m /\ MIN n p + i < p`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THENL
           [IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
             [AP_TERM_TAC THEN UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC;
              UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC];
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
            UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC;
            UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC;
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            MAP_EVERY UNDISCH_TAC [`i < MIN m p - MIN n p`; `p < 2 EXP 64`] THEN
            ARITH_TAC;
            REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
            UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC;
            UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC];
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--6) THEN
        BIGNUM_ADD_CLOSE_TAC;
        SUBGOAL_THEN `(MIN m p - MIN n p + 1) - (MIN m p - MIN n p) = 1`
        ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        BIGNUM_ADD_CARRY_REASSOC_TAC THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--2) THEN
        BIGNUM_ADD_CLOSE_TAC];
      ALL_TAC] THEN

    (*** Branch A: the return, or the carry word and the zero padding of z ***)

    ASM_CASES_TAC `p = MIN m p` THENL
     [BIGNUM_ADD_COND_TAC `p = MIN m p` THEN
      SUBGOAL_THEN `p - MIN m p = 0` ASSUME_TAC THENL
       [UNDISCH_TAC `p = MIN m p` THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = MIN m p`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--5) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    BIGNUM_ADD_COND_TAC `p = MIN m p` THEN
    SUBGOAL_THEN
     `~(p - MIN m p = 0) /\ MIN m p < p /\ val (word (MIN m p + 1):int64) = MIN m p + 1 /\ word_add (word (MIN m p)) (word 1):int64 = word (MIN m p + 1)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `~(p = MIN m p)` THEN ARITH_TAC;
        UNDISCH_TAC `~(p = MIN m p)` THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`~(p = MIN m p)`; `p < 2 EXP 64`] THEN ARITH_TAC;
        REWRITE_TAC[GSYM WORD_ADD]];
      ALL_TAC] THEN
    BIGNUM_ADD_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xac`
     `\s. read RSI s = z /\ read RDI s = word (p - MIN m p) /\
          read R10 s = word (MIN m p) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress` THEN
    CONJ_TAC THENL
     [X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--7) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `p = MIN m p + 1` THENL
     [BIGNUM_ADD_COND_TAC `p = MIN m p + 1` THEN
      SUBGOAL_THEN `word_sub (word (p - MIN m p)) (word 1):int64 = word 0`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `p - MIN m p = 1` SUBST1_TAC THENL
         [UNDISCH_TAC `p = MIN m p + 1` THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV];
        ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = MIN m p + 1`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--4) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    BIGNUM_ADD_COND_TAC `p = MIN m p + 1` THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `p - MIN m p - 1` `pc + 0xac` `pc + 0xac`
     `\i s. read RSI s = z /\ read RDI s = word ((p - MIN m p) - i) /\
            read R10 s = word (MIN m p + i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress` THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(p = MIN m p + 1)` THEN UNDISCH_TAC `~(p = MIN m p)` THEN ARITH_TAC;
      REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC [] THEN
      BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `word_sub (word ((p - MIN m p) - i)) (word 1):int64 =
        word ((p - MIN m p) - (i + 1)) /\
        val (word ((p - MIN m p) - (i + 1)):int64) = (p - MIN m p) - (i + 1) /\
        ~((p - MIN m p) - (i + 1) = 0) /\
        val (word (MIN m p + (i + 1)):int64) = MIN m p + (i + 1) /\
        word_add (word (MIN m p + i)) (word 1):int64 = word (MIN m p + (i + 1)) /\
        MIN m p + (i + 1) < p`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
           [AP_TERM_TAC THEN UNDISCH_TAC `i < p - MIN m p - 1` THEN ARITH_TAC;
            UNDISCH_TAC `i < p - MIN m p - 1` THEN ARITH_TAC];
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
          UNDISCH_TAC `i < p - MIN m p - 1` THEN ARITH_TAC;
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          MAP_EVERY UNDISCH_TAC [`i < p - MIN m p - 1`; `p < 2 EXP 64`] THEN ARITH_TAC;
          REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
          UNDISCH_TAC `i < p - MIN m p - 1` THEN ARITH_TAC];
        ALL_TAC] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--4) THEN
      BIGNUM_ADD_CLOSE_TAC;
      SUBGOAL_THEN
       `word_sub (word ((p - MIN m p) - (p - MIN m p - 1))) (word 1):int64 = word 0`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `(p - MIN m p) - (p - MIN m p - 1) = 1` SUBST1_TAC THENL
         [UNDISCH_TAC `~(p = MIN m p)` THEN UNDISCH_TAC `MIN m p < p` THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV];
        ALL_TAC] THEN
      BIGNUM_ADD_CARRY_REASSOC_TAC THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_EXEC (1--4) THEN
      BIGNUM_ADD_CLOSE_TAC]]);;

let BIGNUM_ADD_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e p z m x n y pc stackpointer returnaddress.
        ALL (nonoverlapping (z,8 * val p))
        [word pc,LENGTH bignum_add_mc; stackpointer,8] /\
        (x = z \/ nonoverlapping (x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping (y,8 * val n) (z,8 * val p))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_add_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [p; z; m; x; n; y] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events x y z p n m pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [x,val m * 8; y,val n * 8; z,val p * 8; stackpointer,8]
                      [z,val p * 8; stackpointer,0]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum (z,val p)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_ADD_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_ADD_WINDOWS_EXEC = X86_MK_EXEC_RULE bignum_add_windows_tmc;;

let BIGNUM_ADD_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e p z m x n y pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [word pc,LENGTH bignum_add_windows_tmc; x,8 * val m; y,8 * val n] /\
        ALL (nonoverlapping (z,8 * val p))
        [word pc,LENGTH bignum_add_windows_tmc;
         word_sub stackpointer (word 16),24] /\
        (x = z \/ nonoverlapping (x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping (y,8 * val n) (z,8 * val p))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_add_windows_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [p; z; m; x; n; y] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events x y z p n m pc
                      (word_sub stackpointer (word 16))
                      returnaddress /\
                      memaccess_inbounds e2
                      [x,val m * 8; y,val n * 8; z,val p * 8;
                       word_add stackpointer (word 40),8;
                       word_add stackpointer (word 48),8;
                       word_sub stackpointer (word 16),24]
                      [z,val p * 8; word_sub stackpointer (word 16),16]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bignum (z,val p);
              memory :> bytes (word_sub stackpointer (word 16),16)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (y:int64) (z:int64) (p:int64) (n:int64) (m:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      if MIN (val m) (val p) < MIN (val n) (val p) then
        APPEND
         (APPEND
           (if val p = MIN (val n) (val p) then f_ev_b3s x y z p n m pc stackpointer returnaddress
            else APPEND
                  (if val p = MIN (val n) (val p) + 1 then f_ev_b4s x y z p n m pc stackpointer returnaddress
                   else APPEND (f_ev_b4q x y z p n m pc stackpointer returnaddress)
                         (APPEND (ENUMERATEL (val p - MIN (val n) (val p) - 1)
                                             (f_ev_b4l x y z p n m pc stackpointer returnaddress))
                                 (f_ev_b4p x y z p n m pc stackpointer returnaddress)))
                  (f_ev_b3t x y z p n m pc stackpointer returnaddress))
           (APPEND (f_ev_b2q x y z p n m pc stackpointer returnaddress)
             (APPEND (ENUMERATEL (MIN (val n) (val p) - MIN (val m) (val p))
                                 (f_ev_b2l x y z p n m pc stackpointer returnaddress))
                     (f_ev_b2p x y z p n m pc stackpointer returnaddress))))
         (if MIN (val m) (val p) = 0 then f_ev_b1s x y z p n m pc stackpointer returnaddress
          else APPEND (f_ev_b1q x y z p n m pc stackpointer returnaddress)
                (APPEND (ENUMERATEL (MIN (val m) (val p)) (f_ev_b1l x y z p n m pc stackpointer returnaddress))
                        (f_ev_b1p x y z p n m pc stackpointer returnaddress)))
      else
        APPEND
         (APPEND
           (if val p = MIN (val m) (val p) then f_ev_a3s x y z p n m pc stackpointer returnaddress
            else APPEND
                  (if val p = MIN (val m) (val p) + 1 then f_ev_a4s x y z p n m pc stackpointer returnaddress
                   else APPEND (f_ev_a4q x y z p n m pc stackpointer returnaddress)
                         (APPEND (ENUMERATEL (val p - MIN (val m) (val p) - 1)
                                             (f_ev_a4l x y z p n m pc stackpointer returnaddress))
                                 (f_ev_a4p x y z p n m pc stackpointer returnaddress)))
                  (f_ev_a3t x y z p n m pc stackpointer returnaddress))
           (if MIN (val m) (val p) = MIN (val n) (val p) then f_ev_a2s x y z p n m pc stackpointer returnaddress
            else APPEND (f_ev_a2q x y z p n m pc stackpointer returnaddress)
                  (APPEND (ENUMERATEL (MIN (val m) (val p) - MIN (val n) (val p))
                                      (f_ev_a2l x y z p n m pc stackpointer returnaddress))
                          (f_ev_a2p x y z p n m pc stackpointer returnaddress))))
         (if MIN (val n) (val p) = 0 then f_ev_a1s x y z p n m pc stackpointer returnaddress
          else APPEND (f_ev_a1q x y z p n m pc stackpointer returnaddress)
                (APPEND (ENUMERATEL (MIN (val n) (val p)) (f_ev_a1l x y z p n m pc stackpointer returnaddress))
                        (f_ev_a1p x y z p n m pc stackpointer returnaddress))) :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `m:num` THEN X_GEN_TAC `x:int64` THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`y:int64`; `pc:num`] THEN
  PURE_REWRITE_TAC[WINDOWS_ABI_STACK_THM] THEN
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add x (word 16)) (word 16):int64 = x`] THEN
  REWRITE_TAC[fst BIGNUM_ADD_WINDOWS_EXEC; ALL; NONOVERLAPPING_CLAUSES;
              WINDOWS_C_ARGUMENTS; SOME_FLAGS;
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  BIGNUM_ADD_EXISTS_LAST_TAC THEN
  SUBGOAL_THEN
   `(if p < m then word p else word m):int64 = word (MIN m p) /\
    (if p < n then word p else word n):int64 = word (MIN n p) /\
    val (word (MIN m p):int64) = MIN m p /\
    val (word (MIN n p):int64) = MIN n p`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC];
    ALL_TAC] THEN

  ASM_CASES_TAC `MIN m p < MIN n p` THENL
   [BIGNUM_ADD_COND_TAC `MIN m p < MIN n p` THEN
    SUBGOAL_THEN
     `word_sub (word p) (word (MIN n p)):int64 = word (p - MIN n p) /\
      val (word (p - MIN n p):int64) = p - MIN n p /\
      word_sub (word (MIN n p)) (word (MIN m p)):int64 =
      word (MIN n p - MIN m p) /\
      val (word (MIN n p - MIN m p):int64) = MIN n p - MIN m p /\
      ~(MIN n p - MIN m p = 0) /\
      MIN m p + (MIN n p - MIN m p) = MIN n p`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [IMP_REWRITE_TAC[WORD_SUB2] THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
        IMP_REWRITE_TAC[WORD_SUB2] THEN UNDISCH_TAC `MIN m p < MIN n p` THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
        UNDISCH_TAC `MIN m p < MIN n p` THEN ARITH_TAC;
        UNDISCH_TAC `MIN m p < MIN n p` THEN ARITH_TAC];
      ALL_TAC] THEN

    (*** Branch B: the common part of x and y ***)

    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x96`
     `\s. read RSI s = z /\ read RCX s = x /\ read R9 s = y /\
          read RDI s = word (p - MIN n p) /\
          read R8 s = word (MIN n p - MIN m p) /\ read R10 s = word (MIN m p) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = rdi_init /\
          read (memory :> bytes64 stackpointer) s = rsi_init` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `MIN m p = 0` THENL
       [BIGNUM_ADD_COND_TAC `MIN m p = 0` THEN
        SUBGOAL_THEN `0 < MIN n p` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`MIN m p = 0`; `MIN m p < MIN n p`] THEN ARITH_TAC;
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--19) THEN
        BIGNUM_ADD_CLOSE_TAC;
        ALL_TAC] THEN
      BIGNUM_ADD_COND_TAC `MIN m p = 0` THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `MIN m p` `pc + 0x82` `pc + 0x96`
       `\i s. read RSI s = z /\ read RCX s = x /\ read R9 s = y /\
              read RDI s = word (p - MIN n p) /\
              read R8 s = word (MIN n p - MIN m p) /\
              read RDX s = word (MIN m p - i) /\ read R10 s = word i /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = rdi_init /\
          read (memory :> bytes64 stackpointer) s = rsi_init` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--19) THEN
        BIGNUM_ADD_CLOSE_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        BIGNUM_ADD_UPFACTS_TAC `i:num` `i:num` `MIN m p` `MIN m p` THEN
        BIGNUM_ADD_DOWNFACTS_TAC `i:num` `MIN m p` THEN
        SUBGOAL_THEN `i < m /\ i < n /\ i < p` STRIP_ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`i < MIN m p`; `MIN m p < MIN n p`] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--6) THEN
        BIGNUM_ADD_CLOSE_TAC;
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC [] THEN
        BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      ALL_TAC] THEN

    (*** Branch B: the rest of y ***)

    BIGNUM_ADD_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xaa`
     `\s. read RSI s = z /\ read RDI s = word (p - MIN n p) /\
          read R10 s = word (MIN n p) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = rdi_init /\
          read (memory :> bytes64 stackpointer) s = rsi_init` THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_WHILE_UP2_TAC `MIN n p - MIN m p` `pc + 0x96` `pc + 0xaa`
       `\i s. read RSI s = z /\ read R9 s = y /\
              read RDI s = word (p - MIN n p) /\
              read R8 s = word ((MIN n p - MIN m p) - i) /\
              read R10 s = word (MIN m p + i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = rdi_init /\
          read (memory :> bytes64 stackpointer) s = rsi_init` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC [] THEN
        BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        BIGNUM_ADD_DOWNFACTS_TAC `i:num` `MIN n p - MIN m p` THEN
        SUBGOAL_THEN
         `val (word (MIN m p + i):int64) = MIN m p + i /\
          word_add (word (MIN m p + i)) (word 1):int64 = word (MIN m p + (i + 1)) /\
          MIN m p + i < n /\ MIN m p + i < p`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            MAP_EVERY UNDISCH_TAC [`i < MIN n p - MIN m p`; `p < 2 EXP 64`] THEN
            ARITH_TAC;
            REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
            UNDISCH_TAC `i < MIN n p - MIN m p` THEN ARITH_TAC;
            UNDISCH_TAC `i < MIN n p - MIN m p` THEN ARITH_TAC];
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--6) THEN
        BIGNUM_ADD_CLOSE_TAC;
        BIGNUM_ADD_CARRY_REASSOC_TAC THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC [] THEN
        BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      ALL_TAC] THEN

    (*** Branch B: the return, or the carry word and the zero padding of z ***)

    ASM_CASES_TAC `p = MIN n p` THENL
     [BIGNUM_ADD_COND_TAC `p = MIN n p` THEN
      SUBGOAL_THEN `p - MIN n p = 0` ASSUME_TAC THENL
       [UNDISCH_TAC `p = MIN n p` THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = MIN n p`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--7) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    BIGNUM_ADD_COND_TAC `p = MIN n p` THEN
    SUBGOAL_THEN
     `~(p - MIN n p = 0) /\ MIN n p < p /\ val (word (MIN n p + 1):int64) = MIN n p + 1 /\ word_add (word (MIN n p)) (word 1):int64 = word (MIN n p + 1)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `~(p = MIN n p)` THEN ARITH_TAC;
        UNDISCH_TAC `~(p = MIN n p)` THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`~(p = MIN n p)`; `p < 2 EXP 64`] THEN ARITH_TAC;
        REWRITE_TAC[GSYM WORD_ADD]];
      ALL_TAC] THEN
    BIGNUM_ADD_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xc8`
     `\s. read RSI s = z /\ read RDI s = word (p - MIN n p) /\
          read R10 s = word (MIN n p) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = rdi_init /\
          read (memory :> bytes64 stackpointer) s = rsi_init` THEN
    CONJ_TAC THENL
     [X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--7) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `p = MIN n p + 1` THENL
     [BIGNUM_ADD_COND_TAC `p = MIN n p + 1` THEN
      SUBGOAL_THEN `word_sub (word (p - MIN n p)) (word 1):int64 = word 0`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `p - MIN n p = 1` SUBST1_TAC THENL
         [UNDISCH_TAC `p = MIN n p + 1` THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV];
        ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = MIN n p + 1`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--6) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    BIGNUM_ADD_COND_TAC `p = MIN n p + 1` THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `p - MIN n p - 1` `pc + 0xc8` `pc + 0xc8`
     `\i s. read RSI s = z /\ read RDI s = word ((p - MIN n p) - i) /\
            read R10 s = word (MIN n p + i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = rdi_init /\
          read (memory :> bytes64 stackpointer) s = rsi_init` THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(p = MIN n p + 1)` THEN UNDISCH_TAC `~(p = MIN n p)` THEN ARITH_TAC;
      REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC [] THEN
      BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `word_sub (word ((p - MIN n p) - i)) (word 1):int64 =
        word ((p - MIN n p) - (i + 1)) /\
        val (word ((p - MIN n p) - (i + 1)):int64) = (p - MIN n p) - (i + 1) /\
        ~((p - MIN n p) - (i + 1) = 0) /\
        val (word (MIN n p + (i + 1)):int64) = MIN n p + (i + 1) /\
        word_add (word (MIN n p + i)) (word 1):int64 = word (MIN n p + (i + 1)) /\
        MIN n p + (i + 1) < p`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
           [AP_TERM_TAC THEN UNDISCH_TAC `i < p - MIN n p - 1` THEN ARITH_TAC;
            UNDISCH_TAC `i < p - MIN n p - 1` THEN ARITH_TAC];
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
          UNDISCH_TAC `i < p - MIN n p - 1` THEN ARITH_TAC;
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          MAP_EVERY UNDISCH_TAC [`i < p - MIN n p - 1`; `p < 2 EXP 64`] THEN ARITH_TAC;
          REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
          UNDISCH_TAC `i < p - MIN n p - 1` THEN ARITH_TAC];
        ALL_TAC] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--4) THEN
      BIGNUM_ADD_CLOSE_TAC;
      SUBGOAL_THEN
       `word_sub (word ((p - MIN n p) - (p - MIN n p - 1))) (word 1):int64 = word 0`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `(p - MIN n p) - (p - MIN n p - 1) = 1` SUBST1_TAC THENL
         [UNDISCH_TAC `~(p = MIN n p)` THEN UNDISCH_TAC `MIN n p < p` THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV];
        ALL_TAC] THEN
      BIGNUM_ADD_CARRY_REASSOC_TAC THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--6) THEN
      BIGNUM_ADD_CLOSE_TAC];
    BIGNUM_ADD_COND_TAC `MIN m p < MIN n p` THEN
    SUBGOAL_THEN
     `word_sub (word p) (word (MIN m p)):int64 = word (p - MIN m p) /\
      val (word (p - MIN m p):int64) = p - MIN m p /\
      word_sub (word (MIN m p)) (word (MIN n p)):int64 =
      word (MIN m p - MIN n p) /\
      word_add (word (MIN m p - MIN n p)) (word 1):int64 =
      word (MIN m p - MIN n p + 1) /\
      MIN n p + (MIN m p - MIN n p) = MIN m p`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [IMP_REWRITE_TAC[WORD_SUB2] THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
        IMP_REWRITE_TAC[WORD_SUB2] THEN UNDISCH_TAC `~(MIN m p < MIN n p)` THEN
        ARITH_TAC;
        REWRITE_TAC[GSYM WORD_ADD];
        UNDISCH_TAC `~(MIN m p < MIN n p)` THEN ARITH_TAC];
      ALL_TAC] THEN

    (*** Branch A: the common part of x and y ***)

    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x61`
     `\s. read RSI s = z /\ read RCX s = x /\ read R9 s = y /\
          read RDI s = word (p - MIN m p) /\
          read RDX s = word (MIN m p - MIN n p + 1) /\
          read R10 s = word (MIN n p) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = rdi_init /\
          read (memory :> bytes64 stackpointer) s = rsi_init` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `MIN n p = 0` THENL
       [BIGNUM_ADD_COND_TAC `MIN n p = 0` THEN
        SUBGOAL_THEN `~(MIN m p < 0)` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--20) THEN
        BIGNUM_ADD_CLOSE_TAC;
        ALL_TAC] THEN
      BIGNUM_ADD_COND_TAC `MIN n p = 0` THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `MIN n p` `pc + 0x3c` `pc + 0x50`
       `\i s. read RSI s = z /\ read RCX s = x /\ read R9 s = y /\
              read RDI s = word (p - MIN m p) /\
              read RDX s = word (MIN m p - MIN n p + 1) /\
              read R8 s = word (MIN n p - i) /\ read R10 s = word i /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = rdi_init /\
          read (memory :> bytes64 stackpointer) s = rsi_init` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--20) THEN
        BIGNUM_ADD_CLOSE_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        BIGNUM_ADD_UPFACTS_TAC `i:num` `i:num` `MIN n p` `MIN n p` THEN
        BIGNUM_ADD_DOWNFACTS_TAC `i:num` `MIN n p` THEN
        SUBGOAL_THEN `i < m /\ i < n /\ i < p` STRIP_ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`i < MIN n p`; `~(MIN m p < MIN n p)`] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--6) THEN
        BIGNUM_ADD_CLOSE_TAC;
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--1) THEN
        BIGNUM_ADD_CLOSE_TAC];
      ALL_TAC] THEN

    (*** Branch A: the rest of x ***)

    BIGNUM_ADD_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x66`
     `\s. read RSI s = z /\ read RDI s = word (p - MIN m p) /\
          read R10 s = word (MIN m p) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = rdi_init /\
          read (memory :> bytes64 stackpointer) s = rsi_init` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `MIN m p = MIN n p` THENL
       [BIGNUM_ADD_COND_TAC `MIN m p = MIN n p` THEN
        SUBGOAL_THEN `MIN m p - MIN n p + 1 = 1` ASSUME_TAC THENL
         [UNDISCH_TAC `MIN m p = MIN n p` THEN ARITH_TAC; ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--2) THEN
        BIGNUM_ADD_CLOSE_TAC;
        ALL_TAC] THEN
      BIGNUM_ADD_COND_TAC `MIN m p = MIN n p` THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `MIN m p - MIN n p` `pc + 0x61` `pc + 0x61`
       `\i s. read RSI s = z /\ read RCX s = x /\
              read RDI s = word (p - MIN m p) /\
              read RDX s = word ((MIN m p - MIN n p + 1) - i) /\
              read R10 s = word (MIN n p + i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = rdi_init /\
          read (memory :> bytes64 stackpointer) s = rsi_init` THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `~(MIN m p = MIN n p)` THEN
        UNDISCH_TAC `~(MIN m p < MIN n p)` THEN ARITH_TAC;
        REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC [] THEN
        BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN
         `word_sub (word ((MIN m p - MIN n p + 1) - i)) (word 1):int64 =
          word (MIN m p - MIN n p - i) /\
          val (word (MIN m p - MIN n p - i):int64) = MIN m p - MIN n p - i /\
          ~(MIN m p - MIN n p - i = 0) /\
          (MIN m p - MIN n p + 1) - (i + 1) = MIN m p - MIN n p - i /\
          val (word (MIN n p + i):int64) = MIN n p + i /\
          word_add (word (MIN n p + i)) (word 1):int64 = word (MIN n p + (i + 1)) /\
          MIN n p + i < m /\ MIN n p + i < p`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THENL
           [IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
             [AP_TERM_TAC THEN UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC;
              UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC];
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
            UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC;
            UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC;
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            MAP_EVERY UNDISCH_TAC [`i < MIN m p - MIN n p`; `p < 2 EXP 64`] THEN
            ARITH_TAC;
            REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
            UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC;
            UNDISCH_TAC `i < MIN m p - MIN n p` THEN ARITH_TAC];
          ALL_TAC] THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--6) THEN
        BIGNUM_ADD_CLOSE_TAC;
        SUBGOAL_THEN `(MIN m p - MIN n p + 1) - (MIN m p - MIN n p) = 1`
        ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        BIGNUM_ADD_CARRY_REASSOC_TAC THEN
        X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--2) THEN
        BIGNUM_ADD_CLOSE_TAC];
      ALL_TAC] THEN

    (*** Branch A: the return, or the carry word and the zero padding of z ***)

    ASM_CASES_TAC `p = MIN m p` THENL
     [BIGNUM_ADD_COND_TAC `p = MIN m p` THEN
      SUBGOAL_THEN `p - MIN m p = 0` ASSUME_TAC THENL
       [UNDISCH_TAC `p = MIN m p` THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = MIN m p`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--7) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    BIGNUM_ADD_COND_TAC `p = MIN m p` THEN
    SUBGOAL_THEN
     `~(p - MIN m p = 0) /\ MIN m p < p /\ val (word (MIN m p + 1):int64) = MIN m p + 1 /\ word_add (word (MIN m p)) (word 1):int64 = word (MIN m p + 1)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `~(p = MIN m p)` THEN ARITH_TAC;
        UNDISCH_TAC `~(p = MIN m p)` THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`~(p = MIN m p)`; `p < 2 EXP 64`] THEN ARITH_TAC;
        REWRITE_TAC[GSYM WORD_ADD]];
      ALL_TAC] THEN
    BIGNUM_ADD_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xc8`
     `\s. read RSI s = z /\ read RDI s = word (p - MIN m p) /\
          read R10 s = word (MIN m p) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = rdi_init /\
          read (memory :> bytes64 stackpointer) s = rsi_init` THEN
    CONJ_TAC THENL
     [X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--7) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `p = MIN m p + 1` THENL
     [BIGNUM_ADD_COND_TAC `p = MIN m p + 1` THEN
      SUBGOAL_THEN `word_sub (word (p - MIN m p)) (word 1):int64 = word 0`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `p - MIN m p = 1` SUBST1_TAC THENL
         [UNDISCH_TAC `p = MIN m p + 1` THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV];
        ALL_TAC] THEN
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = MIN m p + 1`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--6) THEN
      BIGNUM_ADD_CLOSE_TAC;
      ALL_TAC] THEN
    BIGNUM_ADD_COND_TAC `p = MIN m p + 1` THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `p - MIN m p - 1` `pc + 0xc8` `pc + 0xc8`
     `\i s. read RSI s = z /\ read RDI s = word ((p - MIN m p) - i) /\
            read R10 s = word (MIN m p + i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s = rdi_init /\
          read (memory :> bytes64 stackpointer) s = rsi_init` THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(p = MIN m p + 1)` THEN UNDISCH_TAC `~(p = MIN m p)` THEN ARITH_TAC;
      REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC [] THEN
      BIGNUM_ADD_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `word_sub (word ((p - MIN m p) - i)) (word 1):int64 =
        word ((p - MIN m p) - (i + 1)) /\
        val (word ((p - MIN m p) - (i + 1)):int64) = (p - MIN m p) - (i + 1) /\
        ~((p - MIN m p) - (i + 1) = 0) /\
        val (word (MIN m p + (i + 1)):int64) = MIN m p + (i + 1) /\
        word_add (word (MIN m p + i)) (word 1):int64 = word (MIN m p + (i + 1)) /\
        MIN m p + (i + 1) < p`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
           [AP_TERM_TAC THEN UNDISCH_TAC `i < p - MIN m p - 1` THEN ARITH_TAC;
            UNDISCH_TAC `i < p - MIN m p - 1` THEN ARITH_TAC];
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
          UNDISCH_TAC `i < p - MIN m p - 1` THEN ARITH_TAC;
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          MAP_EVERY UNDISCH_TAC [`i < p - MIN m p - 1`; `p < 2 EXP 64`] THEN ARITH_TAC;
          REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
          UNDISCH_TAC `i < p - MIN m p - 1` THEN ARITH_TAC];
        ALL_TAC] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--4) THEN
      BIGNUM_ADD_CLOSE_TAC;
      SUBGOAL_THEN
       `word_sub (word ((p - MIN m p) - (p - MIN m p - 1))) (word 1):int64 = word 0`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `(p - MIN m p) - (p - MIN m p - 1) = 1` SUBST1_TAC THENL
         [UNDISCH_TAC `~(p = MIN m p)` THEN UNDISCH_TAC `MIN m p < p` THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV];
        ALL_TAC] THEN
      BIGNUM_ADD_CARRY_REASSOC_TAC THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false BIGNUM_ADD_WINDOWS_EXEC (1--6) THEN
      BIGNUM_ADD_CLOSE_TAC]]);;

let BIGNUM_ADD_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e p z m x n y pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [word pc,LENGTH bignum_add_windows_mc; x,8 * val m; y,8 * val n] /\
        ALL (nonoverlapping (z,8 * val p))
        [word pc,LENGTH bignum_add_windows_mc;
         word_sub stackpointer (word 16),24] /\
        (x = z \/ nonoverlapping (x,8 * val m) (z,8 * val p)) /\
        (y = z \/ nonoverlapping (y,8 * val n) (z,8 * val p))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_add_windows_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [p; z; m; x; n; y] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events x y z p n m pc
                      (word_sub stackpointer (word 16))
                      returnaddress /\
                      memaccess_inbounds e2
                      [x,val m * 8; y,val n * 8; z,val p * 8;
                       word_add stackpointer (word 40),8;
                       word_add stackpointer (word 48),8;
                       word_sub stackpointer (word 16),24]
                      [z,val p * 8; word_sub stackpointer (word 16),16]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bignum (z,val p);
              memory :> bytes (word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_ADD_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
