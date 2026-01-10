(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction modulo m_25519, full group order for curve25519/edwards25519.   *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/curve25519/bignum_mod_m25519.o";;
 ****)

let bignum_mod_m25519_mc =
  define_assert_from_elf "bignum_mod_m25519_mc" "x86/curve25519/bignum_mod_m25519.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x48; 0x83; 0xfe; 0x04;  (* CMP (% rsi) (Imm8 (word 4)) *)
  0x0f; 0x82; 0x06; 0x01; 0x00; 0x00;
                           (* JB (Imm32 (word 262)) *)
  0x48; 0x83; 0xee; 0x04;  (* SUB (% rsi) (Imm8 (word 4)) *)
  0x4c; 0x8b; 0x5c; 0xf2; 0x18;
                           (* MOV (% r11) (Memop Quadword (%%%% (rdx,3,rsi,&24))) *)
  0x4c; 0x8b; 0x54; 0xf2; 0x10;
                           (* MOV (% r10) (Memop Quadword (%%%% (rdx,3,rsi,&16))) *)
  0x4c; 0x8b; 0x4c; 0xf2; 0x08;
                           (* MOV (% r9) (Memop Quadword (%%%% (rdx,3,rsi,&8))) *)
  0x4c; 0x8b; 0x04; 0xf2;  (* MOV (% r8) (Memop Quadword (%%% (rdx,3,rsi))) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xb8; 0x68; 0x9f; 0xae; 0xe7; 0xd2; 0x18; 0x93; 0xc0;
                           (* MOV (% rax) (Imm64 (word 13876462170967809896)) *)
  0x48; 0xba; 0xb2; 0xe6; 0xbc; 0x17; 0xf5; 0xce; 0xf7; 0xa6;
                           (* MOV (% rdx) (Imm64 (word 12031312481604134578)) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x80;
                           (* MOV (% rbx) (Imm64 (word 9223372036854775808)) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x49; 0x19; 0xdb;        (* SBB (% r11) (% rbx) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0x21; 0xd8;        (* AND (% rax) (% rbx) *)
  0x48; 0x21; 0xda;        (* AND (% rdx) (% rbx) *)
  0x48; 0xc1; 0xe3; 0x3f;  (* SHL (% rbx) (Imm8 (word 63)) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x49; 0x83; 0xd2; 0x00;  (* ADC (% r10) (Imm8 (word 0)) *)
  0x49; 0x11; 0xdb;        (* ADC (% r11) (% rbx) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x0f; 0x84; 0xc4; 0x00; 0x00; 0x00;
                           (* JE (Imm32 (word 196)) *)
  0x4c; 0x89; 0xdb;        (* MOV (% rbx) (% r11) *)
  0x4c; 0x0f; 0xa4; 0xd3; 0x01;
                           (* SHLD (% rbx) (% r10) (Imm8 (word 1)) *)
  0x49; 0xc1; 0xeb; 0x3f;  (* SHR (% r11) (Imm8 (word 63)) *)
  0x4c; 0x29; 0xdb;        (* SUB (% rbx) (% r11) *)
  0x49; 0xd1; 0xe2;        (* SHL (% r10) (Imm8 (word 1)) *)
  0x4d; 0x0f; 0xac; 0xda; 0x01;
                           (* SHRD (% r10) (% r11) (Imm8 (word 1)) *)
  0x48; 0xb8; 0x68; 0x9f; 0xae; 0xe7; 0xd2; 0x18; 0x93; 0xc0;
                           (* MOV (% rax) (Imm64 (word 13876462170967809896)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x49; 0x89; 0xd3;        (* MOV (% r11) (% rdx) *)
  0x48; 0xb8; 0xb2; 0xe6; 0xbc; 0x17; 0xf5; 0xce; 0xf7; 0xa6;
                           (* MOV (% rax) (Imm64 (word 12031312481604134578)) *)
  0x48; 0xf7; 0xe3;        (* MUL2 (% rdx,% rax) (% rbx) *)
  0x49; 0x01; 0xc3;        (* ADD (% r11) (% rax) *)
  0x48; 0x83; 0xd2; 0x00;  (* ADC (% rdx) (Imm8 (word 0)) *)
  0x4c; 0x8b; 0x64; 0xf1; 0xf8;
                           (* MOV (% r12) (Memop Quadword (%%%% (rcx,3,rsi,-- &8))) *)
  0x49; 0x29; 0xec;        (* SUB (% r12) (% rbp) *)
  0x4d; 0x19; 0xd8;        (* SBB (% r8) (% r11) *)
  0x49; 0x19; 0xd1;        (* SBB (% r9) (% rdx) *)
  0x49; 0x83; 0xda; 0x00;  (* SBB (% r10) (Imm8 (word 0)) *)
  0x48; 0x19; 0xdb;        (* SBB (% rbx) (% rbx) *)
  0x48; 0xb8; 0x68; 0x9f; 0xae; 0xe7; 0xd2; 0x18; 0x93; 0xc0;
                           (* MOV (% rax) (Imm64 (word 13876462170967809896)) *)
  0x48; 0x21; 0xd8;        (* AND (% rax) (% rbx) *)
  0x48; 0xba; 0xb2; 0xe6; 0xbc; 0x17; 0xf5; 0xce; 0xf7; 0xa6;
                           (* MOV (% rdx) (Imm64 (word 12031312481604134578)) *)
  0x48; 0x21; 0xda;        (* AND (% rdx) (% rbx) *)
  0x48; 0xbb; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x80;
                           (* MOV (% rbx) (Imm64 (word 9223372036854775808)) *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x49; 0x83; 0xd1; 0x00;  (* ADC (% r9) (Imm8 (word 0)) *)
  0x49; 0x11; 0xda;        (* ADC (% r10) (% rbx) *)
  0x4d; 0x89; 0xd3;        (* MOV (% r11) (% r10) *)
  0x4d; 0x89; 0xca;        (* MOV (% r10) (% r9) *)
  0x4d; 0x89; 0xc1;        (* MOV (% r9) (% r8) *)
  0x4d; 0x89; 0xe0;        (* MOV (% r8) (% r12) *)
  0x48; 0xff; 0xce;        (* DEC (% rsi) *)
  0x0f; 0x85; 0x64; 0xff; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294967140)) *)
  0xeb; 0x26;              (* JMP (Imm8 (word 38)) *)
  0x4d; 0x31; 0xc0;        (* XOR (% r8) (% r8) *)
  0x4d; 0x31; 0xc9;        (* XOR (% r9) (% r9) *)
  0x4d; 0x31; 0xd2;        (* XOR (% r10) (% r10) *)
  0x4d; 0x31; 0xdb;        (* XOR (% r11) (% r11) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x74; 0x15;              (* JE (Imm8 (word 21)) *)
  0x4c; 0x8b; 0x02;        (* MOV (% r8) (Memop Quadword (%% (rdx,0))) *)
  0x48; 0xff; 0xce;        (* DEC (% rsi) *)
  0x74; 0x0d;              (* JE (Imm8 (word 13)) *)
  0x4c; 0x8b; 0x4a; 0x08;  (* MOV (% r9) (Memop Quadword (%% (rdx,8))) *)
  0x48; 0xff; 0xce;        (* DEC (% rsi) *)
  0x74; 0x04;              (* JE (Imm8 (word 4)) *)
  0x4c; 0x8b; 0x52; 0x10;  (* MOV (% r10) (Memop Quadword (%% (rdx,16))) *)
  0x4c; 0x89; 0x07;        (* MOV (Memop Quadword (%% (rdi,0))) (% r8) *)
  0x4c; 0x89; 0x4f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r9) *)
  0x4c; 0x89; 0x57; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r10) *)
  0x4c; 0x89; 0x5f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r11) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
];;

let bignum_mod_m25519_tmc = define_trimmed "bignum_mod_m25519_tmc" bignum_mod_m25519_mc;;

let BIGNUM_MOD_M25519_EXEC = X86_MK_CORE_EXEC_RULE bignum_mod_m25519_tmc;;

(* ------------------------------------------------------------------------- *)
(* Common tactic for slightly different standard and Windows variants.       *)
(* ------------------------------------------------------------------------- *)

let m_25519 = new_definition `m_25519 = 57896044618658097711785492504343953926856930875039260848015607506283634007912`;;

(* ------------------------------------------------------------------------- *)
(* Correctness of standard ABI version.                                      *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MOD_M25519_CORRECT = time prove
 (`!z k x n pc.
      nonoverlapping (word pc,0x14e) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_mod_m25519_tmc) /\
                read RIP s = word(pc + 0x4) /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read RIP s = word (pc + 0x149) /\
                bignum_from_memory (z,4) s = n MOD m_25519)
          (MAYCHANGE [RIP; RSI; RAX; RDX; RCX; RBX; RBP;
                      R8; R9; R10; R11; R12] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X_GEN_TAC `z:int64` THEN W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN DISCH_TAC THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Case split over the k < 4 case, which is a different path ***)

  ASM_CASES_TAC `k < 4` THENL
   [SUBGOAL_THEN `n MOD m_25519 = n` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * k)` THEN ASM_REWRITE_TAC[] THEN
      TRANS_TAC LE_TRANS `2 EXP (64 * 3)` THEN
      ASM_REWRITE_TAC[LE_EXP; m_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "n_" `read(memory :> bytes(x,8 * 4)) s0` THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `k < 4 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`)) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    EXPAND_TAC "n" THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THENL
     [X86_STEPS_TAC BIGNUM_MOD_M25519_EXEC (1--12);
      X86_STEPS_TAC BIGNUM_MOD_M25519_EXEC (1--15);
      X86_STEPS_TAC BIGNUM_MOD_M25519_EXEC (1--18);
      X86_STEPS_TAC BIGNUM_MOD_M25519_EXEC (1--19)] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[VAL_WORD_0] THEN
    ARITH_TAC;
    FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [NOT_LT])] THEN

  (*** Initial 4-digit modulus ***)

  ENSURES_SEQUENCE_TAC `pc + 0x6d`
   `\s. bignum_from_memory(x,k) s = n /\
        read RDI s = z /\
        read RCX s = x /\
        read RSI s = word(k - 4) /\
        bignum_of_wordlist[read R8 s; read R9 s; read R10 s; read R11 s] =
        (highdigits n (k - 4)) MOD m_25519` THEN
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
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV)) THEN
    BIGNUM_LDIGITIZE_TAC "m_"
     `read (memory :> bytes (word_add x (word(8 * j)),8 * 4)) s0` THEN
    X86_ACCSTEPS_TAC BIGNUM_MOD_M25519_EXEC (12--15) (1--15) THEN
    SUBGOAL_THEN `carry_s15 <=> m < m_25519` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[m_25519; GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      ALL_TAC] THEN
    X86_ACCSTEPS_TAC BIGNUM_MOD_M25519_EXEC (20--23) (16--23) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s23" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[m_25519] THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
    SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM NOT_LT] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `m < 2 EXP (64 * 4)` THEN REWRITE_TAC[m_25519] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_LT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
                GSYM REAL_OF_NUM_POW] THEN
    ASM_REWRITE_TAC[GSYM bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[REAL_BITVAL_NOT; m_25519] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[WORD_AND_MASK] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
    ALL_TAC] THEN

  (*** Finish off the k = 4 case which is now just the writeback ***)

  FIRST_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o MATCH_MP (ARITH_RULE
   `4 <= k ==> k = 4 \/ 4 < k`))
  THENL
   [GHOST_INTRO_TAC `d0:int64` `read R8` THEN
    GHOST_INTRO_TAC `d1:int64` `read R9` THEN
    GHOST_INTRO_TAC `d2:int64` `read R10` THEN
    GHOST_INTRO_TAC `d3:int64` `read R11` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MOD_M25519_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN `0 < k - 4 /\ ~(k - 4 = 0)` STRIP_ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Setup of loop invariant ***)

  ENSURES_WHILE_PDOWN_TAC `k - 4` `pc + 0x76` `pc + 0x10c`
   `\i s. (bignum_from_memory(x,k) s = n /\
           read RDI s = z /\
           read RCX s = x /\
           read RSI s = word i /\
           bignum_of_wordlist[read R8 s; read R9 s; read R10 s; read R11 s] =
           (highdigits n i) MOD m_25519) /\
          (read ZF s <=> i = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [VAL_INT64_TAC `k - 4` THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MOD_M25519_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MOD_M25519_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    GHOST_INTRO_TAC `d0:int64` `read R8` THEN
    GHOST_INTRO_TAC `d1:int64` `read R9` THEN
    GHOST_INTRO_TAC `d2:int64` `read R10` THEN
    GHOST_INTRO_TAC `d3:int64` `read R11` THEN
    REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_MOD_M25519_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN

  (*** Mathematics of main loop with decomposition and quotient estimate ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GHOST_INTRO_TAC `m1:int64` `read R8` THEN
  GHOST_INTRO_TAC `m2:int64` `read R9` THEN
  GHOST_INTRO_TAC `m3:int64` `read R10` THEN
  GHOST_INTRO_TAC `m4:int64` `read R11` THEN
  GLOBALIZE_PRECONDITION_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m0:int64 = word(bigdigit n i)` THEN
  ABBREV_TAC `m = bignum_of_wordlist[m0; m1; m2; m3; m4]` THEN
  SUBGOAL_THEN `m < 2 EXP 64 * m_25519` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    MP_TAC(SPEC `m0:int64` VAL_BOUND_64) THEN
    ASM_REWRITE_TAC[m_25519] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `highdigits n i MOD m_25519 = m MOD m_25519` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[HIGHDIGITS_STEP] THEN
    EXPAND_TAC "m" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
    EXPAND_TAC "m0" THEN
    SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC MOD_DOWN_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Full simulation interrupted to tweak the load address ***)

  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  X86_ACCSTEPS_TAC BIGNUM_MOD_M25519_EXEC [8;12;13;14] (1--14) THEN
  VAL_INT64_TAC `i + 1` THEN
  ASSUME_TAC(SPEC `i:num` WORD_INDEX_WRAP) THEN
  SUBGOAL_THEN `i:num < k` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `x:int64`; `s14:x86state`; `i:num`]
        BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  DISCH_THEN(MP_TAC o AP_TERM `word:num->int64` o SYM) THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN DISCH_TAC THEN
  X86_ACCSTEPS_TAC BIGNUM_MOD_M25519_EXEC [16;17;18;19;20;27;28;29;30] (15--35) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s35" THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN

  (*** Quotient and associated mangling ***)

  ABBREV_TAC
   `q:int64 =
    word_sub (word_subword((word_join:int64->int64->int128) m4 m3) (63,64))
             (word_ushr m4 63)` THEN

  SUBGOAL_THEN
   `MIN (m DIV 2 EXP 255) (2 EXP 64 - 1) = val(q:int64) /\
    val q + m DIV 2 EXP 255 DIV 2 EXP 64 = m DIV 2 EXP 255`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    SUBGOAL_THEN
     `word_ushr (m4:int64) 63 = word(m DIV 2 EXP 255 DIV 2 EXP 64) /\
      word_subword ((word_join:int64->int64->int128) m4 m3) (63,64):int64 =
      word(m DIV 2 EXP 255)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; word_ushr; word_subword] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      EXPAND_TAC "m" THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[bignum_of_wordlist] THEN REWRITE_TAC[WORD_EQ] THEN
      REWRITE_TAC[DIMINDEX_64; MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN] THEN
      REWRITE_TAC[DIMINDEX_128; DIV_MOD; CONG; GSYM EXP_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN; ADD_SYM] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `m DIV 2 EXP 255 <= 2 EXP 64` MP_TAC THENL
     [UNDISCH_TAC `m < 2 EXP 64 * m_25519` THEN
      REWRITE_TAC[m_25519] THEN ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `a <= b <=> a = b \/ a < b`]] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
     [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      SIMP_TAC[DIV_LT; WORD_SUB_0; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      ARITH_TAC];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `&(val(word_subword
         ((word_join:int64->int64->int128)
          (word_ushr m4 63) (word_shl m3 1)) (1,64):int64)):real =
    (&2 pow 64 * &(val(m4:int64)) + &(val(m3:int64))) -
    &2 pow 63 * &(val(q:int64))`
  SUBST_ALL_TAC THENL
   [POP_ASSUM(MP_TAC o REWRITE_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `q + x:real = y ==> q = y - x`)) THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN EXPAND_TAC "m" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    REWRITE_TAC[bignum_of_wordlist; ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE
     `(a + 2 EXP 64 * q) DIV 2 EXP 63 =
      (2 EXP 63 * (2 * q) + a) DIV 2 EXP 63`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    CONV_TAC WORD_BLAST;
    POP_ASSUM(K ALL_TAC)] THEN

  (*** Main reasoning including quotient estimate correctness ***)

  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQUAL_FROM_CONGRUENT_MOD_MOD THEN
  EXISTS_TAC `256` THEN
  EXISTS_TAC
   `&m - (&(val(q:int64)) - &(bitval(m < val q * m_25519))) *
         &m_25519:real` THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  REPLICATE_TAC 2
   (CONJ_TAC THENL [REWRITE_TAC[m_25519] THEN ARITH_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `m < val(q:int64) * m_25519 <=> carry_s19`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[m_25519; GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      EXPAND_TAC "m" THEN
      REWRITE_TAC[m_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      BOOL_CASES_TAC `carry_s19:bool` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
        filter (is_ratconst o rand o concl) o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_DIV] THEN
    REWRITE_TAC[INT_REM_UNIQUE] THEN
    CONJ_TAC THENL [DISJ2_TAC; CONV_TAC INTEGER_RULE] THEN
    MAP_EVERY UNDISCH_TAC
     [`MIN (m DIV 2 EXP 255) (2 EXP 64 - 1) = val(q:int64)`;
      `m < 2 EXP 64 * m_25519`] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_DIV] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[m_25519; bitval] THEN
    COND_CASES_TAC THEN ASM_INT_ARITH_TAC]);;

let BIGNUM_MOD_M25519_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 24),32) (z,32) /\
      ALL (nonoverlapping (word_sub stackpointer (word 24),24))
          [(word pc,LENGTH bignum_mod_m25519_tmc); (x, 8 * val k)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_m25519_tmc) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_m25519_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD m_25519)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                 memory :> bytes(word_sub stackpointer (word 24),24)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_mod_m25519_tmc BIGNUM_MOD_M25519_CORRECT
    `[RBX; RBP; R12]` 24);;

let BIGNUM_MOD_M25519_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 24),32) (z,32) /\
      ALL (nonoverlapping (word_sub stackpointer (word 24),24))
          [(word pc,LENGTH bignum_mod_m25519_mc); (x, 8 * val k)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_m25519_mc) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_m25519_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD m_25519)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                 memory :> bytes(word_sub stackpointer (word 24),24)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_M25519_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_mod_m25519_windows_mc = define_from_elf
   "bignum_mod_m25519_windows_mc" "x86/curve25519/bignum_mod_m25519.obj";;

let bignum_mod_m25519_windows_tmc = define_trimmed "bignum_mod_m25519_windows_tmc" bignum_mod_m25519_windows_mc;;

let BIGNUM_MOD_M25519_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 40),48) (z,32) /\
      ALL (nonoverlapping (word_sub stackpointer (word 40),40))
          [(word pc,LENGTH bignum_mod_m25519_windows_tmc); (x, 8 * val k)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_m25519_windows_tmc) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_m25519_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD m_25519)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                 memory :> bytes(word_sub stackpointer (word 40),40)])`,
 WINDOWS_X86_WRAP_STACK_TAC
    bignum_mod_m25519_windows_tmc bignum_mod_m25519_tmc
    BIGNUM_MOD_M25519_CORRECT
    `[RBX; RBP; R12]` 24);;

let BIGNUM_MOD_M25519_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z k x n pc stackpointer returnaddress.
      nonoverlapping (word_sub stackpointer (word 40),48) (z,32) /\
      ALL (nonoverlapping (word_sub stackpointer (word 40),40))
          [(word pc,LENGTH bignum_mod_m25519_windows_mc); (x, 8 * val k)] /\
      nonoverlapping (word pc,LENGTH bignum_mod_m25519_windows_mc) (z,32)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_mod_m25519_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; k; x] s /\
                bignum_from_memory (x,val k) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = n MOD m_25519)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                 memory :> bytes(word_sub stackpointer (word 40),40)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_M25519_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* (specs generated with generate_four_variants_of_x86_safety_specs)         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_mod_m25519" subroutine_signatures)
    BIGNUM_MOD_M25519_CORRECT
    BIGNUM_MOD_M25519_EXEC;;

let BIGNUM_MOD_M25519_SAFE = time prove
 (`exists f_events.
       forall e z k x pc.
           nonoverlapping (word pc,334) (z,32)
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) (BUTLAST bignum_mod_m25519_tmc) /\
                    read RIP s = word (pc + 4) /\
                    C_ARGUMENTS [z; k; x] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + 329) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x z k pc /\
                         memaccess_inbounds e2 [x,val k * 8; z,32] [z,32]))
               (MAYCHANGE
                [RIP; RSI; RAX; RDX; RCX; RBX; RBP; R8; R9; R10; R11; R12] ,,
                MAYCHANGE SOME_FLAGS ,,
                MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bignum (z,4)])`,

  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(x:int64) (z:int64) (k:int64) (pc:num).
      if val k = 0 then
        f_ev_k0 x z k pc
      else if val k = 1 then
        f_ev_k1 x z k pc
      else if val k = 2 then
        f_ev_k2 x z k pc
      else if val k = 3 then
        f_ev_k3 x z k pc
      else
        APPEND
          (if val k = 4 then
            f_ev_4 x z k pc
           else APPEND
            (f_ev_loop_post x z k pc)
            (APPEND
              (ENUMERATEL (val k - 4) (f_ev_loop x z k pc))
              (f_ev_loop_pre x z k pc)))
          (f_ev_1 x z k pc)
      :(uarch_event) list` THEN

  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN

  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k' = val (k:int64)` THEN
  SUBGOAL_THEN `k' < 2 EXP 64` ASSUME_TAC THENL [
    EXPAND_TAC "k'" THEN MATCH_ACCEPT_TAC VAL_BOUND_64; ALL_TAC
  ] THEN
  ASM_CASES_TAC `k' < 4` THENL [
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
      `k < 4 ==> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`)) THEN
    STRIP_TAC THENL [
      ASM_REWRITE_TAC[ARITH] THEN
      X86_SIM_TAC BIGNUM_MOD_M25519_EXEC (1--12) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      (* k = 1 *)
      ASM_REWRITE_TAC[ARITH] THEN
      SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
      X86_SIM_TAC BIGNUM_MOD_M25519_EXEC (1--15) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      (* k = 2 *)
      ASM_REWRITE_TAC[ARITH] THEN
      SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
      X86_SIM_TAC BIGNUM_MOD_M25519_EXEC (1--18) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      (* k = 3 *)
      ASM_REWRITE_TAC[ARITH] THEN
      SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
      X86_SIM_TAC BIGNUM_MOD_M25519_EXEC (1--19) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
    ];

    ALL_TAC
  ] THEN

  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
    `~(k < 4) ==> ~(k = 0) /\ ~(k = 1) /\ ~(k = 2) /\ ~(k = 3)`)) THEN
  ASM_REWRITE_TAC[] THEN

  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x6d`
   `\s. read RDI s = z /\
        read RCX s = x /\
        read RSI s = word(k' - 4)` THEN CONJ_TAC THENL [
    X86_SIM_TAC ~canonicalize_pc_diff:false
      BIGNUM_MOD_M25519_EXEC (1--23) THEN
    CONJ_TAC THENL [
      IMP_REWRITE_TAC[GSYM WORD_SUB2] THEN
      EXPAND_TAC "k'" THEN ASM_REWRITE_TAC[WORD_VAL] THEN ASM_ARITH_TAC;
      ALL_TAC
    ] THEN

    (* to help memory inbounds reasoning (got from fn correctness proof *)
    SUBGOAL_THEN
      `8 * val (word_sub k (word 4):int64) = (8 * (k' - 4))` MP_TAC THENL [
      SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
      IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL [
        IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN SIMPLE_ARITH_TAC;
        SIMPLE_ARITH_TAC];
      ALL_TAC
    ] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    (* rewrite k with word k' *)
    SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
    REWRITE_TAC[ASSUME `val (k:int64) = k'`] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC
  ] THEN

  (*** Finish off the k = 4 case which is now just the writeback ***)

  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
   `~(k' < 4) ==> k' = 4 \/ (~(k' = 4) /\ 4 < k')`))
  THENL
   [ASM_REWRITE_TAC[SUB_REFL;MULT_0] THEN
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC BIGNUM_MOD_M25519_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    CONJ_TAC THENL [ CONV_TAC (ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC;

    ALL_TAC] THEN

  ASM_REWRITE_TAC[] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k' - 4` `pc + 0x76` `pc + 0x112`
   `\i s. read RDI s = z /\
          read RCX s = x /\
          read RSI s = word ((k' - 4) - i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [
    SIMPLE_ARITH_TAC;

    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC BIGNUM_MOD_M25519_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [
      IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN
      SIMPLE_ARITH_TAC;

      ALL_TAC
    ] THEN
    CONJ_TAC THENL [REWRITE_TAC[SUB_0]; ALL_TAC] THEN
    (* rewrite k with word k' *)
    SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
    REWRITE_TAC[ASSUME `val (k:int64) = k'`] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC BIGNUM_MOD_M25519_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC
  ] THEN

  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY VAL_INT64_TAC [`k':num`; `k'-4`; `k' - 4 - i`] THEN
  X86_STEPS_TAC BIGNUM_MOD_M25519_EXEC (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN
    REPEAT CONJ_TAC THENL [
      GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN SIMPLE_ARITH_TAC;
      SIMPLE_ARITH_TAC;
    ];
    ALL_TAC
  ] THEN
  CONJ_TAC THENL [
    IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
    [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ];
    ALL_TAC
  ] THEN
  (* safety_print_log := 1;; revealed that CONTAINED_TAC could not prove
     expressions including `word_sub (word (k' - 4 - i)) (word 1)` and
     `word (8 * (...) + 1844...)`. *)
  SUBGOAL_THEN `word_sub (word (k' - 4 - i)) (word 1) =
                word (k' - 4 - (i + 1)):int64` SUBST_ALL_TAC THENL [
    IMP_REWRITE_TAC[WORD_SUB2] THEN
    CONJ_TAC THENL [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC];
    ALL_TAC
  ] THEN
  SUBGOAL_THEN `word (8 * (k' - 4 - i) + 18446744073709551608):int64 =
                word (8 * (k' - 4 - (i + 1)))` SUBST_ALL_TAC THENL [
    REWRITE_TAC[WORD_BLAST
      `word (x + 18446744073709551608) = word_sub (word x) (word 8):int64`] THEN
    IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL [
      AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
      SIMPLE_ARITH_TAC
    ];
    ALL_TAC
  ] THEN
  (* rewrite k with word k' *)
  SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
  REWRITE_TAC[ASSUME `val (k:int64) = k'`] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let BIGNUM_MOD_M25519_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e z k x pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 24),32) (z,32) /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
        [word pc,LENGTH bignum_mod_m25519_tmc; x,8 * val k] /\
        nonoverlapping (word pc,LENGTH bignum_mod_m25519_tmc) (z,32)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_mod_m25519_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [z; k; x] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events x z k pc (word_sub stackpointer (word 24))
                      returnaddress /\
                      memaccess_inbounds e2
                      [x,val k * 8; z,32; word_sub stackpointer (word 24),32]
                      [z,32; word_sub stackpointer (word 24),24]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bignum (z,4);
              memory :> bytes (word_sub stackpointer (word 24),24)])`,
  X86_PROMOTE_RETURN_STACK_TAC bignum_mod_m25519_tmc BIGNUM_MOD_M25519_SAFE
    `[RBX; RBP; R12]` 24
  THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let BIGNUM_MOD_M25519_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e z k x pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 24),32) (z,32) /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
        [word pc,LENGTH bignum_mod_m25519_mc; x,8 * val k] /\
        nonoverlapping (word pc,LENGTH bignum_mod_m25519_mc) (z,32)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_mod_m25519_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [z; k; x] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events x z k pc (word_sub stackpointer (word 24))
                      returnaddress /\
                      memaccess_inbounds e2
                      [x,val k * 8; z,32; word_sub stackpointer (word 24),32]
                      [z,32; word_sub stackpointer (word 24),24]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bignum (z,4);
              memory :> bytes (word_sub stackpointer (word 24),24)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_M25519_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MOD_M25519_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e z k x pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 40),48) (z,32) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
        [word pc,LENGTH bignum_mod_m25519_windows_tmc; x,8 * val k] /\
        nonoverlapping (word pc,LENGTH bignum_mod_m25519_windows_tmc) (z,32)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_mod_m25519_windows_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [z; k; x] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events x z k pc (word_sub stackpointer (word 40))
                      returnaddress /\
                      memaccess_inbounds e2
                      [x,val k * 8; z,32; word_sub stackpointer (word 40),48]
                      [z,32; word_sub stackpointer (word 40),40]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bignum (z,4);
              memory :> bytes (word_sub stackpointer (word 40),40)])`,
  WINDOWS_X86_WRAP_STACK_TAC
    bignum_mod_m25519_windows_tmc bignum_mod_m25519_tmc
    BIGNUM_MOD_M25519_SAFE
    `[RBX; RBP; R12]` 24
  THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let BIGNUM_MOD_M25519_WINDOWS_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e z k x pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 40),48) (z,32) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),40))
        [word pc,LENGTH bignum_mod_m25519_windows_mc; x,8 * val k] /\
        nonoverlapping (word pc,LENGTH bignum_mod_m25519_windows_mc) (z,32)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_mod_m25519_windows_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [z; k; x] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events x z k pc (word_sub stackpointer (word 40))
                      returnaddress /\
                      memaccess_inbounds e2
                      [x,val k * 8; z,32; word_sub stackpointer (word 40),48]
                      [z,32; word_sub stackpointer (word 40),40]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bignum (z,4);
              memory :> bytes (word_sub stackpointer (word 40),40)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_MOD_M25519_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
