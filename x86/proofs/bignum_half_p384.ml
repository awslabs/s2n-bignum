(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Halving modulo p_384, the field characteristic for the NIST P-384 curve.  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p384/bignum_half_p384.o";;
 ****)

let bignum_half_p384_mc =
  define_assert_from_elf "bignum_half_p384_mc" "x86/p384/bignum_half_p384.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x41; 0xb9; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r9d) (Imm32 (word 1)) *)
  0x49; 0x21; 0xc1;        (* AND (% r9) (% rax) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0xb9; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% ecx) (Imm32 (word 4294967295)) *)
  0x4c; 0x21; 0xc9;        (* AND (% rcx) (% r9) *)
  0x48; 0x89; 0xca;        (* MOV (% rdx) (% rcx) *)
  0x4c; 0x31; 0xca;        (* XOR (% rdx) (% r9) *)
  0x4d; 0x89; 0xc8;        (* MOV (% r8) (% r9) *)
  0x4d; 0x01; 0xc0;        (* ADD (% r8) (% r8) *)
  0x4d; 0x21; 0xc8;        (* AND (% r8) (% r9) *)
  0x4d; 0x89; 0xca;        (* MOV (% r10) (% r9) *)
  0x4d; 0x89; 0xcb;        (* MOV (% r11) (% r9) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x13; 0x56; 0x08;  (* ADC (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x13; 0x46; 0x10;  (* ADC (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x13; 0x4e; 0x18;  (* ADC (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x13; 0x56; 0x20;  (* ADC (% r10) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x13; 0x5e; 0x28;  (* ADC (% r11) (Memop Quadword (%% (rsi,40))) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x0f; 0xac; 0xd1; 0x01;
                           (* SHRD (% rcx) (% rdx) (Imm8 (word 1)) *)
  0x48; 0x89; 0x0f;        (* MOV (Memop Quadword (%% (rdi,0))) (% rcx) *)
  0x4c; 0x0f; 0xac; 0xc2; 0x01;
                           (* SHRD (% rdx) (% r8) (Imm8 (word 1)) *)
  0x48; 0x89; 0x57; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rdx) *)
  0x4d; 0x0f; 0xac; 0xc8; 0x01;
                           (* SHRD (% r8) (% r9) (Imm8 (word 1)) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x4d; 0x0f; 0xac; 0xd1; 0x01;
                           (* SHRD (% r9) (% r10) (Imm8 (word 1)) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0x4d; 0x0f; 0xac; 0xda; 0x01;
                           (* SHRD (% r10) (% r11) (Imm8 (word 1)) *)
  0x4c; 0x89; 0x57; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r10) *)
  0x49; 0x0f; 0xac; 0xc3; 0x01;
                           (* SHRD (% r11) (% rax) (Imm8 (word 1)) *)
  0x4c; 0x89; 0x5f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r11) *)
  0xc3                     (* RET *)
];;

let bignum_half_p384_tmc = define_trimmed "bignum_half_p384_tmc" bignum_half_p384_mc;;

let BIGNUM_HALF_P384_EXEC = X86_MK_CORE_EXEC_RULE bignum_half_p384_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_384 = new_definition `p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319`;;

let BIGNUM_HALF_P384_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x7c) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_half_p384_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = word (pc + 0x7b) /\
                  (n < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 2 * n) MOD p_384))
            (MAYCHANGE [RIP; RAX; RDX; RCX; R8; R9; R10; R11] ,,
             MAYCHANGE SOME_FLAGS ,,
             MAYCHANGE [memory :> bignum(z,6)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `6` `n:num` THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 6)) s0` THEN

  X86_STEPS_TAC BIGNUM_HALF_P384_EXEC (1--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_AND_1_BITVAL]) THEN
  SUBGOAL_THEN `bit 0 (n_0:int64) <=> ODD n` SUBST_ALL_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[BIT_LSB; ODD_ADD; ODD_MULT; ODD_EXP] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC BIGNUM_HALF_P384_EXEC (14--19) (14--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  SUBGOAL_THEN
   `(inverse_mod p_384 2 * n) MOD p_384 =
    (if ODD n then n + p_384 else n) DIV 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[MOD_UNIQUE] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN UNDISCH_TAC `n < p_384` THEN ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONG_SYM] THEN MATCH_MP_TAC CONG_DIV_COPRIME THEN
    REWRITE_TAC[COPRIME_2; DIVIDES_2; GSYM NOT_ODD] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[p_384; ODD_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[COND_ID] THEN REWRITE_TAC[COND_RATOR; COND_RAND] THEN
    REWRITE_TAC[COND_ID; NUMBER_RULE
     `(n + p:num == m) (mod p) <=> (n == m) (mod p)`] THEN
    MATCH_MP_TAC(NUMBER_RULE
       `(x * y == 1) (mod n) ==> (a == x * y * a) (mod n)`) THEN
    REWRITE_TAC[INVERSE_MOD_RMUL_EQ; COPRIME_2] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `2 EXP 384 * bitval(carry_s19) +
    bignum_of_wordlist [sum_s14; sum_s15; sum_s16; sum_s17; sum_s18; sum_s19] =
    if ODD n then n + p_384 else n`
  (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist; p_384] THEN
    ASM_REWRITE_TAC[] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s32" THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MOD_CONV) THEN
  REWRITE_TAC[MATCH_MP VAL_WORD_SUBWORD_JOIN_64 (ARITH_RULE `1 <= 64`)] THEN
  SIMP_TAC[VAL_WORD_BITVAL; ADD_CLAUSES; bignum_of_wordlist; MULT_CLAUSES;
           BITVAL_BOUND_ALT; MOD_LT; EXP_1] THEN
  REWRITE_TAC[VAL_MOD_2; BIT_WORD_MASK; DIMINDEX_64] THEN
  REWRITE_TAC[GSYM VAL_MOD_2] THEN ARITH_TAC);;

let BIGNUM_HALF_P384_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_half_p384_tmc) (z,8 * 6) /\
        nonoverlapping (stackpointer,8) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_half_p384_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 2 * n) MOD p_384))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,6)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_half_p384_tmc
      BIGNUM_HALF_P384_CORRECT);;

let BIGNUM_HALF_P384_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,LENGTH bignum_half_p384_mc) (z,8 * 6) /\
        nonoverlapping (stackpointer,8) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_half_p384_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 2 * n) MOD p_384))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,6)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_HALF_P384_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_half_p384_windows_mc = define_from_elf
   "bignum_half_p384_windows_mc" "x86/p384/bignum_half_p384.obj";;

let bignum_half_p384_windows_tmc = define_trimmed "bignum_half_p384_windows_tmc" bignum_half_p384_windows_mc;;

let BIGNUM_HALF_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_half_p384_windows_tmc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_half_p384_windows_tmc) (z,8 * 6) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_half_p384_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 2 * n) MOD p_384))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,6);
                        memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_half_p384_windows_tmc bignum_half_p384_tmc
      BIGNUM_HALF_P384_CORRECT);;

let BIGNUM_HALF_P384_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_half_p384_windows_mc); (x,8 * 6)] /\
        nonoverlapping (word pc,LENGTH bignum_half_p384_windows_mc) (z,8 * 6) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 6)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_half_p384_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,6) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n < p_384
                   ==> bignum_from_memory (z,6) s =
                       (inverse_mod p_384 2 * n) MOD p_384))
            (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum(z,6);
                        memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_HALF_P384_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

