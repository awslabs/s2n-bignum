(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Negation mod p_521, field characteristic for NIST P-521 curve.            *)
(* ========================================================================= *)

(**** print_literal_from_elf "x86/p521/bignum_neg_p521.o";;
 ****)

let bignum_neg_p521_mc = define_assert_from_elf "bignum_neg_p521_mc" "x86/p521/bignum_neg_p521.o"
[
  0x48; 0x8b; 0x0e;        (* MOV (% rcx) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0x48; 0x8b; 0x56; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x09; 0xd0;        (* OR (% rax) (% rdx) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x09; 0xc0;        (* OR (% rax) (% r8) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0x4c; 0x09; 0xc8;        (* OR (% rax) (% r9) *)
  0x4c; 0x8b; 0x56; 0x20;  (* MOV (% r10) (Memop Quadword (%% (rsi,32))) *)
  0x4c; 0x09; 0xd0;        (* OR (% rax) (% r10) *)
  0x4c; 0x8b; 0x5e; 0x28;  (* MOV (% r11) (Memop Quadword (%% (rsi,40))) *)
  0x4c; 0x09; 0xd8;        (* OR (% rax) (% r11) *)
  0x48; 0x0b; 0x46; 0x30;  (* OR (% rax) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x0b; 0x46; 0x38;  (* OR (% rax) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x0b; 0x46; 0x40;  (* OR (% rax) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0x31; 0xc1;        (* XOR (% rcx) (% rax) *)
  0x48; 0x89; 0x0f;        (* MOV (Memop Quadword (%% (rdi,0))) (% rcx) *)
  0x48; 0x31; 0xc2;        (* XOR (% rdx) (% rax) *)
  0x48; 0x89; 0x57; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rdx) *)
  0x49; 0x31; 0xc0;        (* XOR (% r8) (% rax) *)
  0x4c; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r8) *)
  0x49; 0x31; 0xc1;        (* XOR (% r9) (% rax) *)
  0x4c; 0x89; 0x4f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r9) *)
  0x49; 0x31; 0xc2;        (* XOR (% r10) (% rax) *)
  0x4c; 0x89; 0x57; 0x20;  (* MOV (Memop Quadword (%% (rdi,32))) (% r10) *)
  0x49; 0x31; 0xc3;        (* XOR (% r11) (% rax) *)
  0x4c; 0x89; 0x5f; 0x28;  (* MOV (Memop Quadword (%% (rdi,40))) (% r11) *)
  0x48; 0x8b; 0x4e; 0x30;  (* MOV (% rcx) (Memop Quadword (%% (rsi,48))) *)
  0x48; 0x31; 0xc1;        (* XOR (% rcx) (% rax) *)
  0x48; 0x89; 0x4f; 0x30;  (* MOV (Memop Quadword (%% (rdi,48))) (% rcx) *)
  0x48; 0x8b; 0x56; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rsi,56))) *)
  0x48; 0x31; 0xc2;        (* XOR (% rdx) (% rax) *)
  0x48; 0x89; 0x57; 0x38;  (* MOV (Memop Quadword (%% (rdi,56))) (% rdx) *)
  0x4c; 0x8b; 0x46; 0x40;  (* MOV (% r8) (Memop Quadword (%% (rsi,64))) *)
  0x48; 0x25; 0xff; 0x01; 0x00; 0x00;
                           (* AND (% rax) (Imm32 (word 511)) *)
  0x49; 0x31; 0xc0;        (* XOR (% r8) (% rax) *)
  0x4c; 0x89; 0x47; 0x40;  (* MOV (Memop Quadword (%% (rdi,64))) (% r8) *)
  0xc3                     (* RET *)
];;

let BIGNUM_NEG_P521_EXEC = X86_MK_CORE_EXEC_RULE bignum_neg_p521_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let p_521 = new_definition `p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151`;;

let BIGNUM_NEG_P521_CORRECT = time prove
 (`!z x n pc.
        nonoverlapping (word pc,0x8c) (z,8 * 9) /\
        (x = z \/ nonoverlapping (x,8 * 9) (z,8 * 9))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST bignum_neg_p521_mc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = word (pc + 0x8b) /\
                  (n <= p_521
                   ==> bignum_from_memory (z,9) s = (p_521 - n) MOD p_521))
          (MAYCHANGE [RIP; RAX; RCX; RDX; R8; R9; R10; R11] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 9)) s0` THEN
  X86_STEPS_TAC BIGNUM_NEG_P521_EXEC (1--39) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[WORD_UNMASK_64] THEN DISCARD_STATE_TAC "s39" THEN

  SUBGOAL_THEN `(p_521 - n) MOD p_521 = if n = 0 then 0 else p_521 - n`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) MOD_CASES o lhand o snd) THEN
    UNDISCH_TAC `n <= p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [GSYM REAL_OF_NUM_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_EQ_0; ALL] THEN
  REWRITE_TAC[WORD_SUB_0; VAL_EQ_0; WORD_OR_EQ_0; WORD_AND_MASK] THEN
  REWRITE_TAC[CONJ_ACI; COND_SWAP; WORD_XOR_MASK] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[WORD_XOR_0; VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
  EXPAND_TAC "n" THEN
  REWRITE_TAC[p_521; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN

  SUBGOAL_THEN
   `&(val(word_xor n_8 (word 511):int64)):real =
    &(val(word 511:int64)) - &(val n_8)`
  SUBST1_TAC THENL[ALL_TAC; CONV_TAC WORD_REDUCE_CONV THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `n DIV 2 EXP 512 < 2 EXP 9` MP_TAC THENL
   [UNDISCH_TAC `n <= p_521` THEN REWRITE_TAC[p_521] THEN ARITH_TAC;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM th]) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV)) THEN
    DISCH_TAC] THEN
  ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN
  REWRITE_TAC[ARITH_RULE `511 = 2 EXP 9 - 1`] THEN
  ASM_SIMP_TAC[WORD_XOR_MASK_WORD; VAL_WORD_SUB_CASES] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `n < 2 EXP 9 ==> n <= 511`)) THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN
  SIMP_TAC[REAL_OF_NUM_SUB]);;

let BIGNUM_NEG_P521_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        nonoverlapping (word pc,0x8c) (z,8 * 9) /\
        nonoverlapping (stackpointer,8) (z,8 * 9) /\
        (x = z \/ nonoverlapping (x,8 * 9) (z,8 * 9))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) bignum_neg_p521_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n <= p_521
                   ==> bignum_from_memory (z,9) s = (p_521 - n) MOD p_521))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_neg_p521_mc BIGNUM_NEG_P521_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let windows_bignum_neg_p521_mc = define_from_elf
   "windows_bignum_neg_p521_mc" "x86/p521/bignum_neg_p521.obj";;

let WINDOWS_BIGNUM_NEG_P521_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,0x96); (x,8 * 9)] /\
        nonoverlapping (word pc,0x96) (z,8 * 9) /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 9) /\
        (x = z \/ nonoverlapping (x,8 * 9) (z,8 * 9))
        ==> ensures x86
             (\s. bytes_loaded s (word pc) windows_bignum_neg_p521_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [z; x] s /\
                  bignum_from_memory (x,9) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (n <= p_521
                   ==> bignum_from_memory (z,9) s = (p_521 - n) MOD p_521))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,9);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC windows_bignum_neg_p521_mc bignum_neg_p521_mc
    BIGNUM_NEG_P521_CORRECT);;
