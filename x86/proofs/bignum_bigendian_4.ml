(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Big-endian transformation (just byte reversal as x86 is little-endian).   *)
(* There are three different correctness variants corresponding to the three *)
(* aliases with different types (bigendian, frombebytes and tobebytes).      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/p256/bignum_bigendian_4.o";;
 ****)

let bignum_bigendian_4_mc =
  define_assert_from_elf "bignum_bigendian_4_mc" "x86/p256/bignum_bigendian_4.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x8b; 0x56; 0x18;  (* MOV (% rdx) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x0f; 0xc8;        (* BSWAP (% rax) *)
  0x48; 0x0f; 0xca;        (* BSWAP (% rdx) *)
  0x48; 0x89; 0x47; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% rax) *)
  0x48; 0x89; 0x17;        (* MOV (Memop Quadword (%% (rdi,0))) (% rdx) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x8b; 0x56; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x0f; 0xc8;        (* BSWAP (% rax) *)
  0x48; 0x0f; 0xca;        (* BSWAP (% rdx) *)
  0x48; 0x89; 0x47; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% rax) *)
  0x48; 0x89; 0x57; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% rdx) *)
  0xc3                     (* RET *)
];;

let bignum_bigendian_4_tmc = define_trimmed "bignum_bigendian_4_tmc" bignum_bigendian_4_mc;;

let BIGNUM_BIGENDIAN_4_EXEC = X86_MK_CORE_EXEC_RULE bignum_bigendian_4_tmc;;

(* ------------------------------------------------------------------------- *)
(* Proof as a "frombebytes" function.                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_FROMBEBYTES_4_CORRECT = time prove
 (`!z x l pc.
      nonoverlapping (word pc,0x2b) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_bigendian_4_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,32)) s = l)
           (\s. read RIP s = word (pc + 0x2a) /\
                bignum_from_memory(z,4) s = num_of_bytelist (REVERSE l))
          (MAYCHANGE [RIP; RAX; RDX] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `l:byte list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BYTELIST_DIGITIZE_TAC "b_" `read (memory :> bytelist (x,32)) s0` THEN
  BIGNUM_DIGITIZE_TAC "d_" `bignum_from_memory(x,4) s0` THEN
  EVERY_ASSUM(fun th ->
   try MP_TAC(GEN_REWRITE_RULE LAND_CONV
        [CONJUNCT2(CONJUNCT2 READ_MEMORY_BYTESIZED_SPLIT)] th)
   with Failure _ -> ALL_TAC) THEN
  REWRITE_TAC[IMP_IMP] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
        [READ_MEMORY_BYTESIZED_SPLIT] THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  X86_STEPS_TAC BIGNUM_BIGENDIAN_4_EXEC (1--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "l" THEN REWRITE_TAC[REVERSE; APPEND] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[num_of_bytelist] THEN
  CONV_TAC WORD_BLAST);;

let BIGNUM_FROMBEBYTES_4_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x l pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_bigendian_4_tmc) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_bigendian_4_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,32)) s = l)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = num_of_bytelist (REVERSE l))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_bigendian_4_tmc
    BIGNUM_FROMBEBYTES_4_CORRECT);;

let BIGNUM_FROMBEBYTES_4_SUBROUTINE_CORRECT = time prove
 (`!z x l pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_bigendian_4_mc) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_bigendian_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,32)) s = l)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = num_of_bytelist (REVERSE l))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_FROMBEBYTES_4_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* As a "tobebytes" function.                                                *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_TOBEBYTES_4_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x2b) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_bigendian_4_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = word (pc + 0x2a) /\
                read (memory :> bytelist(z,32)) s =
                REVERSE(bytelist_of_num 32 n))
          (MAYCHANGE [RIP; RAX; RDX] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ONCE_REWRITE_TAC[READ_BYTES_EQ_BYTELIST; READ_BYTELIST_EQ_BYTES] THEN
  REWRITE_TAC[LENGTH_REVERSE; LENGTH_BYTELIST_OF_NUM] THEN
  MP_TAC(ISPECL [`z:int64`; `x:int64`; `bytelist_of_num 32 n`; `pc:num`]
        BIGNUM_FROMBEBYTES_4_CORRECT) THEN
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
  SIMP_TAC[]);;

let BIGNUM_TOBEBYTES_4_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_bigendian_4_tmc) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_bigendian_4_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytelist(z,32)) s =
                REVERSE(bytelist_of_num 32 n))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_bigendian_4_tmc
    BIGNUM_TOBEBYTES_4_CORRECT);;

let BIGNUM_TOBEBYTES_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_bigendian_4_mc) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_bigendian_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytelist(z,32)) s =
                REVERSE(bytelist_of_num 32 n))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TOBEBYTES_4_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* As a bignum-to-bignum operation.                                          *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_BIGENDIAN_4_CORRECT = time prove
 (`!z x n pc.
      nonoverlapping (word pc,0x2b) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (BUTLAST bignum_bigendian_4_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = word (pc + 0x2a) /\
                bignum_from_memory(z,4) s =
                num_of_bytelist(REVERSE(bytelist_of_num 32 n)))
          (MAYCHANGE [RIP; RAX; RDX] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
        [BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[READ_BYTES_EQ_BYTELIST] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  MP_TAC(ISPECL [`z:int64`; `x:int64`; `bytelist_of_num 32 n`; `pc:num`]
        BIGNUM_FROMBEBYTES_4_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
  SIMP_TAC[]);;

let BIGNUM_BIGENDIAN_4_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_bigendian_4_tmc) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_bigendian_4_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory(z,4) s =
                num_of_bytelist(REVERSE(bytelist_of_num 32 n)))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_bigendian_4_tmc
    BIGNUM_BIGENDIAN_4_CORRECT);;

let BIGNUM_BIGENDIAN_4_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
      nonoverlapping (stackpointer,8) (z,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_bigendian_4_mc) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_bigendian_4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory(z,4) s =
                num_of_bytelist(REVERSE(bytelist_of_num 32 n)))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_BIGENDIAN_4_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_bigendian_4_windows_mc = define_from_elf
   "bignum_bigendian_4_windows_mc" "x86/p256/bignum_bigendian_4.obj";;

let bignum_bigendian_4_windows_tmc = define_trimmed "bignum_bigendian_4_windows_tmc" bignum_bigendian_4_windows_mc;;

let BIGNUM_FROMBEBYTES_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x l pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_bigendian_4_windows_tmc); (x,8 * 4)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_bigendian_4_windows_tmc) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_bigendian_4_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,32)) s = l)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = num_of_bytelist (REVERSE l))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_bigendian_4_windows_tmc
    bignum_bigendian_4_tmc BIGNUM_FROMBEBYTES_4_CORRECT);;

let BIGNUM_FROMBEBYTES_4_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x l pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_bigendian_4_windows_mc); (x,8 * 4)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_bigendian_4_windows_mc) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_bigendian_4_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                read (memory :> bytelist(x,32)) s = l)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory (z,4) s = num_of_bytelist (REVERSE l))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_FROMBEBYTES_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

let BIGNUM_TOBEBYTES_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_bigendian_4_windows_tmc); (x,8 * 4)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_bigendian_4_windows_tmc) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_bigendian_4_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytelist(z,32)) s =
                REVERSE(bytelist_of_num 32 n))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_bigendian_4_windows_tmc
    bignum_bigendian_4_tmc BIGNUM_TOBEBYTES_4_CORRECT);;

let BIGNUM_TOBEBYTES_4_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_bigendian_4_windows_mc); (x,8 * 4)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_bigendian_4_windows_mc) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_bigendian_4_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                read (memory :> bytelist(z,32)) s =
                REVERSE(bytelist_of_num 32 n))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_TOBEBYTES_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

let BIGNUM_BIGENDIAN_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_bigendian_4_windows_tmc); (x,8 * 4)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_bigendian_4_windows_tmc) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_bigendian_4_windows_tmc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory(z,4) s =
                num_of_bytelist(REVERSE(bytelist_of_num 32 n)))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_bigendian_4_windows_tmc
    bignum_bigendian_4_tmc BIGNUM_BIGENDIAN_4_CORRECT);;

let BIGNUM_BIGENDIAN_4_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!z x n pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,LENGTH bignum_bigendian_4_windows_mc); (x,8 * 4)] /\
      nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
      nonoverlapping (word pc,LENGTH bignum_bigendian_4_windows_mc) (z,8 * 4) /\
      (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
      ==> ensures x86
           (\s. bytes_loaded s (word pc) bignum_bigendian_4_windows_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                WINDOWS_C_ARGUMENTS [z; x] s /\
                bignum_from_memory(x,4) s = n)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                bignum_from_memory(z,4) s =
                num_of_bytelist(REVERSE(bytelist_of_num 32 n)))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bignum(z,4);
                      memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_BIGENDIAN_4_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* (specs generated with generate_four_variants_of_x86_safety_specs)         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_bigendian_4" subroutine_signatures)
    BIGNUM_BIGENDIAN_4_CORRECT
    BIGNUM_BIGENDIAN_4_EXEC;;

let BIGNUM_BIGENDIAN_4_SAFE = time prove
 (`exists f_events.
       forall e z x pc.
           nonoverlapping (word pc,43) (z,8 * 4) /\
           (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) (BUTLAST bignum_bigendian_4_tmc) /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [z; x] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + 42) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events x z pc /\
                         memaccess_inbounds e2 [x,32; z,32] [z,32]))
               (MAYCHANGE [RIP; RAX; RDX] ,,
                MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bignum (z,4)])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars BIGNUM_BIGENDIAN_4_EXEC);;

let BIGNUM_BIGENDIAN_4_NOIBT_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e z x pc stackpointer returnaddress.
        nonoverlapping (stackpointer,8) (z,8 * 4) /\
        nonoverlapping (word pc,LENGTH bignum_bigendian_4_tmc) (z,8 * 4) /\
        (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_bigendian_4_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [z; x] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events x z pc stackpointer returnaddress /\
                      memaccess_inbounds e2 [x,32; z,32; stackpointer,8]
                      [z,32; stackpointer,0]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum (z,4)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_bigendian_4_tmc BIGNUM_BIGENDIAN_4_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let BIGNUM_BIGENDIAN_4_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e z x pc stackpointer returnaddress.
        nonoverlapping (stackpointer,8) (z,8 * 4) /\
        nonoverlapping (word pc,LENGTH bignum_bigendian_4_mc) (z,8 * 4) /\
        (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_bigendian_4_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [z; x] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events x z pc stackpointer returnaddress /\
                      memaccess_inbounds e2 [x,32; z,32; stackpointer,8]
                      [z,32; stackpointer,0]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bignum (z,4)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_BIGENDIAN_4_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_BIGENDIAN_4_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e z x pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [word pc,LENGTH bignum_bigendian_4_windows_tmc; x,8 * 4] /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
        nonoverlapping (word pc,LENGTH bignum_bigendian_4_windows_tmc)
        (z,8 * 4) /\
        (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_bigendian_4_windows_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [z; x] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events x z pc (word_sub stackpointer (word 16))
                      returnaddress /\
                      memaccess_inbounds e2
                      [x,32; z,32; word_sub stackpointer (word 16),24]
                      [z,32; word_sub stackpointer (word 16),16]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bignum (z,4);
              memory :> bytes (word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_bigendian_4_windows_tmc bignum_bigendian_4_tmc
    BIGNUM_BIGENDIAN_4_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let BIGNUM_BIGENDIAN_4_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e z x pc stackpointer returnaddress.
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
        [word pc,LENGTH bignum_bigendian_4_windows_mc; x,8 * 4] /\
        nonoverlapping (word_sub stackpointer (word 16),24) (z,8 * 4) /\
        nonoverlapping (word pc,LENGTH bignum_bigendian_4_windows_mc)
        (z,8 * 4) /\
        (x = z \/ nonoverlapping (x,8 * 4) (z,8 * 4))
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) bignum_bigendian_4_windows_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [z; x] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events x z pc (word_sub stackpointer (word 16))
                      returnaddress /\
                      memaccess_inbounds e2
                      [x,32; z,32; word_sub stackpointer (word 16),24]
                      [z,32; word_sub stackpointer (word 16),16]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bignum (z,4);
              memory :> bytes (word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_BIGENDIAN_4_NOIBT_WINDOWS_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* The aliases bignum_frombebytes_4 and bignum_tobebytes_4 run the same      *)
(* code, and their signatures and correctness theorems give the same safety  *)
(* specifications. This is checked for the core one here; those of the       *)
(* subroutine forms are derived from it and the assumptions of the           *)
(* subroutine correctness theorems, which are also the same.                 *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_FROMBEBYTES_4_SAFE = prove
 (fst(mk_safety_spec ~keep_maychanges:true
       (assoc "bignum_frombebytes_4" subroutine_signatures)
       BIGNUM_FROMBEBYTES_4_CORRECT BIGNUM_BIGENDIAN_4_EXEC),
  MATCH_ACCEPT_TAC BIGNUM_BIGENDIAN_4_SAFE);;

let BIGNUM_FROMBEBYTES_4_NOIBT_SUBROUTINE_SAFE =
  BIGNUM_BIGENDIAN_4_NOIBT_SUBROUTINE_SAFE;;

let BIGNUM_FROMBEBYTES_4_SUBROUTINE_SAFE =
  BIGNUM_BIGENDIAN_4_SUBROUTINE_SAFE;;

let BIGNUM_FROMBEBYTES_4_NOIBT_WINDOWS_SUBROUTINE_SAFE =
  BIGNUM_BIGENDIAN_4_NOIBT_WINDOWS_SUBROUTINE_SAFE;;

let BIGNUM_FROMBEBYTES_4_WINDOWS_SUBROUTINE_SAFE =
  BIGNUM_BIGENDIAN_4_WINDOWS_SUBROUTINE_SAFE;;

let BIGNUM_TOBEBYTES_4_SAFE = prove
 (fst(mk_safety_spec ~keep_maychanges:true
       (assoc "bignum_tobebytes_4" subroutine_signatures)
       BIGNUM_TOBEBYTES_4_CORRECT BIGNUM_BIGENDIAN_4_EXEC),
  MATCH_ACCEPT_TAC BIGNUM_BIGENDIAN_4_SAFE);;

let BIGNUM_TOBEBYTES_4_NOIBT_SUBROUTINE_SAFE =
  BIGNUM_BIGENDIAN_4_NOIBT_SUBROUTINE_SAFE;;

let BIGNUM_TOBEBYTES_4_SUBROUTINE_SAFE =
  BIGNUM_BIGENDIAN_4_SUBROUTINE_SAFE;;

let BIGNUM_TOBEBYTES_4_NOIBT_WINDOWS_SUBROUTINE_SAFE =
  BIGNUM_BIGENDIAN_4_NOIBT_WINDOWS_SUBROUTINE_SAFE;;

let BIGNUM_TOBEBYTES_4_WINDOWS_SUBROUTINE_SAFE =
  BIGNUM_BIGENDIAN_4_WINDOWS_SUBROUTINE_SAFE;;
