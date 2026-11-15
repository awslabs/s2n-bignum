(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extraction of bytes from a Keccak state. This is the code for             *)
(* mlkem_keccakf1600_extract_bytes from mlkem-native's portable C            *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which copies len bytes of the 200-byte state starting at byte off. It is  *)
(* verified in the whole image (see libmlkem.ml).                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_keccakf1600_extract_bytes:
       +0x0: mov    edx,edx
       +0x2: test   ecx,ecx
       +0x4: je     <mlkem_keccakf1600_extract_bytes+0x20>
       +0x6: mov    ecx,ecx
       +0x8: xor    eax,eax
       +0xa: add    rdi,rdx
       +0xd: nop    DWORD PTR [rax]
      +0x10: movzx  edx,BYTE PTR [rdi+rax*1]
      +0x14: mov    BYTE PTR [rsi+rax*1],dl
      +0x17: add    rax,0x1
      +0x1b: cmp    rcx,rax
      +0x1e: jne    <mlkem_keccakf1600_extract_bytes+0x10>
      +0x20: ret
 ***)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_keccakf1600_extract_bytes"];;

(*** The zero-extended arguments off and len, and the test of len ***)

let EXTRACT_BYTES_ARGS_TAC =
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  FIRST_ASSUM(fun th ->
    if concl th <> `~(len = 0)` then NO_TAC else
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = concl th then th' else REWRITE_RULE[th] th'));;

(*** The new byte of the result, and the loop test ***)

let EXTRACT_BYTES_BYTE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
  REWRITE_TAC[WORD_ADD; READ_MEMORY_BYTES_SNOC] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_16;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8 /\ 4294967296 = 2 EXP 32 /\
                          18446744073709551616 = 2 EXP 64`;
              MOD_MOD_EXP_MIN] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`val(S:1600 word) DIV 2 EXP (8 * off)`,`x:num`) THEN
  REWRITE_TAC[MULT_CLAUSES; MOD_MULT_MOD] THEN ARITH_TAC;;

let EXTRACT_BYTES_TEST_TAC =
  SUBGOAL_THEN
   `~(val(word_sub (word len) (word_add (word i) (word 1)):int64) = 0) <=>
    i + 1 < len`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `len < 2 EXP 64 /\ i + 1 < 2 EXP 64` MP_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As in common/fips202/fips202.ml, the state is a        *)
(* 1600-bit word S, and the bytes extracted are bytes off to off + len - 1   *)
(* of it, which as a number are                                              *)
(* (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len).                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_CORRECT_STMT =
  `!a d off len (S:1600 word) pc.
    aligned 16 (word pc:int64) /\
    off + len <= 200 /\
    ALL (nonoverlapping (d,len)) [(word pc,libmlkem_size); (a,200)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_keccakf1600_extract_bytes) /\
           C_ARGUMENTS [a; d; word off; word len] s /\
           read (memory :> wbytes a) s = S)
      (\s. read RIP s = word (pc + mlkem_keccakf1600_extract_bytes_ret) /\
           read (memory :> bytes(d,len)) s =
           (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(d,len)])`;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_CORRECT_STMT;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a d off len (S:1600 word) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    off + len <= 200 /\
    ALL (nonoverlapping (d,len))
        [(word pc,libmlkem_size); (a,200); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_keccakf1600_extract_bytes) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [a; d; word off; word len] s /\
           read (memory :> wbytes a) s = S)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           read (memory :> bytes(d,len)) s =
           (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(d,len)])`;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SAFE_STMT =
  `exists f_events.
       forall e a d off len pc.
           aligned 16 (word pc:int64) /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len)) [word pc,libmlkem_size; a,200]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_keccakf1600_extract_bytes) /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_keccakf1600_extract_bytes_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc /\
                         memaccess_inbounds e2 [a,200; d,len] [d,len]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(d,len)])`;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SAFE_STMT;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a d off len pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len))
               [word pc,libmlkem_size; a,200; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_keccakf1600_extract_bytes) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc stackpointer
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,200; d,len; stackpointer,8] [d,len]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(d,len)])`;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for callers  *)
(* whose events depend on the result, such as the rejection sampling in      *)
(* mlkem_poly_rej_uniform. Separate correctness and safety theorems are      *)
(* ensures statements whose postconditions might hold at different points of *)
(* an execution, so they cannot be combined after the fact; here the loop    *)
(* invariant of the correctness proof is used with the events of the safety  *)
(* proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_FULL_STMT =
  `exists f_events.
       forall e a d off len (S:1600 word) pc.
           aligned 16 (word pc:int64) /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len)) [word pc,libmlkem_size; a,200]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_keccakf1600_extract_bytes) /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read (memory :> wbytes a) s = S /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_keccakf1600_extract_bytes_ret) /\
                    read (memory :> bytes(d,len)) s =
                    (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc /\
                         memaccess_inbounds e2 [a,200; d,len] [d,len]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(d,len)])`;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_FULL =
  assume_spec MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_FULL_STMT;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a d off len (S:1600 word) pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len))
               [word pc,libmlkem_size; a,200; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_keccakf1600_extract_bytes) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read (memory :> wbytes a) s = S /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    read (memory :> bytes(d,len)) s =
                    (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc stackpointer
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,200; d,len; stackpointer,8] [d,len]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(d,len)])`;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
