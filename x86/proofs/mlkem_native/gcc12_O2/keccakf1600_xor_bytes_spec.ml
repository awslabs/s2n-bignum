(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* XOR of bytes into a Keccak state. This is the code for                    *)
(* mlkem_keccakf1600_xor_bytes from mlkem-native's portable C implementation *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which XORs len  *)
(* bytes of data into the 200-byte state starting at byte off. It is         *)
(* verified in the whole image (see libmlkem.ml).                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_keccakf1600_xor_bytes:
       +0x0: mov    edx,edx
       +0x2: test   ecx,ecx
       +0x4: je     <mlkem_keccakf1600_xor_bytes+0x22>
       +0x6: mov    ecx,ecx
       +0x8: add    rdi,rdx
       +0xb: lea    rdx,[rsi+rcx*1]
       +0xf: nop
      +0x10: movzx  eax,BYTE PTR [rsi]
      +0x13: add    rsi,0x1
      +0x17: xor    BYTE PTR [rdi],al
      +0x19: add    rdi,0x1
      +0x1d: cmp    rsi,rdx
      +0x20: jne    <mlkem_keccakf1600_xor_bytes+0x10>
      +0x22: ret
 ***)

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_keccakf1600_xor_bytes"];;

(*** The zero-extended arguments off and len, and the test of len ***)

let XOR_BYTES_ARGS_TAC =
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  FIRST_ASSUM(fun th ->
    if concl th <> `~(len = 0)` then NO_TAC else
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = concl th then th' else REWRITE_RULE[th] th'));;

(* ------------------------------------------------------------------------- *)
(* The state after i of the bytes of the data m have been XORed into it, as  *)
(* bytes. Only byte off + i changes in the next step.                        *)
(* ------------------------------------------------------------------------- *)

let BYTE_UPDATE_STMT =
  `!x c k j.
        x < 2 EXP (8 * k) /\ c < 256
        ==> ((x + 2 EXP (8 * k) * c) DIV 2 EXP (8 * j)) MOD 256 =
            if j = k then c else (x DIV 2 EXP (8 * j)) MOD 256`;;

let BYTE_UPDATE =
  assume_spec BYTE_UPDATE_STMT;;

let XOR_BYTES_STEP_STMT =
  `!(S:1600 word) m off i j.
        off + i < 200 /\ j < 200
        ==> word_subword
             (word_xor S (word(2 EXP (8 * off) *
                               m MOD 2 EXP (8 * (i + 1)))))
             (8 * j,8):byte =
            if j = off + i
            then word_xor
                  (word_subword
                    (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                    (8 * j,8))
                  (word((m DIV 2 EXP (8 * i)) MOD 256))
            else word_subword
                  (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                  (8 * j,8)`;;

let XOR_BYTES_STEP =
  assume_spec XOR_BYTES_STEP_STMT;;

(*** The invariant for the bytes other than byte t ***)

let XOR_BYTES_RESTRICT_RULE t th =
  let j,bod = dest_forall(concl th) in
  let p,q = dest_imp bod in
  let p' = mk_conj(p,mk_neg(mk_eq(j,t))) in
  GEN j (DISCH p' (MP (SPEC j th) (CONJUNCT1(ASSUME p'))));;

(*** The facts for byte off + i of the state and byte i of the data, with
 *** the others restricted so that they are kept over the store
 ***)

let XOR_BYTES_STATE_TAC =
  SUBGOAL_THEN `off + i < 200` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes8` (concl th) then
      ASSUME_TAC(MP (SPEC `off + i` th) (ASSUME `off + i < 200`)) THEN
      ASSUME_TAC(XOR_BYTES_RESTRICT_RULE `off + i` th)
    else failwith "XOR_BYTES_RESTRICT_RULE") THEN
  MP_TAC(SPECL [`d:int64`; `len:num`; `m:num`; `i:num`; `s0:x86state`]
               READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(*** The incremented pointers, the new bytes of the state and the test ***)

let XOR_BYTES_PTRS_TAC =
  MAP_EVERY (fun _ -> CONJ_TAC THENL
    [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC]; ALL_TAC])
   (1--2);;

let XOR_BYTES_BYTE_TAC =
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[XOR_BYTES_STEP] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_VAL_MOD_256] THEN AP_TERM_TAC THEN
  SPEC_TAC(`word((m DIV 2 EXP (8 * i)) MOD 256):byte`,`b:byte`) THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));;

let XOR_BYTES_TEST_TAC =
  SUBGOAL_THEN
   `~(val(word_sub (word_add (word_add d (word i)) (word 1))
                   (word_add d (word len)):int64) = 0) <=>
    i + 1 < len`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `len < 2 EXP 64 /\ i + 1 < 2 EXP 64` MP_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  XOR_BYTES_PTRS_TAC;;

(*** The bytes of the state at the start, and the whole state at the end ***)

let XOR_BYTES_INIT_TAC =
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; WORD_XOR_0; word_subword] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES8_OF_NUM THEN
  EXISTS_TAC `200` THEN ASM_REWRITE_TAC[];;

let XOR_BYTES_FINAL_TAC =
  SUBGOAL_THEN `m MOD 2 EXP (8 * len) = m`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC MOD_LT THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
      `read (memory :> bytes (d,len)) s = m`) o concl)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC] THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(rand w)) VAL_BOUND)) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  DISCH_THEN(fun th -> SUBST1_TAC(SYM(MATCH_MP MOD_LT th))) THEN
  REWRITE_TAC[ARITH_RULE `1600 = 8 * 200`] THEN
  MATCH_MP_TAC READ_MEMORY_BYTES_OF_BYTES8 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_subword; ARITH_RULE `2 EXP 8 = 256`]) THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As in keccak_absorb in common/fips202/fips202.ml, the  *)
(* state is a 1600-bit word S. The len bytes of data, as a number m, are     *)
(* XORed into it starting at byte off, giving word_xor S                     *)
(* (word(2 EXP (8 * off) * m)).                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_CORRECT_STMT =
  `!a d off len (S:1600 word) m pc.
    aligned 16 (word pc:int64) /\
    off + len <= 200 /\
    ALL (nonoverlapping (a,200)) [(word pc,libmlkem_size); (d,len)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_keccakf1600_xor_bytes) /\
           C_ARGUMENTS [a; d; word off; word len] s /\
           read (memory :> wbytes a) s = S /\
           read (memory :> bytes(d,len)) s = m)
      (\s. read RIP s = word (pc + mlkem_keccakf1600_xor_bytes_ret) /\
           read (memory :> wbytes a) s =
           word_xor S (word(2 EXP (8 * off) * m)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,200)])`;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_CORRECT_STMT;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a d off len (S:1600 word) m pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    off + len <= 200 /\
    ALL (nonoverlapping (a,200))
        [(word pc,libmlkem_size); (d,len); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_keccakf1600_xor_bytes) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [a; d; word off; word len] s /\
           read (memory :> wbytes a) s = S /\
           read (memory :> bytes(d,len)) s = m)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           read (memory :> wbytes a) s =
           word_xor S (word(2 EXP (8 * off) * m)))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,200)])`;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SAFE_STMT =
  `exists f_events.
       forall e a d off len pc.
           aligned 16 (word pc:int64) /\
           off + len <= 200 /\
           ALL (nonoverlapping (a,200)) [word pc,libmlkem_size; d,len]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_keccakf1600_xor_bytes) /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_keccakf1600_xor_bytes_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc /\
                         memaccess_inbounds e2 [d,len; a,200] [a,200]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,200)])`;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SAFE_STMT;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a d off len pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           off + len <= 200 /\
           ALL (nonoverlapping (a,200))
               [word pc,libmlkem_size; d,len; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_keccakf1600_xor_bytes) /\
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
                          [d,len; a,200; stackpointer,8] [a,200]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,200)])`;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* mlkem_keccakf1600_extract_bytes.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_FULL_STMT =
  `exists f_events.
       forall e a d off len (S:1600 word) m pc.
           aligned 16 (word pc:int64) /\
           off + len <= 200 /\
           ALL (nonoverlapping (a,200)) [word pc,libmlkem_size; d,len]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_keccakf1600_xor_bytes) /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read (memory :> wbytes a) s = S /\
                    read (memory :> bytes(d,len)) s = m /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_keccakf1600_xor_bytes_ret) /\
                    read (memory :> wbytes a) s =
                    word_xor S (word(2 EXP (8 * off) * m)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc /\
                         memaccess_inbounds e2 [d,len; a,200] [a,200]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,200)])`;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_FULL =
  assume_spec MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_FULL_STMT;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a d off len (S:1600 word) m pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           off + len <= 200 /\
           ALL (nonoverlapping (a,200))
               [word pc,libmlkem_size; d,len; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_keccakf1600_xor_bytes) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read (memory :> wbytes a) s = S /\
                    read (memory :> bytes(d,len)) s = m /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    read (memory :> wbytes a) s =
                    word_xor S (word(2 EXP (8 * off) * m)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc stackpointer
                                returnaddress /\
                         memaccess_inbounds e2
                          [d,len; a,200; stackpointer,8] [a,200]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,200)])`;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
