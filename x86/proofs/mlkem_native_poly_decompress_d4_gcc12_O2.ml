(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 4 bits per coefficient.                *)
(* This is the code for mlkem_poly_decompress_d4 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). It is verified in the whole image (see           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2740.        *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2740: xor    edx,edx
    2742: nop    WORD PTR [rax+rax*1+0x0]
    2748: movzx  eax,BYTE PTR [rsi+rdx*1]
    274c: and    eax,0xf
    274f: imul   eax,eax,0xd01
    2755: add    eax,0x8
    2758: shr    eax,0x4
    275b: mov    WORD PTR [rdi+rdx*4],ax
    275f: movzx  eax,BYTE PTR [rsi+rdx*1]
    2763: shr    al,0x4
    2766: movzx  eax,al
    2769: imul   eax,eax,0xd01
    276f: add    eax,0x8
    2772: shr    eax,0x4
    2775: mov    WORD PTR [rdi+rdx*4+0x2],ax
    277a: add    rdx,0x1
    277e: cmp    rdx,0x80
    2785: jne    2748 <mlkem_poly_decompress_d4+0x8>
    2787: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2740,0x2788];;

(* ------------------------------------------------------------------------- *)
(* The two 4-bit fields of a byte of an array given as a number.             *)
(* ------------------------------------------------------------------------- *)

let BYTE_NIBBLES = prove
 (`(!n k. (n DIV 2 EXP k) MOD 2 EXP 4 = ((n DIV 2 EXP k) MOD 256) MOD 16) /\
   (!n k. (n DIV 2 EXP (k + 4)) MOD 2 EXP 4 =
          ((n DIV 2 EXP k) MOD 256) DIV 16)`,
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN REPEAT STRIP_TAC THEN
  SPEC_TAC(`n DIV 2 EXP k`,`x:num`) THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `256 = 16 * 16`; MOD_MOD; DIV_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 4 in common/fips203.ml, the    *)
(* result for a 4-bit field y is the integer closest to 3329 * y / 16,       *)
(* rounding up on ties, i.e. (3329 * y + 8) DIV 16.                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_CORRECT = prove
 (`!r a n pc.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,512)) [(word pc,0x82a0); (a,128)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + 0x2740) /\
           C_ARGUMENTS [r; a] s /\
           read (memory :> bytes(a,128)) s = n)
      (\s. read RIP s = word (pc + 0x2787) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word((3329 * (n DIV 2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + 0x2748` `pc + 0x277e`
   `\i s. read RDI s = r /\
          read RSI s = a /\
          read RDX s = word i /\
          read (memory :> bytes(a,128)) s = n /\
          (!j. j < 2 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (4 * j)) MOD 2 EXP 4 + 8)
                        DIV 16))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for one byte and two coefficients. The byte is   ***)
    (*** loaded at a + 1 * i, from the index register.                   ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `128`; `n:num`; `1 * i`; `s0:x86state`]
                 READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    VAL_INT64_TAC `i:num` THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 2 * (i + 1) <=> j < 2 * i \/ j = 2 * i \/ j = 2 * i + 1`] THEN
    REWRITE_TAC[TAUT `(p \/ q \/ r ==> s) <=>
                      (p ==> s) /\ (q ==> s) /\ (r ==> s)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * 2 * i = 4 * i`;
                ARITH_RULE `2 * (2 * i + 1) = 4 * i + 2`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `4 * 2 * i = 8 * i`;
                ARITH_RULE `4 * (2 * i + 1) = 8 * i + 4`; MULT_CLAUSES] THEN
    REWRITE_TAC[BYTE_NIBBLES] THEN

    (*** Check all values of the byte ***)

    MP_TAC(SPECL [`n DIV 2 EXP (8 * i)`; `256`] MOD_LT_EQ) THEN
    REWRITE_TAC[ARITH_EQ] THEN
    SPEC_TAC(`(n DIV 2 EXP (8 * i)) MOD 256`,`m:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN `~(val(word_sub (word i) (word 128):int64) = 0)`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 128` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,512))
        [(word pc,0x82a0); (a,128); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + 0x2740) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [r; a] s /\
           read (memory :> bytes(a,128)) s = n)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word((3329 * (n DIV 2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SAFE = time prove
 (`exists f_events.
       forall e r a pc.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512)) [word pc,0x82a0; a,128]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x2740) /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0x2787) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2 [a,128; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num).
      APPEND
        (f_ev_epil a r pc)
        (APPEND
          (ENUMERATEL 128 (\i. f_ev_loop a r pc i))
          (f_ev_prol a r pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + 0x2748` `pc + 0x2787`
    `\i s. read RDI s = r /\ read RSI s = a /\ read RDX s = word i` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--2) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  VAL_INT64_TAC `i:num` THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--16) THEN
  SUBGOAL_THEN
   `~(val(word_add (word i) (word 18446744073709551489):int64) = 0) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_ADD_CASES; DIMINDEX_64] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT;
                 ARITH_RULE `i < 128 ==> i < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 128` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,0x82a0; a,128; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x2740) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [a,128; r,512; stackpointer,8] [r,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
