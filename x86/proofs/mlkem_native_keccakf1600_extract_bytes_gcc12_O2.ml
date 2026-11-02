(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extraction of bytes from a Keccak state.                                  *)
(* This is the code for mlkem_keccakf1600_extract_bytes from mlkem-native's  *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which copies len bytes of the 200-byte state     *)
(* starting at byte off. It is verified in the whole image (see              *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x3d10.        *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    3d10: mov    edx,edx
    3d12: test   ecx,ecx
    3d14: je     3d30 <mlkem_keccakf1600_extract_bytes+0x20>
    3d16: mov    ecx,ecx
    3d18: xor    eax,eax
    3d1a: add    rdi,rdx
    3d1d: nop    DWORD PTR [rax]
    3d20: movzx  edx,BYTE PTR [rdi+rax*1]
    3d24: mov    BYTE PTR [rsi+rax*1],dl
    3d27: add    rax,0x1
    3d2b: cmp    rcx,rax
    3d2e: jne    3d20 <mlkem_keccakf1600_extract_bytes+0x10>
    3d30: ret
 ***)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x3d10,0x3d31];;

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
(* Correctness proof. As in common/fips202.ml, the state is a 1600-bit word  *)
(* S, and the bytes extracted are bytes off to off + len - 1 of it, which as *)
(* a number are (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len).             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_CORRECT = prove
 (`!a d off len (S:1600 word) pc.
    aligned 16 (word pc:int64) /\
    off + len <= 200 /\
    ALL (nonoverlapping (d,len)) [(word pc,0x82a0); (a,200)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + 0x3d10) /\
           C_ARGUMENTS [a; d; word off; word len] s /\
           read (memory :> wbytes a) s = S)
      (\s. read RIP s = word (pc + 0x3d30) /\
           read (memory :> bytes(d,len)) s =
           (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(d,len)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `S:1600 word`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; READ_MEMORY_WBYTES_VAL] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The case len = 0, where nothing is done ***)

  ASM_CASES_TAC `len = 0` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];
    ALL_TAC] THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `len:num` `pc + 0x3d20` `pc + 0x3d2b`
   `\i s. read RAX s = word i /\ read RSI s = d /\ read RCX s = word len /\
          read RDI s = word_add a (word off) /\
          read (memory :> bytes(a,200)) s = val(S:1600 word) /\
          read (memory :> bytes(d,i)) s =
          (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--2) THEN
    EXTRACT_BYTES_ARGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (3--7) THEN
    ARGS_32_TAC [`off:num`; `len:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];

    (*** The loop body, copying one byte, which is loaded from         ***)
    (*** a + (off + 1 * i), as the address from the index register is  ***)
    (*** normalized                                                    ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `off + 1 * i`;
                  `s0:x86state`] READ_MEMORY_BYTES8_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    VAL_INT64_TAC `i:num` THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EXTRACT_BYTES_BYTE_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--2) THEN
    SUBGOAL_THEN `~(val(word_sub (word len) (word i):int64) = 0)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `len < 2 EXP 64 /\ i < 2 EXP 64` MP_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!a d off len (S:1600 word) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    off + len <= 200 /\
    ALL (nonoverlapping (d,len))
        [(word pc,0x82a0); (a,200); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + 0x3d10) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [a; d; word off; word len] s /\
           read (memory :> wbytes a) s = S)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           read (memory :> bytes(d,len)) s =
           (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(d,len)])`,
  X86_ADD_RETURN_NOSTACK_TAC
   MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
   MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SAFE = time prove
 (`exists f_events.
       forall e a d off len pc.
           aligned 16 (word pc:int64) /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len)) [word pc,0x82a0; a,200]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x3d10) /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0x3d30) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc /\
                         memaccess_inbounds e2 [a,200; d,len] [d,len]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(d,len)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (d:int64) (off:num) (len:num) (pc:num).
      if len = 0 then f_ev_len0 a d off len pc
      else
        APPEND
          (f_ev_epil a d off len pc)
          (APPEND
            (ENUMERATEL len (\i. f_ev_loop a d off len pc i))
            (f_ev_prol a d off len pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[] THENL
   [X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC (1--3) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + 0x3d20` `pc + 0x3d30`
    `\i s. read RAX s = word i /\ read RSI s = d /\ read RCX s = word len /\
           read RDI s = word_add a (word off)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--2) THEN
    EXTRACT_BYTES_ARGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (3--7) THEN
    ARGS_32_TAC [`off:num`; `len:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  VAL_INT64_TAC `i:num` THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
   (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXTRACT_BYTES_TEST_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e a d off len pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len))
               [word pc,0x82a0; a,200; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x3d10) /\
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
                MAYCHANGE [memory :> bytes(d,len)])`,
  X86_ADD_RETURN_NOSTACK_TAC
   MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
   MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for callers  *)
(* whose events depend on the result, such as the rejection sampling in      *)
(* mlkem_poly_rej_uniform. Separate correctness and safety theorems are      *)
(* ensures statements whose postconditions might hold at different points of *)
(* an execution, so they cannot be combined after the fact; here the loop    *)
(* invariant of the correctness proof is used with the events of the safety  *)
(* proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_FULL = time prove
 (`exists f_events.
       forall e a d off len (S:1600 word) pc.
           aligned 16 (word pc:int64) /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len)) [word pc,0x82a0; a,200]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x3d10) /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read (memory :> wbytes a) s = S /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0x3d30) /\
                    read (memory :> bytes(d,len)) s =
                    (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc /\
                         memaccess_inbounds e2 [a,200; d,len] [d,len]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(d,len)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (d:int64) (off:num) (len:num) (pc:num).
      if len = 0 then f_ev_len0 a d off len pc
      else
        APPEND
          (f_ev_epil a d off len pc)
          (APPEND
            (ENUMERATEL len (\i. f_ev_loop a d off len pc i))
            (f_ev_prol a d off len pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `S:1600 word`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              READ_MEMORY_WBYTES_VAL;
              fst MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The case len = 0, where nothing is done ***)

  ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[] THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN

  (*** The loop invariant, with the loop test at the end of the body ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + 0x3d20` `pc + 0x3d30`
   `\i s. read RAX s = word i /\ read RSI s = d /\ read RCX s = word len /\
          read RDI s = word_add a (word off) /\
          read (memory :> bytes(a,200)) s = val(S:1600 word) /\
          read (memory :> bytes(d,i)) s =
          (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--2) THEN
    EXTRACT_BYTES_ARGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (3--7) THEN
    ARGS_32_TAC [`off:num`; `len:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, copying one byte, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `off + 1 * i`;
                  `s0:x86state`] READ_MEMORY_BYTES8_OF_NUM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    VAL_INT64_TAC `i:num` THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EXTRACT_BYTES_TEST_TAC THEN
    CONJ_TAC THENL [EXTRACT_BYTES_BYTE_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop exit, at the return ***)

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  time prove
 (`exists f_events.
       forall e a d off len (S:1600 word) pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len))
               [word pc,0x82a0; a,200; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x3d10) /\
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
                MAYCHANGE [memory :> bytes(d,len)])`,
  X86_ADD_RETURN_NOSTACK_TAC
   MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
   MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_FULL THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
