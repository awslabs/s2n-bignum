(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extraction of bytes from a Keccak state. This is the code for             *)
(* mlkem_keccakf1600_extract_bytes from mlkem-native's portable C            *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which copies len bytes of the 200-byte state starting at byte off. It is  *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x2c60.                                            *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2c60: mov     w2, w2
    2c64: cbz     w3, 2c8c <mlkem_keccakf1600_extract_bytes+0x2c>
    2c68: mov     w3, w3
    2c6c: add     x4, x0, x2
    2c70: mov     x0, #0x0
    2c74: nop
    2c78: ldrb    w2, [x4, x0]
    2c7c: strb    w2, [x1, x0]
    2c80: add     x0, x0, #0x1
    2c84: cmp     x3, x0
    2c88: b.ne    2c78 <mlkem_keccakf1600_extract_bytes+0x18>
    2c8c: ret
 ***)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2c60,0x2c90];;

(*** The zero-extended arguments off and len, and the test of len ***)

let EXTRACT_BYTES_ARGS_TAC =
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  FIRST_ASSUM(fun th ->
    if concl th <> `~(len = 0)` then NO_TAC else
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = concl th then th' else REWRITE_RULE[th] th'));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As in common/fips202.ml, the state is a 1600-bit word  *)
(* S, and the bytes extracted are bytes off to off + len - 1 of it, which    *)
(* as a number are (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len).          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!a d off len (S:1600 word) pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (d,len)) [(word pc,0x6480); (a,200)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2c60) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read (memory :> wbytes a) s = S)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(d,len)) s =
                  (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d,len)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `S:1600 word`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; READ_MEMORY_WBYTES_VAL] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The case len = 0, where nothing is done ***)

  ASM_CASES_TAC `len = 0` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];
    ALL_TAC] THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `len:num` `pc + 0x2c78` `pc + 0x2c84`
   `\i s. read X0 s = word i /\ read X1 s = d /\ read X3 s = word len /\
          read X4 s = word_add a (word off) /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,200)) s = val(S:1600 word) /\
          read (memory :> bytes(d,i)) s =
          (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--2) THEN
    EXTRACT_BYTES_ARGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (3--6) THEN
    ARGS_32_TAC [`off:num`; `len:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];

    (*** The loop body, copying one byte ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `off + i`;
                  `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
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
    REWRITE_TAC[MULT_CLAUSES; MOD_MULT_MOD] THEN ARITH_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend on off as well   *)
(* as len, so the theorem is stated directly rather than by mk_safety_spec.  *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e a d off len pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len)) [word pc,0x6480; a,200]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x2c60) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc returnaddress /\
                         memaccess_inbounds e2 [a,200; d,len] [d,len]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (d,len)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (d:int64) (off:num) (len:num) (pc:num)
      (returnaddress:int64).
      if len = 0 then f_ev_len0 a d off len pc returnaddress
      else
        APPEND
          (f_ev_epil a d off len pc returnaddress)
          (APPEND
            (ENUMERATEL len (\i. f_ev_loop a d off len pc returnaddress i))
            (f_ev_prol a d off len pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[] THENL
   [ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC (1--3) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + 0x2c78` `pc + 0x2c8c`
    `\i s. read X30 s = returnaddress /\
           read X0 s = word i /\ read X1 s = d /\ read X3 s = word len /\
           read X4 s = word_add a (word off)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--2) THEN
    EXTRACT_BYTES_ARGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (3--6) THEN
    ARGS_32_TAC [`off:num`; `len:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
   (1--5) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
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
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
