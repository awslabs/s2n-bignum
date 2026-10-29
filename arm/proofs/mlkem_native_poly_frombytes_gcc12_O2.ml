(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of 12-bit coefficients from bytes, without reduction.           *)
(* This is the code for mlkem_poly_frombytes from mlkem-native's portable C  *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see                                    *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x22a0.        *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    22a0: add     x6, x1, #0x180
    22a4: nop
    22a8: ldrb    w2, [x1, #1]
    22ac: add     x0, x0, #0x4
    22b0: ldrb    w4, [x1, #2]
    22b4: ldrb    w5, [x1], #3
    22b8: ubfiz   w3, w2, #8, #4
    22bc: lsl     w4, w4, #4
    22c0: orr     w3, w3, w5
    22c4: orr     w2, w4, w2, lsr #4
    22c8: sturh   w3, [x0, #-4]
    22cc: sturh   w2, [x0, #-2]
    22d0: cmp     x6, x1
    22d4: b.ne    22a8 <mlkem_poly_frombytes+0x8>
    22d8: ret
 ***)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x22a0,0x22dc];;

(* ------------------------------------------------------------------------- *)
(* The two coefficients from three bytes.                                    *)
(* ------------------------------------------------------------------------- *)

let FROMBYTES_LANES = prove
 (`!n i.
     word_zx(word_join
              (word_subword (word((n DIV 2 EXP (24 * i + 8)) MOD 256):byte)
                            (0,4):4 word)
              (word((n DIV 2 EXP (24 * i)) MOD 256):byte):12 word):int16 =
     word((n DIV 2 EXP (24 * i)) MOD 4096) /\
     word_zx(word_join
              (word((n DIV 2 EXP (24 * i + 16)) MOD 256):byte)
              (word_subword (word((n DIV 2 EXP (24 * i + 8)) MOD 256):byte)
                            (4,4):4 word):12 word):int16 =
     word((n DIV 2 EXP (24 * i + 12)) MOD 4096)`,
  let rule = GEN_ALL o CONV_RULE NUM_REDUCE_CONV o SPEC_ALL in
  let l1 = rule(SPECL [`m:num`; `16`; `16`] MOD_MOD)
  and l2 = rule(GSYM(SPECL [`m:num`; `16`; `16`] DIV_MOD))
  and l3 = rule(SPECL [`m:num`; `256`; `16`] DIV_DIV)
  and l4 = rule(GSYM(SPECL [`m:num`; `4096`; `16`] DIV_DIV))
  and l5 = rule(GSYM(SPECL [`m:num`; `256`; `16`] MOD_MULT_MOD))
  and l6 = rule(GSYM(SPECL [`m:num`; `16`; `256`] MOD_MULT_MOD)) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP (24 * i)`,`m:num`) THEN
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_JOIN;
     VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL; DIV_1; l1; l2; l3] THEN
  REWRITE_TAC[l4] THEN REWRITE_TAC[l5; l6; MOD_MOD_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,0x6480); (a,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x22a0) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,384)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + 0x22a8` `pc + 0x22d0`
   `\i s. read X0 s = word_add r (word(4 * i)) /\
          read X1 s = word_add a (word(3 * i)) /\
          read X6 s = word_add a (word 384) /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,384)) s = n /\
          (!j. j < 2 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((n DIV 2 EXP (12 * j)) MOD 2 EXP 12))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for three bytes and two coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun k ->
      MP_TAC(SPECL [`a:int64`; `384`; `n:num`; k; `s0:armstate`]
                   READ_MEMORY_BYTES8_OF_NUM) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC])
     [`3 * i`; `3 * i + 1`; `3 * i + 2`] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE
       `j < 2 * (i + 1) <=> j < 2 * i \/ j = 2 * i \/ j = 2 * i + 1`] THEN
      REWRITE_TAC[TAUT `(p \/ q \/ r ==> s) <=>
                        (p ==> s) /\ (q ==> s) /\ (r ==> s)`;
                  FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `2 * 2 * i = 4 * i`;
                  ARITH_RULE `2 * (2 * i + 1) = 4 * i + 2`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM FROMBYTES_LANES] THEN
      CONJ_TAC THEN BYTES_BITBLAST_TAC];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_frombytes_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 384]", "true")],
   "void",
   [("a", "384", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_frombytes_signature
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,0x6480; a,384]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x22a0) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,384; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc returnaddress)
        (APPEND
          (ENUMERATEL 128 (\i. f_ev_loop a r pc returnaddress i))
          (f_ev_prol a r pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + 0x22a8` `pc + 0x22d8`
    `\i s. read X30 s = returnaddress /\
           read X0 s = word_add r (word(4 * i)) /\
           read X1 s = word_add a (word(3 * i)) /\
           read X6 s = word_add a (word 384)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--2) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--12) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add a (word 384))
                   (word_add (word_add a (word (3 * i))) (word 3)):int64) =
      0) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
      word_sub x (word_add y z)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 128 ==> 3 * i + 3 < 18446744073709551616`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`;
                ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
