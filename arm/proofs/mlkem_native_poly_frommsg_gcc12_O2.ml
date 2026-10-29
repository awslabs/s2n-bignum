(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 32-byte message to a polynomial.                          *)
(* This is the code for mlkem_poly_frommsg from mlkem-native's portable C    *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see                                    *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x22e0.        *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    22e0: mov     x6, x0
    22e4: mov     x5, x1
    22e8: mov     x3, #0x0
    22ec: mov     w8, #0x1
    22f0: mov     w7, #0x681
    22f4: nop
    22f8: lsl     w4, w3, #3
    22fc: mov     w1, #0x0
    2300: lsl     w0, w8, w1
    2304: ldrb    w2, [x5, x3]
    2308: and     w0, w0, #0xff
    230c: and     w0, w0, w2
    2310: neg     w0, w0
    2314: add     w2, w1, w4
    2318: and     w0, w7, w0, asr #16
    231c: add     w1, w1, #0x1
    2320: strh    w0, [x6, x2, lsl #1]
    2324: cmp     w1, #0x8
    2328: b.ne    2300 <mlkem_poly_frommsg+0x20>
    232c: add     x3, x3, #0x1
    2330: cmp     x3, #0x20
    2334: b.ne    22f8 <mlkem_poly_frommsg+0x18>
    2338: ret
 ***)

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x22e0,0x233c];;

(* ------------------------------------------------------------------------- *)
(* The bits of a byte of an array given as a number.                         *)
(* ------------------------------------------------------------------------- *)

let BYTE_BIT = prove
 (`!n m k. k < 8
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 256) DIV 2 EXP k) MOD 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP m`,`x:num`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM(SPEC `2` EXP_1)] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; ARITH_RULE `256 = 2 EXP 8`;
              MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k < 8 ==> MIN 8 (k + 1) = k + 1`]);;

(* ------------------------------------------------------------------------- *)
(* In the inner loop, which is unrolled in the simulation, tidy up the index *)
(* 8 * i + k of the coefficient (k the iteration of the inner loop) before   *)
(* it is used in the store with a shifted register offset.                   *)
(* ------------------------------------------------------------------------- *)

let FROMMSG_INDEX_TAC k =
  let jt = if k = 0 then `8 * i` else
           mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k) in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X2 s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "FROMMSG_INDEX_TAC");;

let FROMMSG_BODY_TAC =
  SUBGOAL_THEN `word_zx (word_shl (word_zx (word i:int64):int32) 3):int64 =
                word(8 * i)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [WORD_SMALL_TAC; ALL_TAC] THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC
     ((3 + 11 * k)--(8 + 11 * k)) THEN
    FROMMSG_INDEX_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC
     ((9 + 11 * k)--(13 + 11 * k))) (0--7);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 1 in common/fips203.ml, the    *)
(* result for a bit y is the integer closest to 3329 * y / 2, rounding up on *)
(* ties, i.e. (3329 * y + 1) DIV 2.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,0x6480); (a,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x22e0) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,32)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The outer loop, over the bytes, with the test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x22f8` `pc + 0x2330`
   `\i s. read X3 s = word i /\
          read X5 s = a /\
          read X6 s = r /\
          read X7 s = word 1665 /\
          read X8 s = word 1 /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,32)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP j) MOD 2 + 1) DIV 2))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for one byte and eight coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `32`; `n:num`; `i:num`; `s0:armstate`]
                 READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC (1--2) THEN
    FROMMSG_BODY_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC (91--91) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 8 * (i + 1) <=>
      j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
      j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
      j = 8 * i + 7`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[BYTE_BIT; ARITH] THEN
    REWRITE_TAC[GSYM(CONV_RULE NUM_REDUCE_CONV
     (SPECL [`n DIV 2 EXP (8 * i)`; `2`; `128`] MOD_MOD))] THEN

    (*** Check all values of the byte ***)

    MP_TAC(SPECL [`n DIV 2 EXP (8 * i)`; `256`] MOD_LT_EQ) THEN
    REWRITE_TAC[ARITH_EQ] THEN
    SPEC_TAC(`(n DIV 2 EXP (8 * i)) MOD 256`,`m:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC (2--3) THEN
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

let mlkem_native_poly_frommsg_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 32]", "true")],
   "void",
   [("a", "32", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_frommsg_signature
    MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,0x6480; a,32]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x22e0) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,32; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc returnaddress)
        (APPEND
          (ENUMERATEL 32 (\i. f_ev_loop a r pc returnaddress i))
          (f_ev_prol a r pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x22f8` `pc + 0x2338`
    `\i s. read X30 s = returnaddress /\
           read X3 s = word i /\
           read X5 s = a /\
           read X6 s = r /\
           read X8 s = word 1` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC (1--6) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC (1--2) THEN
  FROMMSG_BODY_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_EXEC (91--93) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(val(word_add (word i) (word 18446744073709551585):int64) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    ASM_CASES_TAC `i = 31` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 /\ ~(i = 31)
      ==> i + 18446744073709551585 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
