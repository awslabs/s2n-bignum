(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a polynomial to a 32-byte message.                          *)
(* This is the code for mlkem_poly_tomsg from mlkem-native's portable C      *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see                                    *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2340.        *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2340: mov     w8, #0xafb8
    2344: mov     x4, x0
    2348: mov     x6, x1
    234c: mov     x3, #0x0
    2350: movk    w8, #0x13, lsl #16
    2354: mov     w7, #0x40000000
    2358: lsl     w5, w3, #3
    235c: mov     w2, #0x0
    2360: mov     w1, #0x0
    2364: strb    wzr, [x4, x3]
    2368: add     w0, w1, w5
    236c: ldrsh   w0, [x6, x0, lsl #1]
    2370: madd    w0, w0, w8, w7
    2374: lsr     w0, w0, #31
    2378: lsl     w0, w0, w1
    237c: orr     w2, w2, w0
    2380: and     w2, w2, #0xff
    2384: add     w1, w1, #0x1
    2388: strb    w2, [x4, x3]
    238c: cmp     w1, #0x8
    2390: b.ne    2368 <mlkem_poly_tomsg+0x28>
    2394: add     x3, x3, #0x1
    2398: cmp     x3, #0x20
    239c: b.ne    2358 <mlkem_poly_tomsg+0x18>
    23a0: ret
 ***)

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2340,0x23a4];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to one bit, as computed.                 *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D1_ARITH = prove
 (`!v. v < 3329
       ==> (1073741824 + v * 1290168) DIV 2147483648 =
           (4 * v + 3329) DIV 6658`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`4 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(4 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(4 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(1073741824 + v * 1290168) - q * 2147483648` THEN
  ASM_ARITH_TAC);;

let TOMSG_BIT = prove
 (`!y:int16.
        val y < 3329
        ==> word_ushr
             (word_zx (word_zx
               (word (1073741824 +
                      val (word_zx (word_zx (word_sx y:int32):int64):int32) *
                      1290168):int32):int64):int32) 31 =
            word(((4 * val y + 3329) DIV 6658) MOD 2)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SX_SMALL; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_32_64; MOD_MOD_REFL] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`] THEN
  SUBGOAL_THEN `((4 * val(y:int16) + 3329) DIV 6658) MOD 2 < 4294967296`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 ==> x < 4294967296`) THEN
    REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2147483648 * 2`; GSYM DIV_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[COMPRESS_D1_ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Splitting off the bits for one byte from the number for the message.      *)
(* ------------------------------------------------------------------------- *)

let NSUM_BYTE = prove
 (`!f m. nsum {k | k < 8} (\k. f(m + k) * 2 EXP (m + k)) =
         2 EXP m * nsum {k | k < 8} (\k. f(m + k) * 2 EXP k)`,
  REWRITE_TAC[EXP_ADD; GSYM NSUM_LMUL] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[MULT_AC]);;

(* ------------------------------------------------------------------------- *)
(* In the inner loop, which is unrolled in the simulation, tidy up the index *)
(* 8 * i + k of the coefficient (k the iteration of the inner loop) before   *)
(* it is used in the load with a shifted register offset.                    *)
(* ------------------------------------------------------------------------- *)

let tomsg_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let TOMSG_INDEX_TAC k =
  let jt = el k tomsg_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X0 s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "TOMSG_INDEX_TAC");;

let TOMSG_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC (1--1) THEN
  SUBGOAL_THEN `word_zx (word_shl (word_zx (word i:int64):int32) 3):int64 =
                word(8 * i)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [WORD_SMALL_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC (2--4) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC
     ((5 + 11 * k)--(5 + 11 * k)) THEN
    TOMSG_INDEX_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC
     ((6 + 11 * k)--(15 + 11 * k))) (0--7) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC (93--93);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 1 in common/fips203.ml, the bit  *)
(* for a coefficient x in [0,3329) is the integer closest to 2 * x / 3329,   *)
(* rounding up on ties, modulo 2, i.e. ((4 * x + 3329) DIV 6658) MOD 2, and  *)
(* as for mlkem_encode 1 the bits are put together little-endian. Like the   *)
(* C code, this relies on the coefficients being in [0,3329).                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        ALL (nonoverlapping (r,32)) [(word pc,0x6480); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2340) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,32)) s =
                       nsum {i | i < 256}
                            (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 *
                                 2 EXP i)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,32)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The outer loop, over the bytes, with the test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x2358` `pc + 0x2398`
   `\i s. read X3 s = word i /\
          read X4 s = r /\
          read X6 s = a /\
          read X7 s = word 1073741824 /\
          read X8 s = word 1290168 /\
          read X30 s = returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          ((!j. j < 256 ==> val(x j) < 3329)
           ==> read(memory :> bytes(r,i)) s =
               nsum {j | j < 8 * i}
                (\j. ((4 * val(x j) + 3329) DIV 6658) MOD 2 * 2 EXP j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; NSUM_CLAUSES_NUMSEG_LT;
                READ_MEMORY_BYTES_TRIVIAL];

    (*** The loop body, for eight coefficients and one byte ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun jt ->
      FIRST_ASSUM(MP_TAC o SPEC jt o check (is_forall o concl)) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i < 32` THEN ARITH_TAC; DISCH_TAC])
     tomsg_indices THEN
    TOMSG_BODY_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    (*** Split off the new byte and the bits for it ***)

    REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`; NSUM_LT_ADD;
                EQ_ADD_LCANCEL] THEN
    REWRITE_TAC[BETA_RULE(ISPECL
     [`\j. ((4 * val((x:num->int16) j) + 3329) DIV 6658) MOD 2`; `8 * i`]
     NSUM_BYTE)] THEN
    REWRITE_TAC[EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[NUMSEG_LT; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN

    (*** The compression of each coefficient ***)

    MAP_EVERY (fun jt ->
      MP_TAC(SPEC (mk_comb(`x:num->int16`,jt)) TOMSG_BIT) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (can (term_match []
                `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o
          concl)) THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) tomsg_indices THEN

    (*** Check all combinations of the bits ***)

    MAP_EVERY (fun jt ->
      let ft = vsubst [mk_comb(`x:num->int16`,jt),`y:int16`]
                `((4 * val(y:int16) + 3329) DIV 6658) MOD 2` in
      MP_TAC(SPECL [lhand ft; `2`] MOD_LT_EQ) THEN REWRITE_TAC[ARITH_EQ] THEN
      SPEC_TAC(ft,genvar `:num`)) (rev tomsg_indices) THEN
    CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (is_imp o concl))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_tomsg_signature =
  ([("r", "uint8_t[static 32]", "false");
    ("a", "int16_t[static 256]", "true")],
   "void",
   [("a", "256", 2)],
   [("r", "32", 1)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_tomsg_signature
    MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           ALL (nonoverlapping (r,32)) [word pc,0x6480; a,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x2340) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,512; r,32] [r,32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,32)])`,
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
              fst MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x2358` `pc + 0x23a0`
    `\i s. read X30 s = returnaddress /\
           read X3 s = word i /\
           read X4 s = r /\
           read X6 s = a` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC (1--6) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  TOMSG_BODY_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_EXEC (94--95) THEN
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
