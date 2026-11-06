(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of polynomial coefficients to Montgomery form. This is the     *)
(* code for mlkem_poly_tomont from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -O3 (see mlkem_native/README.md), which the       *)
(* compiler has vectorized. It is verified in the whole image (see           *)
(* libmlkem.ml). The loop is the same as with -O2, but the vector of 0xf2ff  *)
(* is made with MVNI instead of MOVI, and the two vectors of constants       *)
(* loaded from the read-only data are not next to each other: that of        *)
(* 3329^-1 mod 2^16, which other functions share, is at the start of the     *)
(* block mlkem_poly_tomont_consts, and that of 1353 at its end. So the       *)
(* theorem of constant time and memory safety has that block of              *)
(* mlkem_poly_tomont_consts_size bytes as a read-only region, where with -O2 *)
(* it has the 32 bytes of the two vectors.                                   *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_tomont:
       +0x0: adrp    x2, <page>
       +0x4: adrp    x1, <page>
       +0x8: mvni    v3.8h, #0xd, lsl #8
       +0xc: ldr     q5, [x2, #2336]
      +0x10: ldr     q4, [x1, #2400]
      +0x14: add     x1, x0, #0x200
      +0x18: ldr     q0, [x0]
      +0x1c: smull   v1.4s, v0.4h, v4.4h
      +0x20: smull2  v0.4s, v0.8h, v4.8h
      +0x24: uzp1    v2.8h, v1.8h, v0.8h
      +0x28: mul     v2.8h, v2.8h, v5.8h
      +0x2c: smlal   v1.4s, v2.4h, v3.4h
      +0x30: smlal2  v0.4s, v2.8h, v3.8h
      +0x34: uzp2    v1.8h, v1.8h, v0.8h
      +0x38: str     q1, [x0], #16
      +0x3c: cmp     x1, x0
      +0x40: b.ne    <mlkem_poly_tomont+0x18>
      +0x44: ret
 ***)

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_tomont"];;

(*** The vectors of 3329^-1 mod 2^16 and of 1353 = 2^32 mod 3329 ***)

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_CONSTANTS =
  map (fun d -> MLKEM_NATIVE_IMAGE_CONST_RULE d 128)
   [layout "mlkem_poly_tomont_const1"; layout "mlkem_poly_tomont_const2"];;

(* ------------------------------------------------------------------------- *)
(* The value computed in each lane.                                          *)
(* ------------------------------------------------------------------------- *)

let TOMONT_LANE = prove
 (`!x:int16.
     (ival(montred_neon(word_mul (word_sx x) (word 1353))) ==
      (&2 pow 16 * ival x) rem &3329) (mod &3329) /\
     abs(ival(montred_neon(word_mul (word_sx x) (word 1353)))) <= &3328`,
  GEN_TAC THEN REWRITE_TAC[MONTRED_NEON_SCALAR; INT_CONG_RREM] THEN
  MP_TAC(MLKEM_NATIVE_CONGBOUND_RULE undefined
   `montred_scalar(word_mul (word_sx (x:int16)) (word 1353))`) THEN
  MATCH_MP_TAC(TAUT `(p ==> p') /\ (q ==> q') ==> p /\ q ==> p' /\ q'`) THEN
  CONJ_TAC THENL [ALL_TAC; INT_ARITH_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(a * b:int == c) (mod n)
    ==> (x == a * y * b) (mod n) ==> (x == c * y) (mod n)`) THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a x pc returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O3_mc /\
           read PC s = word (pc + mlkem_poly_tomont) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word (2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 256
               ==> let z_i = read(memory :> bytes16
                                (word_add a (word (2 * i)))) s in
                   (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `x:num->int16`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + mlkem_poly_tomont_loop1`
   `pc + mlkem_poly_tomont_loop1_test`
   `\i s. read X0 s = word_add a (word(16 * i)) /\
          read X1 s = word_add a (word 512) /\
          read X30 s = returnaddress /\
          read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
          read Q4 s = word 0x05490549054905490549054905490549 /\
          read Q5 s = word 0xf301f301f301f301f301f301f301f301 /\
          (!j. 8 * i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          (!j. j < 8 * i
               ==> let z_j = read(memory :> bytes16
                                (word_add a (word(2 * j)))) s in
                   (ival z_j == (tomont_3329 (ival o x)) j) (mod &3329) /\
                   abs(ival z_j) <= &3328)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vectors of constants from the image ***)

    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
      MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_CONSTANTS THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC (3--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;

    (*** The loop body, for 8 coefficients loaded as one 128-bit word ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [MATCH_MP CHUNK8_INPUT_SPLIT (ASSUME `i < 32`)]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add a (word(16 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[montred_neon]) (1--9) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (fun th ->
        can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
        free_in `a:int64` (concl th))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[tomont_3329; o_THM; TOMONT_LANE];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `tomont_3329` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The signature is the same as for mlkem_tomont, and the block of the ***)
(*** vectors of constants is a read-only object.                         ***)

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + mlkem_poly_tomont_consts):int64`,
                       `mlkem_poly_tomont_consts_size:num`]
    ~keep_maychanges:true
    (assoc "mlkem_tomont" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (a,512) (word pc,libmlkem_size)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_tomont) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc returnaddress /\
                        memaccess_inbounds e2
                         [a,512;
                          word (pc + mlkem_poly_tomont_consts),
                          mlkem_poly_tomont_consts_size] [a,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a pc returnaddress)
        (APPEND
          (ENUMERATEL 32 (\i. f_ev_loop a pc returnaddress i))
          (f_ev_prol a pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_tomont_loop1`
   `pc + mlkem_poly_tomont_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = word_add a (word(16 * i)) /\
           read X1 s = word_add a (word 512)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC (3--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O3_EXEC (1--11) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add a (word 512))
                   (word_add (word_add a (word (16 * i))) (word 16)):int64) =
      0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
      word_sub x (word_add y z)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 16 * i + 16 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
