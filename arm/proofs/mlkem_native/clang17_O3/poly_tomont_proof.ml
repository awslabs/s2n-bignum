(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of polynomial coefficients to Montgomery form.                 *)
(* This is the code for mlkem_poly_tomont from mlkem-native's portable C     *)
(* implementation compiled by clang 17 with -O3 (see                         *)
(* mlkem_native/README.md), which the compiler has vectorized, 16            *)
(* coefficients at a time. Unlike the gcc 12 -O2 code, it makes its vectors  *)
(* of constants with MOV, DUP and MVNI instead of loading them from the      *)
(* read-only data. It is verified in the whole image (see libmlkem.ml).      *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_tomont:
       +0x0: mov     w9, #0x549
       +0x4: mov     w10, #0x50490000
       +0x8: mov     x8, xzr
       +0xc: mvni    v2.4s, #0xd, lsl #8
      +0x10: dup     v0.8h, w9
      +0x14: dup     v1.4s, w10
      +0x18: add     x9, x0, x8
      +0x1c: add     x8, x8, #0x20
      +0x20: cmp     x8, #0x200
      +0x24: ldp     q3, q4, [x9]
      +0x28: sxtl    v5.4s, v3.4h
      +0x2c: sxtl2   v6.4s, v3.8h
      +0x30: sxtl    v7.4s, v4.4h
      +0x34: mul     v5.4s, v5.4s, v1.4s
      +0x38: mul     v7.4s, v7.4s, v1.4s
      +0x3c: sxtl2   v16.4s, v4.8h
      +0x40: mul     v6.4s, v6.4s, v1.4s
      +0x44: mul     v16.4s, v16.4s, v1.4s
      +0x48: sshr    v5.4s, v5.4s, #16
      +0x4c: sshr    v7.4s, v7.4s, #16
      +0x50: smull2  v17.4s, v3.8h, v0.8h
      +0x54: sshr    v6.4s, v6.4s, #16
      +0x58: smull   v3.4s, v3.4h, v0.4h
      +0x5c: smull2  v18.4s, v4.8h, v0.8h
      +0x60: smull   v4.4s, v4.4h, v0.4h
      +0x64: mul     v5.4s, v5.4s, v2.4s
      +0x68: mul     v7.4s, v7.4s, v2.4s
      +0x6c: sshr    v16.4s, v16.4s, #16
      +0x70: mul     v6.4s, v6.4s, v2.4s
      +0x74: mul     v16.4s, v16.4s, v2.4s
      +0x78: addhn   v3.4h, v5.4s, v3.4s
      +0x7c: addhn   v4.4h, v7.4s, v4.4s
      +0x80: addhn2  v3.8h, v6.4s, v17.4s
      +0x84: addhn2  v4.8h, v16.4s, v18.4s
      +0x88: stp     q3, q4, [x9]
      +0x8c: b.ne    <mlkem_poly_tomont+0x18>
      +0x90: ret
 ***)

let MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_tomont"];;

(* ------------------------------------------------------------------------- *)
(* Splitting off the 16 coefficients handled by one iteration of the loop.   *)
(* ------------------------------------------------------------------------- *)

let CHUNK16_INPUT_SPLIT = prove
 (`!P i. i < 16
         ==> ((!j. 16 * i <= j /\ j < 256 ==> P j) <=>
              (!j. 16 * (i + 1) <= j /\ j < 256 ==> P j) /\
              (!k. k < 16 ==> P(16 * i + k)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `16 * (i + 1) <= j` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 16 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `16 * i <= j ==> 16 * i + (j - 16 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CHUNK16_OUTPUT_SPLIT = prove
 (`!P i. (!j. j < 16 * (i + 1) ==> P j) <=>
         (!j. j < 16 * i ==> P j) /\ (!k. k < 16 ==> P(16 * i + k))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j < 16 * i` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 16 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < 16 * i) ==> 16 * i + (j - 16 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CHUNK16_ADDR = prove
 (`!a i k. word_add a (word(2 * (16 * i + k))):int64 =
           word_add (word_add a (word(32 * i))) (word(2 * k))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(*** Addresses word_add (word_add a (word(32 * i + 16))) (word k) and the
 *** like, as the simulation leaves them, in the form
 *** word_add a (word(32 * i + k')) of the specification
 ***)

let ADDR_NORM_CONV =
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
  REWRITE_CONV[GSYM ADD_ASSOC] THENC NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The value computed in each lane. The code computes the Montgomery         *)
(* reduction of x * 1353, but with the low half of the quotient computed     *)
(* from x directly, as the high half of x * (20553 * 2^16) for               *)
(* 20553 = 1353 * 62209 mod 2^16 (62209 being 3329^-1 mod 2^16). This is     *)
(* the same as montred_neon.                                                 *)
(* ------------------------------------------------------------------------- *)

let TOMONT_CLANG17_O3_FACTOR = prove
 (`!x:int16.
     word_ishr (word_mul (word_sx x) (word 1346961408)) 16:int32 =
     word_sx (word_mul (word_subword (word_mul (word_sx x) (word 1353):int32)
                                     (0,16))
                       (word 62209):int16)`,
  BITBLAST_TAC);;

let TOMONT_CLANG17_O3_MONTRED = prove
 (`!x:int16.
     word_subword
      (word_add
        (word_mul
          (word_ishr (word_mul (word_shl (word_sx x:int32) 0)
                               (word 1346961408)) 16)
          (word 4294963967))
        (word_mul (word_sx x) (word 1353)):int32) (16,16):int16 =
     montred_neon(word_mul (word_sx x) (word 1353))`,
  REWRITE_TAC[WORD_SHL_ZERO; TOMONT_CLANG17_O3_FACTOR; montred_neon]);;

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

let MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a x pc returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
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

  (*** The loop invariant, with the loop test at the end of the body ***)

  ENSURES_WHILE_UP2_TAC `16` `pc + mlkem_poly_tomont_loop1`
   `pc + mlkem_poly_tomont_loop1_exit`
   `\i s. read X0 s = a /\ read X8 s = word(32 * i) /\
          read X30 s = returnaddress /\
          read Q0 s = word 0x05490549054905490549054905490549 /\
          read Q1 s = word 0x50490000504900005049000050490000 /\
          read Q2 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
          (!j. 16 * i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          (!j. j < 16 * i
               ==> let z_j = read(memory :> bytes16
                                (word_add a (word(2 * j)))) s in
                   (ival z_j == (tomont_3329 (ival o x)) j) (mod &3329) /\
                   abs(ival z_j) <= &3328)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of the constants and the offset ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;

    (*** The loop body, for 16 coefficients loaded as two 128-bit words ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [MATCH_MP CHUNK16_INPUT_SPLIT (ASSUME `i < 16`)]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK16_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add a (word(32 * i)))) s0`) THEN
    MP_TAC(CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
                                 NORMALIZE_RELATIVE_ADDRESS_CONV))
     (READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add (word_add a (word(32 * i)))
                                        (word 16))) s0`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[montred_neon]) (1--30) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read (memory :> bytes128 a) s30 = x`) o
             concl))) THEN
    RULE_ASSUM_TAC(fun th ->
      if free_in `bytes16` (concl th) && not(is_forall(concl th))
      then CONV_RULE ADDR_NORM_CONV th else th) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_add (word(32 * i)) (word 18446744073709551136):int64) =
        0) <=>
      i + 1 < 16`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      ASM_CASES_TAC `i = 15` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 16 /\ ~(i = 15)
        ==> 32 * i + 18446744073709551136 < 18446744073709551616`] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[CHUNK16_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[tomont_3329; o_THM; TOMONT_CLANG17_O3_MONTRED; TOMONT_LANE];

    (*** The return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_EXEC (1--1) THEN
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

(*** The signature is the same as for mlkem_tomont ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_tomont" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (a,512) (word pc,libmlkem_size)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_tomont) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc returnaddress /\
                        memaccess_inbounds e2 [a,512] [a,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a pc returnaddress)
        (APPEND
          (ENUMERATEL 16 (\i. f_ev_loop a pc returnaddress i))
          (f_ev_prol a pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `16` `pc + mlkem_poly_tomont_loop1`
   `pc + mlkem_poly_tomont_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = a /\ read X8 s = word(32 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_EXEC (1--6) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_TOMONT_CLANG17_O3_EXEC (1--30) THEN
  SUBGOAL_THEN
   `~(val(word_add (word(32 * i)) (word 18446744073709551136):int64) = 0) <=>
    i + 1 < 16`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    ASM_CASES_TAC `i = 15` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 16 /\ ~(i = 15)
      ==> 32 * i + 18446744073709551136 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
