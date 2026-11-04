(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of polynomials, coefficientwise with wraparound. This is the     *)
(* code for mlkem_poly_add from mlkem-native's portable C implementation     *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md), which the     *)
(* compiler has vectorized and unrolled completely, after a check that the   *)
(* two arrays do not overlap. It is verified in the whole image (see         *)
(* libmlkem.ml).                                                             *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image. If the arrays overlap, a scalar loop does the
 *** additions one at a time; otherwise the code from +0x3c does them on
 *** 16 pairs of Q registers, the pattern of +0x3c to +0x60 continuing
 *** with the offsets increased by 32 each time:

    mlkem_poly_add:
       +0x0: add     x8, x1, #0x200
       +0x4: cmp     x8, x0
       +0x8: b.ls    <mlkem_poly_add+0x3c>
       +0xc: add     x8, x0, #0x200
      +0x10: cmp     x8, x1
      +0x14: b.ls    <mlkem_poly_add+0x3c>
      +0x18: mov     x8, xzr
      +0x1c: ldrh    w9, [x0, x8]
      +0x20: ldrh    w10, [x1, x8]
      +0x24: add     w9, w10, w9
      +0x28: strh    w9, [x0, x8]
      +0x2c: add     x8, x8, #0x2
      +0x30: cmp     x8, #0x200
      +0x34: b.ne    <mlkem_poly_add+0x1c>
      +0x38: ret
      +0x3c: ldp     q0, q1, [x0]
      +0x40: ldp     q2, q3, [x1]
      +0x44: add     v0.8h, v2.8h, v0.8h
      +0x48: ldp     q4, q2, [x0, #32]
      +0x4c: add     v1.8h, v3.8h, v1.8h
      +0x50: stp     q0, q1, [x0]
      +0x54: ldp     q3, q5, [x1, #32]
      +0x58: add     v1.8h, v3.8h, v4.8h
      +0x5c: ldp     q0, q3, [x0, #64]
      +0x60: add     v2.8h, v5.8h, v2.8h
      ...
     +0x16c: ldp     q4, q5, [x1, #480]
     +0x170: add     v0.8h, v4.8h, v1.8h
     +0x174: add     v1.8h, v5.8h, v2.8h
     +0x178: stp     q0, q1, [x0, #480]
     +0x17c: ret
 ***)

let MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_add"];;

(* ------------------------------------------------------------------------- *)
(* The check for overlap. For arrays r and b of 512 bytes, the code takes    *)
(* the vectorized path if b + 512 <= r or r + 512 <= b, computed modulo      *)
(* 2^64. When the arrays do not overlap, one of these holds: if neither did, *)
(* the start of one array would be within the other, also when an array     *)
(* wraps around the end of the address space.                                *)
(* ------------------------------------------------------------------------- *)

let MOD_2N_CASES = prove
 (`!x n. x < 2 * n ==> x MOD n = if x < n then x else x - n`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC);;

let ALIAS_CHECK_512 = prove
 (`!r b:int64.
        nonoverlapping (r,512) (b,512)
        ==> ~(val r <= val (word_add b (word 512)) /\
              ~(val (word_sub (word_add b (word 512)) r) = 0)) \/
            ~(val b <= val (word_add r (word 512)) /\
              ~(val (word_sub (word_add r (word 512)) b) = 0))`,
  let n = `18446744073709551616` in
  let wit_tac i j =
    MAP_EVERY EXISTS_TAC [i; j] THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    W(fun (asl,w) -> let l,r = dest_eq w in
       MP_TAC(SPECL [lhand l; n] MOD_2N_CASES) THEN
       MP_TAC(SPECL [lhand r; n] MOD_2N_CASES)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC in
  let wrap_tacs =
   [wit_tac `0` `(m + 18446744073709551616) - p`;
    wit_tac `(p + 18446744073709551616) - m` `0`] in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; nonoverlapping_modulo] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `r:int64` VAL_BOUND_64) THEN
  MP_TAC(ISPEC `b:int64` VAL_BOUND_64) THEN
  SPEC_TAC(`val(r:int64)`,`m:num`) THEN SPEC_TAC(`val(b:int64)`,`p:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `!x. x < 2 EXP 64
        ==> (x + 512) MOD 18446744073709551616 =
            if x + 512 < 18446744073709551616 then x + 512
            else (x + 512) - 18446744073709551616`
  (fun th -> ASM_SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_2N_CASES THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_neg(concl th) && is_exists(rand(concl th)))) THEN
  REWRITE_TAC[CONG] THEN
  ASM_CASES_TAC `p + 512 < 18446744073709551616` THEN
  ASM_CASES_TAC `m + 512 < 18446744073709551616` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THEN
  (ASM_CASES_TAC `m:num <= p` THENL
    [FIRST(wit_tac `p - m:num` `0` :: wrap_tacs);
     FIRST(wit_tac `0` `m - p:num` :: wrap_tacs)]));;

(*** The two conditions, and using one of them in a case of the proof ***)

let ALIAS_CHECK_1 =
 `~(val (r:int64) <= val (word_add b (word 512):int64) /\
    ~(val (word_sub (word_add b (word 512)) r:int64) = 0))`
and ALIAS_CHECK_2 =
 `~(val (b:int64) <= val (word_add r (word 512):int64) /\
    ~(val (word_sub (word_add r (word 512)) b:int64) = 0))`;;

let USE_CASE_TAC c =
  FIRST_X_ASSUM(fun th ->
    if concl th = c then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_ADD_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r b x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (b,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_add) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add r (word(2 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add b (word(2 * i))))
                             s = y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word_add (x i) (y i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `b:int64`; `x:num->int16`; `y:num->int16`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_SEQUENCE_TAC `pc + mlkem_poly_add_join1`
   `\s. read X0 s = r /\ read X1 s = b /\ read X30 s = returnaddress /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                 x i) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add b (word(2 * i)))) s =
                 y i)` THEN
  CONJ_TAC THENL
   [

    (*** The check for overlap, which goes to the vectorized code ***)

    ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`r:int64`; `b:int64`] ALIAS_CHECK_512) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES]; DISCH_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC (1--3) THEN
    ASM_CASES_TAC ALIAS_CHECK_1 THENL
     [USE_CASE_TAC ALIAS_CHECK_1 THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      USE_CASE_TAC (mk_neg ALIAS_CHECK_1) THEN
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC (4--6) THEN
      USE_CASE_TAC ALIAS_CHECK_2 THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    ALL_TAC] THEN

  (*** The vectorized code, with the 32 blocks of 8 coefficients of each
   *** input as 128-bit words, and the 32 blocks of the result split again
   ***)

  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun v ->
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_forall(concl th) && free_in v (concl th))) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC) [`r:int64`; `b:int64`] THEN
  MAP_EVERY (fun v ->
    MAP_EVERY (fun k ->
      let a = if k = 0 then v else
              mk_comb(mk_comb(`word_add:int64->int64->int64`,v),
                      mk_comb(`word:num->int64`,mk_small_numeral(16 * k))) in
      MP_TAC(READ_MEMORY_MERGE_CONV 3
        (subst [a,`a:int64`] `read(memory :> bytes128 a) s0`))) (0--31))
   [`r:int64`; `b:int64`] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC[]) (1--81) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (fun th -> can (term_match [] `read (memory :> bytes128 a) s81 = x`)
                         (concl th)))) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_add_signature =
  ([("r", "int16_t[static 256]", "false");
    ("b", "int16_t[static 256]", "true")],
   "void",
   [("r", "256", 2); ("b", "256", 2)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_add_signature
    MLKEM_NATIVE_POLY_ADD_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_ADD_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r b pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; b,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_add) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; b] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events b r pc returnaddress /\
                         memaccess_inbounds e2 [r,512; b,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(b:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_vec b r pc returnaddress)
        (if ~(val r <= val (word_add b (word 512)) /\
              ~(val (word_sub (word_add b (word 512)) r) = 0))
         then f_ev_check1 b r pc returnaddress
         else f_ev_check2 b r pc returnaddress)
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_add_join1`
   `\s. read X0 s = r /\ read X1 s = b /\ read X30 s = returnaddress` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`r:int64`; `b:int64`] ALIAS_CHECK_512) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES]; DISCH_TAC] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC (1--3) THEN
    ASM_CASES_TAC ALIAS_CHECK_1 THENL
     [USE_CASE_TAC ALIAS_CHECK_1 THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      USE_CASE_TAC (mk_neg ALIAS_CHECK_1) THEN
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC (4--6) THEN
      USE_CASE_TAC ALIAS_CHECK_2 THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC (1--81) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
