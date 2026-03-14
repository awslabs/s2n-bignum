(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise multiplication and accumulation of polynomials in ML-DSA NTT    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "arm/mldsa/mldsa_pointwise_acc_l5.o";;
 ****)

let mldsa_pointwise_acc_l5_mc = define_assert_from_elf
 "mldsa_pointwise_acc_l5_mc" "arm/mldsa/mldsa_pointwise_acc_l5.o"
[
  0x529c0023;       (* arm_MOV W3 (rvalue (word 57345)) *)
  0x72a00fe3;       (* arm_MOVK W3 (word 127) 16 *)
  0x4e040c60;       (* arm_DUP_GEN Q0 X3 32 128 *)
  0x52840023;       (* arm_MOV W3 (rvalue (word 8193)) *)
  0x72a07003;       (* arm_MOVK W3 (word 896) 16 *)
  0x4e040c61;       (* arm_DUP_GEN Q1 X3 32 128 *)
  0xd2800803;       (* arm_MOV X3 (rvalue (word 64)) *)
  0x3dc00431;       (* arm_LDR Q17 X1 (Immediate_Offset (word 16)) *)
  0x3dc00832;       (* arm_LDR Q18 X1 (Immediate_Offset (word 32)) *)
  0x3dc00c33;       (* arm_LDR Q19 X1 (Immediate_Offset (word 48)) *)
  0x3cc40430;       (* arm_LDR Q16 X1 (Postimmediate_Offset (word 64)) *)
  0x3dc00455;       (* arm_LDR Q21 X2 (Immediate_Offset (word 16)) *)
  0x3dc00856;       (* arm_LDR Q22 X2 (Immediate_Offset (word 32)) *)
  0x3dc00c57;       (* arm_LDR Q23 X2 (Immediate_Offset (word 48)) *)
  0x3cc40454;       (* arm_LDR Q20 X2 (Postimmediate_Offset (word 64)) *)
  0x0eb4c218;       (* arm_SMULL_VEC Q24 Q16 Q20 32 *)
  0x4eb4c219;       (* arm_SMULL2_VEC Q25 Q16 Q20 32 *)
  0x0eb5c23a;       (* arm_SMULL_VEC Q26 Q17 Q21 32 *)
  0x4eb5c23b;       (* arm_SMULL2_VEC Q27 Q17 Q21 32 *)
  0x0eb6c25c;       (* arm_SMULL_VEC Q28 Q18 Q22 32 *)
  0x4eb6c25d;       (* arm_SMULL2_VEC Q29 Q18 Q22 32 *)
  0x0eb7c27e;       (* arm_SMULL_VEC Q30 Q19 Q23 32 *)
  0x4eb7c27f;       (* arm_SMULL2_VEC Q31 Q19 Q23 32 *)
  0x3dc0f030;       (* arm_LDR Q16 X1 (Immediate_Offset (word 960)) *)
  0x3dc0f431;       (* arm_LDR Q17 X1 (Immediate_Offset (word 976)) *)
  0x3dc0f832;       (* arm_LDR Q18 X1 (Immediate_Offset (word 992)) *)
  0x3dc0fc33;       (* arm_LDR Q19 X1 (Immediate_Offset (word 1008)) *)
  0x3dc0f054;       (* arm_LDR Q20 X2 (Immediate_Offset (word 960)) *)
  0x3dc0f455;       (* arm_LDR Q21 X2 (Immediate_Offset (word 976)) *)
  0x3dc0f856;       (* arm_LDR Q22 X2 (Immediate_Offset (word 992)) *)
  0x3dc0fc57;       (* arm_LDR Q23 X2 (Immediate_Offset (word 1008)) *)
  0x0eb48218;       (* arm_SMLAL_VEC Q24 Q16 Q20 32 *)
  0x4eb48219;       (* arm_SMLAL2_VEC Q25 Q16 Q20 32 *)
  0x0eb5823a;       (* arm_SMLAL_VEC Q26 Q17 Q21 32 *)
  0x4eb5823b;       (* arm_SMLAL2_VEC Q27 Q17 Q21 32 *)
  0x0eb6825c;       (* arm_SMLAL_VEC Q28 Q18 Q22 32 *)
  0x4eb6825d;       (* arm_SMLAL2_VEC Q29 Q18 Q22 32 *)
  0x0eb7827e;       (* arm_SMLAL_VEC Q30 Q19 Q23 32 *)
  0x4eb7827f;       (* arm_SMLAL2_VEC Q31 Q19 Q23 32 *)
  0x3dc1f030;       (* arm_LDR Q16 X1 (Immediate_Offset (word 1984)) *)
  0x3dc1f431;       (* arm_LDR Q17 X1 (Immediate_Offset (word 2000)) *)
  0x3dc1f832;       (* arm_LDR Q18 X1 (Immediate_Offset (word 2016)) *)
  0x3dc1fc33;       (* arm_LDR Q19 X1 (Immediate_Offset (word 2032)) *)
  0x3dc1f054;       (* arm_LDR Q20 X2 (Immediate_Offset (word 1984)) *)
  0x3dc1f455;       (* arm_LDR Q21 X2 (Immediate_Offset (word 2000)) *)
  0x3dc1f856;       (* arm_LDR Q22 X2 (Immediate_Offset (word 2016)) *)
  0x3dc1fc57;       (* arm_LDR Q23 X2 (Immediate_Offset (word 2032)) *)
  0x0eb48218;       (* arm_SMLAL_VEC Q24 Q16 Q20 32 *)
  0x4eb48219;       (* arm_SMLAL2_VEC Q25 Q16 Q20 32 *)
  0x0eb5823a;       (* arm_SMLAL_VEC Q26 Q17 Q21 32 *)
  0x4eb5823b;       (* arm_SMLAL2_VEC Q27 Q17 Q21 32 *)
  0x0eb6825c;       (* arm_SMLAL_VEC Q28 Q18 Q22 32 *)
  0x4eb6825d;       (* arm_SMLAL2_VEC Q29 Q18 Q22 32 *)
  0x0eb7827e;       (* arm_SMLAL_VEC Q30 Q19 Q23 32 *)
  0x4eb7827f;       (* arm_SMLAL2_VEC Q31 Q19 Q23 32 *)
  0x3dc2f030;       (* arm_LDR Q16 X1 (Immediate_Offset (word 3008)) *)
  0x3dc2f431;       (* arm_LDR Q17 X1 (Immediate_Offset (word 3024)) *)
  0x3dc2f832;       (* arm_LDR Q18 X1 (Immediate_Offset (word 3040)) *)
  0x3dc2fc33;       (* arm_LDR Q19 X1 (Immediate_Offset (word 3056)) *)
  0x3dc2f054;       (* arm_LDR Q20 X2 (Immediate_Offset (word 3008)) *)
  0x3dc2f455;       (* arm_LDR Q21 X2 (Immediate_Offset (word 3024)) *)
  0x3dc2f856;       (* arm_LDR Q22 X2 (Immediate_Offset (word 3040)) *)
  0x3dc2fc57;       (* arm_LDR Q23 X2 (Immediate_Offset (word 3056)) *)
  0x0eb48218;       (* arm_SMLAL_VEC Q24 Q16 Q20 32 *)
  0x4eb48219;       (* arm_SMLAL2_VEC Q25 Q16 Q20 32 *)
  0x0eb5823a;       (* arm_SMLAL_VEC Q26 Q17 Q21 32 *)
  0x4eb5823b;       (* arm_SMLAL2_VEC Q27 Q17 Q21 32 *)
  0x0eb6825c;       (* arm_SMLAL_VEC Q28 Q18 Q22 32 *)
  0x4eb6825d;       (* arm_SMLAL2_VEC Q29 Q18 Q22 32 *)
  0x0eb7827e;       (* arm_SMLAL_VEC Q30 Q19 Q23 32 *)
  0x4eb7827f;       (* arm_SMLAL2_VEC Q31 Q19 Q23 32 *)
  0x3dc3f030;       (* arm_LDR Q16 X1 (Immediate_Offset (word 4032)) *)
  0x3dc3f431;       (* arm_LDR Q17 X1 (Immediate_Offset (word 4048)) *)
  0x3dc3f832;       (* arm_LDR Q18 X1 (Immediate_Offset (word 4064)) *)
  0x3dc3fc33;       (* arm_LDR Q19 X1 (Immediate_Offset (word 4080)) *)
  0x3dc3f054;       (* arm_LDR Q20 X2 (Immediate_Offset (word 4032)) *)
  0x3dc3f455;       (* arm_LDR Q21 X2 (Immediate_Offset (word 4048)) *)
  0x3dc3f856;       (* arm_LDR Q22 X2 (Immediate_Offset (word 4064)) *)
  0x3dc3fc57;       (* arm_LDR Q23 X2 (Immediate_Offset (word 4080)) *)
  0x0eb48218;       (* arm_SMLAL_VEC Q24 Q16 Q20 32 *)
  0x4eb48219;       (* arm_SMLAL2_VEC Q25 Q16 Q20 32 *)
  0x0eb5823a;       (* arm_SMLAL_VEC Q26 Q17 Q21 32 *)
  0x4eb5823b;       (* arm_SMLAL2_VEC Q27 Q17 Q21 32 *)
  0x0eb6825c;       (* arm_SMLAL_VEC Q28 Q18 Q22 32 *)
  0x4eb6825d;       (* arm_SMLAL2_VEC Q29 Q18 Q22 32 *)
  0x0eb7827e;       (* arm_SMLAL_VEC Q30 Q19 Q23 32 *)
  0x4eb7827f;       (* arm_SMLAL2_VEC Q31 Q19 Q23 32 *)
  0x4e991b10;       (* arm_UZP1 Q16 Q24 Q25 32 *)
  0x4ea19e10;       (* arm_MUL_VEC Q16 Q16 Q1 32 128 *)
  0x0ea0a218;       (* arm_SMLSL_VEC Q24 Q16 Q0 32 *)
  0x4ea0a219;       (* arm_SMLSL2_VEC Q25 Q16 Q0 32 *)
  0x4e995b10;       (* arm_UZP2 Q16 Q24 Q25 32 *)
  0x4e9b1b51;       (* arm_UZP1 Q17 Q26 Q27 32 *)
  0x4ea19e31;       (* arm_MUL_VEC Q17 Q17 Q1 32 128 *)
  0x0ea0a23a;       (* arm_SMLSL_VEC Q26 Q17 Q0 32 *)
  0x4ea0a23b;       (* arm_SMLSL2_VEC Q27 Q17 Q0 32 *)
  0x4e9b5b51;       (* arm_UZP2 Q17 Q26 Q27 32 *)
  0x4e9d1b92;       (* arm_UZP1 Q18 Q28 Q29 32 *)
  0x4ea19e52;       (* arm_MUL_VEC Q18 Q18 Q1 32 128 *)
  0x0ea0a25c;       (* arm_SMLSL_VEC Q28 Q18 Q0 32 *)
  0x4ea0a25d;       (* arm_SMLSL2_VEC Q29 Q18 Q0 32 *)
  0x4e9d5b92;       (* arm_UZP2 Q18 Q28 Q29 32 *)
  0x4e9f1bd3;       (* arm_UZP1 Q19 Q30 Q31 32 *)
  0x4ea19e73;       (* arm_MUL_VEC Q19 Q19 Q1 32 128 *)
  0x0ea0a27e;       (* arm_SMLSL_VEC Q30 Q19 Q0 32 *)
  0x4ea0a27f;       (* arm_SMLSL2_VEC Q31 Q19 Q0 32 *)
  0x4e9f5bd3;       (* arm_UZP2 Q19 Q30 Q31 32 *)
  0x3d800411;       (* arm_STR Q17 X0 (Immediate_Offset (word 16)) *)
  0x3d800812;       (* arm_STR Q18 X0 (Immediate_Offset (word 32)) *)
  0x3d800c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 48)) *)
  0x3c840410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 64)) *)
  0xf1001063;       (* arm_SUBS X3 X3 (rvalue (word 4)) *)
  0xb5fff2e3;       (* arm_CBNZ X3 (word 2096732) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLDSA_POINTWISE_ACC_L5_EXEC = ARM_MK_EXEC_RULE mldsa_pointwise_acc_l5_mc;;

(* ========================================================================= *)
(* Correctness proof                                                         *)
(* ========================================================================= *)

let MLDSA_POINTWISE_ACC_L5_CORRECT = prove
 (`!r a b x y pc.
    nonoverlapping (word pc, LENGTH mldsa_pointwise_acc_l5_mc) (r, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_pointwise_acc_l5_mc) (a, 5120) /\
    nonoverlapping (word pc, LENGTH mldsa_pointwise_acc_l5_mc) (b, 5120) /\
    nonoverlapping (r, 1024) (a, 5120) /\
    nonoverlapping (r, 1024) (b, 5120) /\
    nonoverlapping (a, 5120) (b, 5120)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mldsa_pointwise_acc_l5_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [r; a; b] s /\
               (!i. i < 1280 ==> abs(ival(x i)) <= &8380416) /\
               (!i. i < 1280 ==> abs(ival(y i)) <= &75423752) /\
               (!i. i < 1280 ==>
                 read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 1280 ==>
                 read(memory :> bytes32(word_add b (word(4 * i)))) s = y i))
          (\s. read PC s = word(pc + 0x1C4) /\
               (!i. i < 256 ==>
                 let zi = read(memory :> bytes32(word_add r (word(4 * i)))) s in
                 (ival zi == mldsa_pointwise_acc_l5 (ival o x) (ival o y) i)
                   (mod &8380417) /\
                 abs(ival zi) <= &8380416))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(r, 1024)])`,

  (* Setup *)
  MAP_EVERY X_GEN_TAC
    [`r:int64`; `a:int64`; `b:int64`;
     `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL;
              fst MLDSA_POINTWISE_ACC_L5_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  (* Lift x bound to match y bound for product lemma *)
  SUBGOAL_THEN
    `!i. i < 1280 ==> abs(ival((x:num->int32) i)) <= &75423752`
    ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&8380416:int` THEN
   CONJ_TAC THENL [ASM_MESON_TAC[]; CONV_TAC INT_REDUCE_CONV];
   ALL_TAC] THEN

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS; MODIFIABLE_SIMD_REGS] THEN

  (* Initialize and merge memory *)
  ENSURES_INIT_TAC "s0" THEN

  (* Merge a: 5120 bytes = 320 x 128-bit blocks *)
  MEMORY_128_FROM_32_TAC "a" 0 320 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
  STRIP_TAC THEN

  (* Merge b: 5120 bytes = 320 x 128-bit blocks *)
  MEMORY_128_FROM_32_TAC "b" 0 320 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
  STRIP_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN

  (* Simulate all 1703 instructions with SIMD simplification *)
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLDSA_POINTWISE_ACC_L5_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[arm_mldsa_pointwise_montred'])
        (1--1703) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Discard unused input memory (a, b) bytes128 reads *)
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o
    check (fun th ->
      let t = concl th in
      is_eq t &&
      let lhs = fst(dest_eq t) in
      can (find_term (fun t -> is_const t && fst(dest_const t) = "memory")) lhs &&
      (can (find_term (fun t -> t = `a:int64`)) lhs ||
       can (find_term (fun t -> t = `b:int64`)) lhs)))) THEN

  (* Split remaining bytes128 -> bytes32 for output memory *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE (SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (* Expand output cases, substitute, simplify subwords *)
  CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN

  (* Rewrite ARM montred to standard montred for CONGBOUND *)
  REWRITE_TAC[ARM_MLDSA_MONTRED_EQ] THEN

  (* Product bounds (tight: 8380416 * 75423752 = 632082418040832) *)
  SUBGOAL_THEN
   `!i. i < 1280 ==>
     abs(ival(word_mul (word_sx ((x:num->int32) i):int64)
                       (word_sx ((y:num->int32) i):int64))) <= &632082418040832`
   ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`(x:num->int32) i`; `(y:num->int32) i`] IVAL_WORD_MUL_SX32_64) THEN
   ANTS_TAC THENL
    [ASM_MESON_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
   REWRITE_TAC[INT_ABS_MUL] THEN
   MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&8380416 * &75423752:int` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC INT_LE_MUL2 THEN REWRITE_TAC[INT_ABS_POS] THEN ASM_MESON_TAC[];
     CONV_TAC INT_REDUCE_CONV];
   ALL_TAC] THEN

  (* Prove postcondition - congruence + bounds for each coefficient *)
  W(fun (asl,w) ->
    let lfn = PROCESS_BOUND_ASSUMPTIONS
      (CONJUNCTS(tryfind (CONV_RULE EXPAND_CASES_CONV o snd) asl))
    in
    let prove_group =
      W(fun (asl,w) ->
        let mr = rand(lhand(rator(lhand w))) in
        MP_TAC(ASM_CONGBOUND_RULE lfn mr) THEN
        MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
         [(* Congruence branch *)
          REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 8380417 4294967296`] THEN
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
          REWRITE_TAC[GSYM INT_REM_EQ; o_THM; mldsa_pointwise_acc_l5;
                       INVERSE_MOD_CONV `inverse_mod 8380417 4294967296`] THEN
          CONV_TAC INT_REM_DOWN_CONV THEN
          CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
          REPEAT(W(fun (_,w) ->
            let prod = find_term
              (can (term_match []
                `ival(word_mul (word_sx (x:int32):int64) (word_sx (y:int32)))`)) w in
            let wm = rand prod in
            let xi = rand(rand(rator wm)) in
            let yi = rand(rand wm) in
            SUBGOAL_THEN (mk_eq(prod,
              mk_binop `( * ):int->int->int`
                (mk_comb(`ival:int32->int`, xi))
                (mk_comb(`ival:int32->int`, yi)))) SUBST1_TAC THENL
             [MATCH_MP_TAC IVAL_WORD_MUL_SX32_64 THEN
              CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC])) THEN
          CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC;
          (* Bounds branch *)
          REWRITE_TAC[INT_ABS_BOUNDS] THEN
          MATCH_MP_TAC(INT_ARITH
           `l':int <= l /\ u <= u'
            ==> l <= x /\ x <= u ==> l' <= x /\ x <= u'`) THEN
          CONV_TAC INT_REDUCE_CONV])
    in
    REPEAT(W(fun (_,w) ->
      if length(conjuncts w) > 2 then CONJ_TAC else NO_TAC)) THEN
    prove_group));;

(* ========================================================================= *)
(* Subroutine form                                                           *)
(* ========================================================================= *)

let MLDSA_POINTWISE_ACC_L5_SUBROUTINE_CORRECT = prove
 (`!r a b x y pc returnaddress.
    nonoverlapping (word pc, LENGTH mldsa_pointwise_acc_l5_mc) (r, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_pointwise_acc_l5_mc) (a, 5120) /\
    nonoverlapping (word pc, LENGTH mldsa_pointwise_acc_l5_mc) (b, 5120) /\
    nonoverlapping (r, 1024) (a, 5120) /\
    nonoverlapping (r, 1024) (b, 5120) /\
    nonoverlapping (a, 5120) (b, 5120)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mldsa_pointwise_acc_l5_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [r; a; b] s /\
               (!i. i < 1280 ==> abs(ival(x i)) <= &8380416) /\
               (!i. i < 1280 ==> abs(ival(y i)) <= &75423752) /\
               (!i. i < 1280 ==>
                 read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 1280 ==>
                 read(memory :> bytes32(word_add b (word(4 * i)))) s = y i))
          (\s. read PC s = returnaddress /\
               (!i. i < 256 ==>
                 let zi = read(memory :> bytes32(word_add r (word(4 * i)))) s in
                 (ival zi == mldsa_pointwise_acc_l5 (ival o x) (ival o y) i)
                   (mod &8380417) /\
                 abs(ival zi) <= &8380416))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(r, 1024)])`,
  REWRITE_TAC[fst MLDSA_POINTWISE_ACC_L5_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLDSA_POINTWISE_ACC_L5_EXEC
    (REWRITE_RULE[fst MLDSA_POINTWISE_ACC_L5_EXEC]
       MLDSA_POINTWISE_ACC_L5_CORRECT));;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mldsa_pointwise_acc_l5" subroutine_signatures)
    MLDSA_POINTWISE_ACC_L5_SUBROUTINE_CORRECT
    MLDSA_POINTWISE_ACC_L5_EXEC;;

let MLDSA_POINTWISE_ACC_L5_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a b pc returnaddress.
           nonoverlapping (word pc,LENGTH mldsa_pointwise_acc_l5_mc) (r,1024) /\
           nonoverlapping (word pc,LENGTH mldsa_pointwise_acc_l5_mc) (a,5120) /\
           nonoverlapping (word pc,LENGTH mldsa_pointwise_acc_l5_mc) (b,5120) /\
           nonoverlapping (r,1024) (a,5120) /\
           nonoverlapping (r,1024) (b,5120) /\
           nonoverlapping (a,5120) (b,5120)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mldsa_pointwise_acc_l5_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a; b] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a b r pc returnaddress /\
                         memaccess_inbounds e2 [a,5120; b,5120; r,1024]
                         [r,1024]))
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLDSA_POINTWISE_ACC_L5_EXEC);;

