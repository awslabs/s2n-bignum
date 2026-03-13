(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Use hint to correct high bits of decomposition (ML-DSA, param 44).        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "arm/mldsa/mldsa_poly_use_hint_88.o";;
 ****)

let mldsa_poly_use_hint_88_mc = define_assert_from_elf
 "mldsa_poly_use_hint_88_mc" "arm/mldsa/mldsa_poly_use_hint_88.o"
[
  0x529c0024;       (* arm_MOV W4 (rvalue (word 57345)) *)
  0x72a00fe4;       (* arm_MOVK W4 (word 127) 16 *)
  0x4e040c94;       (* arm_DUP_GEN Q20 X4 32 128 *)
  0x528d8005;       (* arm_MOV W5 (rvalue (word 27648)) *)
  0x72a00fc5;       (* arm_MOVK W5 (word 126) 16 *)
  0x4e040cb5;       (* arm_DUP_GEN Q21 X5 32 128 *)
  0x529d0007;       (* arm_MOV W7 (rvalue (word 59392)) *)
  0x72a00047;       (* arm_MOVK W7 (word 2) 16 *)
  0x4e040cf6;       (* arm_DUP_GEN Q22 X7 32 128 *)
  0x5280b02b;       (* arm_MOV W11 (rvalue (word 1409)) *)
  0x72ab02cb;       (* arm_MOVK W11 (word 22550) 16 *)
  0x4e040d77;       (* arm_DUP_GEN Q23 X11 32 128 *)
  0x4f010578;       (* arm_MOVI Q24 (word 184683593771) *)
  0xd2800203;       (* arm_MOV X3 (rvalue (word 16)) *)
  0x3dc00421;       (* arm_LDR Q1 X1 (Immediate_Offset (word 16)) *)
  0x3dc00822;       (* arm_LDR Q2 X1 (Immediate_Offset (word 32)) *)
  0x3dc00c23;       (* arm_LDR Q3 X1 (Immediate_Offset (word 48)) *)
  0x3cc40420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 64)) *)
  0x3dc00445;       (* arm_LDR Q5 X2 (Immediate_Offset (word 16)) *)
  0x3dc00846;       (* arm_LDR Q6 X2 (Immediate_Offset (word 32)) *)
  0x3dc00c47;       (* arm_LDR Q7 X2 (Immediate_Offset (word 48)) *)
  0x3cc40444;       (* arm_LDR Q4 X2 (Postimmediate_Offset (word 64)) *)
  0x4eb7b431;       (* arm_SQDMULH_VEC Q17 Q1 Q23 32 128 *)
  0x4f2f2631;       (* arm_SRSHR_VEC Q17 Q17 17 32 128 *)
  0x4eb53439;       (* arm_CMGT_VEC Q25 Q1 Q21 32 128 *)
  0x6eb69621;       (* arm_MLS_VEC Q1 Q17 Q22 32 128 *)
  0x4e791e31;       (* arm_BIC_VEC Q17 Q17 Q25 128 *)
  0x4eb98421;       (* arm_ADD_VEC Q1 Q1 Q25 32 128 *)
  0x6ea09821;       (* arm_CMLE_VEC_ZERO Q1 Q1 32 128 *)
  0x4f001421;       (* arm_ORR_VEC Q1 Q1 (rvalue (word 79228162532711081671548469249)) 128 *)
  0x4ea59431;       (* arm_MLA_VEC Q17 Q1 Q5 32 128 *)
  0x4eb83639;       (* arm_CMGT_VEC Q25 Q17 Q24 32 128 *)
  0x4e791e31;       (* arm_BIC_VEC Q17 Q17 Q25 128 *)
  0x6eb86e31;       (* arm_UMIN_VEC Q17 Q17 Q24 32 128 *)
  0x4eb7b452;       (* arm_SQDMULH_VEC Q18 Q2 Q23 32 128 *)
  0x4f2f2652;       (* arm_SRSHR_VEC Q18 Q18 17 32 128 *)
  0x4eb53459;       (* arm_CMGT_VEC Q25 Q2 Q21 32 128 *)
  0x6eb69642;       (* arm_MLS_VEC Q2 Q18 Q22 32 128 *)
  0x4e791e52;       (* arm_BIC_VEC Q18 Q18 Q25 128 *)
  0x4eb98442;       (* arm_ADD_VEC Q2 Q2 Q25 32 128 *)
  0x6ea09842;       (* arm_CMLE_VEC_ZERO Q2 Q2 32 128 *)
  0x4f001422;       (* arm_ORR_VEC Q2 Q2 (rvalue (word 79228162532711081671548469249)) 128 *)
  0x4ea69452;       (* arm_MLA_VEC Q18 Q2 Q6 32 128 *)
  0x4eb83659;       (* arm_CMGT_VEC Q25 Q18 Q24 32 128 *)
  0x4e791e52;       (* arm_BIC_VEC Q18 Q18 Q25 128 *)
  0x6eb86e52;       (* arm_UMIN_VEC Q18 Q18 Q24 32 128 *)
  0x4eb7b473;       (* arm_SQDMULH_VEC Q19 Q3 Q23 32 128 *)
  0x4f2f2673;       (* arm_SRSHR_VEC Q19 Q19 17 32 128 *)
  0x4eb53479;       (* arm_CMGT_VEC Q25 Q3 Q21 32 128 *)
  0x6eb69663;       (* arm_MLS_VEC Q3 Q19 Q22 32 128 *)
  0x4e791e73;       (* arm_BIC_VEC Q19 Q19 Q25 128 *)
  0x4eb98463;       (* arm_ADD_VEC Q3 Q3 Q25 32 128 *)
  0x6ea09863;       (* arm_CMLE_VEC_ZERO Q3 Q3 32 128 *)
  0x4f001423;       (* arm_ORR_VEC Q3 Q3 (rvalue (word 79228162532711081671548469249)) 128 *)
  0x4ea79473;       (* arm_MLA_VEC Q19 Q3 Q7 32 128 *)
  0x4eb83679;       (* arm_CMGT_VEC Q25 Q19 Q24 32 128 *)
  0x4e791e73;       (* arm_BIC_VEC Q19 Q19 Q25 128 *)
  0x6eb86e73;       (* arm_UMIN_VEC Q19 Q19 Q24 32 128 *)
  0x4eb7b410;       (* arm_SQDMULH_VEC Q16 Q0 Q23 32 128 *)
  0x4f2f2610;       (* arm_SRSHR_VEC Q16 Q16 17 32 128 *)
  0x4eb53419;       (* arm_CMGT_VEC Q25 Q0 Q21 32 128 *)
  0x6eb69600;       (* arm_MLS_VEC Q0 Q16 Q22 32 128 *)
  0x4e791e10;       (* arm_BIC_VEC Q16 Q16 Q25 128 *)
  0x4eb98400;       (* arm_ADD_VEC Q0 Q0 Q25 32 128 *)
  0x6ea09800;       (* arm_CMLE_VEC_ZERO Q0 Q0 32 128 *)
  0x4f001420;       (* arm_ORR_VEC Q0 Q0 (rvalue (word 79228162532711081671548469249)) 128 *)
  0x4ea49410;       (* arm_MLA_VEC Q16 Q0 Q4 32 128 *)
  0x4eb83619;       (* arm_CMGT_VEC Q25 Q16 Q24 32 128 *)
  0x4e791e10;       (* arm_BIC_VEC Q16 Q16 Q25 128 *)
  0x6eb86e10;       (* arm_UMIN_VEC Q16 Q16 Q24 32 128 *)
  0x3d800411;       (* arm_STR Q17 X0 (Immediate_Offset (word 16)) *)
  0x3d800812;       (* arm_STR Q18 X0 (Immediate_Offset (word 32)) *)
  0x3d800c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 48)) *)
  0x3c840410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 64)) *)
  0xf1000463;       (* arm_SUBS X3 X3 (rvalue (word 1)) *)
  0x54fff861;       (* arm_BNE (word 2096908) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLDSA_USE_HINT_88_EXEC = ARM_MK_EXEC_RULE mldsa_poly_use_hint_88_mc;;

(* ========================================================================= *)
(* Specification: use_hint for ML-DSA parameter set 44                       *)
(*                                                                           *)
(* Constants:                                                                *)
(*   Q = 8380417                                                             *)
(*   GAMMA2 = (Q-1)/88 = 95232                                               *)
(*   2*GAMMA2 = 190464                                                       *)
(*   Output range: [0, 43]                                                   *)
(*                                                                           *)
(* Algorithm per coefficient (matching C reference mld_use_hint):            *)
(*   1. decompose: compute a1 (high bits) and a0 (remainder)                 *)
(*   2. if hint=0: return a1                                                 *)
(*   3. if a0 > 0: return min(a1 + 1, 43)                                    *)
(*   4. if a0 <= 0: return min(a1 - 1, 43) with clamping via BIC+UMIN        *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Correctness proof                                                         *)
(* ========================================================================= *)

let MLDSA_USE_HINT_88_CORRECT = prove
 (`!b a h x y pc.
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_mc) (b, 1024) /\
    nonoverlapping (b, 1024) (a, 1024) /\
    nonoverlapping (b, 1024) (h, 1024)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mldsa_poly_use_hint_88_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [b; a; h] s /\
               (!i. i < 256 ==> val(x i) < 8380417) /\
               (!i. i < 256 ==> val(y i) <= 1) /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add h (word(4 * i)))) s = y i))
          (\s. read PC s = word(pc + 0x130) /\
               (!i. i < 256 ==>
                 val(read(memory :> bytes32(word_add b (word(4 * i)))) s) <= 43))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(b, 1024)])`,

  (* Setup *)
  MAP_EVERY X_GEN_TAC
    [`b:int64`; `a:int64`; `h:int64`;
     `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL;
              fst MLDSA_USE_HINT_88_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS; MODIFIABLE_SIMD_REGS] THEN

  (* Initialize and merge memory *)
  ENSURES_INIT_TAC "s0" THEN
  USE_HINT_88_MEMORY_128_FROM_32_TAC "a" 0 64 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
  STRIP_TAC THEN
  USE_HINT_88_MEMORY_128_FROM_32_TAC "h" 0 64 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
  STRIP_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN

  (* Simulate 1006 instructions (excluding RET) *)
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLDSA_USE_HINT_88_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[])
        (1--1006) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Split bytes128 -> bytes32 for output memory *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE (SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (* Expand output cases, substitute *)
  CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN

  (* Prove bounds - each output coefficient has val <= 43 *)
  (* The UMIN with 43 at the end guarantees val(word_umin x (word n)) <= n *)
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[VAL_WORD_UMIN; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;


(* ========================================================================= *)
(* Subroutine form                                                           *)
(* ========================================================================= *)

let MLDSA_USE_HINT_88_SUBROUTINE_CORRECT = prove
 (`!b a h x y pc returnaddress.
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_mc) (b, 1024) /\
    nonoverlapping (b, 1024) (a, 1024) /\
    nonoverlapping (b, 1024) (h, 1024)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mldsa_poly_use_hint_88_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [b; a; h] s /\
               (!i. i < 256 ==> val(x i) < 8380417) /\
               (!i. i < 256 ==> val(y i) <= 1) /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add h (word(4 * i)))) s = y i))
          (\s. read PC s = returnaddress /\
               (!i. i < 256 ==>
                 val(read(memory :> bytes32(word_add b (word(4 * i)))) s) <= 43))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(b, 1024)])`,
  REWRITE_TAC[fst MLDSA_USE_HINT_88_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLDSA_USE_HINT_88_EXEC
    (REWRITE_RULE[fst MLDSA_USE_HINT_88_EXEC]
       MLDSA_USE_HINT_88_CORRECT));;


(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mldsa_poly_use_hint_88" subroutine_signatures)
    MLDSA_USE_HINT_88_SUBROUTINE_CORRECT
    MLDSA_USE_HINT_88_EXEC;;

let MLDSA_USE_HINT_88_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e b a h pc returnaddress.
           nonoverlapping (word pc,LENGTH mldsa_poly_use_hint_88_mc) (b,1024) /\
           nonoverlapping (b,1024) (a,1024) /\
           nonoverlapping (b,1024) (h,1024)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mldsa_poly_use_hint_88_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [b; a; h] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a h b pc returnaddress /\
                         memaccess_inbounds e2 [a,1024; h,1024; b,1024]
                         [b,1024]))
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLDSA_USE_HINT_88_EXEC);;
