(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of polynomial coefficients to Montgomery form.                 *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_tomont.o";;
 ****)

let mlkem_tomont_mc = define_assert_from_elf
  "mlkem_tomont_mc" "arm/mlkem/mlkem_tomont.o"
[
  0x5281a022;       (* arm_MOV W2 (rvalue (word 3329)) *)
  0x4e020c44;       (* arm_DUP_GEN Q4 X2 16 128 *)
  0x5289d7e2;       (* arm_MOV W2 (rvalue (word 20159)) *)
  0x4e020c45;       (* arm_DUP_GEN Q5 X2 16 128 *)
  0x12808262;       (* arm_MOVN W2 (word 1043) 0 *)
  0x4e020c42;       (* arm_DUP_GEN Q2 X2 16 128 *)
  0x12850462;       (* arm_MOVN W2 (word 10275) 0 *)
  0x4e020c43;       (* arm_DUP_GEN Q3 X2 16 128 *)
  0xd2800101;       (* arm_MOV X1 (rvalue (word 8)) *)
  0x3dc00c1a;       (* arm_LDR Q26 X0 (Immediate_Offset (word 48)) *)
  0x3dc00417;       (* arm_LDR Q23 X0 (Immediate_Offset (word 16)) *)
  0x4e629f51;       (* arm_MUL_VEC Q17 Q26 Q2 16 128 *)
  0x6e63b747;       (* arm_SQRDMULH_VEC Q7 Q26 Q3 16 128 *)
  0x3dc0081b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 32)) *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0x6f4440f1;       (* arm_MLS_VEC Q17 Q7 (Q4 :> LANE_H 0) 16 128 *)
  0x6e63b6e5;       (* arm_SQRDMULH_VEC Q5 Q23 Q3 16 128 *)
  0x3cc40407;       (* arm_LDR Q7 X0 (Postimmediate_Offset (word 64)) *)
  0x3c9f0011;       (* arm_STR Q17 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x6e63b77d;       (* arm_SQRDMULH_VEC Q29 Q27 Q3 16 128 *)
  0x6e63b4f3;       (* arm_SQRDMULH_VEC Q19 Q7 Q3 16 128 *)
  0x4e629ef9;       (* arm_MUL_VEC Q25 Q23 Q2 16 128 *)
  0x4e629ce0;       (* arm_MUL_VEC Q0 Q7 Q2 16 128 *)
  0x4e629f7a;       (* arm_MUL_VEC Q26 Q27 Q2 16 128 *)
  0x3dc00c07;       (* arm_LDR Q7 X0 (Immediate_Offset (word 48)) *)
  0x6f4440b9;       (* arm_MLS_VEC Q25 Q5 (Q4 :> LANE_H 0) 16 128 *)
  0x3dc00417;       (* arm_LDR Q23 X0 (Immediate_Offset (word 16)) *)
  0x6f4443ba;       (* arm_MLS_VEC Q26 Q29 (Q4 :> LANE_H 0) 16 128 *)
  0x6f444260;       (* arm_MLS_VEC Q0 Q19 (Q4 :> LANE_H 0) 16 128 *)
  0x3c9d0019;       (* arm_STR Q25 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e629cf1;       (* arm_MUL_VEC Q17 Q7 Q2 16 128 *)
  0x6e63b4e7;       (* arm_SQRDMULH_VEC Q7 Q7 Q3 16 128 *)
  0x3c9c0000;       (* arm_STR Q0 X0 (Immediate_Offset (word 18446744073709551552)) *)
  0x3dc0081b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 32)) *)
  0x3c9e001a;       (* arm_STR Q26 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xb5fffd61;       (* arm_CBNZ X1 (word 2097068) *)
  0x6f4440f1;       (* arm_MLS_VEC Q17 Q7 (Q4 :> LANE_H 0) 16 128 *)
  0x6e63b6e7;       (* arm_SQRDMULH_VEC Q7 Q23 Q3 16 128 *)
  0x4e629efa;       (* arm_MUL_VEC Q26 Q23 Q2 16 128 *)
  0x6e63b779;       (* arm_SQRDMULH_VEC Q25 Q27 Q3 16 128 *)
  0x3cc40417;       (* arm_LDR Q23 X0 (Postimmediate_Offset (word 64)) *)
  0x4e629f7b;       (* arm_MUL_VEC Q27 Q27 Q2 16 128 *)
  0x6f4440fa;       (* arm_MLS_VEC Q26 Q7 (Q4 :> LANE_H 0) 16 128 *)
  0x6e63b6e7;       (* arm_SQRDMULH_VEC Q7 Q23 Q3 16 128 *)
  0x4e629ef7;       (* arm_MUL_VEC Q23 Q23 Q2 16 128 *)
  0x3c9f0011;       (* arm_STR Q17 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x6f44433b;       (* arm_MLS_VEC Q27 Q25 (Q4 :> LANE_H 0) 16 128 *)
  0x3c9d001a;       (* arm_STR Q26 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x6f4440f7;       (* arm_MLS_VEC Q23 Q7 (Q4 :> LANE_H 0) 16 128 *)
  0x3c9e001b;       (* arm_STR Q27 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9c0017;       (* arm_STR Q23 X0 (Immediate_Offset (word 18446744073709551552)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_TOMONT_EXEC = ARM_MK_EXEC_RULE mlkem_tomont_mc;;

(* ------------------------------------------------------------------------- *)
(* The proof, taken directly with only minor style and formatting changes    *)
(* from mlkem-native (see proofs/hol_light/arm/proofs/mlkem_tomont.ml). *)
(* ------------------------------------------------------------------------- *)

let MLKEM_TOMONT_CORRECT = prove
 (`!ptr x pc.
      nonoverlapping (word pc,LENGTH mlkem_tomont_mc) (ptr,512)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_tomont_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [ptr] s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add ptr (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0xd0) /\
                !i. i < 256
                    ==> let z_i = read(memory :> bytes16
                                     (word_add ptr (word (2 * i)))) s in
                        (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                        abs(ival z_i) <= &3328)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(ptr,512)])`,
  REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    NONOVERLAPPING_CLAUSES; C_ARGUMENTS; fst MLKEM_TOMONT_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (* Split quantified assumptions into separate cases *)
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
    (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  (* Initialize symbolic execution *)
  ENSURES_INIT_TAC "s0" THEN

  (* Rewrite memory-read assumptions from 16-bit granularity
   * to 128-bit granularity. *)
  MEMORY_128_FROM_16_TAC "ptr" 32 THEN
  ASM_REWRITE_TAC [WORD_ADD_0] THEN
  (* Forget original shape of assumption *)
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 ptr) s = x`] THEN

  (* Symbolic execution
     Note that we simplify eagerly after every step.
     This reduces the proof time *)
  STRIP_TAC THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_TOMONT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[barmul])
            (1--184) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  ASM_REWRITE_TAC [] THEN

  (* Reverse restructuring *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE (SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (* Split quantified post-condition into separate cases *)
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC [WORD_ADD_0] THEN

  (* Forget all assumptions *)
  POP_ASSUM_LIST (K ALL_TAC) THEN

  (* We have two goals per index: A congruence goal and a bounds goal.
     Split by index, but keep congruence & bounds goal together. *)
  REPEAT (W(fun (asl, w) ->
    if length(conjuncts w) > 3 then CONJ_TAC else NO_TAC)) THEN

  (* At this point, we have, for every polynomial coefficient, a subgoal
     with 2 conjuncts, one regarding functional correctness of the coefficient,
     another regarding its absolute value. *)

  (* Instantiate general congruence and bounds rule for Barrett multiplication
   * so it matches the current goal, and add as new assumption. *)
  W (MP_TAC o CONGBOUND_RULE o rand o rand o rator o rator o lhand o snd) THEN
  ASM_REWRITE_TAC [o_THM; tomont_3329] THEN
  (* The CONGBOUND_RULE also gives us a conjunct for value & bound,
     matching the shape of the subgoals.
     The following splits `A /\ B ==> C /\ D` in `A ==> C` and `B ==> D` *)
  MATCH_MP_TAC MONO_AND THEN (CONJ_TAC THENL
  [
      (* Correctness *)
      REWRITE_TAC [GSYM INT_REM_EQ] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC[INT_REM_EQ] THEN
      REWRITE_TAC [REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC
    ;
      (* Bound *)
      REWRITE_TAC [INT_ABS_BOUNDS] THEN
      (* The bound we obtain from the generic theorem about Barrett
       * multiplication is stronger than what we need -- weaken it. *)
      MATCH_MP_TAC(INT_ARITH
        `l':int <= l /\ u <= u'
         ==> l <= t /\ t <= u ==> l' <= t /\ t <= u'`) THEN
      CONV_TAC INT_REDUCE_CONV
  ])
);;

let MLKEM_TOMONT_SUBROUTINE_CORRECT = prove
 (`!ptr x pc returnaddress.
    nonoverlapping (word pc, LENGTH mlkem_tomont_mc) (ptr, 512)
    ==>
    ensures arm
      (\s. // Assert that poly_tomont is loaded at PC
           aligned_bytes_loaded s (word pc) mlkem_tomont_mc /\
           read PC s = word pc  /\
           // Remember LR as point-to-stop
           read X30 s = returnaddress /\
           // poly_tomont takes one argument, the base pointer
           C_ARGUMENTS [ptr] s  /\
           // Give name to 16-bit coefficients stored at ptr to be
           // able to refer to them in the post-condition
           (!i. i < 256
                ==> read(memory :> bytes16(word_add ptr (word (2 * i)))) s =
                    x i)
          )
      (\s. // We have reached the LR
           read PC s = returnaddress /\
           // Coefficients have changed according to tomont_3329 and
           // are < MLKEM_Q in absolute value.
           (!i. i < 256
                ==> let z_i = read(memory :> bytes16
                                       (word_add ptr (word (2 * i)))) s in
                    (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
          )
      // Register and memory footprint
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(ptr, 512)])`,
  let TWEAK_CONV = REWRITE_CONV[fst MLKEM_TOMONT_EXEC] in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_TOMONT_EXEC
   (CONV_RULE TWEAK_CONV MLKEM_TOMONT_CORRECT));;
