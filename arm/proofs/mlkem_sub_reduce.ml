(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Subtraction of polynomials, reducing the coefficients to nonnegative      *)
(* remainders.                                                               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_sub_reduce.o";;
 ****)

let mlkem_sub_reduce_mc = define_assert_from_elf
  "mlkem_sub_reduce_mc" "arm/mlkem/mlkem_sub_reduce.o"
[
  0xd503245f;       (* arm_BTI *)
  0x5281a022;       (* arm_MOV W2 (rvalue (word 3329)) *)
  0x4e020c5e;       (* arm_DUP_GEN Q30 X2 16 128 *)
  0x5289d7e2;       (* arm_MOV W2 (rvalue (word 20159)) *)
  0x4e020c5f;       (* arm_DUP_GEN Q31 X2 16 128 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0xad400400;       (* arm_LDP Q0 Q1 X0 (Immediate_Offset (iword (&0))) *)
  0xad410c02;       (* arm_LDP Q2 Q3 X0 (Immediate_Offset (iword (&32))) *)
  0xacc11424;       (* arm_LDP Q4 Q5 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc11c26;       (* arm_LDP Q6 Q7 X1 (Postimmediate_Offset (iword (&32))) *)
  0x6e648400;       (* arm_SUB_VEC Q0 Q0 Q4 16 128 *)
  0x6e658421;       (* arm_SUB_VEC Q1 Q1 Q5 16 128 *)
  0x6e668442;       (* arm_SUB_VEC Q2 Q2 Q6 16 128 *)
  0x6e678463;       (* arm_SUB_VEC Q3 Q3 Q7 16 128 *)
  0x4e7fb410;       (* arm_SQDMULH_VEC Q16 Q0 Q31 16 128 *)
  0x4e7fb431;       (* arm_SQDMULH_VEC Q17 Q1 Q31 16 128 *)
  0x4e7fb452;       (* arm_SQDMULH_VEC Q18 Q2 Q31 16 128 *)
  0x4e7fb473;       (* arm_SQDMULH_VEC Q19 Q3 Q31 16 128 *)
  0x4f152610;       (* arm_SRSHR_VEC Q16 Q16 11 16 128 *)
  0x4f152631;       (* arm_SRSHR_VEC Q17 Q17 11 16 128 *)
  0x4f152652;       (* arm_SRSHR_VEC Q18 Q18 11 16 128 *)
  0x4f152673;       (* arm_SRSHR_VEC Q19 Q19 11 16 128 *)
  0x6e7e9600;       (* arm_MLS_VEC Q0 Q16 Q30 16 128 *)
  0x6e7e9621;       (* arm_MLS_VEC Q1 Q17 Q30 16 128 *)
  0x6e7e9642;       (* arm_MLS_VEC Q2 Q18 Q30 16 128 *)
  0x6e7e9663;       (* arm_MLS_VEC Q3 Q19 Q30 16 128 *)
  0x4f110410;       (* arm_SSHR_VEC Q16 Q0 15 16 128 *)
  0x4f110431;       (* arm_SSHR_VEC Q17 Q1 15 16 128 *)
  0x4f110452;       (* arm_SSHR_VEC Q18 Q2 15 16 128 *)
  0x4f110473;       (* arm_SSHR_VEC Q19 Q3 15 16 128 *)
  0x4e3e1e10;       (* arm_AND_VEC Q16 Q16 Q30 128 *)
  0x4e3e1e31;       (* arm_AND_VEC Q17 Q17 Q30 128 *)
  0x4e3e1e52;       (* arm_AND_VEC Q18 Q18 Q30 128 *)
  0x4e3e1e73;       (* arm_AND_VEC Q19 Q19 Q30 128 *)
  0x4e708400;       (* arm_ADD_VEC Q0 Q0 Q16 16 128 *)
  0x4e718421;       (* arm_ADD_VEC Q1 Q1 Q17 16 128 *)
  0x4e728442;       (* arm_ADD_VEC Q2 Q2 Q18 16 128 *)
  0x4e738463;       (* arm_ADD_VEC Q3 Q3 Q19 16 128 *)
  0xac810400;       (* arm_STP Q0 Q1 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac810c02;       (* arm_STP Q2 Q3 X0 (Postimmediate_Offset (iword (&32))) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffba1;       (* arm_BNE (word 2097012) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_sub_reduce_tmc =
  define_trimmed "mlkem_sub_reduce_tmc" mlkem_sub_reduce_mc;;

let MLKEM_SUB_REDUCE_EXEC = ARM_MK_EXEC_RULE mlkem_sub_reduce_tmc;;

(* ------------------------------------------------------------------------- *)
(* The reduction of each difference is that of mlkem_reduce.                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_SUB_REDUCE_LEMMA = prove
 (`!x:int16.
        ival(word_add (barred x)
                      (word_and (word 3329) (word_ishr (barred x) 15))) =
        ival x rem &3329`,
  GEN_TAC THEN
  MP_TAC(CONGBOUND_RULE `barred x`) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP
   (prove
     (`(y == x) (mod &3329) /\ --(&1664) <= y /\ y <= &1664
       ==> x rem &3329 = if y < &0 then y + &3329 else y`,
      REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_UNIQUE] THEN
      CONV_TAC INT_REDUCE_CONV THEN
      CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THEN
      UNDISCH_TAC `(y:int == x) (mod &3329)` THEN
      SPEC_TAC(`&3329:int`,`p:int`) THEN CONV_TAC INTEGER_RULE)) th]) THEN
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_SUB_REDUCE_CORRECT = prove
 (`!r a x y pc.
        ALL (nonoverlapping (word pc,0xa8)) [(r,512); (a,512)] /\
        nonoverlapping (r,512) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_sub_reduce_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s =
                           x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s =
                           y i))
             (\s. read PC s = word(pc + 0xa4) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s) =
                          ival(word_sub (x i) (y i)) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `y:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Manually expand the cases in the hypotheses ***)

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  ENSURES_INIT_TAC "s0" THEN

  (*** Restructure to match the 128-bit loads ***)

  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
            (subst[mk_small_numeral(16*n),`n:num`]
                  `read (memory :> bytes128(word_add r (word n))) s0`))
            (0--31))) THEN
  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
            (subst[mk_small_numeral(16*n),`n:num`]
                  `read (memory :> bytes128(word_add a (word n))) s0`))
            (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  REPEAT STRIP_TAC THEN

  (*** Simulate the whole thing, unrolling the loop ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_SUB_REDUCE_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[barred])
            (1--293) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Split the 128-bit results into 16-bit coefficients ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s293" THEN
  REWRITE_TAC[MLKEM_SUB_REDUCE_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a x y pc returnaddress.
        ALL (nonoverlapping (word pc,0xa8)) [(r,512); (a,512)] /\
        nonoverlapping (r,512) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_sub_reduce_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s =
                           x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s =
                           y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s) =
                          ival(word_sub (x i) (y i)) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_SUB_REDUCE_EXEC MLKEM_SUB_REDUCE_CORRECT);;

let MLKEM_SUB_REDUCE_SUBROUTINE_CORRECT = prove
 (`!r a x y pc returnaddress.
        ALL (nonoverlapping (word pc,0xac)) [(r,512); (a,512)] /\
        nonoverlapping (r,512) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_sub_reduce_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s =
                           x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s =
                           y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add r (word(2 * i)))) s) =
                          ival(word_sub (x i) (y i)) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE mlkem_sub_reduce_mc mlkem_sub_reduce_tmc
    MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_sub_reduce" subroutine_signatures)
    MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_CORRECT
    MLKEM_SUB_REDUCE_EXEC;;

let MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (word pc,0xa8)) [(r,512); (a,512)] /\
           nonoverlapping (r,512) (a,512)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_sub_reduce_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [r,512; a,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_SUB_REDUCE_EXEC);;

let MLKEM_SUB_REDUCE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (word pc,0xac)) [(r,512); (a,512)] /\
           nonoverlapping (r,512) (a,512)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_sub_reduce_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [r,512; a,512] [r,512])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE mlkem_sub_reduce_mc mlkem_sub_reduce_tmc
    MLKEM_SUB_REDUCE_NOIBT_SUBROUTINE_SAFE));;
