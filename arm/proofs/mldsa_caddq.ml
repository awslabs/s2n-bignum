(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness of mldsa_caddq:                                    *)
(* Modular reduction of polynomial coefficients from (-q, q) to [0, q)       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "arm/mldsa/mldsa_caddq.o";;
 ****)

let mldsa_caddq_mc = define_assert_from_elf "mldsa_caddq_mc" "arm/mldsa/mldsa_caddq.o"
[
  0x529c0029;       (* arm_MOV W9 (rvalue (word 57345)) *)
  0x72a00fe9;       (* arm_MOVK W9 (word 127) 16 *)
  0x4e040d24;       (* arm_DUP_GEN Q4 X9 32 128 *)
  0xd2800201;       (* arm_MOV X1 (rvalue (word 16)) *)
  0x3dc00000;       (* arm_LDR Q0 X0 (Immediate_Offset (word 0)) *)
  0x3dc00401;       (* arm_LDR Q1 X0 (Immediate_Offset (word 16)) *)
  0x3dc00802;       (* arm_LDR Q2 X0 (Immediate_Offset (word 32)) *)
  0x3dc00c03;       (* arm_LDR Q3 X0 (Immediate_Offset (word 48)) *)
  0x6f210405;       (* arm_USHR_VEC Q5 Q0 31 32 128 *)
  0x4ea494a0;       (* arm_MLA_VEC Q0 Q5 Q4 32 128 *)
  0x6f210425;       (* arm_USHR_VEC Q5 Q1 31 32 128 *)
  0x4ea494a1;       (* arm_MLA_VEC Q1 Q5 Q4 32 128 *)
  0x6f210445;       (* arm_USHR_VEC Q5 Q2 31 32 128 *)
  0x4ea494a2;       (* arm_MLA_VEC Q2 Q5 Q4 32 128 *)
  0x6f210465;       (* arm_USHR_VEC Q5 Q3 31 32 128 *)
  0x4ea494a3;       (* arm_MLA_VEC Q3 Q5 Q4 32 128 *)
  0x3d800401;       (* arm_STR Q1 X0 (Immediate_Offset (word 16)) *)
  0x3d800802;       (* arm_STR Q2 X0 (Immediate_Offset (word 32)) *)
  0x3d800c03;       (* arm_STR Q3 X0 (Immediate_Offset (word 48)) *)
  0x3c840400;       (* arm_STR Q0 X0 (Postimmediate_Offset (word 64)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffde1;       (* arm_BNE (word 2097084) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLDSA_CADDQ_EXEC = ARM_MK_EXEC_RULE mldsa_caddq_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLDSA_CADDQ_MC =
  REWRITE_CONV[mldsa_caddq_mc] `LENGTH mldsa_caddq_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLDSA_CADDQ_PREAMBLE_LENGTH = new_definition
  `MLDSA_CADDQ_PREAMBLE_LENGTH = 0`;;

let MLDSA_CADDQ_POSTAMBLE_LENGTH = new_definition
  `MLDSA_CADDQ_POSTAMBLE_LENGTH = 4`;;

let MLDSA_CADDQ_CORE_START = new_definition
  `MLDSA_CADDQ_CORE_START = MLDSA_CADDQ_PREAMBLE_LENGTH`;;

let MLDSA_CADDQ_CORE_END = new_definition
  `MLDSA_CADDQ_CORE_END = LENGTH mldsa_caddq_mc - MLDSA_CADDQ_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLDSA_CADDQ_MC;
              MLDSA_CADDQ_CORE_START; MLDSA_CADDQ_CORE_END;
              MLDSA_CADDQ_PREAMBLE_LENGTH; MLDSA_CADDQ_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Functional specification of mldsa_caddq                                   *)
(*                                                                           *)
(* The AArch64 code computes, per coefficient, x + (x >>_u 31) * Q, i.e. it  *)
(* adds Q exactly when the sign bit is set (x < 0).                          *)
(* ------------------------------------------------------------------------- *)

let mldsa_caddq = define
   `mldsa_caddq (x:int32) = word_add x (word_mul (word_ushr x 31) (word 8380417))`;;

let mldsa_caddq_direct = prove
   (`!x:int32.
      ival(mldsa_caddq x) = if ival x < &0 then ival x + &8380417 else ival x`,
    REWRITE_TAC[mldsa_caddq] THEN BITBLAST_TAC);;

let mldsa_caddq_rem = prove
   (`!x:int32. abs(ival x) < &8380417
      ==> ival(mldsa_caddq x) = ival x rem &8380417`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[mldsa_caddq_direct] THEN
    COND_CASES_TAC THENL [
      ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
      REWRITE_TAC[INT_REM_UNIQUE] THEN
      CONV_TAC INT_REDUCE_CONV THEN
      CONJ_TAC THENL [ASM_INT_ARITH_TAC; CONV_TAC INTEGER_RULE];
      MATCH_MP_TAC(GSYM INT_REM_LT) THEN
      ASM_INT_ARITH_TAC
    ]);;

let mldsa_caddq_bound = prove
 (`!x:int32. abs(ival x) < &8380417
    ==> &0 <= ival(mldsa_caddq x) /\ ival(mldsa_caddq x) < &8380417`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:int32` mldsa_caddq_rem) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`ival(x:int32)`; `&8380417:int`] INT_REM_POS) THEN
    INT_ARITH_TAC;
    MP_TAC(SPECL [`ival(x:int32)`; `&8380417:int`] INT_LT_REM) THEN
    INT_ARITH_TAC]);;

let mldsa_caddq_lower = prove
 (`!x:int32. abs(ival x) < &8380417
    ==> &0 <= ival(mldsa_caddq x)`,
  MESON_TAC[mldsa_caddq_bound]);;

let mldsa_caddq_upper = prove
 (`!x:int32. abs(ival x) < &8380417
    ==> ival(mldsa_caddq x) < &8380417`,
  MESON_TAC[mldsa_caddq_bound]);;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_CADDQ_CORRECT = prove
 (`!a x pc.
        nonoverlapping (word pc,LENGTH mldsa_caddq_mc) (a,1024)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_caddq_mc /\
                  read PC s = word (pc + MLDSA_CADDQ_CORE_START) /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256 ==>
                     read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &8380417))
             (\s. read PC s = word(pc + MLDSA_CADDQ_CORE_END) /\
                  (!i. i < 256 ==>
                     ival(read(memory :> bytes32(word_add a (word(4 * i)))) s) =
                     ival(x i) rem &8380417) /\
                  (!i. i < 256 ==>
                     &0 <= ival(read(memory :> bytes32(word_add a (word(4 * i)))) s) /\
                     ival(read(memory :> bytes32(word_add a (word(4 * i)))) s) < &8380417))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (* Expand the bounded forall in precondition to 256 explicit cases *)
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  ENSURES_INIT_TAC "s0" THEN

  (* Merge bytes32 reads into bytes128 reads (4 x 32-bit = 128-bit) *)
  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 2
            (subst[mk_small_numeral(16*n),`n:num`]
                  `read (memory :> bytes128(word_add a (word n))) s0`))
            (0--63))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  STRIP_TAC THEN

  (* Symbolically execute all instructions until target PC and fold to mldsa_caddq *)
  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLDSA_CADDQ_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC ONCE_REWRITE_CONV [GSYM mldsa_caddq]))) 1 THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Split bytes128 results back into bytes32 *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
   check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (* Simplify nested subword operations in assumptions *)
  RULE_ASSUM_TAC (CONV_RULE (RAND_CONV (TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) THEN

  (* Expand postcondition foralls to 256 cases and rewrite with assumptions *)
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN

  (* Keep only the input bounds assumptions and discharge both postcondition
     conjuncts via the spec lemmas *)
  DISCARD_NONMATCHING_ASSUMPTIONS [`abs (ival t) < &8380417`] THEN
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC mldsa_caddq_rem ORELSE MATCH_MP_TAC mldsa_caddq_lower ORELSE
   MATCH_MP_TAC mldsa_caddq_upper) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness theorem (includes return)                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_CADDQ_SUBROUTINE_CORRECT = prove
 (`!a x pc returnaddress.
        nonoverlapping (word pc,LENGTH mldsa_caddq_mc) (a,1024)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_caddq_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256 ==>
                     read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &8380417))
             (\s. read PC s = returnaddress /\
                  (!i. i < 256 ==>
                     ival(read(memory :> bytes32(word_add a (word(4 * i)))) s) =
                     ival(x i) rem &8380417) /\
                  (!i. i < 256 ==>
                     &0 <= ival(read(memory :> bytes32(word_add a (word(4 * i)))) s) /\
                     ival(read(memory :> bytes32(word_add a (word(4 * i)))) s) < &8380417))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`,
 CONV_TAC LENGTH_SIMPLIFY_CONV THEN
 let TWEAK_CONV =
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0]
     in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLDSA_CADDQ_EXEC
   (CONV_RULE TWEAK_CONV (CONV_RULE LENGTH_SIMPLIFY_CONV MLDSA_CADDQ_CORRECT)));;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mldsa_caddq" subroutine_signatures)
    MLDSA_CADDQ_SUBROUTINE_CORRECT
    MLDSA_CADDQ_EXEC;;

let MLDSA_CADDQ_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a pc returnaddress.
           nonoverlapping (word pc,LENGTH mldsa_caddq_mc) (a,1024)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mldsa_caddq_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc returnaddress /\
                         memaccess_inbounds e2 [a,1024]
                         [a,1024]))
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLDSA_CADDQ_EXEC);;
