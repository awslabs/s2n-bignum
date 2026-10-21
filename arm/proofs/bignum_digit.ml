(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time digit selection from bignum.                                *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_digit.o";;
 ****)

let bignum_digit_mc =
  define_assert_from_elf "bignum_digit_mc" "arm/generic/bignum_digit.o"
[
  0xb4000140;       (* arm_CBZ X0 (word 40) *)
  0xaa1f03e3;       (* arm_MOV X3 XZR *)
  0xaa1f03e4;       (* arm_MOV X4 XZR *)
  0xf8647825;       (* arm_LDR X5 X1 (Shiftreg_Offset X4 3) *)
  0xeb02009f;       (* arm_CMP X4 X2 *)
  0x9a8300a3;       (* arm_CSEL X3 X5 X3 Condition_EQ *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54ffff63;       (* arm_BCC (word 2097132) *)
  0xaa0303e0;       (* arm_MOV X0 X3 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_DIGIT_EXEC = ARM_MK_EXEC_RULE bignum_digit_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_DIGIT_CORRECT = prove
 (`!k x n a pc.
        ensures arm
         (\s. aligned_bytes_loaded s (word pc) bignum_digit_mc /\
              read PC s = word pc /\
              C_ARGUMENTS [k;x;n] s /\
              bignum_from_memory (x,val k) s = a)
         (\s. read PC s = word(pc + 0x28) /\
              C_RETURN s = word(bigdigit a (val n)))
         (MAYCHANGE [PC; X0; X3; X4; X5] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `x:int64` THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`a:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  BIGNUM_TERMRANGE_TAC `k:num` `a:num` THEN

  (*** The trivial case k = 0 ***)

  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_THEN `k = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_DIGIT_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[BIGDIGIT_0];
    ALL_TAC] THEN

  (*** Main loop setup ***)

  ENSURES_WHILE_UP_TAC `k:num` `pc + 0xc` `pc + 0x1c`
   `\i s. read X0 s = word k /\
          read X1 s = x /\
          read X2 s = word n /\
          read X3 s = word(bigdigit (lowdigits a i) n) /\
          read X4 s = word i /\
          bignum_from_memory(word_add x (word(8 * i)),k - i) s =
          highdigits a i` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; LOWDIGITS_0; BIGDIGIT_0] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_DIGIT_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[HIGHDIGITS_0];
    ALL_TAC; (*** Main loop invariant ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_DIGIT_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_DIGIT_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  (*** Main loop invariant ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
  ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC BIGNUM_DIGIT_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; VAL_EQ_0; WORD_SUB_EQ_0] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM COND_RAND] THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[GSYM VAL_EQ; BIGDIGIT_LOWDIGITS] THEN
  ASM_CASES_TAC `i:num = n` THEN ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n < i + 1 <=> n < i \/ n = i`]);;

let BIGNUM_DIGIT_SUBROUTINE_CORRECT = prove
 (`!k x n a pc returnaddress.
        ensures arm
         (\s. aligned_bytes_loaded s (word pc) bignum_digit_mc /\
              read PC s = word pc /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [k;x;n] s /\
              bignum_from_memory (x,val k) s = a)
         (\s. read PC s = returnaddress /\
              C_RETURN s = word(bigdigit a (val n)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_DIGIT_EXEC BIGNUM_DIGIT_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_digit" subroutine_signatures)
    BIGNUM_DIGIT_SUBROUTINE_CORRECT
    BIGNUM_DIGIT_EXEC;;

let BIGNUM_DIGIT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e k x n pc returnaddress.
           ensures arm
           (\s.
                aligned_bytes_loaded s (word pc) bignum_digit_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [k; x; n] s /\
                read events s = e)
           (\s.
                read PC s = returnaddress /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events x k pc returnaddress /\
                     memaccess_inbounds e2 [x,val k * 8] []))
           MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`,
  ASSERT_CONCL_TAC full_spec THEN
  ARM_SAFETY_SKELETON_TAC ["k"]
   (Cases(`k = 0`,
     Leg("k0",
       ASM_REWRITE_TAC[] THEN
       ARM_SAFETY_SIM_TAC BIGNUM_DIGIT_EXEC (1--2) THEN DISCHARGE_SAFETY_PROPERTY_TAC),
     Loop(`k:num`, `pc + 0xc`, `pc + 0x24`,
       `\i s. read X0 s = word k /\ read X1 s = x /\ read X2 s = n /\
              read X4 s = word i /\ read X30 s = returnaddress`,
       Leg("pre",
         (* prologue: CBZ not taken; MOV X3; MOV X4 -> loop head *)
         ARM_SAFETY_SIM_TAC BIGNUM_DIGIT_EXEC (1--3) THEN DISCHARGE_SAFETY_PROPERTY_TAC),
       Leg("loop",
         (* main loop body: LDR; CMP; CSEL; ADD; CMP; BCC *)
         VAL_INT64_TAC `i:num` THEN REWRITE_TAC[] THEN
         ARM_SAFETY_SIM_TAC BIGNUM_DIGIT_EXEC (1--6) THEN
         (* the loop counter word i increments to word(i+1) *)
         SUBGOAL_THEN `word_add (word i) (word 1):int64 = word(i+1)` ASSUME_TAC THENL
         [ CONV_TAC WORD_RULE; ALL_TAC ] THEN
         SUBGOAL_THEN `val(word(i+1):int64) = i + 1` ASSUME_TAC THENL
         [ MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
         SIMPLE_ARITH_TAC; ALL_TAC ] THEN
         (* rewrite counter to word(i+1) and the CBCC condition to i+1<k *)
         ASM_REWRITE_TAC[] THEN
         (* the back-branch PC target: closes by cases on i+1<k *)
         CONJ_TAC THENL [ COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC ] THEN
         (* help CONTAINED_TAC bound the load index a[i] within [a, k*8] *)
         SUBGOAL_THEN `i < k` ASSUME_TAC THENL [ SIMPLE_ARITH_TAC; ALL_TAC ] THEN
         DISCHARGE_SAFETY_PROPERTY_TAC),
       Leg("post",
         (* epilogue: MOV X0; RET *)
         REWRITE_TAC[] THEN
         ARM_SAFETY_SIM_TAC BIGNUM_DIGIT_EXEC (1--2) THEN DISCHARGE_SAFETY_PROPERTY_TAC)))));;
