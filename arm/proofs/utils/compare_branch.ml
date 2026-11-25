(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The conditions of an unsigned comparison with an immediate, as the step   *)
(* tactics leave them, as comparisons of the value.                          *)
(*                                                                           *)
(* After cmp x, #k (subs xzr, x, #k), the condition "hi" of b.hi, b.ls,     *)
(* csel, ... (C set and Z clear) is, for a 64-bit register,                  *)
(*                                                                           *)
(*   k <= val x /\ ~(val(word_sub x (word k)) = 0)                           *)
(*                                                                           *)
(* and for a 32-bit register (whose carry the model states in integers)      *)
(*                                                                           *)
(*   &(val x) - &k = &(val(word_sub x (word k))) /\                          *)
(*   ~(val(word_sub x (word k)) = 0)                                         *)
(*                                                                           *)
(* WORD_CMP_HI and WORD_CMP_HI_INT say that both are k < val x. A branch on  *)
(* such a condition is decided by bstep (common/bstep.ml) from the           *)
(* assumptions, which it uses as rewrites: CMP_HI_TAC x k adds the two       *)
(* equivalences as assumptions, so that a case split on k < val x decides    *)
(* the branch. bstep rewrites the condition with all the assumptions, so if  *)
(* some of them rewrite parts of it (such as word_zx (word n) = word n or    *)
(* val x = n), CMP_HI_TAC ~rws:[those] x k states the equivalences in the   *)
(* form that they lead to, and the case split is on the rewritten k < val x. *)
(* ========================================================================= *)

let WORD_CMP_HI = prove
 (`!(x:N word) k.
        k < 2 EXP dimindex(:N)
        ==> ((k <= val x /\ ~(val(word_sub x (word k)) = 0)) <=> k < val x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[VAL_WORD; MOD_LT] THEN
  ARITH_TAC);;

let WORD_CMP_HI_INT = prove
 (`!(x:N word) k.
        k < 2 EXP dimindex(:N)
        ==> ((&(val x) - &k:int = &(val(word_sub x (word k))) /\
              ~(val(word_sub x (word k)) = 0)) <=> k < val x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
   [INT_VAL_WORD_SUB_CASES] THEN
  ASM_SIMP_TAC[VAL_WORD; MOD_LT; GSYM VAL_EQ; INT_OF_NUM_LE] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INT_ARITH `&x - &k:int = &x + (p - &k) <=> p = &0`;
                  INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  ASM_ARITH_TAC);;

let CMP_HI_TAC ?(rws=[]) (x:term) (k:term) =
  let th = ISPECL [x; k] WORD_CMP_HI and ith = ISPECL [x; k] WORD_CMP_HI_INT in
  let red th =
    let th = CONV_RULE(LAND_CONV(REWRITE_CONV[DIMINDEX_64; DIMINDEX_32;
                                              DIMINDEX_16; DIMINDEX_8] THENC
                                 NUM_REDUCE_CONV)) th in
    let th = MP th TRUTH in
    if rws = [] then th else REWRITE_RULE rws th in
  ASSUME_TAC(red th) THEN ASSUME_TAC(red ith);;
