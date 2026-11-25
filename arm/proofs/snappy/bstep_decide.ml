(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Blocks of bstep through branches that the assumptions decide only by      *)
(* arithmetic.                                                               *)
(*                                                                           *)
(* bstep (common/bstep.ml) follows a conditional branch only if the          *)
(* assumptions, used as rewrites, reduce its condition to T or F; otherwise  *)
(* the block stops with "PC not constant: `if C then .. else ..`". The       *)
(* conditions of compiled code are comparisons of pointers and lengths, e.g. *)
(* val (word_add op (word (b - 15))) < val op_limit, which follow from       *)
(* arithmetic facts that are not rewrites. ARM_BSTEP_DECIDE_TAC ~decide      *)
(* execth (m--n) runs ARM_BSTEP_TAC execth (m--n); when it stops at such a   *)
(* branch it proves C or ~C by the tactic decide from the assumptions, adds  *)
(* it as an assumption (so that the rewrite decides the branch) and runs the *)
(* block again, up to 64 times. If decide proves neither, it fails with the  *)
(* condition: the proof must split the cases.                                *)
(*                                                                           *)
(* The condition is the PC value at which the block stopped, which bstep    *)
(* records for the domain (bstep_stopped_pc, common/bstep.ml). The default   *)
(* decide is ARITH_TAC on the arithmetic assumptions (those without a state, *)
(* of type bool, made of numbers) after rewriting with ~rws, which should    *)
(* turn the values of the words in the condition into numbers (e.g.          *)
(* val(word_add op (word k)) = val op + k under no wrap-around).             *)
(* ========================================================================= *)

(* The condition of the branch at which the last block stopped.            *)

let bstep_branch_condition () =
  match !(bstep_stopped_pc ()) with
    Some(Comb(Comb(Comb(Const("COND",_),c),_),_)) -> c
  | _ -> failwith "bstep_branch_condition";;

(* The values of words in a condition as numbers, where the arithmetic      *)
(* facts show that there is no wrap-around: val(word k) = k for k < 2^64,    *)
(* val(word_add x (word k)) = val x + k for val x + k < 2^64 and             *)
(* val(word_sub x (word k)) = val x - k for k <= val x, inside out. The side *)
(* conditions are proved by ARITH_TAC from the facts ths (after the same     *)
(* rewriting).                                                               *)

let VAL_WORD_NOWRAP = prove
 (`!k. k < 2 EXP 64 ==> val(word k:int64) = k`,
  SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]);;

let VAL_WORD_ADD_NOWRAP = prove
 (`!(x:int64) k. val x + k < 2 EXP 64 ==> val(word_add x (word k)) = val x + k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64] THEN
  SUBGOAL_THEN `val(word k:int64) = k` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_NOWRAP THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]]);;

let VAL_WORD_SUB_NOWRAP = prove
 (`!(x:int64) k. k <= val x ==> val(word_sub x (word k)) = val x - k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `x:int64 = word_add (word_sub x (word k)) (word k)`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th]) THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub x (word k):int64) + k < 2 EXP 64` ASSUME_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[VAL_WORD_ADD_NOWRAP] THEN ARITH_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB; DIMINDEX_64] THEN
  SUBGOAL_THEN `val(word k:int64) = k` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_NOWRAP THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(x:int64) + 2 EXP 64 - k = (val x - k) + 1 * 2 EXP 64`
  SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 2 EXP 64 ==> x - k < 2 EXP 64`] THEN
  ASM_ARITH_TAC);;

let VAL_WORD_SUB_EQ_0 = prove
 (`!x y:N word. val(word_sub x y) = 0 <=> val x = val y`,
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; VAL_EQ]);;

let rec VAL_NOWRAP_CONV (ths:thm list) tm =
  let side t =
    let t' = rhs(concl(TOP_DEPTH_CONV (VAL_NOWRAP_CONV ths) t)) in
    let th = TAC_PROOF(([],t'),
      MAP_EVERY MP_TAC ths THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) in
    EQ_MP (SYM(TOP_DEPTH_CONV (VAL_NOWRAP_CONV ths) t)) th in
  match tm with
    Comb(Const("val",_),Comb(Const("word",_),k)) when type_of(rand tm) = `:int64` ->
      let th = ISPEC k VAL_WORD_NOWRAP in
      MP th (side (lhand(concl th)))
  | Comb(Const("val",_),
         Comb(Comb(Const("word_add",_),x),Comb(Const("word",_),k)))
      when type_of x = `:int64` ->
      let th = ISPECL [x;k] VAL_WORD_ADD_NOWRAP in
      MP th (side (lhand(concl th)))
  | Comb(Const("val",_),
         Comb(Comb(Const("word_sub",_),x),Comb(Const("word",_),k)))
      when type_of x = `:int64` ->
      let th = ISPECL [x;k] VAL_WORD_SUB_NOWRAP in
      MP th (side (lhand(concl th)))
  | _ -> failwith "VAL_NOWRAP_CONV";;

(* The default decision: the arithmetic assumptions, rewritten by rws, with  *)
(* the values of words as numbers, and ARITH_TAC.                            *)

let BSTEP_ARITH_DECIDE_TAC ?(rws:thm list = []) : tactic =
  fun (asl,w) ->
    let arith th =
      let c = concl th in
      type_of c = bool_ty &&
      not(exists (fun v -> type_of v = `:armstate`) (frees c)) &&
      (try let _ = find_term (fun t -> match t with
             Const("read",_) | Const("write",_) -> true | _ -> false) c in
           false
       with Failure _ -> true) in
    let ths = map (REWRITE_RULE rws) (filter arith (map snd asl)) in
    (REWRITE_TAC(VAL_WORD_SUB_EQ_0 :: rws) THEN
     CONV_TAC(TOP_DEPTH_CONV (VAL_NOWRAP_CONV ths)) THEN
     MAP_EVERY MP_TAC ths THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) (asl,w);;

let ARM_BSTEP_DECIDE_TAC ?keep ?folds ?rewrites
      ?(decide:tactic = BSTEP_ARITH_DECIDE_TAC ~rws:[])
      execth snums : tactic =
  let rec go k (asl,w) =
    try ARM_BSTEP_TAC ?keep ?folds ?rewrites execth snums (asl,w)
    with Failure msg ->
        let c = try bstep_branch_condition () with Failure _ -> failwith msg in
        if k <= 0 then failwith ("ARM_BSTEP_DECIDE_TAC: too many branches: " ^
                                 msg) else
        let th =
          try TAC_PROOF((asl,c),decide) with Failure _ ->
          try TAC_PROOF((asl,mk_neg c),decide) with Failure _ ->
            failwith ("ARM_BSTEP_DECIDE_TAC: cannot decide `" ^
                      string_of_term c ^ "`") in
        (ASSUME_TAC th THEN go (k - 1)) (asl,w) in
  go 64;;
