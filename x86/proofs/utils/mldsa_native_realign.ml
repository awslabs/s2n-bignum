(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the functions of mldsa-native's x86-64 code that  *)
(* align their stack frames to 32 bytes with AND RSP,-32, so that the        *)
(* addresses in the frame depend on the stack pointer on entry. Their        *)
(* statements allow for the up to 31 bytes by which the AND may lower RSP,   *)
(* within the N bytes of stack below the return address, without assuming    *)
(* the alignment of the stack that the ABI guarantees, and the proofs follow *)
(* those of the x86 proofs of mlkem-native for such functions (e.g.          *)
(* mlkem512_check_pk). After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC,             *)
(* stackpointer is the bottom of the N bytes, and the AND is of word_add     *)
(* stackpointer (word k), where N - k bytes have been pushed before it (k =  *)
(* N if the AND comes first, as when gcc keeps a copy of the original stack  *)
(* pointer in R10). REALIGN_TAC k introduces                                 *)
(*                                                                           *)
(*   delta = 31 - val(word_add stackpointer (word k)) MOD 32                 *)
(*   bot = word_add stackpointer (word delta)                                *)
(*                                                                           *)
(* with delta <= 31 and the value word_add bot (word(k - 31)) of the AND, so *)
(* that the aligned frame and the stacks of the callees are at fixed offsets *)
(* in the region (bot,k - 31), and the registers pushed before the AND are   *)
(* in (word_add stackpointer (word k),N - k). REALIGN_FRAME_TAC N k then     *)
(* states the frame of the goal with these two regions in place of the N     *)
(* bytes, and REALIGN_NONOV_TAC l rs gives the region (bot,l) apart from     *)
(* each region of rs. After the AND, REALIGN_RSP_TAC puts its value in RSP.  *)
(* The events must not depend on bot and delta, which are not arguments of   *)
(* the events function, so REALIGN_UNBOT_TAC expands them before the events  *)
(* are matched at the end of each part of a proof.                           *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_full.ml";;

let REALIGN_AND_MASK = prove
 (`!x:int64. word_and x (word 18446744073709551584) =
             word_sub x (word_and x (word 31))`,
  CONV_TAC WORD_BLAST);;

let REALIGN_AND = prove
 (`!(p:int64) k.
        31 <= k
        ==> word_and (word_add p (word k)) (word 18446744073709551584) =
            word_add
             (word_add p (word(31 - val(word_add p (word k)) MOD 32)))
             (word(k - 31))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALIGN_AND_MASK] THEN
  SUBGOAL_THEN
   `val(word_add p (word k):int64) MOD 32 =
    val(word_and (word_add p (word k)) (word 31):int64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `31 = 2 EXP 5 - 1`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM WORD_VAL] THEN
  ABBREV_TAC `m = val(word_and (word_add p (word k)) (word 31):int64)` THEN
  SUBGOAL_THEN `m < 32` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `31 = 2 EXP 5 - 1`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE
   `word_sub (word_add a b) c:int64 = word_add a (word_sub b c)`;
   WORD_RULE
   `word_add (word_add a b) c:int64 = word_add a (word_add b c)`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  SUBGOAL_THEN `(31 - m) + (k - 31) = k - m` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `m < 32 /\ 31 <= k ==> m <= k`]);;

let REALIGN_TAC k =
  let kt = mk_small_numeral k in
  let x = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                  mk_comb(`word:num->int64`,kt)) in
  let dtm = mk_binop `(-):num->num->num` `31`
             (mk_binop `(MOD):num->num->num` (mk_comb(`val:int64->num`,x))
                       `32`) in
  let th = CONV_RULE(DEPTH_CONV NUM_SUB_CONV)
            (MP (SPECL [`stackpointer:int64`; kt] REALIGN_AND)
                (EQT_ELIM(NUM_REDUCE_CONV
                  (mk_binop `(<=):num->num->bool` `31` kt)))) in
  let gtm = mk_eq(lhs(concl th),
                  mk_comb(mk_comb(`word_add:int64->int64->int64`,`bot:int64`),
                          mk_comb(`word:num->int64`,
                                  mk_small_numeral(k - 31)))) in
  ABBREV_TAC(mk_eq(`delta:num`,dtm)) THEN
  SUBGOAL_THEN `delta <= 31` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `bot = word_add (stackpointer:int64) (word delta)` THEN
  SUBGOAL_THEN gtm ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["bot"; "delta"] THEN ACCEPT_TAC th; ALL_TAC];;

(*** The frame of the goal with the two regions for the N bytes ***)

let REALIGN_FRAME_TAC n k =
  let sp = `stackpointer:int64` in
  let mk_reg a l =
    subst [a,`a:int64`; l,`l:num`] `memory :> bytes(a:int64,l:num)` in
  let old = mk_reg sp (mk_small_numeral n) in
  let news =
    mk_reg `bot:int64` (mk_small_numeral(k - 31)) ::
    (if n = k then [] else
     [mk_reg (mk_comb(mk_comb(`word_add:int64->int64->int64`,sp),
                      mk_comb(`word:num->int64`,mk_small_numeral k)))
             (mk_small_numeral(n - k))]) in
  let rec fix tm =
    match tm with
      Comb(Const("MAYCHANGE",_) as c,l) when is_list l ->
        let els = dest_list l in
        if mem old els then
          let ty = type_of(hd els) in
          mk_comb(c,mk_list(flat(map (fun e -> if e = old then news else [e])
                                     els),ty))
        else tm
    | Comb(f,x) -> mk_comb(fix f,fix x)
    | _ -> tm in
  W(fun (asl,w) ->
    let c = rand w in
    let c' = fix c in
    if c' = c then failwith "REALIGN_FRAME_TAC: no stack region" else
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC c' THEN
    CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["bot"; "delta"] THEN SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC]);;

(*** The region (bot,l) apart from each of the regions rs ***)

let REALIGN_NONOV_TAC l rs =
  let r0 = mk_pair(`bot:int64`,mk_small_numeral l) in
  MAP_EVERY (fun r ->
    SUBGOAL_THEN
     (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,r0),r))
     ASSUME_TAC THENL
     [EXPAND_TAC "bot" THEN NONOVERLAPPING_TAC; ALL_TAC]) rs;;

(*** The value of the AND in RSP ***)

let REALIGN_RSP_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `word_and (word_add stackpointer (word k))
                            (word 18446744073709551584):int64 = x`)
           (concl th)
    then RULE_ASSUM_TAC(fun th' ->
           if free_in `RSP` (concl th') then REWRITE_RULE[th] th' else th')
    else NO_TAC);;

(*** Expanding bot and delta, for matching the events ***)

let REALIGN_UNBOT_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `bot:int64`
    then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `delta:num`
    then SUBST_ALL_TAC(SYM th) else NO_TAC);;
