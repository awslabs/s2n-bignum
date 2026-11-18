(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the scalar loops of mldsa-native that compute    *)
(* one coefficient per iteration, possibly with data-dependent branches.     *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_scalar.ml.                         *)

needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/fips204/properties/mldsa_native_scalar.ml";;

let LANE_BLAST_TAC (defs:thm list) =
  REWRITE_TAC(MLD_CT_CMASK_NEG_ISHR::defs) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_ZX_ZX_32_64_32; ADD_CLAUSES; WORD_ADD; WORD_MUL;
              WORD_VAL; VAL_EQ_0; WORD_SUB_0; INT_SUB_RZERO; IVAL_POS_32;
              GSYM MSB_IVAL; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_COMMON_TAC THEN BITBLAST_TAC;;

(* ------------------------------------------------------------------------- *)
(* After the simulation of an iteration that stores a function of the input  *)
(* coefficient v (such as x i) as a 32-bit word at the address addr, replace *)
(* the stored value by f v, proving the equation for all values of v with    *)
(* LANE_BLAST_TAC defs. The equation also rewrites the other assumptions, so *)
(* that a later value computed from this one has it as f v.                  *)
(* ------------------------------------------------------------------------- *)

let SCALAR_LANE_TAC (addr:term) (v:term) (f:term) (defs:thm list) =
  let is_store l =
    try let c = rand(rator l) in
        let b,a = dest_comb(rand c) in
        name_of(rator(rator l)) = "read" && name_of b = "bytes32" && a = addr
    with Failure _ -> false in
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if is_store l && free_in v r then
      let y = genvar(type_of v) in
      let lemma = prove
       (mk_forall(y,mk_eq(subst[y,v] r,mk_comb(f,y))),
        GEN_TAC THEN LANE_BLAST_TAC defs) in
      ASSUME_TAC(REWRITE_RULE[lemma] th) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[lemma])
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The same for a stored value that depends on two inputs v1 and v2 (such as *)
(* x i and y i), under the assumptions about them that the case splits of    *)
(* BRANCH_CASES_TAC have made: those that contain v1 or v2 and no other free *)
(* variables than those of v1 and v2, other than facts about the state.      *)
(* ------------------------------------------------------------------------- *)

let SCALAR_LANE2_TAC (addr:term) (v1:term) (v2:term) (f:term)
                     (defs:thm list) =
  let is_store l =
    try let c = rand(rator l) in
        let b,a = dest_comb(rand c) in
        name_of(rator(rator l)) = "read" && name_of b = "bytes32" && a = addr
    with Failure _ -> false in
  W(fun (asl,w) ->
    let vs = frees v1 @ frees v2 in
    let conds = filter (fun t ->
      not(is_eq t && is_comb(lhs t) &&
          (try name_of(rator(rator(lhs t))) = "read" with Failure _ -> false))
      && (free_in v1 t || free_in v2 t) &&
      subset (subtract (frees t) vs) [])
     (map (concl o snd) asl) in
    FIRST_X_ASSUM(fun th ->
      let l,r = dest_eq(concl th) in
      if is_store l && (free_in v1 r || free_in v2 r) then
        let y1 = genvar(type_of v1) and y2 = genvar(type_of v2) in
        let sb = subst [y1,v1; y2,v2] in
        let hyp = if conds = [] then `T` else list_mk_conj(map sb conds) in
        let lemma = prove
         (list_mk_forall([y1;y2],
            mk_imp(hyp,mk_eq(sb r,list_mk_comb(f,[y1;y2])))),
          REPEAT GEN_TAC THEN LANE_BLAST_TAC defs) in
        let hth = if conds = [] then TRUTH
                  else end_itlist CONJ (map ASSUME conds) in
        ASSUME_TAC(TRANS th (MP (SPECL [v1;v2] lemma) hth))
      else NO_TAC));;

(* ------------------------------------------------------------------------- *)
(* Within an iteration, replace the value in the 64-bit register reg (such   *)
(* as X2) computed from the input v by word_zx (f v), proving the equation   *)
(* for all v with LANE_BLAST_TAC defs, so that the values computed from it   *)
(* in the rest of the iteration are in terms of f v. This keeps the terms    *)
(* small when the code computes several functions of the same intermediate   *)
(* values (as mld_use_hint does with the high and low parts).                *)
(* ------------------------------------------------------------------------- *)

let REG_LANE_TAC (reg:term) (v:term) (f:term) (defs:thm list) =
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if (try rand(rator l) = reg with Failure _ -> false) && free_in v r then
      let y = genvar(type_of v) in
      let lemma = prove
       (mk_forall(y,mk_eq(subst[y,v] r,
                          mk_comb(`word_zx:int32->int64`,mk_comb(f,y)))),
        GEN_TAC THEN LANE_BLAST_TAC defs) in
      ASSUME_TAC(REWRITE_RULE[lemma] th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Split the goal on the condition of a conditional branch whose target the  *)
(* simulation could not decide, read PC s = if c then .. else .., so that    *)
(* the simulation can go on in each case.                                    *)
(* ------------------------------------------------------------------------- *)

let BRANCH_CASES_TAC =
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if not(is_cond r) || not(can (term_match [] `read PC s`) l)
    then failwith "BRANCH_CASES_TAC" else
    let c = lhand(rator r) in
    ASM_CASES_TAC c THENL
     [ASSUME_TAC(REWRITE_RULE[ASSUME c] th);
      ASSUME_TAC(REWRITE_RULE[ASSUME(mk_neg c)] th)]);;
