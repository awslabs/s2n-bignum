(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the scalar loops of mldsa-native that compute    *)
(* one coefficient per iteration, possibly with data-dependent branches.     *)
(* ========================================================================= *)

needs "common/fips204/properties/mldsa_native.ml";;

(* ------------------------------------------------------------------------- *)
(* The mask of ct.h as a shift, for bit-blasting.                            *)
(* ------------------------------------------------------------------------- *)

let MLD_CT_CMASK_NEG_ISHR = prove
 (`!x:int32. mld_ct_cmask_neg x = word_ishr x 31`,
  REWRITE_TAC[mld_ct_cmask_neg; WORD_ISHR_31_COND]);;

(* ------------------------------------------------------------------------- *)
(* An equation between a value computed by the code and its specification,   *)
(* both functions of an input word (possibly under hypotheses), by           *)
(* bit-blasting. Bit-blasting a 32-bit product, or a sum of two unrelated    *)
(* 32-bit values, is slow, so the largest word subterm that occurs on both   *)
(* sides is first generalized to a variable, repeatedly, and then any        *)
(* remaining application of an mld_ function. This needs the defs to unfold  *)
(* the specification into the form of the code, with a product or sum       *)
(* computed in the same way on both sides; it is sound in any case, as an    *)
(* instance of a stronger claim, but may then fail.                          *)
(* ------------------------------------------------------------------------- *)

let GEN_COMMON_TAC =
  let rec size t =
    match t with
      Comb(f,x) -> size f + size x
    | Abs(_,b) -> 1 + size b
    | _ -> 1 in
  let is_word_ty ty = try fst(dest_type ty) = "word" with Failure _ -> false in
  let is_mld t =
    try let f,_ = strip_comb t in
        let n = name_of f in
        is_const f && String.length n > 4 && String.sub n 0 4 = "mld_"
    with Failure _ -> false in
  let cands t = find_terms (fun u -> is_comb u && is_word_ty(type_of u) &&
                                     frees u <> [] && size u >= 2) t in
  let body_of w =
    let b = snd(strip_forall w) in if is_imp b then rand b else b in
  let STEP_TAC =
    W(fun (asl,w) ->
      let l,r = dest_eq(body_of w) in
      let common = intersect (cands l) (cands r) in
      if common = [] then failwith "GEN_COMMON_TAC" else
      let t = hd(sort (fun a b -> size a > size b) common) in
      REPEAT GEN_TAC THEN SPEC_TAC(t,genvar(type_of t)))
  and MLD_TAC =
    W(fun (asl,w) ->
      let t = find_term is_mld (snd(strip_forall w)) in
      REPEAT GEN_TAC THEN SPEC_TAC(t,genvar(type_of t))) in
  REPEAT STEP_TAC THEN REPEAT MLD_TAC THEN REPEAT GEN_TAC;;

let IVAL_POS_32 = prove
 (`!w:int32. &0 < ival w <=> ~bit 31 w /\ ~(w = word 0)`,
  GEN_TAC THEN
  REWRITE_TAC[INT_ARITH `&0:int < x <=> ~(x < &0) /\ ~(x = &0)`;
              IVAL_EQ_0; GSYM MSB_IVAL; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV);;
