(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the x86 ML-KEM leaves whose vectors of results    *)
(* are computed lane by lane from fields of the input, in particular by      *)
(* table lookups (VPSHUFB with indices from the data). The terms that the    *)
(* simulation gives for such a vector are large, and slow the later steps,   *)
(* so the vector computed from each block of the input is replaced, as soon  *)
(* as it is computed, by a join of its lanes as a function of fields of that *)
(* block, by a lemma about the function of the block that the simulated term *)
(* is (proved once, lane by lane, by bit-blasting, and then reused for the   *)
(* other blocks, whose terms are the same function of their own block).      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(* ------------------------------------------------------------------------- *)
(* Making words, subwords and joins of lanes.                                *)
(* ------------------------------------------------------------------------- *)

let word_width ty = Num.int_of_num(dest_finty(dest_word_ty ty));;

let mk_word_ty_n n = mk_type("word",[mk_finty(Num.num_of_int n)]);;

let mk_wjoin h l =
  let pty = mk_word_ty_n(word_width(type_of h) + word_width(type_of l)) in
  let c = mk_const("word_join",[]) in
  let ty = mk_fun_ty (type_of h) (mk_fun_ty (type_of l) pty) in
  mk_comb(mk_comb(inst (type_match (type_of c) ty []) c,h),l);;

let mk_wsubword y p w =
  let c = mk_const("word_subword",[]) in
  let ty = mk_fun_ty (type_of y) (mk_fun_ty `:num#num` (mk_word_ty_n w)) in
  mk_comb(mk_comb(inst (type_match (type_of c) ty []) c,y),
          mk_pair(mk_small_numeral p,mk_small_numeral w));;

(*** The join of a list of lanes, lowest first, as a balanced tree (the
 *** form in which READ_MEMORY_SPLIT_CONV and SIMD_SIMPLIFY_CONV split it)
 ***)

let rec mk_jointree lanes =
  match lanes with
    [l] -> l
  | _ -> let lo,hi = chop_list (length lanes / 2) lanes in
         mk_wjoin (mk_jointree hi) (mk_jointree lo);;

(*** |- !y. y = (the join of the n lanes word_subword y (w * k,w)) ***)

let JOINTREE_SPLIT_RULE n w ty =
  let y = mk_var("y",ty) in
  BITBLAST_RULE(mk_forall(y,mk_eq(y,mk_jointree
    (map (fun k -> mk_wsubword y (k * w) w) (0--(n-1))))));;

(* ------------------------------------------------------------------------- *)
(* A lookup in a 16-byte table by a 4-bit index, as VPSHUFB does it, as a    *)
(* multiplexer over the bits of the index; and conditionals as masks, which  *)
(* the bit-blasting handles without splitting cases.                         *)
(* ------------------------------------------------------------------------- *)

let NYBBLE_LOOKUP_MUX = prove
 (`!(w:int128) (i:nybble).
     word_subword w (8 * val i,8):byte =
     if bit 3 i then
       if bit 2 i then
         if bit 1 i then
           if bit 0 i then word_subword w (120,8) else word_subword w (112,8)
         else if bit 0 i then word_subword w (104,8) else word_subword w (96,8)
       else if bit 1 i then
           if bit 0 i then word_subword w (88,8) else word_subword w (80,8)
         else if bit 0 i then word_subword w (72,8) else word_subword w (64,8)
     else
       if bit 2 i then
         if bit 1 i then
           if bit 0 i then word_subword w (56,8) else word_subword w (48,8)
         else if bit 0 i then word_subword w (40,8) else word_subword w (32,8)
       else if bit 1 i then
           if bit 0 i then word_subword w (24,8) else word_subword w (16,8)
         else if bit 0 i then word_subword w (8,8) else word_subword w (0,8)`,
  GEN_TAC THEN
  SUBGOAL_THEN `!P. (!i:nybble. P i) <=> (!n. n < 16 ==> P(word n:nybble))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
    X_GEN_TAC `i:nybble` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `val(i:nybble)`) THEN
    REWRITE_TAC[WORD_VAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPEC `i:nybble` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_CONV `dimindex(:4)`] THEN ARITH_TAC;
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV)) THEN
    REWRITE_TAC[]]);;

let COND_AS_MASK = prove
 (`!b (x:N word) y.
     (if b then x else y) =
     word_or (word_and (word_neg(word(bitval b))) x)
             (word_and (word_not(word_neg(word(bitval b)))) y)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_NOT;
              BIT_WORD_MASK] THEN
  MESON_TAC[]);;

(*** A lane of a simulated vector given as a function of fields of the
 *** input, with the lane functions defined in defs: their tables are
 *** expanded into multiplexers, the lane is picked out of the vector, and
 *** the result is bit-blasted
 ***)

let LANE_BITBLAST_TAC defs =
  REPEAT GEN_TAC THEN
  REWRITE_TAC(NYBBLE_LOOKUP_MUX :: defs) THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[COND_AS_MASK] THEN
  BITBLAST_TAC;;

(* ------------------------------------------------------------------------- *)
(* The abstraction of the vector computed from one block. A lemma maker      *)
(* (n,w,lane,tac) for vectors of n lanes of w bits proves, for a term t      *)
(* whose variables vs are the words of the block,                            *)
(*                                                                           *)
(* |- !xs. t[xs/vs] = (the join of the lanes (lane xs k) for k < n)          *)
(*                                                                           *)
(* each lane by tac; the lemmas are cached by the abstracted term, so each   *)
(* function is proved once. The words of a block should be variables (e.g.   *)
(* abbreviations of the loaded words), so that the terms of all the blocks   *)
(* are the same function and do not grow with their offsets.                 *)
(* ------------------------------------------------------------------------- *)

let CHUNK_LEMMA =
  let cache = ref ([]:(term*thm)list) in
  fun (n,w,lane,tac) vs t ->
    let xs = map2 (fun i v -> mk_var("x"^string_of_int i,type_of v))
                  (0--(length vs - 1)) vs in
    let body = subst (zip xs vs) t in
    let key = list_mk_abs(xs,body) in
    let th =
      try assoc key !cache with Failure _ ->
      let lanes = map (fun k ->
        prove(list_mk_forall(xs,mk_eq(mk_wsubword body (k * w) w,lane xs k)),
              tac)) (0--(n-1)) in
      let jt = JOINTREE_SPLIT_RULE n w (type_of body) in
      let th = GENL xs (CONV_RULE(RAND_CONV(REWRITE_CONV(map SPEC_ALL lanes)))
                          (SPEC body jt)) in
      cache := (key,th) :: !cache; th in
    SPECL vs th;;

(*** At state k, replace the value of register reg (the vector just computed
 *** from the block with words vs) by the join of its lanes. The new fact is
 *** put back as an assumption by MP_TAC and DISCH_TAC rather than
 *** ASSUME_TAC, so that it does not keep the large term as a hypothesis.
 ***)

let CHUNK_ABSTRACT_TAC lemmaspec reg vs k =
  let sv = mk_var("s"^string_of_int k,`:x86state`) in
  let lpat = list_mk_icomb "read" [reg; sv] in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if not(is_eq c) || lhs c <> lpat then failwith "CHUNK_ABSTRACT_TAC" else
    MP_TAC(TRANS th (CHUNK_LEMMA lemmaspec vs (rhs c))) THEN DISCH_TAC);;

(* ------------------------------------------------------------------------- *)
(* SIMD simplification that also pushes subwords through word_not (from     *)
(* VPANDN), and the result of VPMOVMSKB as a join of bits.                   *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_NOT_CONV tm =
  let th = PART_MATCH (lhs o rand) WORD_SUBWORD_NOT tm in
  MP th (EQT_ELIM((DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
                    (lhand(concl th))));;

let SIMD_SIMPLIFY_NOT_CONV defs =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SUBWORD_NOT_CONV ORELSEC
    WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV (map GSYM defs);;

let SIMD_SIMPLIFY_NOT_TAC defs =
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_NOT_CONV defs)) o
    check (can (term_match [] `read X (s:x86state):int256 = whatever`) o
           concl)));;

(*** |- !b0 ... bn. word(bitval b0 + 2 * bitval b1 + 4 * bitval b2 + ...)
 ***               = (the join of the bits word(bitval bk):1 word),
 *** the form of the result of VPMOVMSKB in the simulation (n = 32)
 ***)

let MASK_JOIN_RULE n =
  let bs = map (fun i -> mk_var("b"^string_of_int i,`:bool`)) (0--(n-1)) in
  let sum = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
    (map2 (fun i b ->
       let bv = mk_comb(`bitval`,b) in
       if i = 0 then bv else
       mk_binop `( * ):num->num->num`
         (mk_numeral(Num.power_num (Num.num_of_int 2) (Num.num_of_int i))) bv)
     (0--(n-1)) bs) in
  let lhs = mk_comb(mk_const("word",[mk_finty(Num.num_of_int n),`:N`]),sum) in
  let lanes = map (fun b -> mk_comb(`word:num->1 word`,mk_comb(`bitval`,b)))
                  bs in
  prove(list_mk_forall(bs,mk_eq(lhs,mk_jointree lanes)),BITBLAST_TAC);;
