(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The elements of the words that LD3 reads and that ST3 and ST4 write, as   *)
(* trees of word_join of their elements, for the simulation of vectorized    *)
(* code that uses them on 128-bit registers. The model gives the registers   *)
(* loaded by LD3 as word_subdeinterleave 3 esize z j, for the 384 bits z     *)
(* read, and the 128-bit parts of the memory written by ST3 and ST4 as       *)
(* word_subword (word_interleave esize [x1; ...; xl]) (128 * m,128). The     *)
(* rules below give these as joins of elements (word_subword of z, or of the *)
(* registers), which SIMD_SIMPLIFY_CONV can then simplify further. Each rule *)
(* is proved bit by bit, when it is first needed, and then cached.           *)
(* ========================================================================= *)

let mlkem_native_word_index t = hd(snd(dest_type t));;

(*** A balanced tree of word_join of a list of words, most significant
 *** first, as the simulation produces it for loads ***)

let rec MLKEM_NATIVE_JOIN_TREE l =
  match l with
    [x] -> x
  | _ -> let n = length l / 2 in
         let hl,ll = chop_list n l in
         let hi = MLKEM_NATIVE_JOIN_TREE hl
         and lo = MLKEM_NATIVE_JOIN_TREE ll in
         let size t = dest_finty(hd(snd(dest_type(type_of t)))) in
         let ty = mk_type("word",[mk_finty(size hi +/ size lo)]) in
         let jn = inst [mlkem_native_word_index(type_of hi),`:A`; mlkem_native_word_index(type_of lo),`:B`;
                        mlkem_native_word_index ty,`:C`]
                       `word_join:A word->B word->C word` in
         mk_comb(mk_comb(jn,hi),lo);;

let MLKEM_NATIVE_BITWISE_TAC defs =
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN REWRITE_TAC defs THEN
  REPEAT(CHANGED_TAC
   (CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
    CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC EL_CONV ORELSEC
                        LENGTH_CONV ORELSEC DIMINDEX_CONV)) THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV))) THEN
  REWRITE_TAC[];;

(*** word_subdeinterleave l e z j = the elements j, l + j, 2 * l + j, ...
 *** of e bits of z:(128 * l) word, a 128-bit word ***)

let MLKEM_NATIVE_DEINTERLEAVE_LEMMA =
  let cache = ref [] in
  fun l e j ->
    try assoc (l,e,j) (!cache) with Failure _ ->
    let zty = mk_type("word",[mk_finty(Num.num_of_int(128 * l))]) in
    let ety = mk_type("word",[mk_finty(Num.num_of_int e)]) in
    let z = mk_var("z",zty) in
    let sub k =
      mk_comb(mk_comb(inst [mlkem_native_word_index zty,`:A`; mlkem_native_word_index ety,`:B`]
                       `word_subword:A word->num#num->B word`,z),
              mk_pair(mk_small_numeral(e * (l * k + j)),mk_small_numeral e)) in
    let rhs = MLKEM_NATIVE_JOIN_TREE (map sub (rev(0--(128 / e - 1)))) in
    let lhs = list_mk_comb
     (inst [mlkem_native_word_index zty,`:A`; `:128`,`:B`]
       `word_subdeinterleave:num->num->A word->num->B word`,
      [mk_small_numeral l; mk_small_numeral e; z; mk_small_numeral j]) in
    let th = GEN z (prove(mk_eq(lhs,rhs),
                          MLKEM_NATIVE_BITWISE_TAC [word_subdeinterleave])) in
    (cache := ((l,e,j),th)::(!cache); th);;

(*** word_subword (word_interleave e [x1; ...; xl]) (128 * m,128), for
 *** 128-bit words xi, as the elements of e bits from them ***)

let MLKEM_NATIVE_INTERLEAVE_LEMMA =
  let cache = ref [] in
  fun l e m ->
    try assoc (l,e,m) (!cache) with Failure _ ->
    let zty = mk_type("word",[mk_finty(Num.num_of_int(128 * l))]) in
    let ety = mk_type("word",[mk_finty(Num.num_of_int e)]) in
    let xs = map (fun i -> mk_var("x"^string_of_int i,`:int128`)) (1--l) in
    let per = 128 / e in
    let elt t =
      let x = el (t mod l) xs in
      mk_comb(mk_comb(inst [`:128`,`:A`; mlkem_native_word_index ety,`:B`]
                       `word_subword:A word->num#num->B word`,x),
              mk_pair(mk_small_numeral(e * (t / l)),mk_small_numeral e)) in
    let rhs = MLKEM_NATIVE_JOIN_TREE
      (map elt (rev((per * m)--(per * m + per - 1)))) in
    let ilv = mk_comb(mk_comb(inst [`:128`,`:N`; mlkem_native_word_index zty,`:M`]
                        `word_interleave:num->(N word)list->M word`,
                       mk_small_numeral e),
                      mk_list(xs,`:int128`)) in
    let lhs = mk_comb(mk_comb(inst [mlkem_native_word_index zty,`:A`; `:128`,`:B`]
                        `word_subword:A word->num#num->B word`,ilv),
                      mk_pair(mk_small_numeral(128 * m),`128`)) in
    let th = GENL xs (prove(mk_eq(lhs,rhs),
                            MLKEM_NATIVE_BITWISE_TAC [word_interleave])) in
    (cache := ((l,e,m),th)::(!cache); th);;

(*** Rewrite all such terms in a theorem or assumption ***)

let MLKEM_NATIVE_INTERLEAVE_CONV tm =
  match tm with
    Comb(Comb(Comb(Comb(Const("word_subdeinterleave",_),l),e),z),j)
      when is_numeral l && is_numeral e && is_numeral j &&
           type_of tm = `:int128` ->
      ISPEC z (MLKEM_NATIVE_DEINTERLEAVE_LEMMA
                (dest_small_numeral l) (dest_small_numeral e)
                (dest_small_numeral j))
  | Comb(Comb(Const("word_subword",_),
              (Comb(Comb(Const("word_interleave",_),e),xl) as ilv)),
         Comb(Comb(Const(",",_),p),w))
      when is_numeral e && is_list xl && is_numeral p && is_numeral w &&
           dest_small_numeral w = 128 &&
           dest_small_numeral p mod 128 = 0 &&
           type_of tm = `:int128` ->
      let xs = dest_list xl in
      ISPECL xs (MLKEM_NATIVE_INTERLEAVE_LEMMA (length xs)
                  (dest_small_numeral e) (dest_small_numeral p / 128))
  | _ -> failwith "MLKEM_NATIVE_INTERLEAVE_CONV";;

let MLKEM_NATIVE_INTERLEAVE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> match t with
              Const(("word_subdeinterleave"|"word_interleave"),_) -> true
            | _ -> false)) (concl th)
    then CONV_RULE(TOP_DEPTH_CONV MLKEM_NATIVE_INTERLEAVE_CONV) th
    else th);;
