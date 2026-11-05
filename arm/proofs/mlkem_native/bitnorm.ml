(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A bit-level normal form for the words in vectorized code. When compiled   *)
(* code moves the fields of its input around with TBL, shifts, masks, lane   *)
(* inserts and the like, the simulation composes the terms for these         *)
(* operations, and the terms for later registers grow with every step (in    *)
(* mlkem_poly_decompress_d10 at clang -O3, to some 500 KB per lane), since   *)
(* SIMD_SIMPLIFY_CONV only pushes word_subword through word_and and joins.   *)
(*                                                                           *)
(* Here each bit of such a term is computed in OCaml as a constant or as a   *)
(* bit of an "atom", a maximal subterm that is not a bit operation (e.g. a   *)
(* variable for the input, or a product), and the term is replaced by the    *)
(* join of its runs of constant bits and of consecutive bits of one atom,    *)
(* e.g.                                                                      *)
(*                                                                           *)
(*   word_and (word_shl (word_join x y:int32) 8) (word 0x300)                *)
(*     = word_join (word 0:22 word)                                          *)
(*        (word_join (word_subword y (0,2):2 word) (word 0:8 word))          *)
(*                                                                           *)
(* for bytes x and y. The equation is proved by bit-blasting with the atoms  *)
(* replaced by variables. Applied after each step of a simulation, this      *)
(* keeps each register as small as the fields it holds.                      *)
(*                                                                           *)
(* The bit operations are word_subword, word_join, word_zx, word_sx,         *)
(* word_ushr, word_shl, word_and, word_or, word_xor, word_not, word_insert,  *)
(* and word_add when no carries can occur (no bit position that is not zero  *)
(* in both, or x + x as a shift); numbers in them must be ground. Anything   *)
(* else, or a combination of two different bits of atoms, is an atom.       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/interleave.ml";;

let bits_wsize ty =
  match ty with
    Tyapp("word",[n]) -> Num.int_of_num(dest_finty n)
  | _ -> failwith "bits_wsize";;

(*** Each bit is -1 (zero), -2 (one) or 4096 * k + j for bit j of atom k ***)

let bits_atom atoms tm =
  let rec find i l =
    match l with
      [] -> atoms := !atoms @ [tm]; i
    | t::ts -> if t = tm then i else find (i + 1) ts in
  find 0 !atoms;;

let bits_value b =
  Array.fold_right
    (fun x acc -> if x = -1 then num 2 */ acc
                  else if x = -2 then num 2 */ acc +/ num 1
                  else failwith "bits_value: not constant") b (num 0);;

let rec bits_num atoms tm =
  if is_numeral tm then dest_numeral tm else
  match tm with
    Comb(Comb(Const("*",_),a),b) -> bits_num atoms a */ bits_num atoms b
  | Comb(Comb(Const("+",_),a),b) -> bits_num atoms a +/ bits_num atoms b
  | Comb(Comb(Const("EXP",_),a),b) ->
      power_num (bits_num atoms a) (bits_num atoms b)
  | Comb(Comb(Const("-",_),a),b) ->
      let x = bits_num atoms a -/ bits_num atoms b in
      if x </ num 0 then num 0 else x
  | Comb(Const("val",_),x) -> bits_value(bits_eval atoms x)
  | _ -> failwith "bits_num"

and bits_eval atoms tm =
  let n = bits_wsize(type_of tm) in
  try bits_eval_op atoms n tm with Failure _ ->
  let k = bits_atom atoms tm in
  Array.init n (fun i -> 4096 * k + i)

and bits_eval_op atoms n tm =
  let num_of t = Num.int_of_num(bits_num atoms t) in
  let const v =
    let k = ref v and r = Array.make n (-1) in
    for i = 0 to n - 1 do
      (if mod_num !k (num 2) =/ num 1 then r.(i) <- -2);
      k := quo_num !k (num 2)
    done; r in
  let bitop f x y =
    let xb = bits_eval atoms x and yb = bits_eval atoms y in
    Array.init n (fun i -> f xb.(i) yb.(i)) in
  match tm with
    Comb(Const("word",_),k) -> const(bits_num atoms k)
  | Comb(Comb(Const("word_subword",_),x),pl) ->
      let p,l = dest_pair pl in
      let p = num_of p and l = num_of l and xb = bits_eval atoms x in
      let m = Array.length xb in
      Array.init n (fun i -> if i < l && p + i < m then xb.(p + i) else -1)
  | Comb(Comb(Const("word_join",_),x),y) ->
      let xb = bits_eval atoms x and yb = bits_eval atoms y in
      let nx = Array.length xb and ny = Array.length yb in
      Array.init n (fun i -> if i < ny then yb.(i)
                             else if i - ny < nx then xb.(i - ny) else -1)
  | Comb(Const("word_zx",_),x) ->
      let xb = bits_eval atoms x in
      let m = Array.length xb in
      Array.init n (fun i -> if i < m then xb.(i) else -1)
  | Comb(Const("word_sx",_),x) ->
      let xb = bits_eval atoms x in
      let m = Array.length xb in
      Array.init n (fun i -> if i < m then xb.(i) else xb.(m - 1))
  | Comb(Comb(Const("word_ushr",_),x),k) ->
      let k = num_of k in
      let xb = bits_eval atoms x in
      Array.init n (fun i -> if i + k < n then xb.(i + k) else -1)
  | Comb(Comb(Const("word_shl",_),x),k) ->
      let k = num_of k in
      let xb = bits_eval atoms x in
      Array.init n (fun i -> if i >= k then xb.(i - k) else -1)
  | Comb(Comb(Const("word_and",_),x),y) ->
      bitop (fun a b ->
        if a = -1 || b = -1 then -1 else if a = -2 then b
        else if b = -2 then a else if a = b then a
        else failwith "bits_eval: word_and") x y
  | Comb(Comb(Const("word_or",_),x),y) ->
      bitop (fun a b ->
        if a = -2 || b = -2 then -2 else if a = -1 then b
        else if b = -1 then a else if a = b then a
        else failwith "bits_eval: word_or") x y
  | Comb(Comb(Const("word_xor",_),x),y) ->
      bitop (fun a b ->
        if a = -1 then b else if b = -1 then a
        else if a = -2 && b = -2 then -1 else if a = b then -1
        else failwith "bits_eval: word_xor") x y
  | Comb(Const("word_not",_),x) ->
      let xb = bits_eval atoms x in
      Array.init n (fun i ->
        let a = xb.(i) in
        if a = -1 then -2 else if a = -2 then -1
        else failwith "bits_eval: word_not")
  | Comb(Comb(Comb(Const("word_insert",_),x),pl),y) ->
      let p,l = dest_pair pl in
      let p = num_of p and l = num_of l in
      let xb = bits_eval atoms x and yb = bits_eval atoms y in
      let nx = Array.length xb and ny = Array.length yb in
      Array.init n (fun i ->
        if p <= i && i < p + l then (if i - p < ny then yb.(i - p) else -1)
        else if i < nx then xb.(i) else -1)
  | Comb(Comb(Const("word_add",_),x),y) ->
      let xb = bits_eval atoms x in
      if x = y then Array.init n (fun i -> if i = 0 then -1 else xb.(i - 1))
      else
        let yb = bits_eval atoms y in
        if Array.for_all (fun b -> b < 0) xb &&
           Array.for_all (fun b -> b < 0) yb
        then const(mod_num (bits_value xb +/ bits_value yb)
                           (power_num (num 2) (num n)))
        else Array.init n (fun i ->
          if xb.(i) = -1 then yb.(i) else if yb.(i) = -1 then xb.(i)
          else failwith "bits_eval: word_add")
  | _ -> failwith "bits_eval_op";;

(*** The normal form: a join of pieces, each a constant or a run of
 *** consecutive bits of an atom, the most significant first; a run of all
 *** the bits of an atom is the atom itself ***)

let bits_nf atoms b =
  let n = Array.length b in
  let runs = ref [] and i = ref 0 in
  while !i < n do
    let s = !i and bs = b.(!i) in
    let j = ref (s + 1) in
    (if bs < 0 then while !j < n && b.(!j) < 0 do incr j done
     else while !j < n && b.(!j) = bs + (!j - s) do incr j done);
    runs := (s,!j - s,bs) :: !runs;
    i := !j
  done;
  let piece (s,l,bs) =
    let ty = mk_finty(num l) in
    if bs < 0 then
      let v = ref(num 0) in
      for k = s + l - 1 downto s do
        v := num 2 */ !v +/ (if b.(k) = -2 then num 1 else num 0)
      done;
      mk_comb(inst [ty,`:N`] `word:num->N word`,mk_numeral !v)
    else
      let a = el (bs / 4096) atoms and p = bs mod 4096 in
      if p = 0 && bits_wsize(type_of a) = l then a else
      let aty = hd(snd(dest_type(type_of a))) in
      mk_comb(mk_comb(inst [aty,`:M`; ty,`:N`]
                       `word_subword:M word->num#num->N word`,a),
              mk_pair(mk_small_numeral p,mk_small_numeral l)) in
  let join (l1,t1) (l2,t2) =
    let ty1 = mk_finty(num l1) and ty2 = mk_finty(num l2)
    and ty = mk_finty(num(l1 + l2)) in
    l1 + l2,
    mk_comb(mk_comb(inst [ty1,`:M`; ty2,`:N`; ty,`:P`]
                     `word_join:M word->N word->P word`,t1),t2) in
  match map (fun (s,l,bs) -> l,piece(s,l,bs)) !runs with
    [] -> failwith "bits_nf"
  | p::ps -> snd(itlist (fun q acc -> join acc q) (rev ps) p);;

(*** t = its normal form, by bit-blasting with the atoms generalized ***)

let BITS_NORM_CONV tm =
  let atoms = ref [] in
  let b = bits_eval atoms tm in
  let tm' = bits_nf !atoms b in
  if tm' = tm then REFL tm else
  let ats = !atoms in
  let gs = map (genvar o type_of) ats in
  let ith = BITBLAST_RULE(subst (zip gs ats) (mk_eq(tm,tm'))) in
  INST (zip ats gs) ith;;

(*** Any fact read c s = t about a word is put in normal form. The facts
 *** are carried from state to state with the same values, so the values
 *** known to be in normal form (or to be left alone) are remembered ***)

module Bits_termtbl = Hashtbl.Make(struct
  type t = term
  let equal = (=)
  let hash = Hashtbl.hash_param 64 512
end);;

let bits_done : unit Bits_termtbl.t = Bits_termtbl.create 4096;;

let BITS_NORM_RULE th =
  let c = concl th in
  if not(is_eq c &&
         (match lhs c with
            Comb(Comb(Const("read",_),_),_) -> true
          | _ -> false) &&
         can bits_wsize (type_of(rhs c)))
  then th else
  let t = rhs c in
  if Bits_termtbl.mem bits_done t then th else
  try let eth = BITS_NORM_CONV t in
      let t' = rand(concl eth) in
      Bits_termtbl.replace bits_done t' ();
      if t' = t then th else TRANS th eth
  with Failure _ -> (Bits_termtbl.replace bits_done t (); th);;

let BITS_NORM_TAC = RULE_ASSUM_TAC BITS_NORM_RULE;;

(*** word_interleave e [x1; ...; xl] for n-bit words xi (as ST2-ST4 store
 *** them) as the join of its elements, most significant first, proved bit
 *** by bit when first needed and cached; MLKEM_NATIVE_INTERLEAVE_CONV in
 *** interleave.ml only covers 128-bit parts of it for 128-bit words ***)

let BITS_INTERLEAVE_LEMMA =
  let cache = ref [] in
  fun l e n ->
    try assoc (l,e,n) (!cache) with Failure _ ->
    let xty = mk_type("word",[mk_finty(Num.num_of_int n)]) in
    let xs = map (fun i -> mk_var("x"^string_of_int i,xty)) (1--l) in
    let elt t =
      mk_comb(mk_comb(inst [mk_finty(Num.num_of_int n),`:A`;
                            mk_finty(Num.num_of_int e),`:B`]
                       `word_subword:A word->num#num->B word`,el (t mod l) xs),
              mk_pair(mk_small_numeral(e * (t / l)),mk_small_numeral e)) in
    let rhs = MLKEM_NATIVE_JOIN_TREE (map elt (rev(0--(l * n / e - 1)))) in
    let lhs = mk_comb(mk_comb(inst [mk_finty(Num.num_of_int n),`:N`;
                                    mk_finty(Num.num_of_int(l * n)),`:M`]
                        `word_interleave:num->(N word)list->M word`,
                       mk_small_numeral e),
                      mk_list(xs,xty)) in
    let th = GENL xs (prove(mk_eq(lhs,rhs),
      GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
      CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
      CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
      REWRITE_TAC[word_interleave] THEN
      REPEAT(CHANGED_TAC
       (CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
        CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC EL_CONV ORELSEC
                            LENGTH_CONV ORELSEC DIMINDEX_CONV)) THEN
        CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV))) THEN
      REWRITE_TAC[])) in
    (cache := ((l,e,n),th)::(!cache); th);;

let BITS_INTERLEAVE_CONV tm =
  match tm with
    Comb(Comb(Const("word_interleave",_),e),xl)
      when is_numeral e && is_list xl ->
      let xs = dest_list xl in
      ISPECL xs (BITS_INTERLEAVE_LEMMA (length xs) (dest_small_numeral e)
                  (bits_wsize(type_of(hd xs))))
  | _ -> failwith "BITS_INTERLEAVE_CONV";;

(*** The facts about the memory written by ST2-ST4, in normal form ***)

let BITS_INTERLEAVE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> match t with
              Const("word_interleave",_) -> true | _ -> false)) (concl th)
    then BITS_NORM_RULE(CONV_RULE(ONCE_DEPTH_CONV BITS_INTERLEAVE_CONV) th)
    else th);;
