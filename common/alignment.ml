(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ------------------------------------------------------------------------- *)
(* Additional proof support for "aligned w" subgoals (w = 16, 32 etc.).      *)
(* ------------------------------------------------------------------------- *)

let NORMALIZE_ALIGNED_WORD_CONV =
  let pth = prove
   (`(!n x:int64.
      w divides n ==> (aligned w (word_add x (word n)) <=> aligned w x)) /\
     (!n x:int64.
      w divides n ==> (aligned w (word_add (word n) x) <=> aligned w x)) /\
     (!n x:int64.
      w divides n ==> (aligned w (word_sub x (word n)) <=> aligned w x)) /\
     (!n x:int64.
      w divides n ==> (aligned w (word_sub (word n) x) <=> aligned w x))`,
    MESON_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD_SUB_EQ; ALIGNED_WORD;
             aligned]) in
  let funs = map (PART_MATCH (lhs o rand)) (CONJUNCTS pth) in
  let conv tm =
    try let th = tryfind (fun f -> f tm) funs in
        MP th (EQT_ELIM(DIVIDES_CONV(lhand(concl th))))
    with Failure _ -> failwith "" in
  fun tm ->
    match tm with
      Comb(Comb(Const("aligned",_),w),x) when is_numeral w -> REPEATC conv tm
     | _ -> failwith "NORMALIZE_ALIGNED_WORD_CONV";;

let rec SUB_ALIGNED_WORD_CONV conv tm =
  match tm with
  | Comb(Comb(Const("aligned",_),w),_) when is_numeral w -> RAND_CONV conv tm
  | Comb(l,r) -> COMB_CONV (SUB_ALIGNED_WORD_CONV conv) tm
  | Abs(x,bod) -> ABS_CONV (SUB_ALIGNED_WORD_CONV conv) tm
  | _ -> REFL tm;;

let (ALIGNED_WORD_TAC:tactic) =
  let basetac =
    CONV_TAC
     (SUB_ALIGNED_WORD_CONV(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV)) THEN
    ASM (GEN_REWRITE_TAC
      (LAND_CONV o SUB_ALIGNED_WORD_CONV o TOP_DEPTH_CONV)) [] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
    ASSUM_LIST(fun thl ->
      REWRITE_TAC(mapfilter (CONV_RULE NORMALIZE_ALIGNED_WORD_CONV) thl))
  and trigger = vfree_in `aligned:num->int64->bool` in
  fun (asl,w) -> if trigger w then basetac (asl,w) else ALL_TAC (asl,w);;

let ALIGNED_WORD_CONV ths =
  let baseconv =
    SUB_ALIGNED_WORD_CONV(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THENC
    GEN_REWRITE_CONV (SUB_ALIGNED_WORD_CONV o TOP_DEPTH_CONV) ths THENC
    ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV THENC
    REWRITE_CONV(mapfilter (CONV_RULE NORMALIZE_ALIGNED_WORD_CONV) ths)
  and trigger = vfree_in `aligned:num->int64->bool` in
  fun tm -> if trigger tm then baseconv tm else REFL tm;;
