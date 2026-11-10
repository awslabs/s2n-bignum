(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the loops of mldsa-native's x86-64 code that      *)
(* compute one coefficient per iteration, possibly with data-dependent       *)
(* branches, as arm/proofs/utils/mldsa_native_scalar.ml has for AArch64, and *)
(* for the vectorized loops that use vectors of constants from the           *)
(* read-only data of the image.                                              *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_poly.ml";;

(* ------------------------------------------------------------------------- *)
(* Constants in the image. IMAGE_CONST_RULE_FOR image_mc d k gives           *)
(*                                                                           *)
(* |- !s pc. bytes_loaded s (word pc) <image>                                *)
(*           ==> read (memory :> bytes<k> (word(pc + d))) s = word v         *)
(*                                                                           *)
(* for the k-bit value v (k = 8, 16, 32, 64 or 128) at address d in the      *)
(* image, as MLKEM_NATIVE_IMAGE_CONST_RULE_FOR does for AArch64.             *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_WBYTES_BYTES_LOADED = prove
 (`!(a:int64) (l:byte list) s:x86state.
        bytes_loaded s a l /\ LENGTH l = dimindex(:N) DIV 8
        ==> read (memory :> wbytes a) s:N word = word(num_of_bytelist l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bytes_loaded] THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]);;

let IMAGE_CONST_RULE_FOR image_mc =
  let rec take n l =
    if n = 0 then [] else
    match l with h::t -> h::take (n - 1) t | [] -> failwith "take" in
  let rec drop n l =
    if n = 0 then l else
    match l with _::t -> drop (n - 1) t | [] -> failwith "drop" in
  let imagel = dest_list(rhs(concl image_mc)) in
  let wbths = [8,BYTES8_WBYTES; 16,BYTES16_WBYTES; 32,BYTES32_WBYTES;
               64,BYTES64_WBYTES; 128,BYTES128_WBYTES] in
  let bl_tm = mk_comb(`bytes_loaded (s:x86state) (word pc)`,
                      lhs(concl image_mc)) in
  fun d k ->
    let l = mk_list(take (k / 8) (drop d imagel),`:byte`) in
    let th1 = UNDISCH(SPEC_ALL(BYTES_LOADED_SUBPROGRAM_RULE
                image_mc (REFL l) d)) in
    let a = rand(rator(concl th1)) in
    let lth = ISPECL [a; l; `s:x86state`]
               (INST_TYPE [mk_finty(Num.num_of_int k),`:N`]
                          READ_MEMORY_WBYTES_BYTES_LOADED) in
    let lenth = prove(rand(lhand(concl lth)),
      REWRITE_TAC[LENGTH] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV) in
    let th2 = MP lth (CONJ th1 lenth) in
    let th3 = CONV_RULE(RAND_CONV(RAND_CONV
      (REWRITE_CONV[num_of_bytelist] THENC DEPTH_CONV WORD_RED_CONV THENC
       NUM_REDUCE_CONV))) th2 in
    let th4 = REWRITE_RULE[GSYM(assoc k wbths)] th3 in
    GENL [`s:x86state`; `pc:num`] (DISCH bl_tm th4);;

(* ------------------------------------------------------------------------- *)
(* The simulation gives the address of a RIP-relative memory operand as      *)
(* word(val(word(pc + r)) + k), where pc + r is the address of the next      *)
(* instruction and k the displacement, and for an aligned SSE instruction it *)
(* needs the alignment of that address to decide the alignment check.        *)
(* IMAGE_RIPREL_TAC th r, before the simulation of the instruction that ends *)
(* at pc + r and loads the constant of th (from IMAGE_CONST_RULE_FOR, at     *)
(* pc + d), adds to the assumptions the value of the constant and the        *)
(* alignment to 16 of its address in that form, with k = d - r, given the    *)
(* loaded image and its alignment there.                                     *)
(* ------------------------------------------------------------------------- *)

let RIPREL_ADDR_LEMMA = prove
 (`!n k. word(val(word n:int64) + k):int64 = word(n + k)`,
  REWRITE_TAC[WORD_EQ; DIMINDEX_64; VAL_WORD; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let IMAGE_RIPREL_TAC =
  let word_tm = `word:num->int64`
  and val_tm = `val:int64->num`
  and plus_tm = `(+):num->num->num`
  and aligned_tm = `aligned:num->int64->bool` in
  fun th r ->
    FIRST_ASSUM(fun bth ->
      let cth = MATCH_MP th bth in
      let l = lhs(concl cth) in
      let wad = rand(rand(rand(rator l))) in
      let p,dt = dest_binop plus_tm (rand wad) in
      let d = dest_small_numeral dt in
      let rt = mk_small_numeral r and kt = mk_small_numeral(d - r) in
      let addr = mk_comb(word_tm,
        mk_binop plus_tm
         (mk_comb(val_tm,mk_comb(word_tm,mk_binop plus_tm p rt))) kt) in
      let eqth = CONV_RULE(RAND_CONV(RAND_CONV NUM_REDUCE_CONV))
        (REWRITE_CONV[RIPREL_ADDR_LEMMA; GSYM ADD_ASSOC] addr) in
      let ath = mk_comb(mk_comb(aligned_tm,`16`),addr) in
      ASSUME_TAC(REWRITE_RULE[SYM eqth] cth) THEN
      SUBGOAL_THEN ath ASSUME_TAC THENL
       [REWRITE_TAC[eqth] THEN ALIGNED_WORD_EXTENDED_TAC; ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A fact about an XMM register, the bottom half of the YMM register that    *)
(* the simulation of the legacy SSE instructions uses, as a fact about the   *)
(* YMM register with an unknown top half, as in the x86 proofs of            *)
(* mlkem-native (mlkem_rej_uniform_VARIABLE_TIME.ml), e.g. for a vector of   *)
(* constants in a loop invariant.                                            *)
(* ------------------------------------------------------------------------- *)

let XMM_EXISTSTOP = prove
 (`!c s:S. read (c :> zerotop_128) s = l
           ==> ?h. read c s = (word_join:int128->int128->int256) h l`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `word_subword (read c (s:S):int256) (128,128):int128` THEN
  REWRITE_TAC[READ_ZEROTOP_128] THEN CONV_TAC WORD_BLAST);;

let XMM_EXISTSTOP_RULE =
  REWRITE_RULE (map GSYM
   [XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7;
    XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15]) o
  C ISPEC XMM_EXISTSTOP;;

let XMM_EXISTSTOP_TAC top y =
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (XMM_EXISTSTOP_RULE y)) THEN
  DISCH_THEN(X_CHOOSE_TAC(mk_var(top,`:int128`)));;

(* ------------------------------------------------------------------------- *)
(* For a load or store of a 32-bit coefficient at base + index, the address  *)
(* is computed as word_add a (word(1 * n)) when the index register is word n *)
(* (and val(word n) = n is in the assumptions, from VAL_INT64_TAC), so       *)
(* INDEX4_ADDR_TAC restates the assumptions about the coefficients at        *)
(* word_add a (word(4 * i)) in that form, as INDEX_ADDR_TAC of               *)
(* utils/mldsa_native.ml does for the 128-bit words at word_add a            *)
(* (word(16 * i)).                                                           *)
(* ------------------------------------------------------------------------- *)

let INDEX4_ADDR_TAC =
  let pth = ARITH_RULE `4 * i = 1 * 4 * i` in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (term_match []
          `read (memory :> bytes32 (word_add a (word(4 * i)))) s = v`) c
    then ONCE_REWRITE_RULE[pth] th else th);;

(* ------------------------------------------------------------------------- *)
(* 32-bit values that the compiled code computes in 64-bit registers, as in  *)
(* utils/mldsa_native.ml: a 32-bit value sign-extended (MOVSXD, CDQE) and    *)
(* read back as 32 bits, the mask of the sign of a 32-bit value z, computed  *)
(* by sign-extending it and shifting right by 31 (as mld_ct_cmask_neg_i32    *)
(* does), and the 32-bit sums that LEA computes in 64 bits and truncates, as *)
(* the simulation gives them.                                                *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_SX_32_64_32 = prove
 (`!x:int32. word_zx(word_sx x:int64):int32 = x`,
  BITBLAST_TAC);;

let WORD_ZX_ISHR_SX_31 = prove
 (`!x:int32. word_zx(word_ishr (word_sx x:int64) 31):int32 = word_ishr x 31`,
  BITBLAST_TAC);;

let WORD_SX_NARROW_64_32 = prove
 (`!x:int64. word_sx x:int32 = word_zx x`,
  BITBLAST_TAC);;

let WORD_ZX_NARROW_ADD_64_32 = prove
 (`!x y:int64. word_zx(word_add x y):int32 = word_add (word_zx x) (word_zx y)`,
  BITBLAST_TAC);;

(*** The carry flag of a 32-bit SUB of 1 (for CMOVB), as the simulation  ***)
(*** gives it: no borrow unless the value is zero                       ***)

let WORD_SUB_1_BORROW_32 = prove
 (`!w:int32. (&(val w) - &1:int = &(val(word_sub w (word 1)))) <=>
             ~(w = word 0)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_SUB_CASES; VAL_WORD;
                           DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THENL
   [UNDISCH_TAC `1 <= val(w:int32)` THEN ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
    UNDISCH_TAC `~(1 <= val(w:int32))` THEN
    REWRITE_TAC[NOT_LE; ARITH_RULE `n < 1 <=> n = 0`] THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC INT_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* The mask of ct.h as a shift, for bit-blasting.                            *)
(* ------------------------------------------------------------------------- *)

let MLD_CT_CMASK_NEG_ISHR = prove
 (`!x:int32. mld_ct_cmask_neg x = word_ishr x 31`,
  REWRITE_TAC[mld_ct_cmask_neg; WORD_ISHR_31_COND]);;

(* ------------------------------------------------------------------------- *)
(* An equation between a value computed by the code and its specification,   *)
(* both functions of an input word (possibly under hypotheses), by           *)
(* bit-blasting, as in arm/proofs/utils/mldsa_native_scalar.ml. Bit-blasting *)
(* a 32-bit product, or a sum of two unrelated 32-bit values, is slow, so    *)
(* the largest word subterm that occurs on both sides is first generalized   *)
(* to a variable, repeatedly, and then any remaining application of an mld_  *)
(* function. This needs the defs to unfold the specification into the form   *)
(* of the code, with a product or sum computed in the same way on both       *)
(* sides; it is sound in any case, as an instance of a stronger claim, but   *)
(* may then fail. The 32-bit values computed in 64-bit registers are first   *)
(* put in their 32-bit forms with the lemmas above, with the sums            *)
(* associated to the left.                                                   *)
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

let LANE_BLAST_TAC (defs:thm list) =
  REWRITE_TAC(MLD_CT_CMASK_NEG_ISHR::defs) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_SX_NARROW_64_32; WORD_ZX_NARROW_ADD_64_32;
              WORD_ZX_ZX_32_64_32; WORD_ZX_SX_32_64_32; WORD_ZX_ISHR_SX_31;
              WORD_SUB_1_BORROW_32;
              ADD_CLAUSES; MULT_CLAUSES; WORD_ADD; WORD_VAL; WORD_ADD_ASSOC;
              VAL_EQ_0; WORD_SUB_0; INT_SUB_RZERO; IVAL_POS_32;
              GSYM MSB_IVAL; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
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
(* as RAX) computed from the input v by word_zx (f v), proving the equation  *)
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
(* The same for a register reg written by a 32-bit operation, with the value *)
(* word_zx t for a 32-bit t computed from v: REG32_LANE_TAC proves t = f v   *)
(* and rewrites all the assumptions with it, so that also the flags set by   *)
(* the operation, and a branch on them, are in terms of f v.                 *)
(* ------------------------------------------------------------------------- *)

let REG32_LANE_TAC (reg:term) (v:term) (f:term) (defs:thm list) =
  let zx_tm = `word_zx:int32->int64` in
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if (try rand(rator l) = reg with Failure _ -> false) &&
       is_comb r && rator r = zx_tm && free_in v r then
      let t = rand r and y = genvar(type_of v) in
      let lemma = prove
       (mk_forall(y,mk_eq(subst[y,v] t,mk_comb(f,y))),
        GEN_TAC THEN LANE_BLAST_TAC defs) in
      ASSUME_TAC th THEN RULE_ASSUM_TAC(REWRITE_RULE[lemma])
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Split the goal on the condition of a conditional branch whose target the  *)
(* simulation could not decide, read RIP s = if c then .. else .., so that   *)
(* the simulation can go on in each case.                                    *)
(* ------------------------------------------------------------------------- *)

let BRANCH_CASES_TAC =
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if not(is_cond r) || not(can (term_match [] `read RIP s`) l)
    then failwith "BRANCH_CASES_TAC" else
    let c = lhand(rator r) in
    ASM_CASES_TAC c THENL
     [ASSUME_TAC(REWRITE_RULE[ASSUME c] th);
      ASSUME_TAC(REWRITE_RULE[ASSUME(mk_neg c)] th)]);;
