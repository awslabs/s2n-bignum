(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics shared by the proofs of the pieces of                  *)
(* CompressFragmentDoubleHash (gcc12_O2):                                    *)
(*                                                                           *)
(*  - FML_*: the copies of FindMatchLengthPlain, for the piece fml and the   *)
(*    copy that loop5 reaches (word facts, reads of the input, branches on  *)
(*    data, calls through contracts or the induction hypothesis);           *)
(*  - CF2_BT_*: the backtracking, for the pieces join4 and loop4.            *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_model_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* FindMatchLengthPlain (the pieces fml and loop5): words.                  *)
(* ------------------------------------------------------------------------- *)

let FML_ZX8_EQ = prove
 (`!a b:byte. word_zx a:int32 = word_zx b <=> a = b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
  MP_TAC(ISPEC `a:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN SIMP_TAC[MOD_LT; ARITH_RULE
   `x < 2 EXP 8 ==> x < 2 EXP 32`]);;

let FML_ADDR2 = prove
 (`!(a:int64) p q. word_add (word_add a (word p)) (word q) = word_add a (word(p + q))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let FML_SX_ZX = prove
 (`!k. k < 2 EXP 31 ==> word_sx (word_zx (word k:int64):int32):int64 = word k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k < 2147483648 /\ k < 4294967296 /\ k < 9223372036854775808 /\
                k < 18446744073709551616` STRIP_ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM IVAL_EQ] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_32; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
  MP_TAC(ISPEC `word_zx (word k:int64):int32` IVAL_EQ_VAL) THEN
  MP_TAC(ISPEC `word k:int64` IVAL_EQ_VAL) THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let FML_SUB_EQ = prove
 (`!(x:int64) p q r. q <= p /\ p - q = r
     ==> word_sub (word_add x (word p)) (word_add x (word q)) = word r`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[ADD_SUB2; WORD_ADD] THEN CONV_TAC WORD_RULE);;

let FML_SUB_EQ2 = prove
 (`!(x:int64) p q r. q <= p /\ p - q = r
     ==> word_sub (word_add x (word p)) (word q) = word_add x (word r)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[ADD_SUB2; WORD_ADD] THEN CONV_TAC WORD_RULE);;

let FML_CTZ_ISHR3 = prove
 (`!z. z < 64 ==> word_ishr (word_zx (word z:int64):int32) 3 = word(z DIV 8)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* FindMatchLengthPlain (the pieces fml and loop5): tactics.                *)
(* ------------------------------------------------------------------------- *)

let FML_EXEC = SNAPPY_CF2_GCC12_O2_EXEC;;

(* Rewrite word_sx (word_zx (word k)) to word k, k < 2^31 by the arithmetic. *)

let FML_SXFROM_SMALL = prove
 (`!x. x < 2 EXP 31
       ==> word_sxfrom 31 (word_subword (word x:int64) (0,32):int64):int64 = word x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SXFROM; BIT_WORD_SUBWORD;
              DIMINDEX_64; DIMINDEX_32; ADD_CLAUSES] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BIT_WORD; DIMINDEX_64] THEN
  ASM_CASES_TAC `i < 31` THENL
   [ASM_SIMP_TAC[ARITH_RULE `i < 31 ==> MIN 31 i = i`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC(TAUT `a ==> (a /\ b <=> b)`) THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `~(i < 31) ==> MIN 31 i = 31`] THEN
    SUBGOAL_THEN `x DIV 2 EXP 31 = 0 /\ x DIV 2 EXP i = 0`
     (fun th -> REWRITE_TAC[th; ODD]) THEN
    CONJ_TAC THEN MATCH_MP_TAC DIV_LT THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC LTE_TRANS `2 EXP 31` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC]);;

let FML_SXFROM_GEN = prove
 (`!x:N word. val x < 2 EXP 31
       ==> word_sxfrom 31 (word_subword x (0,32):int64):int64 = word(val x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_subword (x:N word) (0,32):int64 =
                word_subword (word(val x):int64) (0,32)` SUBST1_TAC THENL
   [REWRITE_TAC[word_subword; VAL_WORD; DIMINDEX_64; EXP; DIV_1] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 2 EXP 31 ==> x < 2 EXP 64`];
    ASM_SIMP_TAC[FML_SXFROM_SMALL]]);;

let FML_SX_CONV (asl:(string*thm)list) : conv = fun tm ->
  match tm with
    Comb(Const("word_sx",_),(Comb(Const("word_zx",_),Comb(Const("word",_),k)) as x))
      when type_of tm = `:int64` && type_of x = `:int32` &&
           type_of(rand x) = `:int64` ->
      let lt = mk_binary "<" (k,`2 EXP 31`) in
      let lth = TAC_PROOF((asl,lt), CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC) in
      MP (SPEC k FML_SX_ZX) lth
  | Comb(Comb(Const("word_sxfrom",_),n),Comb(Comb(Const("word_subword",_),x),p))
      when n = `31` && p = `(0,32)` && type_of tm = `:int64` ->
      (match x with
         Comb(Const("word",_),k) when type_of x = `:int64` ->
           let lt = mk_binary "<" (k,`2 EXP 31`) in
           let lth = TAC_PROOF((asl,lt),
             CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC) in
           MP (SPEC k FML_SXFROM_SMALL) lth
       | _ ->
           let lt = mk_binary "<" (mk_icomb(`val:N word->num`,x),`2 EXP 31`) in
           let lth = TAC_PROOF((asl,lt),
             REWRITE_TAC (VAL_WORD_SHL :: CF2_VAL_RULES) THEN
             CONV_TAC NUM_REDUCE_CONV THEN
             REPEAT CF2_MOD_ELIM_TAC THEN CF2_ARITH_TAC) in
           MP (ISPEC x FML_SXFROM_GEN) lth)
  | _ -> failwith "FML_SX_CONV";;

let FML_SX_TAC : tactic = fun (asl,w) ->
  let cnv = DEPTH_CONV (FML_SX_CONV asl) in
  (RULE_ASSUM_TAC(CONV_RULE cnv) THEN CONV_TAC cnv) (asl,w);;

(* A read of the input at the current state: rd with s for the state, whose  *)
(* address is word_add inp (word p) after FML_SX and FML_ADDR2.               *)

let FML_READ_TAC (lemma:thm) (rd:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let tm = subst [s,`s:armstate`] rd in
  let th = TAC_PROOF((asl,tm),
    FML_SX_TAC THEN REWRITE_TAC[FML_ADDR2] THEN
    MATCH_MP_TAC lemma THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; CF2_ARITH_TAC]) in
  ASSUME_TAC th (asl,w);;

let FML_READ64_TAC (addr:term) (p:term) =
  FML_READ_TAC SNAPPY_READ_LOAD64
   (subst [addr,`x:int64`; p,`p:num`]
     `read (memory :> bytes64 x) (s:armstate) = word(snappy_load64 src p)`);;

let FML_READ8_TAC (addr:term) (p:term) =
  FML_READ_TAC SNAPPY_READ_EL
   (subst [addr,`x:int64`; p,`p:num`]
     `read (memory :> bytes8 x) (s:armstate) = EL p (src:byte list)`);;

(* Prove word equalities of addresses and small numbers.                    *)

let FML_WORD_EQ_TAC =
  FML_SX_TAC THEN REWRITE_TAC[FML_ADDR2] THEN
  FIRST
   [REFL_TAC;
    MATCH_MP_TAC FML_SUB_EQ THEN CONJ_TAC THEN CF2_ARITH_TAC;
    MATCH_MP_TAC FML_SUB_EQ2 THEN CONJ_TAC THEN CF2_ARITH_TAC;
    CF2_WORD_EQ_TAC];;

(* Replace the fact read c s = v (s the current state) by read c s = t.      *)

let FML_CANON_TAC (c:string) (t:term) : tactic = fun (asl,w) ->
  let c = parse_term(c ^ ":(armstate,int64)component") in
  let s = rand w in
  let r = list_mk_icomb "read" [c;s] in
  let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = r) asl) in
  if rhs(concl th) = t then ALL_TAC (asl,w) else
  let eq = TAC_PROOF((asl,mk_eq(rhs(concl th),t)),FML_WORD_EQ_TAC) in
  (FIRST_X_ASSUM(fun th' -> if concl th' = concl th then
      ASSUME_TAC(TRANS th' eq) else failwith "")) (asl,w);;

(* A branch on data: prove b <=> cond for the condition b of the PC fact,  *)
(* and split on cond (or, with ~known, decide it by the arithmetic).        *)

let FML_PC_COND (asl,w) =
  let s = rand w in
  let is_pc th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),r)
        -> s' = s && is_cond r
    | _ -> false in
  snd(find (is_pc o snd) asl);;

let FML_BYTE_EQ_TAC = REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; FML_ZX8_EQ] THEN
  TRY(MESON_TAC[]);;

let FML_BRANCH_TAC ?(tac=CF2_COND_EQ_TAC []) (cond:term) : tactic = fun (asl,w) ->
  let pcth = FML_PC_COND (asl,w) in
  let b,_ = dest_cond(rhs(concl pcth)) in
  let eqth = try TAC_PROOF((asl,mk_iff(b,cond)),tac)
             with Failure _ -> TAC_PROOF((asl,mk_iff(b,mk_neg cond)),tac) in
  (ASM_CASES_TAC cond THEN
   FIRST_X_ASSUM(fun cth ->
     FIRST_X_ASSUM(fun th -> if concl th = concl pcth then
        ASSUME_TAC(REWRITE_RULE[eqth; cth] th) else failwith "") THEN
     ASSUME_TAC cth)) (asl,w);;

let FML_KNOWN_BRANCH_TAC ?(tac=CF2_COND_EQ_TAC []) (cond:term) : tactic =
  fun (asl,w) ->
  let pcth = FML_PC_COND (asl,w) in
  let b,_ = dest_cond(rhs(concl pcth)) in
  let eqth = TAC_PROOF((asl,mk_iff(b,cond)),tac) in
  let vth = try EQT_INTRO(TAC_PROOF((asl,cond),CF2_ARITH_TAC))
            with Failure _ -> EQF_INTRO(TAC_PROOF((asl,mk_neg cond),CF2_ARITH_TAC)) in
  (FIRST_X_ASSUM(fun th -> if concl th = concl pcth then
      ASSUME_TAC(REWRITE_RULE[eqth; vth] th) else failwith "")) (asl,w);;

(* Go through th (|- !vars. hyps ==> ensures ..., or an assumption of that  *)
(* form), its variables given by name in inst (the others as they are, the  *)
(* events variable e as the current events), the hypotheses proved by the   *)
(* assumptions or the arithmetic.                                            *)

let FML_NORM_RULES = [LEFT_ADD_DISTRIB; MULT_CLAUSES; ADD_CLAUSES; GSYM ADD_ASSOC];;

let FML_HYP_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; CF2_ARITH_TAC;
         REWRITE_TAC FML_NORM_RULES THEN CF2_ARITH_TAC;
         REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC];;

let FML_CALL_TAC (th:thm) (inst:(term*string)list) sname : tactic =
  fun (asl,w) ->
  let s = rand w in
  let evth = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("events",_)),s')),_)
        -> s' = s | _ -> false) asl) in
  let ev = rhs(concl evth) in
  let base n = let l = String.length n in
    let rec go i = if i > 0 && n.[i-1] = '\'' then go (i-1) else i in
    String.sub n 0 (go l) in
  let rec go th =
    let c = concl th in
    if is_forall c then
      let v = fst(dest_forall c) in
      let n,ty = dest_var v in
      let n = base n in
      let t = if n = "e" then ev else
              try fst(find (fun (_,m) -> m = n) inst)
              with Failure _ -> mk_var(n,ty) in
      go (SPEC t th)
    else if is_imp c then
      let th = REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES] th in
      if is_imp(concl th) then
        let h = lhand(concl th) in
        go (MP th (TAC_PROOF((asl,h),FML_HYP_TAC)))
      else go th
    else th in
  ARM_BSTEP_CALL_TAC FML_EXEC (go th) sname (asl,w);;

let FML_IH_TAC (inst:(term*string)list) sname : tactic =
  FIRST_ASSUM(fun ih ->
    if is_forall(concl ih) &&
       can (find_term (fun t -> match t with Const("ensures",_) -> true
                                           | _ -> false)) (concl ih)
    then FML_CALL_TAC ih inst sname else failwith "FML_IH_TAC");;

(* WF induction on the measure m with the events variable e also           *)
(* generalized in the hypothesis.                                            *)

let FML_INDUCT_TAC (m:term) =
  REPEAT GEN_TAC THEN SPEC_TAC(`e:(uarch_event)list`,`e:(uarch_event)list`) THEN
  WF_INDUCT_TAC m THEN GEN_TAC;;

(* The end: the conjuncts of the postcondition.                              *)

let FML_FIN_TAC =
  BSTEP_FINAL_TAC THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(FML_SX_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[FML_ADDR2]) THEN
      MEMSAFE_EVENTS_TAC THEN NO_TAC);;

(* The value of the register c (fact read c s = v) is word t.               *)

let FML_REG_TAC =
  W(fun (asl,w) ->
    let l,r = dest_eq w in
    let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = l) asl) in
    GEN_REWRITE_TAC LAND_CONV [th] THEN FML_WORD_EQ_TAC);;

(* An instance of a lemma |- hyps ==> concl as an assumption, the sums in  *)
(* it right-associated, the hypotheses proved by FML_HYP_TAC.               *)

let FML_FACT_TAC (th:thm) (args:term list) =
  MP_TAC(ISPECL args th) THEN
  ANTS_TAC THENL [FML_HYP_TAC;
                  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[GSYM ADD_ASSOC])];;

(* ------------------------------------------------------------------------- *)
(* The backtracking (the pieces join4 and loop4).                           *)
(* ------------------------------------------------------------------------- *)

let CF2_BT_STEP7 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     snappy_cf2_step src (SnappyCState 7 ip ne sk c x t1 t2 out) =
     if ne < ip /\ 0 < c /\ EL (ip - 1) src = EL (c - 1) src
     then SnappyCState 7 (ip - 1) ne sk (c - 1) (x + 1) t1 t2 out
     else SnappyCState 3 ip ne sk c x t1 t2 out`,
  REPEAT GEN_TAC THEN SNAPPY_CF2_UNFOLD_TAC THEN REWRITE_TAC[]);;

let CF2_BT_PRED = prove
 (`!k. 1 <= k ==> word(k + 18446744073709551615):int64 = word(k - 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `k + 18446744073709551615 = (k - 1) + 1 * 2 EXP 64`
   SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]]);;

let CF2_BT_SUB1 = prove
 (`!(a:int64) k. 1 <= k
     ==> word_sub (word_add a (word k)) (word 1) = word_add a (word(k - 1)) /\
         word_add a (word(k + 18446744073709551615)) =
         word_add a (word(k - 1)) /\
         word_add (word_add a (word k)) (word 18446744073709551615) =
         word_add a (word(k - 1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[ARITH_RULE `(1 + d) - 1 = d`] THEN
  SUBGOAL_THEN `word(d + 18446744073709551616):int64 = word d` ASSUME_TAC
  THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `d + 18446744073709551616 = d + 1 * 18446744073709551616`];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE
   `(1 + d) + 18446744073709551615 = d + 18446744073709551616`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC] THEN CONV_TAC WORD_RULE;
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    ASM_REWRITE_TAC[ARITH_RULE
     `(1 + d) + 18446744073709551615 = d + 18446744073709551616`]]);;

let CF2_BT_CARRY = prove
 (`!a b:int64. &(val a) - &(val b):int = &(val(word_sub a b)) <=>
               val b <= val a`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[INT_ARITH `x - y:int = z <=> x = y + z`; INT_OF_NUM_ADD;
              INT_OF_NUM_EQ; VAL_WORD_SUB_CASES] THEN
  MP_TAC(ISPEC `a:int64` VAL_BOUND) THEN MP_TAC(ISPEC `b:int64` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let CF2_BT_ZX8 = prove
 (`!a b:byte. word_zx a:int32 = word_zx b <=> a = b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
  MP_TAC(ISPEC `a:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN SIMP_TAC[MOD_LT; ARITH_RULE
   `x < 2 EXP 8 ==> x < 2 EXP 32`]);;

(* val (word_add inp (word k)) = val inp + k inside the input.             *)

let CF2_BT_VAL_TAC (ks:term list) : tactic = fun (asl,w) ->
  let one k = TAC_PROOF((asl,
      mk_eq(mk_comb(`val:int64->num`,mk_comb(mk_comb(`word_add:int64->int64->int64`,
            `inp:int64`),mk_comb(`word:num->int64`,k))),
            mk_binary "+" (`val(inp:int64)`,k))),
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CF2_MOD_ELIM_TAC THEN REFL_TAC) in
  REWRITE_TAC(map one ks) (asl,w);;

(* The byte read (memory :> bytes8 (word_add inp (word(k + 2^64 - 1)))) at   *)
(* the current state, from the input region, as EL (k - 1) src.             *)

let CF2_BT_BYTE_TAC (k:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let tm = subst [k,`k:num`; s,`s:armstate`]
   `read (memory :> bytes8 (word_add inp (word(k + 18446744073709551615)))) s =
    EL (k - 1) (src:byte list)` in
  let th = TAC_PROOF((asl,tm),
    SUBGOAL_THEN (mk_binary "<=" (`1`,k)) ASSUME_TAC THENL
     [CF2_ARITH_TAC;
      ASM_SIMP_TAC[CF2_BT_PRED] THEN MATCH_MP_TAC SNAPPY_READ_EL THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; CF2_ARITH_TAC]]) in
  ASSUME_TAC (INST [k,`k:num`] th) (asl,w);;

(* Replace the fact read c s = v by read c s = t, with v = t proved.         *)

let CF2_BT_CANON_TAC (c:term) (t:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let r = list_mk_icomb "read" [c;s] in
  let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = r) asl) in
  let eq = TAC_PROOF((asl,mk_eq(rhs(concl th),t)),
    FIRST
     [MP_TAC(SPECL [`inp:int64`; lhand(rand(rand t))] CF2_BT_SUB1) THEN
      ANTS_TAC THENL [CF2_ARITH_TAC; SIMP_TAC[]] THEN NO_TAC;
      CF2_WORD_EQ_TAC]) in
  (FIRST_X_ASSUM(fun th' -> if concl th' = concl th then
      ASSUME_TAC(TRANS th' eq) else failwith "")) (asl,w);;

(* A branch on data: the PC fact read PC s = if b then .. else ..; prove     *)
(* b <=> cond with tac and split on cond.                                    *)

let CF2_BT_BRANCH_TAC (tac:tactic) (cond:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let is_pc th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),r)
        -> s' = s && is_cond r
    | _ -> false in
  let pcth = snd(find (is_pc o snd) asl) in
  let b,_ = dest_cond(rhs(concl pcth)) in
  let eqth = TAC_PROOF((asl,mk_iff(b,cond)),tac) in
  (ASM_CASES_TAC cond THEN
   FIRST_X_ASSUM(fun cth ->
     FIRST_X_ASSUM(fun th -> if concl th = concl pcth then
        ASSUME_TAC(REWRITE_RULE[eqth; cth] th) else failwith "") THEN
     ASSUME_TAC cth)) (asl,w);;

let CF2_BT_BYTE_EQ_TAC =
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; CF2_BT_ZX8];;

let CF2_BT_CARRY_EQ_TAC ks =
  REWRITE_TAC[CF2_BT_CARRY] THEN CF2_BT_VAL_TAC ks THEN
  REPEAT COND_CASES_TAC THEN CF2_ARITH_TAC;;

(* A step of the backtracking in the model: snappy_cf2_step src X = Y.       *)

let CF2_BT_MODEL_TAC =
  REWRITE_TAC[CF2_BT_STEP7] THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  ASM_REWRITE_TAC[SNAPPY_CSTATE_INJ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[];;

let CF2_BT_REACH_TAC (mids:term list) : tactic = fun (asl,w) ->
  let r0 = snd(find (fun (_,th) ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "snappy_cf2_reach"
      with Failure _ -> false) asl) in
  let x0 = rand(concl r0) in
  let rec tac prevs = match prevs with
      [] -> ACCEPT_TAC r0
    | p::rest ->
        MATCH_MP_TAC SNAPPY_CF2_REACH_STEP_EQ THEN EXISTS_TAC p THEN
        CONJ_TAC THENL [tac rest; CF2_BT_MODEL_TAC] in
  tac (rev (x0 :: mids)) (asl,w);;

(* The events: the byte loads at ip - 1 and c - 1 in the form of the input,  *)
(* then MEMSAFE_EVENTS_TAC.                                                  *)

let CF2_BT_EVENTS_TAC : tactic = fun (asl,w) ->
  let sub k =
    let th = TAC_PROOF((asl,mk_binary "<=" (`1`,k)),CF2_ARITH_TAC) in
    CONJUNCT2(CONJUNCT2(MP (SPECL [`inp:int64`; k] CF2_BT_SUB1) th)) in
  let ths = mapfilter sub [`ip:num`; `c:num`] in
  (REWRITE_TAC[snappy_cf2_events] THEN
   RULE_ASSUM_TAC(fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("events",_)),_)),_)
         -> REWRITE_RULE ths th
     | _ -> th) THEN
   MEMSAFE_EVENTS_TAC) (asl,w);;

(* ASM_REWRITE_TAC without the definition of ts (which would change the     *)
(* regions of the events).                                                   *)

let CF2_BT_ASM_REWRITE_TAC : tactic = fun (asl,w) ->
  let ok (_,th) = match concl th with
      Comb(Comb(Const("=",_),Var("ts",_)),_) -> false
    | _ -> true in
  REWRITE_TAC (map snd (filter ok asl)) (asl,w);;

let CF2_BT_TARGET_TAC (pt:term) (st:term) (mids:term list) =
  MAP_EVERY EXISTS_TAC [pt; st] THEN
  REPEAT CONJ_TAC THENL
   [CF2_BT_REACH_TAC mids;
    REWRITE_TAC[snappy_cf2_pot] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CF2_ARITH_TAC;
    REWRITE_TAC[snappy_cf2_point] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[snappy_cf2_at; snappy_cf2_regs; snappy_phase; snappy_ip;
                snappy_ne; snappy_skip; snappy_cand; snappy_aux; snappy_t1;
                snappy_t2; snappy_out] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN CF2_BT_ASM_REWRITE_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(CF2_BT_EVENTS_TAC THEN NO_TAC) THEN
    TRY CF2_ARITH_TAC THEN TRY CF2_WORD_EQ_TAC];;

(* The body from loop4 (the bound ne < ip /\ 0 < c known), from step k.      *)

let CF2_BT_BODY_TAC execth k =
  CF2_BT_BYTE_TAC `ip:num` THEN CF2_BT_BYTE_TAC `c:num` THEN
  ARM_BSTEP_TAC execth (k--(k+3)) THEN
  CF2_BT_BRANCH_TAC CF2_BT_BYTE_EQ_TAC
   `EL (ip - 1) (src:byte list) = EL (c - 1) src` THENL
   [ARM_BSTEP_TAC execth ((k+4)--(k+5)) THEN
    CF2_BT_CANON_TAC `X8:(armstate,int64)component` `word_add (inp:int64) (word(ip - 1))` THEN
    CF2_BT_CANON_TAC `X14:(armstate,int64)component` `word_add (inp:int64) (word(c - 1))` THEN
    ARM_BSTEP_TAC execth ((k+6)--(k+9)) THEN
    CF2_BT_BRANCH_TAC (CF2_BT_CARRY_EQ_TAC [`ne:num`; `ip - 1`; `c - 1`])
     `~(ne < ip - 1 /\ 0 < c - 1)` THENL
     [BSTEP_FINAL_TAC THEN
      CF2_BT_TARGET_TAC `CompressFragmentDoubleHash_join5:num`
       `SnappyCState 3 (ip - 1) ne sk (c - 1) (x + 1) t1 t2 out`
       [`SnappyCState 7 (ip - 1) ne sk (c - 1) (x + 1) t1 t2 out`];
      BSTEP_FINAL_TAC THEN
      CF2_BT_TARGET_TAC `CompressFragmentDoubleHash_loop4:num`
       `SnappyCState 7 (ip - 1) ne sk (c - 1) (x + 1) t1 t2 out` []];
    BSTEP_FINAL_TAC THEN
    CF2_BT_TARGET_TAC `CompressFragmentDoubleHash_join5:num`
     `SnappyCState 3 ip ne sk c x t1 t2 out` []];;
