(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the top-level functions of mldsa-native: bytes of memory as    *)
(* lists of bytes and as 128-bit chunks, and the folds of the constant-time  *)
(* comparison mld_ct_memcmp (ct.h), which the code vectorizes 16 bytes at a  *)
(* time, accumulating the OR and the XOR of the differences; and the proof   *)
(* of the FULL theorems for mld_sign_pk_from_sk (PFS_FULL_TAC).              *)
(* ========================================================================= *)

needs "common/layout.ml";;
needs "common/mlkem_mldsa.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/fips204/properties/mldsa_native_full.ml";;
needs "common/fips204/properties/mldsa_native_matrix.ml";;
needs "common/fips203/properties/mlkem_native_image.ml";;

let mld_chunk128 = new_definition
 `mld_chunk128 (f:num->byte) i =
    word(num_of_bytelist(list_of_seq (\k. f(16 * i + k)) 16)):int128`;;

let mld_or_fold = define
 `(mld_or_fold (a:num->int128) b 0 = word 0) /\
  (mld_or_fold a b (SUC i) =
     word_or (mld_or_fold a b i) (word_xor (a i) (b i)))`;;

let mld_xor_fold = define
 `(mld_xor_fold (a:num->int128) b 0 = word 0) /\
  (mld_xor_fold a b (SUC i) =
     word_xor (mld_xor_fold a b i) (word_xor (a i) (b i)))`;;

let MLD_OR_FOLD_EQ_0 = prove
 (`!(a:num->int128) b n.
        mld_or_fold a b n = word 0 <=> !i. i < n ==> a i = b i`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[mld_or_fold; LT] THEN
  REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

let WORD_NUM_OF_BYTELIST_16_EQ = prove
 (`!l1 l2:byte list.
        LENGTH l1 = 16 /\ LENGTH l2 = 16
        ==> ((word(num_of_bytelist l1):int128) = word(num_of_bytelist l2) <=>
             l1 = l2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  MP_TAC(ISPEC `l1:byte list` NUM_OF_BYTELIST_BOUND) THEN
  MP_TAC(ISPEC `l2:byte list` NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN
  DISCH_THEN(MP_TAC o AP_TERM `bytelist_of_num 16`) THEN
  ASM_MESON_TAC[BYTELIST_OF_NUM_OF_BYTELIST]);;

let MLD_CHUNK128_EQ = prove
 (`!(f:num->byte) g n.
        (!i. i < n ==> mld_chunk128 f i = mld_chunk128 g i) <=>
        (!j. j < 16 * n ==> f j = g j)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[mld_chunk128; WORD_NUM_OF_BYTELIST_16_EQ; LENGTH_LIST_OF_SEQ] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j DIV 16`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `EL (j MOD 16):byte list->byte`) THEN
    SIMP_TAC[EL_LIST_OF_SEQ; MOD_LT_EQ; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `16 * j DIV 16 + j MOD 16 = j`];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let LIST_OF_SEQ_ADD_GEN = prove
 (`!(f:num->A) m n.
        list_of_seq f (m + n) =
        APPEND (list_of_seq f m) (list_of_seq (\k. f(m + k)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_NIL; APPEND_ASSOC]);;

let VAL_MLD_CHUNK128 = prove
 (`!(f:num->byte) i.
        val(mld_chunk128 f i) =
        num_of_bytelist(list_of_seq (\k. f(16 * i + k)) 16)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_chunk128; VAL_WORD; DIMINDEX_128] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `list_of_seq (\k. (f:num->byte)(16 * i + k)) 16`
         NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let WORD_ZX_ZX_ZX_32 = prove
 (`!x:int32. word_zx(word_zx(word_zx x:int64):int32):int64 = word_zx x`,
  CONV_TAC WORD_BLAST);;

let PFS_DIVMOD_LEMMA = prove
 (`!B x y u v. x < B /\ y < B /\ x + B * u = y + B * v ==> x = y /\ u = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x + B * u) MOD B = (y + B * v) MOD B /\
                (x + B * u) DIV B = (y + B * v) DIV B` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(B = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* More of the same: the folds one step further, the comparison as a         *)
(* predicate, 64 bytes as four chunks, the 32 bytes of two chunks, and two   *)
(* byte strings one after the other.                                         *)
(* ------------------------------------------------------------------------- *)

let MLD_OR_FOLD_ADD1 = prove
 (`!(a:num->int128) b i.
        mld_or_fold a b (i + 1) =
        word_or (mld_or_fold a b i) (word_xor (a i) (b i))`,
  REWRITE_TAC[GSYM ADD1; mld_or_fold]);;

let MLD_XOR_FOLD_ADD1 = prove
 (`!(a:num->int128) b i.
        mld_xor_fold a b (i + 1) =
        word_xor (mld_xor_fold a b i) (word_xor (a i) (b i))`,
  REWRITE_TAC[GSYM ADD1; mld_xor_fold]);;

let MLD_CT_MEMCMP_EQ_0 = prove
 (`!(a:num->byte) b n.
        mld_ct_memcmp a b n = word 0 <=> !i. i < n ==> a i = b i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_ct_memcmp] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let MLD_CHUNKS4_EQ = prove
 (`!(f:num->byte) g.
        (!j. j < 64 ==> f(64 + j) = g j) <=>
        mld_chunk128 f 4 = mld_chunk128 g 0 /\
        mld_chunk128 f 5 = mld_chunk128 g 1 /\
        mld_chunk128 f 6 = mld_chunk128 g 2 /\
        mld_chunk128 f 7 = mld_chunk128 g 3`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\j. (f:num->byte)(64 + j)`; `g:num->byte`; `4`]
                MLD_CHUNK128_EQ) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN BETA_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  SUBGOAL_THEN `!i. mld_chunk128 (\j. (f:num->byte)(64 + j)) i =
                    mld_chunk128 f (4 + i)` (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[mld_chunk128] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    CONV_TAC NUM_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* The result of mld_ct_memcmp as the code computes it from the OR fold vor  *)
(* and the XOR fold vxor of the differences: PFS_CMP_RULE vor vxor th turns  *)
(* th, |- l = e with e the value the simulation gives, into                  *)
(* |- l = if vor = word 0 then word 0 else word 255. The OR-reduced and      *)
(* XOR-reduced bytes of e are generalized, so that BITBLAST_RULE proves the  *)
(* rest quickly (WORD_BLAST takes far longer on these terms).                *)
(* ------------------------------------------------------------------------- *)

let PFS_SUBWORD8_32 = WORD_BLAST
  `!x:int128. word_subword x (0,8):int32 = word_zx(word_subword x (0,8):byte)`;;

let pfs_is_byte_sub t =
  try fst(dest_const(fst(strip_comb t))) = "word_subword" &&
      rand t = `(0,8)` && type_of t = `:byte`
  with Failure _ -> false;;

let pfs_word ty n =
  mk_comb(mk_const("word",[hd(snd(dest_type ty)),`:N`]),mk_small_numeral n);;

let PFS_CMP_RULE vor vxor th =
  let e = rhs(concl th) in
  let th0 = REWRITE_CONV[PFS_SUBWORD8_32] e in
  let eb = rhs(concl th0) in
  let rb = find_term (fun t -> pfs_is_byte_sub t && free_in vor t) eb
  and sb = find_term (fun t -> pfs_is_byte_sub t && free_in vxor t) eb in
  let rv = genvar `:byte` and qv = genvar `:byte` in
  let er = subst [rv,rb; qv,sb] eb in
  let ty = type_of e in
  let tgt r = mk_cond(mk_eq(r,`word 0:byte`),pfs_word ty 0,pfs_word ty 255) in
  let tha = SPECL [rb; sb]
    (BITBLAST_RULE (list_mk_forall([rv;qv], mk_eq(er, tgt rv)))) in
  let vv = genvar(type_of vor) in
  let thb = SPEC vor (BITBLAST_RULE
    (mk_forall(vv, mk_eq(mk_eq(subst[vv,vor] rb, `word 0:byte`),
                         mk_eq(vv, pfs_word (type_of vor) 0))))) in
  TRANS th (TRANS th0
    (CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV(REWR_CONV thb))) tha));;

(* ------------------------------------------------------------------------- *)
(* Branches decided by the facts: PFS_DECIDE_TAC evaluates the comparisons   *)
(* of addresses with the same base in the PC and the events, and             *)
(* PFS_CASES_TAC p splits on p and rewrites them with the case. PFS_RUN_TAC  *)
(* simulates from step n to the return, with the calls of memset through the *)
(* PLT, whose events are unified as those of the callees (the shared         *)
(* LIBC_SAFE_CALL_TAC does not allow the functions of the events template).  *)
(* ------------------------------------------------------------------------- *)

let PFS_WORD_SUB_ADD = WORD_RULE
  `!a:int64 x y. word_sub (word_add a x) (word_add a y) = word_sub x y`;;

let pfs_pc_offset t =
  try dest_small_numeral(rand(rand t)) with Failure _ -> -1;;

(* ------------------------------------------------------------------------- *)
(* The memory safety of the events at the end of a segment. The events of    *)
(* the template instantiated so far are beta-reduced, and the list is        *)
(* normalized (PFS_LIST_CONV), so that the events of the invariant, e2, can  *)
(* be folded back; then each part is checked by itself, the parts of e2 and  *)
(* of the callees from the assumptions. The events e2 of the postcondition   *)
(* become a metavariable with a name of its own (PFS_META_EXISTS_TAC):       *)
(* META_EXISTS_TAC chooses a primed e2 that is only fresh in its own goal,   *)
(* which on the valid path is the name of the events of the last memset on   *)
(* the invalid path, and instantiating the metavariable also replaces that   *)
(* variable in the other goal, so that a justification fails (with ABS).     *)
(* ------------------------------------------------------------------------- *)

let rec PFS_MA_TAC (asl,w) =
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THEN
    PFS_MA_TAC) ORELSE
   W(fun (_,w) ->
     let l = lhand(rator w) in
     if is_cons l && not(is_const(rand l) && fst(dest_const(rand l)) = "NIL")
     then GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_CONS] THEN CONJ_TAC THEN
          PFS_MA_TAC
     else NO_TAC) ORELSE
   DISCHARGE_MEMACCESS_INBOUNDS_TAC) (asl,w);;

let PFS_LIST_CONV = REWRITE_CONV[APPEND; APPEND_NIL; GSYM APPEND_ASSOC];;

let PFS_MEMACCESS_TAC =
  let isenum t = try fst(dest_const t) = "ENUMERATEL" with Failure _ -> false in
  CONV_TAC(RATOR_CONV(RATOR_CONV(RAND_CONV PFS_LIST_CONV))) THEN
  TRY(FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var(lhs c) && can (find_term isenum) (rhs c)
    then REWRITE_TAC[GSYM(CONV_RULE(RAND_CONV PFS_LIST_CONV) th)]
    else NO_TAC)) THEN
  PFS_MA_TAC;;

(* Atomic, for proofs on several domains (see common/par.ml) *)
let pfs_meta_count = par_counter ();;

let PFS_META_EXISTS_TAC (asl,w) =
  let v = fst(dest_exists w) in
  let k = 1 + pfs_meta_count () in
  let v' = mk_var("pfs_" ^ fst(dest_var v) ^ "_" ^
                  string_of_int k,type_of v) in
  (CONV_TAC(GEN_ALPHA_CONV v') THEN SAFE_META_EXISTS_TAC allowed_vars_e)
  (asl,w);;

let PFS_EVENTS_TAC =
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  PFS_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
    else ALL_TAC) THEN
  PFS_MEMACCESS_TAC;;

let pfs_n = mk_small_numeral;;
let pfs_sp n = subst [pfs_n n,`n:num`] `word_add stackpointer (word n):int64`;;
let pfs_sk n = subst [pfs_n n,`n:num`] `word_add sk (word n):int64`;;

let pfs_asm_rhs (asl,w) l =
  rhs(concl(snd(find (fun (_,th) ->
    try lhs(concl th) = l with Failure _ -> false) asl)));;

let PFS_FINAL_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_0]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  PFS_EVENTS_TAC;;
