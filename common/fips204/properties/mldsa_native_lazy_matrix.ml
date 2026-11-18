(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the matrix-vector products of the reduced-RAM     *)
(* code (mld_polyvec_matrix_pointwise_montgomery_row_lazy and _yvec_lazy):   *)
(* the code copies rho to a buffer of 64 bytes on the stack and stores the   *)
(* indices j and i of an entry after it before each call of                  *)
(* mldsa_poly_uniform, as mld_polyvec_matrix_expand_eager does (see          *)
(* mldsa_native_matrix.ml), but for a row index i that is an argument        *)
(* of the function rather than a constant. The results are folded with       *)
(* mld_lazy_acc of common/mldsa_native_lazy.ml.                              *)
(* ========================================================================= *)

needs "common/mldsa_native_lazy.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/fips204/properties/mldsa_native_matrix.ml";;
needs "common/fips204/properties/mldsa_native_keypair.ml";;

(* ------------------------------------------------------------------------- *)
(* The row index i < 256, passed as the 64-bit word i and stored as a byte   *)
(* (via the 32-bit and with 255 of the code).                                *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_ROW_INDEX = prove
 (`!i. i < 256
       ==> word_zx(word_zx(word_zx(word_and (word_zx(word i:int64):int32)
                                            (word 255)):int64):int32):byte =
           word i /\
           word_zx(word_and (word_zx(word i:int64):int32) (word 255)):int64 =
           word i`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `word i:int64 = word_zx(word i:byte)` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_8; DIMINDEX_64] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`word i:byte`,`b:byte`) THEN CONV_TAC WORD_BLAST);;

(* MLD_LAZY_ROW_INDEX_TAC k rewrites the index in the assumptions, given     *)
(* the assumption i < k for a numeral k <= 256.                              *)

let MLD_LAZY_ROW_INDEX_TAC k =
  let kt = mk_small_numeral k in
  let lt = ARITH_RULE(mk_imp(mk_binop `(<):num->num->bool` `i:num` kt,
                             `i < 256`)) in
  W(fun (asl,w) ->
    let ith = MP lt (ASSUME(mk_binop `(<):num->num->bool` `i:num` kt)) in
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP MLD_LAZY_ROW_INDEX ith]));;

let MLD_LAZY_ROW_TERM_TAC k l j =
  let jt = mk_small_numeral j and kt = mk_small_numeral k
  and lt = mk_small_numeral l in
  FIRST_ASSUM(fun th ->
    if is_forall (concl th) &&
       can (find_term ((=) `mld_rej_uniform_terminates`)) (concl th)
    then ASSUME_TAC(MP (SPECL [`i:num`; jt] th)
                       (CONJ (ASSUME(mk_binop `(<):num->num->bool` `i:num` kt))
                             (EQT_ELIM(NUM_REDUCE_CONV
                               (mk_binop `(<):num->num->bool` jt lt)))))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The terms of the results: the product of entry (i,j) with polynomial j of *)
(* x, and the partial sums, as the code computes them (with x itself for     *)
(* polynomial 0, as the facts about the vector give it); and the expansion   *)
(* of mld_lazy_acc for a numeral, which gives them back.                     *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_ROW_ENTRY j =
  mk_comb(`mld_poly_uniform`,
          list_mk_comb(`mld_matrix_seed`,
                       [`r:num`; `i:num`; mk_small_numeral j]));;

let MLD_LAZY_ROW_POLY j =
  if j = 0 then `x:num->int32` else
  mk_abs(`k:num`,mk_comb(`x:num->int32`,
         mk_binop `(+):num->num->num` (mk_small_numeral(256 * j)) `k:num`));;

let MLD_LAZY_ROW_PW j =
  mk_comb(mk_comb(`mld_poly_pointwise_montgomery`,MLD_LAZY_ROW_ENTRY j),
          MLD_LAZY_ROW_POLY j);;

let rec MLD_LAZY_ROW_ACC j =
  if j = 0 then MLD_LAZY_ROW_PW 0
  else mk_comb(mk_comb(`mld_poly_add`,MLD_LAZY_ROW_ACC (j - 1)),
               MLD_LAZY_ROW_PW j);;

let MLD_LAZY_ACC_CONV =
  let th0,th1 = CONJ_PAIR mld_lazy_acc in
  let rec conv tm =
    match tm with
      Comb(Comb(Comb(Comb(Const("mld_lazy_acc",_),_),_),_),n)
      when is_numeral n ->
        if dest_small_numeral n = 0 then REWR_CONV th0 tm
        else (RAND_CONV num_CONV THENC REWR_CONV th1 THENC
              LAND_CONV conv THENC
              RAND_CONV(DEPTH_CONV NUM_SUC_CONV)) tm
    | _ -> failwith "MLD_LAZY_ACC_CONV" in
  conv;;

(* The postcondition of the row function from the fact for t at the end.     *)

let MLD_LAZY_ROW_POST_TAC =
  REWRITE_TAC[mld_polyvec_matrix_row_lazy] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV MLD_LAZY_ACC_CONV) THEN
  REWRITE_TAC[mld_matrix_entry; mld_poly_of] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; ETA_AX] THEN
  FIRST_ASSUM ACCEPT_TAC;;

(* ------------------------------------------------------------------------- *)
(* The product w = A y (mld_polyvec_matrix_pointwise_montgomery_yvec_lazy),  *)
(* simulated with both loops unrolled. The code samples polynomial j of y    *)
(* (mld_sign_y g RP kappa for the sampler g of gamma1) into scratch and      *)
(* transforms it, and accumulates its products with column j of A into the   *)
(* polynomials of w. MLD_LAZY_YVEC_Y g j and MLD_LAZY_YVEC_YHAT g j are the  *)
(* polynomial j of y and of its transform as the specification gives them,   *)
(* and MLD_LAZY_YVEC_PW, _ACC and _W the products, the partial sums of a row *)
(* and the vector of the sums.                                               *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_YVEC_YV g =
  list_mk_comb(`mld_sign_y`,[g; `RP:num`; `val(kappa:int16)`]);;

let MLD_LAZY_YVEC_YHATV g =
  mk_comb(`mld_polyvec_map mld_poly_ntt`,MLD_LAZY_YVEC_YV g);;

let MLD_LAZY_YVEC_Y g j =
  mk_comb(mk_comb(`mld_poly_of`,MLD_LAZY_YVEC_YV g),mk_small_numeral j);;

let MLD_LAZY_YVEC_YHAT g j =
  mk_comb(mk_comb(`mld_poly_of`,MLD_LAZY_YVEC_YHATV g),mk_small_numeral j);;

let MLD_LAZY_YVEC_ENTRY i j =
  mk_comb(`mld_poly_uniform`,
          list_mk_comb(`mld_matrix_seed`,
                       [`r:num`; mk_small_numeral i; mk_small_numeral j]));;

let MLD_LAZY_YVEC_PW g i j =
  list_mk_comb(`mld_poly_pointwise_montgomery`,
               [MLD_LAZY_YVEC_ENTRY i j; MLD_LAZY_YVEC_YHAT g j]);;

let rec MLD_LAZY_YVEC_ACC g i j =
  if j = 0 then MLD_LAZY_YVEC_PW g i 0
  else list_mk_comb(`mld_poly_add`,
                    [MLD_LAZY_YVEC_ACC g i (j - 1); MLD_LAZY_YVEC_PW g i j]);;

let MLD_LAZY_YVEC_W g l =
  mk_comb(`mld_polyvec`,
          mk_abs(`i:num`,
                 list_mk_comb(`mld_lazy_acc`,
                              [`r:num`; `i:num`; MLD_LAZY_YVEC_YHATV g;
                               mk_small_numeral(l - 1)])));;

(* The coefficients sampled into scratch, as polynomial j of y: the nonce is *)
(* kappa + j as a 16-bit word, from the 32-bit sum of the code.              *)

let MLD_LAZY_YVEC_Y_TAC g j =
  let gr = mk_comb(g,`RP:num`) and jt = mk_small_numeral j in
  let nonce = mk_comb(`word:num->int16`,
                      mk_binop `(+):num->num->num` `val(kappa:int16)` jt) in
  FIRST_ASSUM(fun th ->
    let t = find_term (fun t -> is_comb t && rator t = gr) (concl th) in
    let eth = prove(mk_eq(rand t,nonce),
                    REWRITE_TAC[WORD_ADD; WORD_VAL] THEN BITBLAST_TAC) in
    let tm = subst [MLD_LAZY_YVEC_Y g j,t] (concl th) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN
      DISCH_THEN(fun ith ->
        REWRITE_TAC[MP (SPEC `i:num` th) ith; eth; mld_sign_y] THEN
        SIMP_TAC[MLD_POLY_OF_POLYVEC; ith]);
      ALL_TAC]);;

(* The transform in scratch, as polynomial j of the transform of y.          *)

let MLD_LAZY_YVEC_YHAT_TAC g j =
  let t = mk_comb(`mld_poly_ntt`,MLD_LAZY_YVEC_Y g j) in
  FIRST_ASSUM(fun th ->
    if not(can (find_term ((=) t)) (concl th)) then failwith "YHAT" else
    let tm = subst [MLD_LAZY_YVEC_YHAT g j,t] (concl th) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN
      DISCH_THEN(fun ith ->
        REWRITE_TAC[MP (SPEC `i:num` th) ith] THEN
        SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP; ith]);
      ALL_TAC]);;

(* The postcondition, from the fact for w after the inverse transform.       *)

let MLD_LAZY_YVEC_POST_TAC =
  REWRITE_TAC[mld_polyvec_matrix_yvec_lazy] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC;;

(* ------------------------------------------------------------------------- *)
(* A FULL theorem from one for the vector t as the reduced-RAM code computes *)
(* it: MLD_LAZY_FULL0 stmt is the FULL statement stmt with mld_compute_t     *)
(* replaced by mld_compute_t_lazy and without the hypothesis on the bound of *)
(* s1hat (the conjunct with MLD_NTT_BOUND = 94279689), and                   *)
(* MLD_LAZY_FULL_OF_FULL0_TAC th lemtac proves stmt from th, the theorem for *)
(* MLD_LAZY_FULL0 stmt, with the facts that lemtac adds to the assumptions   *)
(* (from the hypotheses of stmt), which rewrite the postcondition of th to   *)
(* that of stmt. The events are the same, so a SAFE theorem follows from th  *)
(* by SAFE_OF_FULL_TAC as from a FULL theorem.                               *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_FULL0 =
  let is_bound t = can (find_term ((=) `&94279689:int`)) t in
  let rec drop t =
    if is_conj t then
      let l,r = dest_conj t in
      if is_bound l then r else mk_conj(l,drop r)
    else t in
  let rec go t =
    if is_forall t then let v,b = dest_forall t in mk_forall(v,go b)
    else if is_exists t then let v,b = dest_exists t in mk_exists(v,go b)
    else if is_imp t then
      let h,c = dest_imp t in
      if (try fst(dest_const(fst(strip_comb c))) = "ensures"
          with Failure _ -> false)
      then mk_imp(drop h,c) else mk_imp(h,go c)
    else t in
  fun tm -> subst [`mld_compute_t_lazy`,`mld_compute_t`] (go tm);;

(* ------------------------------------------------------------------------- *)
(* MLD_LAZY_REPOLY_TAC old nw ths: from the newest fact                      *)
(* !k. k < 256 ==> read l s = old k, the same fact for nw, where             *)
(* old k = nw k for k < 256 follows by rewriting with ths (and k < 256),     *)
(* e.g. a polynomial computed by the code and polynomial i of a vector of    *)
(* the specification.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_REPOLY_TAC old nw ths =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(is_forall c) ||
       not(can (find_term (fun t -> is_comb t && rator t = old)) c)
    then failwith "MLD_LAZY_REPOLY_TAC" else
    let k,_ = dest_forall c in
    let tm = subst [nw,old] c in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [X_GEN_TAC k THEN
      DISCH_THEN(fun kth ->
        REWRITE_TAC[MP (SPEC k th) kth] THEN SIMP_TAC(kth::ths));
      ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The nonce of the sampling of polynomial i of y in signing.                *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_NONCE16 = prove
 (`!i k. word_zx(word_zx(word_add (word_zx(word i:int64):int32)
                         (word_zx(word_zx(word k:int16):int64):int32)):int64)
         :int16 = word(k + i) /\
         word_zx(word_zx(word_add (word_zx(word i:int64):int32)
           (word_zx(word_zx(word_zx(word k:int16):int32):int64):int32)):int64)
         :int16 = word(k + i)`,
  let mins = ARITH_RULE
   `MIN 16 64 = 16 /\ MIN 32 64 = 32 /\ MIN 32 16 = 16 /\ MIN 64 16 = 16 /\
    MIN 64 32 = 32 /\ MIN 16 32 = 16 /\ MIN 16 16 = 16` in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[mins] THEN ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN; MOD_MOD_REFL; mins; ADD_SYM]);;

(* The same with the two operands of the sum in the other order, as the      *)
(* code for ML-DSA-65 and ML-DSA-87 adds them.                               *)

let MLD_LAZY_NONCE16_KI = prove
 (`!i k. word_zx(word_zx(word_add
           (word_zx(word_zx(word_zx(word k:int16):int32):int64):int32)
           (word_zx(word i:int64):int32)):int64):int16 = word(k + i) /\
         word_zx(word_zx(word_add (word_zx(word_zx(word k:int16):int64):int32)
           (word_zx(word i:int64):int32)):int64):int16 = word(k + i)`,
  let mins = ARITH_RULE
   `MIN 16 64 = 16 /\ MIN 32 64 = 32 /\ MIN 32 16 = 16 /\ MIN 64 16 = 16 /\
    MIN 64 32 = 32 /\ MIN 16 32 = 16 /\ MIN 16 16 = 16` in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[mins] THEN ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN; MOD_MOD_REFL; mins]);;

(* Polynomial i of y sampled with the nonce k + i of the code, as            *)
(* polynomial i of mld_sign_y g rhop k (MLD_LAZY_NONCE16 and                 *)
(* MLD_LAZY_NONCE16_KI are the nonce from the 16-bit k and the 32-bit sum of *)
(* the code).                                                                *)

let MLD_LAZY_SIGN_Y_TAC g =
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_LAZY_NONCE16; MLD_LAZY_NONCE16_KI]) THEN
  MLD_LAZY_REPOLY_TAC
   (list_mk_comb(g,[`rhop:num`; `word(k + i):int16`]))
   (list_mk_comb(`mld_poly_of`,
     [list_mk_comb(`mld_sign_y`,[g; `rhop:num`; `k:num`]); `i:num`]))
   [mld_sign_y; MLD_POLY_OF_POLYVEC];;
