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
(* The product w = A y (mld_polyvec_matrix_pointwise_montgomery_yvec_lazy).  *)
(* The code samples polynomial j of y (mld_sign_y g RP kappa for the sampler *)
(* g of gamma1) into scratch and transforms it, and accumulates its products *)
(* with column j of A into the polynomials of w. MLD_LAZY_YVEC_Y g j and     *)
(* MLD_LAZY_YVEC_YHAT g j are polynomial j of y and of its transform as the  *)
(* specification gives them, for a numeral j, and MLD_LAZY_YVEC_W g l the    *)
(* vector of the sums for l columns.                                         *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_YVEC_YV g =
  list_mk_comb(`mld_sign_y`,[g; `RP:num`; `val(kappa:int16)`]);;

let MLD_LAZY_YVEC_YHATV g =
  mk_comb(`mld_polyvec_map mld_poly_ntt`,MLD_LAZY_YVEC_YV g);;

let MLD_LAZY_YVEC_Y g j =
  mk_comb(mk_comb(`mld_poly_of`,MLD_LAZY_YVEC_YV g),mk_small_numeral j);;

let MLD_LAZY_YVEC_YHAT g j =
  mk_comb(mk_comb(`mld_poly_of`,MLD_LAZY_YVEC_YHATV g),mk_small_numeral j);;

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

(* ------------------------------------------------------------------------- *)
(* The loops of the signing product (_yvec_lazy), whose proofs follow the    *)
(* loops of the code, as those of the x86-64 code do                         *)
(* (x86/proofs/utils/mldsa_native_lazy_matrix.ml), rather than unrolling     *)
(* them: the loop over the columns, with the first column apart, as the code *)
(* takes another path for its rows, and for each column the loop over the    *)
(* rows. The code aligns the buffer of the seed to 32 bytes in its frame:    *)
(* MLD_LAZY_BUFFER_AND gives the AND of the code as the stack pointer plus   *)
(* an offset, which MLD_LAZY_BUFFER_BOUND bounds for a stack pointer aligned *)
(* to 16, so that the buffer is a variable buf in the proofs, apart from the *)
(* other regions, which MLD_LAZY_UNBUF_TAC expands before the events are     *)
(* matched at the end of each part, as the events must not depend on it.     *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_BUFFER_AND = prove
 (`!(p:int64) k.
        31 <= k
        ==> word_and (word_add p (word k)) (word 18446744073709551584) =
            word_add p (word(k - val(word_add p (word k)) MOD 32))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_BLAST `word_and (x:int64) (word 18446744073709551584) =
                          word_sub x (word_and x (word 31))`] THEN
  SUBGOAL_THEN
   `word_and (word_add p (word k)) (word 31):int64 =
    word(val(word_add p (word k):int64) MOD 32)`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `31 = 2 EXP 5 - 1`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC(GSYM MOD_LT) THEN
    MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `32` THEN
    REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = val(word_add p (word k):int64) MOD 32` THEN
  SUBGOAL_THEN `m <= k` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `31` THEN
    ASM_REWRITE_TAC[ARITH_RULE `m <= 31 <=> m < 32`; MOD_LT_EQ] THEN
    ARITH_TAC;
    ASM_SIMP_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE]);;

let MLD_LAZY_BUFFER_BOUND = prove
 (`!p:int64. aligned 16 p ==> 15 <= val(word_add p (word 1503)) MOD 32`,
  GEN_TAC THEN REWRITE_TAC[MLD_ALIGNED_16_32] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (BITBLAST_RULE
   `word_and (p:int64) (word 15) = word 0
    ==> word_and (word_add p (word 1503)) (word 31) = word 15 \/
        word_and (word_add p (word 1503)) (word 31) = word 31`)) THEN
  DISCH_THEN(DISJ_CASES_THEN (MP_TAC o AP_TERM `val:int64->num`)) THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `31 = 2 EXP 5 - 1`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let MLD_LAZY_UNBUF_TAC =
  FIRST_X_ASSUM(fun th ->
    if concl th = `word_add stackpointer (word boff):int64 = buf`
    then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `boff:num`
    then SUBST_ALL_TAC(SYM th) else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The columns and the rows: MLD_LAZY_ACC_ADD1 gives the next sum of a row   *)
(* of mld_lazy_acc, MLD_LAZY_TERM_TAC tm proves the termination tm of the    *)
(* sampling of an entry from mld_matrix_terminates (rewritten with its       *)
(* definition in the assumptions), and MLD_LAZY_VAL_ZX the value of a        *)
(* counter as the 32-bit tests of the code see it. For a loop over the rows  *)
(* i of the vector at w whose rows before i are done and the rest are as     *)
(* before (as in utils/mldsa_native_polyvec.ml), with the rows given by      *)
(* mld_polyvec of the sums, MLD_LAZY_ROW_TAC fr tm proves tm, that           *)
(* coefficient c of row i is fr i c, from the fact for the rows from i on,   *)
(* given by mld_polyvec fr, and MLD_LAZY_JOIN_TAC ths the fact for the rows  *)
(* before i + 1, from those for the rows before i and the postcondition of   *)
(* the callee for row i, rewritten with ths.                                 *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_ACC_ADD1 = prove
 (`!rho i (v:num->int32) n.
        mld_lazy_acc rho i v (n + 1) =
        mld_poly_add (mld_lazy_acc rho i v n)
         (mld_poly_pointwise_montgomery (mld_matrix_entry rho i (n + 1))
                                        (mld_poly_of v (n + 1)))`,
  REWRITE_TAC[GSYM ADD1; mld_lazy_acc]);;

let MLD_LAZY_TERM_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_forall c &&
         (try fst(strip_comb(snd(dest_imp(snd(strip_forall c))))) =
              `mld_rej_uniform_terminates`
          with Failure _ -> false)
      then MATCH_MP_TAC th else NO_TAC) THEN
    CONJ_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

let MLD_LAZY_VAL_ZX = prove
 (`!n. n < 2 EXP 32 ==> val(word_zx(word n:int64):int32) = n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `n < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `n < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]]);;

let MLD_LAZY_ROW_TAC fr tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `c:num` THEN DISCH_TAC THEN
    W(fun (asl,w) ->
      SUBGOAL_THEN
       (mk_eq(rhs w,mk_comb(mk_comb(`mld_polyvec`,fr),`256 * i + c`)))
       SUBST1_TAC THENL
       [ASM_SIMP_TAC[MLD_POLYVEC_COEFF]; ALL_TAC]) THEN
    FIRST_ASSUM(fun th ->
      MP_TAC(SPEC `256 * i + c` th) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN MATCH_MP_TAC THEN SIMPLE_ARITH_TAC);
    ALL_TAC];;

let MLD_LAZY_JOIN_TAC ths =
  MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `c:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC(MLD_POLYVEC_COEFF :: ths) THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Polynomial c of y and of its transform in scratch for a column c that is  *)
(* a term: MLD_LAZY_YVEC_YJ_TAC g c rewrites the postcondition of the        *)
(* sampler g of gamma1, with the nonce kappa + c from the 16-bit kappa and   *)
(* the 32-bit sum of the code (MLD_LAZY_YVEC_NONCE), into polynomial c of    *)
(* mld_sign_y g RP (val kappa), and MLD_LAZY_YVEC_YHATJ_TAC g c that of the  *)
(* NTT into polynomial c of its transform, as MLD_LAZY_YVEC_Y_TAC and        *)
(* MLD_LAZY_YVEC_YHAT_TAC do for a numeral.                                  *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_YVEC_NONCE =
  GEN `i:num` (GEN `kappa:int16` (REWRITE_RULE[WORD_VAL]
    (SPECL [`i:num`; `val(kappa:int16)`] MLD_LAZY_NONCE16)));;

let MLD_LAZY_YVEC_YJ_TAC g jt =
  let yv = list_mk_comb(`mld_sign_y`,[g; `RP:num`; `val(kappa:int16)`]) in
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_LAZY_YVEC_NONCE]) THEN
  MLD_LAZY_REPOLY_TAC
   (list_mk_comb(g,[`RP:num`;
     mk_comb(`word:num->int16`,mk_binop `(+):num->num->num`
       `val(kappa:int16)` jt)]))
   (list_mk_comb(`mld_poly_of`,[yv; jt]))
   [mld_sign_y; MLD_POLY_OF_POLYVEC];;

let MLD_LAZY_YVEC_YHATJ_TAC g jt =
  let yv = list_mk_comb(`mld_sign_y`,[g; `RP:num`; `val(kappa:int16)`]) in
  MLD_LAZY_REPOLY_TAC
   (mk_comb(`mld_poly_ntt`,list_mk_comb(`mld_poly_of`,[yv; jt])))
   (list_mk_comb(`mld_poly_of`,
      [mk_comb(`mld_polyvec_map mld_poly_ntt`,yv); jt]))
   [MLD_POLY_OF_POLYVEC_MAP];;

(* ------------------------------------------------------------------------- *)
(* The events: MLD_LAZY_YVEC_TEMPLATE l k is the template for l columns and  *)
(* k rows, with the prologue, the first column apart (f_ev_..0), the loop    *)
(* over the other columns, each with the sampling of its polynomial of y     *)
(* (cb), the loop over the rows and its end (ce), and the epilogue. A part   *)
(* of a proof whose precondition fixes the events so far as e2 = T, with     *)
(* instances of the metavariables of the template, is started with           *)
(* MLD_LAZY_GEN_OLD_TAC name, which generalizes the longest tail of T that   *)
(* also occurs in the events of the postcondition into a variable of that    *)
(* name, so that the simulation of the calls cannot rewrite T in one place   *)
(* and not in the other; the part is ended with VERIF_EVENTS_TAC of          *)
(* utils/mldsa_native_verify.ml for that variable.                           *)
(* MLD_LAZY_EVENTS_REASSOC_TAC th rewrites the events of the postcondition,  *)
(* at the top only, with th, into the form that ENSURES_EVENTS_WHILE_UP2_TAC *)
(* needs.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_YVEC_ARGS =
  "w mat y scratch r rp guard mf pc stackpointer returnaddress";;

let MLD_LAZY_YVEC_TEMPLATE l k =
  let lam =
    "\\(w:int64) (mat:int64) (y:int64) (scratch:int64) (r:num) (rp:int64) " ^
    "(guard:int64) (mf:int64) (pc:num) (stackpointer:int64) " ^
    "(returnaddress:int64)." in
  let a = MLD_LAZY_YVEC_ARGS in
  let f n = "(f_ev_" ^ n ^ " " ^ a ^ ")"
  and fl n = "(f_ev_" ^ n ^ " " ^ a ^ " l)"
  and ks = string_of_int k in
  let col0 =
    "(APPEND " ^ f "ce0" ^ " (APPEND (ENUMERATEL " ^ ks ^
    " (\\i. f_ev_row0 " ^ a ^ " i)) " ^ f "cb0" ^ "))"
  and col =
    "(\\l. APPEND " ^ fl "ce" ^ " (APPEND (ENUMERATEL " ^ ks ^
    " (\\i. f_ev_row " ^ a ^ " l i)) " ^ fl "cb" ^ "))" in
  parse_term(lam ^ " APPEND " ^ f "epil" ^ " (APPEND (ENUMERATEL " ^
             string_of_int(l - 1) ^ " " ^ col ^
             ") (APPEND " ^ col0 ^ " " ^ f "prol" ^
             ")) :(uarch_event)list");;

let MLD_LAZY_GEN_OLD_TAC name =
  W(fun (asl,w) ->
    let pre = rand(rator(rator w)) and post = rand(rator w) in
    let is_e2eq t = is_eq t && is_var(lhs t) && fst(dest_var(lhs t)) = "e2" in
    match (try Some(rhs(find_term is_e2eq pre),rhs(find_term is_e2eq post))
           with Failure _ -> None) with
      None -> ALL_TAC
    | Some(tpre,tpost) ->
        let rec pick t =
          if free_in t tpost then t
          else if is_comb t then pick (rand t) else failwith "pick" in
        let x = pick tpre in
        if is_var x then ALL_TAC
        else SPEC_TAC(x,mk_var(name,type_of x)) THEN GEN_TAC);;

let MLD_LAZY_EVENTS_REASSOC_TAC th =
  W(fun (asl,w) ->
    let post = rand(rator w) in
    let e2eq = find_term (fun t -> is_eq t && is_var(lhs t) &&
                                   fst(dest_var(lhs t)) = "e2") post in
    REWRITE_TAC[GEN_REWRITE_CONV I [th] (rhs e2eq)]);;

(* ------------------------------------------------------------------------- *)
(* The parts of the invariants, as strings: polynomial c of the transform of *)
(* y in scratch (MLD_LAZY_INV_SCRATCH, for the transform yhat given by       *)
(* MLD_LAZY_INV_YHAT g), and the n coefficients of the vector w with the     *)
(* sums for the columns up to c (MLD_LAZY_INV_W), in the loop over the rows  *)
(* those of the rows before i (MLD_LAZY_INV_DONE) and from i                 *)
(* (MLD_LAZY_INV_REST).                                                      *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_INV_YHAT g =
  "(mld_polyvec_map mld_poly_ntt (mld_sign_y " ^ g ^
  " RP (val(kappa:int16))))";;

let MLD_LAZY_INV_SCRATCH yhat c =
  "(!j. j < 256
        ==> read (memory :> bytes32 (word_add scratch (word(4 * j)))) s =
            mld_poly_of " ^ yhat ^ " " ^ c ^ " j)";;

let MLD_LAZY_INV_W yhat n c =
  "(!j. j < " ^ n ^ "
        ==> read (memory :> bytes32 (word_add w (word(4 * j)))) s =
            mld_polyvec (\\q. mld_lazy_acc r q " ^ yhat ^ " " ^ c ^ ") j)";;

let MLD_LAZY_INV_DONE yhat c =
  "(!j. j < 256 * i
        ==> read (memory :> bytes32 (word_add w (word(4 * j)))) s =
            mld_polyvec (\\q. mld_lazy_acc r q " ^ yhat ^ " " ^ c ^ ") j)";;

let MLD_LAZY_INV_REST yhat n c =
  "(!j. 256 * i <= j /\\ j < " ^ n ^ "
        ==> read (memory :> bytes32 (word_add w (word(4 * j)))) s =
            mld_polyvec (\\q. mld_lazy_acc r q " ^ yhat ^ " " ^ c ^ ") j)";;
