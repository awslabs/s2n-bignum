(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The arithmetic of mldsa-native's portable C code in the NTT domain and    *)
(* its relation to FIPS 204 (common/fips204.ml): the NTT, the inverse NTT    *)
(* and the pointwise products of common/mldsa_native_poly.ml and             *)
(* mldsa_native_polyvec.ml up to congruence mod q = 8380417, as the explicit *)
(* forms of common/mlkem_mldsa.ml (arm_mldsa_forward_ntt, ...), and from     *)
(* these, for inputs within the bounds of the C contracts, the NTT as        *)
(* mldsa_ntt, the inverse NTT of the Montgomery dot product of a row of the  *)
(* matrix with a vector as the dot product in R_q, and the inverse NTT of a  *)
(* pointwise Montgomery product as the product in R_q.                       *)
(* ========================================================================= *)

needs "common/mlkem_mldsa.ml";;
needs "common/int_linear.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "common/fips204_theory.ml";;

(* ------------------------------------------------------------------------- *)
(* Montgomery reduction and multiplication as mldsa_pointwise_montred,       *)
(* and the zetas as words.                                                   *)
(* ------------------------------------------------------------------------- *)

let ZX_SX_32_64 = prove
 (`!y:int32. word_zx(word_sx y:int64):int32 = y`,
  CONV_TAC WORD_BLAST);;

let ZX_SUBWORD_64_32 = prove
 (`!x:int64. word_zx x:int32 = word_subword x (0,32)`,
  CONV_TAC WORD_BLAST);;

let MLD_MONTGOMERY_REDUCE_POINTWISE = prove
 (`!a. mld_montgomery_reduce a = mldsa_pointwise_montred a`,
  GEN_TAC THEN REWRITE_TAC[mld_montgomery_reduce; mldsa_pointwise_montred] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM ZX_SUBWORD_64_32] THEN
  SIMP_TAC[WORD_ZX_MUL; DIMINDEX_32; DIMINDEX_64; ARITH; ZX_SX_32_64] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_MUL_SYM]);;

let MLD_FQMUL_POINTWISE = prove
 (`!a b. mld_fqmul a b =
         mldsa_pointwise_montred (word_mul (word_sx a) (word_sx b))`,
  REWRITE_TAC[mld_fqmul; MLD_MONTGOMERY_REDUCE_POINTWISE]);;

let MLD_NTT_LAYERS_SUC = prove
 (`!l x. mld_ntt_layers (SUC l) x =
         mld_ntt_blocks l (2 EXP l) (mld_ntt_layers l x)`,
  REWRITE_TAC[mld_ntt_layers]);;

let MLD_ZETA_CLAUSES =
  let zl = rand(concl mld_zetas) in
  let conv k =
    let tm = mk_comb(`mld_zeta`,mk_small_numeral k) in
    let th1 = REWR_CONV mld_zeta tm in
    let th2 = CONV_RULE(RAND_CONV(RAND_CONV
      (RAND_CONV(REWR_CONV mld_zetas) THENC EL_CONV))) th1 in
    CONV_RULE(RAND_CONV WORD_IWORD_CONV) th2 in
  ignore zl; end_itlist CONJ (map conv (0--255));;

let MLD_MONT_INVERSE = INVERSE_MOD_CONV `inverse_mod 8380417 4294967296`;;

(* ------------------------------------------------------------------------- *)
(* In each layer, coefficient i only depends on the block containing it.     *)
(* ------------------------------------------------------------------------- *)

let MLD_NTT_BLOCKS_LOCAL = prove
 (`!l b (r:num->int32) i.
        mld_ntt_blocks l b r i =
        if i < 2 * 2 EXP (7 - l) * b
        then mld_ntt_block (mld_zeta(2 EXP l + i DIV (2 * 2 EXP (7 - l))))
               (2 * 2 EXP (7 - l) * (i DIV (2 * 2 EXP (7 - l))))
               (2 EXP (7 - l)) r i
        else r i`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[mld_ntt_blocks; MULT_CLAUSES; CONJUNCT1 LT] THEN
  MAP_EVERY X_GEN_TAC [`r:num->int32`; `i:num`] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SPEC `r:num->int32`) THEN
  ABBREV_TAC `L = 2 EXP (7 - l)` THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  ASM_CASES_TAC `i < 2 * L * b` THENL
   [GEN_REWRITE_TAC LAND_CONV [mld_ntt_block] THEN
    SUBGOAL_THEN `~(2 * L * b <= i)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(2 * L * b + L <= i)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `i < 2 * (L + L * b)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `i < 2 * (L + L * b)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `i DIV (2 * L) = b` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i - 2 * L * b` THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[mld_ntt_block] THEN
    SUBGOAL_THEN `2 * L * b <= i` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `i < 2 * L * b + L` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `~(i + L < 2 * L * b)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `2 * L * b + L <= i /\ i < 2 * L * b + 2 * L`
       (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(i - L < 2 * L * b)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC];
    GEN_REWRITE_TAC LAND_CONV [mld_ntt_block] THEN
    SUBGOAL_THEN `~(2 * L * b <= i /\ i < 2 * L * b + L) /\
                  ~(2 * L * b + L <= i /\ i < 2 * L * b + 2 * L)`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let MLD_INVNTT_BLOCKS_LOCAL = prove
 (`!m b (r:num->int32) i.
        mld_invntt_blocks m b r i =
        if i < 2 * 2 EXP (8 - m) * b
        then mld_invntt_block
               (word_neg(mld_zeta(2 EXP m - 1 - i DIV (2 * 2 EXP (8 - m)))))
               (2 * 2 EXP (8 - m) * (i DIV (2 * 2 EXP (8 - m))))
               (2 EXP (8 - m)) r i
        else r i`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[mld_invntt_blocks; MULT_CLAUSES; CONJUNCT1 LT] THEN
  MAP_EVERY X_GEN_TAC [`r:num->int32`; `i:num`] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SPEC `r:num->int32`) THEN
  ABBREV_TAC `L = 2 EXP (8 - m)` THEN
  SUBGOAL_THEN `~(L = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  ASM_CASES_TAC `i < 2 * L * b` THENL
   [GEN_REWRITE_TAC LAND_CONV [mld_invntt_block] THEN
    SUBGOAL_THEN `~(2 * L * b <= i)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(2 * L * b + L <= i)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `i < 2 * (L + L * b)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `i < 2 * (L + L * b)` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `i DIV (2 * L) = b` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i - 2 * L * b` THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[mld_invntt_block] THEN
    SUBGOAL_THEN `2 * L * b <= i` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `i < 2 * L * b + L` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `~(i + L < 2 * L * b)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `2 * L * b + L <= i /\ i < 2 * L * b + 2 * L`
       (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(i - L < 2 * L * b)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC];
    GEN_REWRITE_TAC LAND_CONV [mld_invntt_block] THEN
    SUBGOAL_THEN `~(2 * L * b <= i /\ i < 2 * L * b + L) /\
                  ~(2 * L * b + L <= i /\ i < 2 * L * b + 2 * L)`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The residues g^e rem q, for g = 1753 and its inverse 731434 modulo q      *)
(* (both of order 512), by a table of g^b rem q for b < 512.                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POW_REM_CONV =
  let mk_conv g =
    let gtm = mk_intconst(num g) in
    let pat = mk_binop `rem` (mk_binop `(pow):int->num->int` gtm `e:num`)
                        `&8380417:int` in
    let oth = prove
     (subst [`512 * a + b`,`e:num`]
            (mk_eq(pat,subst [`b:num`,`e:num`] pat)),
      REWRITE_TAC[INT_POW_ADD; GSYM INT_POW_POW] THEN
      ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
      ONCE_REWRITE_TAC[GSYM INT_POW_REM] THEN
      CONV_TAC(ONCE_DEPTH_CONV(LAND_CONV(LAND_CONV(LAND_CONV
        INT_REDUCE_CONV)))) THEN
      REWRITE_TAC[INT_POW_ONE; INT_REM_REM; INT_MUL_LID] THEN
      CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[INT_REM_REM; INT_MUL_LID]) in
    let tconv b =
      let tm = subst [mk_small_numeral b,`e:num`] pat in
      (GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
       ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV) tm in
    let tbl = Array.of_list (map tconv (0--511)) in
    let plus_tm = `(+):num->num->num` and times_tm = `( * ):num->num->num`
    and t512 = `512` and rem_tm = `rem` and q_tm = `&8380417:int`
    and a_tm = `a:num` and b_tm = `b:num`
    and pow_tm = `(pow):int->num->int` and gpow_tm = rator(lhand pat) in
    fun tm ->
      if not(is_binop rem_tm tm && rand tm = q_tm &&
             is_binop pow_tm (lhand tm) && lhand(lhand tm) = gtm)
      then failwith "MLDSA_POW_REM_CONV" else
      let e = dest_numeral(rand(lhand tm)) in
      let a = quo_num e (num 512) and b = mod_num e (num 512) in
      let atm = mk_numeral a and btm = mk_numeral b in
      let eth = SYM(NUM_REDUCE_CONV
         (mk_comb(mk_comb(plus_tm,mk_comb(mk_comb(times_tm,t512),atm)),btm))) in
      let th1 = AP_THM (AP_TERM rem_tm (AP_TERM gpow_tm eth)) q_tm in
      let th2 = INST [atm,a_tm; btm,b_tm] oth in
      TRANS th1 (TRANS th2 tbl.(Num.int_of_num b)) in
  let c1 = mk_conv 1753 and c2 = mk_conv 731434 in
  fun tm -> try c1 tm with Failure _ -> c2 tm;;

(* ------------------------------------------------------------------------- *)
(* The coefficients of each layer of the transforms as words in those of     *)
(* the previous layer, their congruences and bounds for all layers, and      *)
(* the explicit forms of the transforms with the residues of the powers.     *)
(* ------------------------------------------------------------------------- *)

let MLD_INVNTT_LAYERS_SUC = prove
 (`!n x. mld_invntt_layers (SUC n) x =
         mld_invntt_blocks (8 - n) (2 EXP (7 - n)) (mld_invntt_layers n x)`,
  REWRITE_TAC[mld_invntt_layers]);;

let MLD_NTT_LAYER_CONV,MLD_INVNTT_LAYER_CONV =
  let mk lconst sucth locth l0th =
    let simp =
      NUM_REDUCE_CONV THENC REWRITE_CONV[] THENC
      REWRITE_CONV[mld_ntt_block; mld_invntt_block] THENC NUM_REDUCE_CONV THENC
      REWRITE_CONV[l0th; MLD_ZETA_CLAUSES] THENC
      REWRITE_CONV[MLD_FQMUL_POINTWISE] THENC
      DEPTH_CONV WORD_RED_CONV in
    fun tm ->
      match tm with
        Comb(Comb(Comb(c,ntm),xtm),itm) when c = lconst ->
          let th0 = AP_THM (AP_THM (AP_TERM c (num_CONV ntm)) xtm) itm in
          let th1 = CONV_RULE (RAND_CONV
                     (RATOR_CONV(REWR_CONV sucth) THENC REWR_CONV locth)) th0 in
          CONV_RULE (RAND_CONV simp) th1
      | _ -> failwith "MLD_NTT_LAYER_CONV" in
  mk `mld_ntt_layers` (SPEC_ALL MLD_NTT_LAYERS_SUC) MLD_NTT_BLOCKS_LOCAL
     (CONJUNCT1 mld_ntt_layers),
  mk `mld_invntt_layers` (SPEC_ALL MLD_INVNTT_LAYERS_SUC)
     MLD_INVNTT_BLOCKS_LOCAL (CONJUNCT1 mld_invntt_layers);;

let MLD_NTT_CONGBOUND_TABLE conv lconst xtm bths =
  let lfn0 = PROCESS_BOUND_ASSUMPTIONS bths in
  let rec layer n lfn =
    if n > 8 then lfn else
    let ntm = mk_small_numeral n in
    let step i lfn' =
      let tm = list_mk_comb(lconst,[ntm; xtm; mk_small_numeral i]) in
      let eth = conv tm in
      let cth = ASM_CONGBOUND_RULE lfn (rand(concl eth)) in
      (tm |-> SUBS[SYM eth] cth) lfn' in
    layer (n + 1) (itlist step (0--255) lfn) in
  layer 1 lfn0;;

let ARM_MLDSA_FORWARD_NTT_FAST_CONV =
  GEN_REWRITE_CONV I [ARM_MLDSA_FORWARD_NTT_ALT] THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE8_CLAUSES] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  ONCE_DEPTH_CONV MLDSA_POW_REM_CONV;;

let ARM_MLDSA_INVERSE_NTT_FAST_CONV =
  GEN_REWRITE_CONV I [ARM_MLDSA_INVERSE_NTT_ALT] THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE8_CLAUSES] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  ONCE_DEPTH_CONV MLDSA_POW_REM_CONV THENC INT_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The forward NTT (mld_poly_ntt in poly.h): for |x| < q, congruent to       *)
(* arm_mldsa_forward_ntt, with |output| < MLD_NTT_BOUND = 94279689.          *)
(* ------------------------------------------------------------------------- *)

let MLD_POLY_NTT_CONG = prove
 (`!x:num->int32.
        (!i. i < 256 ==> abs(ival(x i)) < &8380417)
        ==> !i. i < 256
                ==> (ival(mld_poly_ntt x i) ==
                     arm_mldsa_forward_ntt (ival o x) i) (mod &8380417) /\
                    abs(ival(mld_poly_ntt x i)) < &94279689`,
  REWRITE_TAC[mld_poly_ntt] THEN GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  W(fun (asl,w) ->
    let ath = snd(hd asl) in
    let tbl = MLD_NTT_CONGBOUND_TABLE MLD_NTT_LAYER_CONV `mld_ntt_layers`
                `x:num->int32` (CONJUNCTS(CONV_RULE EXPAND_CASES_CONV ath)) in
    let fin w =
      let ttm = rand(lhand(rator(lhand w))) in
      TAC_PROOF((asl,w),
        MP_TAC(apply tbl ttm) THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
         [REWRITE_TAC[MLD_MONT_INVERSE] THEN
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
          CONV_TAC(RATOR_CONV(RAND_CONV ARM_MLDSA_FORWARD_NTT_FAST_CONV)) THEN
          REWRITE_TAC[INT_CONG_RREM; o_THM] THEN INT_LINEAR_CONG_TAC;
          INT_ARITH_TAC]) in
    let rec fins w =
      let c,r = dest_conj w in
      if is_conj r then
        let b,rest = dest_conj r in
        let th = fin(mk_conj(c,b)) in
        CONJ (CONJUNCT1 th) (CONJ (CONJUNCT2 th) (fins rest))
      else fin w in
    ACCEPT_TAC(fins w)));;

(* ------------------------------------------------------------------------- *)
(* The inverse NTT (mld_poly_invntt_tomont in poly.h): for |x| < q,          *)
(* congruent to arm_mldsa_inverse_ntt, with |output| < q.                    *)
(* ------------------------------------------------------------------------- *)

let MLD_POLY_INVNTT_TOMONT_CONG = prove
 (`!x:num->int32.
        (!i. i < 256 ==> abs(ival(x i)) < &8380417)
        ==> !i. i < 256
                ==> (ival(mld_poly_invntt_tomont x i) ==
                     arm_mldsa_inverse_ntt (ival o x) i) (mod &8380417) /\
                    abs(ival(mld_poly_invntt_tomont x i)) < &8380417`,
  REWRITE_TAC[mld_poly_invntt_tomont; mld_fqscale;
              MLD_MONTGOMERY_REDUCE_POINTWISE] THEN
  GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  W(fun (asl,w) ->
    let ath = snd(hd asl) in
    let tbl = MLD_NTT_CONGBOUND_TABLE MLD_INVNTT_LAYER_CONV
                `mld_invntt_layers` `x:num->int32`
                (CONJUNCTS(CONV_RULE EXPAND_CASES_CONV ath)) in
    let fin w =
      let ttm = rand(lhand(rator(lhand w))) in
      TAC_PROOF((asl,w),
        MP_TAC(ASM_CONGBOUND_RULE tbl ttm) THEN
        MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
         [REWRITE_TAC[MLD_MONT_INVERSE] THEN
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
          CONV_TAC(RATOR_CONV(RAND_CONV ARM_MLDSA_INVERSE_NTT_FAST_CONV)) THEN
          REWRITE_TAC[INT_CONG_RREM; o_THM] THEN INT_LINEAR_CONG_TAC;
          INT_ARITH_TAC]) in
    let rec fins w =
      let c,r = dest_conj w in
      if is_conj r then
        let b,rest = dest_conj r in
        let th = fin(mk_conj(c,b)) in
        CONJ (CONJUNCT1 th) (CONJ (CONJUNCT2 th) (fins rest))
      else fin w in
    ACCEPT_TAC(fins w)));;

(* ------------------------------------------------------------------------- *)
(* The pointwise Montgomery products (mld_poly_pointwise_montgomery and      *)
(* mld_polyvec_pointwise_acc_montgomery for L = 4, 5, 7), with the bounds    *)
(* of the C contracts: inputs below q (the matrix) and MLD_NTT_BOUND.        *)
(* ------------------------------------------------------------------------- *)

let MLD_POLY_POINTWISE_MONTGOMERY_CONG = prove
 (`!(a:num->int32) b i.
        abs(ival(a i)) < &94279689 /\ abs(ival(b i)) < &94279689
        ==> (ival(mld_poly_pointwise_montgomery a b i) ==
             mldsa_pointwise (ival o a) (ival o b) i) (mod &8380417) /\
            abs(ival(mld_poly_pointwise_montgomery a b i)) < &8380417`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mld_poly_pointwise_montgomery; MLD_MONTGOMERY_REDUCE_POINTWISE;
              mldsa_pointwise; o_THM; INT_CONG_RREM] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(GEN_CONGBOUND_RULE (CONJUNCTS th)
     `mldsa_pointwise_montred
        (word_mul (word_sx((a:num->int32) i))
                  (word_sx((b:num->int32) i)))`)) THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_MUL_AC]; INT_ARITH_TAC]);;

let MLD_POLYVEC_DOT_CONV =
  let th0 = CONJUNCT1 mld_polyvec_dot and th1 = CONJUNCT2 mld_polyvec_dot in
  let rec conv tm =
    match tm with
      Comb(Comb(Comb(Comb(Const("mld_polyvec_dot",_),n),_),_),_)
        when is_numeral n ->
        if dest_small_numeral n = 0 then REWR_CONV th0 tm else
        (RATOR_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV num_CONV))) THENC
         REWR_CONV th1 THENC LAND_CONV conv) tm
    | _ -> failwith "MLD_POLYVEC_DOT_CONV" in
  conv;;

let MLD_POINTWISE_ACC_CONG_TAC accdef l =
  let n = 256 * l in
  let ntm = mk_small_numeral n and ith = ASSUME `i < 256` in
  let norm = map (fun k ->
    if k = 0 then ARITH_RULE `256 * 0 + i = i` else
    ARITH_RULE(subst [mk_small_numeral k,`k:num`;
                      mk_small_numeral(256 * k),`m:num`]
                `256 * k + i = i + m`)) (0--(l-1)) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mld_polyvec_pointwise_acc_montgomery;
              MLD_MONTGOMERY_REDUCE_POINTWISE; accdef; o_THM;
              INT_CONG_RREM; MLD_MONT_INVERSE] THEN
  CONV_TAC(ONCE_DEPTH_CONV MLD_POLYVEC_DOT_CONV) THEN
  REWRITE_TAC norm THEN
  W(fun (asl,w) ->
    let tm = rand(lhand(rator(lhand w))) in
    let atoms = setify(find_terms
      (fun t -> is_comb t &&
                (rator t = `u:num->int32` || rator t = `v:num->int32`))
      tm) in
    let bth t =
      let hth = snd(find (fun (_,th) ->
        let c = concl th in
        is_forall c &&
        can (fun c -> rator(rand(rand(lhand(rand(snd(dest_forall c))))))
                      = rator t || failwith "") c) asl) in
      let lth = PROVE_HYP ith (UNDISCH(ARITH_RULE
                   (mk_imp(`i < 256`,mk_binop `(<)` (rand t) ntm)))) in
      MP (SPEC (rand t) hth) lth in
    MP_TAC(GEN_CONGBOUND_RULE (map bth atoms) tm)) THEN
  REWRITE_TAC[MLD_MONT_INVERSE] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
    INT_LINEAR_CONG_TAC;
    INT_ARITH_TAC];;

let MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L4_CONG = prove
 (`!(u:num->int32) v i.
        i < 256 /\
        (!j. j < 1024 ==> abs(ival(u j)) < &8380417) /\
        (!j. j < 1024 ==> abs(ival(v j)) < &94279689)
        ==> (ival(mld_polyvec_pointwise_acc_montgomery 4 u v i) ==
             mldsa_pointwise_acc_l4 (ival o u) (ival o v) i) (mod &8380417) /\
            abs(ival(mld_polyvec_pointwise_acc_montgomery 4 u v i))
            < &8380417`,
  MLD_POINTWISE_ACC_CONG_TAC mldsa_pointwise_acc_l4 4);;

let MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L5_CONG = prove
 (`!(u:num->int32) v i.
        i < 256 /\
        (!j. j < 1280 ==> abs(ival(u j)) < &8380417) /\
        (!j. j < 1280 ==> abs(ival(v j)) < &94279689)
        ==> (ival(mld_polyvec_pointwise_acc_montgomery 5 u v i) ==
             mldsa_pointwise_acc_l5 (ival o u) (ival o v) i) (mod &8380417) /\
            abs(ival(mld_polyvec_pointwise_acc_montgomery 5 u v i))
            < &8380417`,
  MLD_POINTWISE_ACC_CONG_TAC mldsa_pointwise_acc_l5 5);;

let MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L7_CONG = prove
 (`!(u:num->int32) v i.
        i < 256 /\
        (!j. j < 1792 ==> abs(ival(u j)) < &8380417) /\
        (!j. j < 1792 ==> abs(ival(v j)) < &94279689)
        ==> (ival(mld_polyvec_pointwise_acc_montgomery 7 u v i) ==
             mldsa_pointwise_acc_l7 (ival o u) (ival o v) i) (mod &8380417) /\
            abs(ival(mld_polyvec_pointwise_acc_montgomery 7 u v i))
            < &8380417`,
  MLD_POINTWISE_ACC_CONG_TAC mldsa_pointwise_acc_l7 7);;

(* ------------------------------------------------------------------------- *)
(* The explicit forms of the NTT and of its inverse (with its Montgomery     *)
(* factor 2^32) as mldsa_ntt and mldsa_ntt_inv of FIPS 204.                  *)
(* ------------------------------------------------------------------------- *)

let ARM_MLDSA_FORWARD_NTT_MLDSA_NTT = prove
 (`!a k. arm_mldsa_forward_ntt a k = mldsa_ntt (mldsa_poly a) k`,
  REWRITE_TAC[arm_mldsa_forward_ntt; MLDSA_NTT_MLDSA_POLY]);;

let MLDSA_NTT_ARM_FORWARD_NTT = prove
 (`!f k. f IN ring_carrier mldsa_rq
         ==> mldsa_ntt f k = arm_mldsa_forward_ntt (\i. coeff i f) k`,
  SIMP_TAC[arm_mldsa_forward_ntt; MLDSA_NTT_FORWARD]);;

let ARM_MLDSA_INVERSE_NTT_MLDSA_NTT_INV = prove
 (`!a k. k < 256
         ==> arm_mldsa_inverse_ntt a k =
             (&2 pow 32 * coeff k (mldsa_ntt_inv (\i. a i rem &8380417)))
             rem &8380417`,
  SIMP_TAC[arm_mldsa_inverse_ntt; MLDSA_NTT_INV_TOMONT]);;

(* ------------------------------------------------------------------------- *)
(* Two facts about R_q in the NTT domain: the inverse NTT is linear for      *)
(* scalars, and the dot product of the inverse NTTs of the rows of a matrix  *)
(* with a vector is the inverse NTT of the sums of the pointwise products.   *)
(* Also mld_caddq, which gives the representative in [0,q).                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NTT_INV_CMUL = prove
 (`!c a k.
        (!i. i < 256 ==> &0 <= a i /\ a i < &8380417) /\ k < 256
        ==> coeff k (mldsa_ntt_inv (\i. (c * a i) rem &8380417)) =
            (c * coeff k (mldsa_ntt_inv a)) rem &8380417`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLDSA_NTT_INV_COEFF o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[MLDSA_NTT_INV_COEFF] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!C x y c n:int. (x == c * y) (mod n)
                    ==> (C * x == c * (C * y)) (mod n)`) THEN
  REWRITE_TAC[GSYM ISUM_LMUL] THEN MATCH_MP_TAC INT_CONG_ISUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[INT_MUL_ASSOC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!x y w n:int. (x == y) (mod n) ==> (x * w == y * w) (mod n)`) THEN
  REWRITE_TAC[INT_REM_MOD_SELF]);;

let MLDSA_DOT_NTT_INV_ISUM = prove
 (`!n a v.
        (!j k. j < n /\ k < 256 ==> &0 <= a j k /\ a j k < &8380417) /\
        (!j. j < n ==> v j IN ring_carrier mldsa_rq)
        ==> mldsa_ntt_inv
             (\k. isum {j | j < n} (\j. a j k * mldsa_ntt (v j) k)
                  rem &8380417) =
            mldsa_dot n (\j. mldsa_ntt_inv (a j)) v`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_DOT_NTT_INV] THEN
  REWRITE_TAC[MLDSA_ZQ] THEN
  SIMP_TAC[MLDSA_ZQ_RING_SUM; FINITE_NUMSEG_LT]);;

let MLD_CADDQ_REM = prove
 (`!a:int32. abs(ival a) < &8380417
             ==> ival(mld_caddq a) = ival a rem &8380417`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[mld_caddq] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `word_add a (word 8380417):int32 = iword(ival a + &8380417)`
    SUBST1_TAC THENL
     [REWRITE_TAC[IWORD_INT_ADD; IWORD_IVAL; GSYM WORD_IWORD]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_INT_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[INT_REM_UNIQUE] THEN
    CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[int_congruent] THEN EXISTS_TAC `-- &1:int` THEN
    INT_ARITH_TAC;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_LT THEN
    ASM_INT_ARITH_TAC]);;

let MLD_POLY_CADDQ_REM = prove
 (`!(a:num->int32) i.
        abs(ival(a i)) < &8380417
        ==> ival(mld_poly_caddq a i) = ival(a i) rem &8380417`,
  SIMP_TAC[mld_poly_caddq; MLD_CADDQ_REM]);;

(* ------------------------------------------------------------------------- *)
(* The inverse NTT of an array congruent to 2^-32 * S is the inverse NTT of  *)
(* S (the Montgomery factors cancel); the C NTT represents mldsa_ntt of its  *)
(* input; the dot products of the C code; and the pointwise products.        *)
(* ------------------------------------------------------------------------- *)

let MLD_MONT_CANCEL = prove
 (`(&2 pow 32 * &(inverse_mod 8380417 4294967296) == &1:int) (mod &8380417)`,
  REWRITE_TAC[MLD_MONT_INVERSE; GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV);;

let MLD_FIPS204_INVNTT_MONT = prove
 (`!(P:num->int32) S.
        (!k. k < 256
             ==> abs(ival(P k)) < &8380417 /\
                 (ival(P k) == &(inverse_mod 8380417 4294967296) * S k)
                 (mod &8380417))
        ==> !n. n < 256
                ==> (ival(mld_poly_invntt_tomont P n) ==
                     coeff n (mldsa_ntt_inv (\k. S k rem &8380417)))
                    (mod &8380417) /\
                    abs(ival(mld_poly_invntt_tomont P n)) < &8380417`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `P:num->int32` MLD_POLY_INVNTT_TOMONT_CONG) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n < 256` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARM_MLDSA_INVERSE_NTT_MLDSA_NTT_INV] THEN
  SUBGOAL_THEN
   `mldsa_ntt_inv (\i. (ival o (P:num->int32)) i rem &8380417) =
    mldsa_ntt_inv
     (\i. (&(inverse_mod 8380417 4294967296) * (S i rem &8380417))
          rem &8380417)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLDSA_NTT_INV_EQ THEN REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[INT_REM_EQ] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `i < 256`)) THEN
    MP_TAC(SPECL [`(S:num->int) i`; `&8380417:int`] INT_REM_MOD_SELF) THEN
    SPEC_TAC(`&8380417:int`,`q:int`) THEN
    SPEC_TAC(`&(inverse_mod 8380417 4294967296):int`,`c:int`) THEN
    CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`&(inverse_mod 8380417 4294967296):int`;
    `\i. (S:num->int) i rem &8380417`; `n:num`] MLDSA_NTT_INV_CMUL)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC MLD_MONT_CANCEL THEN
  SPEC_TAC(`coeff n (mldsa_ntt_inv (\k. (S:num->int) k rem &8380417))`,
           `x:int`) THEN
  SPEC_TAC(`&(inverse_mod 8380417 4294967296):int`,`c:int`) THEN
  SPEC_TAC(`(&2 pow 32):int`,`t:int`) THEN
  SPEC_TAC(`&8380417:int`,`q:int`) THEN
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`c * x:int`; `q:int`] INT_REM_MOD_SELF) THEN
  MP_TAC(SPECL [`t * (c * x) rem q:int`; `q:int`] INT_REM_MOD_SELF) THEN
  CONV_TAC INTEGER_RULE);;

let MLD_FIPS204_POLY_NTT = prove
 (`!x:num->int32.
        (!i. i < 256 ==> abs(ival(x i)) < &8380417)
        ==> !k. k < 256
                ==> (ival(mld_poly_ntt x k) ==
                     mldsa_ntt (mldsa_poly (\i. ival(x i))) k)
                    (mod &8380417) /\
                    abs(ival(mld_poly_ntt x k)) < &94279689`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MLD_POLY_NTT_CONG) THEN
  REWRITE_TAC[ARM_MLDSA_FORWARD_NTT_MLDSA_NTT; o_DEF]);;

let MLD_FIPS204_POLYVEC_NTT = prove
 (`!l (x:num->int32).
        (!j. j < 256 * l ==> abs(ival(x j)) < &8380417)
        ==> !j m. j < l /\ m < 256
                  ==> (ival(mld_polyvec_map mld_poly_ntt x (256 * j + m)) ==
                       mldsa_ntt (mldsa_poly (\i. ival(x(256 * j + i)))) m)
                      (mod &8380417) /\
                      abs(ival(mld_polyvec_map mld_poly_ntt x (256 * j + m)))
                      < &94279689`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `m:num`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MLD_POLYVEC_MAP_COEFF] THEN
  MP_TAC(SPEC `mld_poly_of (x:num->int32) j` MLD_FIPS204_POLY_NTT) THEN
  REWRITE_TAC[mld_poly_of] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[]]);;

let MLDSA_POINTWISE_ACC_ISUM = prove
 (`(!f g i. mldsa_pointwise_acc_l4 f g i =
            (isum {j | j < 4} (\j. f(i + 256 * j) * g(i + 256 * j)) *
             &(inverse_mod 8380417 4294967296)) rem &8380417) /\
   (!f g i. mldsa_pointwise_acc_l5 f g i =
            (isum {j | j < 5} (\j. f(i + 256 * j) * g(i + 256 * j)) *
             &(inverse_mod 8380417 4294967296)) rem &8380417) /\
   (!f g i. mldsa_pointwise_acc_l7 f g i =
            (isum {j | j < 7} (\j. f(i + 256 * j) * g(i + 256 * j)) *
             &(inverse_mod 8380417 4294967296)) rem &8380417)`,
  REWRITE_TAC[mldsa_pointwise_acc_l4; mldsa_pointwise_acc_l5;
              mldsa_pointwise_acc_l7; NUMSEG_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_ISUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES]);;

(* The inverse NTT of the Montgomery dot product of a row u of the matrix    *)
(* in the NTT domain (values in [0,q), row j being the array of A_j^) with   *)
(* a vector v that represents the NTTs of polynomials Y_j (within the NTT    *)
(* bound) is congruent to the dot product sum_j A_j * Y_j in R_q.            *)

let MLD_FIPS204_INVNTT_ACC_TAC acccong l =
  let lt = mk_small_numeral l and nt = mk_small_numeral (256 * l) in
  let sub t = subst [lt,`l:num`; nt,`n:num`] t in
  let ubnd = sub
   `!j m. j < l /\ m < 256
          ==> &0 <= ival((u:num->int32)(256 * j + m)) /\
              ival(u(256 * j + m)) < &8380417`
  and vrep = sub
   `!j m. j < l /\ m < 256
          ==> (ival((v:num->int32)(256 * j + m)) ==
               mldsa_ntt ((Y:num->(1->num)->int) j) m) (mod &8380417) /\
              abs(ival(v(256 * j + m))) < &94279689`
  and sumc = sub `(isum {j | j < l}
      (\j. ival((u:num->int32)(k + 256 * j)) *
           ival((v:num->int32)(k + 256 * j))) ==
     isum {j | j < l}
      (\j. ival(u(256 * j + k)) * mldsa_ntt ((Y:num->(1->num)->int) j) k))
    (mod &8380417)`
  and atm = sub `isum {j | j < l}
      (\j. ival((u:num->int32)(k + 256 * j)) *
           ival((v:num->int32)(k + 256 * j)))`
  and btm = sub `isum {j | j < l}
      (\j. ival((u:num->int32)(256 * j + k)) *
           mldsa_ntt ((Y:num->(1->num)->int) j) k)`
  and ptm = sub `ival(mld_polyvec_pointwise_acc_montgomery l (u:num->int32)
                       (v:num->int32) k)` in
  let idx = ARITH_RULE(sub `i < n ==> i = 256 * (i DIV 256) + i MOD 256 /\
                                     i DIV 256 < l /\ i MOD 256 < 256`) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
    [lt; `\j k. ival((u:num->int32)(256 * j + k))`;
     `Y:num->(1->num)->int`] MLDSA_DOT_NTT_INV_ISUM)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MLD_FIPS204_INVNTT_MONT THEN BETA_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`u:num->int32`; `v:num->int32`; `k:num`] acccong) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN
    DISCH_THEN(MP_TAC o MATCH_MP idx) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC ubnd THEN
      DISCH_THEN(MP_TAC o SPECL [`i DIV 256`; `i MOD 256`]) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      UNDISCH_TAC vrep THEN
      DISCH_THEN(MP_TAC o SPECL [`i DIV 256`; `i MOD 256`]) THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[MLDSA_POINTWISE_ACC_ISUM; o_THM] THEN
  SUBGOAL_THEN sumc MP_TAC THENL
   [MATCH_MP_TAC INT_CONG_ISUM THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `k + 256 * j = 256 * j + k`] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!a b c n:int. (b == c) (mod n) ==> (a * b == a * c) (mod n)`) THEN
    UNDISCH_TAC vrep THEN DISCH_THEN(MP_TAC o SPECL [`j:num`; `k:num`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [mk_binop `( * ):int->int->int` atm
                 `&(inverse_mod 8380417 4294967296):int`; `&8380417:int`]
               INT_REM_MOD_SELF) THEN
  W(fun (asl,w) ->
    let r = find_term (fun t -> is_comb t && is_comb(rator t) &&
                                rator(rator t) = `(rem):int->int->int`) w in
    SPEC_TAC(r,`r:int`)) THEN
  SPEC_TAC(atm,`a:int`) THEN SPEC_TAC(btm,`b:int`) THEN
  SPEC_TAC(ptm,`p:int`) THEN
  SPEC_TAC(`&(inverse_mod 8380417 4294967296):int`,`c:int`) THEN
  SPEC_TAC(`&8380417:int`,`q:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE;;

let MLD_FIPS204_INVNTT_ACC_STMT l =
  subst [mk_small_numeral l,`l:num`]
  `!(u:num->int32) (v:num->int32) (Y:num->(1->num)->int).
        (!j m. j < l /\ m < 256
               ==> &0 <= ival(u(256 * j + m)) /\
                   ival(u(256 * j + m)) < &8380417) /\
        (!j. j < l ==> Y j IN ring_carrier mldsa_rq) /\
        (!j m. j < l /\ m < 256
               ==> (ival(v(256 * j + m)) == mldsa_ntt (Y j) m)
                   (mod &8380417) /\
                   abs(ival(v(256 * j + m))) < &94279689)
        ==> !k. k < 256
                ==> (ival(mld_poly_invntt_tomont
                       (mld_polyvec_pointwise_acc_montgomery l u v) k) ==
                     coeff k (mldsa_dot l
                       (\j. mldsa_ntt_inv (\m. ival(u(256 * j + m)))) Y))
                    (mod &8380417) /\
                    abs(ival(mld_poly_invntt_tomont
                       (mld_polyvec_pointwise_acc_montgomery l u v) k))
                    < &8380417`;;

let MLD_FIPS204_INVNTT_ACC_L4 = prove
 (MLD_FIPS204_INVNTT_ACC_STMT 4,
  MLD_FIPS204_INVNTT_ACC_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L4_CONG 4);;

let MLD_FIPS204_INVNTT_ACC_L5 = prove
 (MLD_FIPS204_INVNTT_ACC_STMT 5,
  MLD_FIPS204_INVNTT_ACC_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L5_CONG 5);;

let MLD_FIPS204_INVNTT_ACC_L7 = prove
 (MLD_FIPS204_INVNTT_ACC_STMT 7,
  MLD_FIPS204_INVNTT_ACC_TAC MLD_POLYVEC_POINTWISE_ACC_MONTGOMERY_L7_CONG 7);;

(* The inverse NTT of the pointwise Montgomery product of a and b, which     *)
(* represent the NTTs of f and g within the NTT bound, is congruent to the   *)
(* product f * g in R_q.                                                     *)

let MLD_FIPS204_INVNTT_POINTWISE = prove
 (`!(a:num->int32) (b:num->int32) f g.
        f IN ring_carrier mldsa_rq /\ g IN ring_carrier mldsa_rq /\
        (!k. k < 256 ==> (ival(a k) == mldsa_ntt f k) (mod &8380417) /\
                         abs(ival(a k)) < &94279689) /\
        (!k. k < 256 ==> (ival(b k) == mldsa_ntt g k) (mod &8380417) /\
                         abs(ival(b k)) < &94279689)
        ==> !k. k < 256
                ==> (ival(mld_poly_invntt_tomont
                       (mld_poly_pointwise_montgomery a b) k) ==
                     coeff k (ring_mul mldsa_rq f g)) (mod &8380417) /\
                    abs(ival(mld_poly_invntt_tomont
                       (mld_poly_pointwise_montgomery a b) k)) < &8380417`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM MLDSA_NTT_INV_MUL] THEN REWRITE_TAC[MLDSA_ZQ] THEN
  MATCH_MP_TAC MLD_FIPS204_INVNTT_MONT THEN BETA_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:num->int32`; `b:num->int32`; `k:num`]
               MLD_POLY_POINTWISE_MONTGOMERY_CONG) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[mldsa_pointwise; o_THM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl))) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(MP_TAC o CONJUNCT1)) THEN
  MP_TAC(SPECL [`ival((a:num->int32) k) * ival((b:num->int32) k) *
                 &(inverse_mod 8380417 4294967296)`; `&8380417:int`]
               INT_REM_MOD_SELF) THEN
  W(fun (asl,w) ->
    let r = find_term (fun t -> is_comb t && is_comb(rator t) &&
                                rator(rator t) = `(rem):int->int->int`) w in
    SPEC_TAC(r,`r:int`)) THEN
  SPEC_TAC(`ival((a:num->int32) k)`,`x:int`) THEN
  SPEC_TAC(`ival((b:num->int32) k)`,`y:int`) THEN
  SPEC_TAC(`mldsa_ntt (f:(1->num)->int) k`,`x':int`) THEN
  SPEC_TAC(`mldsa_ntt (g:(1->num)->int) k`,`y':int`) THEN
  SPEC_TAC(`ival(mld_poly_pointwise_montgomery (a:num->int32)
                  (b:num->int32) k)`,`p:int`) THEN
  SPEC_TAC(`&(inverse_mod 8380417 4294967296):int`,`c:int`) THEN
  SPEC_TAC(`&8380417:int`,`q:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE);;
