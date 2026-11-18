(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The arithmetic of mldsa-native's portable C code in the NTT domain up to  *)
(* congruence mod q = 8380417: the NTT, the inverse NTT and the pointwise    *)
(* products of common/mldsa_native_poly.ml and mldsa_native_polyvec.ml as    *)
(* the explicit forms of common/mlkem_mldsa.ml (arm_mldsa_forward_ntt, ...), *)
(* with bounds. These do not involve FIPS 204;                               *)
(* common/fips204/properties/mldsa_native_fips204_ntt.ml relates them to it. *)
(* ========================================================================= *)

needs "common/mlkem_mldsa.ml";;
needs "common/int_linear.ml";;
needs "common/mldsa_native_polyvec.ml";;

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

(* ------------------------------------------------------------------------- *)
(* Reduction (reduce.h): for a <= INT32_MAX - 2^22, the precondition of      *)
(* mld_reduce32, its result is congruent to a mod q and in [-6283009,        *)
(* 6283009), the range MLD_REDUCE32_RANGE_MAX of reduce.h (the bound         *)
(* -6283009 is reached, for a = -2143289344). And mld_caddq, which gives the *)
(* representative in [0,q).                                                  *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_REDUCE32 = prove
 (`!a:int32.
        ival a <= &2143289343
        ==> (ival(mld_reduce32 a) == ival a) (mod &8380417) /\
            --(&6283009) <= ival(mld_reduce32 a) /\
            ival(mld_reduce32 a) < &6283009`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `a:int32` IVAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
  ABBREV_TAC `t = (ival(a:int32) + &4194304) div &8388608` THEN
  SUBGOAL_THEN `--(&256) <= t /\ t:int <= &255` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    REWRITE_TAC[INT_ARITH `x <= &255 <=> x < &256:int`] THEN
    SIMP_TAC[INT_LE_DIV_EQ; INT_DIV_LT_EQ; INT_ARITH `&0:int < &8388608`] THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(mld_reduce32 a) = ival(a:int32) - t * &8380417`
  SUBST1_TAC THENL
   [REWRITE_TAC[mld_reduce32; WORD_RULE
     `word_sub (a:int32) (word_mul b (word 8380417)) =
      iword(ival a - ival b * &8380417)`] THEN
    REWRITE_TAC[IVAL_WORD_ISHR; WORD_RULE
     `word_add (a:int32) (word 4194304) = iword(ival a + &4194304)`] THEN
    SUBGOAL_THEN `ival(iword(ival(a:int32) + &4194304):int32) =
                  ival a + &4194304` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
      ASM_INT_ARITH_TAC;
      CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SPEC_TAC(`&8380417:int`,`n:int`) THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  MP_TAC(SPECL [`ival(a:int32) + &4194304`; `&8388608:int`] INT_DIVISION) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = --(&256):int` THEN ASM_INT_ARITH_TAC);;

let MLD_FIPS204_POLY_REDUCE = prove
 (`!(a:num->int32) i.
        ival(a i) <= &2143289343
        ==> (ival(mld_poly_reduce a i) == ival(a i)) (mod &8380417) /\
            --(&6283009) <= ival(mld_poly_reduce a i) /\
            ival(mld_poly_reduce a i) < &6283009`,
  SIMP_TAC[mld_poly_reduce; MLD_FIPS204_REDUCE32]);;

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
