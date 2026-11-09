(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation of mldsa-native and FIPS 204: for each parameter set, the  *)
(* public and secret keys that the specification of mldsa-native's key       *)
(* generation (mld_keypair_pk_44 etc. of common/mldsa_native_sign.ml) gives  *)
(* for a seed are those of mldsa_keygen_internal of common/fips204.ml,       *)
(* assuming that the rejection samplers of the C code terminate.             *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native_fips204_ntt.ml";;
needs "arm/proofs/utils/mldsa_native_fips204_sample.ml";;
needs "arm/proofs/utils/mldsa_native_fips204_round.ml";;
needs "arm/proofs/utils/mldsa_native_fips204_pack.ml";;

(* ------------------------------------------------------------------------- *)
(* Extensionality of mldsa_poly and mldsa_dot, the ranges of Power2Round,    *)
(* and exact 32-bit addition.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLY_EXT = prove
 (`!a b. (!m. m < 256 ==> a m = b m) ==> mldsa_poly a = mldsa_poly b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_poly; FUN_EQ_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let MLDSA_DOT_EQ = prove
 (`!n f g u v. (!j. j < n ==> f j = g j /\ u j = v j)
               ==> mldsa_dot n f u = mldsa_dot n g v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_dot] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

let MLDSA_POWER2ROUND_BOUNDS = prove
 (`!r. &0 <= FST(mldsa_power2round r) /\
       FST(mldsa_power2round r) < &1024 /\
       --(&4096) < SND(mldsa_power2round r) /\
       SND(mldsa_power2round r) <= &4096 /\
       (&8192 * FST(mldsa_power2round r) + SND(mldsa_power2round r) ==
        r) (mod &8380417)`,
  GEN_TAC THEN REWRITE_TAC[mldsa_power2round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPEC `r:int` MLDSA_REM_Q) THEN
  SPEC_TAC(`r rem &8380417`,`rp:int`) THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rp:int`; `8192`] MLDSA_MODPM) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`mldsa_modpm rp 8192`,`r0:int`) THEN GEN_TAC THEN
  REWRITE_TAC[int_congruent] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `d:int`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `rp - r0:int = &8192 * --d` SUBST1_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[INT_DIV_MUL; INT_ARITH `~(&8192:int = &0)`] THEN
  REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
   [ASM_INT_ARITH_TAC;
    ASM_INT_ARITH_TAC;
    ASM_INT_ARITH_TAC;
    ASM_INT_ARITH_TAC;
    UNDISCH_TAC `(rp == r:int) (mod &8380417)` THEN
    REWRITE_TAC[int_congruent] THEN STRIP_TAC THEN
    EXISTS_TAC `d':int` THEN ASM_INT_ARITH_TAC]);;

let MLD_FIPS204_IVAL_WORD_ADD = prove
 (`!x y:int32.
        --(&2147483648) <= ival x + ival y /\ ival x + ival y < &2147483648
        ==> ival(word_add x y) = ival x + ival y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add x y:int32 = iword(ival x + ival y)` SUBST1_TAC THENL
   [REWRITE_TAC[IWORD_INT_ADD; IWORD_IVAL]; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* One coefficient of t = A s1 + s2 as mld_compute_t computes it: row i of   *)
(* the matrix expanded from rho, s1hat representing the NTTs of S1, and the  *)
(* unpacked polynomial i of s2 within q, for l = 4, 5 and 7.                 *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_COMPUTE_T_STMT l =
  subst [mk_small_numeral l,`l:num`]
  `!k (unpack:(num->byte)->num->int32) p rho (s1hat:num->int32)
     (s2:num->byte) (S1:num->(1->num)->int) i n.
        mld_matrix_terminates k l rho /\ rho < 2 EXP 256 /\ k <= 256 /\
        i < k /\ n < 256 /\
        (!j. j < l ==> S1 j IN ring_carrier mldsa_rq) /\
        (!j m. j < l /\ m < 256
               ==> (ival(s1hat(256 * j + m)) == mldsa_ntt (S1 j) m)
                   (mod &8380417) /\
                   abs(ival(s1hat(256 * j + m))) < &94279689) /\
        (!m. m < 256 ==> abs(ival(unpack (\t. s2(p * i + t)) m)) < &8380417)
        ==> ival(mld_compute_t l unpack p rho s1hat s2 (256 * i + n)) =
            coeff n (ring_add mldsa_rq
                      (mldsa_dot l (mldsa_expand_a (bytelist_of_num 32 rho) i)
                                 S1)
                      (mldsa_poly (\m. ival(unpack (\t. s2(p * i + t)) m))))`;;

let MLD_FIPS204_COMPUTE_T_TAC accth l =
  let lt = mk_small_numeral l in
  let sub t = subst [lt,`l:num`] t in
  let uabbr = sub `u = \j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j)`
  and uback = sub `(\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j)) =
                   (u:num->int32)`
  and idx = ARITH_RULE(sub
     `(256 * l) * i + 256 * j + m = 256 * (l * i + j) + m`)
  and dotsub = sub
   `mldsa_dot l (mldsa_expand_a (bytelist_of_num 32 rho) i) S1 =
    mldsa_dot l (\j. mldsa_ntt_inv (\m. ival((u:num->int32)(256 * j + m))))
              S1`
  and dtm = sub `coeff n (mldsa_dot l
     (\j. mldsa_ntt_inv (\m. ival((u:num->int32)(256 * j + m))))
     (S1:num->(1->num)->int))`
  and xabbr = sub `X = mld_poly_invntt_tomont
                        (mld_polyvec_pointwise_acc_montgomery l u s1hat)`
  and ufree t = free_in `U:num->int32` (concl t) && is_forall (concl t) in
  let rowfacts = sub
   `!j m. j < l /\ m < 256
          ==> ival((u:num->int32)(256 * j + m)) =
              mldsa_rej_ntt_poly
               (APPEND (bytelist_of_num 32 rho) [word j; word i]) m /\
              &(val(u(256 * j + m))) = ival(u(256 * j + m)) /\
              &0 <= ival(u(256 * j + m)) /\ ival(u(256 * j + m)) < &8380417` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mld_compute_t] THEN ASM_SIMP_TAC[MLD_POLYVEC_COEFF] THEN
  ABBREV_TAC uabbr THEN
  ABBREV_TAC `U = unpack (\t. (s2:num->byte)(p * i + t)):num->int32` THEN
  SUBGOAL_THEN rowfacts ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`j:num`; `m:num`] THEN STRIP_TAC THEN
    EXPAND_TAC "u" THEN BETA_TAC THEN REWRITE_TAC[idx] THEN
    MP_TAC(SPECL [`k:num`; lt; `rho:num`; `i:num`; `j:num`; `m:num`]
                 MLD_FIPS204_MATRIX_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[MLDSA_REJ_NTT_POLY_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`u:num->int32`; `s1hat:num->int32`; `S1:num->(1->num)->int`]
               accth) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(MP_TAC o SPEC `n:num`)] THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC xabbr THEN STRIP_TAC THEN
  SUBGOAL_THEN dotsub SUBST1_TAC THENL
   [MATCH_MP_TAC MLDSA_DOT_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN BETA_TAC THEN
    MP_TAC(SPECL [`k:num`; lt; `rho:num`; `i:num`; `j:num`]
                 MLD_FIPS204_EXPAND_A) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC MLDSA_NTT_INV_EQ THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    BETA_TAC THEN UNDISCH_THEN uback (fun th -> REWRITE_TAC[GSYM th]) THEN
    BETA_TAC THEN REWRITE_TAC[idx] THEN
    MP_TAC(SPECL [`k:num`; lt; `rho:num`; `i:num`; `j:num`; `m:num`]
                 MLD_FIPS204_MATRIX_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(mld_poly_add X U n) = ival((X:num->int32) n) + ival((U:num->int32) n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mld_poly_add] THEN MATCH_MP_TAC MLD_FIPS204_IVAL_WORD_ADD THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check ufree) THEN
    UNDISCH_TAC `abs(ival((X:num->int32) n)) < &8380417` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`mld_poly_add X U`; `n:num`] MLD_FIPS204_POLY_REDUCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check ufree) THEN
    UNDISCH_TAC `abs(ival((X:num->int32) n)) < &8380417` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    STRIP_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_POLY_CADDQ_REM o lhand o snd) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[MLDSA_RQ_COEFF_ADD; MLDSA_DOT_IN_RQ; MLDSA_POLY_IN_RQ] THEN
  ASM_REWRITE_TAC[COEFF_MLDSA_POLY; INT_REM_EQ] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `(x:int == y) (mod n)`) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ival((U:num->int32) n)`; `&8380417:int`] INT_REM_MOD_SELF) THEN
  SPEC_TAC(`ival((U:num->int32) n) rem &8380417`,`r:int`) THEN
  SPEC_TAC(dtm,`d:int`) THEN
  SPEC_TAC(`ival(mld_poly_reduce (mld_poly_add X U) n)`,`a:int`) THEN
  SPEC_TAC(`ival((X:num->int32) n)`,`x:int`) THEN
  SPEC_TAC(`ival((U:num->int32) n)`,`y:int`) THEN
  SPEC_TAC(`&8380417:int`,`q:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE;;

let MLD_FIPS204_COMPUTE_T_L4 = prove
 (MLD_FIPS204_COMPUTE_T_STMT 4,
  MLD_FIPS204_COMPUTE_T_TAC MLD_FIPS204_INVNTT_ACC_L4 4);;

let MLD_FIPS204_COMPUTE_T_L5 = prove
 (MLD_FIPS204_COMPUTE_T_STMT 5,
  MLD_FIPS204_COMPUTE_T_TAC MLD_FIPS204_INVNTT_ACC_L5 5);;

let MLD_FIPS204_COMPUTE_T_L7 = prove
 (MLD_FIPS204_COMPUTE_T_STMT 7,
  MLD_FIPS204_COMPUTE_T_TAC MLD_FIPS204_INVNTT_ACC_L7 7);;

(* ------------------------------------------------------------------------- *)
(* The seeds: the 128 bytes H(xi || k || l) and the numbers rho and rho'     *)
(* that the C code takes from them.                                          *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_KEYPAIR_SEEDBUF = prove
 (`!k l seed.
        seed < 2 EXP 256 /\ k < 256 /\ l < 256
        ==> mld_keypair_seedbuf k l seed =
            shake256 (APPEND (bytelist_of_num 32 seed) [word k; word l])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_keypair_seedbuf] THEN
  MP_TAC(SPECL [`seed:num`; `l:num`; `k:num`] MLD_FIPS204_MATRIX_SEED) THEN
  ASM_REWRITE_TAC[mld_matrix_seed] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MLD_FIPS204_SHAKE256_BYTE]);;

let MLD_FIPS204_KEYPAIR_RHO = prove
 (`!k l seed. bytelist_of_num 32 (mld_keypair_rho k l seed) =
              list_of_seq (mld_keypair_seedbuf k l seed) 32 /\
              bytelist_of_num 64 (mld_keypair_rhoprime k l seed) =
              list_of_seq (\j. mld_keypair_seedbuf k l seed (32 + j)) 64`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_keypair_rho; mld_keypair_rhoprime] THEN
  CONJ_TAC THEN
  W(fun (asl,w) -> MP_TAC(ISPEC (rand(rand(lhand w)))
                    BYTELIST_OF_NUM_OF_BYTELIST)) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ]);;

(* ------------------------------------------------------------------------- *)
(* The keys. The proof is the same for the three parameter sets, given by    *)
(* the definitions of the parameter set, of the C keys and of the            *)
(* termination condition, and the lemmas for the packing of s1 and s2 and    *)
(* for compute_t. MLD_FIPS204_KEYPAIR_INST instantiates the variables of a   *)
(* term that the table of a parameter set names: k, l, eta, the length p of  *)
(* a packed polynomial of s1 or s2 and the lengths derived from them, and    *)
(* the C functions.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_ENCODE_SUBST_TAC pat target tac =
  W(fun (asl,w) ->
    let t = find_term (fun t -> can (term_match [] pat) t) w in
    SUBGOAL_THEN (mk_eq(t,target)) SUBST1_TAC THENL
     [MATCH_MP_TAC MLDSA_ENCODE_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      BETA_TAC THEN tac;
      ALL_TAC]);;

let MLD_FIPS204_TFACT_TAC =
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
    check (fun th -> is_forall(concl th) &&
                     free_in `mldsa_power2round` (concl th) &&
                     free_in `TT:num->int32` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC);;

let MLD_FIPS204_SFACT_TAC itm =
  FIRST_X_ASSUM(MP_TAC o SPEC itm o
    check (fun th -> is_forall(concl th) &&
                     free_in `mldsa_rej_bounded_poly` (concl th) &&
                     not(free_in `TT:num->int32` (concl th)))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (MP_TAC o SPEC `n MOD 256`)) THEN
  REWRITE_TAC[COEFF_MLDSA_POLY; MOD_LT_EQ; ARITH_EQ; MLDSA_MODPM_REM] THEN
  REWRITE_TAC[ARITH_RULE `256 * (a + n DIV 256) + n MOD 256 = 256 * a + n /\
                          256 * n DIV 256 + n MOD 256 = n`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MLDSA_MODPM_SMALL THEN
  ASM_INT_ARITH_TAC;;

let MLD_FIPS204_KEYPAIR_TABLE (params_def,pk_def,sk_def,term_def) =
  match snd(strip_comb(rhs(concl pk_def))) with
    [eta_tm; k_tm; l_tm; pack; unpack; p_tm] ->
      let eta = dest_small_numeral eta_tm and k = dest_small_numeral k_tm
      and l = dest_small_numeral l_tm and p = dest_small_numeral p_tm in
      map (fun (s,n) -> s,mk_small_numeral n)
       ["k",k; "l",l; "eta",eta; "p",p; "c",(if eta = 2 then 3 else 4);
        "kl",k + l; "nk",256 * k; "nl",256 * l; "nkl",256 * (k + l);
        "pl",p * l; "pk",p * k; "t1b",320 * k; "pkb",32 + 320 * k;
        "t0b",416 * k; "skb",128 + p * (k + l) + 416 * k;
        "s2off",128 + p * l; "s2end",128 + p * (k + l)] @
      ["params",lhs(concl params_def); "pkf",lhs(concl pk_def);
       "skf",lhs(concl sk_def); "kpterm",lhs(concl term_def);
       "pack",pack; "unpack",unpack]
  | _ -> failwith "MLD_FIPS204_KEYPAIR_TABLE";;

let MLD_FIPS204_KEYPAIR_INST tab tm =
  let inst v =
    match filter (fun (s,_) -> s = name_of v) tab with
      [] -> []
    | (_,t)::_ -> if type_of t = type_of v then [t,v]
                  else failwith ("MLD_FIPS204_KEYPAIR_INST: " ^ name_of v) in
  if type_vars_in_term tm <> [] then failwith "MLD_FIPS204_KEYPAIR_INST"
  else vsubst (flat (map inst (frees tm))) tm;;

let MLD_FIPS204_KEYPAIR_TAC defs (etapack_th,etaunpack_th,computet_th) =
  let params_def,pk_def,sk_def,term_def = defs in
  let tab = MLD_FIPS204_KEYPAIR_TABLE defs in
  let kp = MLD_FIPS204_KEYPAIR_INST tab in
  let k_tm = assoc "k" tab and l_tm = assoc "l" tab
  and eta_tm = assoc "eta" tab and p_tm = assoc "p" tab
  and kl_tm = assoc "kl" tab and nkl_tm = assoc "nkl" tab
  and pack_tm = assoc "pack" tab and unpack_tm = assoc "unpack" tab
  and pkf_tm = assoc "pkf" tab in
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[params_def; mldsa_keygen_internal; mldsa_h] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   (kp `shake256 (APPEND (bytelist_of_num 32 seed) [word k; word l]) =
    mld_keypair_seedbuf k l seed`)
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MLD_FIPS204_KEYPAIR_SEEDBUF THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[MLD_FIPS204_SLICE_LIST_OF_SEQ; ARITH] THEN
  ABBREV_TAC (kp `SB = mld_keypair_seedbuf k l seed`) THEN
  REWRITE_TAC[ADD_CLAUSES; ETA_AX] THEN
  MP_TAC(SPECL [k_tm; l_tm; `seed:num`] MLD_FIPS204_KEYPAIR_RHO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  ABBREV_TAC (kp `R = mld_keypair_rho k l seed`) THEN
  ABBREV_TAC (kp `RP = mld_keypair_rhoprime k l seed`) THEN
  ABBREV_TAC (kp `S = mld_keypair_s eta k l seed`) THEN
  SUBGOAL_THEN `RP < 2 EXP 512 /\ R < 2 EXP 256` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["RP"; "R"] THEN
    REWRITE_TAC[mld_keypair_rho; mld_keypair_rhoprime] THEN
    CONJ_TAC THEN
    W(MP_TAC o PART_MATCH lhand NUM_OF_BYTELIST_BOUND o lhand o snd) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[];
    ALL_TAC] THEN

  (*** The polynomials of s1 and s2 as sampled by the C code ***)

  SUBGOAL_THEN
   (kp `!i. i < kl
        ==> mldsa_rej_bounded_poly eta
              (APPEND (bytelist_of_num 64 RP) (bytelist_of_num 2 i)) =
            mldsa_poly (\m. ival((S:num->int32)(256 * i + m))) /\
            (!m. m < 256 ==> abs(ival(S(256 * i + m))) <= &eta)`)
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN(kp `!m. m < 256 ==> (S:num->int32)(256 * i + m) =
                      mld_poly_uniform_eta eta RP (word i) m`)
    ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN SIMP_TAC[mld_keypair_s; MLD_POLYVEC_COEFF] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word i:byte) = i` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     (kp `mld_rej_eta_terminates eta
       (mld_shake256_stream 66 (RP + 2 EXP 512 * val(word i:byte)))`)
    ASSUME_TAC THENL
     [UNDISCH_TAC (kp `(kpterm:num->bool) seed`) THEN
      ASM_REWRITE_TAC[term_def; mld_keypair_terminates] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [eta_tm; `RP:num`; `word i:byte`]
                   MLD_FIPS204_POLY_UNIFORM_ETA) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MLDSA_POLY_EXT THEN ASM_SIMP_TAC[];
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      MP_TAC(SPECL [eta_tm; `RP:num`; `word i:byte`; `m:num`]
                   MLD_FIPS204_POLY_UNIFORM_ETA_BOUND) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN(kp `!j. j < nkl ==> abs(ival((S:num->int32) j)) <= &eta`)
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(ARITH_RULE(kp `j < nkl ==> j = 256 * (j DIV 256) + j MOD 256 /\
                                   j DIV 256 < kl /\ j MOD 256 < 256`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j DIV 256` o
      check (fun th -> is_forall(concl th) &&
                       free_in `mldsa_rej_bounded_poly` (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN

  (*** Unpacking the packed s2 gives back s2 ***)

  SUBGOAL_THEN
   (kp `!i m. i < kl /\ m < 256
          ==> unpack
               (\t. mld_polyvec_pack p pack S
                     (p * i + t)) m =
              (S:num->int32)(256 * i + m)`)
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM MLD_POLYVEC_UNPACK_COEFF] THEN
    MATCH_MP_TAC etaunpack_th THEN
    EXISTS_TAC kl_tm THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
      check (fun th -> is_forall(concl th) &&
                       free_in nkl_tm (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; INT_ARITH_TAC];
    ALL_TAC] THEN

  (*** The coefficients of t ***)

  ABBREV_TAC (kp `TT = mld_keypair_t eta k l pack
                    unpack p seed`) THEN
  SUBGOAL_THEN
   (kp `!i n. i < k /\ n < 256
          ==> ival((TT:num->int32)(256 * i + n)) =
              coeff n (ring_add mldsa_rq
                (mldsa_dot l (mldsa_expand_a (bytelist_of_num 32 R) i)
                  (\j. mldsa_rej_bounded_poly eta
                        (APPEND (bytelist_of_num 64 RP) (bytelist_of_num 2 j))))
                (mldsa_rej_bounded_poly eta
                  (APPEND (bytelist_of_num 64 RP)
                          (bytelist_of_num 2 (l + i)))))`)
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    EXPAND_TAC "TT" THEN REWRITE_TAC[mld_keypair_t] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [l_tm; `S:num->int32`] MLD_FIPS204_POLYVEC_NTT) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
        check (fun th -> is_forall(concl th) &&
                         free_in nkl_tm (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; INT_ARITH_TAC];
      DISCH_TAC] THEN
    MP_TAC(BETA_RULE(SPECL
     [k_tm; unpack_tm; p_tm; `R:num`;
      `mld_polyvec_map mld_poly_ntt (S:num->int32)`;
      (kp `\j. mld_polyvec_pack p pack (S:num->int32)
            (l * p + j)`);
      `\j. mldsa_poly (\m. ival((S:num->int32)(256 * j + m)))`;
      `i:num`; `n:num`] computet_th)) THEN
    REWRITE_TAC[ARITH_RULE(kp `l * p + p * i + t = p * (l + i) + t`)] THEN
    ASM_SIMP_TAC[MLDSA_POLY_IN_RQ; ARITH_RULE(kp `i < k ==> l + i < kl`);
                 ARITH_RULE(kp `k <= 256`)] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC(kp `256 * (l + i) + m`) o
        check (fun th -> is_forall(concl th) && free_in nkl_tm (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; INT_ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN BINOP_TAC THENL
     [MATCH_MP_TAC MLDSA_DOT_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
        check (fun th -> is_forall(concl th) &&
                         free_in `mldsa_rej_bounded_poly` (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC MLDSA_POLY_EXT THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      BETA_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [(kp `l + i`); `m:num`] o
        check (fun th -> free_in unpack_tm (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN

  (*** Their ranges and Power2Round ***)

  SUBGOAL_THEN
   (kp `!n. n < nk
        ==> ival((TT:num->int32) n) =
            coeff (n MOD 256) (ring_add mldsa_rq
                (mldsa_dot l (mldsa_expand_a (bytelist_of_num 32 R) (n DIV 256))
                  (\j. mldsa_rej_bounded_poly eta
                        (APPEND (bytelist_of_num 64 RP) (bytelist_of_num 2 j))))
                (mldsa_rej_bounded_poly eta
                  (APPEND (bytelist_of_num 64 RP)
                          (bytelist_of_num 2 (l + n DIV 256))))) /\
            &0 <= ival(TT n) /\ ival(TT n) < &8380417 /\
            (ival(mld_power2round_hi(TT n)),ival(mld_power2round_lo(TT n))) =
            mldsa_power2round(ival(TT n))`)
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n DIV 256`; `n MOD 256`] o
      check (fun th -> is_forall(concl th) &&
                       free_in `TT:num->int32` (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `256 * n DIV 256 + n MOD 256 = n`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
    MATCH_MP_TAC(TAUT `(p /\ q) /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MLDSA_RQ_COEFF THEN
      SIMP_TAC[RING_ADD; MLDSA_DOT_IN_RQ; MLDSA_REJ_BOUNDED_POLY_IN_RQ];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN STRIP_TAC THEN
      MATCH_MP_TAC MLD_FIPS204_POWER2ROUND THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN

  (*** The public key ***)

  MP_TAC(SPECL [k_tm; l_tm; `seed:num`] MLD_FIPS204_KEYPAIR_RHO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   (kp `list_of_seq ((pkf:num->num->byte) seed) pkb =
    APPEND (bytelist_of_num 32 R)
     (mldsa_encode 10 nk (\n. ival(mld_power2round_hi((TT:num->int32) n))))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[pk_def; mld_keypair_pk] THEN
    ASM_REWRITE_TAC[ARITH_RULE(kp `pkb = 32 + t1b`); MLD_LIST_OF_SEQ_ADD] THEN
    BINOP_TAC THENL
     [MATCH_MP_TAC LIST_OF_SEQ_EQ THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `~(32 + k < 32) /\ (32 + k) - 32 = k`] THEN
    REWRITE_TAC[ETA_AX] THEN
    MP_TAC(SPECL [k_tm;
     `mld_polyvec_map mld_poly_power2round_hi (TT:num->int32)`]
     MLD_FIPS204_POLYVEC_T1_PACK) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN
     (kp `!i. i < nk
          ==> ival(mld_polyvec_map mld_poly_power2round_hi
                    (TT:num->int32) i) =
              ival(mld_power2round_hi(TT i))`)
    ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`mld_poly_power2round_hi`; `TT:num->int32`;
                     `i DIV 256`; `i MOD 256`] MLD_POLYVEC_MAP_COEFF) THEN
      REWRITE_TAC[MOD_LT_EQ; ARITH_EQ;
                  ARITH_RULE `256 * i DIV 256 + i MOD 256 = i`] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[mld_poly_power2round_hi; mld_poly_of] THEN
      REWRITE_TAC[ARITH_RULE `256 * i DIV 256 + i MOD 256 = i`];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
        check (fun th -> is_forall(concl th) &&
                         free_in `mldsa_power2round` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `ival((TT:num->int32) i)` MLDSA_POWER2ROUND_BOUNDS) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[FST; SND] THEN
      SIMP_TAC[];
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MLDSA_ENCODE_EQ THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MLD_FIPS204_ENCODE_SUBST_TAC
   (kp `mldsa_encode 10 nk f`)
   (kp `mldsa_encode 10 nk (\n. ival(mld_power2round_hi((TT:num->int32) n)))`)
   (MLD_FIPS204_TFACT_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      free_in `mldsa_power2round` (concl th) && is_eq(concl th) &&
      not(is_forall(concl th)))) THEN
    REWRITE_TAC[FST]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    free_in pkf_tm (concl th))) THEN
  REWRITE_TAC[PAIR_EQ] THEN

  (*** The secret key: s1, s2 and t0 as the C code packs them ***)

  REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN
  SUBGOAL_THEN
   (kp `mldsa_encode c nl
     (\n. &eta - mldsa_modpm (coeff (n MOD 256)
       (mldsa_rej_bounded_poly eta
         (APPEND (bytelist_of_num 64 RP) (bytelist_of_num 2 (n DIV 256)))))
        8380417) =
    mldsa_encode c nl (\n. &eta - ival((S:num->int32) n))`)
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLDSA_ENCODE_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    BETA_TAC THEN MLD_FIPS204_SFACT_TAC `n DIV 256`;
    ALL_TAC] THEN
  SUBGOAL_THEN
   (kp `mldsa_encode c nk
     (\n. &eta - mldsa_modpm (coeff (n MOD 256)
       (mldsa_rej_bounded_poly eta
         (APPEND (bytelist_of_num 64 RP)
                 (bytelist_of_num 2 (l + n DIV 256)))))
        8380417) =
    mldsa_encode c nk (\n. &eta - ival((S:num->int32) (nl + n)))`)
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLDSA_ENCODE_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    BETA_TAC THEN MLD_FIPS204_SFACT_TAC (kp `l + n DIV 256`);
    ALL_TAC] THEN
  MLD_FIPS204_ENCODE_SUBST_TAC
   (kp `mldsa_encode 13 nk f`)
   (kp `mldsa_encode 13 nk
     (\n. &4096 - ival(mld_power2round_lo((TT:num->int32) n)))`)
   (MLD_FIPS204_TFACT_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      free_in `mldsa_power2round` (concl th) && is_eq(concl th) &&
      not(is_forall(concl th)))) THEN
    REWRITE_TAC[SND]) THEN

  (*** The C secret key, piece by piece ***)

  REWRITE_TAC[sk_def; mld_keypair_sk] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM pk_def] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE(kp `skb = 32 + 32 + 64 + pl + pk + t0b`);
              MLD_LIST_OF_SEQ_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  BINOP_TAC THENL
   [CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN SIMP_TAC[];
    ALL_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC LIST_OF_SEQ_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 32 ==> ~(32 + i < 32) /\ 32 + i < 64`] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   (kp `mld_shake256_byte pkb
     (num_of_bytelist(list_of_seq ((pkf:num->num->byte) seed) pkb)) =
    shake256 (list_of_seq ((pkf:num->num->byte) seed) pkb)`)
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) MLD_FIPS204_SHAKE256_BYTE o
      lhand o snd) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPEC(kp `list_of_seq ((pkf:num->num->byte) seed) pkb`)
                   NUM_OF_BYTELIST_BOUND) THEN
      REWRITE_TAC[LENGTH_LIST_OF_SEQ; EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPEC(kp `list_of_seq ((pkf:num->num->byte) seed) pkb`)
                 BYTELIST_OF_NUM_OF_BYTELIST) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN SIMP_TAC[];
    ALL_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC LIST_OF_SEQ_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 64 ==> ~(64 + i < 32) /\ ~(64 + i < 64) /\
                                         64 + i < 128 /\ (64 + i) - 64 = i`];
    ALL_TAC] THEN
  BINOP_TAC THENL
   [MP_TAC(SPECL [l_tm; `S:num->int32`] etapack_th) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
        check (fun th -> is_forall(concl th) && free_in nkl_tm (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; INT_ARITH_TAC];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE(kp
     `i < pl ==> ~(128 + i < 32) /\ ~(128 + i < 64) /\ ~(128 + i < 128) /\
                 128 + i < s2end /\ (128 + i) - 128 = i`)];
    ALL_TAC] THEN
  BINOP_TAC THENL
   [MP_TAC(SPECL [k_tm; (kp `\n. (S:num->int32)(nl + n)`)]
                 etapack_th) THEN
    CONV_TAC NUM_REDUCE_CONV THEN BETA_TAC THEN ANTS_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC(kp `nl + i`) o
        check (fun th -> is_forall(concl th) && free_in nkl_tm (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; INT_ARITH_TAC];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE(kp `i < pk ==> ~(s2off + i < 32) /\
                  ~(s2off + i < 64) /\ ~(s2off + i < 128) /\
                  s2off + i < s2end /\ (s2off + i) - 128 = pl + i`)] THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL
      [p_tm; pack_tm; `S:num->int32`; l_tm; `i:num`]
      MLD_FIPS204_POLYVEC_PACK_SHIFT)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN

  (*** t0 ***)

  SUBGOAL_THEN
   (kp `!i. i < nk
        ==> ival(mld_polyvec_map mld_poly_power2round_lo
                  (TT:num->int32) i) =
            ival(mld_power2round_lo(TT i))`)
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`mld_poly_power2round_lo`; `TT:num->int32`;
                   `i DIV 256`; `i MOD 256`] MLD_POLYVEC_MAP_COEFF) THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ;
                ARITH_RULE `256 * i DIV 256 + i MOD 256 = i`] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[mld_poly_power2round_lo; mld_poly_of] THEN
    REWRITE_TAC[ARITH_RULE `256 * i DIV 256 + i MOD 256 = i`];
    ALL_TAC] THEN
  MP_TAC(SPECL [k_tm;
                `mld_polyvec_map mld_poly_power2round_lo (TT:num->int32)`]
               MLD_FIPS204_POLYVEC_T0_PACK) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
      check (fun th -> is_forall(concl th) &&
                       free_in `mldsa_power2round` (concl th) &&
                       free_in `TT:num->int32` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC `ival((TT:num->int32) i)` MLDSA_POWER2ROUND_BOUNDS) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      free_in `mldsa_power2round` (concl th) && is_eq(concl th) &&
      not(is_forall(concl th)))) THEN
    REWRITE_TAC[FST; SND] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  TRANS_TAC EQ_TRANS (kp `mldsa_encode 13 nk
    (\i. &4096 - ival(mld_polyvec_map mld_poly_power2round_lo
                        (TT:num->int32) i))`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MLDSA_ENCODE_EQ THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      free_in `mld_polyt0_pack` (concl th))) THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE(kp `i < t0b ==> ~(s2end + i < 32) /\
                  ~(s2end + i < 64) /\ ~(s2end + i < 128) /\
                  ~(s2end + i < s2end) /\ (s2end + i) - s2end = i`)]];;

let MLD_FIPS204_KEYPAIR_44 = prove
 (`!seed. seed < 2 EXP 256 /\
          mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 seed) /\
          mld_keypair_terminates_44 seed
          ==> mldsa_keygen_internal mldsa44 (bytelist_of_num 32 seed) =
              (list_of_seq (mld_keypair_pk_44 seed) 1312,
               list_of_seq (mld_keypair_sk_44 seed) 2560)`,
  MLD_FIPS204_KEYPAIR_TAC
   (mldsa44,mld_keypair_pk_44,mld_keypair_sk_44,mld_keypair_terminates_44)
   (MLD_FIPS204_POLYVEC_ETA_PACK_2,MLD_FIPS204_POLYVEC_ETA_UNPACK_PACK_2,
    MLD_FIPS204_COMPUTE_T_L4));;

let MLD_FIPS204_KEYPAIR_65 = prove
 (`!seed. seed < 2 EXP 256 /\
          mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 seed) /\
          mld_keypair_terminates_65 seed
          ==> mldsa_keygen_internal mldsa65 (bytelist_of_num 32 seed) =
              (list_of_seq (mld_keypair_pk_65 seed) 1952,
               list_of_seq (mld_keypair_sk_65 seed) 4032)`,
  MLD_FIPS204_KEYPAIR_TAC
   (mldsa65,mld_keypair_pk_65,mld_keypair_sk_65,mld_keypair_terminates_65)
   (MLD_FIPS204_POLYVEC_ETA_PACK_4,MLD_FIPS204_POLYVEC_ETA_UNPACK_PACK_4,
    MLD_FIPS204_COMPUTE_T_L5));;

let MLD_FIPS204_KEYPAIR_87 = prove
 (`!seed. seed < 2 EXP 256 /\
          mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 seed) /\
          mld_keypair_terminates_87 seed
          ==> mldsa_keygen_internal mldsa87 (bytelist_of_num 32 seed) =
              (list_of_seq (mld_keypair_pk_87 seed) 2592,
               list_of_seq (mld_keypair_sk_87 seed) 4896)`,
  MLD_FIPS204_KEYPAIR_TAC
   (mldsa87,mld_keypair_pk_87,mld_keypair_sk_87,mld_keypair_terminates_87)
   (MLD_FIPS204_POLYVEC_ETA_PACK_2,MLD_FIPS204_POLYVEC_ETA_UNPACK_PACK_2,
    MLD_FIPS204_COMPUTE_T_L7));;
