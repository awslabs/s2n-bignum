(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of key generation (mld_sign_keypair_internal in     *)
(* sign.c): the bytes of a buffer one by one and as a number, the seed       *)
(* buffer, the polynomials of s and their packing, the vectors of            *)
(* polynomials in memory from those of their polynomials, the bytes of the   *)
(* keys from those of their parts, and the values that the code declassifies *)
(* and the termination of the samplings for a nonce.                         *)
(* ========================================================================= *)

needs "common/mldsa_native_sign.ml";;
needs "common/fips202/properties/keccak_fips202.ml";;
needs "common/fips204/properties/mldsa_native_matrix.ml";;

(* ------------------------------------------------------------------------- *)
(* The n bytes at a as a number are num_of_bytelist(list_of_seq f n) if and  *)
(* only if the bytes at a + j are f j for j < n.                             *)
(* ------------------------------------------------------------------------- *)

let MLD_KEYPAIR_DIVMOD_LEMMA = prove
 (`!B x y u v. x < B /\ y < B /\ x + B * u = y + B * v ==> x = y /\ u = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(B = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x + B * u) MOD B = (y + B * v) MOD B /\
                (x + B * u) DIV B = (y + B * v) DIV B` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* The values that the code declassifies for nonce n, and the termination of *)
(* its sampling, for the nonces that the code uses.                          *)
(* ------------------------------------------------------------------------- *)

let MLD_KEYPAIR_DECLASS_USED = prove
 (`!eta k l (used:num->bool) seed n.
        used n
        ==> mld_poly_uniform_eta_declass eta
             (mld_shake256_stream 66
               (mld_keypair_rhoprime k l seed + 2 EXP 512 * n)) =
            mld_keypair_declass eta k l used seed n`,
  SIMP_TAC[mld_keypair_declass]);;

let MLD_KEYPAIR_TERMINATES_USED = prove
 (`!eta k l (used:num->bool) seed n.
        mld_keypair_terminates eta k l used seed /\ used n
        ==> mld_rej_eta_terminates eta
             (mld_shake256_stream 66
               (mld_keypair_rhoprime k l seed + 2 EXP 512 * n))`,
  SIMP_TAC[mld_keypair_terminates]);;

(* ------------------------------------------------------------------------- *)
(* Byte j of the packing of a polynomial with coefficients in [-eta,eta]     *)
(* depends only on its coefficients (those below 256), and so do the         *)
(* polynomials of s and their packing.                                       *)
(* ------------------------------------------------------------------------- *)

let MLD_POLYETA_PACK_4_LOCAL = prove
 (`!(a:num->int32) b j.
        (!i. i < 256 ==> a i = b i) /\ j < 128
        ==> mld_polyeta_pack_4 a j = mld_polyeta_pack_4 b j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyeta_pack_4] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `(a:num->int32)(2 * j + 0) = b(2 * j + 0) /\
                a(2 * j + 1) = b(2 * j + 1)`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let MLD_POLYETA_PACK_2_LOCAL = prove
 (`!(a:num->int32) b j.
        (!i. i < 256 ==> a i = b i) /\ j < 96
        ==> mld_polyeta_pack_2 a j = mld_polyeta_pack_2 b j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyeta_pack_2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `!m. m < 8 ==> (a:num->int32)(8 * j DIV 3 + m) =
                              b(8 * j DIV 3 + m)` MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `j DIV 3 < 32` MP_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]]);;

let MLD_KEYPAIR_S_COEFF = prove
 (`!eta k l seed i t.
        t < 256
        ==> mld_keypair_s eta k l seed (256 * i + t) =
            mld_poly_uniform_eta eta (mld_keypair_rhoprime k l seed) (word i)
             t`,
  SIMP_TAC[mld_keypair_s; MLD_POLYVEC_COEFF]);;

let MLD_KEYPAIR_S_PACK = prove
 (`!eta k l seed p (pack:(num->int32)->num->byte) i t.
        (!a b j. (!i. i < 256 ==> a i = b i) /\ j < p
                 ==> pack a j = pack b j) /\
        t < p
        ==> mld_polyvec_pack p pack (mld_keypair_s eta k l seed) (p * i + t) =
            pack (mld_poly_uniform_eta eta (mld_keypair_rhoprime k l seed)
                   (word i)) t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLD_POLYVEC_PACK_COEFF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[mld_keypair_s; MLD_POLY_OF_POLYVEC]);;

let MLD_KEYPAIR_S_PACK_4 = prove
 (`!k l seed i t.
        t < 128
        ==> mld_polyvec_pack 128 mld_polyeta_pack_4
             (mld_keypair_s 4 k l seed) (128 * i + t) =
            mld_polyeta_pack_4
             (mld_poly_uniform_eta 4 (mld_keypair_rhoprime k l seed) (word i))
             t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLD_KEYPAIR_S_PACK THEN
  ASM_REWRITE_TAC[MLD_POLYETA_PACK_4_LOCAL]);;

let MLD_KEYPAIR_S_PACK_2 = prove
 (`!k l seed i t.
        t < 96
        ==> mld_polyvec_pack 96 mld_polyeta_pack_2
             (mld_keypair_s 2 k l seed) (96 * i + t) =
            mld_polyeta_pack_2
             (mld_poly_uniform_eta 2 (mld_keypair_rhoprime k l seed) (word i))
             t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLD_KEYPAIR_S_PACK THEN
  ASM_REWRITE_TAC[MLD_POLYETA_PACK_2_LOCAL]);;

let MLD_KEYPAIR_RANGE_TAC lbl lo extra =
  REMOVE_THEN lbl
   (MP_TAC o SPEC (mk_binop `(-):num->num->num` `j:num` lo)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   (list_mk_conj
     (mk_eq(mk_binop `(+):num->num->num` lo
              (mk_binop `(-):num->num->num` `j:num` lo),`j:num`)::extra))
   (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC;;
