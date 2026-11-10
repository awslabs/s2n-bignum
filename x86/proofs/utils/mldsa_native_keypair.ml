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
needs "x86/proofs/utils/keccak_fips202.ml";;
needs "x86/proofs/utils/mldsa_native_matrix.ml";;

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

let MLD_KEYPAIR_BYTES_STEP = prove
 (`!(a:int64) n (f:num->byte) s.
        read(memory :> bytes(a,SUC n)) s =
        num_of_bytelist(list_of_seq f (SUC n)) <=>
        read(memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n) /\
        read(memory :> bytes8(word_add a (word n))) s = f n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ADD1; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; GSYM ADD1; list_of_seq;
              NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ] THEN
  REWRITE_TAC[num_of_bytelist; READ_MEMORY_BYTES_BYTES8; MULT_CLAUSES;
              ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC MLD_KEYPAIR_DIVMOD_LEMMA THEN
    EXISTS_TAC `2 EXP (8 * n)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
      MP_TAC(ISPEC `list_of_seq (f:num->byte) n` NUM_OF_BYTELIST_BOUND) THEN
      REWRITE_TAC[LENGTH_LIST_OF_SEQ; EXP_MULT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]];
    SIMP_TAC[]]);;

let MLD_KEYPAIR_BYTES_EQ_BYTES8 = prove
 (`!(a:int64) n (f:num->byte) s.
        read(memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n) <=>
        !j. j < n ==> read(memory :> bytes8(word_add a (word j))) s = f j`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[list_of_seq; num_of_bytelist; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL; LT];
    ASM_REWRITE_TAC[MLD_KEYPAIR_BYTES_STEP; LT] THEN MESON_TAC[]]);;

let MLD_KEYPAIR_BYTES_32_OF_HALVES =
  CONV_RULE NUM_REDUCE_CONV MLD_BYTES_32_OF_HALVES;;

(* ------------------------------------------------------------------------- *)
(* The seed buffer: the 128 bytes of SHAKE256 of seed || k || l, with rho in *)
(* the first 32 and rho' in the next 64.                                     *)
(* ------------------------------------------------------------------------- *)

let MLD_KEYPAIR_SEEDBUF = prove
 (`!(a:int64) k l seed s.
        read(memory :> bytes(a,128)) s =
        num_of_bytelist
         (list_of_seq (mld_shake256_byte 34 (seed + 2 EXP 256 * (k + 256 * l)))
                      128)
        ==> (!j. j < 128
                 ==> read(memory :> bytes8(word_add a (word j))) s =
                     mld_keypair_seedbuf k l seed j) /\
            read(memory :> bytes(a,32)) s = mld_keypair_rho k l seed /\
            read(memory :> bytes(word_add a (word 32),64)) s =
            mld_keypair_rhoprime k l seed`,
  REWRITE_TAC[GSYM mld_keypair_seedbuf; MLD_KEYPAIR_BYTES_EQ_BYTES8] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mld_keypair_rho; mld_keypair_rhoprime;
              MLD_KEYPAIR_BYTES_EQ_BYTES8] THEN
  CONJ_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

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

(* ------------------------------------------------------------------------- *)
(* A vector in memory from its polynomials: k polynomials of 256 32-bit      *)
(* coefficients, or of p bytes, from offset off, as the callees give them.   *)
(* ------------------------------------------------------------------------- *)

let MLD_KEYPAIR_JOIN32 = prove
 (`!(a:int64) off (f:num->int32) k s.
        (!i. i < k
             ==> !l. l < 256
                     ==> read(memory :> bytes32
                               (word_add a (word((off + 1024 * i) + 4 * l))))
                           s =
                         f(256 * i + l))
        ==> !j. j < 256 * k
                ==> read(memory :> bytes32(word_add a (word(off + 4 * j)))) s =
                    f j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC VEC_JOIN_ALL THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE
   `off + 4 * (256 * i + l) = (off + 1024 * i) + 4 * l`] THEN
  ASM_SIMP_TAC[]);;

let MLD_KEYPAIR_JOIN8 = prove
 (`!(a:int64) off p (f:num->byte) k s.
        (!i. i < k
             ==> !l. l < p
                     ==> read(memory :> bytes8
                               (word_add a (word((off + p * i) + l)))) s =
                         f(p * i + l))
        ==> !j. j < p * k
                ==> read(memory :> bytes8(word_add a (word(off + j)))) s =
                    f j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC VEC_JOIN_ALL THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `off + p * i + l = (off + p * i) + l`] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The bytes of the public key from rho and the packed t1, and those of the  *)
(* secret key from rho, the key, tr, the packed s and the packed t0.         *)
(* ------------------------------------------------------------------------- *)

let MLD_KEYPAIR_PK_BYTES = prove
 (`!(a:int64) s eta k l (pack:(num->int32)->num->byte)
    (unpack:(num->byte)->num->int32) p seed.
        read(memory :> bytes(a,32)) s = mld_keypair_rho k l seed /\
        (!j. j < 320 * k
             ==> read(memory :> bytes8(word_add a (word(32 + j)))) s =
                 mld_polyvec_pack 320 mld_polyt1_pack
                  (mld_polyvec_map mld_poly_power2round_hi
                    (mld_keypair_t eta k l pack unpack p seed)) j)
        ==> !j. j < 32 + 320 * k
                ==> read(memory :> bytes8(word_add a (word j))) s =
                    mld_keypair_pk eta k l pack unpack p seed j`,
  REWRITE_TAC[mld_keypair_rho; MLD_KEYPAIR_BYTES_EQ_BYTES8] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_keypair_pk] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j - 32`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `32 + (j - 32) = j` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[]]);;

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

let MLD_KEYPAIR_SK_BYTES = prove
 (`!(a:int64) s eta k l (pack:(num->int32)->num->byte)
    (unpack:(num->byte)->num->int32) p seed.
        (!j. j < 32
             ==> read(memory :> bytes8(word_add a (word j))) s =
                 mld_keypair_seedbuf k l seed j) /\
        (!j. j < 32
             ==> read(memory :> bytes8(word_add a (word(32 + j)))) s =
                 mld_keypair_seedbuf k l seed (96 + j)) /\
        (!j. j < 64
             ==> read(memory :> bytes8(word_add a (word(64 + j)))) s =
                 mld_shake256_byte (32 + 320 * k)
                  (num_of_bytelist
                    (list_of_seq (mld_keypair_pk eta k l pack unpack p seed)
                                 (32 + 320 * k))) j) /\
        (!j. j < (l + k) * p
             ==> read(memory :> bytes8(word_add a (word(128 + j)))) s =
                 mld_polyvec_pack p pack (mld_keypair_s eta k l seed) j) /\
        (!j. j < 416 * k
             ==> read(memory :> bytes8
                       (word_add a (word((128 + (l + k) * p) + j)))) s =
                 mld_polyvec_pack 416 mld_polyt0_pack
                  (mld_polyvec_map mld_poly_power2round_lo
                    (mld_keypair_t eta k l pack unpack p seed)) j)
        ==> !j. j < (128 + (l + k) * p) + 416 * k
                ==> read(memory :> bytes8(word_add a (word j))) s =
                    mld_keypair_sk eta k l pack unpack p seed j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "r0") (CONJUNCTS_THEN2
   (LABEL_TAC "r1") (CONJUNCTS_THEN2 (LABEL_TAC "r2") (CONJUNCTS_THEN2
   (LABEL_TAC "r3") (LABEL_TAC "r4"))))) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_keypair_sk] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `j < 32` THEN ASM_REWRITE_TAC[] THENL
   [REMOVE_THEN "r0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `j < 64` THEN ASM_REWRITE_TAC[] THENL
   [MLD_KEYPAIR_RANGE_TAC "r1" `32` [`96 + (j - 32) = j + 64`]; ALL_TAC] THEN
  ASM_CASES_TAC `j < 128` THEN ASM_REWRITE_TAC[] THENL
   [MLD_KEYPAIR_RANGE_TAC "r2" `64` []; ALL_TAC] THEN
  ASM_CASES_TAC `j < 128 + (l + k) * p` THEN ASM_REWRITE_TAC[] THENL
   [MLD_KEYPAIR_RANGE_TAC "r3" `128` []; ALL_TAC] THEN
  MLD_KEYPAIR_RANGE_TAC "r4" `128 + (l + k) * p` []);;
