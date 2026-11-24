(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The algorithms of FIPS 203 for the proofs of the API functions of         *)
(* mlkem_native2 (pke_encrypt_k2_proof.ml etc. in                            *)
(* arm/proofs/mlkem_native/asm): K-PKE key generation, encryption and        *)
(* decryption from the                                                       *)
(* for the three parameter sets. The lemmas are those of the proofs of the   *)
(* compiled C of mlkem-native, with the vectors also given as blocks of      *)
(* polynomials.                                                              *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_fips203.ml";;

(* ------------------------------------------------------------------------- *)
(* The algorithms of FIPS 203 used in the statements: lengths, and the       *)
(* internal ML-KEM algorithms (FIPS 203 Algorithms 16, 17 and 18) with the   *)
(* hash functions unfolded.                                                  *)
(* ------------------------------------------------------------------------- *)

let LENGTH_SHA3_256 = prove
 (`!m. LENGTH(sha3_256 m) = 32`,
  REWRITE_TAC[sha3_256; LENGTH_LIST_OF_SEQ]);;

let LENGTH_SHA3_512 = prove
 (`!m. LENGTH(sha3_512 m) = 64`,
  REWRITE_TAC[sha3_512; LENGTH_LIST_OF_SEQ]);;

let KPKE_KEYGEN_LENGTHS = prove
 (`!k eta1 eta2 du dv d.
        LENGTH(FST(kpke_keygen (k,eta1,eta2,du,dv) d)) = 384 * k + 32 /\
        LENGTH(SND(kpke_keygen (k,eta1,eta2,du,dv) d)) = 384 * k`,
  REWRITE_TAC[kpke_keygen; mlkem_g] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH_APPEND; MLKEM_ENCODE_LENGTH; mlkem_slice;
              LENGTH_LIST_OF_SEQ] THEN
  ARITH_TAC);;

let KPKE_ENCRYPT_LENGTH = prove
 (`!k eta1 eta2 du dv ek m r.
        LENGTH(kpke_encrypt (k,eta1,eta2,du,dv) ek m r) = 32 * (du * k + dv)`,
  REWRITE_TAC[kpke_encrypt] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH_APPEND; MLKEM_ENCODE_LENGTH] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `du * 256 * k = 8 * (32 * du * k) /\ dv * 256 = 8 * (32 * dv)`
  (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ARITH_TAC);;

let KPKE_DECRYPT_LENGTH = prove
 (`!k eta1 eta2 du dv dk c.
        LENGTH(kpke_decrypt (k,eta1,eta2,du,dv) dk c) = 32`,
  REWRITE_TAC[kpke_decrypt] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_SLICE_SLICE = prove
 (`!a n b m (l:byte list).
        a + n <= m
        ==> mlkem_slice a n (mlkem_slice b m l) = mlkem_slice (b + a) n l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_slice] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `a + i < m` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[EL_LIST_OF_SEQ; ADD_ASSOC]]);;

let NUM_OF_BYTELIST_INJ = prove
 (`!l1 l2:byte list.
        LENGTH l1 = LENGTH l2
        ==> (num_of_bytelist l1 = num_of_bytelist l2 <=> l1 = l2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM BYTELIST_OF_NUM_OF_BYTELIST] THEN
  ASM_REWRITE_TAC[]);;

let MLKEM_KEYGEN_PAIR = prove
 (`!k eta1 eta2 du dv d z.
        mlkem_keygen_internal (k,eta1,eta2,du,dv) d z =
        FST(kpke_keygen (k,eta1,eta2,du,dv) d),
        APPEND (SND(kpke_keygen (k,eta1,eta2,du,dv) d))
         (APPEND (FST(kpke_keygen (k,eta1,eta2,du,dv) d))
           (APPEND (mlkem_h(FST(kpke_keygen (k,eta1,eta2,du,dv) d))) z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_keygen_internal] THEN
  SPEC_TAC(`kpke_keygen (k,eta1,eta2,du,dv) d`,`kk:byte list#byte list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

let MLKEM_ENCAPS_PAIR = prove
 (`!k eta1 eta2 du dv ek m.
        mlkem_encaps_internal (k,eta1,eta2,du,dv) ek m =
        mlkem_slice 0 32 (sha3_512 (APPEND m (sha3_256 ek))),
        kpke_encrypt (k,eta1,eta2,du,dv) ek m
         (mlkem_slice 32 32 (sha3_512 (APPEND m (sha3_256 ek))))`,
  REWRITE_TAC[mlkem_encaps_internal; mlkem_g; mlkem_h] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let MLKEM_DECAPS_ALT = prove
 (`!k eta1 eta2 du dv dk c.
        mlkem_decaps_internal (k,eta1,eta2,du,dv) dk c =
        let m' = kpke_decrypt (k,eta1,eta2,du,dv)
                  (mlkem_slice 0 (384 * k) dk) c in
        let g = sha3_512 (APPEND m' (mlkem_slice (768 * k + 32) 32 dk)) in
        if kpke_encrypt (k,eta1,eta2,du,dv)
            (mlkem_slice (384 * k) (384 * k + 32) dk) m'
            (mlkem_slice 32 32 g) =
           c
        then mlkem_slice 0 32 g
        else list_of_seq
              (shake256 (APPEND (mlkem_slice (768 * k + 64) 32 dk) c))
                         32`,
  REWRITE_TAC[mlkem_decaps_internal; mlkem_g; mlkem_j] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* K-PKE (FIPS 203 Algorithms 13, 14 and 15) from the coefficients computed  *)
(* by the kernels, for k = 2, 3 and 4, with the vectors as flat arrays of    *)
(* 256 * k coefficients.                                                     *)
(* ------------------------------------------------------------------------- *)

(*** Key generation for k = 2 (FIPS 203 Algorithm 13): the coefficients 2p
 *** and 2p + 1 of row r of t_hat = A_hat o s_hat + e_hat from the sums of
 *** the products accumulated by basemul, which carry the factor 169 = 2^-16
 *** mod q that tomont removes, and the key pair from all the coefficients
 ***)

let KPKE_KEYGEN_COEFF_EVEN_K2 = prove
 (`!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 2 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A 1 (2 * p + 1) * YT 1 + A 1 (2 * p) * Y 1 (2 * p)) +
                   (A 0 (2 * p + 1) * YT 0 + A 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 2}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_2;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_DOUBLE; ARITH_RULE `(2 * p) DIV 2 = p`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`(&17:int) pow (2 * bitreverse7 p + 1)`,`z:int`) THEN GEN_TAC THEN
  MP_TAC(prove(`(&65536 * &169:int == &1) (mod &3329)`,
               REWRITE_TAC[int_congruent] THEN EXISTS_TAC `&3327:int` THEN
               INT_ARITH_TAC)) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  SPEC_TAC(`&65536:int`,`r:int`) THEN REPEAT GEN_TAC THEN
  CONV_TAC INTEGER_RULE);;

let KPKE_KEYGEN_COEFF_ODD_K2 = prove
 (`!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 2 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A 1 (2 * p + 1) * Y 1 (2 * p) + A 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A 0 (2 * p + 1) * Y 0 (2 * p) + A 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 2}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_2;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN; ADD_SUB] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  MP_TAC(prove(`(&65536 * &169:int == &1) (mod &3329)`,
               REWRITE_TAC[int_congruent] THEN EXISTS_TAC `&3327:int` THEN
               INT_ARITH_TAC)) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  SPEC_TAC(`&65536:int`,`r:int`) THEN REPEAT GEN_TAC THEN
  CONV_TAC INTEGER_RULE);;

let KPKE_KEYGEN_K2_RESULT = prove
 (`!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
    (pt:num->int16) (pt2:num->int16) (tr:num->int16) (sr:num->int16).
     mlkem_g(APPEND d [word 2]) = rho,sigma /\
     (!i j n. i < 2 /\ j < 2 /\ n < 256
              ==> mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(sh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word j))) i)
                (mod &3329) /\
                abs(ival(sh(256 * j + i))) <= &23594) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(eh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word(2 + j)))) i)
                (mod &3329) /\
                abs(ival(eh(256 * j + i))) <= &23594) /\
     (!j p. j < 2 /\ p < 128
            ==> (ival(mc(128 * j + p)) ==
                 ival(sh(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!r p. r < 2 /\ p < 128
            ==> (ival(pt(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(mc(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(mc p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p))))) (mod &3329) /\
                (ival(pt(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(sh(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(sh(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 512 ==> (ival(pt2 i) == &65536 * ival(pt i)) (mod &3329) /\
                      abs(ival(pt2 i)) <= &3328) /\
     (!i. i < 512 ==> ival(tr i) = ival(word_add (pt2 i) (eh i)) rem &3329) /\
     (!i. i < 512 ==> ival(sr i) = ival(sh i) rem &3329)
     ==> num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq tr 512)) +
         2 EXP (8 * 768) * num_of_bytelist rho =
         num_of_bytelist(FST(kpke_keygen mlkem512 d)) /\
         num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq sr 512)) =
         num_of_bytelist(SND(kpke_keygen mlkem512 d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem512] THEN
  MP_TAC(SPECL [`2`; `3`; `2`; `10`; `4`; `d:byte list`] KPKE_KEYGEN_FIPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 2 = 512`;
              ARITH_RULE `(12 * 512) DIV 8 = 768`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_ENCODE_12_LIST
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `EVEN 512`; MLKEM_NTT_CBD_BOUNDS] THEN
  SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_ADD; RING_SUM; MLKEM_NTT_CBD_IN_ZQ] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC;
    AP_TERM_TAC THEN AP_TERM_TAC] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM IWORD_IVAL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[IWORD_IVAL] THEN
  MP_TAC(SPECL [`256`; `2`; `i:num`] EXISTS_DIV_MOD_LT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `256 * 2 = 512`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THENL
   [ALL_TAC;
    TRANS_TAC EQ_TRANS
     `(mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word r))) n) rem &3329` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[MLKEM_NTT_CBD_BOUNDS]]] THEN
  SUBGOAL_THEN `?p. p < 128 /\ (n = 2 * p \/ n = 2 * p + 1)` MP_TAC THENL
   [MP_TAC(SPECL [`2`; `128`; `n:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `m:num`] THEN
    REWRITE_TAC[ARITH_RULE `m < 2 <=> m = 0 \/ m = 1`] THEN
    STRIP_TAC THEN EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("ival",_),Comb(Comb(Const("word_add",_),_),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_ADD_SMALL t)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THENL
   [MP_TAC(SPECL
     [`\j. mlkem_sample_ntt (APPEND rho [word j; word r])`;
      `\j n. ival((sh:num->int16)(256 * j + n))`;
      `\j. ival((mc:num->int16)(128 * j + p))`;
      `\j. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p))`;
      `ival((pt2:num->int16)(256 * r + 2 * p))`;
      `ival((eh:num->int16)(256 * r + 2 * p))`;
      `mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word(2 + r)))) (2 * p)`;
      `p:num`] KPKE_KEYGEN_COEFF_EVEN_K2);
    MP_TAC(SPECL
     [`\j. mlkem_sample_ntt (APPEND rho [word j; word r])`;
      `\j n. ival((sh:num->int16)(256 * j + n))`;
      `\j. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p + 1))`;
      `ival((pt2:num->int16)(256 * r + 2 * p + 1))`;
      `ival((eh:num->int16)(256 * r + 2 * p + 1))`;
      `mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 sigma (word(2 + r))))
                 (2 * p + 1)`;
      `p:num`] KPKE_KEYGEN_COEFF_ODD_K2)] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(*** Key generation for k = 3 (FIPS 203 Algorithm 13): the coefficients 2p
 *** and 2p + 1 of row r of t_hat = A_hat o s_hat + e_hat from the sums of
 *** the products accumulated by basemul, which carry the factor 169 = 2^-16
 *** mod q that tomont removes, and the key pair from all the coefficients
 ***)

let KPKE_KEYGEN_COEFF_EVEN_K3 = prove
 (`!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 3 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A 2 (2 * p + 1) * YT 2 + A 2 (2 * p) * Y 2 (2 * p)) +
                   (A 1 (2 * p + 1) * YT 1 + A 1 (2 * p) * Y 1 (2 * p)) +
                   (A 0 (2 * p + 1) * YT 0 + A 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 3}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_3;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_DOUBLE; ARITH_RULE `(2 * p) DIV 2 = p`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`(&17:int) pow (2 * bitreverse7 p + 1)`,`z:int`) THEN GEN_TAC THEN
  MP_TAC(prove(`(&65536 * &169:int == &1) (mod &3329)`,
               REWRITE_TAC[int_congruent] THEN EXISTS_TAC `&3327:int` THEN
               INT_ARITH_TAC)) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  SPEC_TAC(`&65536:int`,`r:int`) THEN REPEAT GEN_TAC THEN
  CONV_TAC INTEGER_RULE);;

let KPKE_KEYGEN_COEFF_ODD_K3 = prove
 (`!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 3 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A 2 (2 * p + 1) * Y 2 (2 * p) + A 2 (2 * p) * Y 2 (2 * p + 1)) +
            (A 1 (2 * p + 1) * Y 1 (2 * p) + A 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A 0 (2 * p + 1) * Y 0 (2 * p) + A 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 3}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_3;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN; ADD_SUB] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  MP_TAC(prove(`(&65536 * &169:int == &1) (mod &3329)`,
               REWRITE_TAC[int_congruent] THEN EXISTS_TAC `&3327:int` THEN
               INT_ARITH_TAC)) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  SPEC_TAC(`&65536:int`,`r:int`) THEN REPEAT GEN_TAC THEN
  CONV_TAC INTEGER_RULE);;

let KPKE_KEYGEN_K3_RESULT = prove
 (`!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
    (pt:num->int16) (pt2:num->int16) (tr:num->int16) (sr:num->int16).
     mlkem_g(APPEND d [word 3]) = rho,sigma /\
     (!i j n. i < 3 /\ j < 3 /\ n < 256
              ==> mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(sh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j))) i)
                (mod &3329) /\
                abs(ival(sh(256 * j + i))) <= &23594) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(eh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(3 + j)))) i)
                (mod &3329) /\
                abs(ival(eh(256 * j + i))) <= &23594) /\
     (!j p. j < 3 /\ p < 128
            ==> (ival(mc(128 * j + p)) ==
                 ival(sh(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!r p. r < 3 /\ p < 128
            ==> (ival(pt(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(mc(256 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(mc(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(mc p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p))))) (mod &3329) /\
                (ival(pt(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(sh(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(sh(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(sh(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 768 ==> (ival(pt2 i) == &65536 * ival(pt i)) (mod &3329) /\
                      abs(ival(pt2 i)) <= &3328) /\
     (!i. i < 768 ==> ival(tr i) = ival(word_add (pt2 i) (eh i)) rem &3329) /\
     (!i. i < 768 ==> ival(sr i) = ival(sh i) rem &3329)
     ==> num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq tr 768)) +
         2 EXP (8 * 1152) * num_of_bytelist rho =
         num_of_bytelist(FST(kpke_keygen mlkem768 d)) /\
         num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq sr 768)) =
         num_of_bytelist(SND(kpke_keygen mlkem768 d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem768] THEN
  MP_TAC(SPECL [`3`; `2`; `2`; `10`; `4`; `d:byte list`] KPKE_KEYGEN_FIPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 3 = 768`;
              ARITH_RULE `(12 * 768) DIV 8 = 1152`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_ENCODE_12_LIST
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `EVEN 768`; MLKEM_NTT_CBD_BOUNDS] THEN
  SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_ADD; RING_SUM; MLKEM_NTT_CBD_IN_ZQ] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC;
    AP_TERM_TAC THEN AP_TERM_TAC] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM IWORD_IVAL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[IWORD_IVAL] THEN
  MP_TAC(SPECL [`256`; `3`; `i:num`] EXISTS_DIV_MOD_LT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `256 * 3 = 768`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THENL
   [ALL_TAC;
    TRANS_TAC EQ_TRANS
     `(mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word r))) n) rem &3329` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[MLKEM_NTT_CBD_BOUNDS]]] THEN
  SUBGOAL_THEN `?p. p < 128 /\ (n = 2 * p \/ n = 2 * p + 1)` MP_TAC THENL
   [MP_TAC(SPECL [`2`; `128`; `n:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `m:num`] THEN
    REWRITE_TAC[ARITH_RULE `m < 2 <=> m = 0 \/ m = 1`] THEN
    STRIP_TAC THEN EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("ival",_),Comb(Comb(Const("word_add",_),_),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_ADD_SMALL t)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THENL
   [MP_TAC(SPECL
     [`\j. mlkem_sample_ntt (APPEND rho [word j; word r])`;
      `\j n. ival((sh:num->int16)(256 * j + n))`;
      `\j. ival((mc:num->int16)(128 * j + p))`;
      `\j. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p))`;
      `ival((pt2:num->int16)(256 * r + 2 * p))`;
      `ival((eh:num->int16)(256 * r + 2 * p))`;
      `mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(3 + r)))) (2 * p)`;
      `p:num`] KPKE_KEYGEN_COEFF_EVEN_K3);
    MP_TAC(SPECL
     [`\j. mlkem_sample_ntt (APPEND rho [word j; word r])`;
      `\j n. ival((sh:num->int16)(256 * j + n))`;
      `\j. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p + 1))`;
      `ival((pt2:num->int16)(256 * r + 2 * p + 1))`;
      `ival((eh:num->int16)(256 * r + 2 * p + 1))`;
      `mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(3 + r))))
                 (2 * p + 1)`;
      `p:num`] KPKE_KEYGEN_COEFF_ODD_K3)] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(*** Key generation for k = 4 (FIPS 203 Algorithm 13): the coefficients 2p
 *** and 2p + 1 of row r of t_hat = A_hat o s_hat + e_hat from the sums of
 *** the products accumulated by basemul, which carry the factor 169 = 2^-16
 *** mod q that tomont removes, and the key pair from all the coefficients
 ***)

let KPKE_KEYGEN_COEFF_EVEN_K4 = prove
 (`!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 4 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A 3 (2 * p + 1) * YT 3 + A 3 (2 * p) * Y 3 (2 * p)) +
                   (A 2 (2 * p + 1) * YT 2 + A 2 (2 * p) * Y 2 (2 * p)) +
                   (A 1 (2 * p + 1) * YT 1 + A 1 (2 * p) * Y 1 (2 * p)) +
                   (A 0 (2 * p + 1) * YT 0 + A 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 4}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_4;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_DOUBLE; ARITH_RULE `(2 * p) DIV 2 = p`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`(&17:int) pow (2 * bitreverse7 p + 1)`,`z:int`) THEN GEN_TAC THEN
  MP_TAC(prove(`(&65536 * &169:int == &1) (mod &3329)`,
               REWRITE_TAC[int_congruent] THEN EXISTS_TAC `&3327:int` THEN
               INT_ARITH_TAC)) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  SPEC_TAC(`&65536:int`,`r:int`) THEN REPEAT GEN_TAC THEN
  CONV_TAC INTEGER_RULE);;

let KPKE_KEYGEN_COEFF_ODD_K4 = prove
 (`!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 4 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A 3 (2 * p + 1) * Y 3 (2 * p) + A 3 (2 * p) * Y 3 (2 * p + 1)) +
            (A 2 (2 * p + 1) * Y 2 (2 * p) + A 2 (2 * p) * Y 2 (2 * p + 1)) +
            (A 1 (2 * p + 1) * Y 1 (2 * p) + A 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A 0 (2 * p + 1) * Y 0 (2 * p) + A 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 4}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_4;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN; ADD_SUB] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  MP_TAC(prove(`(&65536 * &169:int == &1) (mod &3329)`,
               REWRITE_TAC[int_congruent] THEN EXISTS_TAC `&3327:int` THEN
               INT_ARITH_TAC)) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  SPEC_TAC(`&65536:int`,`r:int`) THEN REPEAT GEN_TAC THEN
  CONV_TAC INTEGER_RULE);;

let KPKE_KEYGEN_K4_RESULT = prove
 (`!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
    (pt:num->int16) (pt2:num->int16) (tr:num->int16) (sr:num->int16).
     mlkem_g(APPEND d [word 4]) = rho,sigma /\
     (!i j n. i < 4 /\ j < 4 /\ n < 256
              ==> mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(sh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j))) i)
                (mod &3329) /\
                abs(ival(sh(256 * j + i))) <= &23594) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(eh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(4 + j)))) i)
                (mod &3329) /\
                abs(ival(eh(256 * j + i))) <= &23594) /\
     (!j p. j < 4 /\ p < 128
            ==> (ival(mc(128 * j + p)) ==
                 ival(sh(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!r p. r < 4 /\ p < 128
            ==> (ival(pt(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(mc(384 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(sh(768 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(mc(256 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(mc(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(mc p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p))))) (mod &3329) /\
                (ival(pt(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(sh(768 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(sh(768 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(sh(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(sh(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(sh(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 1024 ==> (ival(pt2 i) == &65536 * ival(pt i)) (mod &3329) /\
                      abs(ival(pt2 i)) <= &3328) /\
     (!i. i < 1024 ==> ival(tr i) = ival(word_add (pt2 i) (eh i)) rem &3329) /\
     (!i. i < 1024 ==> ival(sr i) = ival(sh i) rem &3329)
     ==> num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq tr 1024)) +
         2 EXP (8 * 1536) * num_of_bytelist rho =
         num_of_bytelist(FST(kpke_keygen mlkem1024 d)) /\
         num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq sr 1024)) =
         num_of_bytelist(SND(kpke_keygen mlkem1024 d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem1024] THEN
  MP_TAC(SPECL [`4`; `2`; `2`; `11`; `5`; `d:byte list`] KPKE_KEYGEN_FIPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`;
              ARITH_RULE `(12 * 1024) DIV 8 = 1536`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_ENCODE_12_LIST
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `EVEN 1024`; MLKEM_NTT_CBD_BOUNDS] THEN
  SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_ADD; RING_SUM; MLKEM_NTT_CBD_IN_ZQ] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC;
    AP_TERM_TAC THEN AP_TERM_TAC] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM IWORD_IVAL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[IWORD_IVAL] THEN
  MP_TAC(SPECL [`256`; `4`; `i:num`] EXISTS_DIV_MOD_LT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THENL
   [ALL_TAC;
    TRANS_TAC EQ_TRANS
     `(mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word r))) n) rem &3329` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[MLKEM_NTT_CBD_BOUNDS]]] THEN
  SUBGOAL_THEN `?p. p < 128 /\ (n = 2 * p \/ n = 2 * p + 1)` MP_TAC THENL
   [MP_TAC(SPECL [`2`; `128`; `n:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `m:num`] THEN
    REWRITE_TAC[ARITH_RULE `m < 2 <=> m = 0 \/ m = 1`] THEN
    STRIP_TAC THEN EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("ival",_),Comb(Comb(Const("word_add",_),_),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_ADD_SMALL t)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THENL
   [MP_TAC(SPECL
     [`\j. mlkem_sample_ntt (APPEND rho [word j; word r])`;
      `\j n. ival((sh:num->int16)(256 * j + n))`;
      `\j. ival((mc:num->int16)(128 * j + p))`;
      `\j. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p))`;
      `ival((pt2:num->int16)(256 * r + 2 * p))`;
      `ival((eh:num->int16)(256 * r + 2 * p))`;
      `mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(4 + r)))) (2 * p)`;
      `p:num`] KPKE_KEYGEN_COEFF_EVEN_K4);
    MP_TAC(SPECL
     [`\j. mlkem_sample_ntt (APPEND rho [word j; word r])`;
      `\j n. ival((sh:num->int16)(256 * j + n))`;
      `\j. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p + 1))`;
      `ival((pt2:num->int16)(256 * r + 2 * p + 1))`;
      `ival((eh:num->int16)(256 * r + 2 * p + 1))`;
      `mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(4 + r))))
                 (2 * p + 1)`;
      `p:num`] KPKE_KEYGEN_COEFF_ODD_K4)] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(*** Encryption for k = 2 (FIPS 203 Algorithm 14): the ciphertext from
 *** t_hat decoded from ek, y_hat and its mulcache, e1, e2 and the message
 *** mu, the products of A_hat^T and of t_hat^T with y_hat, their inverse
 *** NTTs, the sums with the noise and the reductions before compression
 ***)

let KPKE_ENCRYPT_K2_RESULT = prove
 (`!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
    (E2:num->int16) (MU:num->int16) (U0:num->int16) (V0:num->int16)
    (U1:num->int16) (V1:num->int16) (U3:num->int16) (V4:num->int16).
     (!i j n. i < 2 /\ j < 2 /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice 768 32 ek) [word j; word i]) n
                  < &3329) /\
     (!i. i < 512
          ==> TT i = word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(YH(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j))) i)
                (mod &3329) /\
                abs(ival(YH(256 * j + i))) <= &23594) /\
     (!j p. j < 2 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(YH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(E1(256 * j + i)) ==
                 coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word(2 + j)))))
                (mod &3329) /\
                abs(ival(E1(256 * j + i))) <= &2) /\
     (!i. i < 256
          ==> (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word 4))))
              (mod &3329) /\
              abs(ival(E2 i)) <= &2) /\
     (!i. i < 256
          ==> MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1)
                          DIV 2)) /\
     (!q p. q < 2 /\ p < 128
            ==> (ival(U0(256 * q + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p))))) (mod &3329) /\
                (ival(U0(256 * q + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(YH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(YH(2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(V0(2 * p)) ==
               &169 *
               ((ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
                (ival(TT(2 * p + 1)) * ival(MC p) +
                 ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
              (ival(V0(2 * p + 1)) ==
               &169 *
               ((ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
                (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
                 ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(U1(256 * j + i)) ==
                 inverse_ntt (\n. ival(U0(256 * j + n))) i) (mod &3329) /\
                abs(ival(U1(256 * j + i))) <= &26624) /\
     (!i. i < 256
          ==> (ival(V1 i) == inverse_ntt (\n. ival(V0 n)) i) (mod &3329) /\
              abs(ival(V1 i)) <= &26624) /\
     (!i. i < 512 ==> ival(U3 i) = ival(word_add (U1 i) (E1 i)) rem &3329) /\
     (!i. i < 256
          ==> ival(V4 i) =
              ival(word_add (word_add (V1 i) (E2 i)) (MU i)) rem &3329)
     ==> nsum {i | i < 512}
              (\i. ((2048 * val(U3 i) + 3329) DIV 6658) MOD 1024 *
                   2 EXP (10 * i)) +
         2 EXP (8 * 640) *
         nsum {i | i < 256}
              (\i. ((32 * val(V4 i) + 3329) DIV 6658) MOD 16 * 2 EXP (4 * i)) =
         num_of_bytelist(kpke_encrypt mlkem512 ek m r)`,
  let inv_tac ui k =
    W(fun (_,w) ->
      let pinv = find_term (fun t -> match t with
        Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
      SUBGOAL_THEN
       (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                        pinv),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
       [MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
        REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
        ALL_TAC] THEN
      MP_TAC(ISPECL [rand pinv; ui; `&169:int`; k] MLKEM_NTT_INV_CONG_MUL) THEN
      ANTS_TAC THENL
       [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
        ASM_SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
        DISCH_TAC])
  and digit_tac =
    AP_THM_TAC THEN AP_TERM_TAC THEN
    W(fun (_,w) ->
      let t = find_term (fun t -> match t with
        Comb(Const("num_of_int",_),
             Comb(Comb(Const("rem",_),
                  Comb(Comb(Const("mlkem_compress",_),_),_)),_)) -> true
        | _ -> false) w in
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_COMPRESS_DIGIT t)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MLKEM_COEFF_POS THEN
      REPEAT(MATCH_MP_TAC RING_ADD THEN
             REWRITE_TAC[MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ]) THEN
      MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VAL_EQ_NUM_OF_INT_IVAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC MLKEM_COEFF_POS THEN
      REPEAT(MATCH_MP_TAC RING_ADD THEN
             REWRITE_TAC[MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ]) THEN
      MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      ALL_TAC]
  and parity_tac =
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`2`; `128`; `n':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `b:num`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o
      MATCH_MP(ARITH_RULE `b < 2 ==> b = 0 \/ b = 1`)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `p < 128` THEN ARITH_TAC; ALL_TAC])
  and row_tac =
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; INT_CONG_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem512] THEN
  MP_TAC(SPECL [`2`; `3`; `2`; `10`; `4`; `ek:byte list`; `m:byte list`;
                `r:byte list`] KPKE_ENCRYPT_FIPS) THEN
  REWRITE_TAC[ARITH_RULE `384 * 2 = 768`] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 2 = 512`; ARITH_RULE `2 * 2 = 4`;
              ARITH_RULE `(10 * 512) DIV 8 = 640`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) NUM_OF_BYTELIST_MLKEM_ENCODE
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  REPEAT(ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC DIVIDES_CONV);
    DISCH_THEN SUBST1_TAC]) THEN
  BINOP_TAC THENL [ALL_TAC; AP_TERM_TAC] THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  digit_tac THENL
   [MP_TAC(SPECL [`256`; `2`; `i:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 2 = 512`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THEN
    SUBGOAL_THEN
     `!n'. n' < 256
           ==> (ival((U0:num->int16)(256 * j + n')) ==
                &169 * ring_sum mlkem_zq {j' | j' < 2}
                        (\j'. fips203_multiply_ntts
                               (mlkem_sample_ntt
                                 (APPEND (mlkem_slice 768 32 ek)
                                         [word j; word j']))
                               (mlkem_ntt
                                 (mlkem_cbd 3 (mlkem_prf 3 r (word j'))))
                               n')) (mod &3329)`
    ASSUME_TAC THENL
     [parity_tac THENL
       [MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 768 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 768 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. ival((MC:num->int16)(128 * j' + p))`;
          `\j'. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p))`; `p:num`]
         BASEMUL2_ROW_EVEN);
        MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 768 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 768 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p + 1))`; `p:num`]
         BASEMUL2_ROW_ODD)] THEN
      row_tac;
      ALL_TAC] THEN
    W(fun (_,w) ->
      let t = find_term (fun t -> match t with
        Comb(Const("ival",_),Comb(Comb(Const("word_add",_),_),_)) -> true
        | _ -> false) w in
      MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_ADD_BOUNDED t)) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `abs(ival((U1:num->int16)(256 * j + n))) <= &26624 /\
                    abs(ival((E1:num->int16)(256 * j + n))) <= &2`
      MP_TAC THENL [ASM_SIMP_TAC[]; INT_ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    inv_tac `\n'. ival((U0:num->int16)(256 * j + n'))` `n:num` THEN
    ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_CBD_IN_RQ] THEN
    REWRITE_TAC[MLKEM_ZQ_ADD; INT_REM_EQ] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(a:int == c) (mod q) /\ (b == d) (mod q)
      ==> (a + b == c + d) (mod q)`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
    EXISTS_TAC `inverse_ntt (\n'. ival((U0:num->int16)(256 * j + n'))) n` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n'. n' < 256
         ==> (ival((V0:num->int16) n') ==
              &169 * ring_sum mlkem_zq {j' | j' < 2}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 ek (256 * j' + n))
                             (mlkem_ntt
                               (mlkem_cbd 3 (mlkem_prf 3 r (word j'))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 2 /\ x < 256
              ==> (ival((TT:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 ek (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 2` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j')))`;
        `ival((V0:num->int16)(2 * p))`; `p:num`] BASEMUL2_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j')))`;
        `ival((V0:num->int16)(2 * p + 1))`; `p:num`] BASEMUL2_ROW_ODD)] THEN
    row_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN `(num_of_bytelist m DIV 2 EXP i) MOD 2 < 2` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival((MU:num->int16) i) =
    &((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MU_IVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(ival((V1:num->int16) i)) <= &26624 /\
                abs(ival((E2:num->int16) i)) <= &2`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add ((V1:num->int16) i) ((E2:num->int16) i)) =
    ival(V1 i) + ival(E2 i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_BOUNDED THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o fst o chop_list 2) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)) =
    ival(word_add (V1 i) (E2 i)) + ival(MU i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_BOUNDED THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ARITH_RULE
     `(3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2 <= 1665`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    UNDISCH_TAC `abs(ival((V1:num->int16) i)) <= &26624` THEN
    UNDISCH_TAC `abs(ival((E2:num->int16) i)) <= &2` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  inv_tac `\n. ival((V0:num->int16) n)` `i:num` THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ;
               RING_ADD] THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY; MLKEM_DECODE_1] THEN
  ASM_SIMP_TAC[MLKEM_DECOMPRESS_1] THEN
  REWRITE_TAC[MLKEM_ZQ_ADD; INT_REM_EQ] THEN
  MATCH_MP_TAC INT_CONG_ADD3_REM_ALT THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
    EXISTS_TAC `inverse_ntt (\n. ival((V0:num->int16) n)) i` THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_LT THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
    MP_TAC(ARITH_RULE
     `(3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2 <= 1665`) THEN
    ARITH_TAC]);;

(*** Decryption for k = 2 (FIPS 203 Algorithm 15): the message from u and
 *** v decompressed from the ciphertext, s_hat decoded from dk, u_hat and
 *** its mulcache, the product of s_hat^T and u_hat, its inverse NTT and
 *** the reduced difference v - w before compression
 ***)

let KPKE_DECRYPT_K2_RESULT = prove
 (`!dk ct (UD:num->int16) (VD:num->int16) (SS:num->int16) (UH:num->int16)
    (MC:num->int16) (WP:num->int16) (WI:num->int16) (VR:num->int16).
     (!i. i < 512
          ==> UD i =
              word((3329 * (num_of_bytelist ct DIV 2 EXP (10 * i)) MOD
                    2 EXP 10 + 512) DIV 1024)) /\
     (!i. i < 256
          ==> VD i =
              word((3329 * (num_of_bytelist(mlkem_slice 640 128 ct) DIV
                            2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16)) /\
     (!i. i < 512
          ==> SS i = word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(UH(256 * j + i)) ==
                 forward_ntt (\n. ival(UD(256 * j + n))) i) (mod &3329) /\
                abs(ival(UH(256 * j + i))) <= &23594) /\
     (!j p. j < 2 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(UH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(WP(2 * p)) ==
               &169 *
               ((ival(SS(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
                (ival(SS(2 * p + 1)) * ival(MC p) +
                 ival(SS(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
              (ival(WP(2 * p + 1)) ==
               &169 *
               ((ival(SS(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
                (ival(SS(2 * p + 1)) * ival(UH(2 * p)) +
                 ival(SS(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 256
          ==> (ival(WI i) == inverse_ntt (\n. ival(WP n)) i) (mod &3329) /\
              abs(ival(WI i)) <= &26624) /\
     (!i. i < 256 ==> ival(VR i) = ival(word_sub (VD i) (WI i)) rem &3329)
     ==> nsum {i | i < 256}
              (\i. ((4 * val(VR i) + 3329) DIV 6658) MOD 2 * 2 EXP i) =
         num_of_bytelist(kpke_decrypt mlkem512 dk ct)`,
  let parity_tac =
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`2`; `128`; `n':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `b:num`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o
      MATCH_MP(ARITH_RULE `b < 2 ==> b = 0 \/ b = 1`)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `p < 128` THEN ARITH_TAC; ALL_TAC])
and row_tac =
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; INT_CONG_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem512] THEN
  REWRITE_TAC[KPKE_DECRYPT_FIPS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  W(fun (_,w) ->
    let enc = find_term (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) NUM_OF_BYTELIST_MLKEM_ENCODE
            (mk_comb(`num_of_bytelist`,enc)))) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC DIVIDES_CONV);
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[MULT_CLAUSES] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(fun (_,w) ->
    let pinv = find_term (fun t -> match t with
      Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
    SUBGOAL_THEN
     (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                      pinv),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
     [MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      ALL_TAC]) THEN
  W(fun (_,w) ->
    let wt = find_term (fun t -> match t with
      Comb(Comb(Comb(Const("ring_sub",_),_),_),_) -> true | _ -> false) w in
    SUBGOAL_THEN
     (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                      wt),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
     [MATCH_MP_TAC RING_SUB THEN ASM_REWRITE_TAC[MLKEM_POLY_IN_RQ];
      ALL_TAC]) THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("num_of_int",_),
           Comb(Comb(Const("rem",_),
                Comb(Comb(Const("mlkem_compress",_),_),_)),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) MLKEM_COMPRESS_DIGIT t)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MLKEM_COEFF_POS THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VAL_EQ_NUM_OF_INT_IVAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC MLKEM_COEFF_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_SUB; MLKEM_POLY_IN_RQ] THEN
  REWRITE_TAC[MLKEM_ZQ; INT_REM_EQ] THEN
  ABBREV_TAC `fv = (num_of_bytelist (mlkem_slice 640 128 ct) DIV
                    2 EXP (4 * i)) MOD 2 EXP 4` THEN
  SUBGOAL_THEN `(3329 * fv + 8) DIV 16 < 3329` ASSUME_TAC THENL
   [SUBGOAL_THEN `fv < 16` MP_TAC THENL
     [EXPAND_TAC "fv" THEN
      REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`; MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(word((3329 * fv + 8) DIV 16):int16) =
                &((3329 * fv + 8) DIV 16)` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_SMALL THEN
    UNDISCH_TAC `(3329 * fv + 8) DIV 16 < 3329` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(ival((WI:num->int16) i)) <= &26624` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("ival",_),Comb(Comb(Const("word_sub",_),_),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_SUB_BOUNDED t)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(3329 * fv + 8) DIV 16 < 3329` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
    UNDISCH_TAC `abs(ival((WI:num->int16) i)) <= &26624` THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY] THEN
  SIMP_TAC[MLKEM_DECODE_SMALL; ARITH_RULE `4 < 12`] THEN
  ASM_SIMP_TAC[MLKEM_DECOMPRESS_NUM; ARITH_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&((3329 * fv + 8) DIV 16) rem &3329 = &((3329 * fv + 8) DIV 16)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(b:int == d) (mod q) ==> (a - b == a - d) (mod q)`) THEN
  SUBGOAL_THEN
   `!j' n. j' < 2 /\ n < 256
           ==> (ival((UH:num->int16)(256 * j' + n)) ==
                mlkem_ntt (mlkem_poly
                  (\j''. mlkem_decompress 10
                          (mlkem_decode 10 ct (256 * j' + j'')))) n)
               (mod &3329)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MLKEM_NATIVE_NTT_CONG THEN
    EXISTS_TAC `\n. (UD:num->int16)(256 * j' + n)` THEN
    REWRITE_TAC[MLKEM_POLY_IN_RQ] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[] THEN
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `256 * j' + n' < 512` ASSUME_TAC THENL
     [UNDISCH_TAC `j' < 2` THEN UNDISCH_TAC `n' < 256` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COEFF_MLKEM_POLY; MLKEM_DECODE_SMALL; ARITH_RULE `10 < 12`;
                 MLKEM_DECOMPRESS_NUM; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[INT_CONG_RREM] THEN
    ABBREV_TAC `fu = (num_of_bytelist ct DIV 2 EXP (10 * (256 * j' + n'))) MOD
                     1024` THEN
    SUBGOAL_THEN `fu < 1024` MP_TAC THENL
     [EXPAND_TAC "fu" THEN REWRITE_TAC[MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      DISCH_TAC] THEN
    SUBGOAL_THEN `ival(word((3329 * fu + 512) DIV 1024):int16) =
                  &((3329 * fu + 512) DIV 1024)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_SMALL THEN UNDISCH_TAC `fu < 1024` THEN ARITH_TAC;
      REWRITE_TAC[INT_CONG_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n'. n' < 256
         ==> (ival((WP:num->int16) n') ==
              &169 * ring_sum mlkem_zq {j' | j' < 2}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 dk (256 * j' + n))
                             (mlkem_ntt (mlkem_poly
                               (\j''. mlkem_decompress 10
                                       (mlkem_decode 10 ct (256 * j' + j'')))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 2 /\ x < 256
              ==> (ival((SS:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 dk (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 2` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 10
                        (mlkem_decode 10 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p))`; `p:num`] BASEMUL2_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 10
                        (mlkem_decode 10 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p + 1))`; `p:num`] BASEMUL2_ROW_ODD)] THEN
    row_tac;
    ALL_TAC] THEN
  W(fun (_,w) ->
    let pinv = find_term (fun t -> match t with
      Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
    MP_TAC(ISPECL [rand pinv; `\n. ival((WP:num->int16) n)`; `&169:int`;
                   `i:num`] MLKEM_NTT_INV_CONG_MUL)) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
    DISCH_TAC] THEN
  MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
  EXISTS_TAC `inverse_ntt (\n. ival((WP:num->int16) n)) i` THEN
  ASM_SIMP_TAC[]);;

(*** The modulus check of an encapsulation key for k = 2 (FIPS 203
 *** section 7.2) as the bound of its 12-bit fields
 ***)

let MLKEM_EK_CHECK_512 = prove
 (`!ek. LENGTH ek = 800
        ==> (mlkem_ek_check mlkem512 ek <=>
             !i. i < 512
                 ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12
                     < 3329)`,
  SIMP_TAC[mlkem512; MLKEM_EK_CHECK] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** Encryption for k = 3 (FIPS 203 Algorithm 14): the ciphertext from
 *** t_hat decoded from ek, y_hat and its mulcache, e1, e2 and the message
 *** mu, the products of A_hat^T and of t_hat^T with y_hat, their inverse
 *** NTTs, the sums with the noise and the reductions before compression
 ***)

let KPKE_ENCRYPT_K3_RESULT = prove
 (`!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
    (E2:num->int16) (MU:num->int16) (U0:num->int16) (V0:num->int16)
    (U1:num->int16) (V1:num->int16) (U3:num->int16) (V4:num->int16).
     (!i j n. i < 3 /\ j < 3 /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice 1152 32 ek) [word j; word i]) n
                  < &3329) /\
     (!i. i < 768
          ==> TT i = word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(YH(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j))) i)
                (mod &3329) /\
                abs(ival(YH(256 * j + i))) <= &23594) /\
     (!j p. j < 3 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(YH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(E1(256 * j + i)) ==
                 coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word(3 + j)))))
                (mod &3329) /\
                abs(ival(E1(256 * j + i))) <= &2) /\
     (!i. i < 256
          ==> (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word 6))))
              (mod &3329) /\
              abs(ival(E2 i)) <= &2) /\
     (!i. i < 256
          ==> MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1)
                          DIV 2)) /\
     (!q p. q < 3 /\ p < 128
            ==> (ival(U0(256 * q + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(MC(256 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p))))) (mod &3329) /\
                (ival(U0(256 * q + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(YH(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(YH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(YH(2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(V0(2 * p)) ==
               &169 *
               ((ival(TT(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p))) +
                (ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
                (ival(TT(2 * p + 1)) * ival(MC p) +
                 ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
              (ival(V0(2 * p + 1)) ==
               &169 *
               ((ival(TT(512 + 2 * p + 1)) * ival(YH(512 + 2 * p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p + 1))) +
                (ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
                (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
                 ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(U1(256 * j + i)) ==
                 inverse_ntt (\n. ival(U0(256 * j + n))) i) (mod &3329) /\
                abs(ival(U1(256 * j + i))) <= &26624) /\
     (!i. i < 256
          ==> (ival(V1 i) == inverse_ntt (\n. ival(V0 n)) i) (mod &3329) /\
              abs(ival(V1 i)) <= &26624) /\
     (!i. i < 768 ==> ival(U3 i) = ival(word_add (U1 i) (E1 i)) rem &3329) /\
     (!i. i < 256
          ==> ival(V4 i) =
              ival(word_add (word_add (V1 i) (E2 i)) (MU i)) rem &3329)
     ==> nsum {i | i < 768}
              (\i. ((2048 * val(U3 i) + 3329) DIV 6658) MOD 1024 *
                   2 EXP (10 * i)) +
         2 EXP (8 * 960) *
         nsum {i | i < 256}
              (\i. ((32 * val(V4 i) + 3329) DIV 6658) MOD 16 * 2 EXP (4 * i)) =
         num_of_bytelist(kpke_encrypt mlkem768 ek m r)`,
  let inv_tac ui k =
    W(fun (_,w) ->
      let pinv = find_term (fun t -> match t with
        Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
      SUBGOAL_THEN
       (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                        pinv),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
       [MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
        REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
        ALL_TAC] THEN
      MP_TAC(ISPECL [rand pinv; ui; `&169:int`; k] MLKEM_NTT_INV_CONG_MUL) THEN
      ANTS_TAC THENL
       [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
        ASM_SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
        DISCH_TAC])
  and digit_tac =
    AP_THM_TAC THEN AP_TERM_TAC THEN
    W(fun (_,w) ->
      let t = find_term (fun t -> match t with
        Comb(Const("num_of_int",_),
             Comb(Comb(Const("rem",_),
                  Comb(Comb(Const("mlkem_compress",_),_),_)),_)) -> true
        | _ -> false) w in
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_COMPRESS_DIGIT t)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MLKEM_COEFF_POS THEN
      REPEAT(MATCH_MP_TAC RING_ADD THEN
             REWRITE_TAC[MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ]) THEN
      MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VAL_EQ_NUM_OF_INT_IVAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC MLKEM_COEFF_POS THEN
      REPEAT(MATCH_MP_TAC RING_ADD THEN
             REWRITE_TAC[MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ]) THEN
      MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      ALL_TAC]
  and parity_tac =
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`2`; `128`; `n':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `b:num`] THEN
    REWRITE_TAC[ARITH_RULE `b < 2 <=> b = 0 \/ b = 1`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `p < 128` THEN ARITH_TAC; ALL_TAC])
  and row_tac =
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; INT_CONG_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem768] THEN
  MP_TAC(SPECL [`3`; `2`; `2`; `10`; `4`; `ek:byte list`; `m:byte list`;
                `r:byte list`] KPKE_ENCRYPT_FIPS) THEN
  REWRITE_TAC[ARITH_RULE `384 * 3 = 1152`] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 3 = 768`; ARITH_RULE `2 * 3 = 6`;
              ARITH_RULE `(10 * 768) DIV 8 = 960`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) NUM_OF_BYTELIST_MLKEM_ENCODE
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  REPEAT(ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC DIVIDES_CONV);
    DISCH_THEN SUBST1_TAC]) THEN
  BINOP_TAC THENL [ALL_TAC; AP_TERM_TAC] THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  digit_tac THENL
   [MP_TAC(SPECL [`256`; `3`; `i:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 3 = 768`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THEN
    SUBGOAL_THEN
     `!n'. n' < 256
           ==> (ival((U0:num->int16)(256 * j + n')) ==
                &169 * ring_sum mlkem_zq {j' | j' < 3}
                        (\j'. fips203_multiply_ntts
                               (mlkem_sample_ntt
                                 (APPEND (mlkem_slice 1152 32 ek)
                                         [word j; word j']))
                               (mlkem_ntt
                                 (mlkem_cbd 2 (mlkem_prf 2 r (word j'))))
                               n')) (mod &3329)`
    ASSUME_TAC THENL
     [parity_tac THENL
       [MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1152 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1152 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. ival((MC:num->int16)(128 * j' + p))`;
          `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p))`; `p:num`]
         BASEMUL3_ROW_EVEN);
        MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1152 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1152 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p + 1))`; `p:num`]
         BASEMUL3_ROW_ODD)] THEN
      row_tac;
      ALL_TAC] THEN
    W(fun (_,w) ->
      let t = find_term (fun t -> match t with
        Comb(Const("ival",_),Comb(Comb(Const("word_add",_),_),_)) -> true
        | _ -> false) w in
      MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_ADD_BOUNDED t)) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `abs(ival((U1:num->int16)(256 * j + n))) <= &26624 /\
                    abs(ival((E1:num->int16)(256 * j + n))) <= &2`
      MP_TAC THENL [ASM_SIMP_TAC[]; INT_ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    inv_tac `\n'. ival((U0:num->int16)(256 * j + n'))` `n:num` THEN
    ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_CBD_IN_RQ] THEN
    REWRITE_TAC[MLKEM_ZQ_ADD; INT_REM_EQ] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(a:int == c) (mod q) /\ (b == d) (mod q)
      ==> (a + b == c + d) (mod q)`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
    EXISTS_TAC `inverse_ntt (\n'. ival((U0:num->int16)(256 * j + n'))) n` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n'. n' < 256
         ==> (ival((V0:num->int16) n') ==
              &169 * ring_sum mlkem_zq {j' | j' < 3}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 ek (256 * j' + n))
                             (mlkem_ntt
                               (mlkem_cbd 2 (mlkem_prf 2 r (word j'))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 3 /\ x < 256
              ==> (ival((TT:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 ek (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 3` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
        `ival((V0:num->int16)(2 * p))`; `p:num`] BASEMUL3_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
        `ival((V0:num->int16)(2 * p + 1))`; `p:num`] BASEMUL3_ROW_ODD)] THEN
    row_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN `(num_of_bytelist m DIV 2 EXP i) MOD 2 < 2` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival((MU:num->int16) i) =
    &((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MU_IVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(ival((V1:num->int16) i)) <= &26624 /\
                abs(ival((E2:num->int16) i)) <= &2`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add ((V1:num->int16) i) ((E2:num->int16) i)) =
    ival(V1 i) + ival(E2 i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_BOUNDED THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o fst o chop_list 2) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)) =
    ival(word_add (V1 i) (E2 i)) + ival(MU i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_BOUNDED THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ARITH_RULE
     `(3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2 <= 1665`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    UNDISCH_TAC `abs(ival((V1:num->int16) i)) <= &26624` THEN
    UNDISCH_TAC `abs(ival((E2:num->int16) i)) <= &2` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  inv_tac `\n. ival((V0:num->int16) n)` `i:num` THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ;
               RING_ADD] THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY; MLKEM_DECODE_1] THEN
  ASM_SIMP_TAC[MLKEM_DECOMPRESS_1] THEN
  REWRITE_TAC[MLKEM_ZQ_ADD; INT_REM_EQ] THEN
  MATCH_MP_TAC INT_CONG_ADD3_REM_ALT THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
    EXISTS_TAC `inverse_ntt (\n. ival((V0:num->int16) n)) i` THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_LT THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
    MP_TAC(ARITH_RULE
     `(3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2 <= 1665`) THEN
    ARITH_TAC]);;

(*** Decryption for k = 3 (FIPS 203 Algorithm 15): the message from u and
 *** v decompressed from the ciphertext, s_hat decoded from dk, u_hat and
 *** its mulcache, the product of s_hat^T and u_hat, its inverse NTT and
 *** the reduced difference v - w before compression
 ***)

let KPKE_DECRYPT_K3_RESULT = prove
 (`!dk ct (UD:num->int16) (VD:num->int16) (SS:num->int16) (UH:num->int16)
    (MC:num->int16) (WP:num->int16) (WI:num->int16) (VR:num->int16).
     (!i. i < 768
          ==> UD i =
              word((3329 * (num_of_bytelist ct DIV 2 EXP (10 * i)) MOD
                    2 EXP 10 + 512) DIV 1024)) /\
     (!i. i < 256
          ==> VD i =
              word((3329 * (num_of_bytelist(mlkem_slice 960 128 ct) DIV
                            2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16)) /\
     (!i. i < 768
          ==> SS i = word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(UH(256 * j + i)) ==
                 forward_ntt (\n. ival(UD(256 * j + n))) i) (mod &3329) /\
                abs(ival(UH(256 * j + i))) <= &23594) /\
     (!j p. j < 3 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(UH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(WP(2 * p)) ==
               &169 *
               ((ival(SS(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p))) +
                (ival(SS(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
                (ival(SS(2 * p + 1)) * ival(MC p) +
                 ival(SS(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
              (ival(WP(2 * p + 1)) ==
               &169 *
               ((ival(SS(512 + 2 * p + 1)) * ival(UH(512 + 2 * p)) +
                 ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p + 1))) +
                (ival(SS(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
                (ival(SS(2 * p + 1)) * ival(UH(2 * p)) +
                 ival(SS(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 256
          ==> (ival(WI i) == inverse_ntt (\n. ival(WP n)) i) (mod &3329) /\
              abs(ival(WI i)) <= &26624) /\
     (!i. i < 256 ==> ival(VR i) = ival(word_sub (VD i) (WI i)) rem &3329)
     ==> nsum {i | i < 256}
              (\i. ((4 * val(VR i) + 3329) DIV 6658) MOD 2 * 2 EXP i) =
         num_of_bytelist(kpke_decrypt mlkem768 dk ct)`,
  let parity_tac =
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`2`; `128`; `n':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `b:num`] THEN
    REWRITE_TAC[ARITH_RULE `b < 2 <=> b = 0 \/ b = 1`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `p < 128` THEN ARITH_TAC; ALL_TAC])
and row_tac =
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; INT_CONG_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem768] THEN
  REWRITE_TAC[KPKE_DECRYPT_FIPS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  W(fun (_,w) ->
    let enc = find_term (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) NUM_OF_BYTELIST_MLKEM_ENCODE
            (mk_comb(`num_of_bytelist`,enc)))) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC DIVIDES_CONV);
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[MULT_CLAUSES] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(fun (_,w) ->
    let pinv = find_term (fun t -> match t with
      Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
    SUBGOAL_THEN
     (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                      pinv),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
     [MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      ALL_TAC]) THEN
  W(fun (_,w) ->
    let wt = find_term (fun t -> match t with
      Comb(Comb(Comb(Const("ring_sub",_),_),_),_) -> true | _ -> false) w in
    SUBGOAL_THEN
     (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                      wt),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
     [MATCH_MP_TAC RING_SUB THEN ASM_REWRITE_TAC[MLKEM_POLY_IN_RQ];
      ALL_TAC]) THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("num_of_int",_),
           Comb(Comb(Const("rem",_),
                Comb(Comb(Const("mlkem_compress",_),_),_)),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) MLKEM_COMPRESS_DIGIT t)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MLKEM_COEFF_POS THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VAL_EQ_NUM_OF_INT_IVAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC MLKEM_COEFF_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_SUB; MLKEM_POLY_IN_RQ] THEN
  REWRITE_TAC[MLKEM_ZQ; INT_REM_EQ] THEN
  ABBREV_TAC `fv = (num_of_bytelist (mlkem_slice 960 128 ct) DIV
                    2 EXP (4 * i)) MOD 2 EXP 4` THEN
  SUBGOAL_THEN `(3329 * fv + 8) DIV 16 < 3329` ASSUME_TAC THENL
   [SUBGOAL_THEN `fv < 16` MP_TAC THENL
     [EXPAND_TAC "fv" THEN
      REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`; MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(word((3329 * fv + 8) DIV 16):int16) =
                &((3329 * fv + 8) DIV 16)` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_SMALL THEN
    UNDISCH_TAC `(3329 * fv + 8) DIV 16 < 3329` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(ival((WI:num->int16) i)) <= &26624` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("ival",_),Comb(Comb(Const("word_sub",_),_),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_SUB_BOUNDED t)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(3329 * fv + 8) DIV 16 < 3329` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
    UNDISCH_TAC `abs(ival((WI:num->int16) i)) <= &26624` THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY] THEN
  SIMP_TAC[MLKEM_DECODE_SMALL; ARITH_RULE `4 < 12`] THEN
  ASM_SIMP_TAC[MLKEM_DECOMPRESS_NUM; ARITH_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&((3329 * fv + 8) DIV 16) rem &3329 = &((3329 * fv + 8) DIV 16)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(b:int == d) (mod q) ==> (a - b == a - d) (mod q)`) THEN
  SUBGOAL_THEN
   `!j' n. j' < 3 /\ n < 256
           ==> (ival((UH:num->int16)(256 * j' + n)) ==
                mlkem_ntt (mlkem_poly
                  (\j''. mlkem_decompress 10
                          (mlkem_decode 10 ct (256 * j' + j'')))) n)
               (mod &3329)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MLKEM_NATIVE_NTT_CONG THEN
    EXISTS_TAC `\n. (UD:num->int16)(256 * j' + n)` THEN
    REWRITE_TAC[MLKEM_POLY_IN_RQ] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[] THEN
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `256 * j' + n' < 768` ASSUME_TAC THENL
     [UNDISCH_TAC `j' < 3` THEN UNDISCH_TAC `n' < 256` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COEFF_MLKEM_POLY; MLKEM_DECODE_SMALL; ARITH_RULE `10 < 12`;
                 MLKEM_DECOMPRESS_NUM; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[INT_CONG_RREM] THEN
    ABBREV_TAC `fu = (num_of_bytelist ct DIV 2 EXP (10 * (256 * j' + n'))) MOD
                     1024` THEN
    SUBGOAL_THEN `fu < 1024` MP_TAC THENL
     [EXPAND_TAC "fu" THEN REWRITE_TAC[MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      DISCH_TAC] THEN
    SUBGOAL_THEN `ival(word((3329 * fu + 512) DIV 1024):int16) =
                  &((3329 * fu + 512) DIV 1024)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_SMALL THEN UNDISCH_TAC `fu < 1024` THEN ARITH_TAC;
      REWRITE_TAC[INT_CONG_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n'. n' < 256
         ==> (ival((WP:num->int16) n') ==
              &169 * ring_sum mlkem_zq {j' | j' < 3}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 dk (256 * j' + n))
                             (mlkem_ntt (mlkem_poly
                               (\j''. mlkem_decompress 10
                                       (mlkem_decode 10 ct (256 * j' + j'')))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 3 /\ x < 256
              ==> (ival((SS:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 dk (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 3` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 10
                        (mlkem_decode 10 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p))`; `p:num`] BASEMUL3_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 10
                        (mlkem_decode 10 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p + 1))`; `p:num`] BASEMUL3_ROW_ODD)] THEN
    row_tac;
    ALL_TAC] THEN
  W(fun (_,w) ->
    let pinv = find_term (fun t -> match t with
      Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
    MP_TAC(ISPECL [rand pinv; `\n. ival((WP:num->int16) n)`; `&169:int`;
                   `i:num`] MLKEM_NTT_INV_CONG_MUL)) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
    DISCH_TAC] THEN
  MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
  EXISTS_TAC `inverse_ntt (\n. ival((WP:num->int16) n)) i` THEN
  ASM_SIMP_TAC[]);;

(*** The modulus check of an encapsulation key for k = 3 (FIPS 203
 *** section 7.2) as the bound of its 12-bit fields
 ***)

let MLKEM_EK_CHECK_768 = prove
 (`!ek. LENGTH ek = 1184
        ==> (mlkem_ek_check mlkem768 ek <=>
             !i. i < 768
                 ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12
                     < 3329)`,
  SIMP_TAC[mlkem768; MLKEM_EK_CHECK] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** Encryption for k = 4 (FIPS 203 Algorithm 14): the ciphertext from
 *** t_hat decoded from ek, y_hat and its mulcache, e1, e2 and the message
 *** mu, the products of A_hat^T and of t_hat^T with y_hat, their inverse
 *** NTTs, the sums with the noise and the reductions before compression
 ***)

let KPKE_ENCRYPT_K4_RESULT = prove
 (`!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
    (E2:num->int16) (MU:num->int16) (U0:num->int16) (V0:num->int16)
    (U1:num->int16) (V1:num->int16) (U3:num->int16) (V4:num->int16).
     (!i j n. i < 4 /\ j < 4 /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice 1536 32 ek) [word j; word i]) n
                  < &3329) /\
     (!i. i < 1024
          ==> TT i = word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(YH(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j))) i)
                (mod &3329) /\
                abs(ival(YH(256 * j + i))) <= &23594) /\
     (!j p. j < 4 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(YH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(E1(256 * j + i)) ==
                 coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word(4 + j)))))
                (mod &3329) /\
                abs(ival(E1(256 * j + i))) <= &2) /\
     (!i. i < 256
          ==> (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word 8))))
              (mod &3329) /\
              abs(ival(E2 i)) <= &2) /\
     (!i. i < 256
          ==> MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1)
                          DIV 2)) /\
     (!q p. q < 4 /\ p < 128
            ==> (ival(U0(256 * q + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 3]) (2 * p + 1) *
                   ival(MC(384 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 3]) (2 * p) *
                   ival(YH(768 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(MC(256 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p))))) (mod &3329) /\
                (ival(U0(256 * q + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 3]) (2 * p + 1) *
                   ival(YH(768 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 3]) (2 * p) *
                   ival(YH(768 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(YH(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(YH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(YH(2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1536 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(V0(2 * p)) ==
               &169 *
               ((ival(TT(768 + 2 * p + 1)) * ival(MC(384 + p)) +
                 ival(TT(768 + 2 * p)) * ival(YH(768 + 2 * p))) +
                (ival(TT(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p))) +
                (ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
                (ival(TT(2 * p + 1)) * ival(MC p) +
                 ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
              (ival(V0(2 * p + 1)) ==
               &169 *
               ((ival(TT(768 + 2 * p + 1)) * ival(YH(768 + 2 * p)) +
                 ival(TT(768 + 2 * p)) * ival(YH(768 + 2 * p + 1))) +
                (ival(TT(512 + 2 * p + 1)) * ival(YH(512 + 2 * p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p + 1))) +
                (ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
                (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
                 ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(U1(256 * j + i)) ==
                 inverse_ntt (\n. ival(U0(256 * j + n))) i) (mod &3329) /\
                abs(ival(U1(256 * j + i))) <= &26624) /\
     (!i. i < 256
          ==> (ival(V1 i) == inverse_ntt (\n. ival(V0 n)) i) (mod &3329) /\
              abs(ival(V1 i)) <= &26624) /\
     (!i. i < 1024
          ==> ival(U3 i) = ival(word_add (U1 i) (E1 i)) rem &3329) /\
     (!i. i < 256
          ==> ival(V4 i) =
              ival(word_add (word_add (V1 i) (E2 i)) (MU i)) rem &3329)
     ==> nsum {i | i < 1024}
              (\i. ((4096 * val(U3 i) + 3329) DIV 6658) MOD 2048 *
                   2 EXP (11 * i)) +
         2 EXP (8 * 1408) *
         nsum {i | i < 256}
              (\i. ((64 * val(V4 i) + 3329) DIV 6658) MOD 32 * 2 EXP (5 * i)) =
         num_of_bytelist(kpke_encrypt mlkem1024 ek m r)`,
  let inv_tac ui k =
    W(fun (_,w) ->
      let pinv = find_term (fun t -> match t with
        Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
      SUBGOAL_THEN
       (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                        pinv),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
       [MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
        REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
        ALL_TAC] THEN
      MP_TAC(ISPECL [rand pinv; ui; `&169:int`; k] MLKEM_NTT_INV_CONG_MUL) THEN
      ANTS_TAC THENL
       [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
        ASM_SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
        DISCH_TAC])
  and digit_tac =
    AP_THM_TAC THEN AP_TERM_TAC THEN
    W(fun (_,w) ->
      let t = find_term (fun t -> match t with
        Comb(Const("num_of_int",_),
             Comb(Comb(Const("rem",_),
                  Comb(Comb(Const("mlkem_compress",_),_),_)),_)) -> true
        | _ -> false) w in
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_COMPRESS_DIGIT t)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MLKEM_COEFF_POS THEN
      REPEAT(MATCH_MP_TAC RING_ADD THEN
             REWRITE_TAC[MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ]) THEN
      MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VAL_EQ_NUM_OF_INT_IVAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC MLKEM_COEFF_POS THEN
      REPEAT(MATCH_MP_TAC RING_ADD THEN
             REWRITE_TAC[MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ]) THEN
      MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      ALL_TAC]
  and parity_tac =
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`2`; `128`; `n':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `b:num`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o
      MATCH_MP(ARITH_RULE `b < 2 ==> b = 0 \/ b = 1`)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `p < 128` THEN ARITH_TAC; ALL_TAC])
  and row_tac =
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; INT_CONG_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem1024] THEN
  MP_TAC(SPECL [`4`; `2`; `2`; `11`; `5`; `ek:byte list`; `m:byte list`;
                `r:byte list`] KPKE_ENCRYPT_FIPS) THEN
  REWRITE_TAC[ARITH_RULE `384 * 4 = 1536`] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`; ARITH_RULE `2 * 4 = 8`;
              ARITH_RULE `(11 * 1024) DIV 8 = 1408`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) NUM_OF_BYTELIST_MLKEM_ENCODE
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  REPEAT(ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC DIVIDES_CONV);
    DISCH_THEN SUBST1_TAC]) THEN
  BINOP_TAC THENL [ALL_TAC; AP_TERM_TAC] THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  digit_tac THENL
   [MP_TAC(SPECL [`256`; `4`; `i:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THEN
    SUBGOAL_THEN
     `!n'. n' < 256
           ==> (ival((U0:num->int16)(256 * j + n')) ==
                &169 * ring_sum mlkem_zq {j' | j' < 4}
                        (\j'. fips203_multiply_ntts
                               (mlkem_sample_ntt
                                 (APPEND (mlkem_slice 1536 32 ek)
                                         [word j; word j']))
                               (mlkem_ntt
                                 (mlkem_cbd 2 (mlkem_prf 2 r (word j'))))
                               n')) (mod &3329)`
    ASSUME_TAC THENL
     [parity_tac THENL
       [MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1536 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1536 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. ival((MC:num->int16)(128 * j' + p))`;
          `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p))`; `p:num`]
         BASEMUL4_ROW_EVEN);
        MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1536 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1536 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p + 1))`; `p:num`]
         BASEMUL4_ROW_ODD)] THEN
      row_tac;
      ALL_TAC] THEN
    W(fun (_,w) ->
      let t = find_term (fun t -> match t with
        Comb(Const("ival",_),Comb(Comb(Const("word_add",_),_),_)) -> true
        | _ -> false) w in
      MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_ADD_BOUNDED t)) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `abs(ival((U1:num->int16)(256 * j + n))) <= &26624 /\
                    abs(ival((E1:num->int16)(256 * j + n))) <= &2`
      MP_TAC THENL [ASM_SIMP_TAC[]; INT_ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    inv_tac `\n'. ival((U0:num->int16)(256 * j + n'))` `n:num` THEN
    ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_CBD_IN_RQ] THEN
    REWRITE_TAC[MLKEM_ZQ_ADD; INT_REM_EQ] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(a:int == c) (mod q) /\ (b == d) (mod q)
      ==> (a + b == c + d) (mod q)`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
    EXISTS_TAC `inverse_ntt (\n'. ival((U0:num->int16)(256 * j + n'))) n` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n'. n' < 256
         ==> (ival((V0:num->int16) n') ==
              &169 * ring_sum mlkem_zq {j' | j' < 4}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 ek (256 * j' + n))
                             (mlkem_ntt
                               (mlkem_cbd 2 (mlkem_prf 2 r (word j'))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 4 /\ x < 256
              ==> (ival((TT:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 ek (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 4` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
        `ival((V0:num->int16)(2 * p))`; `p:num`] BASEMUL4_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
        `ival((V0:num->int16)(2 * p + 1))`; `p:num`] BASEMUL4_ROW_ODD)] THEN
    row_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN `(num_of_bytelist m DIV 2 EXP i) MOD 2 < 2` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival((MU:num->int16) i) =
    &((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MU_IVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(ival((V1:num->int16) i)) <= &26624 /\
                abs(ival((E2:num->int16) i)) <= &2`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add ((V1:num->int16) i) ((E2:num->int16) i)) =
    ival(V1 i) + ival(E2 i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_BOUNDED THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o fst o chop_list 2) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)) =
    ival(word_add (V1 i) (E2 i)) + ival(MU i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_BOUNDED THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ARITH_RULE
     `(3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2 <= 1665`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    UNDISCH_TAC `abs(ival((V1:num->int16) i)) <= &26624` THEN
    UNDISCH_TAC `abs(ival((E2:num->int16) i)) <= &2` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  inv_tac `\n. ival((V0:num->int16) n)` `i:num` THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ;
               RING_ADD] THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY; MLKEM_DECODE_1] THEN
  ASM_SIMP_TAC[MLKEM_DECOMPRESS_1] THEN
  REWRITE_TAC[MLKEM_ZQ_ADD; INT_REM_EQ] THEN
  MATCH_MP_TAC INT_CONG_ADD3_REM_ALT THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
    EXISTS_TAC `inverse_ntt (\n. ival((V0:num->int16) n)) i` THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_LT THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
    MP_TAC(ARITH_RULE
     `(3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2 <= 1665`) THEN
    ARITH_TAC]);;

(*** Decryption for k = 4 (FIPS 203 Algorithm 15): the message from u and
 *** v decompressed from the ciphertext, s_hat decoded from dk, u_hat and
 *** its mulcache, the product of s_hat^T and u_hat, its inverse NTT and
 *** the reduced difference v - w before compression
 ***)

let KPKE_DECRYPT_K4_RESULT = prove
 (`!dk ct (UD:num->int16) (VD:num->int16) (SS:num->int16) (UH:num->int16)
    (MC:num->int16) (WP:num->int16) (WI:num->int16) (VR:num->int16).
     (!i. i < 1024
          ==> UD i =
              word((3329 * (num_of_bytelist ct DIV 2 EXP (11 * i)) MOD
                    2 EXP 11 + 1024) DIV 2048)) /\
     (!i. i < 256
          ==> VD i =
              word((3329 * (num_of_bytelist(mlkem_slice 1408 160 ct) DIV
                            2 EXP (5 * i)) MOD 2 EXP 5 + 16) DIV 32)) /\
     (!i. i < 1024
          ==> SS i = word((num_of_bytelist dk DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(UH(256 * j + i)) ==
                 forward_ntt (\n. ival(UD(256 * j + n))) i) (mod &3329) /\
                abs(ival(UH(256 * j + i))) <= &23594) /\
     (!j p. j < 4 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(UH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(WP(2 * p)) ==
               &169 *
               ((ival(SS(768 + 2 * p + 1)) * ival(MC(384 + p)) +
                 ival(SS(768 + 2 * p)) * ival(UH(768 + 2 * p))) +
                (ival(SS(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p))) +
                (ival(SS(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p))) +
                (ival(SS(2 * p + 1)) * ival(MC p) +
                 ival(SS(2 * p)) * ival(UH(2 * p))))) (mod &3329) /\
              (ival(WP(2 * p + 1)) ==
               &169 *
               ((ival(SS(768 + 2 * p + 1)) * ival(UH(768 + 2 * p)) +
                 ival(SS(768 + 2 * p)) * ival(UH(768 + 2 * p + 1))) +
                (ival(SS(512 + 2 * p + 1)) * ival(UH(512 + 2 * p)) +
                 ival(SS(512 + 2 * p)) * ival(UH(512 + 2 * p + 1))) +
                (ival(SS(256 + 2 * p + 1)) * ival(UH(256 + 2 * p)) +
                 ival(SS(256 + 2 * p)) * ival(UH(256 + 2 * p + 1))) +
                (ival(SS(2 * p + 1)) * ival(UH(2 * p)) +
                 ival(SS(2 * p)) * ival(UH(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 256
          ==> (ival(WI i) == inverse_ntt (\n. ival(WP n)) i) (mod &3329) /\
              abs(ival(WI i)) <= &26624) /\
     (!i. i < 256 ==> ival(VR i) = ival(word_sub (VD i) (WI i)) rem &3329)
     ==> nsum {i | i < 256}
              (\i. ((4 * val(VR i) + 3329) DIV 6658) MOD 2 * 2 EXP i) =
         num_of_bytelist(kpke_decrypt mlkem1024 dk ct)`,
  let parity_tac =
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`2`; `128`; `n':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `b:num`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o
      MATCH_MP(ARITH_RULE `b < 2 ==> b = 0 \/ b = 1`)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `p < 128` THEN ARITH_TAC; ALL_TAC])
and row_tac =
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; INT_CONG_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem1024] THEN
  REWRITE_TAC[KPKE_DECRYPT_FIPS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  W(fun (_,w) ->
    let enc = find_term (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) NUM_OF_BYTELIST_MLKEM_ENCODE
            (mk_comb(`num_of_bytelist`,enc)))) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC DIVIDES_CONV);
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[MULT_CLAUSES] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(fun (_,w) ->
    let pinv = find_term (fun t -> match t with
      Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
    SUBGOAL_THEN
     (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                      pinv),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
     [MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      ALL_TAC]) THEN
  W(fun (_,w) ->
    let wt = find_term (fun t -> match t with
      Comb(Comb(Comb(Const("ring_sub",_),_),_),_) -> true | _ -> false) w in
    SUBGOAL_THEN
     (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                      wt),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
     [MATCH_MP_TAC RING_SUB THEN ASM_REWRITE_TAC[MLKEM_POLY_IN_RQ];
      ALL_TAC]) THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("num_of_int",_),
           Comb(Comb(Const("rem",_),
                Comb(Comb(Const("mlkem_compress",_),_),_)),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) MLKEM_COMPRESS_DIGIT t)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MLKEM_COEFF_POS THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VAL_EQ_NUM_OF_INT_IVAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC MLKEM_COEFF_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_SUB; MLKEM_POLY_IN_RQ] THEN
  REWRITE_TAC[MLKEM_ZQ; INT_REM_EQ] THEN
  ABBREV_TAC `fv = (num_of_bytelist (mlkem_slice 1408 160 ct) DIV
                    2 EXP (5 * i)) MOD 2 EXP 5` THEN
  SUBGOAL_THEN `(3329 * fv + 16) DIV 32 < 3329` ASSUME_TAC THENL
   [SUBGOAL_THEN `fv < 32` MP_TAC THENL
     [EXPAND_TAC "fv" THEN
      REWRITE_TAC[ARITH_RULE `32 = 2 EXP 5`; MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(word((3329 * fv + 16) DIV 32):int16) =
                &((3329 * fv + 16) DIV 32)` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_SMALL THEN
    UNDISCH_TAC `(3329 * fv + 16) DIV 32 < 3329` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(ival((WI:num->int16) i)) <= &26624` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("ival",_),Comb(Comb(Const("word_sub",_),_),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_SUB_BOUNDED t)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(3329 * fv + 16) DIV 32 < 3329` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
    UNDISCH_TAC `abs(ival((WI:num->int16) i)) <= &26624` THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY] THEN
  SIMP_TAC[MLKEM_DECODE_SMALL; ARITH_RULE `5 < 12`] THEN
  ASM_SIMP_TAC[MLKEM_DECOMPRESS_NUM; ARITH_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&((3329 * fv + 16) DIV 32) rem &3329 = &((3329 * fv + 16) DIV 32)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(b:int == d) (mod q) ==> (a - b == a - d) (mod q)`) THEN
  SUBGOAL_THEN
   `!j' n. j' < 4 /\ n < 256
           ==> (ival((UH:num->int16)(256 * j' + n)) ==
                mlkem_ntt (mlkem_poly
                  (\j''. mlkem_decompress 11
                          (mlkem_decode 11 ct (256 * j' + j'')))) n)
               (mod &3329)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MLKEM_NATIVE_NTT_CONG THEN
    EXISTS_TAC `\n. (UD:num->int16)(256 * j' + n)` THEN
    REWRITE_TAC[MLKEM_POLY_IN_RQ] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[] THEN
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `256 * j' + n' < 1024` ASSUME_TAC THENL
     [UNDISCH_TAC `j' < 4` THEN UNDISCH_TAC `n' < 256` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COEFF_MLKEM_POLY; MLKEM_DECODE_SMALL; ARITH_RULE `11 < 12`;
                 MLKEM_DECOMPRESS_NUM; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[INT_CONG_RREM] THEN
    ABBREV_TAC `fu = (num_of_bytelist ct DIV 2 EXP (11 * (256 * j' + n'))) MOD
                     2048` THEN
    SUBGOAL_THEN `fu < 2048` MP_TAC THENL
     [EXPAND_TAC "fu" THEN REWRITE_TAC[MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      DISCH_TAC] THEN
    SUBGOAL_THEN `ival(word((3329 * fu + 1024) DIV 2048):int16) =
                  &((3329 * fu + 1024) DIV 2048)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_SMALL THEN UNDISCH_TAC `fu < 2048` THEN ARITH_TAC;
      REWRITE_TAC[INT_CONG_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n'. n' < 256
         ==> (ival((WP:num->int16) n') ==
              &169 * ring_sum mlkem_zq {j' | j' < 4}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 dk (256 * j' + n))
                             (mlkem_ntt (mlkem_poly
                               (\j''. mlkem_decompress 11
                                       (mlkem_decode 11 ct (256 * j' + j'')))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 4 /\ x < 256
              ==> (ival((SS:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 dk (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 4` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 11
                        (mlkem_decode 11 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p))`; `p:num`] BASEMUL4_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 11
                        (mlkem_decode 11 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p + 1))`; `p:num`] BASEMUL4_ROW_ODD)] THEN
    row_tac;
    ALL_TAC] THEN
  W(fun (_,w) ->
    let pinv = find_term (fun t -> match t with
      Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
    MP_TAC(ISPECL [rand pinv; `\n. ival((WP:num->int16) n)`; `&169:int`;
                   `i:num`] MLKEM_NTT_INV_CONG_MUL)) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
    DISCH_TAC] THEN
  MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
  EXISTS_TAC `inverse_ntt (\n. ival((WP:num->int16) n)) i` THEN
  ASM_SIMP_TAC[]);;

(*** The modulus check of an encapsulation key for k = 4 (FIPS 203
 *** section 7.2) as the bound of its 12-bit fields
 ***)

let MLKEM_EK_CHECK_1024 = prove
 (`!ek. LENGTH ek = 1568
        ==> (mlkem_ek_check mlkem1024 ek <=>
             !i. i < 1024
                 ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12
                     < 3329)`,
  SIMP_TAC[mlkem1024; MLKEM_EK_CHECK] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The vectors as blocks: polynomial j of a vector as a function of j and of *)
(* the index of the coefficient, and the K-PKE results in that form.         *)
(* ------------------------------------------------------------------------- *)

(*** Coefficient i of polynomial j of a vector at index 256 * j + i ***)

let DIVMOD_256_BLOCK = prove
 (`!j i. i < 256 ==> (256 * j + i) DIV 256 = j /\ (256 * j + i) MOD 256 = i`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i:num`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `j:num`] THEN
  ASM_ARITH_TAC);;

let DIVMOD_LT_BLOCK = prove
 (`!n k i. i < n * k ==> i DIV n < k /\ i MOD n < n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[MULT_CLAUSES; LT; RDIV_LT_EQ; MOD_LT_EQ]);;

(*** The length of a slice of a byte list ***)

let LENGTH_MLKEM_SLICE = prove
 (`!a n (l:byte list). LENGTH(mlkem_slice a n l) = n`,
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]);;

(*** Evaluation of x DIV n and x MOD n (n a numeral) where x is c + t (c a
 *** numeral multiple of n), n * j + t, or t, given t < n from the
 *** assumptions; the terms that cannot be evaluated are left alone
 ***)

let DIVMOD_EVAL_TAC (asl,w as gl) =
  let is_dm t = match t with
      Comb(Comb(Const(("DIV"|"MOD"),_),_),n) -> is_numeral n
    | _ -> false in
  let tms = setify(find_terms is_dm w) in
  let attempt tm =
    let op = fst(dest_const(rator(rator tm))) and x = rand(rator tm)
    and n = rand tm in
    let nv = dest_numeral n in
    let q,r =
      if is_binary "+" x then
        let a = lhand x and t = rand x in
        if is_numeral a then mk_numeral(quo_num (dest_numeral a) nv),t
        else if is_binary "*" a && lhand a = n then rand a,t
        else `0`,x
      else `0`,x in
    let goal = mk_eq(tm,if op = "DIV" then q else r) in
    let tac = if op = "DIV"
              then MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC r THEN ASM_ARITH_TAC
              else MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC q THEN
                   ASM_ARITH_TAC in
    TAC_PROOF((asl,goal),tac) in
  let ths = mapfilter attempt tms in
  REWRITE_TAC ths gl;;

(*** The statement of the K-PKE key generation in terms of the polynomials
 *** of the vectors and their blocks of coefficients (functions of the
 *** index of the polynomial and of the coefficient)
 ***)

let api_param k = match k with
    2 -> "mlkem512" | 3 -> "mlkem768" | _ -> "mlkem1024";;

let api_eta1 k = if k = 2 then 3 else 2;;

let kpke_keygen_blocks_tm k =
  let ks = string_of_int k and es = string_of_int(api_eta1 k) in
  let a c =
    "mlkem_sample_ntt (APPEND rho [word "^string_of_int c^"; word r])" in
  let ev c = let cs = string_of_int c in
    "("^a c^" (2 * p + 1) * ival((MC:num->num->int16) "^cs^" p) + "^
    a c^" (2 * p) * ival((SH:num->num->int16) "^cs^" (2 * p)))" in
  let od c = let cs = string_of_int c in
    "("^a c^" (2 * p + 1) * ival((SH:num->num->int16) "^cs^" (2 * p)) + "^
    a c^" (2 * p) * ival((SH:num->num->int16) "^cs^" (2 * p + 1)))" in
  let sum f = String.concat " + " (map f (rev(0--(k-1)))) in
  parse_term(
   "!d rho sigma (SH:num->num->int16) (EH:num->num->int16) "^
   "(MC:num->num->int16) (PT:num->num->int16) (PU:num->num->int16) "^
   "(TR:num->num->int16) (SR:num->num->int16). "^
   "mlkem_g(APPEND d [word "^ks^"]) = rho,sigma /\\ "^
   "(!i j n. i < "^ks^" /\\ j < "^ks^" /\\ n < 256 ==> "^
   "  mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(SH j i) == mlkem_ntt (mlkem_cbd "^es^" (mlkem_prf "^es^
   "   sigma (word j))) i) (mod &3329) /\\ abs(ival(SH j i)) <= &23594) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(EH j i) == mlkem_ntt (mlkem_cbd "^es^" (mlkem_prf "^es^
   "   sigma (word("^ks^" + j)))) i) (mod &3329) /\\ "^
   "  abs(ival(EH j i)) <= &23594) /\\ "^
   "(!j p. j < "^ks^" /\\ p < 128 ==> "^
   "  (ival(MC j p) == ival(SH j (2 * p + 1)) * "^
   "   &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\\ "^
   "(!r p. r < "^ks^" /\\ p < 128 ==> "^
   "  (ival(PT r (2 * p)) == &169 * ("^sum ev^")) (mod &3329) /\\ "^
   "  (ival(PT r (2 * p + 1)) == &169 * ("^sum od^")) (mod &3329)) /\\ "^
   "(!r i. r < "^ks^" /\\ i < 256 ==> "^
   "  (ival(PU r i) == &65536 * ival(PT r i)) (mod &3329) /\\ "^
   "  abs(ival(PU r i)) <= &3328) /\\ "^
   "(!r i. r < "^ks^" /\\ i < 256 ==> "^
   "  ival(TR r i) = ival(word_add (PU r i) (EH r i)) rem &3329) /\\ "^
   "(!r i. r < "^ks^" /\\ i < 256 ==> ival(SR r i) = ival(SH r i) rem &3329) "^
   "==> num_of_wordlist(MAP (word_zx:int16->12 word) "^
   "      (list_of_seq (\\i. TR (i DIV 256) (i MOD 256)) "^
   string_of_int(256 * k)^")) + "^
   "    2 EXP (8 * "^string_of_int(384 * k)^") * num_of_bytelist rho = "^
   "    num_of_bytelist(FST(kpke_keygen "^api_param k^" d)) /\\ "^
   "    num_of_wordlist(MAP (word_zx:int16->12 word) "^
   "      (list_of_seq (\\i. SR (i DIV 256) (i MOD 256)) "^
   string_of_int(256 * k)^")) = "^
   "    num_of_bytelist(SND(kpke_keygen "^api_param k^" d))");;

let KPKE_KEYGEN_BLOCKS_TAC flat =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC flat THEN
  MAP_EVERY EXISTS_TAC
   [`sigma:byte list`; `\i. (SH:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (EH:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (MC:num->num->int16) (i DIV 128) (i MOD 128)`;
    `\i. (PT:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (PU:num->num->int16) (i DIV 256) (i MOD 256)`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  DIVMOD_EVAL_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC DIVMOD_LT_BLOCK THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

(*** The arithmetic of the coefficients of encryption: 16-bit sums in
 *** range, the coefficients 0 or 1665 of the message, the remainders mod q,
 *** and the two additions to v (the noise e2 and the message) with only
 *** the second reduced
 ***)

let IVAL_WORD_ADD_INRANGE = prove
 (`!x y:int16. abs(ival x + ival y) < &32768
               ==> ival(word_add x y) = ival x + ival y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add x y:int16 = iword(ival x + ival y)` SUBST1_TAC THENL
   [REWRITE_TAC[IWORD_INT_ADD; IWORD_IVAL]; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_INT_ARITH_TAC);;

let MU_CASES = prove
 (`!n i. word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2):int16 = word 0 \/
         word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2):int16 = word 1665`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n DIV 2 EXP i`; `2`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(n DIV 2 EXP i) MOD 2`,`b:num`) THEN
  REWRITE_TAC[ARITH_RULE `b < 2 <=> b = 0 \/ b = 1`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let REM_3329_BOUNDS = prove
 (`!y. &0 <= y rem &3329 /\ y rem &3329 < &3329`,
  GEN_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC INT_REM_POS THEN INT_ARITH_TAC;
    MATCH_MP_TAC INT_LT_REM THEN INT_ARITH_TAC]);;

let V_TWO_STEP = prove
 (`!(v1:int16) (e2:int16) (mu:int16) (v2:int16) (v4:int16).
     abs(ival v1) <= &26624 /\ abs(ival e2) <= &2 /\
     (mu = word 0 \/ mu = word 1665) /\
     ival v2 = ival(word_add v1 e2) rem &3329 /\
     ival v4 = ival(word_add v2 mu) rem &3329
     ==> ival v4 = ival(word_add (word_add v1 e2) mu) rem &3329`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `ival(mu:int16) = &0 \/ ival(mu:int16) = &1665`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    SIMP_TAC[IVAL_WORD_SMALL; ARITH_RULE `0 < 32768 /\ 1665 < 32768`];
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(word_add v1 e2:int16) = ival v1 + ival e2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_INRANGE THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ival(v2:int16) /\ ival(v2:int16) < &3329`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[REM_3329_BOUNDS]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(word_add v2 mu:int16) = ival v2 + ival mu`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_INRANGE THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add (word_add v1 e2) mu:int16) = (ival v1 + ival e2) + ival mu`
  ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) IVAL_WORD_ADD_INRANGE o
      lhand o snd) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[]);;

(*** An index as block and offset ***)

let DIVMOD_256_RECOMB = prove
 (`!i. 256 * (i DIV 256) + i MOD 256 = i`,
  GEN_TAC THEN MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ARITH_TAC);;

(*** The NTTs only use the first 256 coefficients ***)

let FORWARD_NTT_LOCAL = prove
 (`!f g k. (!n. n < 256 ==> f n = g n) ==> forward_ntt f k = forward_ntt g k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[forward_ntt] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ISUM_EQ THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPECL [`k:num`; `2`] MOD_LT_EQ) THEN ASM_ARITH_TAC);;

let INVERSE_NTT_LOCAL = prove
 (`!f g k. (!n. n < 256 ==> f n = g n) ==> inverse_ntt f k = inverse_ntt g k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inverse_ntt] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ISUM_EQ THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPECL [`k:num`; `2`] MOD_LT_EQ) THEN
  MP_TAC(SPEC `j:num` BITREVERSE7_BOUND) THEN ASM_ARITH_TAC);;

let FORWARD_NTT_BLOCK = prove
 (`!(U:num->num->int16) j k.
     forward_ntt (\n. ival(U ((256 * j + n) DIV 256) ((256 * j + n) MOD 256)))
                 k =
     forward_ntt (\n. ival(U j n)) k`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FORWARD_NTT_LOCAL THEN
  SIMP_TAC[DIVMOD_256_BLOCK]);;

let INVERSE_NTT_BLOCK = prove
 (`!(U:num->num->int16) j k.
     inverse_ntt (\n. ival(U ((256 * j + n) DIV 256) ((256 * j + n) MOD 256)))
                 k =
     inverse_ntt (\n. ival(U j n)) k`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INVERSE_NTT_LOCAL THEN
  SIMP_TAC[DIVMOD_256_BLOCK]);;

(*** A coefficient reduced mod q as an unsigned value below q ***)

let VAL_LT_OF_REM = prove
 (`!x:int16 y. ival x = y rem &3329 ==> val x < 3329`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `y:int` REM_3329_BOUNDS) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `x:int16` VAL_BOUND) THEN REWRITE_TAC[ival; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

(*** The statement of K-PKE encryption for k in terms of the polynomials of
 *** the vectors and their blocks of coefficients
 ***)

let api_du k = if k = 4 then 11 else 10;;
let api_dv k = if k = 4 then 5 else 4;;

let kpke_encrypt_blocks_tm k =
  let ks = string_of_int k and es = string_of_int(api_eta1 k) in
  let n x = string_of_int x in
  let rho = "(mlkem_slice "^n(384 * k)^" 32 ek)" in
  let a c = "mlkem_sample_ntt (APPEND "^rho^" [word q; word "^n c^"])" in
  let ev c = let cs = n c in
    "("^a c^" (2 * p + 1) * ival((MC:num->num->int16) "^cs^" p) + "^
    a c^" (2 * p) * ival((YH:num->num->int16) "^cs^" (2 * p)))" in
  let od c = let cs = n c in
    "("^a c^" (2 * p + 1) * ival((YH:num->num->int16) "^cs^" (2 * p)) + "^
    a c^" (2 * p) * ival((YH:num->num->int16) "^cs^" (2 * p + 1)))" in
  let tev c = let cs = n c in
    "(ival((TT:num->num->int16) "^cs^" (2 * p + 1)) * ival(MC "^cs^" p) + "^
    "ival(TT "^cs^" (2 * p)) * ival(YH "^cs^" (2 * p)))" in
  let tod c = let cs = n c in
    "(ival((TT:num->num->int16) "^cs^" (2 * p + 1)) * "^
    "ival(YH "^cs^" (2 * p)) + "^
    "ival(TT "^cs^" (2 * p)) * ival(YH "^cs^" (2 * p + 1)))" in
  let sum f = String.concat " + " (map f (rev(0--(k-1)))) in
  let du = api_du k and dv = api_dv k in
  let p2 x = n(1 lsl x) in
  parse_term(
   "!ek m r (TT:num->num->int16) (YH:num->num->int16) (MC:num->num->int16) "^
   "(E1:num->num->int16) (E2:num->int16) (MU:num->int16) "^
   "(U0:num->num->int16) (V0:num->int16) (U1:num->num->int16) "^
   "(V1:num->int16) (U3:num->num->int16) (V2:num->int16) (V4:num->int16). "^
   "(!i j n. i < "^ks^" /\\ j < "^ks^" /\\ n < 256 ==> "^
   "  mlkem_sample_ntt (APPEND "^rho^" [word j; word i]) n < &3329) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  TT j i = word((num_of_bytelist ek DIV 2 EXP (12 * (256 * j + i))) "^
   "               MOD 2 EXP 12)) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(YH j i) == mlkem_ntt (mlkem_cbd "^es^" (mlkem_prf "^es^
   "   r (word j))) i) (mod &3329) /\\ abs(ival(YH j i)) <= &23594) /\\ "^
   "(!j p. j < "^ks^" /\\ p < 128 ==> "^
   "  (ival(MC j p) == ival(YH j (2 * p + 1)) * "^
   "   &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(E1 j i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word("^ks^
   " + j))))) (mod &3329) /\\ abs(ival(E1 j i)) <= &2) /\\ "^
   "(!i. i < 256 ==> "^
   "  (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word "^n(2 * k)^
   ")))) (mod &3329) /\\ abs(ival(E2 i)) <= &2) /\\ "^
   "(!i. i < 256 ==> "^
   "  MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) "^
   "             DIV 2)) /\\ "^
   "(!q p. q < "^ks^" /\\ p < 128 ==> "^
   "  (ival(U0 q (2 * p)) == &169 * ("^sum ev^")) (mod &3329) /\\ "^
   "  (ival(U0 q (2 * p + 1)) == &169 * ("^sum od^")) (mod &3329)) /\\ "^
   "(!p. p < 128 ==> "^
   "  (ival(V0(2 * p)) == &169 * ("^sum tev^")) (mod &3329) /\\ "^
   "  (ival(V0(2 * p + 1)) == &169 * ("^sum tod^")) (mod &3329)) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(U1 j i) == inverse_ntt (\\n. ival(U0 j n)) i) (mod &3329) /\\ "^
   "  abs(ival(U1 j i)) <= &26624) /\\ "^
   "(!i. i < 256 ==> (ival(V1 i) == inverse_ntt (\\n. ival(V0 n)) i) "^
   "  (mod &3329) /\\ abs(ival(V1 i)) <= &26624) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  ival(U3 j i) = ival(word_add (U1 j i) (E1 j i)) rem &3329) /\\ "^
   "(!i. i < 256 ==> "^
   "  ival(V2 i) = ival(word_add (V1 i) (E2 i)) rem &3329) /\\ "^
   "(!i. i < 256 ==> ival(V4 i) = ival(word_add (V2 i) (MU i)) rem &3329) "^
   "==> nsum {i | i < "^n(256 * k)^"} "^
   "      (\\i. (("^p2(du+1)^" * val(U3 (i DIV 256) (i MOD 256)) + 3329) "^
   "           DIV 6658) MOD "^p2 du^" * 2 EXP ("^n du^" * i)) + "^
   "    2 EXP (8 * "^n(32 * du * k)^") * "^
   "    nsum {i | i < 256} "^
   "      (\\i. (("^p2(dv+1)^" * val(V4 i) + 3329) DIV 6658) MOD "^p2 dv^
   "           * 2 EXP ("^n dv^" * i)) = "^
   "    num_of_bytelist(kpke_encrypt "^api_param k^" ek m r)");;

let KPKE_ENCRYPT_BLOCKS_TAC flat =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC flat THEN
  MAP_EVERY EXISTS_TAC
   [`\i. (TT:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (YH:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (MC:num->num->int16) (i DIV 128) (i MOD 128)`;
    `\i. (E1:num->num->int16) (i DIV 256) (i MOD 256)`;
    `E2:num->int16`; `MU:num->int16`;
    `\i. (U0:num->num->int16) (i DIV 256) (i MOD 256)`; `V0:num->int16`;
    `\i. (U1:num->num->int16) (i DIV 256) (i MOD 256)`; `V1:num->int16`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST
   [(* v reduced twice *)
    MATCH_MP_TAC V_TWO_STEP THEN EXISTS_TAC `(V2:num->int16) i` THEN
    ASM_SIMP_TAC[MU_CASES] THEN NO_TAC;
    DIVMOD_EVAL_TAC THEN REWRITE_TAC[FORWARD_NTT_BLOCK; INVERSE_NTT_BLOCK] THEN
    ASM_SIMP_TAC[] THEN
    FIRST
     [(* the encoded t, from the blocks by i = 256 * (i DIV 256) + i MOD 256 *)
      FIRST_X_ASSUM(fun th ->
        if can (find_term (fun t -> t = `TT:num->num->int16`)) (concl th) &&
           is_forall(concl th)
        then MP_TAC(SPECL [`i DIV 256`; `i MOD 256`] th) THEN
             ANTS_TAC THENL
              [MATCH_MP_TAC DIVMOD_LT_BLOCK THEN CONV_TAC NUM_REDUCE_CONV THEN
               ASM_REWRITE_TAC[];
               REWRITE_TAC[DIVMOD_256_RECOMB]] THEN NO_TAC
        else NO_TAC);
      FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC DIVMOD_LT_BLOCK THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]];;

(*** The 12-bit fields of a 384-byte slice of ek ***)

let FIELD_OF_SLICE = prove
 (`!x j i. i < 256
           ==> (((x DIV 2 EXP (8 * (384 * j))) MOD 2 EXP (8 * 384)) DIV
                2 EXP (12 * i)) MOD 2 EXP 12 =
               (x DIV 2 EXP (12 * (256 * j + i))) MOD 2 EXP 12`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `12 * (256 * j + i) = 8 * (384 * j) + 12 * i`;
              EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`x DIV 2 EXP (8 * (384 * j))`,`y:num`) THEN GEN_TAC THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `i < 256 ==> MIN (8 * 384) (12 * i + 12) = 12 * i + 12`]);;

let FIELD_OF_SLICE_EK = prove
 (`!ek j i. 384 * j + 384 <= LENGTH ek /\ i < 256
            ==> (num_of_bytelist(mlkem_slice (384 * j) 384 ek) DIV
                 2 EXP (12 * i)) MOD 2 EXP 12 =
                (num_of_bytelist ek DIV 2 EXP (12 * (256 * j + i))) MOD
                2 EXP 12`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_SLICE_NUM] THEN
  MATCH_MP_TAC FIELD_OF_SLICE THEN ASM_REWRITE_TAC[]);;

(*** The d-bit fields of an m-byte slice, 8 * m = 256 * d ***)

let FIELD_OF_SLICE_GEN = prove
 (`!x m d j i. 8 * m = d * 256 /\ i < 256
               ==> (((x DIV 2 EXP (8 * (m * j))) MOD 2 EXP (8 * m)) DIV
                    2 EXP (d * i)) MOD 2 EXP d =
                   (x DIV 2 EXP (d * (256 * j + i))) MOD 2 EXP d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `d * (256 * j + i) = 8 * (m * j) + d * i` SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`x DIV 2 EXP (8 * (m * j))`,`y:num`) THEN GEN_TAC THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN `MIN (8 * m) (d * i + d) = d * i + d` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = b <=> b <= a`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `d * i + d = d * (i + 1)`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    REFL_TAC]);;

let FIELD_OF_SLICE_BYTES = prove
 (`!l m d j i. 8 * m = d * 256 /\ m * j + m <= LENGTH l /\ i < 256
               ==> (num_of_bytelist(mlkem_slice (m * j) m l) DIV
                    2 EXP (d * i)) MOD 2 EXP d =
                   (num_of_bytelist l DIV 2 EXP (d * (256 * j + i))) MOD
                   2 EXP d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m * j`; `m:num`; `l:byte list`] MLKEM_SLICE_NUM) THEN
  REWRITE_TAC[ASSUME `m * j + m <= LENGTH(l:byte list)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC FIELD_OF_SLICE_GEN THEN ASM_REWRITE_TAC[]);;

(*** The blocked statement of K-PKE decryption ***)

let kpke_decrypt_blocks_tm k =
  let ks = string_of_int k and n x = string_of_int x in
  let du = api_du k and dv = api_dv k in
  let sum f = String.concat " + " (map f (rev(0--(k-1)))) in
  let tev c = let cs = n c in
    "(ival((SS:num->num->int16) "^cs^" (2 * p + 1)) * ival(MC "^cs^" p) + "^
    "ival(SS "^cs^" (2 * p)) * ival(UH "^cs^" (2 * p)))" in
  let tod c = let cs = n c in
    "(ival((SS:num->num->int16) "^cs^" (2 * p + 1)) * "^
    "ival(UH "^cs^" (2 * p)) + "^
    "ival(SS "^cs^" (2 * p)) * ival(UH "^cs^" (2 * p + 1)))" in
  parse_term(
   "!dk ct (UD:num->num->int16) (VD:num->int16) (SS:num->num->int16) "^
   "(UH:num->num->int16) (MC:num->num->int16) (WP:num->int16) "^
   "(WI:num->int16) (VR:num->int16). "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> UD j i = "^
   "  word((3329 * (num_of_bytelist ct DIV 2 EXP ("^n du^
   " * (256 * j + i))) MOD 2 EXP "^n du^" + "^n(1 lsl (du-1))^") DIV "^
   n(1 lsl du)^")) /\\ "^
   "(!i. i < 256 ==> VD i = "^
   "  word((3329 * (num_of_bytelist(mlkem_slice "^n(32 * du * k)^" "^
   n(32 * dv)^" ct) DIV 2 EXP ("^n dv^" * i)) MOD 2 EXP "^n dv^" + "^
   n(1 lsl (dv-1))^") DIV "^n(1 lsl dv)^")) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  SS j i = word((num_of_bytelist dk DIV 2 EXP (12 * (256 * j + i))) "^
   "               MOD 2 EXP 12)) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(UH j i) == forward_ntt (\\n. ival(UD j n)) i) (mod &3329) /\\ "^
   "  abs(ival(UH j i)) <= &23594) /\\ "^
   "(!j p. j < "^ks^" /\\ p < 128 ==> "^
   "  (ival(MC j p) == ival(UH j (2 * p + 1)) * "^
   "   &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\\ "^
   "(!p. p < 128 ==> "^
   "  (ival(WP(2 * p)) == &169 * ("^sum tev^")) (mod &3329) /\\ "^
   "  (ival(WP(2 * p + 1)) == &169 * ("^sum tod^")) (mod &3329)) /\\ "^
   "(!i. i < 256 ==> (ival(WI i) == inverse_ntt (\\n. ival(WP n)) i) "^
   "  (mod &3329) /\\ abs(ival(WI i)) <= &26624) /\\ "^
   "(!i. i < 256 ==> ival(VR i) = ival(word_sub (VD i) (WI i)) rem &3329) "^
   "==> nsum {i | i < 256} "^
   "      (\\i. ((4 * val(VR i) + 3329) DIV 6658) MOD 2 * 2 EXP i) = "^
   "    num_of_bytelist(kpke_decrypt "^api_param k^" dk ct)");;

let KPKE_DECRYPT_BLOCKS_TAC flat =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC flat THEN
  MAP_EVERY EXISTS_TAC
   [`\i. (UD:num->num->int16) (i DIV 256) (i MOD 256)`; `VD:num->int16`;
    `\i. (SS:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (UH:num->num->int16) (i DIV 256) (i MOD 256)`;
    `\i. (MC:num->num->int16) (i DIV 128) (i MOD 128)`;
    `WP:num->int16`; `WI:num->int16`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  DIVMOD_EVAL_TAC THEN REWRITE_TAC[FORWARD_NTT_BLOCK; INVERSE_NTT_BLOCK] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && length(fst(strip_forall(concl th))) = 2
    then MP_TAC(SPECL [`i DIV 256`; `i MOD 256`] th) THEN
         ANTS_TAC THENL
          [MATCH_MP_TAC DIVMOD_LT_BLOCK THEN CONV_TAC NUM_REDUCE_CONV THEN
           ASM_REWRITE_TAC[];
           REWRITE_TAC[DIVMOD_256_RECOMB]] THEN NO_TAC
    else NO_TAC);;

(*** The blocked statements for k = 2, 3 and 4 ***)

let KPKE_KEYGEN_K2_BLOCKS = prove
 (kpke_keygen_blocks_tm 2, KPKE_KEYGEN_BLOCKS_TAC KPKE_KEYGEN_K2_RESULT);;

let KPKE_KEYGEN_K3_BLOCKS = prove
 (kpke_keygen_blocks_tm 3, KPKE_KEYGEN_BLOCKS_TAC KPKE_KEYGEN_K3_RESULT);;

let KPKE_KEYGEN_K4_BLOCKS = prove
 (kpke_keygen_blocks_tm 4, KPKE_KEYGEN_BLOCKS_TAC KPKE_KEYGEN_K4_RESULT);;

let KPKE_ENCRYPT_K2_BLOCKS = prove
 (kpke_encrypt_blocks_tm 2, KPKE_ENCRYPT_BLOCKS_TAC KPKE_ENCRYPT_K2_RESULT);;

let KPKE_ENCRYPT_K3_BLOCKS = prove
 (kpke_encrypt_blocks_tm 3, KPKE_ENCRYPT_BLOCKS_TAC KPKE_ENCRYPT_K3_RESULT);;

let KPKE_ENCRYPT_K4_BLOCKS = prove
 (kpke_encrypt_blocks_tm 4, KPKE_ENCRYPT_BLOCKS_TAC KPKE_ENCRYPT_K4_RESULT);;

let KPKE_DECRYPT_K2_BLOCKS = prove
 (kpke_decrypt_blocks_tm 2, KPKE_DECRYPT_BLOCKS_TAC KPKE_DECRYPT_K2_RESULT);;

let KPKE_DECRYPT_K3_BLOCKS = prove
 (kpke_decrypt_blocks_tm 3, KPKE_DECRYPT_BLOCKS_TAC KPKE_DECRYPT_K3_RESULT);;

let KPKE_DECRYPT_K4_BLOCKS = prove
 (kpke_decrypt_blocks_tm 4, KPKE_DECRYPT_BLOCKS_TAC KPKE_DECRYPT_K4_RESULT);;
