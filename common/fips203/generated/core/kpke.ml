(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Equivalence of the generated and handwritten K-PKE algorithms             *)
(* (FIPS 203 Algorithms 13, 14 and 15) for all three parameter sets.         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Small arithmetic and bound facts used to discharge the side conditions    *)
(* of the component lemmas.                                                  *)
(* ------------------------------------------------------------------------- *)

let KPKE_RESIDUE_REP = prove
 (`!v. &0 <= v /\ v < &(dimindex(:N))
       ==> &(residue_rep (residue_of_int_mod v:(N)residue)) = v`,
  SIMP_TAC[RESIDUE_OF_INT_MOD_REP; INT_REM_LT; INT_OF_NUM_OF_INT]);;

(* ------------------------------------------------------------------------- *)
(* Erasing the zqlist/zarr round trips of the generated model when the       *)
(* values involved are already reduced mod q.                                *)
(* ------------------------------------------------------------------------- *)

let KPKE_ZARR_ZQLIST_EQ = prove
 (`!a i. i < 256 /\ &0 <= a i /\ a i < &3329 ==> zarr (zqlist a) i = a i`,
  SIMP_TAC[ZARR_ZQLIST] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_REM_LT THEN ASM_REWRITE_TAC[]);;

let KPKE_ZARR_ZQLIST_COEFF = prove
 (`!p i. p IN ring_carrier mlkem_rq /\ i < 256
         ==> zarr (zqlist (\n. coeff n p)) i = coeff i p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KPKE_ZARR_ZQLIST_EQ THEN
  ASM_SIMP_TAC[COEFF_RQ_BOUNDS]);;

let KPKE_ZARR_ZQLIST_NTT = prove
 (`!p i. p IN ring_carrier mlkem_rq /\ i < 256
         ==> zarr (zqlist (mlkem_ntt p)) i = mlkem_ntt p i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KPKE_ZARR_ZQLIST_EQ THEN
  ASM_SIMP_TAC[KPKE_NTT_BOUNDS]);;

let KPKE_ZARR_ZQLIST_SUM = prove
 (`!f i. i < 256
         ==> zarr (zqlist (\n. ring_sum mlkem_zq s (f n))) i =
             ring_sum mlkem_zq s (f i)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KPKE_ZARR_ZQLIST_EQ THEN
  ASM_REWRITE_TAC[KPKE_RING_SUM_BOUNDS]);;

let KPKE_ZARR_ZQLIST_DECODE_12 = prove
 (`!b g i. i < 256
           ==> zarr (zqlist (\n. mlkem_decode 12 b (g n))) i =
               mlkem_decode 12 b (g i)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KPKE_ZARR_ZQLIST_EQ THEN
  ASM_REWRITE_TAC[MLKEM_DECODE_12_BOUNDS]);;

(* ------------------------------------------------------------------------- *)
(* Reading back the residues that the generated model stores for compressed  *)
(* coefficients and for decoded d-bit fields: both are already in range, so  *)
(* the reduction mod 2^d built into residue_of_int_mod does nothing.         *)
(* ------------------------------------------------------------------------- *)

let KPKE_REP_TAC bth =
  GEN_TAC THEN MATCH_MP_TAC KPKE_RESIDUE_REP THEN
  MP_TAC(SPEC_ALL bth) THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[];;

let KPKE_REP_COMPRESS_1 = prove
 (`!x. &(residue_rep (residue_of_int_mod (mlkem_compress 1 x):(2)residue)) =
       mlkem_compress 1 x`,
  KPKE_REP_TAC (SPEC `1` KPKE_COMPRESS_BOUNDS));;

let KPKE_REP_COMPRESS_4 = prove
 (`!x. &(residue_rep (residue_of_int_mod (mlkem_compress 4 x):(16)residue)) =
       mlkem_compress 4 x`,
  KPKE_REP_TAC (SPEC `4` KPKE_COMPRESS_BOUNDS));;

let KPKE_REP_COMPRESS_5 = prove
 (`!x. &(residue_rep (residue_of_int_mod (mlkem_compress 5 x):(32)residue)) =
       mlkem_compress 5 x`,
  KPKE_REP_TAC (SPEC `5` KPKE_COMPRESS_BOUNDS));;

let KPKE_REP_COMPRESS_10 = prove
 (`!x. &(residue_rep (residue_of_int_mod (mlkem_compress 10 x):(1024)residue)) =
       mlkem_compress 10 x`,
  KPKE_REP_TAC (SPEC `10` KPKE_COMPRESS_BOUNDS));;

let KPKE_REP_COMPRESS_11 = prove
 (`!x. &(residue_rep (residue_of_int_mod (mlkem_compress 11 x):(2048)residue)) =
       mlkem_compress 11 x`,
  KPKE_REP_TAC (SPEC `11` KPKE_COMPRESS_BOUNDS));;

let KPKE_REP_DECODE_TAC d =
  REPEAT GEN_TAC THEN MATCH_MP_TAC KPKE_RESIDUE_REP THEN
  MP_TAC(SPECL [d; `b:byte list`; `i:num`] KPKE_DECODE_SMALL) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[];;

let KPKE_REP_DECODE_1 = prove
 (`!b i. &(residue_rep
            (residue_of_int_mod (mlkem_decode 1 b i):(2)residue)) =
         mlkem_decode 1 b i`,
  KPKE_REP_DECODE_TAC `1`);;

let KPKE_REP_DECODE_4 = prove
 (`!b i. &(residue_rep
            (residue_of_int_mod (mlkem_decode 4 b i):(16)residue)) =
         mlkem_decode 4 b i`,
  KPKE_REP_DECODE_TAC `4`);;

let KPKE_REP_DECODE_5 = prove
 (`!b i. &(residue_rep
            (residue_of_int_mod (mlkem_decode 5 b i):(32)residue)) =
         mlkem_decode 5 b i`,
  KPKE_REP_DECODE_TAC `5`);;

let KPKE_REP_DECODE_10 = prove
 (`!b i. &(residue_rep
            (residue_of_int_mod (mlkem_decode 10 b i):(1024)residue)) =
         mlkem_decode 10 b i`,
  KPKE_REP_DECODE_TAC `10`);;

let KPKE_REP_DECODE_11 = prove
 (`!b i. &(residue_rep
            (residue_of_int_mod (mlkem_decode 11 b i):(2048)residue)) =
         mlkem_decode 11 b i`,
  KPKE_REP_DECODE_TAC `11`);;

(* ------------------------------------------------------------------------- *)
(* Congruences for the abstraction functions: two generated lists, vectors   *)
(* or matrices are equal as soon as their in-range entries agree.            *)
(* ------------------------------------------------------------------------- *)

let KPKE_LIST_OF_SEQ_EQ = prove
 (`!(f:num->A) g n. (!i. i < n ==> f i = g i)
                    ==> list_of_seq f n = list_of_seq g n`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIST_EQ] THEN
  ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let KPKE_ZVEC_EQ = prove
 (`!k f g. (!i. i < k ==> f i = g i)
           ==> zvec k (f:num->fips203_zq list) =
               (zvec k g:(A,(P)fips203_poly)common_vec)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zvec] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC KPKE_LIST_OF_SEQ_EQ THEN ASM_SIMP_TAC[]);;

let KPKE_ZMAT_EQ = prove
 (`!k a b. ~(k = 0) /\ (!i j. i < k /\ j < k ==> a i j = b i j)
           ==> zmat k (a:num->num->fips203_zq list) =
               (zmat k b:(R,C,(P)fips203_poly)common_mat)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zmat] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC KPKE_LIST_OF_SEQ_EQ THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; DIVISION; LT_NZ]);;

(* ------------------------------------------------------------------------- *)
(* "Clean" forms of the component lemmas. The generated model keeps Z_q      *)
(* elements and compressed coefficients as residues and reads them back      *)
(* with residue_rep, and it passes polynomials through zqlist and zarr; the  *)
(* lemmas below do that bookkeeping once, so that the main proofs below see  *)
(* terms of the same shape as the handwritten model. The generated           *)
(* constants carry the parameter set in their names, so each family is       *)
(* built for k = 2, 3, 4 from one template and one tactic.                   *)
(* ------------------------------------------------------------------------- *)

let KPKE_BETA_TAC = CONV_TAC(DEPTH_CONV BETA_CONV);;

(* DecodeCompressedVector output fed to DecompressVector.                    *)

let kpke_decompressvector_clean k cfg du dvth repth =
  let s = Printf.sprintf
   "!b:byte list. \
      DecompressVector_d_%d_%d_%d_%s_Configuration_hol \
        (list_of_seq (\\i. list_of_seq \
             (\\n. residue_of_int_mod (mlkem_decode %d b (256 * i + n))) 256) %d) = \
      Value (zvec %d (\\i. zqlist \
             (\\n. mlkem_decompress %d (mlkem_decode %d b (256 * i + n)))))"
   du (1 lsl du) k cfg du k k du du in
  prove(parse_term s,
    GEN_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) dvth o lhand o snd) THEN
    SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC KPKE_ZVEC_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    KPKE_BETA_TAC THEN
    MATCH_MP_TAC ZQLIST_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; repth]);;

(* CompressVector of a vector of already reduced coefficient arrays.         *)

let kpke_compressvector_clean k cfg du cvth =
  let s = Printf.sprintf
   "!a. (!i n. i < %d /\\ n < 256 ==> &0 <= a i n /\\ a i n < &3329) \
        ==> CompressVector_d_%d_%d_%d_%s_Configuration_hol \
              (zvec %d (\\i. zqlist (a i))) = \
            Value (list_of_seq (\\i. list_of_seq \
                    (\\n. residue_of_int_mod (mlkem_compress %d (a i n))) 256) %d)"
   k du (1 lsl du) k cfg k du k in
  prove(parse_term s,
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) cvth o lhand o snd) THEN
    SIMP_TAC[ZQ_LIST_OK_ZQLIST] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC KPKE_LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN KPKE_BETA_TAC THEN
    MATCH_MP_TAC KPKE_LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN KPKE_BETA_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC KPKE_ZARR_ZQLIST_EQ THEN ASM_SIMP_TAC[]);;

(* CompressVector output fed to EncodeCompressedVector.                      *)

let kpke_encodecompressedvector_clean k cfg du ecth repth =
  let s = Printf.sprintf
   "!a. EncodeCompressedVector_d_%d_%d_%d_%s_Configuration_hol \
          (list_of_seq (\\i. list_of_seq \
            (\\n. residue_of_int_mod (mlkem_compress %d (a i n))) 256) %d) = \
        Value (mlkem_encode %d %d \
                (\\n. mlkem_compress %d (a (n DIV 256) (n MOD 256))))"
   du (1 lsl du) k cfg du k du (256 * k) du in
  prove(parse_term s,
    GEN_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) ecth o lhand o snd) THEN
    SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MLKEM_ENCODE_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; repth; MOD_LT_EQ; RDIV_LT_EQ; ARITH]);;

(* ZqByteEncodeVector12 of a vector of already reduced coefficient arrays.   *)

let kpke_zqbyteencodevector_clean k cfg zeth =
  let s = Printf.sprintf
   "!a. (!i n. i < %d /\\ n < 256 ==> &0 <= a i n /\\ a i n < &3329) \
        ==> ZqByteEncodeVector12_%d_FIPS203_NTT_%s_Configuration_hol \
              (zvec %d (\\i. zqlist (a i))) = \
            Value (mlkem_encode 12 %d (\\n. a (n DIV 256) (n MOD 256)))"
   k k cfg k (256 * k) in
  prove(parse_term s,
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) zeth o lhand o snd) THEN
    SIMP_TAC[ZQ_LIST_OK_ZQLIST] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MLKEM_ENCODE_EQ THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN KPKE_BETA_TAC THEN
    MATCH_MP_TAC KPKE_ZARR_ZQLIST_EQ THEN
    ASM_SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ; ARITH] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ; ARITH]);;

(* ZqByteDecodeVector12 applied to the first 384 * k bytes of an            *)
(* encapsulation key: the 12-bit fields read are the same as those of the    *)
(* whole key, because they all lie inside the prefix.                        *)

let kpke_zqbytedecodevector_slice k cfg zdth =
  let s = Printf.sprintf
   "!b:byte list. LENGTH b = %d \
      ==> ZqByteDecodeVector12_%d_%s_Configuration_hol (mlkem_slice 0 %d b) = \
          Value (zvec %d (\\i. zqlist (\\n. mlkem_decode 12 b (256 * i + n))))"
   (384 * k + 32) k cfg (384 * k) k in
  prove(parse_term s,
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) zdth o lhand o snd) THEN
    REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC KPKE_ZVEC_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN KPKE_BETA_TAC THEN
    MATCH_MP_TAC ZQLIST_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    KPKE_BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC KPKE_DECODE_SLICE_0 THEN ASM_ARITH_TAC);;

(* The T_q vector and matrix operations on already reduced arrays.          *)

let kpke_tqvectordot_clean k cfg dotth =
  let s = Printf.sprintf
   "!u v. (!j n. j < %d /\\ n < 256 \
                 ==> (&0 <= u j n /\\ u j n < &3329) /\\ \
                     (&0 <= v j n /\\ v j n < &3329)) \
          ==> TqVectorDot_%d_%s_Configuration_hol \
                (zvec %d (\\i. zqlist (u i))) (zvec %d (\\i. zqlist (v i))) = \
              Value (FIPS203_Poly \
                      (zqlist (\\n. ring_sum mlkem_zq {j | j < %d} \
                                    (\\j. fips203_multiply_ntts (u j) (v j) n))))"
   k k cfg k k k in
  prove(parse_term s,
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) dotth o lhand o snd) THEN
    REWRITE_TAC[ZQ_LIST_OK_ZQLIST] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC ZQLIST_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN KPKE_BETA_TAC THEN
    MATCH_MP_TAC RING_SUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC FIPS203_MULTIPLY_NTTS_EQ THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC KPKE_ZARR_ZQLIST_EQ THEN ASM_SIMP_TAC[]);;

let kpke_tqvectoradd_clean k cfg addth =
  let s = Printf.sprintf
   "!u v. (!j n. j < %d /\\ n < 256 \
                 ==> (&0 <= u j n /\\ u j n < &3329) /\\ \
                     (&0 <= v j n /\\ v j n < &3329)) \
          ==> TqVectorAdd_%d_%s_Configuration_hol \
                (zvec %d (\\i. zqlist (u i))) (zvec %d (\\i. zqlist (v i))) = \
              Value (zvec %d \
                      (\\i. zqlist (\\n. ring_add mlkem_zq (u i n) (v i n))))"
   k k cfg k k k in
  prove(parse_term s,
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) addth o lhand o snd) THEN
    REWRITE_TAC[ZQ_LIST_OK_ZQLIST] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC KPKE_ZVEC_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN KPKE_BETA_TAC THEN
    MATCH_MP_TAC ZQLIST_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[KPKE_ZARR_ZQLIST_EQ]);;

let kpke_tqmatrixvectormul_clean k cfg transposed mvth =
  let entry = if transposed then "a j i" else "a i j"
  and name = if transposed then "TqMatrixTransposeVectorMul" else "TqMatrixVectorMul" in
  let s = Printf.sprintf
   "!a v. (!i j n. i < %d /\\ j < %d /\\ n < 256 \
                   ==> &0 <= a i j n /\\ a i j n < &3329) /\\ \
          (!j n. j < %d /\\ n < 256 ==> &0 <= v j n /\\ v j n < &3329) \
          ==> %s_%d_%s_Configuration_hol \
                (zmat %d (\\i j. zqlist (a i j))) (zvec %d (\\i. zqlist (v i))) = \
              Value (zvec %d \
                      (\\i. zqlist (\\n. ring_sum mlkem_zq {j | j < %d} \
                                   (\\j. fips203_multiply_ntts (%s) (v j) n))))"
   k k k name k cfg k k k k entry in
  prove(parse_term s,
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) mvth o lhand o snd) THEN
    REWRITE_TAC[ZQ_LIST_OK_ZQLIST] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC KPKE_ZVEC_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN KPKE_BETA_TAC THEN
    MATCH_MP_TAC ZQLIST_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN KPKE_BETA_TAC THEN
    MATCH_MP_TAC RING_SUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC FIPS203_MULTIPLY_NTTS_EQ THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC KPKE_ZARR_ZQLIST_EQ THEN ASM_SIMP_TAC[]);;

let kpke_tqvectornttinv_clean k cfg ntith =
  let s = Printf.sprintf
   "!a. (!i n. i < %d /\\ n < 256 ==> &0 <= a i n /\\ a i n < &3329) \
        ==> TqVectorNTTInv_%d_%s_Configuration_hol \
              (zvec %d (\\i. zqlist (a i))) = \
            Value (zvec %d (\\i. zqlist (\\n. coeff n (mlkem_ntt_inv (a i)))))"
   k k cfg k k in
  prove(parse_term s,
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) ntith o lhand o snd) THEN
    REWRITE_TAC[ZQ_LIST_OK_ZQLIST] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC KPKE_ZVEC_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN KPKE_BETA_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MLKEM_NTT_INV_EQ THEN ASM_SIMP_TAC[KPKE_ZARR_ZQLIST_EQ]);;

(* The single-polynomial inverse NTT, compression and decompression.        *)

let KPKE_NTTINV_CLEAN = prove
 (`!a. (!n. n < 256 ==> &0 <= a n /\ a n < &3329)
       ==> NTTInv_hol (FIPS203_Poly (zqlist a)) =
           Value (FIPS203_Poly (zqlist (\n. coeff n (mlkem_ntt_inv a))))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NTTINV_HOL_EQ o lhand o snd) THEN
  REWRITE_TAC[ZQ_LIST_OK_ZQLIST] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC MLKEM_NTT_INV_EQ THEN ASM_SIMP_TAC[KPKE_ZARR_ZQLIST_EQ]);;

let kpke_decompress_clean d decth repth =
  let s = Printf.sprintf
   "!b:byte list. \
      Decompress_d_%d_hol \
        (list_of_seq (\\n. residue_of_int_mod (mlkem_decode %d b n)) 256) = \
      Value (FIPS203_Poly \
              (zqlist (\\n. mlkem_decompress %d (mlkem_decode %d b n))))"
   d d d d in
  prove(parse_term s,
    GEN_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) decth o lhand o snd) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC ZQLIST_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; repth]);;

let kpke_compress_clean d cth =
  let s = Printf.sprintf
   "!a. (!n. n < 256 ==> &0 <= a n /\\ a n < &3329) \
        ==> Compress_d_%d_%d_hol (FIPS203_Poly (zqlist a)) = \
            Value (list_of_seq \
                    (\\n. residue_of_int_mod (mlkem_compress %d (a n))) 256)"
   d (1 lsl d) d in
  prove(parse_term s,
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) cth o lhand o snd) THEN
    REWRITE_TAC[ZQ_LIST_OK_ZQLIST] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC KPKE_LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN KPKE_BETA_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC KPKE_ZARR_ZQLIST_EQ THEN ASM_SIMP_TAC[]);;

let kpke_byteencode_clean d beth repth =
  let s = Printf.sprintf
   "!a. ByteEncode_d_%d_hol \
          (list_of_seq (\\n. residue_of_int_mod (mlkem_compress %d (a n))) 256) = \
        Value (mlkem_encode %d 256 (\\n. mlkem_compress %d (a n)))"
   d d d d in
  prove(parse_term s,
    GEN_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) beth o lhand o snd) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MLKEM_ENCODE_EQ THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; repth]);;

(* The same, for the u part of a ciphertext: the generated model decodes the *)
(* first 32 * du * k bytes of c, the handwritten one indexes into c itself.  *)

let kpke_decompressvector_slice k cfg du clen dvth repth =
  let s = Printf.sprintf
   "!c:byte list. LENGTH c = %d \
      ==> DecompressVector_d_%d_%d_%d_%s_Configuration_hol \
            (list_of_seq (\\i. list_of_seq \
              (\\n. residue_of_int_mod \
                     (mlkem_decode %d (mlkem_slice 0 %d c) (256 * i + n))) 256) %d) = \
          Value (zvec %d (\\i. zqlist \
                 (\\n. mlkem_decompress %d (mlkem_decode %d c (256 * i + n)))))"
   clen du (1 lsl du) k cfg du (32 * du * k) k k du du in
  prove(parse_term s,
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) dvth o lhand o snd) THEN
    SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC KPKE_ZVEC_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    KPKE_BETA_TAC THEN
    MATCH_MP_TAC ZQLIST_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; repth] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC KPKE_DECODE_SLICE_0 THEN ASM_ARITH_TAC);;

(* The rewrites that drive the monadic chain of a generated algorithm: the  *)
(* bind/loop plumbing, the list slices and extents, the zqlist/zarr/zpoly   *)
(* bookkeeping, and the facts needed to see that all the Z_q values that    *)
(* occur are already reduced.                                              *)

let kpke_base_ths =
  [NATIVE_BIND_VALUE; INT_ARITH_APOW; INT_POW_ONE; INT_MUL_RID;
   TYPED_HOL_NONNEGATIVE; TYPED_HOL_BIT_VALUE; TYPED_HOL_INT_TO_BYTE;
   ONEBYTE_HOL; G_SEMANTIC; PRF_SEMANTIC;
   LIST_SLICE_BYTES; SEQUENCE_EXTENT; LENGTH_MLKEM_SLICE; ARITH;
   LENGTH_LIST_OF_SEQ; ZQ_LIST_OK_ZQLIST; LENGTH_ZQLIST;
   ZPOLY_ZQLIST; MLKEM_POLY_COEFF; MLKEM_POLY_IN_RQ; MLKEM_CBD_IN_RQ;
   ZPOLY_IN_RQ; RING_SUB; RING_ADD; COEFF_RQ_BOUNDS;
   MLKEM_DECODE_12_BOUNDS; KPKE_NTT_POLY_BOUNDS; KPKE_NTT_BOUNDS;
   KPKE_RING_SUM_BOUNDS; KPKE_NTT_INV_SUM_IN_RQ];;

(* HOL Light's SIMP_TAC allows conditional rewriting to nest three deep.    *)
(* Discharging a bound on a coefficient of a nested ring_add needs more, so  *)
(* use the same simplifier with a larger level.                             *)

let KPKE_SIMP_CONV thl = GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 8 thl;;

let KPKE_SIMP_TAC thl = CONV_TAC(KPKE_SIMP_CONV thl);;

let KPKE_ASM_SIMP_TAC = ASM KPKE_SIMP_TAC;;

(* ------------------------------------------------------------------------- *)
(* K-PKE decryption. The generated model splits the ciphertext, decodes and  *)
(* decompresses u and v, forward-transforms u, takes the dot product with    *)
(* the secret in the NTT domain and transforms back; that is exactly the     *)
(* NTT-domain form KPKE_DECRYPT_FIPS of the handwritten algorithm.           *)
(* ------------------------------------------------------------------------- *)

let kpke_decrypt_equiv stmt k cfg du dv paramth defth decvecth dvecth
                       bdecth decth zdecth nttth dotth cth beth =
  prove(stmt,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[defth] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    KPKE_ASM_SIMP_TAC (kpke_base_ths @
      [decvecth;
       kpke_decompressvector_slice k cfg du (32 * (du * k + dv)) dvecth
         (if du = 10 then KPKE_REP_DECODE_10 else KPKE_REP_DECODE_11);
       bdecth;
       kpke_decompress_clean dv decth
         (if dv = 4 then KPKE_REP_DECODE_4 else KPKE_REP_DECODE_5);
       zdecth; nttth;
       kpke_tqvectordot_clean k cfg dotth;
       KPKE_NTTINV_CLEAN; RQPOLYSUB_HOL_EQ;
       kpke_compress_clean 1 cth;
       kpke_byteencode_clean 1 beth KPKE_REP_COMPRESS_1]) THEN
    REWRITE_TAC[paramth; KPKE_DECRYPT_FIPS] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV);;

let KPKE_DECRYPT_512_EQUIV = kpke_decrypt_equiv
  KPKE_DECRYPT_512_EQUIV_STMT 2 "MLKEM512" 10 4 mlkem512
  K_PKE_Decrypt_MLKEM512_Configuration_hol_DEF
  DECODECOMPRESSEDVECTOR_2 DECOMPRESSVECTOR_2
  BYTEDECODE_4 DECOMPRESS_4 ZQBYTEDECODEVECTOR12_2 TQVECTORNTT_2
  TQVECTORDOT_2 COMPRESS_1 BYTEENCODE_1;;

let KPKE_DECRYPT_768_EQUIV = kpke_decrypt_equiv
  KPKE_DECRYPT_768_EQUIV_STMT 3 "MLKEM768" 10 4 mlkem768
  K_PKE_Decrypt_MLKEM768_Configuration_hol_DEF
  DECODECOMPRESSEDVECTOR_3 DECOMPRESSVECTOR_3
  BYTEDECODE_4 DECOMPRESS_4 ZQBYTEDECODEVECTOR12_3 TQVECTORNTT_3
  TQVECTORDOT_3 COMPRESS_1 BYTEENCODE_1;;

let KPKE_DECRYPT_1024_EQUIV = kpke_decrypt_equiv
  KPKE_DECRYPT_1024_EQUIV_STMT 4 "MLKEM1024" 11 5 mlkem1024
  K_PKE_Decrypt_MLKEM1024_Configuration_hol_DEF
  DECODECOMPRESSEDVECTOR_4 DECOMPRESSVECTOR_4
  BYTEDECODE_5 DECOMPRESS_5 ZQBYTEDECODEVECTOR12_4 TQVECTORNTT_4
  TQVECTORDOT_4 COMPRESS_1 BYTEENCODE_1;;

(* ------------------------------------------------------------------------- *)
(* The loops of key generation and encryption. Each one folds over a         *)
(* schedule of at most four indices, so we expand the schedule into an       *)
(* explicit list, run the body on each index, and then gather the resulting  *)
(* explicit Common_Vec / Common_Mat back into zvec / zmat form.              *)
(* ------------------------------------------------------------------------- *)

let KPKE_SEQ_EXPAND_TAC =
  REPEAT(CONV_TAC(ONCE_DEPTH_CONV num_CONV) THEN
         REWRITE_TAC[LIST_OF_SEQ; REPLICATE; o_THM]) THEN
  REWRITE_TAC[];;

let kpke_list_of_seq n =
  let items = String.concat "; " (map (fun i -> Printf.sprintf "f %d" i)
                                      (0--(n-1))) in
  prove(parse_term
          (Printf.sprintf "!f:num->A. list_of_seq f %d = [%s]" n items),
        KPKE_SEQ_EXPAND_TAC);;

let kpke_replicate n =
  let items = String.concat "; " (map (fun i -> "x") (0--(n-1))) in
  prove(parse_term
          (Printf.sprintf "!x:A. REPLICATE %d x = [%s]" n items),
        KPKE_SEQ_EXPAND_TAC);;

let KPKE_GATHER_TAC k =
  REWRITE_TAC[zvec; zmat] THEN TRY(CONV_TAC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[kpke_list_of_seq k; kpke_list_of_seq (k * k)] THEN
  TRY(CONV_TAC(DEPTH_CONV BETA_CONV)) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV) THEN TRY REFL_TAC;;

(* The matrix A-hat built by the double loop over i and j.                   *)

let kpke_gather_mat k =
  let entry n = Printf.sprintf
    "FIPS203_Poly (zqlist (mlkem_sample_ntt (APPEND rho [word %d; word %d])))"
    (n mod k) (n / k) in
  let items = String.concat "; " (map entry (0--(k * k - 1))) in
  prove(parse_term (Printf.sprintf
    "!rho:byte list. \
       Common_Mat (FIPS_Matrix [%s]) = \
       zmat %d (\\i j. zqlist (mlkem_sample_ntt (APPEND rho [word j; word i])))"
    items k),
    KPKE_GATHER_TAC k);;

(* A vector of k samples of the centred binomial distribution, with the      *)
(* byte counter running from off; off is "i" for the first such loop of an   *)
(* algorithm and "k + i" for the second.                                     *)

let kpke_gather_cbd k eta off offs =
  let entry i = Printf.sprintf
    "FIPS203_Poly (zqlist (\\n. coeff n (mlkem_cbd %d (mlkem_prf %d s (word %d)))))"
    eta eta (off + i) in
  let items = String.concat "; " (map entry (0--(k-1))) in
  prove(parse_term (Printf.sprintf
    "!s:byte list. \
       Common_Vec [%s] = \
       zvec %d (\\i. zqlist (\\n. coeff n (mlkem_cbd %d (mlkem_prf %d s (word (%s))))))"
    items k eta eta offs),
    KPKE_GATHER_TAC k);;

let KPKE_REDUCE_TAC = CONV_TAC(DEPTH_CONV(INT_RED_CONV ORELSEC NUM_RED_CONV));;

(* The rewrites that run a generated loop: the fold and schedule plumbing,   *)
(* the explicit initial vectors and matrices, and the field updates.         *)

let kpke_loop_ths k =
  [native_foldl_DEF; UNCURRY_DEF; BITVAL_CLAUSES; LENGTH; MAP;
   GSYM APPEND_ASSOC; APPEND; isa_list_update;
   NOMINAL_UPDATE_MAT; NOMINAL_UPDATE_VEC; NOMINAL_UPDATE_POLY;
   NATIVE_LIST_UPDATE; LENGTH_ISA_LIST_UPDATE; KPKE_LENGTH_PRF;
   KPKE_ZQ_ADD_BOUNDS; kpke_replicate k; kpke_replicate (k * k);
   kpke_gather_mat k];;

(* ------------------------------------------------------------------------- *)
(* K-PKE key generation. The generated model samples A-hat with a double     *)
(* loop, samples s and e with two loops sharing a byte counter (so e uses    *)
(* the bytes k, ..., 2k-1), transforms s and e, computes t-hat = A-hat s-hat *)
(* + e-hat and encodes t-hat and s-hat; that is the NTT-domain form          *)
(* KPKE_KEYGEN_FIPS of the handwritten algorithm. The sampling hypothesis    *)
(* of KPKE_KEYGEN_FIPS follows from sample_ok through SAMPLE_OK_BOUND.       *)
(* ------------------------------------------------------------------------- *)

let kpke_keygen_equiv stmt k cfg eta1 paramth defth cbdth nttth mvth addth
                      zeth =
  let bounds = parse_term (Printf.sprintf
    "!i j n. i < %d /\\ j < %d /\\ n < 256 \
     ==> &0 <= mlkem_sample_ntt \
                (APPEND (FST (mlkem_g (APPEND d [word %d]))) [word j; word i]) n /\\ \
         mlkem_sample_ntt \
          (APPEND (FST (mlkem_g (APPEND d [word %d]))) [word j; word i]) n < &3329"
    k k k k)
  and gterm = parse_term (Printf.sprintf
    "mlkem_g (APPEND (d:byte list) [word %d])" k) in
  prove(stmt,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN bounds ASSUME_TAC THENL
     [ASM_SIMP_TAC[SAMPLE_OK_BOUND]; ALL_TAC] THEN
    REWRITE_TAC[defth] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SIMP_TAC[NATIVE_SCHEDULE_UPTO; ARITH] THEN
    REWRITE_TAC[ADD_CLAUSES; kpke_list_of_seq k] THEN
    REPEAT(CHANGED_TAC(KPKE_ASM_SIMP_TAC (kpke_base_ths @ kpke_loop_ths k @
            [kpke_gather_cbd k eta1 0 "i";
             kpke_gather_cbd k eta1 k (Printf.sprintf "%d + i" k);
             SAMPLENTT_HOL_EQ; cbdth; nttth;
             kpke_tqmatrixvectormul_clean k cfg false mvth;
             kpke_tqvectoradd_clean k cfg addth;
             kpke_zqbyteencodevector_clean k cfg zeth]))
           ORELSE CHANGED_TAC KPKE_REDUCE_TAC) THEN
    ASM_SIMP_TAC[paramth; KPKE_KEYGEN_FIPS] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    SPEC_TAC(gterm, `gp:byte list#byte list`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`rho:byte list`; `sigma:byte list`] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV);;

let KPKE_KEYGEN_512_EQUIV = kpke_keygen_equiv
  KPKE_KEYGEN_512_EQUIV_STMT 2 "MLKEM512" 3 mlkem512
  K_PKE_KeyGen_MLKEM512_Configuration_hol_DEF
  CBD_3 TQVECTORNTT_2 TQMATRIXVECTORMUL_2 TQVECTORADD_2
  ZQBYTEENCODEVECTOR12_2;;

let KPKE_KEYGEN_768_EQUIV = kpke_keygen_equiv
  KPKE_KEYGEN_768_EQUIV_STMT 3 "MLKEM768" 2 mlkem768
  K_PKE_KeyGen_MLKEM768_Configuration_hol_DEF
  CBD_2 TQVECTORNTT_3 TQMATRIXVECTORMUL_3 TQVECTORADD_3
  ZQBYTEENCODEVECTOR12_3;;

let KPKE_KEYGEN_1024_EQUIV = kpke_keygen_equiv
  KPKE_KEYGEN_1024_EQUIV_STMT 4 "MLKEM1024" 2 mlkem1024
  K_PKE_KeyGen_MLKEM1024_Configuration_hol_DEF
  CBD_2 TQVECTORNTT_4 TQMATRIXVECTORMUL_4 TQVECTORADD_4
  ZQBYTEENCODEVECTOR12_4;;

(* ------------------------------------------------------------------------- *)
(* K-PKE encryption. The generated model splits the encapsulation key,       *)
(* decodes t-hat, resamples A-hat from rho, samples y, e1 (whose byte        *)
(* counter continues after y, so it uses bytes k, ..., 2k-1) and e2 (byte    *)
(* 2k), and forms u = NTTInv(A-hat^T y-hat) + e1 and                        *)
(* v = NTTInv(t-hat^T y-hat) + e2 + mu; that is the NTT-domain form          *)
(* KPKE_ENCRYPT_FIPS of the handwritten algorithm.                          *)
(* ------------------------------------------------------------------------- *)

let kpke_encrypt_equiv stmt k cfg eta1 eta2 du dv paramth defth zdecth nttth
                       mtvth ntith vaddth dec1th dotth cvth ecth cth beth =
  let bounds = parse_term (Printf.sprintf
    "!i j n. i < %d /\\ j < %d /\\ n < 256 \
     ==> &0 <= mlkem_sample_ntt \
                (APPEND (mlkem_slice %d 32 ek) [word j; word i]) n /\\ \
         mlkem_sample_ntt (APPEND (mlkem_slice %d 32 ek) [word j; word i]) n \
         < &3329"
    k k (384 * k) (384 * k)) in
  prove(stmt,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN bounds ASSUME_TAC THENL
     [ASM_SIMP_TAC[SAMPLE_OK_BOUND]; ALL_TAC] THEN
    REWRITE_TAC[defth] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SIMP_TAC[NATIVE_SCHEDULE_UPTO; ARITH] THEN
    REWRITE_TAC[ADD_CLAUSES; kpke_list_of_seq k] THEN
    REPEAT(CHANGED_TAC(KPKE_ASM_SIMP_TAC (kpke_base_ths @ kpke_loop_ths k @
            [kpke_gather_cbd k eta1 0 "i";
             kpke_gather_cbd k eta2 k (Printf.sprintf "%d + i" k);
             SAMPLENTT_HOL_EQ; CBD_2; CBD_3; nttth;
             kpke_zqbytedecodevector_slice k cfg zdecth;
             kpke_tqmatrixvectormul_clean k cfg true mtvth;
             kpke_tqvectornttinv_clean k cfg ntith;
             vaddth; BYTEDECODE_1;
             kpke_decompress_clean 1 dec1th KPKE_REP_DECODE_1;
             kpke_tqvectordot_clean k cfg dotth;
             KPKE_NTTINV_CLEAN; RQPOLYADD_HOL_EQ;
             kpke_compressvector_clean k cfg du cvth;
             kpke_encodecompressedvector_clean k cfg du ecth
               (if du = 10 then KPKE_REP_COMPRESS_10 else KPKE_REP_COMPRESS_11);
             kpke_compress_clean dv cth;
             kpke_byteencode_clean dv beth
               (if dv = 4 then KPKE_REP_COMPRESS_4 else KPKE_REP_COMPRESS_5)]))
           ORELSE CHANGED_TAC KPKE_REDUCE_TAC) THEN
    ASM_SIMP_TAC[paramth; KPKE_ENCRYPT_FIPS; ARITH] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV);;

let KPKE_ENCRYPT_512_EQUIV = kpke_encrypt_equiv
  KPKE_ENCRYPT_512_EQUIV_STMT 2 "MLKEM512" 3 2 10 4 mlkem512
  K_PKE_Encrypt_MLKEM512_Configuration_hol_DEF
  ZQBYTEDECODEVECTOR12_2 TQVECTORNTT_2 TQMATRIXTRANSPOSEVECTORMUL_2
  TQVECTORNTTINV_2 RQVECTORADD_2 DECOMPRESS_1 TQVECTORDOT_2
  COMPRESSVECTOR_2 ENCODECOMPRESSEDVECTOR_2 COMPRESS_4 BYTEENCODE_4;;

let KPKE_ENCRYPT_768_EQUIV = kpke_encrypt_equiv
  KPKE_ENCRYPT_768_EQUIV_STMT 3 "MLKEM768" 2 2 10 4 mlkem768
  K_PKE_Encrypt_MLKEM768_Configuration_hol_DEF
  ZQBYTEDECODEVECTOR12_3 TQVECTORNTT_3 TQMATRIXTRANSPOSEVECTORMUL_3
  TQVECTORNTTINV_3 RQVECTORADD_3 DECOMPRESS_1 TQVECTORDOT_3
  COMPRESSVECTOR_3 ENCODECOMPRESSEDVECTOR_3 COMPRESS_4 BYTEENCODE_4;;

let KPKE_ENCRYPT_1024_EQUIV = kpke_encrypt_equiv
  KPKE_ENCRYPT_1024_EQUIV_STMT 4 "MLKEM1024" 2 2 11 5 mlkem1024
  K_PKE_Encrypt_MLKEM1024_Configuration_hol_DEF
  ZQBYTEDECODEVECTOR12_4 TQVECTORNTT_4 TQMATRIXTRANSPOSEVECTORMUL_4
  TQVECTORNTTINV_4 RQVECTORADD_4 DECOMPRESS_1 TQVECTORDOT_4
  COMPRESSVECTOR_4 ENCODECOMPRESSEDVECTOR_4 COMPRESS_5 BYTEENCODE_5;;
