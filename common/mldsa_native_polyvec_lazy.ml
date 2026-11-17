(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A functional specification of the matrix products of mldsa-native's       *)
(* portable C implementation built with MLD_CONFIG_REDUCE_RAM (the lazy      *)
(* variants in polyvec_lazy.c), in the style of the other                    *)
(* common/mldsa_native_*.ml files, following the C code.                     *)
(*                                                                           *)
(* In this configuration the matrix A is never stored. Its entries are       *)
(* sampled when they are needed (mld_polymat_expand_entry), one at a time,   *)
(* and the Montgomery product of each entry with the polynomial of the       *)
(* vector is reduced on its own; the products are added up and the sum is    *)
(* reduced (mld_poly_reduce). In the default configuration, the products of  *)
(* a row are accumulated in 64 bits and reduced once                         *)
(* (mld_polyvec_pointwise_acc_montgomery). The results are congruent modulo  *)
(* q, but are not the same integers.                                         *)
(* ========================================================================= *)

needs "common/mldsa_native_sampling.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "common/mldsa_native_sign.ml";;

(* ------------------------------------------------------------------------- *)
(* Entry (i,j) of the matrix, as mld_polymat_expand_entry samples it into a  *)
(* polynomial (mld_poly_uniform of the seed rho || j || i), which is         *)
(* polynomial l * i + j of the expanded matrix mld_polyvec_matrix_expand.    *)
(* ------------------------------------------------------------------------- *)

let mld_matrix_entry = new_definition
 `mld_matrix_entry rho i j = mld_poly_uniform (mld_matrix_seed rho i j)`;;

let MLD_POLYVEC_MATRIX_EXPAND_ENTRY = prove
 (`!l rho i j c.
        j < l /\ c < 256
        ==> mld_polyvec_matrix_expand l rho ((256 * l) * i + 256 * j + c) =
            mld_matrix_entry rho i j c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_matrix_entry] THEN
  SUBGOAL_THEN `(256 * l) * i + 256 * j + c = 256 * (l * i + j) + c`
  SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MLD_POLYVEC_MATRIX_EXPAND_COEFF] THEN
  SUBGOAL_THEN `(l * i + j) DIV l = i /\ (l * i + j) MOD l = j`
   (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Row i of the product of the matrix with a vector v in the NTT domain      *)
(* (mld_polyvec_matrix_pointwise_montgomery_row_lazy): mld_lazy_acc rho v i  *)
(* n is the sum, as the code adds them up, of the Montgomery products of the *)
(* entries (i,j) with the polynomials j of v, for j <= n, and the row of l   *)
(* columns is that sum for n = l - 1, reduced. The matrix-vector product of  *)
(* k rows is the vector of these rows.                                       *)
(* ------------------------------------------------------------------------- *)

let mld_lazy_acc = define
 `(mld_lazy_acc rho (v:num->int32) i 0 =
     mld_poly_pointwise_montgomery (mld_matrix_entry rho i 0)
                                   (mld_poly_of v 0)) /\
  (mld_lazy_acc rho v i (SUC n) =
     mld_poly_add (mld_lazy_acc rho v i n)
      (mld_poly_pointwise_montgomery (mld_matrix_entry rho i (SUC n))
                                     (mld_poly_of v (SUC n))))`;;

let mld_polyvec_matrix_row_lazy = new_definition
 `mld_polyvec_matrix_row_lazy l rho (v:num->int32) i =
    mld_poly_reduce (mld_lazy_acc rho v i (l - 1))`;;

let mld_polyvec_matrix_pointwise_montgomery_lazy = new_definition
 `mld_polyvec_matrix_pointwise_montgomery_lazy l rho (v:num->int32) =
    mld_polyvec (\i. mld_polyvec_matrix_row_lazy l rho v i)`;;

(* ------------------------------------------------------------------------- *)
(* The product w = invNTT(A * NTT(y)) of signing, with y sampled by g1 from  *)
(* rho'' and kappa + j (mld_sign_y), as                                      *)
(* mld_polyvec_matrix_pointwise_montgomery_yvec_lazy computes it: column by  *)
(* column, each polynomial of y sampled and transformed in turn, the         *)
(* products of the column with the entries added to the rows, and finally    *)
(* each row reduced and transformed back. Row k gets the same sum, in the    *)
(* same order, as mld_polyvec_matrix_row_lazy for the vector NTT(y).         *)
(* ------------------------------------------------------------------------- *)

let mld_yvec_lazy_w = new_definition
 `mld_yvec_lazy_w l (g1:num->int16->num->int32) rho rhoprime kappa =
    mld_polyvec_map mld_poly_invntt_tomont
     (mld_polyvec_matrix_pointwise_montgomery_lazy l rho
       (mld_polyvec_map mld_poly_ntt
         (mld_polyvec (\j. g1 rhoprime (word(kappa + j))))))`;;

(* ------------------------------------------------------------------------- *)
(* The polynomials and coefficients of the products.                         *)
(* ------------------------------------------------------------------------- *)

let MLD_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_LAZY_COEFF = prove
 (`!l rho (v:num->int32) i c.
        c < 256
        ==> mld_polyvec_matrix_pointwise_montgomery_lazy l rho v
             (256 * i + c) =
            mld_polyvec_matrix_row_lazy l rho v i c`,
  SIMP_TAC[mld_polyvec_matrix_pointwise_montgomery_lazy; MLD_POLYVEC_COEFF]);;

let MLD_POLY_OF_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_LAZY = prove
 (`!l rho (v:num->int32) i c.
        c < 256
        ==> mld_poly_of (mld_polyvec_matrix_pointwise_montgomery_lazy l rho v)
             i c =
            mld_polyvec_matrix_row_lazy l rho v i c`,
  SIMP_TAC[mld_poly_of; MLD_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_LAZY_COEFF]);;

(* ------------------------------------------------------------------------- *)
(* The vector t = A * s1 + s2 of key generation as mld_compute_pack_t0_t1    *)
(* computes it in this configuration: as mld_compute_t of                    *)
(* common/mldsa_native_sign.ml, but with row k of A * s1hat computed by      *)
(* mld_polyvec_matrix_row_lazy. Byte j of the packing of polynomial k of t1  *)
(* or t0 depends only on that polynomial, as for mld_compute_t.              *)
(* ------------------------------------------------------------------------- *)

let mld_compute_t_lazy = new_definition
 `mld_compute_t_lazy l (unpack:(num->byte)->num->int32) p rho
                     (s1hat:num->int32) (s2:num->byte) =
    mld_polyvec
     (\k. mld_poly_caddq
           (mld_poly_reduce
             (mld_poly_add
               (mld_poly_invntt_tomont
                 (mld_polyvec_matrix_row_lazy l rho s1hat k))
               (unpack (\t. s2(p * k + t))))))`;;

let MLD_COMPUTE_T_LAZY_PACK_T1 = prove
 (`!l (unpack:(num->byte)->num->int32) p r sh s2b i k.
        k < 320
        ==> mld_polyvec_pack 320 mld_polyt1_pack
             (mld_polyvec_map mld_poly_power2round_hi
               (mld_compute_t_lazy l unpack p r sh s2b)) (320 * i + k) =
            mld_polyt1_pack
             (mld_poly_power2round_hi
               (mld_poly_caddq
                 (mld_poly_reduce
                   (mld_poly_add
                     (mld_poly_invntt_tomont
                       (mld_polyvec_matrix_row_lazy l r sh i))
                     (unpack (\t. s2b(p * i + t))))))) k`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLD_POLYVEC_PACK_COEFF] THEN
  MATCH_MP_TAC MLD_POLYT1_PACK_LOCAL THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP; mld_poly_power2round_hi;
           mld_compute_t_lazy; MLD_POLY_OF_POLYVEC]);;

let MLD_COMPUTE_T_LAZY_PACK_T0 = prove
 (`!l (unpack:(num->byte)->num->int32) p r sh s2b i k.
        k < 416
        ==> mld_polyvec_pack 416 mld_polyt0_pack
             (mld_polyvec_map mld_poly_power2round_lo
               (mld_compute_t_lazy l unpack p r sh s2b)) (416 * i + k) =
            mld_polyt0_pack
             (mld_poly_power2round_lo
               (mld_poly_caddq
                 (mld_poly_reduce
                   (mld_poly_add
                     (mld_poly_invntt_tomont
                       (mld_polyvec_matrix_row_lazy l r sh i))
                     (unpack (\t. s2b(p * i + t))))))) k`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLD_POLYVEC_PACK_COEFF] THEN
  MATCH_MP_TAC MLD_POLYT0_PACK_LOCAL THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP; mld_poly_power2round_lo;
           mld_compute_t_lazy; MLD_POLY_OF_POLYVEC]);;

(* ------------------------------------------------------------------------- *)
(* Row i of w1' in verification (see mld_verify_w1 of                        *)
(* common/mldsa_native_sign.ml) as mld_sign_verify_internal computes it in   *)
(* this configuration, with row i of A * zhat computed by                    *)
(* mld_polyvec_matrix_row_lazy.                                              *)
(* ------------------------------------------------------------------------- *)

let mld_verify_w1_lazy = new_definition
 `mld_verify_w1_lazy l (usehint:(num->int32)->(num->int32)->num->int32) rho
                     (zhat:num->int32) (cphat:num->int32) (pk:num->byte)
                     omega (hb:num->byte) i =
    usehint
     (mld_poly_caddq
       (mld_poly_invntt_tomont
         (mld_poly_reduce
           (mld_poly_sub
             (mld_polyvec_matrix_row_lazy l rho zhat i)
             (mld_poly_pointwise_montgomery
               (mld_poly_ntt
                 (mld_poly_shiftl
                   (mld_polyt1_unpack (\j. pk(32 + 320 * i + j)))))
               cphat)))))
     (mld_unpack_hints omega hb i)`;;
