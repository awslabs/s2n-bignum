(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A functional specification of the matrix-vector products of               *)
(* mldsa-native's portable C implementation with MLD_CONFIG_REDUCE_RAM       *)
(* (polyvec_lazy.c), in the style of the other common/mldsa_native_*.ml      *)
(* files, following the C code. With MLD_CONFIG_REDUCE_RAM the matrix A is   *)
(* not stored: each entry is sampled from rho when it is used, and each      *)
(* product of an entry with a polynomial of the vector is reduced            *)
(* (mld_poly_pointwise_montgomery) before it is added to the others, while   *)
(* without it the products of a row are accumulated in 64 bits and reduced   *)
(* once (mld_polyvec_pointwise_acc_montgomery). The results are congruent    *)
(* mod q but not equal as words.                                             *)
(* ========================================================================= *)

needs "common/mldsa_native_sampling.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "common/mldsa_native_sign.ml";;

(* ------------------------------------------------------------------------- *)
(* Entry (i,j) of the matrix expanded from rho, as mld_polymat_expand_entry  *)
(* (polyvec_lazy.c) samples it: mld_poly_uniform of the seed rho || j || i.  *)
(* It is polynomial l * i + j of mld_polyvec_matrix_expand l rho.            *)
(* ------------------------------------------------------------------------- *)

let mld_matrix_entry = new_definition
 `mld_matrix_entry rho i j = mld_poly_uniform (mld_matrix_seed rho i j)`;;

(* ------------------------------------------------------------------------- *)
(* The products of row i of the matrix with the polynomials 0..n of the      *)
(* vector v, each reduced with mld_poly_pointwise_montgomery and added with  *)
(* mld_poly_add in the order of the C loops: the first product, then the     *)
(* others added to it one by one.                                            *)
(* ------------------------------------------------------------------------- *)

let mld_lazy_acc = define
 `(mld_lazy_acc rho i (v:num->int32) 0 =
     mld_poly_pointwise_montgomery (mld_matrix_entry rho i 0)
                                   (mld_poly_of v 0)) /\
  (mld_lazy_acc rho i v (SUC n) =
     mld_poly_add (mld_lazy_acc rho i v n)
      (mld_poly_pointwise_montgomery (mld_matrix_entry rho i (SUC n))
                                     (mld_poly_of v (SUC n))))`;;

(* ------------------------------------------------------------------------- *)
(* mld_polyvec_matrix_pointwise_montgomery_row_lazy: row i of A times the    *)
(* vector v of l polynomials (in the NTT domain), reduced with               *)
(* mld_poly_reduce.                                                          *)
(* ------------------------------------------------------------------------- *)

let mld_polyvec_matrix_row_lazy = new_definition
 `mld_polyvec_matrix_row_lazy l rho (v:num->int32) i =
    mld_poly_reduce (mld_lazy_acc rho i v (l - 1))`;;

(* ------------------------------------------------------------------------- *)
(* mld_polyvec_matrix_pointwise_montgomery_yvec_lazy: w = A y for the        *)
(* vector y of l polynomials (not in the NTT domain), which the code samples *)
(* polynomial by polynomial and transforms to the NTT domain, accumulating   *)
(* the products column by column into the vector of the sums of the rows,    *)
(* which it then reduces with mld_polyveck_reduce and transforms back with   *)
(* mld_polyveck_invntt_tomont.                                               *)
(* ------------------------------------------------------------------------- *)

let mld_polyvec_matrix_yvec_lazy = new_definition
 `mld_polyvec_matrix_yvec_lazy l rho (y:num->int32) =
    mld_polyvec_map mld_poly_invntt_tomont
     (mld_polyvec_map mld_poly_reduce
       (mld_polyvec
         (\i. mld_lazy_acc rho i (mld_polyvec_map mld_poly_ntt y) (l - 1))))`;;

(* ------------------------------------------------------------------------- *)
(* mld_compute_pack_t0_t1: the vector t = A s1 + s2 of key generation, made  *)
(* nonnegative, with row k of A s1 computed by                               *)
(* mld_polyvec_matrix_pointwise_montgomery_row_lazy, as mld_compute_t of     *)
(* common/mldsa_native_sign.ml is without MLD_CONFIG_REDUCE_RAM; and the     *)
(* polynomials of t1 and t0 packed.                                          *)
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
