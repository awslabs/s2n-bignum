(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The results of the lazy matrix products of the reduced-RAM configuration  *)
(* are those of the default one, where they matter: the statements.         *)
(*                                                                           *)
(* With MLD_CONFIG_REDUCE_RAM the matrix A is sampled entry by entry when    *)
(* it is needed, and the Montgomery products of its entries with the         *)
(* polynomials of the vector are reduced one by one and their sum is reduced *)
(* (common/mldsa_native_polyvec_lazy.ml), instead of being accumulated in 64 *)
(* bits and reduced once. The integers differ, but they are congruent modulo *)
(* q and within q of 0, and the code always transforms them back with the    *)
(* inverse NTT and then makes them nonnegative (mld_poly_caddq), so that the *)
(* results are the same as those of the default configuration                *)
(* (common/mldsa_native_sign.ml):                                            *)
(*                                                                           *)
(*  - MLD_KEYPAIR_T_LAZY_XX: t1 and t0 of key generation, packed, from the   *)
(*    seed, if the samplings terminate;                                      *)
(*  - MLD_PK_FROM_SK_T_LAZY_XX: the same from a secret key (any s1 and s2    *)
(*    that unpack), as mld_sign_pk_from_sk recomputes them;                  *)
(*  - MLD_VERIFY_W1_LAZY_XX: each row of w1' in verification, once the norm  *)
(*    of z is checked;                                                       *)
(*  - MLD_SIGN_W_LAZY_XX: w = invNTT(A * NTT(y)) of a signing attempt, made  *)
(*    nonnegative, for y sampled from any rho'' and kappa.                   *)
(*                                                                           *)
(* The machine-code proofs of key generation, pk_from_sk, verification and   *)
(* signing use these statements, so that their theorems are those of the     *)
(* default configuration; lazy_proof.ml proves them, using the congruences   *)
(* of utils/mldsa_native_fips204_ntt.ml, and link.ml discharges them.        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "common/mldsa_native_polyvec_lazy.ml";;

(* ------------------------------------------------------------------------- *)
(* ML-DSA-44                                                                *)
(* ------------------------------------------------------------------------- *)

let MLD_KEYPAIR_T_LAZY_44_STMT =
 `!SEED. SEED < 2 EXP 256 /\ mld_keypair_terminates_44 SEED /\
         mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED)
         ==> (!j. j < 1280
                  ==> mld_polyvec_pack 320 mld_polyt1_pack
                       (mld_polyvec_map mld_poly_power2round_hi
                         (mld_compute_t_lazy 4 mld_polyeta_unpack_2 96
                           (mld_keypair_rho 4 4 SEED)
                           (mld_polyvec_map mld_poly_ntt
                             (mld_keypair_s 2 4 4 SEED))
                           (\j. mld_polyvec_pack 96 mld_polyeta_pack_2
                                 (mld_keypair_s 2 4 4 SEED)
                                 (4 * 96 + j)))) j =
                      mld_polyvec_pack 320 mld_polyt1_pack
                       (mld_polyvec_map mld_poly_power2round_hi
                         (mld_keypair_t 2 4 4 mld_polyeta_pack_2
                            mld_polyeta_unpack_2 96 SEED)) j) /\
             (!j. j < 1664
                  ==> mld_polyvec_pack 416 mld_polyt0_pack
                       (mld_polyvec_map mld_poly_power2round_lo
                         (mld_compute_t_lazy 4 mld_polyeta_unpack_2 96
                           (mld_keypair_rho 4 4 SEED)
                           (mld_polyvec_map mld_poly_ntt
                             (mld_keypair_s 2 4 4 SEED))
                           (\j. mld_polyvec_pack 96 mld_polyeta_pack_2
                                 (mld_keypair_s 2 4 4 SEED)
                                 (4 * 96 + j)))) j =
                      mld_polyvec_pack 416 mld_polyt0_pack
                       (mld_polyvec_map mld_poly_power2round_lo
                         (mld_keypair_t 2 4 4 mld_polyeta_pack_2
                            mld_polyeta_unpack_2 96 SEED)) j)`;;

let MLD_KEYPAIR_T_LAZY_44 = assume_spec MLD_KEYPAIR_T_LAZY_44_STMT;;

let MLD_PK_FROM_SK_T_LAZY_44_STMT =
 `!sk. mld_matrix_terminates 4 4 (mld_sk_rho sk)
       ==> (!j. j < 1280
                ==> mld_polyvec_pack 320 mld_polyt1_pack
                     (mld_polyvec_map mld_poly_power2round_hi
                       (mld_compute_t_lazy 4 mld_polyeta_unpack_2 96
                         (mld_sk_rho sk)
                         (mld_polyvec_map mld_poly_ntt
                           (mld_sk_s1 mld_polyeta_unpack_2 96 sk))
                         (\j. sk(128 + 4 * 96 + j)))) j =
                    mld_polyvec_pack 320 mld_polyt1_pack
                     (mld_polyvec_map mld_poly_power2round_hi
                       (mld_pk_from_sk_t 4 mld_polyeta_unpack_2 96 sk)) j) /\
           (!j. j < 1664
                ==> mld_polyvec_pack 416 mld_polyt0_pack
                     (mld_polyvec_map mld_poly_power2round_lo
                       (mld_compute_t_lazy 4 mld_polyeta_unpack_2 96
                         (mld_sk_rho sk)
                         (mld_polyvec_map mld_poly_ntt
                           (mld_sk_s1 mld_polyeta_unpack_2 96 sk))
                         (\j. sk(128 + 4 * 96 + j)))) j =
                    mld_polyvec_pack 416 mld_polyt0_pack
                     (mld_polyvec_map mld_poly_power2round_lo
                       (mld_pk_from_sk_t 4 mld_polyeta_unpack_2 96 sk)) j)`;;

let MLD_PK_FROM_SK_T_LAZY_44 = assume_spec MLD_PK_FROM_SK_T_LAZY_44_STMT;;

let MLD_VERIFY_W1_LAZY_44_STMT =
 `!rho z cc pk omega hb i c.
     mld_matrix_terminates 4 4 rho /\
     cc < 2 EXP (8 * 32) /\ mld_poly_challenge_terminates 39 32 cc /\
     mld_polyvec_chknorm 4 z (word 130994) = word 0 /\
     i < 4 /\ c < 256
     ==> mld_verify_w1_lazy 4 mld_poly_use_hint_88 rho
          (mld_polyvec_map mld_poly_ntt z)
          (mld_poly_ntt (mld_poly_challenge 39 32 cc)) pk omega hb i
          c =
         mld_verify_w1 4 mld_poly_use_hint_88 rho
          (mld_polyvec_map mld_poly_ntt z)
          (mld_poly_ntt (mld_poly_challenge 39 32 cc)) pk omega hb i
          c`;;

let MLD_VERIFY_W1_LAZY_44 = assume_spec MLD_VERIFY_W1_LAZY_44_STMT;;

let MLD_SIGN_W_LAZY_44_STMT =
 `!rho rhoprime kappa i.
     mld_matrix_terminates 4 4 rho /\ i < 1024
     ==> mld_polyvec_map mld_poly_caddq
          (mld_yvec_lazy_w 4 mld_poly_uniform_gamma1_17 rho rhoprime kappa) i =
         mld_sign_w 4 (mld_polyvec_matrix_expand 4 rho)
          (mld_sign_y mld_poly_uniform_gamma1_17 rhoprime kappa) i`;;

let MLD_SIGN_W_LAZY_44 = assume_spec MLD_SIGN_W_LAZY_44_STMT;;

(* ------------------------------------------------------------------------- *)
(* ML-DSA-65                                                                *)
(* ------------------------------------------------------------------------- *)

let MLD_KEYPAIR_T_LAZY_65_STMT =
 `!SEED. SEED < 2 EXP 256 /\ mld_keypair_terminates_65 SEED /\
         mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED)
         ==> (!j. j < 1920
                  ==> mld_polyvec_pack 320 mld_polyt1_pack
                       (mld_polyvec_map mld_poly_power2round_hi
                         (mld_compute_t_lazy 5 mld_polyeta_unpack_4 128
                           (mld_keypair_rho 6 5 SEED)
                           (mld_polyvec_map mld_poly_ntt
                             (mld_keypair_s 4 6 5 SEED))
                           (\j. mld_polyvec_pack 128 mld_polyeta_pack_4
                                 (mld_keypair_s 4 6 5 SEED)
                                 (5 * 128 + j)))) j =
                      mld_polyvec_pack 320 mld_polyt1_pack
                       (mld_polyvec_map mld_poly_power2round_hi
                         (mld_keypair_t 4 6 5 mld_polyeta_pack_4
                            mld_polyeta_unpack_4 128 SEED)) j) /\
             (!j. j < 2496
                  ==> mld_polyvec_pack 416 mld_polyt0_pack
                       (mld_polyvec_map mld_poly_power2round_lo
                         (mld_compute_t_lazy 5 mld_polyeta_unpack_4 128
                           (mld_keypair_rho 6 5 SEED)
                           (mld_polyvec_map mld_poly_ntt
                             (mld_keypair_s 4 6 5 SEED))
                           (\j. mld_polyvec_pack 128 mld_polyeta_pack_4
                                 (mld_keypair_s 4 6 5 SEED)
                                 (5 * 128 + j)))) j =
                      mld_polyvec_pack 416 mld_polyt0_pack
                       (mld_polyvec_map mld_poly_power2round_lo
                         (mld_keypair_t 4 6 5 mld_polyeta_pack_4
                            mld_polyeta_unpack_4 128 SEED)) j)`;;

let MLD_KEYPAIR_T_LAZY_65 = assume_spec MLD_KEYPAIR_T_LAZY_65_STMT;;

let MLD_PK_FROM_SK_T_LAZY_65_STMT =
 `!sk. mld_matrix_terminates 6 5 (mld_sk_rho sk)
       ==> (!j. j < 1920
                ==> mld_polyvec_pack 320 mld_polyt1_pack
                     (mld_polyvec_map mld_poly_power2round_hi
                       (mld_compute_t_lazy 5 mld_polyeta_unpack_4 128
                         (mld_sk_rho sk)
                         (mld_polyvec_map mld_poly_ntt
                           (mld_sk_s1 mld_polyeta_unpack_4 128 sk))
                         (\j. sk(128 + 5 * 128 + j)))) j =
                    mld_polyvec_pack 320 mld_polyt1_pack
                     (mld_polyvec_map mld_poly_power2round_hi
                       (mld_pk_from_sk_t 5 mld_polyeta_unpack_4 128 sk)) j) /\
           (!j. j < 2496
                ==> mld_polyvec_pack 416 mld_polyt0_pack
                     (mld_polyvec_map mld_poly_power2round_lo
                       (mld_compute_t_lazy 5 mld_polyeta_unpack_4 128
                         (mld_sk_rho sk)
                         (mld_polyvec_map mld_poly_ntt
                           (mld_sk_s1 mld_polyeta_unpack_4 128 sk))
                         (\j. sk(128 + 5 * 128 + j)))) j =
                    mld_polyvec_pack 416 mld_polyt0_pack
                     (mld_polyvec_map mld_poly_power2round_lo
                       (mld_pk_from_sk_t 5 mld_polyeta_unpack_4 128 sk)) j)`;;

let MLD_PK_FROM_SK_T_LAZY_65 = assume_spec MLD_PK_FROM_SK_T_LAZY_65_STMT;;

let MLD_VERIFY_W1_LAZY_65_STMT =
 `!rho z cc pk omega hb i c.
     mld_matrix_terminates 6 5 rho /\
     cc < 2 EXP (8 * 48) /\ mld_poly_challenge_terminates 49 48 cc /\
     mld_polyvec_chknorm 5 z (word 524092) = word 0 /\
     i < 6 /\ c < 256
     ==> mld_verify_w1_lazy 5 mld_poly_use_hint_32 rho
          (mld_polyvec_map mld_poly_ntt z)
          (mld_poly_ntt (mld_poly_challenge 49 48 cc)) pk omega hb i
          c =
         mld_verify_w1 5 mld_poly_use_hint_32 rho
          (mld_polyvec_map mld_poly_ntt z)
          (mld_poly_ntt (mld_poly_challenge 49 48 cc)) pk omega hb i
          c`;;

let MLD_VERIFY_W1_LAZY_65 = assume_spec MLD_VERIFY_W1_LAZY_65_STMT;;

let MLD_SIGN_W_LAZY_65_STMT =
 `!rho rhoprime kappa i.
     mld_matrix_terminates 6 5 rho /\ i < 1536
     ==> mld_polyvec_map mld_poly_caddq
          (mld_yvec_lazy_w 5 mld_poly_uniform_gamma1_19 rho rhoprime kappa) i =
         mld_sign_w 5 (mld_polyvec_matrix_expand 5 rho)
          (mld_sign_y mld_poly_uniform_gamma1_19 rhoprime kappa) i`;;

let MLD_SIGN_W_LAZY_65 = assume_spec MLD_SIGN_W_LAZY_65_STMT;;

(* ------------------------------------------------------------------------- *)
(* ML-DSA-87                                                                *)
(* ------------------------------------------------------------------------- *)

let MLD_KEYPAIR_T_LAZY_87_STMT =
 `!SEED. SEED < 2 EXP 256 /\ mld_keypair_terminates_87 SEED /\
         mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED)
         ==> (!j. j < 2560
                  ==> mld_polyvec_pack 320 mld_polyt1_pack
                       (mld_polyvec_map mld_poly_power2round_hi
                         (mld_compute_t_lazy 7 mld_polyeta_unpack_2 96
                           (mld_keypair_rho 8 7 SEED)
                           (mld_polyvec_map mld_poly_ntt
                             (mld_keypair_s 2 8 7 SEED))
                           (\j. mld_polyvec_pack 96 mld_polyeta_pack_2
                                 (mld_keypair_s 2 8 7 SEED)
                                 (7 * 96 + j)))) j =
                      mld_polyvec_pack 320 mld_polyt1_pack
                       (mld_polyvec_map mld_poly_power2round_hi
                         (mld_keypair_t 2 8 7 mld_polyeta_pack_2
                            mld_polyeta_unpack_2 96 SEED)) j) /\
             (!j. j < 3328
                  ==> mld_polyvec_pack 416 mld_polyt0_pack
                       (mld_polyvec_map mld_poly_power2round_lo
                         (mld_compute_t_lazy 7 mld_polyeta_unpack_2 96
                           (mld_keypair_rho 8 7 SEED)
                           (mld_polyvec_map mld_poly_ntt
                             (mld_keypair_s 2 8 7 SEED))
                           (\j. mld_polyvec_pack 96 mld_polyeta_pack_2
                                 (mld_keypair_s 2 8 7 SEED)
                                 (7 * 96 + j)))) j =
                      mld_polyvec_pack 416 mld_polyt0_pack
                       (mld_polyvec_map mld_poly_power2round_lo
                         (mld_keypair_t 2 8 7 mld_polyeta_pack_2
                            mld_polyeta_unpack_2 96 SEED)) j)`;;

let MLD_KEYPAIR_T_LAZY_87 = assume_spec MLD_KEYPAIR_T_LAZY_87_STMT;;

let MLD_PK_FROM_SK_T_LAZY_87_STMT =
 `!sk. mld_matrix_terminates 8 7 (mld_sk_rho sk)
       ==> (!j. j < 2560
                ==> mld_polyvec_pack 320 mld_polyt1_pack
                     (mld_polyvec_map mld_poly_power2round_hi
                       (mld_compute_t_lazy 7 mld_polyeta_unpack_2 96
                         (mld_sk_rho sk)
                         (mld_polyvec_map mld_poly_ntt
                           (mld_sk_s1 mld_polyeta_unpack_2 96 sk))
                         (\j. sk(128 + 7 * 96 + j)))) j =
                    mld_polyvec_pack 320 mld_polyt1_pack
                     (mld_polyvec_map mld_poly_power2round_hi
                       (mld_pk_from_sk_t 7 mld_polyeta_unpack_2 96 sk)) j) /\
           (!j. j < 3328
                ==> mld_polyvec_pack 416 mld_polyt0_pack
                     (mld_polyvec_map mld_poly_power2round_lo
                       (mld_compute_t_lazy 7 mld_polyeta_unpack_2 96
                         (mld_sk_rho sk)
                         (mld_polyvec_map mld_poly_ntt
                           (mld_sk_s1 mld_polyeta_unpack_2 96 sk))
                         (\j. sk(128 + 7 * 96 + j)))) j =
                    mld_polyvec_pack 416 mld_polyt0_pack
                     (mld_polyvec_map mld_poly_power2round_lo
                       (mld_pk_from_sk_t 7 mld_polyeta_unpack_2 96 sk)) j)`;;

let MLD_PK_FROM_SK_T_LAZY_87 = assume_spec MLD_PK_FROM_SK_T_LAZY_87_STMT;;

let MLD_VERIFY_W1_LAZY_87_STMT =
 `!rho z cc pk omega hb i c.
     mld_matrix_terminates 8 7 rho /\
     cc < 2 EXP (8 * 64) /\ mld_poly_challenge_terminates 60 64 cc /\
     mld_polyvec_chknorm 7 z (word 524168) = word 0 /\
     i < 8 /\ c < 256
     ==> mld_verify_w1_lazy 7 mld_poly_use_hint_32 rho
          (mld_polyvec_map mld_poly_ntt z)
          (mld_poly_ntt (mld_poly_challenge 60 64 cc)) pk omega hb i
          c =
         mld_verify_w1 7 mld_poly_use_hint_32 rho
          (mld_polyvec_map mld_poly_ntt z)
          (mld_poly_ntt (mld_poly_challenge 60 64 cc)) pk omega hb i
          c`;;

let MLD_VERIFY_W1_LAZY_87 = assume_spec MLD_VERIFY_W1_LAZY_87_STMT;;

let MLD_SIGN_W_LAZY_87_STMT =
 `!rho rhoprime kappa i.
     mld_matrix_terminates 8 7 rho /\ i < 2048
     ==> mld_polyvec_map mld_poly_caddq
          (mld_yvec_lazy_w 7 mld_poly_uniform_gamma1_19 rho rhoprime kappa) i =
         mld_sign_w 7 (mld_polyvec_matrix_expand 7 rho)
          (mld_sign_y mld_poly_uniform_gamma1_19 rhoprime kappa) i`;;

let MLD_SIGN_W_LAZY_87 = assume_spec MLD_SIGN_W_LAZY_87_STMT;;
