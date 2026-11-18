(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas that relate the matrix-vector products of the reduced-RAM code *)
(* (common/mldsa_native_lazy.ml) to those of common/mldsa_native_polyvec.ml  *)
(* and common/mldsa_native_sign.ml, and the bounds that their hypotheses     *)
(* need: the statements. lazy_eq_proof.ml proves them. They are stated with  *)
(* assume_spec, as the contracts of the callees are (see                     *)
(* ../../mlkem_native/relative.ml), so that the proofs of the code that uses *)
(* them do not load the arithmetic of                                        *)
(* common/fips204/properties/mldsa_native_ntt_cong.ml, and link.ml           *)
(* discharges them.                                                          *)
(*                                                                           *)
(* With MLD_CONFIG_REDUCE_RAM, each product of an entry of A with a          *)
(* polynomial is reduced before the products are added, and the sum is then  *)
(* reduced; without it, the products are added in 64 bits and the sum        *)
(* reduced once. The results are congruent mod q and below q in absolute     *)
(* value, and so are those of the inverse NTT of either, which mld_caddq     *)
(* maps to the same representative in [0,q). Hence t of key generation,     *)
(* w = A y of signing and w1 of verification are those of the specification *)
(* of the code without MLD_CONFIG_REDUCE_RAM, for inputs within the bounds   *)
(* of the C contracts, which the unpacking, the samplers and the NTT ensure. *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mldsa_native_lazy.ml";;
needs "common/mldsa_native_sign.ml";;

(* ------------------------------------------------------------------------- *)
(* Bounds: the unpacked coefficients of s1, s2 (eta) and z (gamma1) and the  *)
(* coefficients of y are below q in absolute value, the NTT of a polynomial  *)
(* below q is below MLD_NTT_BOUND = 94279689, a Montgomery product is at     *)
(* most 2^30 + 2^22 in absolute value whatever its inputs, and the sampled   *)
(* coefficients of s1 in key generation are below q.                         *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_ETA_UNPACK_BOUND_STMT =
 `(!b i. abs(ival(mld_polyeta_unpack_2 b i)) < &8380417) /\
  (!b i. abs(ival(mld_polyeta_unpack_4 b i)) < &8380417)`;;

let MLD_LAZY_ETA_UNPACK_BOUND = assume_spec MLD_LAZY_ETA_UNPACK_BOUND_STMT;;

let MLD_LAZY_Z_UNPACK_BOUND_STMT =
 `(!b i. abs(ival(mld_polyz_unpack_17 b i)) < &8380417) /\
  (!b i. abs(ival(mld_polyz_unpack_19 b i)) < &8380417)`;;

let MLD_LAZY_Z_UNPACK_BOUND = assume_spec MLD_LAZY_Z_UNPACK_BOUND_STMT;;

let MLD_LAZY_SIGN_Y_BOUND_STMT =
 `(!rp kappa j.
     abs(ival(mld_sign_y mld_poly_uniform_gamma1_17 rp kappa j))
     < &8380417) /\
  (!rp kappa j.
     abs(ival(mld_sign_y mld_poly_uniform_gamma1_19 rp kappa j))
     < &8380417)`;;

let MLD_LAZY_SIGN_Y_BOUND = assume_spec MLD_LAZY_SIGN_Y_BOUND_STMT;;

let MLD_LAZY_POLYVEC_NTT_BOUND_STMT =
 `!n (x:num->int32).
        (!j. j < 256 * n ==> abs(ival(x j)) < &8380417)
        ==> !j. j < 256 * n
                ==> abs(ival(mld_polyvec_map mld_poly_ntt x j)) < &94279689`;;

let MLD_LAZY_POLYVEC_NTT_BOUND = assume_spec MLD_LAZY_POLYVEC_NTT_BOUND_STMT;;

let MLD_LAZY_POINTWISE_BOUND_STMT =
 `!(a:num->int32) b m.
        abs(ival(mld_poly_pointwise_montgomery a b m)) <= &1077936128`;;

let MLD_LAZY_POINTWISE_BOUND = assume_spec MLD_LAZY_POINTWISE_BOUND_STMT;;

let MLD_LAZY_KEYPAIR_S_BOUND_STMT =
 `!eta k l (used:num->bool) seed.
        mld_keypair_terminates eta k l used seed /\ l < 256 /\
        (!n. n < l ==> used n)
        ==> !j. j < 256 * l
                ==> abs(ival(mld_keypair_s eta k l seed j)) < &8380417`;;

let MLD_LAZY_KEYPAIR_S_BOUND = assume_spec MLD_LAZY_KEYPAIR_S_BOUND_STMT;;

(* ------------------------------------------------------------------------- *)
(* Key generation: t1 and t0 packed, from t as mld_compute_pack_t0_t1        *)
(* computes it (mld_compute_t_lazy), for s1hat within the NTT bound and the  *)
(* unpacking of s2 below q.                                                  *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_COMPUTE_T_PACK_STMT =
 `!k l (unpack:(num->byte)->num->int32) p r sh s2b.
        (l = 4 \/ l = 5 \/ l = 7) /\ mld_matrix_terminates k l r /\
        (!j. j < 256 * l ==> abs(ival(sh j)) < &94279689) /\
        (!b m. abs(ival(unpack b m)) < &8380417)
        ==> (!j. j < 320 * k
                 ==> mld_polyvec_pack 320 mld_polyt1_pack
                      (mld_polyvec_map mld_poly_power2round_hi
                        (mld_compute_t_lazy l unpack p r sh s2b)) j =
                     mld_polyvec_pack 320 mld_polyt1_pack
                      (mld_polyvec_map mld_poly_power2round_hi
                        (mld_compute_t l unpack p r sh s2b)) j) /\
            (!j. j < 416 * k
                 ==> mld_polyvec_pack 416 mld_polyt0_pack
                      (mld_polyvec_map mld_poly_power2round_lo
                        (mld_compute_t_lazy l unpack p r sh s2b)) j =
                     mld_polyvec_pack 416 mld_polyt0_pack
                      (mld_polyvec_map mld_poly_power2round_lo
                        (mld_compute_t l unpack p r sh s2b)) j)`;;

let MLD_LAZY_COMPUTE_T_PACK = assume_spec MLD_LAZY_COMPUTE_T_PACK_STMT;;

(* ------------------------------------------------------------------------- *)
(* Signing: w = A y made nonnegative, as mld_sign_w.                         *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_SIGN_W_STMT =
 `!k l rho (y:num->int32) j.
        (l = 4 \/ l = 5 \/ l = 7) /\ mld_matrix_terminates k l rho /\
        j < 256 * k /\
        (!m. m < 256 * l ==> abs(ival(y m)) < &8380417)
        ==> mld_polyvec_map mld_poly_caddq
             (mld_polyvec_matrix_yvec_lazy l rho y) j =
            mld_sign_w l (mld_polyvec_matrix_expand l rho) y j`;;

let MLD_LAZY_SIGN_W = assume_spec MLD_LAZY_SIGN_W_STMT;;

(* ------------------------------------------------------------------------- *)
(* Verification: row i of A z - T, reduced, transformed back and made        *)
(* nonnegative, for the T of the code (c t1 2^d in the NTT domain).          *)
(* ------------------------------------------------------------------------- *)

let MLD_LAZY_VERIFY_STMT =
 `!k l rho (zhat:num->int32) (u:num->int32) i n.
        (l = 4 \/ l = 5 \/ l = 7) /\ mld_matrix_terminates k l rho /\
        i < k /\ n < 256 /\
        (!j. j < 256 * l ==> abs(ival(zhat j)) < &94279689) /\
        (!m. m < 256 ==> abs(ival(u m)) <= &1077936128)
        ==> mld_poly_caddq
             (mld_poly_invntt_tomont
               (mld_poly_reduce
                 (mld_poly_sub (mld_polyvec_matrix_row_lazy l rho zhat i) u)))
             n =
            mld_poly_caddq
             (mld_poly_invntt_tomont
               (mld_poly_reduce
                 (mld_poly_sub
                   (mld_polyvec_pointwise_acc_montgomery l
                     (\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j))
                     zhat)
                   u)))
             n`;;

let MLD_LAZY_VERIFY = assume_spec MLD_LAZY_VERIFY_STMT;;
