(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the proof (see pk_from_sk_65_spec.ml).    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/pk_from_sk_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/lazy_eq_spec.ml";;
needs "arm/proofs/utils/mldsa_native_top.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, by PFS_FULL_TAC of *)
(* utils/mldsa_native_top.ml, given the parameter set (k = 6, l = 5, eta =   *)
(* 4, 128 bytes for a packed polynomial of s1 and s2), the sizes of the      *)
(* keys, the stack (13744 bytes, 8976 of them for the function), the         *)
(* theorems for the callees, and the value of x28 in the loop over the 156   *)
(* chunks of t0 (the copy of rho on the stack).                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  let chkk =
   MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL in
  PFS_FULL_TAC
   { pfs_exec = MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_REDUCED_RAM_EXEC;
     pfs_fn = "mldsa65_pk_from_sk";
     pfs_k = 6; pfs_l = 5; pfs_eta = 4; pfs_p = 128;
     pfs_unpack = `mld_polyeta_unpack_4`;
     pfs_sk = 4032; pfs_pk = 1952; pfs_fr = 13744; pfs_own = 8976;
     pfs_cpt =
       MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;
     pfs_unpack_th =
       MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;
     pfs_chkl =
       MLDSA_NATIVE_POLYVECL_CHKNORM_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;
     pfs_chkk = chkk;
     pfs_ntt = MLDSA_NATIVE_POLYVECL_NTT_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;
     pfs_shake = MLDSA_NATIVE_SHAKE256_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;
     pfs_x28 = `word_add stackpointer (word RHO):int64`;
     pfs_cpt_pre =
       SUBGOAL_THEN
        `!j. j < 1280
             ==> abs(ival(mld_polyvec_map mld_poly_ntt
                           (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                             (\j. (skb:num->byte)(128 + j))) j)) <
                 &94279689`
        ASSUME_TAC THENL
        [MP_TAC(SPECL [`5`; `mld_polyvec_unpack 128 mld_polyeta_unpack_4
                                (\j. (skb:num->byte)(128 + j))`]
                      MLD_LAZY_POLYVEC_NTT_BOUND) THEN
         CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
         DISCH_THEN MATCH_MP_TAC THEN
         REWRITE_TAC[mld_polyvec_unpack; mld_polyvec; MLD_LAZY_ETA_UNPACK_BOUND];
         ALL_TAC] });;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;
