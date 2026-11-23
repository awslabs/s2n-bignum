(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the proof (see pk_from_sk_87_spec.ml).    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pk_from_sk_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/lazy_eq_spec.ml";;
needs "x86/proofs/utils/mldsa_native_top_rr.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, by PFS_RR_FULL_TAC *)
(* of utils/mldsa_native_top_rr.ml, given the parameter set (k = 8, l = 7,   *)
(* eta = 2, 96 bytes for a packed polynomial of s1 and s2), the sizes of the *)
(* keys, the stack (16756 bytes, with the SUB of 11776 for the aligned frame *)
(* of the function, below which mld_compute_pack_t0_t187 uses 4901 bytes     *)
(* with its return address), the theorems for the callees and the tactic     *)
(* that proves, before the call of mld_compute_pack_t0_t187, that the NTT of *)
(* s1 is within the bound that its theorem needs (MLD_LAZY_POLYVEC_NTT_BOUND *)
(* and MLD_LAZY_ETA_UNPACK_BOUND of lazy_eq_spec.ml).                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  let cpt =
    MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
  and unp =
    MLDSA_NATIVE_POLYVECL_UNPACK_ETA_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
  and chkl =
    MLDSA_NATIVE_POLYVECL_CHKNORM_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
  and chkk =
   MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
  and ntt =
    MLDSA_NATIVE_POLYVECL_NTT_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
  and shake =
    MLDSA_NATIVE_SHAKE256_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL in
  PFS_RR_FULL_TAC
   { pfs_exec = MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_REDUCED_RAM_EXEC;
     pfs_fn = "mldsa87_pk_from_sk";
     pfs_k = 8; pfs_l = 7; pfs_eta = 2; pfs_p = 96;
     pfs_unpack = `mld_polyeta_unpack_2`;
     pfs_sk = 4896; pfs_pk = 2592; pfs_fr = 16756; pfs_sub = 11776;
     pfs_cpt = cpt; pfs_unpack_th = unp; pfs_chkl = chkl;
     pfs_chkk = chkk; pfs_ntt = ntt; pfs_shake = shake }
   (SUBGOAL_THEN
     `!j. j < 1792
          ==> abs(ival(mld_polyvec_map mld_poly_ntt
                        (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                          (\j. (skb:num->byte)(128 + j))) j)) <
              &94279689`
     ASSUME_TAC THENL
     [MP_TAC(SPECL [`7`; `mld_polyvec_unpack 96 mld_polyeta_unpack_2
                             (\j. (skb:num->byte)(128 + j))`]
                   MLD_LAZY_POLYVEC_NTT_BOUND) THEN
      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[mld_polyvec_unpack; mld_polyvec; MLD_LAZY_ETA_UNPACK_BOUND];
      ALL_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
