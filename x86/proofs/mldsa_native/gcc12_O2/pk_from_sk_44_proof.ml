(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the proof (see pk_from_sk_44_spec.ml).    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/pk_from_sk_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_top.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, by PFS_FULL_TAC of *)
(* utils/mldsa_native_top.ml, given the parameter set (k = 4, l = 4, eta =   *)
(* 2, 96 bytes for a packed polynomial of s1 and s2), the sizes of the keys, *)
(* the stack (30836 bytes, with the SUB of 7040 for the aligned frame of the *)
(* function) and the theorems for the callees.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let cpt = MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
  and unp = MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
  and chkl = MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
  and chkk =
   MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
  and ntt = MLDSA_NATIVE_POLYVECL_NTT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
  and shake = MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL in
  PFS_FULL_TAC
   { pfs_exec = MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_EXEC;
     pfs_fn = "mldsa44_pk_from_sk";
     pfs_k = 4; pfs_l = 4; pfs_eta = 2; pfs_p = 96;
     pfs_unpack = `mld_polyeta_unpack_2`;
     pfs_sk = 2560; pfs_pk = 1312; pfs_fr = 30836; pfs_sub = 7040;
     pfs_cpt = cpt; pfs_unpack_th = unp; pfs_chkl = chkl;
     pfs_chkk = chkk; pfs_ntt = ntt; pfs_shake = shake });;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
