(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas of lazy_eq_spec.ml: the proofs.                                *)
(* common/fips204/properties/mldsa_native_lazy.ml proves each statement,     *)
(* after lazy_eq_spec.ml has stated it, so that prove records the theorem    *)
(* for it (see ../../mlkem_native/relative.ml).                              *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "common/fips204/properties/mldsa_native_lazy.ml";;

(* Each statement now has its theorem, without assumptions.                  *)

let () =
  List.iter (fun (name,stmt,th) ->
    if hyp th <> [] || not (aconv (concl th) stmt) then
      failwith ("lazy_eq_proof.ml: not proved: "^name))
   ["MLD_LAZY_ETA_UNPACK_BOUND",MLD_LAZY_ETA_UNPACK_BOUND_STMT,
    MLD_LAZY_ETA_UNPACK_BOUND;
    "MLD_LAZY_Z_UNPACK_BOUND",MLD_LAZY_Z_UNPACK_BOUND_STMT,
    MLD_LAZY_Z_UNPACK_BOUND;
    "MLD_LAZY_SIGN_Y_BOUND",MLD_LAZY_SIGN_Y_BOUND_STMT,
    MLD_LAZY_SIGN_Y_BOUND;
    "MLD_LAZY_POLYVEC_NTT_BOUND",MLD_LAZY_POLYVEC_NTT_BOUND_STMT,
    MLD_LAZY_POLYVEC_NTT_BOUND;
    "MLD_LAZY_POINTWISE_BOUND",MLD_LAZY_POINTWISE_BOUND_STMT,
    MLD_LAZY_POINTWISE_BOUND;
    "MLD_LAZY_KEYPAIR_S_BOUND",MLD_LAZY_KEYPAIR_S_BOUND_STMT,
    MLD_LAZY_KEYPAIR_S_BOUND;
    "MLD_LAZY_COMPUTE_T_PACK",MLD_LAZY_COMPUTE_T_PACK_STMT,
    MLD_LAZY_COMPUTE_T_PACK;
    "MLD_LAZY_SIGN_W",MLD_LAZY_SIGN_W_STMT,MLD_LAZY_SIGN_W;
    "MLD_LAZY_VERIFY",MLD_LAZY_VERIFY_STMT,MLD_LAZY_VERIFY];;
