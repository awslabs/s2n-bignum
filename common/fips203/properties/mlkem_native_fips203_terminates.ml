(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The hypothesis mlkem_samplentt_terminates of the theorems for the K-PKE   *)
(* and ML-KEM functions of mlkem-native holds for all their seeds.           *)
(*                                                                           *)
(* The CORRECT and SAFE theorems of these functions assume, for each entry   *)
(* (i,j) of the matrix, mlkem_samplentt_terminates (APPEND rho [word j;      *)
(* word i]), with rho of 32 bytes: a slice of the encapsulation or           *)
(* decapsulation key, or FST(mlkem_g ...) in the key generation.             *)
(* MLKEM_SAMPLE_NTT_TERMINATES of common/fips203/properties/terminates.ml    *)
(* proves it for every seed of fewer than 168 bytes, and so for these of 34  *)
(* bytes. MLKEM_FIPS203_DISCHARGE removes the hypothesis from such a         *)
(* theorem; the fips203.ml files of the builds use it for the API functions. *)
(* The contracts of the functions themselves (the _spec.ml files) are not    *)
(* changed.                                                                  *)
(* ========================================================================= *)

(* This file does not depend on the instruction set, but needs the           *)
(* definitions of arm/proofs/utils/mlkem_native_fips203.ml or its x86        *)
(* counterpart, which load common/fips203/properties/mlkem_native_fips203.ml *)
(* after the base of their instruction set: load one of them first.          *)

needs "common/fips203/properties/mlkem_native_fips203.ml";;
needs "common/fips203/properties/terminates.ml";;

let MLKEM_SAMPLENTT_TERMINATES = prove
 (`!b. LENGTH b < 168 ==> mlkem_samplentt_terminates b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_samplentt_terminates] THEN
  MATCH_MP_TAC MLKEM_SAMPLE_NTT_TERMINATES THEN ASM_REWRITE_TAC[]);;

let MLKEM_SAMPLENTT_TERMINATES_SLICE = prove
 (`!a (x:byte list) i j.
        mlkem_samplentt_terminates
         (APPEND (mlkem_slice a 32 x) [word j; word i])`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLKEM_SAMPLENTT_TERMINATES THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_MLKEM_SLICE; LENGTH] THEN ARITH_TAC);;

let MLKEM_SAMPLENTT_TERMINATES_G = prove
 (`!c i j.
        mlkem_samplentt_terminates (APPEND (FST(mlkem_g c)) [word j; word i])`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLKEM_SAMPLENTT_TERMINATES THEN
  REWRITE_TAC[mlkem_g; LENGTH_APPEND; LENGTH_MLKEM_SLICE; LENGTH] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* MLKEM_FIPS203_DISCHARGE th rewrites each instance of the hypothesis in th *)
(* to T and then removes it: (!i j. i < k /\ j < k ==> T), and the form      *)
(* (!d. LENGTH d = 32 ==> !i j. ...) of mlkem<n>_keypair, become T, and so   *)
(* does a conjunct T. The rules touch nothing else. The rule fails if the    *)
(* conclusion of th does not mention mlkem_samplentt_terminates, or still    *)
(* does afterwards.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_FIPS203_DISCHARGE =
  let rules =
    [MLKEM_SAMPLENTT_TERMINATES_SLICE; MLKEM_SAMPLENTT_TERMINATES_G;
     TAUT `(p ==> T) <=> T`; TAUT `(T /\ p) <=> p`; TAUT `(p /\ T) <=> p`;
     ISPEC `T` FORALL_SIMP] in
  let has_hyp th =
    can (find_term (fun t -> match t with
                               Const("mlkem_samplentt_terminates",_) -> true
                             | _ -> false)) (concl th) in
  fun th ->
    if not (has_hyp th) then
      failwith "MLKEM_FIPS203_DISCHARGE: no mlkem_samplentt_terminates" else
    let th' = PURE_REWRITE_RULE rules th in
    if has_hyp th' then
      failwith "MLKEM_FIPS203_DISCHARGE: mlkem_samplentt_terminates is left"
    else th';;
