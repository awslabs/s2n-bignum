(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Equivalence of the compiler-generated FIPS 204 specification              *)
(* (common/fips204/generated/fips204_generated.ml) with the handwritten one  *)
(* (common/fips204/fips204.ml,                                               *)
(* common/fips204/properties/fips204_properties.ml), for ML-DSA-44, -65,     *)
(* -87.                                                                      *)
(*                                                                           *)
(* WHAT IS PROVED. EQUIVALENCE_THEOREMS (below) lists 56 theorems, all       *)
(* without hypotheses, of the form                                           *)
(*                                                                           *)
(*   !args. xof_ok /\ <lengths> ==> GENERATED_P args = HANDWRITTEN args      *)
(*                                                                           *)
(* where the right-hand side is a Value, a Native_Bottom (the bottom of      *)
(* FIPS 204) or Nontermination. Families, each for P = MLDSA44, MLDSA65 and  *)
(* MLDSA87:                                                                  *)
(*                                                                           *)
(*   EQ_ML_DSA_KEYGEN_P, EQ_ML_DSA_SIGN_P, EQ_ML_DSA_VERIFY_P: ML-DSA key    *)
(*   generation, signing and verification (FIPS 204 Algorithms 1, 2, 3);     *)
(*   EQ_HASHML_DSA_SIGN_P, EQ_HASHML_DSA_VERIFY_P: HashML-DSA (Algorithms    *)
(*   4, 5);                                                                  *)
(*   EQ_KEYGEN_INTERNAL_P, EQ_SIGN_INTERNAL_P, EQ_SIGN_INTERNAL_MU_P,        *)
(*   EQ_ML_DSA_VERIFY_INTERNAL_P, EQ_VERIFY_INTERNAL_MU_FINAL_P: the         *)
(*   internal algorithms (Algorithms 6, 7, 8) with the message              *)
(*   representative mu as the "_MU" variants ("external mu", Section 6.2);   *)
(*   EQ_MLDSASIGNMUCHECKED_P, EQ_MLDSAVERIFYMUCHECKED_P,                     *)
(*   EQ_MLDSAVERIFYINTERNALCHECKED_P, EQ_MLDSAVERIFYLENGTHCHECK_P,           *)
(*   EQ_MLDSAVERIFYPUBLIC_P, EQ_HASHMLDSASIGNPUBLIC_P,                       *)
(*   EQ_HASHMLDSAVERIFYPUBLIC_P, EQ_PREHASHALLOWED_P: the checked wrappers   *)
(*   of the generated API (length checks, the allowed pre-hash numbers);     *)
(*   EQ_PREHASH, EQ_OIDBYTES (not parameter-dependent): the pre-hash         *)
(*   selector and the OID bytes.                                             *)
(*                                                                           *)
(* ASSUMPTIONS, all visible in the statements:                               *)
(*                                                                           *)
(*  - xof_ok (common.ml): the uninterpreted shake256_bits and shake128_bits  *)
(*    of the generated file are SHAKE256 and SHAKE128 of common/fips202/fips202.ml   *)
(*    on bit strings of the form bits_of_bytes s.                            *)
(*  - Messages are bits_of_bytes m with m a byte string. Keys and signatures *)
(*    have the exact lengths of the parameter set. The random generator      *)
(*    does not fail: the statements of KeyGen, Sign, HashML-DSA.Sign and     *)
(*    HashMLDSASignPublic assume ent 0 = SOME of the random bytes (32        *)
(*    bytes for KeyGen), as the FIPS 203 ones do. Its failure is not         *)
(*    covered.                                                               *)
(*  - The pre-hash functions of HashML-DSA stay uninterpreted (prehash_bits  *)
(*    in the generated file; top_prehash n M here): the theorems hold for    *)
(*    any digest function.                                                   *)
(*  - The handwritten results are lifted to the generated ones (common.ml):  *)
(*    mldsa_sign_result by lift_sign_result and mldsa_verify_result by       *)
(*    lift_verify_result for the functions with a context: a success is      *)
(*    Value (Native_Value x), the BadContext failure is Value Native_Bottom, *)
(*    OutOfAttempts (no attempt of the signing loop is accepted) is          *)
(*    Nontermination, and a rejected signature is Value (Native_Value F).    *)
(*    The internal functions return a bare value, lifted by                  *)
(*    lift_sign_internal_result and lift_verify_bool. The signing statements *)
(*    use the unbounded search (bound NONE) of FIPS 204.                     *)
(*                                                                           *)
(* NOT COVERED: messages that are not whole bytes (except the pre-hash of    *)
(* HashML-DSA); whether the handwritten specification matches the text of    *)
(* FIPS 204; probabilities or bounds for the signing loop; side channels;    *)
(* the relation to the mldsa-native code (see arm/proofs/mldsa_native and   *)
(* x86/proofs/mldsa_native).                                                 *)
(*                                                                           *)
(* AUDIT: all.ml, then check.ml; see README.md.                         *)
(* ========================================================================= *)

needs "common/fips204/generated/core/core.ml";;
needs "common/fips204/generated/core/rounding.ml";;
needs "common/fips204/generated/core/sample.ml";;
needs "common/fips204/generated/core/ball.ml";;
needs "common/fips204/generated/core/encode.ml";;
needs "common/fips204/generated/core/hints.ml";;
needs "common/fips204/generated/core/ntt.ml";;
needs "common/fips204/generated/core/ntt_vec.ml";;
needs "common/fips204/generated/core/callables.ml";;
needs "common/fips204/generated/core/sigcodec.ml";;
needs "common/fips204/generated/core/toplevel.ml";;
needs "common/fips204/generated/core/keygen.ml";;
needs "common/fips204/generated/core/verify.ml";;
needs "common/fips204/generated/core/sign.ml";;

(* ------------------------------------------------------------------------- *)
(* The wrapper theorems of toplevel.ml carry the structure theorems of the   *)
(* internal families and the byte-string to bit-string conversion as         *)
(* hypotheses. Here they are discharged with the theorems that prove them,   *)
(* and the names are rebound to the discharged versions (toplevel.ml binds   *)
(* the same names to the conditional ones).                                  *)
(* ------------------------------------------------------------------------- *)

let EQUIV_PROVED =
  [BALL_BYTES_TO_BITS_STRING; ENC_BYTES_TO_BITS_STRING] @
  [EQ_KEYGEN_INTERNAL_MLDSA44; EQ_KEYGEN_INTERNAL_MLDSA65;
   EQ_KEYGEN_INTERNAL_MLDSA87;
   EQ_SIGN_INTERNAL_MU_MLDSA44; EQ_SIGN_INTERNAL_MU_MLDSA65;
   EQ_SIGN_INTERNAL_MU_MLDSA87;
   EQ_SIGN_INTERNAL_MLDSA44; EQ_SIGN_INTERNAL_MLDSA65;
   EQ_SIGN_INTERNAL_MLDSA87;
   EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA44; EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA65;
   EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA87;
   EQ_VERIFY_INTERNAL_FINAL_MLDSA44; EQ_VERIFY_INTERNAL_FINAL_MLDSA65;
   EQ_VERIFY_INTERNAL_FINAL_MLDSA87];;

let EQUIV_DISCHARGE th =
  itlist (fun h th -> if can (find (aconv (concl h))) (hyp th)
                      then PROVE_HYP h th else th)
   EQUIV_PROVED th;;

let EQ_ML_DSA_KEYGEN_MLDSA44 = EQUIV_DISCHARGE EQ_ML_DSA_KEYGEN_MLDSA44;;
let EQ_ML_DSA_KEYGEN_MLDSA65 = EQUIV_DISCHARGE EQ_ML_DSA_KEYGEN_MLDSA65;;
let EQ_ML_DSA_KEYGEN_MLDSA87 = EQUIV_DISCHARGE EQ_ML_DSA_KEYGEN_MLDSA87;;
let EQ_ML_DSA_SIGN_MLDSA44 = EQUIV_DISCHARGE EQ_ML_DSA_SIGN_MLDSA44;;
let EQ_ML_DSA_SIGN_MLDSA65 = EQUIV_DISCHARGE EQ_ML_DSA_SIGN_MLDSA65;;
let EQ_ML_DSA_SIGN_MLDSA87 = EQUIV_DISCHARGE EQ_ML_DSA_SIGN_MLDSA87;;
let EQ_ML_DSA_VERIFY_MLDSA44 = EQUIV_DISCHARGE EQ_ML_DSA_VERIFY_MLDSA44;;
let EQ_ML_DSA_VERIFY_MLDSA65 = EQUIV_DISCHARGE EQ_ML_DSA_VERIFY_MLDSA65;;
let EQ_ML_DSA_VERIFY_MLDSA87 = EQUIV_DISCHARGE EQ_ML_DSA_VERIFY_MLDSA87;;
let EQ_ML_DSA_VERIFY_INTERNAL_MLDSA44 = EQUIV_DISCHARGE EQ_ML_DSA_VERIFY_INTERNAL_MLDSA44;;
let EQ_ML_DSA_VERIFY_INTERNAL_MLDSA65 = EQUIV_DISCHARGE EQ_ML_DSA_VERIFY_INTERNAL_MLDSA65;;
let EQ_ML_DSA_VERIFY_INTERNAL_MLDSA87 = EQUIV_DISCHARGE EQ_ML_DSA_VERIFY_INTERNAL_MLDSA87;;
let EQ_MLDSASIGNMUCHECKED_MLDSA44 = EQUIV_DISCHARGE EQ_MLDSASIGNMUCHECKED_MLDSA44;;
let EQ_MLDSASIGNMUCHECKED_MLDSA65 = EQUIV_DISCHARGE EQ_MLDSASIGNMUCHECKED_MLDSA65;;
let EQ_MLDSASIGNMUCHECKED_MLDSA87 = EQUIV_DISCHARGE EQ_MLDSASIGNMUCHECKED_MLDSA87;;
let EQ_MLDSAVERIFYMUCHECKED_MLDSA44 = EQUIV_DISCHARGE EQ_MLDSAVERIFYMUCHECKED_MLDSA44;;
let EQ_MLDSAVERIFYMUCHECKED_MLDSA65 = EQUIV_DISCHARGE EQ_MLDSAVERIFYMUCHECKED_MLDSA65;;
let EQ_MLDSAVERIFYMUCHECKED_MLDSA87 = EQUIV_DISCHARGE EQ_MLDSAVERIFYMUCHECKED_MLDSA87;;
let EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA44 = EQUIV_DISCHARGE EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA44;;
let EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA65 = EQUIV_DISCHARGE EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA65;;
let EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA87 = EQUIV_DISCHARGE EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA87;;
let EQ_MLDSAVERIFYLENGTHCHECK_MLDSA44 = EQUIV_DISCHARGE EQ_MLDSAVERIFYLENGTHCHECK_MLDSA44;;
let EQ_MLDSAVERIFYLENGTHCHECK_MLDSA65 = EQUIV_DISCHARGE EQ_MLDSAVERIFYLENGTHCHECK_MLDSA65;;
let EQ_MLDSAVERIFYLENGTHCHECK_MLDSA87 = EQUIV_DISCHARGE EQ_MLDSAVERIFYLENGTHCHECK_MLDSA87;;
let EQ_MLDSAVERIFYPUBLIC_MLDSA44 = EQUIV_DISCHARGE EQ_MLDSAVERIFYPUBLIC_MLDSA44;;
let EQ_MLDSAVERIFYPUBLIC_MLDSA65 = EQUIV_DISCHARGE EQ_MLDSAVERIFYPUBLIC_MLDSA65;;
let EQ_MLDSAVERIFYPUBLIC_MLDSA87 = EQUIV_DISCHARGE EQ_MLDSAVERIFYPUBLIC_MLDSA87;;
let EQ_HASHML_DSA_SIGN_MLDSA44 = EQUIV_DISCHARGE EQ_HASHML_DSA_SIGN_MLDSA44;;
let EQ_HASHML_DSA_SIGN_MLDSA65 = EQUIV_DISCHARGE EQ_HASHML_DSA_SIGN_MLDSA65;;
let EQ_HASHML_DSA_SIGN_MLDSA87 = EQUIV_DISCHARGE EQ_HASHML_DSA_SIGN_MLDSA87;;
let EQ_HASHML_DSA_VERIFY_MLDSA44 = EQUIV_DISCHARGE EQ_HASHML_DSA_VERIFY_MLDSA44;;
let EQ_HASHML_DSA_VERIFY_MLDSA65 = EQUIV_DISCHARGE EQ_HASHML_DSA_VERIFY_MLDSA65;;
let EQ_HASHML_DSA_VERIFY_MLDSA87 = EQUIV_DISCHARGE EQ_HASHML_DSA_VERIFY_MLDSA87;;
let EQ_HASHMLDSASIGNPUBLIC_MLDSA44 = EQUIV_DISCHARGE EQ_HASHMLDSASIGNPUBLIC_MLDSA44;;
let EQ_HASHMLDSASIGNPUBLIC_MLDSA65 = EQUIV_DISCHARGE EQ_HASHMLDSASIGNPUBLIC_MLDSA65;;
let EQ_HASHMLDSASIGNPUBLIC_MLDSA87 = EQUIV_DISCHARGE EQ_HASHMLDSASIGNPUBLIC_MLDSA87;;
let EQ_HASHMLDSAVERIFYPUBLIC_MLDSA44 = EQUIV_DISCHARGE EQ_HASHMLDSAVERIFYPUBLIC_MLDSA44;;
let EQ_HASHMLDSAVERIFYPUBLIC_MLDSA65 = EQUIV_DISCHARGE EQ_HASHMLDSAVERIFYPUBLIC_MLDSA65;;
let EQ_HASHMLDSAVERIFYPUBLIC_MLDSA87 = EQUIV_DISCHARGE EQ_HASHMLDSAVERIFYPUBLIC_MLDSA87;;
let EQ_PREHASH = EQUIV_DISCHARGE EQ_PREHASH;;
let EQ_OIDBYTES = EQUIV_DISCHARGE EQ_OIDBYTES;;
let EQ_PREHASHALLOWED_MLDSA44 = EQUIV_DISCHARGE EQ_PREHASHALLOWED_MLDSA44;;
let EQ_PREHASHALLOWED_MLDSA65 = EQUIV_DISCHARGE EQ_PREHASHALLOWED_MLDSA65;;
let EQ_PREHASHALLOWED_MLDSA87 = EQUIV_DISCHARGE EQ_PREHASHALLOWED_MLDSA87;;

(* ------------------------------------------------------------------------- *)
(* The main theorems.                                                        *)
(* ------------------------------------------------------------------------- *)

let EQUIVALENCE_THEOREMS =
  ["EQ_ML_DSA_KEYGEN_MLDSA44",EQ_ML_DSA_KEYGEN_MLDSA44;
   "EQ_ML_DSA_KEYGEN_MLDSA65",EQ_ML_DSA_KEYGEN_MLDSA65;
   "EQ_ML_DSA_KEYGEN_MLDSA87",EQ_ML_DSA_KEYGEN_MLDSA87;
   "EQ_ML_DSA_SIGN_MLDSA44",EQ_ML_DSA_SIGN_MLDSA44;
   "EQ_ML_DSA_SIGN_MLDSA65",EQ_ML_DSA_SIGN_MLDSA65;
   "EQ_ML_DSA_SIGN_MLDSA87",EQ_ML_DSA_SIGN_MLDSA87;
   "EQ_ML_DSA_VERIFY_MLDSA44",EQ_ML_DSA_VERIFY_MLDSA44;
   "EQ_ML_DSA_VERIFY_MLDSA65",EQ_ML_DSA_VERIFY_MLDSA65;
   "EQ_ML_DSA_VERIFY_MLDSA87",EQ_ML_DSA_VERIFY_MLDSA87;
   "EQ_ML_DSA_VERIFY_INTERNAL_MLDSA44",EQ_ML_DSA_VERIFY_INTERNAL_MLDSA44;
   "EQ_ML_DSA_VERIFY_INTERNAL_MLDSA65",EQ_ML_DSA_VERIFY_INTERNAL_MLDSA65;
   "EQ_ML_DSA_VERIFY_INTERNAL_MLDSA87",EQ_ML_DSA_VERIFY_INTERNAL_MLDSA87;
   "EQ_MLDSASIGNMUCHECKED_MLDSA44",EQ_MLDSASIGNMUCHECKED_MLDSA44;
   "EQ_MLDSASIGNMUCHECKED_MLDSA65",EQ_MLDSASIGNMUCHECKED_MLDSA65;
   "EQ_MLDSASIGNMUCHECKED_MLDSA87",EQ_MLDSASIGNMUCHECKED_MLDSA87;
   "EQ_MLDSAVERIFYMUCHECKED_MLDSA44",EQ_MLDSAVERIFYMUCHECKED_MLDSA44;
   "EQ_MLDSAVERIFYMUCHECKED_MLDSA65",EQ_MLDSAVERIFYMUCHECKED_MLDSA65;
   "EQ_MLDSAVERIFYMUCHECKED_MLDSA87",EQ_MLDSAVERIFYMUCHECKED_MLDSA87;
   "EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA44",EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA44;
   "EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA65",EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA65;
   "EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA87",EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA87;
   "EQ_MLDSAVERIFYLENGTHCHECK_MLDSA44",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA44;
   "EQ_MLDSAVERIFYLENGTHCHECK_MLDSA65",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA65;
   "EQ_MLDSAVERIFYLENGTHCHECK_MLDSA87",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA87;
   "EQ_MLDSAVERIFYPUBLIC_MLDSA44",EQ_MLDSAVERIFYPUBLIC_MLDSA44;
   "EQ_MLDSAVERIFYPUBLIC_MLDSA65",EQ_MLDSAVERIFYPUBLIC_MLDSA65;
   "EQ_MLDSAVERIFYPUBLIC_MLDSA87",EQ_MLDSAVERIFYPUBLIC_MLDSA87;
   "EQ_HASHML_DSA_SIGN_MLDSA44",EQ_HASHML_DSA_SIGN_MLDSA44;
   "EQ_HASHML_DSA_SIGN_MLDSA65",EQ_HASHML_DSA_SIGN_MLDSA65;
   "EQ_HASHML_DSA_SIGN_MLDSA87",EQ_HASHML_DSA_SIGN_MLDSA87;
   "EQ_HASHML_DSA_VERIFY_MLDSA44",EQ_HASHML_DSA_VERIFY_MLDSA44;
   "EQ_HASHML_DSA_VERIFY_MLDSA65",EQ_HASHML_DSA_VERIFY_MLDSA65;
   "EQ_HASHML_DSA_VERIFY_MLDSA87",EQ_HASHML_DSA_VERIFY_MLDSA87;
   "EQ_HASHMLDSASIGNPUBLIC_MLDSA44",EQ_HASHMLDSASIGNPUBLIC_MLDSA44;
   "EQ_HASHMLDSASIGNPUBLIC_MLDSA65",EQ_HASHMLDSASIGNPUBLIC_MLDSA65;
   "EQ_HASHMLDSASIGNPUBLIC_MLDSA87",EQ_HASHMLDSASIGNPUBLIC_MLDSA87;
   "EQ_HASHMLDSAVERIFYPUBLIC_MLDSA44",EQ_HASHMLDSAVERIFYPUBLIC_MLDSA44;
   "EQ_HASHMLDSAVERIFYPUBLIC_MLDSA65",EQ_HASHMLDSAVERIFYPUBLIC_MLDSA65;
   "EQ_HASHMLDSAVERIFYPUBLIC_MLDSA87",EQ_HASHMLDSAVERIFYPUBLIC_MLDSA87;
   "EQ_PREHASH",EQ_PREHASH;
   "EQ_OIDBYTES",EQ_OIDBYTES;
   "EQ_PREHASHALLOWED_MLDSA44",EQ_PREHASHALLOWED_MLDSA44;
   "EQ_PREHASHALLOWED_MLDSA65",EQ_PREHASHALLOWED_MLDSA65;
   "EQ_PREHASHALLOWED_MLDSA87",EQ_PREHASHALLOWED_MLDSA87;
   "EQ_KEYGEN_INTERNAL_MLDSA44",EQ_KEYGEN_INTERNAL_MLDSA44;
   "EQ_KEYGEN_INTERNAL_MLDSA65",EQ_KEYGEN_INTERNAL_MLDSA65;
   "EQ_KEYGEN_INTERNAL_MLDSA87",EQ_KEYGEN_INTERNAL_MLDSA87;
   "EQ_SIGN_INTERNAL_MU_MLDSA44",EQ_SIGN_INTERNAL_MU_MLDSA44;
   "EQ_SIGN_INTERNAL_MU_MLDSA65",EQ_SIGN_INTERNAL_MU_MLDSA65;
   "EQ_SIGN_INTERNAL_MU_MLDSA87",EQ_SIGN_INTERNAL_MU_MLDSA87;
   "EQ_SIGN_INTERNAL_MLDSA44",EQ_SIGN_INTERNAL_MLDSA44;
   "EQ_SIGN_INTERNAL_MLDSA65",EQ_SIGN_INTERNAL_MLDSA65;
   "EQ_SIGN_INTERNAL_MLDSA87",EQ_SIGN_INTERNAL_MLDSA87;
   "EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA44",EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA44;
   "EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA65",EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA65;
   "EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA87",EQ_VERIFY_INTERNAL_MU_FINAL_MLDSA87];;

(* ------------------------------------------------------------------------- *)
(* Report, and a check that nothing is left open.                            *)
(* ------------------------------------------------------------------------- *)

let OPEN_HYPOTHESES =
  setify (itlist (fun (_,th) l -> hyp th @ l) EQUIVALENCE_THEOREMS []);;

let EQUIVALENCE_REPORT () =
  Printf.printf "%d theorems, %d open hypotheses\n"
    (length EQUIVALENCE_THEOREMS) (length OPEN_HYPOTHESES);
  List.iter (fun (n,th) ->
      if hyp th <> [] then Printf.printf "  %s: %d hypotheses\n" n (length (hyp th)))
    EQUIVALENCE_THEOREMS;
  if OPEN_HYPOTHESES <> [] then
    failwith "EQUIVALENCE_REPORT: some theorem has open hypotheses";;

EQUIVALENCE_REPORT ();;
