(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shared definitions for the proof that the compiler-generated FIPS 204     *)
(* specification (common/fips204/generated/fips204_generated.ml) agrees with *)
(* the handwritten one (common/fips204/fips204.ml). Load after base.ml.      *)
(*                                                                           *)
(* Convention: every equivalence lemma is an equation                        *)
(*                                                                           *)
(*   GENERATED_hol args = Value (lift (HANDWRITTEN args'))                   *)
(*                                                                           *)
(* (or Nontermination / Fault / Native_Bottom where the generated code has   *)
(* them), where lift_* below maps a value of the handwritten spec to the     *)
(* canonical value of the generated type. Equations of this form compose by  *)
(* rewriting: the arguments of a generated function in a caller are then     *)
(* lifted values, and its lemma rewrites the call. One lift per generated    *)
(* type; do not add a second lift for a type that has one here.              *)
(*                                                                           *)
(* The XOFs: the generated spec has the uninterpreted constants              *)
(* shake256_bits and shake128_bits (functions of the absorbed bit string to  *)
(* the output byte stream). Every lemma that uses H or G assumes xof_ok,     *)
(* which says they are SHAKE256 and SHAKE128 of common/fips202/fips202.ml on *)
(* byte strings. The pre-hash functions (prehash_bits) stay uninterpreted.   *)
(* ========================================================================= *)

(* Z_q: an integer, reduced mod q by residue_of_int_mod.                     *)

let lift_zq = new_definition
 `lift_zq (x:int) = FIPS204_Zq (residue_of_int_mod x)`;;

(* A polynomial (time or NTT domain, by the phantom type) from its 256       *)
(* coefficients; for an element f of R_q of common/fips204/fips204.ml this   *)
(* is used as lift_poly (\i. coeff i f), for an NTT-domain array a as        *)
(* lift_poly a.                                                              *)

let lift_poly = new_definition
 `lift_poly (a:num->int) =
    (FIPS204_Poly (list_of_seq (\i. lift_zq (a i)) 256):(A)fips204_poly)`;;

(* Integer polynomials, without reduction.                                   *)

let lift_intpoly = new_definition
 `lift_intpoly (a:num->int) = FIPS204_IntPoly (list_of_seq a 256)`;;

(* Hint polynomials: coefficient 1 where h holds, else 0.                    *)

let lift_bitpoly = new_definition
 `lift_bitpoly (h:num->bool) =
    FIPS204_BitPoly
     (list_of_seq (\i. residue_of_int_mod (if h i then &1 else &0)) 256)`;;

(* Vectors of dimindex(:N) entries, and matrices of dimindex(:R) rows and    *)
(* dimindex(:C) columns. The generated matrix is a flat list; this assumes   *)
(* row-major order (entry (i,j) at index i * C + j), as in the generated     *)
(* ExpandA and MatrixVectorNTT (see sample.ml and ntt.ml).                   *)

let lift_vec = new_definition
 `lift_vec (v:num->B) =
    (Common_Vec (list_of_seq v (dimindex(:N))):(N,B)common_vec)`;;

let lift_mat = new_definition
 `lift_mat (m:num->num->E) =
    (FIPS_Matrix
      (list_of_seq (\n. m (n DIV dimindex(:C)) (n MOD dimindex(:C)))
                   (dimindex(:R) * dimindex(:C))):(R,C,E)fips_matrix)`;;

(* The XOF assumption.                                                       *)

let xof_ok = new_definition
 `xof_ok <=>
    (!s. shake256_bits (bits_of_bytes s) = shake256 s) /\
    (!s. shake128_bits (bits_of_bytes s) = shake128 s)`;;

(* The results of the handwritten signing and verification functions as the *)
(* results of the generated ones.                                            *)
(*                                                                           *)
(* lift_sign_result and lift_verify_result are for the functions with a      *)
(* context (mldsa_sign, mldsa_verify, hash_mldsa_sign and so on): a success  *)
(* is Value (Native_Value x), the BadContext failure is the bottom of FIPS   *)
(* 204, Value Native_Bottom, and OutOfAttempts (the signing loop does not    *)
(* terminate) is Nontermination. A verification that rejects the signature   *)
(* is Value (Native_Value F).                                                *)
(*                                                                           *)
(* The internal generated functions return a bare value (a signature or a    *)
(* bool), not a native_bottom value: lift_sign_internal_result and           *)
(* lift_verify_bool. The functions that they are compared with take no       *)
(* context and never give BadContext. The BadContext clauses (Fault          *)
(* Explicit_Abort for signing, F for verification) only make the             *)
(* definitions total; no theorem uses them.                                  *)

let lift_sign_result = define
 `lift_sign_result (MLDSA_Sign_Success x) =
    (Value (Native_Value x):((byte list)native_bottom)native_result) /\
  lift_sign_result MLDSA_Sign_Error_BadContext =
    (Value Native_Bottom:((byte list)native_bottom)native_result) /\
  lift_sign_result MLDSA_Sign_Error_OutOfAttempts =
    (Nontermination:((byte list)native_bottom)native_result)`;;

let lift_sign_internal_result = define
 `lift_sign_internal_result (MLDSA_Sign_Success x) =
    (Value x:(byte list)native_result) /\
  lift_sign_internal_result MLDSA_Sign_Error_BadContext =
    (Fault Explicit_Abort:(byte list)native_result) /\
  lift_sign_internal_result MLDSA_Sign_Error_OutOfAttempts =
    (Nontermination:(byte list)native_result)`;;

let lift_verify_result = define
 `lift_verify_result MLDSA_Verify_Success =
    (Value (Native_Value T):(bool native_bottom)native_result) /\
  lift_verify_result MLDSA_Verify_Error_InvalidSignature =
    (Value (Native_Value F):(bool native_bottom)native_result) /\
  lift_verify_result MLDSA_Verify_Error_BadContext =
    (Value Native_Bottom:(bool native_bottom)native_result)`;;

let lift_verify_bool = define
 `lift_verify_bool MLDSA_Verify_Success = (Value T:bool native_result) /\
  lift_verify_bool MLDSA_Verify_Error_InvalidSignature =
    (Value F:bool native_result) /\
  lift_verify_bool MLDSA_Verify_Error_BadContext =
    (Value F:bool native_result)`;;
