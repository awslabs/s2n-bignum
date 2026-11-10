(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A functional specification of the challenge polynomial of mldsa-native,   *)
(* mld_poly_challenge in poly_kl.c (SampleInBall of FIPS 204), following the *)
(* C code over the SHAKE256 output of the seed as an infinite byte stream s  *)
(* (mld_shake256_byte of common/mldsa_native_fips202.ml).                    *)
(*                                                                           *)
(* The first 8 bytes of s give 64 sign bits, as a little-endian number. The  *)
(* bytes from position 8 on are then read one by one: with k coefficients    *)
(* set so far, k < tau, the byte j = s(8 + n) is accepted if j <= i, where   *)
(* i = 256 - tau + k, and then c[i] = c[j] and c[j] = 1 or -1 by sign bit k; *)
(* a byte j > i is skipped. mld_poly_challenge_step tau s n is the pair of k *)
(* and the coefficients after the first n bytes from position 8, starting    *)
(* from the zero polynomial, and the result is the polynomial after the      *)
(* least number of bytes with which k reaches tau. The C code loops until    *)
(* then, which needs the hypothesis mld_poly_challenge_terminates (that      *)
(* there is such a number of bytes) for it to terminate.                     *)
(* ========================================================================= *)

needs "common/mldsa_native_fips202.ml";;

(* ------------------------------------------------------------------------- *)
(* The sign bits, and the coefficient that sign bit k gives (-1 if it is 1). *)
(* ------------------------------------------------------------------------- *)

let mld_poly_challenge_signs = new_definition
 `mld_poly_challenge_signs (s:num->byte) =
    word(num_of_bytelist(list_of_seq s 8)):int64`;;

let mld_poly_challenge_sign = new_definition
 `mld_poly_challenge_sign (s:num->byte) k =
    if bit k (mld_poly_challenge_signs s) then word_neg(word 1)
    else word 1:int32`;;

(* ------------------------------------------------------------------------- *)
(* The number k of coefficients set and the polynomial c after byte n, from  *)
(* those before it, and after n bytes.                                       *)
(* ------------------------------------------------------------------------- *)

let mld_poly_challenge_next = new_definition
 `mld_poly_challenge_next tau (s:num->byte) n (kc:num#(num->int32)) =
    let k = FST kc and c = SND kc and j = val(s(8 + n)) in
    if k < tau /\ j <= 256 - tau + k
    then k + 1,(\t. if t = j then mld_poly_challenge_sign s k
                    else if t = 256 - tau + k then c j
                    else c t)
    else kc`;;

let mld_poly_challenge_step = define
 `mld_poly_challenge_step tau (s:num->byte) 0 = (0,(\t. word 0:int32)) /\
  mld_poly_challenge_step tau s (SUC n) =
    mld_poly_challenge_next tau s n (mld_poly_challenge_step tau s n)`;;

(*** Whether byte n is accepted ***)

let mld_poly_challenge_accept = new_definition
 `mld_poly_challenge_accept tau (s:num->byte) n <=>
    FST(mld_poly_challenge_step tau s n) < tau /\
    val(s(8 + n)) <= 256 - tau + FST(mld_poly_challenge_step tau s n)`;;

(* ------------------------------------------------------------------------- *)
(* The number of bytes read from position 8 on, and the result.              *)
(* ------------------------------------------------------------------------- *)

let mld_poly_challenge_bytes = new_definition
 `mld_poly_challenge_bytes tau (s:num->byte) =
    minimal n. FST(mld_poly_challenge_step tau s n) = tau`;;

let mld_poly_challenge_terminates = new_definition
 `mld_poly_challenge_terminates tau ctlen c <=>
    ?n. FST(mld_poly_challenge_step tau (mld_shake256_byte ctlen c) n) = tau`;;

let mld_poly_challenge = new_definition
 `mld_poly_challenge tau ctlen c =
    SND(mld_poly_challenge_step tau (mld_shake256_byte ctlen c)
         (mld_poly_challenge_bytes tau (mld_shake256_byte ctlen c)))`;;
