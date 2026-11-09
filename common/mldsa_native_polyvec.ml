(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A functional specification of the vector functions of mldsa-native's      *)
(* portable C implementation (polyvec.c and the vector parts of packing.c),  *)
(* in the style of mldsa_native_poly.ml: each C function as a HOL function   *)
(* on machine words, following the C code.                                   *)
(*                                                                           *)
(* A vector of polynomials (mld_polyvecl, mld_polyveck: L or K polynomials   *)
(* of 256 coefficients, one after the other in memory) is one function       *)
(* x:num->int32 for all its coefficients, with coefficient i of polynomial j *)
(* being x(256 * j + i), as in common/fips203.ml for ML-KEM. A vector of     *)
(* packed polynomials of P bytes each is likewise one function b:num->byte,  *)
(* with byte t of polynomial j being b(P * j + t).                           *)
(* ========================================================================= *)

needs "common/mldsa_native_packing.ml";;

(* ------------------------------------------------------------------------- *)
(* Polynomial j of a vector, and the vector of the polynomials f j.          *)
(* ------------------------------------------------------------------------- *)

let mld_poly_of = new_definition
 `mld_poly_of (x:num->int32) j = \i. x(256 * j + i)`;;

let mld_polyvec = new_definition
 `mld_polyvec (f:num->num->int32) = \i. f (i DIV 256) (i MOD 256)`;;

(*** A function on polynomials, applied to each polynomial of a vector ***)

let mld_polyvec_map = new_definition
 `mld_polyvec_map (f:(num->int32)->num->int32) x =
    mld_polyvec (\j. f (mld_poly_of x j))`;;

(*** Packing and unpacking each polynomial, with P bytes per polynomial ***)

let mld_polyvec_pack = new_definition
 `mld_polyvec_pack P (f:(num->int32)->num->byte) x =
    \t. f (mld_poly_of x (t DIV P)) (t MOD P)`;;

let mld_polyvec_unpack = new_definition
 `mld_polyvec_unpack P (f:(num->byte)->num->int32) b =
    mld_polyvec (\j. f (\t. b(P * j + t)))`;;

(* ------------------------------------------------------------------------- *)
(* The norm check of a vector of n polynomials (mld_polyvecl_chknorm):       *)
(* the OR of the checks of the polynomials, in the order of the C loop.      *)
(* ------------------------------------------------------------------------- *)

let mld_polyvec_chknorm = define
 `(mld_polyvec_chknorm 0 (x:num->int32) (B:int32) = word 0:int32) /\
  (mld_polyvec_chknorm (SUC n) x B =
     word_or (mld_polyvec_chknorm n x B)
             (mld_poly_chknorm (mld_poly_of x n) B))`;;

(* ------------------------------------------------------------------------- *)
(* The pointwise product of vectors of n polynomials, accumulated in 64 bits *)
(* and reduced (mld_polyvecl_pointwise_acc_montgomery): coefficient i is the *)
(* Montgomery reduction of the sum over j < n of the products of the         *)
(* coefficients i of polynomials j, as 64-bit words.                         *)
(* ------------------------------------------------------------------------- *)

let mld_polyvec_dot = define
 `(mld_polyvec_dot 0 (u:num->int32) (v:num->int32) i = word 0:int64) /\
  (mld_polyvec_dot (SUC n) u v i =
     word_add (mld_polyvec_dot n u v i)
              (word_mul (word_sx (u(256 * n + i)))
                        (word_sx (v(256 * n + i)))))`;;

let mld_polyvec_pointwise_acc_montgomery = new_definition
 `mld_polyvec_pointwise_acc_montgomery n (u:num->int32) (v:num->int32) =
    \i. mld_montgomery_reduce (mld_polyvec_dot n u v i)`;;

(* ------------------------------------------------------------------------- *)
(* The polynomials and coefficients of the lifted functions.                 *)
(* ------------------------------------------------------------------------- *)

let MLD_POLYVEC_COEFF = prove
 (`!(f:num->num->int32) j i. i < 256 ==> mld_polyvec f (256 * j + i) = f j i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyvec] THEN
  SUBGOAL_THEN `(256 * j + i) DIV 256 = j /\ (256 * j + i) MOD 256 = i`
   (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ADD_CLAUSES;
               ARITH_EQ]);;

let MLD_POLY_OF_POLYVEC = prove
 (`!(f:num->num->int32) j i.
        i < 256 ==> mld_poly_of (mld_polyvec f) j i = f j i`,
  SIMP_TAC[mld_poly_of; MLD_POLYVEC_COEFF]);;

let MLD_POLY_OF_POLYVEC_MAP = prove
 (`!(f:(num->int32)->num->int32) x j i.
        i < 256
        ==> mld_poly_of (mld_polyvec_map f x) j i = f (mld_poly_of x j) i`,
  SIMP_TAC[mld_polyvec_map; MLD_POLY_OF_POLYVEC]);;

let MLD_POLYVEC_MAP_COEFF = prove
 (`!(f:(num->int32)->num->int32) x i k.
        k < 256 ==> mld_polyvec_map f x (256 * i + k) = f (mld_poly_of x i) k`,
  SIMP_TAC[mld_polyvec_map; MLD_POLYVEC_COEFF]);;

let MLD_POLYVEC_PACK_COEFF = prove
 (`!P (f:(num->int32)->num->byte) x i k.
        k < P ==> mld_polyvec_pack P f x (P * i + k) = f (mld_poly_of x i) k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyvec_pack] THEN
  SUBGOAL_THEN `(P * i + k) DIV P = i /\ (P * i + k) MOD P = k`
   (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_REWRITE_TAC[MULT_SYM]);;

let MLD_POLYVEC_UNPACK_COEFF = prove
 (`!P (f:(num->byte)->num->int32) b i k.
        k < 256
        ==> mld_polyvec_unpack P f b (256 * i + k) = f (\t. b(P * i + t)) k`,
  SIMP_TAC[mld_polyvec_unpack; MLD_POLYVEC_COEFF]);;

let MLD_POLYVEC_CHKNORM_ADD1 = prove
 (`!n (x:num->int32) B.
        mld_polyvec_chknorm (n + 1) x B =
        word_or (mld_polyvec_chknorm n x B)
                (mld_poly_chknorm (mld_poly_of x n) B)`,
  REWRITE_TAC[GSYM ADD1; mld_polyvec_chknorm]);;

let MLD_POLY_CHKNORM_POLYVEC_UNPACK = prove
 (`!P (f:(num->byte)->num->int32) b i B.
        mld_poly_chknorm (mld_poly_of (mld_polyvec_unpack P f b) i) B =
        mld_poly_chknorm (f (\t. b(P * i + t))) B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_poly_chknorm; mld_poly_of] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(MESON[]
   `(!k. P k ==> (Q k <=> R k))
    ==> ((?k. P k /\ Q k) <=> (?k. P k /\ R k))`) THEN
  SIMP_TAC[MLD_POLYVEC_UNPACK_COEFF]);;
