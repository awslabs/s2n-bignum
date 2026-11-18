(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A functional specification of the decomposition of a coefficient into    *)
(* high and low parts and of the use of a hint in mldsa-native's portable C  *)
(* implementation (mld_decompose and mld_use_hint of rounding.h and the      *)
(* polynomial versions in poly_kl.c), in the style of                        *)
(* common/mldsa_native_poly.ml: the C arithmetic on int32_t as word          *)
(* arithmetic, with no precondition on the coefficients.                     *)
(*                                                                           *)
(* There are two versions of each, for gamma2 = (q - 1) / 88 (ML-DSA-44,     *)
(* suffix _88) and for gamma2 = (q - 1) / 32 (ML-DSA-65 and ML-DSA-87,       *)
(* suffix _32). The high part is computed as in the C code, from             *)
(* (a + 127) >> 7 by a multiplication and a shift.                           *)
(* ========================================================================= *)

needs "common/mldsa_native_poly.ml";;

(* ------------------------------------------------------------------------- *)
(* mld_ct_sel_int32 of ct.h: a if cond is all ones, b if it is zero, with    *)
(* the uint32_t cond given as an int32 with the same bits.                   *)
(* ------------------------------------------------------------------------- *)

let mld_ct_sel = new_definition
 `mld_ct_sel (a:int32) (b:int32) (cond:int32) =
    word_xor b (word_and cond (word_xor a b))`;;

(* ------------------------------------------------------------------------- *)
(* mld_decompose: a1 = (a + 127) >> 7, then a1 * 11275 + 2^23 >> 24 mapped   *)
(* to 0 if above 43 (gamma2 = (q - 1) / 88), or a1 * 1025 + 2^21 >> 22       *)
(* masked to 4 bits (gamma2 = (q - 1) / 32); a0 = a - a1 * 2 * gamma2, less  *)
(* q if a0 > (q - 1) / 2.                                                    *)
(* ------------------------------------------------------------------------- *)

let mld_decompose_hi_88 = new_definition
 `mld_decompose_hi_88 (a:int32):int32 =
    let f = word_ishr (word_add a (word 127)) 7 in
    let g = word_ishr (word_add (word_mul f (word 11275)) (word 8388608)) 24 in
    mld_ct_sel (word 0) g (mld_ct_cmask_neg (word_sub (word 43) g))`;;

let mld_decompose_lo_88 = new_definition
 `mld_decompose_lo_88 (a:int32):int32 =
    let a0 = word_sub a (word_mul (word_mul (mld_decompose_hi_88 a) (word 2))
                                  (word 95232)) in
    mld_ct_sel (word_sub a0 (word 8380417)) a0
               (mld_ct_cmask_neg (word_sub (word 4190208) a0))`;;

let mld_decompose_hi_32 = new_definition
 `mld_decompose_hi_32 (a:int32):int32 =
    let f = word_ishr (word_add a (word 127)) 7 in
    word_and (word_ishr (word_add (word_mul f (word 1025)) (word 2097152)) 22)
             (word 15)`;;

let mld_decompose_lo_32 = new_definition
 `mld_decompose_lo_32 (a:int32):int32 =
    let a0 = word_sub a (word_mul (word_mul (mld_decompose_hi_32 a) (word 2))
                                  (word 261888)) in
    mld_ct_sel (word_sub a0 (word 8380417)) a0
               (mld_ct_cmask_neg (word_sub (word 4190208) a0))`;;

(* ------------------------------------------------------------------------- *)
(* mld_use_hint: the high part, moved up or down by one (cyclically) by a    *)
(* nonzero hint, depending on the sign of the low part.                      *)
(* ------------------------------------------------------------------------- *)

let mld_use_hint_88 = new_definition
 `mld_use_hint_88 (a:int32) (h:int32):int32 =
    let a1 = mld_decompose_hi_88 a and a0 = mld_decompose_lo_88 a in
    if h = word 0 then a1
    else if &0 < ival a0 then
      if a1 = word 43 then word 0 else word_add a1 (word 1)
    else if a1 = word 0 then word 43 else word_sub a1 (word 1)`;;

let mld_use_hint_32 = new_definition
 `mld_use_hint_32 (a:int32) (h:int32):int32 =
    let a1 = mld_decompose_hi_32 a and a0 = mld_decompose_lo_32 a in
    if h = word 0 then a1
    else if &0 < ival a0 then word_and (word_add a1 (word 1)) (word 15)
    else word_and (word_sub a1 (word 1)) (word 15)`;;

(* ------------------------------------------------------------------------- *)
(* The polynomial versions (poly_kl.c), coefficient by coefficient.          *)
(* ------------------------------------------------------------------------- *)

let mld_poly_decompose_hi_88 = new_definition
 `mld_poly_decompose_hi_88 (a:num->int32) = \i. mld_decompose_hi_88 (a i)`;;

let mld_poly_decompose_lo_88 = new_definition
 `mld_poly_decompose_lo_88 (a:num->int32) = \i. mld_decompose_lo_88 (a i)`;;

let mld_poly_decompose_hi_32 = new_definition
 `mld_poly_decompose_hi_32 (a:num->int32) = \i. mld_decompose_hi_32 (a i)`;;

let mld_poly_decompose_lo_32 = new_definition
 `mld_poly_decompose_lo_32 (a:num->int32) = \i. mld_decompose_lo_32 (a i)`;;

let mld_poly_use_hint_88 = new_definition
 `mld_poly_use_hint_88 (a:num->int32) (h:num->int32) =
    \i. mld_use_hint_88 (a i) (h i)`;;

let mld_poly_use_hint_32 = new_definition
 `mld_poly_use_hint_32 (a:num->int32) (h:num->int32) =
    \i. mld_use_hint_32 (a i) (h i)`;;
