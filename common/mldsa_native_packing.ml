(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A functional specification of the packing and unpacking of polynomials    *)
(* in mldsa-native's portable C implementation (poly.c and poly_kl.c), in    *)
(* the style of common/mldsa_native_poly.ml: each function is given as what  *)
(* the C code computes, byte by byte or coefficient by coefficient, with     *)
(* the C arithmetic on int32_t and uint8_t as word arithmetic.               *)
(*                                                                           *)
(* A byte array is a function b:num->byte, byte j being b j. The packing of  *)
(* a polynomial a:num->int32 is a function of the byte index j, computed     *)
(* from the group of coefficients that byte j belongs to; the unpacking is   *)
(* a function of the coefficient index. The C code shifts and masks the      *)
(* coefficients as int32_t (or uint32_t) values; where a coefficient is out  *)
(* of the range of the packing, its extra bits end up in the bytes exactly   *)
(* as the C expressions put them, so these functions have no precondition.   *)
(* ========================================================================= *)

needs "common/mldsa_native_poly.ml";;

(* ------------------------------------------------------------------------- *)
(* t1: 10 bits per coefficient, 4 coefficients in 5 bytes (poly.c).          *)
(* ------------------------------------------------------------------------- *)

let mld_polyt1_pack = new_definition
 `mld_polyt1_pack (a:num->int32) j:byte =
    let x = \m. a(4 * (j DIV 5) + m) in
    let k = j MOD 5 in
    if k = 0 then word_zx(x 0)
    else if k = 1 then word_zx(word_or (word_ishr (x 0) 8) (word_shl (x 1) 2))
    else if k = 2 then word_zx(word_or (word_ishr (x 1) 6) (word_shl (x 2) 4))
    else if k = 3 then word_zx(word_or (word_ishr (x 2) 4) (word_shl (x 3) 6))
    else word_zx(word_ishr (x 3) 2)`;;

let mld_polyt1_unpack = new_definition
 `mld_polyt1_unpack (b:num->byte) i:int32 =
    let y = \m. word_zx(b(5 * (i DIV 4) + m)):int32 in
    let k = i MOD 4 in
    word_and
     (if k = 0 then word_or (y 0) (word_shl (y 1) 8)
      else if k = 1 then word_or (word_ushr (y 1) 2) (word_shl (y 2) 6)
      else if k = 2 then word_or (word_ushr (y 2) 4) (word_shl (y 3) 4)
      else word_or (word_ushr (y 3) 6) (word_shl (y 4) 2))
     (word 1023)`;;

(* ------------------------------------------------------------------------- *)
(* t0: 13 bits per coefficient, of 2^12 - a as a uint32_t, 8 coefficients in *)
(* 13 bytes (poly.c).                                                        *)
(* ------------------------------------------------------------------------- *)

let mld_polyt0_pack = new_definition
 `mld_polyt0_pack (a:num->int32) j:byte =
    let t = \m. word_sub (word 4096) (a(8 * (j DIV 13) + m)):int32 in
    let k = j MOD 13 in
    if k = 0 then word_zx(t 0)
    else if k = 1 then
      word_or (word_zx(word_ushr (t 0) 8)) (word_zx(word_shl (t 1) 5))
    else if k = 2 then word_zx(word_ushr (t 1) 3)
    else if k = 3 then
      word_or (word_zx(word_ushr (t 1) 11)) (word_zx(word_shl (t 2) 2))
    else if k = 4 then
      word_or (word_zx(word_ushr (t 2) 6)) (word_zx(word_shl (t 3) 7))
    else if k = 5 then word_zx(word_ushr (t 3) 1)
    else if k = 6 then
      word_or (word_zx(word_ushr (t 3) 9)) (word_zx(word_shl (t 4) 4))
    else if k = 7 then word_zx(word_ushr (t 4) 4)
    else if k = 8 then
      word_or (word_zx(word_ushr (t 4) 12)) (word_zx(word_shl (t 5) 1))
    else if k = 9 then
      word_or (word_zx(word_ushr (t 5) 7)) (word_zx(word_shl (t 6) 6))
    else if k = 10 then word_zx(word_ushr (t 6) 2)
    else if k = 11 then
      word_or (word_zx(word_ushr (t 6) 10)) (word_zx(word_shl (t 7) 3))
    else word_zx(word_ushr (t 7) 5)`;;

let mld_polyt0_unpack = new_definition
 `mld_polyt0_unpack (b:num->byte) i:int32 =
    let y = \m. word_zx(b(13 * (i DIV 8) + m)):int32 in
    let k = i MOD 8 in
    word_sub (word 4096)
     (word_and
       (if k = 0 then word_or (y 0) (word_shl (y 1) 8)
        else if k = 1 then
          word_or (word_or (word_ushr (y 1) 5) (word_shl (y 2) 3))
                  (word_shl (y 3) 11)
        else if k = 2 then word_or (word_ushr (y 3) 2) (word_shl (y 4) 6)
        else if k = 3 then
          word_or (word_or (word_ushr (y 4) 7) (word_shl (y 5) 1))
                  (word_shl (y 6) 9)
        else if k = 4 then
          word_or (word_or (word_ushr (y 6) 4) (word_shl (y 7) 4))
                  (word_shl (y 8) 12)
        else if k = 5 then word_or (word_ushr (y 8) 1) (word_shl (y 9) 7)
        else if k = 6 then
          word_or (word_or (word_ushr (y 9) 6) (word_shl (y 10) 2))
                  (word_shl (y 11) 10)
        else word_or (word_ushr (y 11) 3) (word_shl (y 12) 5))
       (word 8191))`;;

(* ------------------------------------------------------------------------- *)
(* eta: 3 bits per coefficient of 2 - a as a uint8_t, 8 coefficients in 3    *)
(* bytes, for eta = 2 (ML-DSA-44 and ML-DSA-87); 4 bits per coefficient of   *)
(* 4 - a, 2 coefficients in a byte, for eta = 4 (ML-DSA-65) (poly_kl.c).     *)
(* ------------------------------------------------------------------------- *)

let mld_polyeta_pack_2 = new_definition
 `mld_polyeta_pack_2 (a:num->int32) j:byte =
    let t = \m. word_zx(word_sub (word 2) (a(8 * (j DIV 3) + m))):byte in
    let k = j MOD 3 in
    if k = 0 then
      word_or (word_or (t 0) (word_shl (t 1) 3)) (word_shl (t 2) 6)
    else if k = 1 then
      word_or (word_or (word_or (word_ushr (t 2) 2) (word_shl (t 3) 1))
                       (word_shl (t 4) 4))
              (word_shl (t 5) 7)
    else
      word_or (word_or (word_ushr (t 5) 1) (word_shl (t 6) 2))
              (word_shl (t 7) 5)`;;

let mld_polyeta_pack_4 = new_definition
 `mld_polyeta_pack_4 (a:num->int32) j:byte =
    let t = \m. word_zx(word_sub (word 4) (a(2 * j + m))):byte in
    word_or (t 0) (word_shl (t 1) 4)`;;

let mld_polyeta_unpack_2 = new_definition
 `mld_polyeta_unpack_2 (b:num->byte) i:int32 =
    let y = \m. word_zx(b(3 * (i DIV 8) + m)):int32 in
    let k = i MOD 8 in
    word_sub (word 2)
     (word_and
       (if k = 0 then y 0
        else if k = 1 then word_ushr (y 0) 3
        else if k = 2 then word_or (word_ushr (y 0) 6) (word_shl (y 1) 2)
        else if k = 3 then word_ushr (y 1) 1
        else if k = 4 then word_ushr (y 1) 4
        else if k = 5 then word_or (word_ushr (y 1) 7) (word_shl (y 2) 1)
        else if k = 6 then word_ushr (y 2) 2
        else word_ushr (y 2) 5)
       (word 7))`;;

let mld_polyeta_unpack_4 = new_definition
 `mld_polyeta_unpack_4 (b:num->byte) i:int32 =
    let y = word_zx(b(i DIV 2)):int32 in
    word_sub (word 4)
     (if i MOD 2 = 0 then word_and y (word 15) else word_ushr y 4)`;;

(* ------------------------------------------------------------------------- *)
(* z: 18 bits per coefficient of 2^17 - a as a uint32_t, 4 coefficients in 9 *)
(* bytes (ML-DSA-44); 20 bits per coefficient of 2^19 - a, 2 coefficients in *)
(* 5 bytes (ML-DSA-65 and ML-DSA-87) (poly_kl.c).                            *)
(* ------------------------------------------------------------------------- *)

let mld_polyz_pack_17 = new_definition
 `mld_polyz_pack_17 (a:num->int32) j:byte =
    let t = \m. word_sub (word 131072) (a(4 * (j DIV 9) + m)):int32 in
    let k = j MOD 9 in
    if k = 0 then word_zx(t 0)
    else if k = 1 then word_zx(word_ushr (t 0) 8)
    else if k = 2 then
      word_or (word_zx(word_ushr (t 0) 16)) (word_zx(word_shl (t 1) 2))
    else if k = 3 then word_zx(word_ushr (t 1) 6)
    else if k = 4 then
      word_or (word_zx(word_ushr (t 1) 14)) (word_zx(word_shl (t 2) 4))
    else if k = 5 then word_zx(word_ushr (t 2) 4)
    else if k = 6 then
      word_or (word_zx(word_ushr (t 2) 12)) (word_zx(word_shl (t 3) 6))
    else if k = 7 then word_zx(word_ushr (t 3) 2)
    else word_zx(word_ushr (t 3) 10)`;;

let mld_polyz_pack_19 = new_definition
 `mld_polyz_pack_19 (a:num->int32) j:byte =
    let t = \m. word_sub (word 524288) (a(2 * (j DIV 5) + m)):int32 in
    let k = j MOD 5 in
    if k = 0 then word_zx(t 0)
    else if k = 1 then word_zx(word_ushr (t 0) 8)
    else if k = 2 then
      word_or (word_zx(word_ushr (t 0) 16)) (word_zx(word_shl (t 1) 4))
    else if k = 3 then word_zx(word_ushr (t 1) 4)
    else word_zx(word_ushr (t 1) 12)`;;

let mld_polyz_unpack_17 = new_definition
 `mld_polyz_unpack_17 (b:num->byte) i:int32 =
    let y = \m. word_zx(b(9 * (i DIV 4) + m)):int32 in
    let k = i MOD 4 in
    word_sub (word 131072)
     (word_and
       (if k = 0 then
          word_or (word_or (y 0) (word_shl (y 1) 8)) (word_shl (y 2) 16)
        else if k = 1 then
          word_or (word_or (word_ushr (y 2) 2) (word_shl (y 3) 6))
                  (word_shl (y 4) 14)
        else if k = 2 then
          word_or (word_or (word_ushr (y 4) 4) (word_shl (y 5) 4))
                  (word_shl (y 6) 12)
        else
          word_or (word_or (word_ushr (y 6) 6) (word_shl (y 7) 2))
                  (word_shl (y 8) 10))
       (word 262143))`;;

let mld_polyz_unpack_19 = new_definition
 `mld_polyz_unpack_19 (b:num->byte) i:int32 =
    let y = \m. word_zx(b(5 * (i DIV 2) + m)):int32 in
    word_sub (word 524288)
     (if i MOD 2 = 0 then
        word_and
         (word_or (word_or (y 0) (word_shl (y 1) 8)) (word_shl (y 2) 16))
         (word 1048575)
      else
        word_or (word_or (word_ushr (y 2) 4) (word_shl (y 3) 4))
                (word_shl (y 4) 12))`;;

(* ------------------------------------------------------------------------- *)
(* w1: 6 bits per coefficient, 4 coefficients in 3 bytes, for gamma2 =       *)
(* (q - 1) / 88 (ML-DSA-44); 4 bits per coefficient, 2 in a byte, for        *)
(* gamma2 = (q - 1) / 32 (ML-DSA-65 and ML-DSA-87) (poly.c).                 *)
(* ------------------------------------------------------------------------- *)

let mld_polyw1_pack_88 = new_definition
 `mld_polyw1_pack_88 (a:num->int32) j:byte =
    let x = \m. a(4 * (j DIV 3) + m) in
    let k = j MOD 3 in
    if k = 0 then word_or (word_zx(x 0)) (word_zx(word_shl (x 1) 6))
    else if k = 1 then
      word_or (word_zx(word_ishr (x 1) 2)) (word_zx(word_shl (x 2) 4))
    else word_or (word_zx(word_ishr (x 2) 4)) (word_zx(word_shl (x 3) 2))`;;

let mld_polyw1_pack_32 = new_definition
 `mld_polyw1_pack_32 (a:num->int32) j:byte =
    word_zx(word_or (a(2 * j)) (word_shl (a(2 * j + 1)) 4))`;;

let mld_polyw1_unpack_88 = new_definition
 `mld_polyw1_unpack_88 (b:num->byte) i:int32 =
    let y = \m. word_zx(b(3 * (i DIV 4) + m)):int32 in
    let k = i MOD 4 in
    if k = 0 then word_and (y 0) (word 63)
    else if k = 1 then
      word_and (word_or (word_ushr (y 0) 6) (word_shl (y 1) 2)) (word 63)
    else if k = 2 then
      word_and (word_or (word_ushr (y 1) 4) (word_shl (y 2) 4)) (word 63)
    else word_ushr (y 2) 2`;;

let mld_polyw1_unpack_32 = new_definition
 `mld_polyw1_unpack_32 (b:num->byte) i:int32 =
    let y = word_zx(b(i DIV 2)):int32 in
    if i MOD 2 = 0 then word_and y (word 15) else word_ushr y 4`;;
