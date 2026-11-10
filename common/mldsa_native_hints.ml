(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A functional specification of the hints of signatures in mldsa-native's   *)
(* portable C implementation: the hint bit of a coefficient (mld_make_hint   *)
(* of rounding.h), and the packing and unpacking of the hints of a vector of *)
(* polynomials in a signature (mld_pack_sig_h and mld_sig_unpack_hints of    *)
(* packing.c), as functions of the input words and bytes, with the return    *)
(* values, in the style of common/mldsa_native_rounding.ml. A vector is one  *)
(* function for all its coefficients, coefficient i of polynomial j being at *)
(* the position 256 * j + i, as in common/mldsa_native_polyvec.ml.           *)
(* ========================================================================= *)

needs "common/mldsa_native_rounding.ml";;
needs "common/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* mld_make_hint(a0, a1), as a boolean: true (1) when a0 is outside          *)
(* [-gamma2, gamma2], or a0 = -gamma2 and a1 is not zero, for                *)
(* gamma2 = (q - 1) / 88 (suffix _88) and (q - 1) / 32 (suffix _32).         *)
(* ------------------------------------------------------------------------- *)

let mld_make_hint_88 = new_definition
 `mld_make_hint_88 (a0:int32) (a1:int32) <=>
    &95232 < ival a0 \/ ival a0 < -- &95232 \/
    ival a0 = -- &95232 /\ ~(a1 = word 0)`;;

let mld_make_hint_32 = new_definition
 `mld_make_hint_32 (a0:int32) (a1:int32) <=>
    &261888 < ival a0 \/ ival a0 < -- &261888 \/
    ival a0 = -- &261888 /\ ~(a1 = word 0)`;;

(*** The hint bits of the positions p of a vector, from the low parts x ***)
(*** (w0) and the high parts unpacked from the bytes b (w1_packed) ***)

let mld_polyvec_make_hint_88 = new_definition
 `mld_polyvec_make_hint_88 (x:num->int32) (b:num->byte) p <=>
    mld_make_hint_88 (x p) (mld_polyvec_unpack 192 mld_polyw1_unpack_88 b p)`;;

let mld_polyvec_make_hint_32 = new_definition
 `mld_polyvec_make_hint_32 (x:num->int32) (b:num->byte) p <=>
    mld_make_hint_32 (x p) (mld_polyvec_unpack 128 mld_polyw1_unpack_32 b p)`;;

(* ------------------------------------------------------------------------- *)
(* Packing (mld_pack_sig_h) the hint bits h of the positions of a vector of  *)
(* k polynomials into omega + k bytes: the coefficients i of the positions   *)
(* with a hint, in order, in the first omega bytes, the others being zero,   *)
(* then for each polynomial j the number of hints of the polynomials up to   *)
(* j. mld_hint_count h p is the number of hints at the positions before p,   *)
(* and mld_hint_index h p the first omega bytes after the positions before   *)
(* p. If there are more than omega hints, the C code stops at the first one  *)
(* that does not fit and returns -1, leaving the bytes unspecified, and it   *)
(* returns 0 otherwise (mld_pack_hints_ret).                                 *)
(* ------------------------------------------------------------------------- *)

let mld_hint_count = define
 `(mld_hint_count (h:num->bool) 0 = 0) /\
  (mld_hint_count h (SUC p) = mld_hint_count h p + (if h p then 1 else 0))`;;

let mld_hint_index = define
 `(mld_hint_index (h:num->bool) 0 t = word 0:byte) /\
  (mld_hint_index h (SUC p) t =
     if h p /\ t = mld_hint_count h p then word(p MOD 256)
     else mld_hint_index h p t)`;;

let mld_pack_hints = new_definition
 `mld_pack_hints omega k (h:num->bool) t:byte =
    if t < omega then mld_hint_index h (256 * k) t
    else word(mld_hint_count h (256 * (t - omega + 1)))`;;

let mld_pack_hints_ret = new_definition
 `mld_pack_hints_ret omega k (h:num->bool):int32 =
    if mld_hint_count h (256 * k) <= omega then word 0 else word 4294967295`;;

(* ------------------------------------------------------------------------- *)
(* Unpacking (mld_sig_unpack_hints) the hints of polynomial i from the       *)
(* omega + k bytes b: the coefficients b j for the j from the number of      *)
(* hints of the polynomials before i (byte omega + i - 1, or 0 for i = 0),   *)
(* mld_hints_start, to that up to i (byte omega + i) are 1, the others 0.    *)
(* The C code returns 0 if these numbers are in order and at most omega, the *)
(* coefficients are strictly increasing and, for the last polynomial, the    *)
(* unused bytes of the first omega are zero (mld_unpack_hints_ok), and -1,   *)
(* leaving the polynomial unspecified, otherwise (mld_unpack_hints_ret).     *)
(* ------------------------------------------------------------------------- *)

let mld_hints_start = new_definition
 `mld_hints_start omega (b:num->byte) i =
    if i = 0 then 0 else val(b(omega + (i - 1)))`;;

let mld_unpack_hints_ok = new_definition
 `mld_unpack_hints_ok omega k (b:num->byte) i <=>
    mld_hints_start omega b i <= val(b(omega + i)) /\
    val(b(omega + i)) <= omega /\
    (!j. mld_hints_start omega b i < j /\ j < val(b(omega + i))
         ==> val(b(j - 1)) < val(b j)) /\
    (i = k - 1
     ==> !j. val(b(omega + i)) <= j /\ j < omega ==> b j = word 0)`;;

let mld_unpack_hints = new_definition
 `mld_unpack_hints omega (b:num->byte) i p:int32 =
    if ?j. mld_hints_start omega b i <= j /\ j < val(b(omega + i)) /\
           val(b j) = p
    then word 1 else word 0`;;

let mld_unpack_hints_ret = new_definition
 `mld_unpack_hints_ret omega k (b:num->byte) i:int32 =
    if mld_unpack_hints_ok omega k b i then word 0 else word 4294967295`;;

(* ------------------------------------------------------------------------- *)
(* The counts and the index bytes position by position.                      *)
(* ------------------------------------------------------------------------- *)

let MLD_HINT_COUNT_ADD1 = prove
 (`!h p. mld_hint_count h (p + 1) =
         mld_hint_count h p + (if h p then 1 else 0)`,
  REWRITE_TAC[GSYM ADD1; mld_hint_count]);;

let MLD_HINT_INDEX_ADD1 = prove
 (`!h p t. mld_hint_index h (p + 1) t =
           if h p /\ t = mld_hint_count h p then word(p MOD 256)
           else mld_hint_index h p t`,
  REWRITE_TAC[GSYM ADD1; mld_hint_index]);;

let MLD_HINT_COUNT_MONO = prove
 (`!h p q. p <= q ==> mld_hint_count h p <= mld_hint_count h q`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LE] THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LE_REFL];
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    REWRITE_TAC[LE_REFL; mld_hint_count] THEN
    FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC]);;

let MLD_HINT_COUNT_LE = prove
 (`!h p. mld_hint_count h p <= p`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[mld_hint_count; LE_REFL] THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ARITH_TAC);;
