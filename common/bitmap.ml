(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bit permutations of numbers: bitmap [i_0;...;i_{k-1}] n is the number     *)
(* whose bit j is bit i_j of n, for j < k, and whose bits from k on are      *)
(* those of n. bitreverse7 and bitreverse8 are BitRev7 of FIPS 203 and       *)
(* BitRev8 of FIPS 204 on [0,128) and [0,256), where they agree with the     *)
(* reversal of a 7-bit or 8-bit word (BITREVERSE7_ALT, BITREVERSE8_ALT).     *)
(*                                                                           *)
(* This file needs only HOL Light. The FIPS 203 and FIPS 204 specifications  *)
(* and the NTT specifications of common/mlkem_mldsa.ml share these           *)
(* definitions, so that they can be loaded into one session.                 *)
(* ========================================================================= *)

needs "Library/words.ml";;

let bitmap = define
 `bitmap l n =
  nsum {i | i < LENGTH l} (\i. 2 EXP i * bitval(numbit (EL i l) n)) +
  2 EXP (LENGTH l) * n DIV 2 EXP (LENGTH l)`;;

(* BITMAP_CONV evaluates bitmap l n for a list l of numerals and a numeral n. *)

let BITMAP_CONV =
  let conv =
    GEN_REWRITE_CONV I [bitmap] THENC
    DEPTH_CONV LENGTH_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [NUMSEG_LT] THENC
    NUM_REDUCE_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [CONJUNCT1 NSUM_CLAUSES] THENC
    ONCE_DEPTH_CONV EXPAND_NSUM_CONV THENC
    DEPTH_CONV EL_CONV THENC
    ONCE_DEPTH_CONV NUMBIT_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITVAL_CLAUSES] THENC
    NUM_REDUCE_CONV in
  fun tm ->
    match tm with
      Comb(Comb(Const("bitmap",_),l),n) ->
        if is_numeral n && is_list l && forall is_numeral (dest_list l)
        then conv tm  else failwith "BITMAP_CONV"
    | _ -> failwith "BITMAP_CONV";;

let bitreverse7 = define
  `bitreverse7 = bitmap [6;5;4;3;2;1;0]`;;

let bitreverse8 = define
  `bitreverse8 = bitmap [7;6;5;4;3;2;1;0]`;;

(* On [0,2^k) they are the reversal of the bits of a k-bit word.             *)

let BITREVERSE7_ALT = prove
 (`!n. n < 128 ==> bitreverse7 n = val(word_reversefields 1 (word n:7 word))`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[bitreverse7] THEN
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC BITMAP_CONV)) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let BITREVERSE8_ALT = prove
 (`!n. n < 256 ==> bitreverse8 n = val(word_reversefields 1 (word n:8 word))`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[bitreverse8] THEN
  CONV_TAC(DEPTH_CONV(WORD_RED_CONV ORELSEC BITMAP_CONV)) THEN
  CONV_TAC WORD_REDUCE_CONV);;
