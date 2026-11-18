(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification of Keccac (https://keccak.team/keccak_specs_summary.html).  *)
(* ========================================================================= *)

(* The specification of Keccak that does not depend on the instruction set   *)
(* is in common/fips202/properties/keccak_spec.ml and keccak_bitblast.ml.    *)
(* This file adds what only the x86 code uses.                               *)

needs "Library/words.ml";;
needs "common/fips202/properties/keccak_spec.ml";;
needs "common/fips202/properties/keccak_bitblast.ml";;

(*** Constants for the byte rotations of the x86 code ***)

let rho8_constant = define
 `rho8_constant:int64 list =
   [word 0x0605040302010007;
    word 0x0E0D0C0B0A09080F;
    word 0x1615141312111017;
    word 0x1E1D1C1B1A19181F]`;;

let rho56_constant = define
 `rho56_constant:int64 list =
   [word 0x0007060504030201;
    word 0x080F0E0D0C0B0A09;
    word 0x1017161514131211;
    word 0x181F1E1D1C1B1A19]`;;

(* ------------------------------------------------------------------------- *)
(* Additional definitions and tactics used in the proof.                     *)
(* ------------------------------------------------------------------------- *)

let PC_OFFSET_CONV =
  GEN_REWRITE_CONV DEPTH_CONV [ARITH_RULE `(m + a) + b = m + (a + b)`] THENC
  NUM_REDUCE_CONV;;

let MEMORY_256_FROM_64_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes256(word_add a (word n))) s0` in
  fun v boff n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(boff + 32*i) in
      READ_MEMORY_MERGE_CONV 2 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

let WORD_SUBWORD_JOIN_EXTRACT_64 = prove
 (`!a:int64 b:int64 c:int64 d:int64. ((word_subword (word_join ((word_join a b):int128) ((word_join c d):int128):int256) (0,64)):int64) = d /\
 !a:int64 b:int64 c:int64 d:int64. ((word_subword (word_join ((word_join a b):int128) ((word_join c d):int128):int256) (64,64)):int64) = c /\
 !a:int64 b:int64 c:int64 d:int64. ((word_subword (word_join ((word_join a b):int128) ((word_join c d):int128):int256) (128,64)):int64) = b /\
 !a:int64 b:int64 c:int64 d:int64. ((word_subword (word_join ((word_join a b):int128) ((word_join c d):int128):int256) (192,64)):int64) = a`,
 REPEAT GEN_TAC THEN
  BITBLAST_TAC);;

let WORD_SUBWORD_JOIN_EXTRACT_128 = prove
 (`!a:int64 b:int64 c:int64 d:int64. ((word_subword (word_join ((word_join a b):int128) ((word_join c d):int128):int256) (0,128)):int128) = ((word_join c d):int128) /\
 !a:int64 b:int64 c:int64 d:int64. ((word_subword (word_join ((word_join a b):int128) ((word_join c d):int128):int256) (128,128)):int128) = ((word_join a b):int128)`,
   REPEAT GEN_TAC THEN
   BITBLAST_TAC);;
