(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A functional specification of the incremental SHAKE functions of          *)
(* mldsa-native's fips202.c (keccak_absorb, keccak_finalize and              *)
(* keccak_squeeze, used by the mld_shake128 and mld_shake256 functions), in  *)
(* terms of keccak_f1600 and keccak_squeeze of common/fips202.ml.            *)
(*                                                                           *)
(* A context is a Keccak state S, as a 1600-bit word, and a position pos in  *)
(* the current block of r bytes. The C functions loop over the blocks; the   *)
(* functions here give their results in closed form:                         *)
(*                                                                           *)
(* - absorbing a message M of inlen bytes (as a number) at position pos      *)
(*   XORs the stream X = 2^(8 * pos) * M into the state block by block,      *)
(*   permuting after each of the n = (pos + inlen) DIV r full blocks, and    *)
(*   leaves the position (pos + inlen) MOD r;                                *)
(* - finalizing XORs the domain separation byte p at pos and 0x80 at r - 1;  *)
(* - squeezing outputs byte pos + j of the stream of rate parts of the       *)
(*   states S, keccak_f1600 S, ..., as byte j, and leaves the state and the  *)
(*   position after the last byte output.                                    *)
(*                                                                           *)
(* These agree with the C code for pos <= r, which holds for every context   *)
(* that the C functions produce.                                             *)
(* ========================================================================= *)

needs "common/fips202.ml";;

(* ------------------------------------------------------------------------- *)
(* Absorbing.                                                                *)
(* ------------------------------------------------------------------------- *)

let mld_keccak_absorb_blocks = define
 `mld_keccak_absorb_blocks r (S:1600 word) X 0 = S /\
  mld_keccak_absorb_blocks r S X (SUC n) =
    keccak_f1600
     (word_xor (mld_keccak_absorb_blocks r S X n)
               (word((X DIV 2 EXP (8 * r * n)) MOD 2 EXP (8 * r))))`;;

let mld_keccak_absorb = new_definition
 `mld_keccak_absorb r (S:1600 word) pos inlen M =
    let X = 2 EXP (8 * pos) * M in
    let n = (pos + inlen) DIV r in
    (word_xor (mld_keccak_absorb_blocks r S X n)
              (word((X DIV 2 EXP (8 * r * n)) MOD 2 EXP (8 * r))):1600 word,
     (pos + inlen) MOD r)`;;

(* ------------------------------------------------------------------------- *)
(* Finalizing, with the domain separation byte p (0x1F for SHAKE).           *)
(* ------------------------------------------------------------------------- *)

let mld_keccak_finalize = new_definition
 `mld_keccak_finalize r p (S:1600 word) pos =
    word_xor (word_xor S (word(2 EXP (8 * pos) * p)))
             (word(2 EXP (8 * (r - 1)) * 128)):1600 word`;;

(* ------------------------------------------------------------------------- *)
(* Squeezing: the output bytes, and the context after outlen bytes.          *)
(* ------------------------------------------------------------------------- *)

let mld_keccak_squeeze_byte = new_definition
 `mld_keccak_squeeze_byte r (S:1600 word) pos j =
    let q = pos + j in
    word_subword (keccak_squeeze (q DIV r) S) (8 * (q MOD r),8):byte`;;

let mld_keccak_squeeze_state = new_definition
 `mld_keccak_squeeze_state r (S:1600 word) pos outlen =
    if outlen = 0 then (S,pos)
    else let k = (pos + outlen - 1) DIV r in
         (keccak_squeeze k S,(pos + outlen) - r * k)`;;

(* ------------------------------------------------------------------------- *)
(* The one-shot SHAKE256 of mld_shake256: absorb the inlen bytes M into the  *)
(* zero state at position 0, finalize with 0x1F, and squeeze from the        *)
(* position r = 136 that finalizing leaves; mld_shake256_byte inlen M j is   *)
(* byte j of the output.                                                     *)
(* ------------------------------------------------------------------------- *)

let mld_shake256_state = new_definition
 `mld_shake256_state inlen M =
    mld_keccak_finalize 136 0x1F
     (FST(mld_keccak_absorb 136 (word 0) 0 inlen M))
     (SND(mld_keccak_absorb 136 (word 0) 0 inlen M))`;;

let mld_shake256_byte = new_definition
 `mld_shake256_byte inlen M =
    mld_keccak_squeeze_byte 136 (mld_shake256_state inlen M) 136`;;
