(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification vocabulary for the AES-GCM bulk kernels aes128_gcm_enc,     *)
(* aes128_gcm_dec, aes256_gcm_enc and aes256_gcm_dec.                        *)
(*                                                                           *)
(* NIST SP 800-38D is big-endian: a 128-bit block is read as a byte string   *)
(* with the first byte most significant.  The kernels hold blocks in the     *)
(* little-endian lane order of a 128-bit load, so the two views differ by    *)
(* word_reversefields 8.  Data blocks are numbered from 0, and c is the      *)
(* counter value used for block 0: c = 2 gives the standard GCM schedule,    *)
(* where counter 1 is reserved for masking the tag.                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/fips197.ml";;
needs "common/polyval_ghash.ml";;

(* ------------------------------------------------------------------------- *)
(* Counter blocks and the keystream.  The block cipher enc is a parameter,   *)
(* instantiated with aes128_cipher or aes256_cipher from common/fips197.ml   *)
(* (as in the gctr function of common/gcm.ml).                               *)
(* ------------------------------------------------------------------------- *)

(* The NIST counter block: 96-bit nonce followed by a 32-bit counter. *)

let ctr_block = new_definition
 `ctr_block nonce ctr :int128 = word_join (nonce:96 word) (word ctr:int32)`;;

(* The keystream block for data block i, in lane order. *)

let aes_ctr_block = new_definition
 `aes_ctr_block (enc:int128->int128 list->int128) (c:num) nonce rk i =
    word_reversefields 8 (enc (ctr_block nonce (i + c)) rk)`;;

(* The i-th output block (keystream XOR input block), in lane order; for     *)
(* encryption this is the i-th ciphertext block.                             *)

let cipher_block = new_definition
 `cipher_block enc (c:num) nonce rk (inblock:num->int128) i =
    word_xor (aes_ctr_block enc c nonce rk i) (inblock i)`;;

(* The output and input blocks in NIST byte order, as hashed by GHASH: the   *)
(* encryption kernels hash their output and the decryption kernels their    *)
(* input, i.e. both hash the ciphertext.                                     *)

let nist_cipher_block = new_definition
 `nist_cipher_block enc (c:num) nonce rk inblock i =
    word_reversefields 8 (cipher_block enc c nonce rk inblock i)`;;

let nist_input_block = new_definition
 `nist_input_block (inblock:num->int128) (i:num) : int128 =
    word_reversefields 8 (inblock i)`;;

(* ------------------------------------------------------------------------- *)
(* The GHASH key table, restricted to the entries the kernels actually read. *)
(* The 4-way unrolled loop uses H^1..H^4 and their Karatsuba middle terms,   *)
(* i.e. the first 6 entries (offsets 0..80) of the table gcm_init_v8         *)
(* produces.  Each middle-term entry holds the lower power's term in its low *)
(* 64-bit lane, the opposite order from htable_mem in common/polyval_ghash.  *)
(* The single-block tail loop only uses H^1 and H^2, but the precondition is *)
(* shared, so all four powers are asserted.                                  *)
(* ------------------------------------------------------------------------- *)

let htable_mem_4 = new_definition
 `htable_mem_4 (h:int128) (ptr:int64) (s:armstate) <=>
  read (memory :> bytes128 ptr) s =
    byteswap128(h_power h 0) /\
  read (memory :> bytes128 (word_add ptr (word 16))) s =
    word_join (karatsuba_mid(h_power h 1) : 64 word)
              (karatsuba_mid(h_power h 0) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 32))) s =
    byteswap128(h_power h 1) /\
  read (memory :> bytes128 (word_add ptr (word 48))) s =
    byteswap128(h_power h 2) /\
  read (memory :> bytes128 (word_add ptr (word 64))) s =
    word_join (karatsuba_mid(h_power h 3) : 64 word)
              (karatsuba_mid(h_power h 2) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 80))) s =
    byteswap128(h_power h 3)`;;
