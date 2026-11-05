(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification vocabulary for the AES-GCM bulk kernels: the 4-way          *)
(* aes128_gcm_enc, aes128_gcm_dec, aes256_gcm_enc and aes256_gcm_dec, and    *)
(* the 8-way _alt kernels such as aes256_gcm_dec_alt.                        *)
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
needs "common/gcm.ml";;

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
(* encryption kernels hash their output and the decryption kernels their     *)
(* input, i.e. both hash the ciphertext.                                     *)

let nist_cipher_block = new_definition
 `nist_cipher_block enc (c:num) nonce rk inblock i =
    word_reversefields 8 (cipher_block enc c nonce rk inblock i)`;;

let nist_input_block = new_definition
 `nist_input_block (inblock:num->int128) (i:num) : int128 =
    word_reversefields 8 (inblock i)`;;

(* ------------------------------------------------------------------------- *)
(* The GHASH key table, restricted to the entries the 4-way kernels read.    *)
(* The 4-way unrolled loop uses H^1..H^4 and their Karatsuba middle terms,   *)
(* i.e. the first 6 entries (offsets 0..80) of the table gcm_init_v8         *)
(* produces.  Each middle-term entry holds the lower power's Karatsuba term  *)
(* in its low 64-bit lane.  The single-block tail loop multiplies only by    *)
(* H^1 and its middle term, but one precondition covers every input length,  *)
(* so all six entries are asserted.                                          *)
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

(* The whole table, all 12 entries (192 bytes) for H^1..H^8, as read by the  *)
(* 8-way unrolled kernels.  It is htable_mem_4 plus the six further entries, *)
(* so htable_mem_4 is a definitional prefix; HTABLE_MEM_8_FLAT in            *)
(* aes_gcm_common.ml gives it as 12 flat conjuncts.                          *)

let htable_mem_8 = new_definition
 `htable_mem_8 (h:int128) (ptr:int64) (s:armstate) <=>
  htable_mem_4 h ptr s /\
  read (memory :> bytes128 (word_add ptr (word 96))) s =
    byteswap128(h_power h 4) /\
  read (memory :> bytes128 (word_add ptr (word 112))) s =
    word_join (karatsuba_mid(h_power h 5) : 64 word)
              (karatsuba_mid(h_power h 4) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 128))) s =
    byteswap128(h_power h 5) /\
  read (memory :> bytes128 (word_add ptr (word 144))) s =
    byteswap128(h_power h 6) /\
  read (memory :> bytes128 (word_add ptr (word 160))) s =
    word_join (karatsuba_mid(h_power h 7) : 64 word)
              (karatsuba_mid(h_power h 6) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 176))) s =
    byteswap128(h_power h 7)`;;

(* ------------------------------------------------------------------------- *)
(* The number of blocks a whole-blocks kernel processes for a bit length     *)
(* len_bits (the C argument).  The 8-way unrolled kernels take whole blocks  *)
(* only: for any len_bits that is not a multiple of 128 they process nothing *)
(* and return 0, and a zero len_bits is zero blocks either way.              *)
(* ------------------------------------------------------------------------- *)

let gcm_wb_blocks = new_definition
 `gcm_wb_blocks (len_bits:int64) =
    if val len_bits MOD 128 = 0 then val len_bits DIV 128 else 0`;;

(* ------------------------------------------------------------------------- *)
(* The counter blocks and the output blocks in terms of NIST SP 800-38D      *)
(* (common/gcm.ml): inc32 advances ctr_block by one, and the output blocks   *)
(* in NIST byte order are GCTR, from the initial counter block               *)
(* ctr_block nonce c, of the input blocks in NIST byte order.  So with       *)
(* c = 2 and the nonce IV the kernels compute GCTR from inc32(J0), where     *)
(* J0 = IV || 1, as GCM-AE and GCM-AD do.                                    *)
(* ------------------------------------------------------------------------- *)

let INC32_CTR_BLOCK = prove
 (`!(nonce:96 word) c. inc32 (ctr_block nonce c) = ctr_block nonce (c + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inc32; ctr_block] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_BLAST
    `word_subword (word_join (nonce:96 word) (wc:int32):int128) (0,32):32 word
     = wc`;
              WORD_BLAST
    `word_subword (word_join (nonce:96 word) (wc:int32):int128) (32,96):96 word
     = nonce`] THEN
  REWRITE_TAC[WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let ITER_INC32_CTR_BLOCK = prove
 (`!j (nonce:96 word) c. ITER j inc32 (ctr_block nonce c) =
   ctr_block nonce (c + j)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[ITER; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[INC32_CTR_BLOCK] THEN REWRITE_TAC[INC32_CTR_BLOCK] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let GCTR_CTR_BLOCK = prove
 (`!enc (ks:int128 list) nonce l c.
     gctr enc ks (ctr_block nonce c) l =
     list_of_seq (\i. word_xor (EL i l) (enc (ctr_block nonce (i + c)) ks))
                 (LENGTH l)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[gctr; LENGTH; LIST_OF_SEQ; INC32_CTR_BLOCK] THEN
  REWRITE_TAC[CONS_11; EL; HD; TL; ADD_CLAUSES; o_DEF] THEN
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[ARITH_RULE `i + c + 1 = SUC(i + c)`]);;

let GCTR_NIST_BLOCKS = prove
 (`!enc rk nonce c inblock n.
     gctr enc rk (ctr_block nonce c)
       (list_of_seq (nist_input_block inblock) n) =
     list_of_seq (nist_cipher_block enc c nonce rk inblock) n`,
  REWRITE_TAC[GCTR_CTR_BLOCK; LENGTH_LIST_OF_SEQ] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ] THEN SIMP_TAC[EL_LIST_OF_SEQ] THEN
  REWRITE_TAC[nist_input_block; nist_cipher_block; cipher_block;
              aes_ctr_block] THEN
  REPEAT STRIP_TAC THEN BITBLAST_TAC);;
