(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Recursive AES-256 counter-mode (CTR) ciphertext spec over an int128 block *)
(* list, used by the AES-256-GCM 8x decrypt proof.                           *)
(*                                                                           *)
(* CTR is symmetric: the same spec serves encrypt and decrypt because both   *)
(* apply word_xor x (aes256_encrypt (gcm_ctr_inc_iter k ctr0) keys).         *)
(*                                                                           *)
(* Design:                                                                   *)
(*  - each int128 element represents one 16-byte block;                      *)
(*  - byte-list adapters appear only where memory readback needs them;       *)
(*  - block k uses gcm_ctr_inc_iter k ctr0, so recursion composes and an     *)
(*    N-block induction advances k to k+1.                                   *)
(*                                                                           *)
(* No CHEAT_TAC, no new axioms.                                              *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_ctr_helpers.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;
(* Reuse the AES-XTS byte-list substrate: byte_list_at, bytes_to_int128,     *)
(* int128_to_bytes, and the shared readback machinery. These are built on    *)
(* aes256_encrypt, so no aes256_block_enc bridge is needed here.             *)
needs "arm/proofs/utils/aes_xts_common.ml";;

(* One CTR output block: data XOR the AES-256 keystream for block index k.   *)
(* This four-argument definition applies CTR to a plaintext/ciphertext block *)
(* indexed by raw ctr0/k rather than by a NIST nonce/counter pair.           *)
let aes_ctr_output_block = new_definition
 `aes_ctr_output_block (ctr0:int128) (k:num) (pt:int128) (keys:int128 list) : int128 =
    word_xor pt (aes256_encrypt (gcm_ctr_inc_iter k ctr0) keys)`;;

(* Recursive CTR over a block list. Position i uses counter                  *)
(* gcm_ctr_inc_iter (k+i) ctr0, where k is the starting block index.         *)
(* This is plain structural recursion, with no well-founded measure needed.  *)
let aes_ctr_rec = define
 `aes_ctr_rec (ctr0:int128) (k:num) ([]:int128 list) (keys:int128 list) = [] /\
  aes_ctr_rec (ctr0:int128) (k:num) (CONS pt pts) (keys:int128 list) =
    CONS (aes_ctr_output_block ctr0 k pt keys)
         (aes_ctr_rec ctr0 (k+1) pts keys)`;;

(* Top spec: CTR-encrypt the whole block list starting at block 0.           *)
let aes_ctr = new_definition
 `aes_ctr (ctr0:int128) (pts:int128 list) (keys:int128 list) : int128 list =
    aes_ctr_rec ctr0 0 pts keys`;;

(* LENGTH is preserved (so a bytes(out_p,16*N) framing matches).             *)
let LENGTH_AES_CTR_REC = prove
 (`!pts ctr0 k keys. LENGTH(aes_ctr_rec ctr0 k pts keys) = LENGTH pts`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[aes_ctr_rec; LENGTH]);;

let LENGTH_AES_CTR = prove
 (`!pts ctr0 keys. LENGTH(aes_ctr ctr0 pts keys) = LENGTH pts`,
  REWRITE_TAC[aes_ctr; LENGTH_AES_CTR_REC]);;

(* Element i of the recursive ciphertext, for any N.                         *)
let EL_AES_CTR_REC = prove
 (`!pts ctr0 k keys i.
     i < LENGTH pts
     ==> EL i (aes_ctr_rec ctr0 k pts keys) =
         aes_ctr_output_block ctr0 (k+i) (EL i pts) keys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; aes_ctr_rec; LT] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  ASM_REWRITE_TAC[EL; HD; TL; ADD_CLAUSES; LT_SUC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH(t:int128 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ctr0:int128`;`k+1`;`keys:int128 list`;`n:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `(k+1)+n = SUC(k+n)`]);;

(* Element i of the top spec, in the explicit word_xor / aes256_encrypt form *)
(* a binary postcondition's per-block store readback carries.                *)
let EL_AES_CTR = prove
 (`!pts ctr0 keys i.
     i < LENGTH pts
     ==> EL i (aes_ctr ctr0 pts keys) =
         word_xor (EL i pts) (aes256_encrypt (gcm_ctr_inc_iter i ctr0) keys)`,
  REWRITE_TAC[aes_ctr] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_AES_CTR_REC; aes_ctr_output_block; ADD_CLAUSES]);;

(* ========================================================================= *)
(* Byte-list view of the ciphertext, for a byte_list_at(out_p,len) postcond. *)
(* Mirrors AES-XTS (aes256_xts_encrypt : byte list) and the encrypt-side     *)
(* aes256_gcm_encrypt, but built on the XTS substrate int128_to_bytes +      *)
(* aes256_encrypt (NO aes256_block_enc).                                     *)
(* ========================================================================= *)

(* Flatten an int128 block list to a byte list (APPEND of int128_to_bytes),  *)
(* exactly the XTS APPEND-of-int128_to_bytes shape.                          *)
let int128_list_to_bytes = define
 `int128_list_to_bytes ([]:int128 list) : byte list = [] /\
  int128_list_to_bytes (CONS w ws) =
    APPEND (int128_to_bytes w) (int128_list_to_bytes ws)`;;

(* LENGTH of the flattened byte list = 16 * number of blocks.                *)
let LENGTH_INT128_TO_BYTES = prove
 (`!w:int128. LENGTH(int128_to_bytes w) = 16`,
  REWRITE_TAC[int128_to_bytes; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_INT128_LIST_TO_BYTES = prove
 (`!ws. LENGTH(int128_list_to_bytes ws) = 16 * LENGTH ws`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[int128_list_to_bytes; LENGTH; LENGTH_APPEND;
                  LENGTH_INT128_TO_BYTES] THEN ARITH_TAC);;

(* Byte ciphertext of the whole block list.                                  *)
let aes_ctr_bytes = new_definition
 `aes_ctr_bytes (ctr0:int128) (pts:int128 list) (keys:int128 list) : byte list =
    int128_list_to_bytes (aes_ctr ctr0 pts keys)`;;

(* ========================================================================= *)
(* Byte-extraction sublemmas for the whole-block byte_list_at bridges of     *)
(* the 8x decrypt proof: a bytes128 read seen as its 16 bytes8 reads, and    *)
(* byte i of an int128 (or of a flattened int128 list) as a word_subword.    *)
(* BYTES128_TO_BYTES8_THM itself lives in aes_xts_common.ml.                 *)
(* ========================================================================= *)

let BYTES128_TO_BYTES8_0 =
  REWRITE_RULE[ADD_CLAUSES; WORD_ADD_0] (SPEC `0` BYTES128_TO_BYTES8_THM);;

let SUBWORD_BYTES_TO_INT128 = prove(
 `!b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 i. i < 16
   ==> word_subword (bytes_to_int128 [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]) (8*i,8):byte =
       EL i [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[bytes_to_int128] THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC WORD_BLAST);;

let BYTE8_OF_BYTES128 = prove(
 `!p s i. i < 16 ==> read (memory :> bytes8 (word_add p (word i))) s =
                     word_subword (read (memory :> bytes128 p) s) (8*i,8)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [BYTES128_TO_BYTES8_0] THEN
  ASM_SIMP_TAC[SUBWORD_BYTES_TO_INT128] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN REWRITE_TAC[WORD_ADD_0]);;

let EL_INT128_TO_BYTES = prove(
 `!w i. i < 16 ==> EL i (int128_to_bytes w):byte = word_subword w (8*i,8)`,
  GEN_TAC THEN REWRITE_TAC[int128_to_bytes] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[]);;

(* num DIV/MOD step lemmas for the int128_list_to_bytes per-byte unfolding.  *)
let DIV16_STEP = prove
 (`!i. 16 <= i ==> i DIV 16 = SUC((i - 16) DIV 16)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i = (i - 16) + 1 * 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC]);;

let MOD16_STEP = prove
 (`!i. 16 <= i ==> i MOD 16 = (i - 16) MOD 16`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i MOD 16 = ((i - 16) + 1 * 16) MOD 16` SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[MOD_MULT_ADD]]);;

(* byte i of the flattened block list = byte (i MOD 16) of block (i DIV 16). *)
let EL_INT128_LIST_TO_BYTES = prove
 (`!cts i. i < 16 * LENGTH cts
     ==> EL i (int128_list_to_bytes cts) =
         word_subword (EL (i DIV 16) cts) (8 * (i MOD 16), 8):byte`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; int128_list_to_bytes; MULT_CLAUSES] THENL
   [REWRITE_TAC[LT] THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(int128_to_bytes h) = 16` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_INT128_TO_BYTES]; ALL_TAC] THEN
  ASM_CASES_TAC `i < 16` THENL
   [ASM_SIMP_TAC[EL_APPEND] THEN
    SUBGOAL_THEN `i DIV 16 = 0 /\ i MOD 16 = i`
      (fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th; EL; HD]) THENL
     [ASM_SIMP_TAC[DIV_LT; MOD_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_INT128_TO_BYTES];
    ASM_SIMP_TAC[EL_APPEND] THEN
    SUBGOAL_THEN `i - 16 < 16 * LENGTH(t:int128 list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `16 <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIV16_STEP; MOD16_STEP; EL; TL]]);;
