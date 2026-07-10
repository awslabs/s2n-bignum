(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
(* ========================================================================= *)
(* Recursive AES-256 counter-mode (CTR) ciphertext spec (XTS-style, but over  *)
(* an int128 block list rather than a byte list).  Part of the shared AES-GCM *)
(* spec home (N-block plan, Task 4).                                          *)
(*                                                                            *)
(* CTR is symmetric: this same spec serves encrypt (data = plaintext) and     *)
(* decrypt (data = ciphertext) -- the transform word_xor x (aes256_encrypt    *)
(* (gcm_ctr_inc_iter k ctr0) keys) is identical either way.                   *)
(*                                                                            *)
(* Design (see _docs/aesv8-gcm-nblock-generalization-plan-20260617.md, D1/D3):*)
(*  - element type = int128 (one per 16-byte block); thin bytes<->int128      *)
(*    adapters are added only where a memory readback needs them.             *)
(*  - block k's counter = gcm_ctr_inc_iter k ctr0 (the shared DEFINED iterator *)
(*    from arm/proofs/utils/gcm_ctr_helpers.ml), so the recursion composes and *)
(*    an N-block induction steps k -> k+1.                                    *)
(*                                                                            *)
(* No CHEAT_TAC, no new axioms.                                               *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_ctr_helpers.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;
(* Reuse the AES-XTS byte-list substrate VERBATIM: byte_list_at, bytes_to_int128, *)
(* int128_to_bytes (and the readback machinery READ_BYTES_AND_BYTE128_SPLIT +      *)
(* SUB_LIST_OF_INT128_TO_BYTES etc.).  These are exactly the defs Mila copied into *)
(* her GCM spec, and they are built on aes256_encrypt (our primitive) -- so reusing *)
(* them keeps us name-compatible with Mila with NO aes256_block_enc bridge (see    *)
(* _docs/gcm-spec-divergence-from-mila-handback.md, decision 2026-06-18).           *)
needs "arm/proofs/utils/aes_xts_common.ml";;

(* One CTR block: data XOR the AES-256 keystream for block index k.           *)
let aes_ctr_block = new_definition
 `aes_ctr_block (ctr0:int128) (k:num) (pt:int128) (keys:int128 list) : int128 =
    word_xor pt (aes256_encrypt (gcm_ctr_inc_iter k ctr0) keys)`;;

(* Recursive CTR over a block list; the block at list position i uses counter *)
(* gcm_ctr_inc_iter (k+i) ctr0.  k = starting block index (0 at buffer head).  *)
(* Plain structural recursion on the list (no WF measure needed).             *)
let aes_ctr_rec = define
 `aes_ctr_rec (ctr0:int128) (k:num) ([]:int128 list) (keys:int128 list) = [] /\
  aes_ctr_rec (ctr0:int128) (k:num) (CONS pt pts) (keys:int128 list) =
    CONS (aes_ctr_block ctr0 k pt keys)
         (aes_ctr_rec ctr0 (k+1) pts keys)`;;

(* Top spec: CTR-encrypt the whole block list starting at block 0.            *)
let aes_ctr = new_definition
 `aes_ctr (ctr0:int128) (pts:int128 list) (keys:int128 list) : int128 list =
    aes_ctr_rec ctr0 0 pts keys`;;

(* LENGTH is preserved (so a bytes(out_p,16*N) framing matches).              *)
let LENGTH_AES_CTR_REC = prove
 (`!pts ctr0 k keys. LENGTH(aes_ctr_rec ctr0 k pts keys) = LENGTH pts`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[aes_ctr_rec; LENGTH]);;

let LENGTH_AES_CTR = prove
 (`!pts ctr0 keys. LENGTH(aes_ctr ctr0 pts keys) = LENGTH pts`,
  REWRITE_TAC[aes_ctr; LENGTH_AES_CTR_REC]);;

(* The per-block workhorse: element i of the recursive ciphertext, for any N.  *)
let EL_AES_CTR_REC = prove
 (`!pts ctr0 k keys i.
     i < LENGTH pts
     ==> EL i (aes_ctr_rec ctr0 k pts keys) =
         aes_ctr_block ctr0 (k+i) (EL i pts) keys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; aes_ctr_rec; LT] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  ASM_REWRITE_TAC[EL; HD; TL; ADD_CLAUSES; LT_SUC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH(t:int128 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ctr0:int128`;`k+1`;`keys:int128 list`;`n:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `(k+1)+n = SUC(k+n)`]);;

(* Element i of the top spec, in the explicit word_xor / aes256_encrypt form   *)
(* a binary postcondition's per-block store readback carries.                  *)
let EL_AES_CTR = prove
 (`!pts ctr0 keys i.
     i < LENGTH pts
     ==> EL i (aes_ctr ctr0 pts keys) =
         word_xor (EL i pts) (aes256_encrypt (gcm_ctr_inc_iter i ctr0) keys)`,
  REWRITE_TAC[aes_ctr] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_AES_CTR_REC; aes_ctr_block; ADD_CLAUSES]);;

(* The concrete 2-block reduction (matches AESV8_GCM_8X_ENC_256_2BLOCK's       *)
(* per-block postcond: block 0 uses ctr0, block 1 uses gcm_ctr_inc ctr0).      *)
let AES_CTR_2_EL = prove
 (`EL 0 (aes_ctr ctr0 [pt0;pt1] keys) =
     word_xor pt0 (aes256_encrypt ctr0 keys) /\
   EL 1 (aes_ctr ctr0 [pt0;pt1] keys) =
     word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys)`,
  REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_block; gcm_ctr_inc_iter] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_1; gcm_ctr_inc_iter] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; EL; HD; TL]);;

(* The 2-block ciphertext list under MAP word_bytereverse -- the GHASH input   *)
(* list [brev ct0; brev ct1] a 2-block GHASH postcond carries.                 *)
let AES_CTR_2_MAP_BREV = prove
 (`MAP word_bytereverse (aes_ctr ctr0 [pt0;pt1] keys) =
   [word_bytereverse (word_xor pt0 (aes256_encrypt ctr0 keys));
    word_bytereverse (word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys))]`,
  REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_block; gcm_ctr_inc_iter] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_1; gcm_ctr_inc_iter; MAP]);;

(* ========================================================================= *)
(* Byte-list view of the ciphertext, for a byte_list_at(out_p,len) postcond.  *)
(* Mirrors AES-XTS (aes256_xts_encrypt : byte list) and Mila's                 *)
(* aes256_gcm_encrypt, but built on the XTS substrate int128_to_bytes +        *)
(* aes256_encrypt (NO aes256_block_enc -- handback doc decision).             *)
(* ========================================================================= *)

(* Flatten an int128 block list to a byte list (APPEND of int128_to_bytes),    *)
(* exactly the XTS/Mila APPEND-of-int128_to_bytes shape.                        *)
let int128_list_to_bytes = define
 `int128_list_to_bytes ([]:int128 list) : byte list = [] /\
  int128_list_to_bytes (CONS w ws) =
    APPEND (int128_to_bytes w) (int128_list_to_bytes ws)`;;

(* LENGTH of the flattened byte list = 16 * number of blocks.                  *)
let LENGTH_INT128_TO_BYTES = prove
 (`!w:int128. LENGTH(int128_to_bytes w) = 16`,
  REWRITE_TAC[int128_to_bytes; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let LENGTH_INT128_LIST_TO_BYTES = prove
 (`!ws. LENGTH(int128_list_to_bytes ws) = 16 * LENGTH ws`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[int128_list_to_bytes; LENGTH; LENGTH_APPEND;
                  LENGTH_INT128_TO_BYTES] THEN ARITH_TAC);;

(* whole-block (tail = 16) byte ciphertext for the full block buffer.          *)
let aes_ctr_bytes = new_definition
 `aes_ctr_bytes (ctr0:int128) (pts:int128 list) (keys:int128 list) : byte list =
    int128_list_to_bytes (aes_ctr ctr0 pts keys)`;;

let LENGTH_AES_CTR_BYTES = prove
 (`!pts ctr0 keys. LENGTH(aes_ctr_bytes ctr0 pts keys) = 16 * LENGTH pts`,
  REWRITE_TAC[aes_ctr_bytes; LENGTH_INT128_LIST_TO_BYTES; LENGTH_AES_CTR]);;

(* Concrete 2-block byte ciphertext (whole blocks): the two int128_to_bytes     *)
(* blocks appended -- the value a byte_list_at(out_p,32) postcond unfolds to.   *)
let AES_CTR_BYTES_2 = prove
 (`aes_ctr_bytes ctr0 [pt0;pt1] keys =
   APPEND (int128_to_bytes (word_xor pt0 (aes256_encrypt ctr0 keys)))
          (int128_to_bytes (word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys)))`,
  REWRITE_TAC[aes_ctr_bytes] THEN
  REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_block; gcm_ctr_inc_iter] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_1; gcm_ctr_inc_iter;
              int128_list_to_bytes; APPEND_NIL]);;

(* ========================================================================= *)
(* Readback bridges: two per-block bytes128 store readbacks  =>  one          *)
(* byte_list_at(out_p,32) buffer clause.  GCM analog of the AES-XTS            *)
(* READ_BYTES_EQ_READ_BYTE128_2BLOCKS_ENC, reusing the XTS substrate           *)
(* (READ_BYTES_AND_BYTE128_SPLIT, READ_MEMORY_BYTES_BYTES128, the             *)
(* int128_to_bytes round-trip lemmas, BYTE_LIST_TO_NUM_THM) from              *)
(* aes_xts_common.ml -- so NO new memory-model infrastructure is invented.    *)
(* ========================================================================= *)

(* base: one bytes128 read => bytes(out_p,16) in num_of_bytelist form.        *)
let CTR_BLOCK0_BYTES16 = prove(
 `!(out_p:int64) ctr0 (pt0:int128) (keys:int128 list) s.
    read (memory :> bytes128 out_p) s = word_xor pt0 (aes256_encrypt ctr0 keys)
    ==> read (memory :> bytes (out_p, 16)) s =
        num_of_bytelist (int128_to_bytes (word_xor pt0 (aes256_encrypt ctr0 keys)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES128] THEN
  ASM_REWRITE_TAC[NUM_OF_BYTELIST_OF_INT128_TO_BYTES]);;

(* num form: two bytes128 reads => bytes(out_p,32) = num_of_bytelist(aes_ctr_bytes). *)
let READ_BYTES_EQ_BYTE128_2BLOCKS_CTR = prove(
 `!(out_p:int64) ctr0 (pt0:int128) (pt1:int128) (keys:int128 list) s.
    read (memory :> bytes128 out_p) s = word_xor pt0 (aes256_encrypt ctr0 keys) /\
    read (memory :> bytes128 (word_add out_p (word 16))) s =
      word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys)
    ==> read (memory :> bytes (out_p, 32)) s =
        num_of_bytelist (aes_ctr_bytes ctr0 [pt0;pt1] keys)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (aes_ctr_bytes ctr0 [pt0;pt1] keys) = 32` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_AES_CTR_BYTES; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  IMP_REWRITE_TAC[ARITH_RULE `32 = 16 + 16`; READ_BYTES_AND_BYTE128_SPLIT] THEN
  EXISTS_TAC `aes_ctr_bytes ctr0 [pt0;pt1] keys` THEN
  ASM_SIMP_TAC[SUB_LIST_LENGTH_IMPLIES; ARITH_RULE `16 + 16 <= 32`] THEN
  REWRITE_TAC[AES_CTR_BYTES_2] THEN
  SUBGOAL_THEN `LENGTH(int128_to_bytes (word_xor pt0 (aes256_encrypt ctr0 keys))) = 16`
    ASSUME_TAC THENL [REWRITE_TAC[LENGTH_INT128_TO_BYTES]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUB_LIST_APPEND_RIGHT_LEMMA; SUB_LIST_OF_INT128_TO_BYTES;
               BYTES_TO_INT128_OF_INT128_TO_BYTES] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[] `s = l ==> num_of_bytelist s = num_of_bytelist l`) THEN
    MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[LENGTH_INT128_TO_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ASM_SIMP_TAC[SUB_LIST_APPEND_LEFT; ARITH_RULE `16 <= 16`;
                 SUB_LIST_OF_INT128_TO_BYTES] THEN
    MP_TAC(SPECL [`out_p:int64`;`ctr0:int128`;`pt0:int128`;`keys:int128 list`;`s:armstate`]
      CTR_BLOCK0_BYTES16) THEN ASM_REWRITE_TAC[]]);;

(* the wrapper a postcond uses: two bytes128 reads => byte_list_at(out_p,32).  *)
let BYTE_LIST_AT_2BLOCKS_CTR = prove(
 `!(out_p:int64) ctr0 (pt0:int128) (pt1:int128) (keys:int128 list) s.
    read (memory :> bytes128 out_p) s = word_xor pt0 (aes256_encrypt ctr0 keys) /\
    read (memory :> bytes128 (word_add out_p (word 16))) s =
      word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys)
    ==> byte_list_at (aes_ctr_bytes ctr0 [pt0;pt1] keys) out_p (word 32) s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (aes_ctr_bytes ctr0 [pt0;pt1] keys) = 32` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_AES_CTR_BYTES; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[byte_list_at] THEN
  SUBGOAL_THEN `val(word 32:int64) = 32` SUBST1_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`32`; `out_p:int64`; `aes_ctr_bytes ctr0 [pt0;pt1] keys`; `s:armstate`]
    BYTE_LIST_TO_NUM_THM) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
  MATCH_MP_TAC READ_BYTES_EQ_BYTE128_2BLOCKS_CTR THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Masked PARTIAL-TAIL byte_list_at bridge (1 <= bl <= 16 bytes).             *)
(*                                                                            *)
(* The binary reads a partial last block as a full 128-bit register and writes *)
(* a masked BLEND: word_xor (word_and CT mask) (word_and outprev (~mask)), with *)
(* mask = word (2 EXP (8*bl) - 1) -- the low bl bytes are ciphertext, the high  *)
(* 16-bl bytes are the caller's pre-existing output (see the .S walkthrough).   *)
(* byte_list_at over bl bytes constrains ONLY the low bl bytes, so it equals    *)
(* the first bl bytes of the ciphertext block -- matching Mila's gcm_ctm_tail   *)
(* (the nfull=0 tail of aes256_gcm_encrypt): word_and ct (word (2 EXP(8*tail)-1)).*)
(*                                                                            *)
(* The byte-extraction sublemmas are PORTED VERBATIM (names per plan R5) from   *)
(* manastasova/s2n-bignum-dev@756df852 arm/proofs/aes256_gcm.ml: BYTE8_OF_BYTES128 *)
(* SUBWORD_BYTES_TO_INT128, EL_SUB_LIST_0, EL_INT128_TO_BYTES, MASK_BYTE_OUT.    *)
(* BYTES128_TO_BYTES8_THM is already in aes_xts_common.ml (shared XTS substrate).*)
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

let EL_SUB_LIST_0 = prove(
 `!(l:A list) n i. i < n ==> EL i (SUB_LIST(0,n) l) = EL i l`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[SUB_LIST_CLAUSES];
    ASM_CASES_TAC `n = 0` THENL [ASM_MESON_TAC[LT]; ALL_TAC] THEN
    SUBGOAL_THEN `n = SUC(n-1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[EL; HD; TL] THEN
    SUBGOAL_THEN `i = SUC(i-1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL; TL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let EL_INT128_TO_BYTES = prove(
 `!w i. i < 16 ==> EL i (int128_to_bytes w):byte = word_subword w (8*i,8)`,
  GEN_TAC THEN REWRITE_TAC[int128_to_bytes] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[]);;

(* word_or form (Mila's gcm_ctm_tail blend) and word_xor form (our LE1BLOCK     *)
(* blend; the two masks are disjoint so or = xor): the masked byte = ct byte.   *)
let MASK_BYTE_OUT = prove(
 `!(ct:int128) (out0:int128) (n:num) (i:num).
    i < n /\ n <= 16
    ==> word_subword (word_or (word_and ct (word (2 EXP (8*n) - 1):int128))
                              (word_and out0 (word_not (word (2 EXP (8*n) - 1):int128)))) (8*i,8):byte =
        word_subword ct (8*i,8)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_NOT;
              BIT_MASK_WORD; DIMINDEX_8; DIMINDEX_128] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * i + j < 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * i + j < 8 * n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let MASK_BYTE_OUT_XOR = prove(
 `!(ct:int128) (out0:int128) (n:num) (i:num).
    i < n /\ n <= 16
    ==> word_subword (word_xor (word_and ct (word (2 EXP (8*n) - 1):int128))
                               (word_and out0 (word_not (word (2 EXP (8*n) - 1):int128)))) (8*i,8):byte =
        word_subword ct (8*i,8)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_XOR; BIT_WORD_AND; BIT_WORD_NOT;
              BIT_MASK_WORD; DIMINDEX_8; DIMINDEX_128] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * i + j < 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * i + j < 8 * n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Byte spec for one partial/full block: the first bl bytes of the ciphertext   *)
(* block (= Mila's gcm_ctm_tail viewed as a byte list, the aes256_gcm_encrypt    *)
(* nfull=0 tail).                                                               *)
let aes_ctr_tail_bytes = new_definition
 `aes_ctr_tail_bytes (ctr0:int128) (pt:int128) (keys:int128 list) (bl:num) : byte list =
    SUB_LIST (0,bl) (int128_to_bytes (word_xor pt (aes256_encrypt ctr0 keys)))`;;

(* The masked-tail readback bridge: a masked-blend bytes128 store (1<=bl<=16)    *)
(* => byte_list_at over bl bytes.  Used to weaken the LE1BLOCK masked postcond.  *)
let BYTE_LIST_AT_TAIL_CTR = prove(
 `!(out_p:int64) ctr0 (pt:int128) (keys:int128 list) outprev (bl:num) s.
    1 <= bl /\ bl <= 16 /\
    read (memory :> bytes128 out_p) s =
      word_xor (word_and (word_xor pt (aes256_encrypt ctr0 keys))
                         (word (2 EXP (8 * bl) - 1)))
               (word_and outprev (word_not (word (2 EXP (8 * bl) - 1))))
    ==> byte_list_at (aes_ctr_tail_bytes ctr0 pt keys bl) out_p (word bl) s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[byte_list_at; aes_ctr_tail_bytes] THEN
  SUBGOAL_THEN `val(word bl:int64) = bl` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < 16` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[BYTE8_OF_BYTES128] THEN
  ASM_SIMP_TAC[EL_SUB_LIST_0; EL_INT128_TO_BYTES] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MASK_BYTE_OUT_XOR]);;

(* ========================================================================= *)
(* GENERAL N-block masked-tail byte_list_at bridge (the OUT_BRIDGE_GEN analog).*)
(*                                                                            *)
(* nfull full-block stores (each = EL k (aes_ctr ...)) + one masked partial    *)
(* tail store (block nfull, low `tail` bytes ciphertext, high bytes outprev)   *)
(* ==> byte_list_at over the combined byte spec aes_ctr_full_tail_bytes, for    *)
(* val len = 16*nfull + tail, 1 <= tail <= 16.  This unifies the whole-block    *)
(* (BYTE_LIST_AT_2BLOCKS_CTR) and partial-single-block (BYTE_LIST_AT_TAIL_CTR)  *)
(* bridges and is what the 17..32-byte band / 4/8-block tail simulations        *)
(* consume.  Modeled on manastasova@756df852 OUT_BRIDGE_GEN (byte-index case    *)
(* split, reusing the ported byte-extraction sublemmas).                       *)
(* ========================================================================= *)

(* General byte ciphertext spec: nfull full blocks ++ first `tail` bytes of the *)
(* masked block nfull.  Built on aes_ctr; the analog of Mila's aes256_gcm_encrypt.*)
let aes_ctr_full_tail_bytes = new_definition
 `aes_ctr_full_tail_bytes (ctr0:int128) (pts:int128 list) (keys:int128 list)
                          (nfull:num) (tail:num) : byte list =
    APPEND (int128_list_to_bytes (SUB_LIST (0,nfull) (aes_ctr ctr0 pts keys)))
           (SUB_LIST (0,tail) (int128_to_bytes
              (word_and (EL nfull (aes_ctr ctr0 pts keys))
                        (word (2 EXP (8 * tail) - 1)))))`;;

(* num DIV/MOD step lemmas for the int128_list_to_bytes per-byte unfolding.    *)
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

(* byte i of the flattened block list = byte (i MOD 16) of block (i DIV 16).   *)
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

let LENGTH_INT128_LIST_TO_BYTES_SUBLIST = prove
 (`!cts nfull. nfull <= LENGTH cts
     ==> LENGTH(int128_list_to_bytes (SUB_LIST (0,nfull) cts)) = 16 * nfull`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_SUB_LIST] THEN
  ASM_SIMP_TAC[ARITH_RULE `nfull <= n ==> MIN (0 + nfull) n - 0 = nfull`] THEN
  ASM_ARITH_TAC);;

let BYTE_LIST_AT_NBLOCK_CTR = prove(
 `!ctr0 pts keys nfull tail out_p (len:int64) outprev s.
    1 <= tail /\ tail <= 16 /\ val len = 16 * nfull + tail /\ nfull < LENGTH pts /\
    (!k. k < nfull
         ==> read (memory :> bytes128 (word_add out_p (word (16 * k)))) s =
             EL k (aes_ctr ctr0 pts keys)) /\
    read (memory :> bytes128 (word_add out_p (word (16 * nfull)))) s =
      word_xor (word_and (EL nfull (aes_ctr ctr0 pts keys))
                         (word (2 EXP (8 * tail) - 1)))
               (word_and outprev (word_not (word (2 EXP (8 * tail) - 1))))
    ==> byte_list_at (aes_ctr_full_tail_bytes ctr0 pts keys nfull tail) out_p len s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[byte_list_at; aes_ctr_full_tail_bytes] THEN
  X_GEN_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(int128_list_to_bytes (SUB_LIST (0,nfull) (aes_ctr ctr0 pts keys))) = 16 * nfull`
     ASSUME_TAC THENL
   [MATCH_MP_TAC LENGTH_INT128_LIST_TO_BYTES_SUBLIST THEN
    ASM_SIMP_TAC[LENGTH_AES_CTR] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i < 16 * nfull` THENL
   [ASM_SIMP_TAC[EL_APPEND] THEN
    SUBGOAL_THEN `i DIV 16 < nfull` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `i < 16 * LENGTH(SUB_LIST (0,nfull) (aes_ctr ctr0 pts keys))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LENGTH_SUB_LIST; LENGTH_AES_CTR] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_INT128_LIST_TO_BYTES; EL_SUB_LIST_0] THEN
    SUBGOAL_THEN `word_add out_p (word i):int64 =
         word_add (word_add out_p (word (16 * (i DIV 16)))) (word (i MOD 16))`
       SUBST1_TAC THENL
     [SUBGOAL_THEN `i = 16 * (i DIV 16) + i MOD 16`
        (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
       [MESON_TAC[DIVISION_SIMP]; ALL_TAC] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add out_p (word (16 * (i DIV 16))):int64`; `s:armstate`; `i MOD 16`]
       BYTE8_OF_BYTES128) THEN
    ANTS_TAC THENL [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) then MP_TAC(SPEC `i DIV 16` th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ASM_SIMP_TAC[EL_APPEND] THEN
    ABBREV_TAC `j = i - 16 * nfull` THEN
    SUBGOAL_THEN `j < tail /\ j < 16 /\ i = 16 * nfull + j` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "j" THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_SUB_LIST_0; EL_INT128_TO_BYTES] THEN
    SUBGOAL_THEN `word_add out_p (word (16 * nfull + j)):int64 =
         word_add (word_add out_p (word (16 * nfull))) (word j)` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add out_p (word (16 * nfull)):int64`; `s:armstate`; `j:num`]
       BYTE8_OF_BYTES128) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    FIRST_X_ASSUM(fun th ->
       if (try lhs(concl th) =
            `read (memory :> bytes128 (word_add out_p (word (16 * nfull)))) s` with _ -> false)
       then GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th] else NO_TAC) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_XOR; BIT_WORD_AND; BIT_WORD_NOT;
                BIT_MASK_WORD; DIMINDEX_8; DIMINDEX_128] THEN
    X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `8 * j + b < 8 * tail` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `8 * j + b < 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;
