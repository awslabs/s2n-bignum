(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
(* ========================================================================= *)
(* Bridge: the house ARM AES-256 cipher (aes256_encrypt) == the FIPS-197       *)
(* NIST cipher (aes256_cipher), UP TO A GLOBAL BYTE-ORDER REVERSAL.            *)
(*                                                                            *)
(* The tree has two AES-256 forward ciphers, both built over common/aes.ml:    *)
(*                                                                            *)
(*  - aes256_encrypt (arm/proofs/utils/aes_encrypt_spec.ml): the "house" Arm    *)
(*    primitive used by the merged AES-XTS proofs and by the AES-GCM decrypt    *)
(*    proof (PR #445).  Its round does ShiftRows THEN SubBytes (matching the    *)
(*    ARM aese instruction) and works in the little-endian byte order the Arm   *)
(*    kernel loads state in (ld1 {v.16b}).                                      *)
(*                                                                            *)
(*  - aes256_cipher (common/fips197.ml): the NIST FIPS-197 cipher, KAT-anchored *)
(*    by PR #389.  Its round does SubBytes THEN ShiftRows and works in the      *)
(*    big-endian byte order of the FIPS-197 spec (byte 0 = MSB).                *)
(*                                                                            *)
(* IMPORTANT — they are NOT equal as functions.  The naive statement            *)
(*   aes256_encrypt block ks = aes256_cipher block ks                          *)
(* is FALSE: on the NIST core vector (fips197.ml), the shared big-endian        *)
(* schedule gives aes256_cipher the correct 0xf3eed1bd... ciphertext but        *)
(* aes256_encrypt a different value.  The two differ by (a) the SubBytes /      *)
(* ShiftRows order WITHIN a round -- those two steps commute, since SubBytes    *)
(* is bytewise and ShiftRows is a byte permutation -- AND (b) a GLOBAL          *)
(* byte-order convention.  The true relation, verified end-to-end on the NIST   *)
(* AES-256 core KAT, is byte-reversal conjugation:                             *)
(*                                                                            *)
(*    aes256_encrypt block ks =                                                *)
(*      word_bytereverse (aes256_cipher (word_bytereverse block)               *)
(*                        (MAP word_bytereverse ks))                           *)
(*                                                                            *)
(* This is exactly the documented-but-previously-unproven relationship in       *)
(* arm/proofs/utils/aes_ctr_spec.ml (lines ~70-76 and its TODO): "with          *)
(* aes256_cipher x = word_bytereverse (aes256_encrypt (word_bytereverse x)      *)
(* rk'), the two outer byte-reversals cancel ... this coincidence is an         *)
(* ARGUMENT, not a theorem".  This file turns that argument into a theorem.     *)
(*                                                                            *)
(* NB on the key schedule: `ks` here is aes256_encrypt's list; the conjugated   *)
(* aes256_cipher call takes `MAP word_bytereverse ks`.  This is the same        *)
(* byte-reversal of the round keys the ARM kernel's memory image implies (see   *)
(* aes_ctr_spec.ml's "key REPRESENTATION" note); the bridge does NOT assert     *)
(* the two proofs' `rk` arguments are the same list, only relates the ciphers   *)
(* once one is byte-reversed.                                                  *)
(*                                                                            *)
(* NIST FIPS-197 has NO AES-128 forward-cipher counterpart named               *)
(* `aes128_encrypt` in this tree (only aes128_cipher exists in common/), so     *)
(* only the AES-256 case is proved here.                                        *)
(*                                                                            *)
(* HOME NOTE: this bridge references aes256_encrypt (arm/proofs/utils/...) so    *)
(* it CANNOT live in common/ -- common/ files never `needs "arm/..."` (a hard   *)
(* layering rule, see common/fips197.ml and aes_ctr_spec.ml).  It sits next to  *)
(* aes256_block_enc_eq_encrypt.ml, the analogous AES bridge.  The pure          *)
(* byte-algebra sub-lemmas below reference only common/ symbols and could be    *)
(* relocated to common/fips197.ml if a common-side consumer ever needs them.    *)
(*                                                                            *)
(* No CHEAT_TAC, no new axioms.                                                *)
(* ========================================================================= *)

needs "common/fips197.ml";;                    (* aes256_cipher, fips197_round, fips197_* *)
needs "arm/proofs/utils/aes_encrypt_spec.ml";; (* aes256_encrypt, aes256_encrypt_round    *)

(* ========================================================================= *)
(* Master byte-algebra lemmas.  A 128-bit AES state is 16 bytes; both cipher   *)
(* families lay bytes out via word_join_list_16_8 (byte 0 = MSB, i.e. list      *)
(* head is the top byte).  word_bytereverse reverses that 16-byte list, and     *)
(* commutes with byte extraction.  Proved by WORD_BLAST with the 16 bytes kept  *)
(* as opaque atoms (no S-box / GF-arithmetic reasoning needed).                 *)
(* ========================================================================= *)

let WORD_JOIN_LIST_16_8_BYTEREVERSE = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15:8 word.
     word_bytereverse
      (word_join_list_16_8 [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]) =
     word_join_list_16_8 [b15;b14;b13;b12;b11;b10;b9;b8;b7;b6;b5;b4;b3;b2;b1;b0]`,
  REWRITE_TAC[word_join_list_16_8] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC WORD_BLAST);;

(* word_subword (byte j) of a byte-reversed word = byte (15-j) of the original. *)
let WORD_SUBWORD_BYTEREVERSE_128 = prove
 (`!x:128 word.
    word_subword (word_bytereverse x) (0,8):8 word = word_subword x (120,8) /\
    word_subword (word_bytereverse x) (8,8):8 word = word_subword x (112,8) /\
    word_subword (word_bytereverse x) (16,8):8 word = word_subword x (104,8) /\
    word_subword (word_bytereverse x) (24,8):8 word = word_subword x (96,8) /\
    word_subword (word_bytereverse x) (32,8):8 word = word_subword x (88,8) /\
    word_subword (word_bytereverse x) (40,8):8 word = word_subword x (80,8) /\
    word_subword (word_bytereverse x) (48,8):8 word = word_subword x (72,8) /\
    word_subword (word_bytereverse x) (56,8):8 word = word_subword x (64,8) /\
    word_subword (word_bytereverse x) (64,8):8 word = word_subword x (56,8) /\
    word_subword (word_bytereverse x) (72,8):8 word = word_subword x (48,8) /\
    word_subword (word_bytereverse x) (80,8):8 word = word_subword x (40,8) /\
    word_subword (word_bytereverse x) (88,8):8 word = word_subword x (32,8) /\
    word_subword (word_bytereverse x) (96,8):8 word = word_subword x (24,8) /\
    word_subword (word_bytereverse x) (104,8):8 word = word_subword x (16,8) /\
    word_subword (word_bytereverse x) (112,8):8 word = word_subword x (8,8) /\
    word_subword (word_bytereverse x) (120,8):8 word = word_subword x (0,8)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* word_subword (byte j) of word_join_list_16_8 [e0;..;e15] = e_(15-j). *)
let WORD_SUBWORD_JOIN_LIST_16_8 = prove
 (`!e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15:8 word.
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (0,8):8 word = e15 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (8,8):8 word = e14 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (16,8):8 word = e13 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (24,8):8 word = e12 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (32,8):8 word = e11 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (40,8):8 word = e10 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (48,8):8 word = e9 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (56,8):8 word = e8 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (64,8):8 word = e7 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (72,8):8 word = e6 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (80,8):8 word = e5 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (88,8):8 word = e4 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (96,8):8 word = e3 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (104,8):8 word = e2 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (112,8):8 word = e1 /\
    word_subword (word_join_list_16_8 [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15]) (120,8):8 word = e0`,
  REWRITE_TAC[word_join_list_16_8] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC WORD_BLAST);;

let WORD_BYTEREVERSE_XOR = prove
 (`!a b:128 word. word_bytereverse (word_xor a b) =
                  word_xor (word_bytereverse a) (word_bytereverse b)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ========================================================================= *)
(* Per-operation byte-reversal conjugation.  SubBytes is bytewise so it        *)
(* commutes with byte-reverse; ShiftRows and MixColumns each conjugate their   *)
(* FIPS-197 counterpart.  The S-box (aes_sub_byte joined_GF2) and the GF        *)
(* multiplies (FFmul02/03 inside aes_mix_word) stay OPAQUE throughout.          *)
(* ========================================================================= *)

let AES_SUB_BYTES_BYTEREVERSE = prove
 (`!s:128 word. aes_sub_bytes joined_GF2 (word_bytereverse s) =
                word_bytereverse (aes_sub_bytes joined_GF2 s)`,
  GEN_TAC THEN REWRITE_TAC[aes_sub_bytes; aes_sub_bytes_select] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_JOIN_LIST_16_8_BYTEREVERSE] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_BYTEREVERSE_128]);;

let AES_SHIFT_ROWS_BYTEREVERSE = prove
 (`!s:128 word. aes_shift_rows (word_bytereverse s) =
                word_bytereverse (fips197_shift_rows s)`,
  GEN_TAC THEN REWRITE_TAC[aes_shift_rows; fips197_shift_rows] THEN
  REWRITE_TAC[WORD_JOIN_LIST_16_8_BYTEREVERSE] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_BYTEREVERSE_128]);;

let AES_MIX_COLUMNS_BYTEREVERSE = prove
 (`!s:128 word. aes_mix_columns (word_bytereverse s) =
                word_bytereverse (fips197_mix_columns s)`,
  GEN_TAC THEN REWRITE_TAC[aes_mix_columns; fips197_mix_columns; aes_mix_word] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_JOIN_LIST_16_8_BYTEREVERSE] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTEREVERSE_128]);;

(* SubBytes / ShiftRows commute (bytewise map vs byte permutation): this is     *)
(* the ONE real content the round-order difference reduces to.                  *)
let AES_SUB_BYTES_SHIFT_ROWS_COMMUTE = prove
 (`!s:128 word.
     aes_sub_bytes joined_GF2 (fips197_shift_rows s) =
     fips197_shift_rows (aes_sub_bytes joined_GF2 s)`,
  GEN_TAC THEN
  REWRITE_TAC[aes_sub_bytes; aes_sub_bytes_select; fips197_shift_rows] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_JOIN_LIST_16_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_JOIN_LIST_16_8]);;

(* ========================================================================= *)
(* Round-level conjugation.  A whole aes256_encrypt_round on byte-reversed      *)
(* inputs equals the byte-reverse of a whole fips197_round (and likewise the    *)
(* MixColumns-omitting final round vs fips197_final_round).                     *)
(* ========================================================================= *)

let AES256_ENCRYPT_ROUND_BYTEREVERSE = prove
 (`!cs rk:128 word.
     aes256_encrypt_round (word_bytereverse cs) (word_bytereverse rk) =
     word_bytereverse (fips197_round cs rk)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[aes256_encrypt_round; fips197_round; fips197_sub_bytes] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[AES_SHIFT_ROWS_BYTEREVERSE; AES_SUB_BYTES_BYTEREVERSE;
              AES_MIX_COLUMNS_BYTEREVERSE; WORD_BYTEREVERSE_XOR;
              WORD_BYTEREVERSE_BYTEREVERSE] THEN
  REWRITE_TAC[AES_SUB_BYTES_SHIFT_ROWS_COMMUTE]);;

(* The aes256_encrypt "final round" is inlined (no named function): it is       *)
(* word_xor (aes_sub_bytes joined_GF2 (aes_shift_rows _)) rk.                    *)
let AES256_ENCRYPT_FINAL_BYTEREVERSE = prove
 (`!cs rk:128 word.
     word_xor (aes_sub_bytes joined_GF2 (aes_shift_rows (word_bytereverse cs)))
              (word_bytereverse rk) =
     word_bytereverse (fips197_final_round cs rk)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fips197_final_round; fips197_sub_bytes] THEN
  REWRITE_TAC[AES_SHIFT_ROWS_BYTEREVERSE; AES_SUB_BYTES_BYTEREVERSE;
              WORD_BYTEREVERSE_XOR; WORD_BYTEREVERSE_BYTEREVERSE] THEN
  REWRITE_TAC[AES_SUB_BYTES_SHIFT_ROWS_COMMUTE]);;

(* ========================================================================= *)
(* Full AES-256 cipher equality, up to byte-reversal.  Requires LENGTH ks = 15 *)
(* (the AES-256 schedule has exactly 15 round keys, indexed EL 0..14).          *)
(* ========================================================================= *)

(* Base form: encrypt on byte-reversed inputs = byte-reverse of the NIST cipher.*)
let AES256_ENCRYPT_BYTEREVERSE_CIPHER = prove
 (`!block ks:(128 word) list.
     LENGTH ks = 15
     ==> aes256_encrypt (word_bytereverse block) (MAP word_bytereverse ks) =
         word_bytereverse (aes256_cipher block ks)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. j < LENGTH (ks:(128 word) list)
        ==> EL j (MAP word_bytereverse ks) = word_bytereverse (EL j ks)`
   ASSUME_TAC THENL [REWRITE_TAC[EL_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < 15 ==> EL j (MAP word_bytereverse ks) =
                   word_bytereverse (EL j (ks:(128 word)list))`
   (LABEL_TAC "elm") THENL
   [FIRST_X_ASSUM(fun eqth -> FIRST_X_ASSUM(fun mth -> ACCEPT_TAC(REWRITE_RULE[eqth] mth)));
    ALL_TAC] THEN
  REMOVE_THEN "elm" (fun elm ->
    MAP_EVERY (fun n ->
      ASSUME_TAC(MP (SPEC (mk_small_numeral n) elm)
        (EQT_ELIM(NUM_LT_CONV(mk_comb(mk_comb(`(<)`,mk_small_numeral n),`15`))))))
     (0--14)) THEN
  ASM_REWRITE_TAC[aes256_encrypt; aes256_cipher] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM WORD_BYTEREVERSE_XOR] THEN
  REWRITE_TAC[AES256_ENCRYPT_ROUND_BYTEREVERSE] THEN
  REWRITE_TAC[AES256_ENCRYPT_FINAL_BYTEREVERSE]);;

(* Consumer form 1 (matches aes_ctr_spec.ml's documented relationship):         *)
(* the NIST cipher as a byte-reversal-conjugated house encrypt.                 *)
let AES256_CIPHER_EQ_BYTEREVERSE_ENCRYPT = prove
 (`!block ks:(128 word) list.
     LENGTH ks = 15
     ==> aes256_cipher block ks =
         word_bytereverse
           (aes256_encrypt (word_bytereverse block) (MAP word_bytereverse ks))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[AES256_ENCRYPT_BYTEREVERSE_CIPHER; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* Consumer form 2 (the form step-2 wants: restate an aes256_encrypt result     *)
(* over aes256_cipher): the house encrypt as a byte-reversal-conjugated NIST    *)
(* cipher, for arbitrary block/ks.                                             *)
let AES256_ENCRYPT_EQ_BYTEREVERSE_CIPHER = prove
 (`!block ks:(128 word) list.
     LENGTH ks = 15
     ==> aes256_encrypt block ks =
         word_bytereverse
           (aes256_cipher (word_bytereverse block) (MAP word_bytereverse ks))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM AES256_ENCRYPT_BYTEREVERSE_CIPHER; LENGTH_MAP;
               WORD_BYTEREVERSE_BYTEREVERSE] THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF; WORD_BYTEREVERSE_BYTEREVERSE; MAP_ID; ETA_AX]);;
