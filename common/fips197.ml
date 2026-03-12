(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES definitions per FIPS 197.                                             *)
(*                                                                           *)
(* This file defines AES key expansion and cipher following the NIST spec    *)
(* exactly (SubBytes before ShiftRows). It is independent from the           *)
(* hardware-oriented definitions in common/aes.ml and arm/x86 proofs.        *)
(* Equivalence can be proved separately.                                     *)
(*                                                                           *)
(* Key expansion reuses aes_subword from common/aes.ml (SubWord is the       *)
(* same in both NIST and hardware models).                                   *)
(* ========================================================================= *)

needs "common/aes.ml";;

(* ========================================================================= *)
(* AES Key Expansion (FIPS 197 Sec 5.2)                                      *)
(* ========================================================================= *)

(* Key expansion core step (FIPS 197 Sec 5.2):
   w[i] = w[i-Nk] XOR SubWord(RotWord(w[i-1])) XOR Rcon[i/Nk] *)
let aes_kexp_core = new_definition
  `aes_kexp_core (rcon:32 word) (prev:32 word) (back:32 word) : 32 word =
    word_xor back (word_xor (aes_subword (word_rol prev 8)) rcon)`;;

let AES_KEXP_CORE_CONV =
  REWRITE_CONV [aes_kexp_core] THENC
  AES_SUBWORD_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(* SubWord-only step (FIPS 197 Sec 5.2: when Nk>6 and i mod Nk = 4) *)
let aes_kexp_sub = new_definition
  `aes_kexp_sub (prev:32 word) (back:32 word) : 32 word =
    word_xor back (aes_subword prev)`;;

let AES_KEXP_SUB_CONV =
  REWRITE_CONV [aes_kexp_sub] THENC
  AES_SUBWORD_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(* Round constants (FIPS 197 Table 5) *)
let aes_rcon = new_definition
  `aes_rcon : (32 word) list =
    [ word 0x01000000; word 0x02000000; word 0x04000000; word 0x08000000
    ; word 0x10000000; word 0x20000000; word 0x40000000; word 0x80000000
    ; word 0x1b000000; word 0x36000000 ]`;;

(* Pre-computed EL reductions for 10-element 32-bit word lists. *)
let EL_10_32_CLAUSES =
  let pat = `EL n [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9]:32 word` in
  map (fun n -> EL_CONV(subst [mk_small_numeral n,`n:num`] pat)) (0--9);;

(* AES-128 key expansion round (FIPS 197 Sec 5.2, Nk=4). *)
let aes128_kexp_round = new_definition
  `aes128_kexp_round (i:num)
    (w0:32 word, w1:32 word, w2:32 word, w3:32 word)
    : 32 word # 32 word # 32 word # 32 word =
    let w4 = aes_kexp_core (EL i aes_rcon) w3 w0 in
    let w5 = word_xor w1 w4 in
    let w6 = word_xor w2 w5 in
    let w7 = word_xor w3 w6 in
    (w4, w5, w6, w7)`;;

(* Conversion for aes128_kexp_round. *)
let AES128_KEXP_ROUND_CONV =
  REWRITE_CONV [aes128_kexp_round; aes_rcon] THENC
  REWRITE_CONV EL_10_32_CLAUSES THENC
  TOP_DEPTH_CONV let_CONV THENC
  AES_KEXP_CORE_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(* AES-256 key expansion round (FIPS 197 Sec 5.2, Nk=8 case).
   Given round index i (0-6) and the previous 8 words, produce the next 8. *)
let aes256_kexp_round = new_definition
  `aes256_kexp_round (i:num)
    (w0:32 word, w1:32 word, w2:32 word, w3:32 word,
     w4:32 word, w5:32 word, w6:32 word, w7:32 word)
    : 32 word # 32 word # 32 word # 32 word #
      32 word # 32 word # 32 word # 32 word =
    let w8  = aes_kexp_core (EL i aes_rcon) w7 w0 in
    let w9  = word_xor w1 w8 in
    let w10 = word_xor w2 w9 in
    let w11 = word_xor w3 w10 in
    let w12 = aes_kexp_sub w11 w4 in
    let w13 = word_xor w5 w12 in
    let w14 = word_xor w6 w13 in
    let w15 = word_xor w7 w14 in
    (w8, w9, w10, w11, w12, w13, w14, w15)`;;

let AES256_KEXP_ROUND_CONV =
  REWRITE_CONV [aes256_kexp_round; aes_rcon] THENC
  REWRITE_CONV EL_10_32_CLAUSES THENC
  TOP_DEPTH_CONV let_CONV THENC
  AES_KEXP_CORE_CONV THENC
  AES_KEXP_SUB_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(* AES-256 last half-round: only 4 words (core step, no SubWord step). *)
let aes256_kexp_last = new_definition
  `aes256_kexp_last (i:num)
    (w0:32 word, w1:32 word, w2:32 word, w3:32 word,
     w4:32 word, w5:32 word, w6:32 word, w7:32 word)
    : 32 word # 32 word # 32 word # 32 word =
    let w8  = aes_kexp_core (EL i aes_rcon) w7 w0 in
    let w9  = word_xor w1 w8 in
    let w10 = word_xor w2 w9 in
    let w11 = word_xor w3 w10 in
    (w8, w9, w10, w11)`;;

let AES256_KEXP_LAST_CONV =
  REWRITE_CONV [aes256_kexp_last; aes_rcon] THENC
  REWRITE_CONV EL_10_32_CLAUSES THENC
  TOP_DEPTH_CONV let_CONV THENC
  AES_KEXP_CORE_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(* ========================================================================= *)
(* KAT: AES-128 Key Expansion (FIPS 197 Appendix A.1)                       *)
(* Key = 2b7e1516 28aed2a6 abf71588 09cf4f3c                                *)
(* ========================================================================= *)

prove(`aes128_kexp_round 0
        (word 0x2b7e1516, word 0x28aed2a6, word 0xabf71588, word 0x09cf4f3c) =
       (word 0xa0fafe17, word 0x88542cb1, word 0x23a33939, word 0x2a6c7605)`,
  CONV_TAC(LAND_CONV AES128_KEXP_ROUND_CONV) THEN REFL_TAC);;

prove(`aes128_kexp_round 9
       (aes128_kexp_round 8
        (aes128_kexp_round 7
         (aes128_kexp_round 6
          (aes128_kexp_round 5
           (aes128_kexp_round 4
            (aes128_kexp_round 3
             (aes128_kexp_round 2
              (aes128_kexp_round 1
                (aes128_kexp_round 0
                  (word 0x2b7e1516, word 0x28aed2a6,
                   word 0xabf71588, word 0x09cf4f3c)))))))))) =
       (word 0xd014f9a8, word 0xc9ee2589, word 0xe13f0cc8, word 0xb6630ca6)`,
  CONV_TAC(LAND_CONV(
    RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV(
      RAND_CONV(RAND_CONV(RAND_CONV AES128_KEXP_ROUND_CONV THENC
      AES128_KEXP_ROUND_CONV) THENC
      AES128_KEXP_ROUND_CONV) THENC
      AES128_KEXP_ROUND_CONV) THENC
      AES128_KEXP_ROUND_CONV) THENC
      AES128_KEXP_ROUND_CONV) THENC
      AES128_KEXP_ROUND_CONV) THENC
      AES128_KEXP_ROUND_CONV) THENC
      AES128_KEXP_ROUND_CONV) THENC
    AES128_KEXP_ROUND_CONV)) THEN
  REFL_TAC);;

(* ========================================================================= *)
(* KAT: AES-256 Key Expansion (FIPS 197 Appendix A.3)                       *)
(* Key = 603deb10 15ca71be 2b73aef0 857d7781                                *)
(*       1f352c07 3b6108d7 2d9810a3 0914dff4                                *)
(* ========================================================================= *)

prove(`aes256_kexp_round 0
        (word 0x603deb10, word 0x15ca71be, word 0x2b73aef0, word 0x857d7781,
         word 0x1f352c07, word 0x3b6108d7, word 0x2d9810a3, word 0x0914dff4) =
       (word 0x9ba35411, word 0x8e6925af, word 0xa51a8b5f, word 0x2067fcde,
        word 0xa8b09c1a, word 0x93d194cd, word 0xbe49846e, word 0xb75d5b9a)`,
  CONV_TAC(LAND_CONV AES256_KEXP_ROUND_CONV) THEN REFL_TAC);;

prove(`aes256_kexp_last 6
       (aes256_kexp_round 5
        (aes256_kexp_round 4
         (aes256_kexp_round 3
          (aes256_kexp_round 2
           (aes256_kexp_round 1
            (aes256_kexp_round 0
              (word 0x603deb10, word 0x15ca71be,
               word 0x2b73aef0, word 0x857d7781,
               word 0x1f352c07, word 0x3b6108d7,
               word 0x2d9810a3, word 0x0914dff4))))))) =
       (word 0xfe4890d1, word 0xe6188d0b, word 0x046df344, word 0x706c631e)`,
  CONV_TAC(LAND_CONV(
    RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV(
      RAND_CONV AES256_KEXP_ROUND_CONV THENC
      AES256_KEXP_ROUND_CONV) THENC
      AES256_KEXP_ROUND_CONV) THENC
      AES256_KEXP_ROUND_CONV) THENC
      AES256_KEXP_ROUND_CONV) THENC
      AES256_KEXP_ROUND_CONV) THENC
    AES256_KEXP_LAST_CONV)) THEN
  REFL_TAC);;

(* ========================================================================= *)
(* AES Cipher steps (FIPS 197 Sec 5.1)                                      *)
(* NIST byte ordering: byte 0 = MSB of 128-bit word.                        *)
(* NIST round order: SubBytes -> ShiftRows -> MixColumns -> AddRoundKey.     *)
(* ========================================================================= *)

(* SubBytes: apply S-box to each byte. *)
let fips197_sub_bytes = new_definition
  `fips197_sub_bytes (s:128 word) : 128 word =
    aes_sub_bytes joined_GF2 s`;;

(* ShiftRows (FIPS 197 Sec 5.1.2): s'[r,c] = s[r, (c+r) mod 4]. *)
let fips197_shift_rows = new_definition
  `fips197_shift_rows (op:128 word) : 128 word =
    word_join_list_16_8
    [ (word_subword op (120, 8))
    ; (word_subword op (80, 8))
    ; (word_subword op (40, 8))
    ; (word_subword op (0, 8))
    ; (word_subword op (88, 8))
    ; (word_subword op (48, 8))
    ; (word_subword op (8, 8))
    ; (word_subword op (96, 8))
    ; (word_subword op (56, 8))
    ; (word_subword op (16, 8))
    ; (word_subword op (104, 8))
    ; (word_subword op (64, 8))
    ; (word_subword op (24, 8))
    ; (word_subword op (112, 8))
    ; (word_subword op (72, 8))
    ; (word_subword op (32, 8)) ]`;;

let FIPS197_SUB_BYTES_CONV =
  REWRITE_CONV [fips197_sub_bytes] THENC AES_SUB_BYTES_CONV;;

let FIPS197_SHIFT_ROWS_CONV =
  REWRITE_CONV [fips197_shift_rows] THENC
  WORD_JOIN_LIST_16_8_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(* KAT: FIPS 197 Appendix B, Round 1 SubBytes *)
prove(`fips197_sub_bytes (word 0x193de3bea0f4e22b9ac68d2ae9f84808) =
       word 0xd42711aee0bf98f1b8b45de51e415230`,
  CONV_TAC(LAND_CONV FIPS197_SUB_BYTES_CONV) THEN REFL_TAC);;

(* KAT: FIPS 197 Appendix B, Round 1 ShiftRows *)
prove(`fips197_shift_rows (word 0xd42711aee0bf98f1b8b45de51e415230) =
       word 0xd4bf5d30e0b452aeb84111f11e2798e5`,
  CONV_TAC(LAND_CONV FIPS197_SHIFT_ROWS_CONV) THEN REFL_TAC);;

(* MixColumns (FIPS 197 Sec 5.1.3). *)
let fips197_mix_columns = new_definition
  `fips197_mix_columns (op:128 word) : 128 word =
    let d00 = aes_mix_word op 120 112 104 96 in
    let d10 = aes_mix_word op 112 104 96 120 in
    let d20 = aes_mix_word op 104 96 120 112 in
    let d30 = aes_mix_word op 96 120 112 104 in
    let d01 = aes_mix_word op 88 80 72 64 in
    let d11 = aes_mix_word op 80 72 64 88 in
    let d21 = aes_mix_word op 72 64 88 80 in
    let d31 = aes_mix_word op 64 88 80 72 in
    let d02 = aes_mix_word op 56 48 40 32 in
    let d12 = aes_mix_word op 48 40 32 56 in
    let d22 = aes_mix_word op 40 32 56 48 in
    let d32 = aes_mix_word op 32 56 48 40 in
    let d03 = aes_mix_word op 24 16 8 0 in
    let d13 = aes_mix_word op 16 8 0 24 in
    let d23 = aes_mix_word op 8 0 24 16 in
    let d33 = aes_mix_word op 0 24 16 8 in
    word_join_list_16_8
    [d00; d10; d20; d30; d01; d11; d21; d31;
     d02; d12; d22; d32; d03; d13; d23; d33]`;;

let FIPS197_MIX_COLUMNS_CONV =
  REWRITE_CONV [fips197_mix_columns] THENC
  AES_MIX_WORD_CONV THENC
  WORD_JOIN_LIST_16_8_CONV THENC
  TOP_DEPTH_CONV let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(* KAT: FIPS 197 Appendix B, Round 1 MixColumns *)
prove(`fips197_mix_columns (word 0xd4bf5d30e0b452aeb84111f11e2798e5) =
       word 0x046681e5e0cb199a48f8d37a2806264c`,
  CONV_TAC(LAND_CONV FIPS197_MIX_COLUMNS_CONV) THEN REFL_TAC);;

(* ========================================================================= *)
(* AddRoundKey (FIPS 197 Sec 5.1.4): XOR state with round key.              *)
(* ========================================================================= *)

let fips197_add_round_key = new_definition
  `fips197_add_round_key (s:128 word) (k:128 word) : 128 word = word_xor s k`;;

(* KAT: FIPS 197 Appendix B, Round 1 AddRoundKey *)
prove(`fips197_add_round_key (word 0x046681e5e0cb199a48f8d37a2806264c)
                             (word 0xa0fafe1788542cb123a339392a6c7605) =
       word 0xa49c7ff2689f352b6b5bea43026a5049`,
  CONV_TAC(REWRITE_CONV [fips197_add_round_key] THENC
           DEPTH_CONV WORD_RED_CONV) THEN REFL_TAC);;

(* ========================================================================= *)
(* AES Cipher (FIPS 197 Algorithm 1) — unrolled                              *)
(* ========================================================================= *)

let fips197_round = new_definition
  `fips197_round (state:128 word) (round_key:128 word) : 128 word =
    word_xor
      (fips197_mix_columns (fips197_shift_rows (fips197_sub_bytes state)))
      round_key`;;

let fips197_final_round = new_definition
  `fips197_final_round (state:128 word) (round_key:128 word) : 128 word =
    word_xor
      (fips197_shift_rows (fips197_sub_bytes state))
      round_key`;;

(* AES-128: 10 rounds (1 initial AddRoundKey + 9 middle + 1 final) *)
let aes128_cipher = new_definition
  `aes128_cipher (plaintext:128 word) (ks:(128 word) list) : 128 word =
    let s0  = word_xor plaintext (EL 0 ks) in
    let s1  = fips197_round s0  (EL 1 ks) in
    let s2  = fips197_round s1  (EL 2 ks) in
    let s3  = fips197_round s2  (EL 3 ks) in
    let s4  = fips197_round s3  (EL 4 ks) in
    let s5  = fips197_round s4  (EL 5 ks) in
    let s6  = fips197_round s5  (EL 6 ks) in
    let s7  = fips197_round s6  (EL 7 ks) in
    let s8  = fips197_round s7  (EL 8 ks) in
    let s9  = fips197_round s8  (EL 9 ks) in
    fips197_final_round s9 (EL 10 ks)`;;

(* AES-256: 14 rounds (1 initial AddRoundKey + 13 middle + 1 final) *)
let aes256_cipher = new_definition
  `aes256_cipher (plaintext:128 word) (ks:(128 word) list) : 128 word =
    let s0  = word_xor plaintext (EL 0 ks) in
    let s1  = fips197_round s0  (EL 1 ks) in
    let s2  = fips197_round s1  (EL 2 ks) in
    let s3  = fips197_round s2  (EL 3 ks) in
    let s4  = fips197_round s3  (EL 4 ks) in
    let s5  = fips197_round s4  (EL 5 ks) in
    let s6  = fips197_round s5  (EL 6 ks) in
    let s7  = fips197_round s6  (EL 7 ks) in
    let s8  = fips197_round s7  (EL 8 ks) in
    let s9  = fips197_round s8  (EL 9 ks) in
    let s10 = fips197_round s9  (EL 10 ks) in
    let s11 = fips197_round s10 (EL 11 ks) in
    let s12 = fips197_round s11 (EL 12 ks) in
    let s13 = fips197_round s12 (EL 13 ks) in
    fips197_final_round s13 (EL 14 ks)`;;

(* ========================================================================= *)
(* Conversions for evaluating the cipher on concrete inputs                  *)
(* ========================================================================= *)

let FIPS197_ROUND_CONV =
  REWRITE_CONV [fips197_round] THENC
  FIPS197_SUB_BYTES_CONV THENC
  FIPS197_SHIFT_ROWS_CONV THENC
  FIPS197_MIX_COLUMNS_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let FIPS197_ROUND_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("fips197_round",_),
         Comb(Const("word",_),s)),
         Comb(Const("word",_),k))
    when is_numeral s && is_numeral k -> FIPS197_ROUND_CONV tm
    | _ -> failwith "FIPS197_ROUND_REDUCE_CONV";;

let FIPS197_FINAL_ROUND_CONV =
  REWRITE_CONV [fips197_final_round] THENC
  FIPS197_SUB_BYTES_CONV THENC
  FIPS197_SHIFT_ROWS_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let FIPS197_FINAL_ROUND_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("fips197_final_round",_),
         Comb(Const("word",_),s)),
         Comb(Const("word",_),k))
    when is_numeral s && is_numeral k -> FIPS197_FINAL_ROUND_CONV tm
    | _ -> failwith "FIPS197_FINAL_ROUND_REDUCE_CONV";;

let FIPS197_ENCRYPT_CONV cipher_def ks_def =
  REWRITE_CONV [ks_def] THENC
  REWRITE_CONV [cipher_def] THENC
  TOP_DEPTH_CONV let_CONV THENC
  DEPTH_CONV (EL_CONV ORELSEC WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  DEPTH_CONV FIPS197_ROUND_REDUCE_CONV THENC
  FIPS197_FINAL_ROUND_REDUCE_CONV;;

(* ========================================================================= *)
(* KAT: FIPS 197 Appendix B — AES-128 full encryption                       *)
(* Plaintext:  0x3243f6a8885a308d313198a2e0370734                            *)
(* Key:        0x2b7e151628aed2a6abf7158809cf4f3c                            *)
(* Ciphertext: 0x3925841d02dc09fbdc118597196a0b32                            *)
(* ========================================================================= *)

let AES128_APPENDIX_B_KEY_SCHEDULE = new_definition
  `AES128_APPENDIX_B_KEY_SCHEDULE:(128 word) list =
    [ word 0x2b7e151628aed2a6abf7158809cf4f3c
    ; word 0xa0fafe1788542cb123a339392a6c7605
    ; word 0xf2c295f27a96b9435935807a7359f67f
    ; word 0x3d80477d4716fe3e1e237e446d7a883b
    ; word 0xef44a541a8525b7fb671253bdb0bad00
    ; word 0xd4d1c6f87c839d87caf2b8bc11f915bc
    ; word 0x6d88a37a110b3efddbf98641ca0093fd
    ; word 0x4e54f70e5f5fc9f384a64fb24ea6dc4f
    ; word 0xead27321b58dbad2312bf5607f8d292f
    ; word 0xac7766f319fadc2128d12941575c006e
    ; word 0xd014f9a8c9ee2589e13f0cc8b6630ca6
    ]`;;

prove(`aes128_cipher (word 0x3243f6a8885a308d313198a2e0370734)
                     AES128_APPENDIX_B_KEY_SCHEDULE =
       word 0x3925841d02dc09fbdc118597196a0b32`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_CONV aes128_cipher
    AES128_APPENDIX_B_KEY_SCHEDULE)) THEN REFL_TAC);;

(* ========================================================================= *)
(* KAT: AES-256 full encryption (NIST AES_Core256 / FIPS 197 Appendix A.3)  *)
(* Key:        0x603deb1015ca71be2b73aef0857d7781                            *)
(*             1f352c073b6108d72d9810a30914dff4                              *)
(* Plaintext:  0x6bc1bee22e409f96e93d7e117393172a                            *)
(* Ciphertext: 0xf3eed1bdb5d2a03c064b5a7e3db181f8                            *)
(* ========================================================================= *)

let AES256_CORE_KEY_SCHEDULE = new_definition
  `AES256_CORE_KEY_SCHEDULE:(128 word) list =
    [ word 0x603DEB1015CA71BE2B73AEF0857D7781
    ; word 0x1F352C073B6108D72D9810A30914DFF4
    ; word 0x9BA354118E6925AFA51A8B5F2067FCDE
    ; word 0xA8B09C1A93D194CDBE49846EB75D5B9A
    ; word 0xD59AECB85BF3C917FEE94248DE8EBE96
    ; word 0xB5A9328A2678A647983122292F6C79B3
    ; word 0x812C81ADDADF48BA24360AF2FAB8B464
    ; word 0x98C5BFC9BEBD198E268C3BA709E04214
    ; word 0x68007BACB2DF331696E939E46C518D80
    ; word 0xC814E20476A9FB8A5025C02D59C58239
    ; word 0xDE1369676CCC5A71FA2563959674EE15
    ; word 0x5886CA5D2E2F31D77E0AF1FA27CF73C3
    ; word 0x749C47AB18501DDAE2757E4F7401905A
    ; word 0xCAFAAAE3E4D59B349ADF6ACEBD10190D
    ; word 0xFE4890D1E6188D0B046DF344706C631E
    ]`;;

prove(`aes256_cipher (word 0x6bc1bee22e409f96e93d7e117393172a)
                     AES256_CORE_KEY_SCHEDULE =
       word 0xf3eed1bdb5d2a03c064b5a7e3db181f8`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_CONV aes256_cipher
    AES256_CORE_KEY_SCHEDULE)) THEN REFL_TAC);;

(* ========================================================================= *)
(* KAT: AESAVS Appendix B GFSbox — AES-128 with all-zero key                *)
(* Source: "The Advanced Encryption Standard Algorithm Validation Suite"      *)
(* ========================================================================= *)

let AESAVS_ZERO_KEY_128_SCHEDULE = new_definition
  `AESAVS_ZERO_KEY_128_SCHEDULE:(128 word) list =
    [ word 0x00000000000000000000000000000000
    ; word 0x62636363626363636263636362636363
    ; word 0x9B9898C9F9FBFBAA9B9898C9F9FBFBAA
    ; word 0x90973450696CCFFAF2F457330B0FAC99
    ; word 0xEE06DA7B876A1581759E42B27E91EE2B
    ; word 0x7F2E2B88F8443E098DDA7CBBF34B9290
    ; word 0xEC614B851425758C99FF09376AB49BA7
    ; word 0x217517873550620BACAF6B3CC61BF09B
    ; word 0x0EF903333BA9613897060A04511DFA9F
    ; word 0xB1D4D8E28A7DB9DA1D7BB3DE4C664941
    ; word 0xB4EF5BCB3E92E21123E951CF6F8F188E
    ]`;;

(* AESAVS GFSbox first vector: key=0, pt=f34481ec... *)
prove(`aes128_cipher (word 0xf34481ec3cc627bacd5dc3fb08f273e6)
                     AESAVS_ZERO_KEY_128_SCHEDULE =
       word 0x0336763e966d92595a567cc9ce537f5e`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_CONV aes128_cipher
    AESAVS_ZERO_KEY_128_SCHEDULE)) THEN REFL_TAC);;

(* AESAVS: key=0, pt=0 *)
prove(`aes128_cipher (word 0x00000000000000000000000000000000)
                     AESAVS_ZERO_KEY_128_SCHEDULE =
       word 0x66e94bd4ef8a2c3b884cfa59ca342b2e`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_CONV aes128_cipher
    AESAVS_ZERO_KEY_128_SCHEDULE)) THEN REFL_TAC);;

(* ========================================================================= *)
(* KAT: AES-256 with all-zero key                                           *)
(* ========================================================================= *)

let AESAVS_ZERO_KEY_256_SCHEDULE = new_definition
  `AESAVS_ZERO_KEY_256_SCHEDULE:(128 word) list =
    [ word 0x00000000000000000000000000000000
    ; word 0x00000000000000000000000000000000
    ; word 0x62636363626363636263636362636363
    ; word 0xAAFBFBFBAAFBFBFBAAFBFBFBAAFBFBFB
    ; word 0x6F6C6CCF0D0F0FAC6F6C6CCF0D0F0FAC
    ; word 0x7D8D8D6AD77676917D8D8D6AD7767691
    ; word 0x5354EDC15E5BE26D31378EA23C38810E
    ; word 0x968A81C141FCF7503C717A3AEB070CAB
    ; word 0x9EAA8F28C0F16D45F1C6E3E7CDFE62E9
    ; word 0x2B312BDF6ACDDC8F56BCA6B5BDBBAA1E
    ; word 0x6406FD52A4F79017553173F098CF1119
    ; word 0x6DBBA90B0776758451CAD331EC71792F
    ; word 0xE7B0E89C4347788B16760B7B8EB91A62
    ; word 0x74ED0BA1739B7E252251AD14CE20D43B
    ; word 0x10F80A1753BF729C45C979E7CB706385
    ]`;;

(* AES-256: key=0, pt=0 *)
prove(`aes256_cipher (word 0x00000000000000000000000000000000)
                     AESAVS_ZERO_KEY_256_SCHEDULE =
       word 0xdc95c078a2408989ad48a21492842087`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_CONV aes256_cipher
    AESAVS_ZERO_KEY_256_SCHEDULE)) THEN REFL_TAC);;

(* AESAVS GFSbox first vector: key=0, pt=014730f8... *)
prove(`aes256_cipher (word 0x014730f80ac625fe84f026c60bfd547d)
                     AESAVS_ZERO_KEY_256_SCHEDULE =
       word 0x5c9d844ed46f9885085e5d6a4f94c7d7`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_CONV aes256_cipher
    AESAVS_ZERO_KEY_256_SCHEDULE)) THEN REFL_TAC);;
