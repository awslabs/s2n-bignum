(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA Rejection uniform sampling (AVX2).                                 *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

needs "x86/proofs/mldsa_rej_uniform_table.ml";;

(*** print_literal_from_elf "x86/mldsa/mldsa_rej_uniform.o";;
 ***)

let mldsa_rej_uniform_mc = define_assert_from_elf
  "mldsa_rej_uniform_mc" "x86/mldsa/mldsa_rej_uniform.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x49; 0xba; 0x00; 0x01; 0x02; 0xff; 0x03; 0x04; 0x05; 0xff;
                           (* MOV (% r10) (Imm64 (word 18376098269764911360)) *)
  0xc4; 0xc1; 0xf9; 0x6e; 0xc2;
                           (* VMOVQ (%_% xmm0) (% r10) *)
  0x49; 0xba; 0x06; 0x07; 0x08; 0xff; 0x09; 0x0a; 0x0b; 0xff;
                           (* MOV (% r10) (Imm64 (word 18377793742465140486)) *)
  0xc4; 0xc3; 0xf9; 0x22; 0xc2; 0x01;
                           (* VPINSRQ (%_% xmm0) (%_% xmm0) (% r10) (Imm8 (word 1)) *)
  0x49; 0xba; 0x04; 0x05; 0x06; 0xff; 0x07; 0x08; 0x09; 0xff;
                           (* MOV (% r10) (Imm64 (word 18377228584898397444)) *)
  0xc4; 0xc1; 0xf9; 0x6e; 0xda;
                           (* VMOVQ (%_% xmm3) (% r10) *)
  0x49; 0xba; 0x0a; 0x0b; 0x0c; 0xff; 0x0d; 0x0e; 0x0f; 0xff;
                           (* MOV (% r10) (Imm64 (word 18378924057598626570)) *)
  0xc4; 0xc3; 0xe1; 0x22; 0xda; 0x01;
                           (* VPINSRQ (%_% xmm3) (%_% xmm3) (% r10) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x7d; 0x38; 0xc3; 0x01;
                           (* VINSERTI128 (%_% ymm0) (%_% ymm0) (%_% xmm3) (Imm8 (word 1)) *)
  0x41; 0xb8; 0xff; 0xff; 0x7f; 0x00;
                           (* MOV (% r8d) (Imm32 (word 8388607)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xc8;
                           (* VMOVD (%_% xmm1) (% r8d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0x41; 0xb8; 0x01; 0xe0; 0x7f; 0x00;
                           (* MOV (% r8d) (Imm32 (word 8380417)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xd0;
                           (* VMOVD (%_% xmm2) (% r8d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x77; 0x46;              (* JA (Imm8 (word 70)) *)
  0x81; 0xf9; 0x28; 0x03; 0x00; 0x00;
                           (* CMP (% ecx) (Imm32 (word 808)) *)
  0x77; 0x3e;              (* JA (Imm8 (word 62)) *)
  0xc5; 0xfe; 0x6f; 0x1c; 0x0e;
                           (* VMOVDQU (%_% ymm3) (Memop Word256 (%%% (rsi,0,rcx))) *)
  0x83; 0xc1; 0x18;        (* ADD (% ecx) (Imm8 (word 24)) *)
  0xc4; 0xe3; 0xfd; 0x00; 0xdb; 0x94;
                           (* VPERMQ (%_% ymm3) (%_% ymm3) (Imm8 (word 148)) *)
  0xc4; 0xe2; 0x65; 0x00; 0xd8;
                           (* VPSHUFB (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xe5; 0xdb; 0xd9;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0xfa; 0xe2;  (* VPSUBD (%_% ymm4) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0x7c; 0x50; 0xc4;  (* VMOVMSKPS (% r8d) (%_% ymm4) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xc8;
                           (* POPCNT (% r9d) (% r8d) *)
  0xc4; 0xa1; 0x7a; 0x7e; 0x24; 0xc2;
                           (* VMOVQ (%_% xmm4) (Memop Quadword (%%% (rdx,3,r8))) *)
  0xc4; 0xe2; 0x7d; 0x31; 0xe4;
                           (* VPMOVZXBD (%_% ymm4) (%_% xmm4) *)
  0xc4; 0xe2; 0x5d; 0x36; 0xdb;
                           (* VPERMD (%_% ymm3) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0xfe; 0x7f; 0x1c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm3) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0xeb; 0xb3;              (* JMP (Imm8 (word 179)) *)
  0x3d; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 256)) *)
  0x73; 0x36;              (* JAE (Imm8 (word 54)) *)
  0x81; 0xf9; 0x45; 0x03; 0x00; 0x00;
                           (* CMP (% ecx) (Imm32 (word 837)) *)
  0x77; 0x2e;              (* JA (Imm8 (word 46)) *)
  0x44; 0x0f; 0xb7; 0x04; 0x0e;
                           (* MOVZX (% r8d) (Memop Word (%%% (rsi,0,rcx))) *)
  0x44; 0x0f; 0xb6; 0x4c; 0x0e; 0x02;
                           (* MOVZX (% r9d) (Memop Byte (%%%% (rsi,0,rcx,&2))) *)
  0x41; 0xc1; 0xe1; 0x10;  (* SHL (% r9d) (Imm8 (word 16)) *)
  0x45; 0x09; 0xc8;        (* OR (% r8d) (% r9d) *)
  0x41; 0x81; 0xe0; 0xff; 0xff; 0x7f; 0x00;
                           (* AND (% r8d) (Imm32 (word 8388607)) *)
  0x83; 0xc1; 0x03;        (* ADD (% ecx) (Imm8 (word 3)) *)
  0x41; 0x81; 0xf8; 0x01; 0xe0; 0x7f; 0x00;
                           (* CMP (% r8d) (Imm32 (word 8380417)) *)
  0x73; 0xcc;              (* JAE (Imm8 (word 204)) *)
  0x44; 0x89; 0x04; 0x87;  (* MOV (Memop Doubleword (%%% (rdi,2,rax))) (% r8d) *)
  0x83; 0xc0; 0x01;        (* ADD (% eax) (Imm8 (word 1)) *)
  0xeb; 0xc3;              (* JMP (Imm8 (word 195)) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mldsa_rej_uniform_tmc =
  define_trimmed "mldsa_rej_uniform_tmc" mldsa_rej_uniform_mc;;

let MLDSA_REJ_UNIFORM_EXEC = X86_MK_CORE_EXEC_RULE mldsa_rej_uniform_tmc;;

(* ========================================================================= *)
(* Pre-helper lemmas (VPSUBD_SIGN_BIT_BOUNDED, SIGN_BIT_BITVAL).             *)
(* ========================================================================= *)

(* === Lemmas that helpers file depends on === *)

let VPSUBD_SIGN_BIT_BOUNDED = prove
 (`!x:int32. val x < 8388608
     ==> (bit 31 (word_sub x (word 8380417)) <=> val x < 8380417)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_VAL; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD_SUB; DIMINDEX_32; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `val(x:int32) < 8380417` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `(val(x:int32) + 4286586879) MOD 4294967296 = val x + 4286586879`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[ODD; ARITH_RULE `ODD 1`] `n = 1 ==> ODD n`) THEN
    MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC `val(x:int32) + 2139103231` THEN ASM_ARITH_TAC;
    REWRITE_TAC[NOT_ODD] THEN
    SUBGOAL_THEN
     `(val(x:int32) + 4286586879) MOD 4294967296 = val x - 8380417`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `val(x:int32) + 4286586879 = (val x - 8380417) + 1 * 4294967296`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[DIV_LT; EVEN] THEN ASM_ARITH_TAC]);;

let SIGN_BIT_BITVAL = prove
 (`!x0:int32. val x0 < 8388608
   ==> bitval(bit 31 (word_sub x0 (word 8380417):int32)) = bitval(val x0 < 8380417)`,
  GEN_TAC THEN DISCH_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[BIT_VAL; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD_SUB; DIMINDEX_32; VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `val(x0:int32) < 8380417` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(val(x0:int32) + 4286586879) MOD 4294967296 = val x0 + 4286586879` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[ODD; ARITH_RULE `ODD 1`] `n = 1 ==> ODD n`) THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `val(x0:int32) + 2139103231` THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `(val(x0:int32) + 4286586879) MOD 4294967296 = val x0 - 8380417` SUBST1_TAC THENL
     [SUBGOAL_THEN `val(x0:int32) + 4286586879 = (val x0 - 8380417) + 1 * 4294967296` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC];
      REWRITE_TAC[NOT_ODD] THEN SIMP_TAC[DIV_LT; EVEN] THEN ASM_ARITH_TAC]]);;

(* ========================================================================= *)
(* Helper lemmas.                                                            *)
(* ========================================================================= *)

(* Helper lemmas for mldsa_rej_uniform proof - VMOVMSKPS+POPCNT chain *)

(* word_popcount is preserved through word_zx *)
let WORD_POPCOUNT_WORD_ZX = prove
 (`!(w:N word). dimindex(:N) <= dimindex(:M) ==> word_popcount(word_zx w:M word) = word_popcount w`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_popcount] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; bits_of_word; BIT_WORD_ZX] THEN
  X_GEN_TAC `j:num` THEN EQ_TAC THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[BIT_TRIVIAL; NOT_LT; LTE_TRANS]);;

(* word_of_bits VMOVMSKPS pattern = sum of bitvals *)
let VMOVMSKPS_BYTE_EQ = prove
 (`!x:int256. word_of_bits(\i. i < 8 /\ bit(32*i+31) x):byte =
   word(bitval(bit 31 x) + 2 * bitval(bit 63 x) + 4 * bitval(bit 95 x) +
        8 * bitval(bit 127 x) + 16 * bitval(bit 159 x) + 32 * bitval(bit 191 x) +
        64 * bitval(bit 223 x) + 128 * bitval(bit 255 x))`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_OF_BITS_AS_WORD_ALT; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN AP_TERM_TAC THEN
  CONV_TAC(LAND_CONV EXPAND_NSUM_CONV) THEN
  REWRITE_TAC[IN] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* bit(32*k+31)(x:int256) = bit 31(word_subword x (32*k,32):int32) *)
let BIT_SUBWORD_256 = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!i. i < 8 ==>
    !x:int256. bit(32*i+31) x = bit 31 (word_subword x (32*i,32):int32)`,
  CONV_TAC WORD_BLAST);;

(* Combined: word_popcount of word_of_bits = word_popcount of bitval sum *)
let VMOVMSKPS_POPCOUNT_EQ = prove
 (`!x:int256.
   word_popcount(word_of_bits(\i. i < 8 /\ bit(32*i+31) x):byte) =
   word_popcount(word(
     bitval(bit 31 (word_subword x (0,32):int32)) +
     2 * bitval(bit 31 (word_subword x (32,32):int32)) +
     4 * bitval(bit 31 (word_subword x (64,32):int32)) +
     8 * bitval(bit 31 (word_subword x (96,32):int32)) +
     16 * bitval(bit 31 (word_subword x (128,32):int32)) +
     32 * bitval(bit 31 (word_subword x (160,32):int32)) +
     64 * bitval(bit 31 (word_subword x (192,32):int32)) +
     128 * bitval(bit 31 (word_subword x (224,32):int32))):byte)`,
  GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VMOVMSKPS_BYTE_EQ; BIT_SUBWORD_256]);;

(* Extract bit 31 from each lane of nested word_join of int32's *)
let BIT_NESTED_JOIN_8 = REWRITE_RULE[LET_DEF; LET_END_DEF] (prove
 (`!(a0:int32) (a1:int32) (a2:int32) (a3:int32) (a4:int32) (a5:int32) (a6:int32) (a7:int32).
   let x:int256 = word_join
     (word_join (word_join a7 a6:int64) (word_join a5 a4:int64):int128)
     (word_join (word_join a3 a2:int64) (word_join a1 a0:int64):int128) in
   bit 31 (word_subword x (0,32):int32) = bit 31 a0 /\
   bit 31 (word_subword x (32,32):int32) = bit 31 a1 /\
   bit 31 (word_subword x (64,32):int32) = bit 31 a2 /\
   bit 31 (word_subword x (96,32):int32) = bit 31 a3 /\
   bit 31 (word_subword x (128,32):int32) = bit 31 a4 /\
   bit 31 (word_subword x (160,32):int32) = bit 31 a5 /\
   bit 31 (word_subword x (192,32):int32) = bit 31 a6 /\
   bit 31 (word_subword x (224,32):int32) = bit 31 a7`,
  REPEAT GEN_TAC THEN CONV_TAC let_CONV THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_JOIN;
              DIMINDEX_32; DIMINDEX_64; DIMINDEX_128; DIMINDEX_256] THEN
  CONV_TAC NUM_REDUCE_CONV));;

(* Byte shuffle extraction: extracting 3 consecutive bytes + zero pad
   gives the 24-bit zero-extended coefficient.
   Low lane (coefficients 0-3 from 128-bit source): *)
let SHUFFLE_LOW_LANE = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!k. k < 4 ==>
    !x:int128.
      word_join (word 0:byte)
        (word_join (word_subword x (24*k+16, 8):byte)
          (word_join (word_subword x (24*k+8, 8):byte)
            (word_subword x (24*k, 8):byte):int16):24 word):int32 =
      word_zx(word_subword x (24*k, 24):24 word)`,
  CONV_TAC WORD_BLAST);;

(* High lane (coefficients 4-7, offset by 32 bits in 128-bit source): *)
let SHUFFLE_HIGH_LANE = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!k. k < 4 ==>
    !y:int128.
      word_join (word 0:byte)
        (word_join (word_subword y (24*k+32+16, 8):byte)
          (word_join (word_subword y (24*k+32+8, 8):byte)
            (word_subword y (24*k+32, 8):byte):int16):24 word):int32 =
      word_zx(word_subword y (24*k+32, 24):24 word)`,
  CONV_TAC WORD_BLAST);;

(* 3-byte word_join with zero high byte = word_zx of 24-bit join *)
let BYTE_JOIN_ZX = prove
 (`!b0 b1 b2:byte.
    word_join (word_join (word 0:byte) (b2:byte):int16)
              (word_join (b1:byte) (b0:byte):int16):int32 =
    word_zx(word_join (word_join (b2:byte) (b1:byte):int16) (b0:byte):24 word):int32`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* word_and with 0x7FFFFF mask on word_zx of 24-bit = word_zx of 23-bit subword *)
let BYTE_JOIN_SUBWORD_ZX = prove
 (`!b0 b1 b2:byte.
    word_and (word_zx(word_join (word_join (b2:byte) (b1:byte):int16) (b0:byte):24 word):int32)
             (word 8388607:int32) =
    word_zx(word_subword (word_join (word_join (b2:byte) (b1:byte):int16) (b0:byte):24 word) (0,23):23 word):int32`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Little-endian 3-byte decomposition of 24-bit words *)
let LITTLE_ENDIAN_3BYTES = prove
 (`!w:24 word. val(word_subword w (0,8):byte) +
               256 * val(word_subword w (8,8):byte) +
               65536 * val(word_subword w (16,8):byte) = val w`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Little-endian 3-byte reconstruction at num level *)
let BYTES3_NUM = prove
 (`!n. n MOD 256 + 256 * (n DIV 256) MOD 256 + 65536 * (n DIV 65536) MOD 256 = n MOD 16777216`,
  GEN_TAC THEN
  SUBGOAL_THEN `16777216 = 65536 * 256` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `65536 = 256 * 256` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV; MOD_MULT_MOD] THEN
  REWRITE_TAC[ARITH_RULE `256 * 256 * 256 = 256 * (256 * 256)`] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN
  MP_TAC(SPEC `256` (SPEC `n:num` DIVISION)) THEN
  MP_TAC(SPEC `256` (SPEC `n DIV 256` DIVISION)) THEN
  REWRITE_TAC[ARITH_RULE `~(256 = 0)`] THEN ARITH_TAC);;

(* val of 3-byte word_join *)
let BYTE_JOIN_VAL = prove
 (`!b0 b1 b2:byte.
    val(word_join (word_join (b2:byte) (b1:byte):int16) (b0:byte) : 24 word) =
    val b0 + 256 * val b1 + 65536 * val b2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_JOIN; DIMINDEX_8; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `256 * val(b2:byte) + val(b1:byte) < 65536`
    (fun th -> SIMP_TAC[th; MOD_LT]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `256 * (256 * val(b2:byte) + val(b1:byte)) + val(b0:byte) < 16777216`
    (fun th -> SIMP_TAC[th; MOD_LT]) THENL [ASM_ARITH_TAC; ARITH_TAC]);;

(* val of byte_join from word n : int256 = n DIV 2^ofs MOD 2^24 *)
let BYTE_JOIN_VAL_WORD = prove
 (`!n ofs.
    val(word_join (word_join (word_subword (word n:int256) (ofs+16,8):byte)
                             (word_subword (word n:int256) (ofs+8,8):byte):int16)
                  (word_subword (word n:int256) (ofs,8):byte) : 24 word) =
    (n MOD 2 EXP 256) DIV 2 EXP ofs MOD 2 EXP 24`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BYTE_JOIN_VAL; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`(n MOD 2 EXP 256) DIV 2 EXP ofs`, `m:num`) THEN
  REWRITE_TAC[BYTES3_NUM]);;

(* Full coefficient lemma: byte_join + 23-bit mask from word n = word(n DIV 2^ofs MOD 2^23) *)
let COEFF_BYTE_JOIN_WORD = prove
 (`!n ofs.
    word_zx(word_subword
      (word_join (word_join (word_subword (word n:int256) (ofs+16,8):byte)
                            (word_subword (word n:int256) (ofs+8,8):byte):int16)
                 (word_subword (word n:int256) (ofs,8):byte) : 24 word)
     (0,23) : 23 word) : int32 =
    word((n MOD 2 EXP 256) DIV 2 EXP ofs MOD 2 EXP 23)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_SUBWORD; VAL_WORD;
              DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BYTE_JOIN_VAL_WORD; DIV_1] THEN
  ONCE_REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 24`)] THEN
  ONCE_REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 23`)] THEN
  ONCE_REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 32`)] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Reduce MOD 2^256 to MOD 2^192 in DIV/MOD extraction context *)
let MOD_256_192 = prove
 (`!n k. k + 23 <= 192 ==>
    (n MOD 2 EXP 256) DIV (2 EXP k) MOD (2 EXP 23) =
    (n MOD 2 EXP 192) DIV (2 EXP k) MOD (2 EXP 23)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

(* word_popcount is preserved through word_zx *)
(* val(word n : 24 word) MOD 2^23 = n MOD 2^23 — avoids MOD_MOD_EXP_MIN loop *)
let VAL_WORD_24_MOD_23 = prove
 (`!n. val(word n : 24 word) MOD 2 EXP 23 = n MOD 2 EXP 23`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* MAP of REJ_SAMPLE coefficient extraction = concrete list *)
let MAP_REJ_COEFFS = prove
 (`!l:(24 word)list. LENGTH l = 8 ==>
   MAP (\x:24 word. word(val x MOD 2 EXP 23):int32) l =
   [word(num_of_wordlist l MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 24 MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 48 MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 72 MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 96 MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 120 MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 144 MOD 2 EXP 23);
    word(num_of_wordlist l DIV 2 EXP 168 MOD 2 EXP 23)]`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LIST_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
  REWRITE_TAC[LENGTH_MAP] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[EL_MAP; EL_NUM_OF_WORDLIST;
    ARITH_RULE `LENGTH l = 8 ==> (n < 8 ==> n < LENGTH l)`] THEN
  REWRITE_TAC[VAL_WORD_24_MOD_23] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[DIV_1]);;

(* NOTE: REJ_SAMPLE_COEFFS was moved to the main proof file because
   it depends on REJ_SAMPLE which is defined there, not in the helpers. *)

(* SUB_LIST(0, LENGTH l) l = l — needed for BYTES_EQ_NUM_OF_WORDLIST_APPEND *)
let SUB_LIST_0_LENGTH = prove
 (`!l:(A)list. SUB_LIST(0, LENGTH l) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_LIST_CLAUSES; LENGTH]);;

(* Memory bytes split: read(bytes(a, m+n)) = read(bytes(a,m)) + 2^(8m) * read(bytes(a+m, n)) *)
let MEMORY_BYTES_SPLIT = prove
 (`!a m n s. read (memory :> bytes (a:int64, m + n)) s =
             read (memory :> bytes (a, m)) s +
             2 EXP (8 * m) * read (memory :> bytes (word_add a (word m), n)) s`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE]);;

(* CMP_MASK_CORRECT: VMOVMSKPS(VPSUBD(coeffs, Q)) = bitval sum of (val c_k < Q).
   Connects the comparison mask byte to the FILTER predicate. *)
let CMP_MASK_CORRECT = prove(
 `!c0 c1 c2 c3 c4 c5 c6 c7:int32.
  val c0 < 8388608 /\ val c1 < 8388608 /\ val c2 < 8388608 /\
  val c3 < 8388608 /\ val c4 < 8388608 /\ val c5 < 8388608 /\
  val c6 < 8388608 /\ val c7 < 8388608 ==>
  val(word_zx(word_zx(word_of_bits
    (\i. i < 8 /\
     bit (32 * i + 31)
     (word_join
       (word_join
         (word_join
           (word_sub c7 (word 8380417):int32)
           (word_sub c6 (word 8380417):int32) : (64)word)
         (word_join
           (word_sub c5 (word 8380417):int32)
           (word_sub c4 (word 8380417):int32) : (64)word) : (128)word)
       (word_join
         (word_join
           (word_sub c3 (word 8380417):int32)
           (word_sub c2 (word 8380417):int32) : (64)word)
         (word_join
           (word_sub c1 (word 8380417):int32)
           (word_sub c0 (word 8380417):int32) : (64)word) : (128)word)
       :int256)) :byte) :int32) :int64) =
  bitval(val c0 < 8380417) + 2 * bitval(val c1 < 8380417) +
  4 * bitval(val c2 < 8380417) + 8 * bitval(val c3 < 8380417) +
  16 * bitval(val c4 < 8380417) + 32 * bitval(val c5 < 8380417) +
  64 * bitval(val c6 < 8380417) + 128 * bitval(val c7 < 8380417)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VMOVMSKPS_BYTE_EQ; BIT_SUBWORD_256] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ASM_SIMP_TAC[VPSUBD_SIGN_BIT_BOUNDED; SIGN_BIT_BITVAL] THEN
  REWRITE_TAC[bitval] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Pre-compute the 256 table entry values for VPERMD brute force.
   Each entry is an int64 value: 8 bytes from the table at offset 8*mask. *)
let TABLE_ENTRY_VALS =
  let table_expanded =
    (REWRITE_CONV[mldsa_rej_uniform_table; num_of_wordlist; DIMINDEX_8] THENC
     DEPTH_CONV WORD_NUM_RED_CONV THENC NUM_REDUCE_CONV)
    `num_of_wordlist mldsa_rej_uniform_table` in
  let table_num = rhs(concl table_expanded) in
  Printf.printf "  TABLE_ENTRY_VALS: computing 256 entries...\n%!";
  let entries = Array.init 256 (fun m ->
    let tm = mk_comb(mk_comb(`(MOD)`,
      mk_comb(mk_comb(`(DIV)`, table_num),
      mk_comb(mk_comb(`(EXP)`, `2`), mk_numeral(Num.num_of_int(64*m))))),
      mk_comb(mk_comb(`(EXP)`, `2`), `64`)) in
    let th = NUM_REDUCE_CONV tm in
    let rhs_val = rhs(concl th) in
    (* Prove: (num_of_wordlist table DIV 2^(64*m)) MOD 2^64 = entry_m *)
    let lhs_tm = mk_comb(mk_comb(`(MOD)`,
      mk_comb(mk_comb(`(DIV)`,
        `num_of_wordlist mldsa_rej_uniform_table`),
      mk_comb(mk_comb(`(EXP)`, `2`), mk_numeral(Num.num_of_int(64*m))))),
      mk_comb(mk_comb(`(EXP)`, `2`), `64`)) in
    let eq = mk_eq(lhs_tm, rhs_val) in
    EQT_ELIM((REWRITE_CONV[table_expanded] THENC NUM_REDUCE_CONV) eq)) in
  Printf.printf "  TABLE_ENTRY_VALS: done (%d entries)\n%!" (Array.length entries);
  entries;;

(* TABLE_ENTRY_FROM_MEMORY: connect bytes64 memory read at table+8k to
   (table_num DIV 2^(64k)) MOD 2^64 via bigdigit/bignum_from_memory *)
let TABLE_ENTRY_FROM_MEMORY = prove(
  `!table (s:x86state) k.
   read(memory :> bytes(table:int64, 2048)) s =
     num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
   k < 256
   ==> val(read(memory :> bytes64(word_add table (word(8 * k)))) s :int64) =
       (num_of_wordlist mldsa_rej_uniform_table DIV 2 EXP (64 * k)) MOD 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`256`; `table:int64`; `s:x86state`; `k:num`]
    BIGDIGIT_BIGNUM_FROM_MEMORY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[bigdigit] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

(* TABLE_NUM_THM: expand mldsa_rej_uniform_table to a numeral for table lookup *)
let TABLE_NUM_THM =
  (REWRITE_CONV[mldsa_rej_uniform_table; num_of_wordlist; DIMINDEX_8] THENC
   DEPTH_CONV WORD_NUM_RED_CONV THENC NUM_REDUCE_CONV)
  `num_of_wordlist mldsa_rej_uniform_table`;;

(* VAL_WORD_GALOIS_64: derive x = word n from val x = n *)
let VAL_WORD_GALOIS_64 = prove(
  `!x:int64 n. val x = n /\ n < 18446744073709551616 ==> x = word n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x:int64 = word(val x)` SUBST1_TAC THENL
  [REWRITE_TAC[WORD_VAL]; ASM_REWRITE_TAC[]]);;

(* VAL_WORD_JOIN8: flatten nested val(word_join^8) to sum of 2^(32*k) * val(ck) *)
let VAL_WORD_JOIN8 = prove(
  `!(c0:int32)(c1:int32)(c2:int32)(c3:int32)(c4:int32)(c5:int32)(c6:int32)(c7:int32).
   val(word_join
     (word_join (word_join c7 c6:(64)word) (word_join c5 c4:(64)word):(128)word)
     (word_join (word_join c3 c2:(64)word) (word_join c1 c0:(64)word):(128)word)
     :int256) =
   val c0 + 2 EXP 32 * val c1 + 2 EXP 64 * val c2 + 2 EXP 96 * val c3 +
   2 EXP 128 * val c4 + 2 EXP 160 * val c5 + 2 EXP 192 * val c6 + 2 EXP 224 * val c7`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_JOIN; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun c -> MP_TAC(ISPEC c VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV) [`c0:int32`;`c1:int32`;`c2:int32`;`c3:int32`;
    `c4:int32`;`c5:int32`;`c6:int32`;`c7:int32`] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `4294967296 * val(c1:int32) + val(c0:int32) < 18446744073709551616`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4294967296 * val(c3:int32) + val(c2:int32) < 18446744073709551616`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4294967296 * val(c5:int32) + val(c4:int32) < 18446744073709551616`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `4294967296 * val(c7:int32) + val(c6:int32) < 18446744073709551616`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `18446744073709551616 * (4294967296 * val(c3:int32) + val(c2:int32)) +
    (4294967296 * val(c1:int32) + val(c0:int32)) <
    340282366920938463463374607431768211456`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `18446744073709551616 * (4294967296 * val(c7:int32) + val(c6:int32)) +
    (4294967296 * val(c5:int32) + val(c4:int32)) <
    340282366920938463463374607431768211456`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `340282366920938463463374607431768211456 *
    (18446744073709551616 * (4294967296 * val(c7:int32) + val(c6:int32)) +
     (4294967296 * val(c5:int32) + val(c4:int32))) +
    (18446744073709551616 * (4294967296 * val(c3:int32) + val(c2:int32)) +
     (4294967296 * val(c1:int32) + val(c0:int32))) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936`
    (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ARITH_TAC);;

(* MOD_BASE_REWRITES: convert numeral MOD bases to symbolic 2 EXP k *)
let MOD_BASE_REWRITES = [
  GSYM(NUM_REDUCE_CONV `2 EXP 32`);
  GSYM(NUM_REDUCE_CONV `2 EXP 64`);
  GSYM(NUM_REDUCE_CONV `2 EXP 96`);
  GSYM(NUM_REDUCE_CONV `2 EXP 128`);
  GSYM(NUM_REDUCE_CONV `2 EXP 160`);
  GSYM(NUM_REDUCE_CONV `2 EXP 192`);
  GSYM(NUM_REDUCE_CONV `2 EXP 224`);
  GSYM(NUM_REDUCE_CONV `2 EXP 256`)];;

(* VAL_BOUND_256: val(x:int256) < 2 EXP 256 *)
let VAL_BOUND_256 = prove(
  `!x:int256. val x < 2 EXP 256`,
  GEN_TAC THEN MP_TAC(ISPEC `x:int256` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_256]);;

(* Factor rules for MOD stripping: rewrite 2^k * x to (2^(k-m) * x) * 2^m *)
let vpermd_factor_for m = List.filter_map (fun k ->
  if k >= m && k <= 224 then
    let two_exp j = mk_comb(mk_comb(`EXP`,`2`),mk_numeral(Num.num_of_int j)) in
    let mul_tm = `( * )` in
    let mk_mul a b = mk_comb(mk_comb(mul_tm,a),b) in
    Some(ARITH_RULE(mk_eq(
      mk_mul (two_exp k) `x:num`,
      mk_mul (mk_mul (two_exp (k-m)) `x:num`) (two_exp m))))
  else None)
  [32;64;96;128;160;192;224];;

let VPERMD_FACTOR_RULES = List.map (fun m -> (m, vpermd_factor_for m))
  [32;64;96;128;160;192;224];;

(* VPERMD_FACTOR_STRIP_TAC: detect MOD base, apply factor rules, strip, MOD_LT *)
let VPERMD_FACTOR_STRIP_TAC : tactic = fun (asl, w) ->
  let base = try
    let mod_term = rand(lhand w) in
    Num.int_of_num(dest_numeral(rand mod_term))
  with _ -> 0 in
  let gk = try List.assoc base VPERMD_FACTOR_RULES with Not_found -> [] in
  (if gk = [] then ALL_TAC
   else
     REWRITE_TAC gk THEN
     TRY(ONCE_REWRITE_TAC[ARITH_RULE `a+b+c+d+e+f+g+h = (a+b+c+d+e+f+g)+h`] THEN REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(ONCE_REWRITE_TAC[ARITH_RULE `a+b+c+d+e+f+g = (a+b+c+d+e+f)+g`] THEN REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(ONCE_REWRITE_TAC[ARITH_RULE `a+b+c+d+e+f = (a+b+c+d+e)+f`] THEN REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(ONCE_REWRITE_TAC[ARITH_RULE `a+b+c+d+e = (a+b+c+d)+e`] THEN REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(ONCE_REWRITE_TAC[ARITH_RULE `a+b+c+d = (a+b+c)+d`] THEN REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(ONCE_REWRITE_TAC[ARITH_RULE `a+b+c = (a+b)+c`] THEN REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(REWRITE_TAC[MOD_MULT_ADD]) THEN
     TRY(MATCH_MP_TAC MOD_LT THEN
         REWRITE_TAC[MULT_CLAUSES] THEN
         RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_32]) THEN ASM_ARITH_TAC))
  (asl, w);;

(* VPERMD_TABLE_CORRECT: 256-case brute force proof that VPERMD with the mldsa
   table correctly compacts coefficients matching FILTER.
   Preconditions: 8 coefficients bounded < 2^23, table entry for the mask.
   Conclusion: val(VPERMD result) MOD 2^(32*popcount) = num_of_wordlist(FILTER ...) *)
let VPERMD_TABLE_CORRECT = time prove(
  `!(c0:int32) (c1:int32) (c2:int32) (c3:int32) (c4:int32) (c5:int32) (c6:int32) (c7:int32) (te:int64).
   val c0 < 8388608 /\ val c1 < 8388608 /\ val c2 < 8388608 /\ val c3 < 8388608 /\
   val c4 < 8388608 /\ val c5 < 8388608 /\ val c6 < 8388608 /\ val c7 < 8388608 /\
   val te = (num_of_wordlist mldsa_rej_uniform_table DIV
     2 EXP (64 * (bitval(val c0 < 8380417) + 2 * bitval(val c1 < 8380417) +
     4 * bitval(val c2 < 8380417) + 8 * bitval(val c3 < 8380417) +
     16 * bitval(val c4 < 8380417) + 32 * bitval(val c5 < 8380417) +
     64 * bitval(val c6 < 8380417) + 128 * bitval(val c7 < 8380417))))
     MOD 2 EXP 64
   ==>
   let coeffs = word_join
     (word_join (word_join c7 c6 :(64)word) (word_join c5 c4 :(64)word) :(128)word)
     (word_join (word_join c3 c2 :(64)word) (word_join c1 c0 :(64)word) :(128)word) :int256 in
   let ix = word_join
     (word_join (word_join (word_zx(word_subword te (56,8):byte):int32)
                           (word_zx(word_subword te (48,8):byte):int32) :(64)word)
               (word_join (word_zx(word_subword te (40,8):byte):int32)
                          (word_zx(word_subword te (32,8):byte):int32) :(64)word) :(128)word)
     (word_join (word_join (word_zx(word_subword te (24,8):byte):int32)
                           (word_zx(word_subword te (16,8):byte):int32) :(64)word)
               (word_join (word_zx(word_subword te (8,8):byte):int32)
                          (word_zx(word_subword te (0,8):byte):int32) :(64)word) :(128)word) :int256 in
   let res = word_join
     (word_join (word_join (word_subword coeffs (32 * val(word_subword ix (224,3):(3)word), 32) :int32)
                           (word_subword coeffs (32 * val(word_subword ix (192,3):(3)word), 32) :int32) :(64)word)
               (word_join (word_subword coeffs (32 * val(word_subword ix (160,3):(3)word), 32) :int32)
                          (word_subword coeffs (32 * val(word_subword ix (128,3):(3)word), 32) :int32) :(64)word) :(128)word)
     (word_join (word_join (word_subword coeffs (32 * val(word_subword ix (96,3):(3)word), 32) :int32)
                           (word_subword coeffs (32 * val(word_subword ix (64,3):(3)word), 32) :int32) :(64)word)
               (word_join (word_subword coeffs (32 * val(word_subword ix (32,3):(3)word), 32) :int32)
                          (word_subword coeffs (32 * val(word_subword ix (0,3):(3)word), 32) :int32) :(64)word) :(128)word) :int256 in
   val res MOD 2 EXP (32 * (bitval(val c0 < 8380417) + bitval(val c1 < 8380417) +
     bitval(val c2 < 8380417) + bitval(val c3 < 8380417) +
     bitval(val c4 < 8380417) + bitval(val c5 < 8380417) +
     bitval(val c6 < 8380417) + bitval(val c7 < 8380417))) =
   num_of_wordlist(FILTER (\c:int32. val c < 8380417) [c0;c1;c2;c3;c4;c5;c6;c7])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_X_ASSUM MP_TAC THEN
  MAP_EVERY ASM_CASES_TAC
    [`val(c0:int32) < 8380417`; `val(c1:int32) < 8380417`;
     `val(c2:int32) < 8380417`; `val(c3:int32) < 8380417`;
     `val(c4:int32) < 8380417`; `val(c5:int32) < 8380417`;
     `val(c6:int32) < 8380417`; `val(c7:int32) < 8380417`] THEN
  ASM_REWRITE_TAC[bitval] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(REWRITE_CONV[TABLE_NUM_THM] THENC NUM_REDUCE_CONV))) THEN
  DISCH_THEN(fun th ->
    let n = rhs(concl th) in
    SUBST_ALL_TAC(MATCH_MP VAL_WORD_GALOIS_64
      (CONJ th (EQT_ELIM(NUM_REDUCE_CONV(mk_comb(mk_comb(`(<)`,n), `18446744073709551616`))))))) THEN
  CONV_TAC(DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[FILTER] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  TRY(REWRITE_TAC[MOD_1; num_of_wordlist] THEN REFL_TAC) THEN
  REWRITE_TAC MOD_BASE_REWRITES THEN
  TRY(SIMP_TAC[MOD_LT; VAL_BOUND_256]) THEN
  REWRITE_TAC[VAL_WORD_JOIN8] THEN
  CONV_TAC(RAND_CONV(REWRITE_CONV[num_of_wordlist; ADD_0; DIMINDEX_32;
    LEFT_ADD_DISTRIB; MULT_CLAUSES; MULT_ASSOC; GSYM(SPEC `2` EXP_ADD)] THENC
    DEPTH_CONV NUM_ADD_CONV)) THEN
  TRY REFL_TAC THEN
  VPERMD_FACTOR_STRIP_TAC);;

(* RESOLVE_TABLE_READ_TAC: resolve read(bytes64(word_add table (word K))) terms
   in the goal using TABLE_ENTRY_FROM_MEMORY + the memory-table hypothesis *)
let RESOLVE_TABLE_READ_TAC : tactic = fun (asl,w) ->
  let mem_hyps = List.filter_map (fun (_,th) ->
    if is_eq(concl th) &&
       (try let c = string_of_term(concl th) in
        let _ = String.index c '2' in
        String.length c > 60 &&
        can (find_term (fun t -> try fst(dest_const t) = "num_of_wordlist" with _ -> false)) (concl th) &&
        can (find_term (fun t -> try dest_numeral t = Num.num_of_int 2048 with _ -> false)) (concl th)
        with _ -> false)
    then Some th else None) asl in
  if mem_hyps = [] then ALL_TAC (asl,w) else
  let reads = find_terms (fun t ->
    try let _ = find_term (fun s -> try fst(dest_const s) = "bytes64" with _ -> false) t in
        let _ = find_term (fun s -> try fst(dest_const s) = "word_add" with _ -> false) t in
        fst(dest_const(fst(strip_comb t))) = "read" &&
        is_comb t && is_var(rand t)
    with _ -> false) w in
  let eqs = List.filter_map (fun rd ->
    try
      let state = rand rd in
      (* rd = read (memory :> bytes64(word_add table (word K))) sNN
         rator rd = read (memory :> bytes64(word_add table (word K)))
         rand(rator rd) = memory :> bytes64(word_add table (word K))
         rand(rand(rator rd)) = bytes64(word_add table (word K))
         rand(rand(rand(rator rd))) = word_add table (word K) *)
      let word_add_tm = rand(rand(rand(rator rd))) in
      let k_tm = rand(rand word_add_tm) in  (* K : num *)
      let k = Num.int_of_num(dest_numeral k_tm) in
      let mask = k / 8 in
      let table_var = rand(rator word_add_tm) in
      (* Find memory hypothesis for this state *)
      let mem_th = try List.find (fun th ->
        try rand(rator(lhs(concl th))) = state with _ -> false) mem_hyps
        with Not_found -> List.hd mem_hyps in
      let spec = SPECL [table_var; state; mk_numeral(Num.num_of_int mask)]
        TABLE_ENTRY_FROM_MEMORY in
      let prem_th = CONJ mem_th
        (EQT_ELIM(NUM_REDUCE_CONV(mk_comb(mk_comb(`(<)`,mk_numeral(Num.num_of_int mask)), `256`)))) in
      let val_eq = MP spec prem_th in
      let val_eq' = CONV_RULE(RAND_CONV(REWRITE_CONV[TABLE_NUM_THM] THENC NUM_REDUCE_CONV)) val_eq in
      (* Also reduce 8*mask in the LHS to match the goal's concrete address *)
      let val_eq'' = CONV_RULE(LAND_CONV(DEPTH_CONV NUM_REDUCE_CONV)) val_eq' in
      let n = rhs(concl val_eq'') in
      Some(MATCH_MP VAL_WORD_GALOIS_64
        (CONJ val_eq'' (EQT_ELIM(NUM_REDUCE_CONV
          (mk_comb(mk_comb(`(<)`,n), `18446744073709551616`))))))
    with _ -> None) reads in
  if eqs = [] then ALL_TAC (asl,w)
  else REWRITE_TAC eqs (asl,w);;

(* VPERMD_MEMORY_BRIDGE: connect a sub-read of the 32-byte VMOVDQU write
   region to the VPERMD MOD result, closing the memory store goal. *)
let VPERMD_MEMORY_BRIDGE = prove
 (`!a (s:x86state) vr n l.
    read(memory :> bytes(a:int64, 32)) s = vr /\
    vr MOD 2 EXP (32 * n) = num_of_wordlist(l:int32 list) /\
    n <= 8
    ==> read(memory :> bytes(a, 4 * n)) s = num_of_wordlist l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `read(memory :> bytes(a:int64, 4 * n)) s =
     read(memory :> bytes(a, 32)) s MOD 2 EXP (8 * (4 * n))`
  SUBST1_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [GSYM(NUM_REDUCE_CONV `8 * 32`)] THEN
    REWRITE_TAC[READ_BYTES_MOD] THEN
    SUBGOAL_THEN `MIN 32 (4 * n) = 4 * n` SUBST1_TAC THENL
     [REWRITE_TAC[MIN] THEN ASM_ARITH_TAC;
      REFL_TAC];
    ASM_REWRITE_TAC[ARITH_RULE `8 * 4 * n = 32 * n`]]);;

(* VAL_READ_BYTES256: val(read(bytes256 addr) s) = read(bytes(addr,32)) s
   Converts a 256-bit word read to a numeric bytes read. *)
let VAL_READ_BYTES256 = prove(
  `!addr (s:(int64->byte)).
    val(read(bytes256 addr) s :int256) = read(bytes(addr,32)) s`,
  REWRITE_TAC[BYTES256_WBYTES; VAL_READ_WBYTES; DIMINDEX_256] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ========================================================================= *)
(* Post-helper lemmas.                                                       *)
(* ========================================================================= *)

(* Remaining helper lemmas from the proof file *)

let DIMINDEX_23 = DIMINDEX_CONV `dimindex(:23)`;;
let DIMINDEX_24 = DIMINDEX_CONV `dimindex(:24)`;;

let VAL_MOD_23_EQ_AND = prove
 (`!w:24 word. (word(val w MOD 2 EXP 23):int32) =
               word_and (word_zx w:int32) (word 8388607)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let REJ_SAMPLE = define
 `REJ_SAMPLE l = FILTER (\x:int32. val x < 8380417)
    (MAP (\x:24 word. word(val x MOD 2 EXP 23):int32) l)`;;

let REJ_SAMPLE_EMPTY = prove
 (`REJ_SAMPLE [] = []`,
  REWRITE_TAC[REJ_SAMPLE; FILTER; MAP]);;

let REJ_SAMPLE_APPEND = prove
 (`!l1 l2. REJ_SAMPLE(APPEND l1 l2) =
           APPEND (REJ_SAMPLE l1) (REJ_SAMPLE l2)`,
  REWRITE_TAC[REJ_SAMPLE; MAP_APPEND; FILTER_APPEND]);;

let mldsa_mask_lemma = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!i. i < 8
       ==> word_and (word_subword (q:int256) (32*i,32)) (word 8388607):int32 =
           word_zx(word_subword (q:int256) (32*i,23):23 word)`,
  CONV_TAC WORD_BLAST);;

let VAL_WORD_ZX_23 = prove
 (`!w:23 word. val(word_zx w:int32) < 8388608`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_23; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `w:23 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_23] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val(w:23 word) MOD 4294967296 = val w` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let ODD_ADD_2 = prove
 (`!n. ODD(2 + n) <=> ODD n`,
  REWRITE_TAC[ODD_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

let COEFF_FROM_BYTES = prove
 ((rand o concl o (EXPAND_CASES_CONV THENC NUM_REDUCE_CONV))
  `!j. j < 8 ==>
    word_and (word_zx(word_subword (buf:192 word) (24*j,24):24 word):int32)
             (word 8388607) =
    word_zx(word_subword (buf:192 word) (24*j,23):23 word)`,
  CONV_TAC WORD_BLAST);;


(* ========================================================================= *)
(* REJ_SAMPLE algebra.                                                       *)
(* ========================================================================= *)

(* Lemmas that defs.ml / step*.ml need but which weren't in the checkpoint loader.
   Extracted verbatim from mldsa_rej_uniform.ml. Load before defs.ml. *)

(* POPCNT of VMOVMSKPS sign-bit mask = LENGTH(FILTER) — 256-case brute force *)
let POPCNT_EQ_LENGTH_FILTER = prove
 (`!x0 x1 x2 x3 x4 x5 x6 x7:int32.
   val x0 < 8388608 /\ val x1 < 8388608 /\ val x2 < 8388608 /\ val x3 < 8388608 /\
   val x4 < 8388608 /\ val x5 < 8388608 /\ val x6 < 8388608 /\ val x7 < 8388608
   ==> word_popcount(word(
         bitval(bit 31 (word_sub x0 (word 8380417):int32)) +
         2 * bitval(bit 31 (word_sub x1 (word 8380417):int32)) +
         4 * bitval(bit 31 (word_sub x2 (word 8380417):int32)) +
         8 * bitval(bit 31 (word_sub x3 (word 8380417):int32)) +
         16 * bitval(bit 31 (word_sub x4 (word 8380417):int32)) +
         32 * bitval(bit 31 (word_sub x5 (word 8380417):int32)) +
         64 * bitval(bit 31 (word_sub x6 (word 8380417):int32)) +
         128 * bitval(bit 31 (word_sub x7 (word 8380417):int32))):byte) =
       LENGTH(FILTER (\x:int32. val x < 8380417) [x0;x1;x2;x3;x4;x5;x6;x7])`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    try let th' = MATCH_MP SIGN_BIT_BITVAL th in REWRITE_TAC[th'] with _ -> ASSUME_TAC th)) THEN
  MAP_EVERY ASM_CASES_TAC
   [`val(x0:int32) < 8380417`; `val(x1:int32) < 8380417`;
    `val(x2:int32) < 8380417`; `val(x3:int32) < 8380417`;
    `val(x4:int32) < 8380417`; `val(x5:int32) < 8380417`;
    `val(x6:int32) < 8380417`; `val(x7:int32) < 8380417`] THEN
  ASM_REWRITE_TAC[FILTER; bitval; LENGTH] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

(* LENGTH(FILTER) = sum of bitvals — the 256-case brute force *)
let FILTER_LENGTH_8 = prove
 (`!x0 x1 x2 x3 x4 x5 x6 x7:int32.
   val x0 < 8388608 /\ val x1 < 8388608 /\ val x2 < 8388608 /\ val x3 < 8388608 /\
   val x4 < 8388608 /\ val x5 < 8388608 /\ val x6 < 8388608 /\ val x7 < 8388608
   ==> LENGTH(FILTER (\x. val x < 8380417) [x0;x1;x2;x3;x4;x5;x6;x7]) =
       bitval(val x0 < 8380417) + bitval(val x1 < 8380417) +
       bitval(val x2 < 8380417) + bitval(val x3 < 8380417) +
       bitval(val x4 < 8380417) + bitval(val x5 < 8380417) +
       bitval(val x6 < 8380417) + bitval(val x7 < 8380417)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`val(x0:int32) < 8380417`; `val(x1:int32) < 8380417`;
    `val(x2:int32) < 8380417`; `val(x3:int32) < 8380417`;
    `val(x4:int32) < 8380417`; `val(x5:int32) < 8380417`;
    `val(x6:int32) < 8380417`; `val(x7:int32) < 8380417`] THEN
  ASM_REWRITE_TAC[FILTER; LENGTH; bitval] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* VMOVMSKPS sign bits + POPCNT = LENGTH(FILTER) for 8 dword lanes *)
let POPCNT_VMOVMSKPS_LEMMA = prove
 (`!q:int256.
  word_popcount(word(
    bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (0,32):int32) (word 8380417):int32)) +
    2 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (32,32):int32) (word 8380417):int32)) +
    4 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (64,32):int32) (word 8380417):int32)) +
    8 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (96,32):int32) (word 8380417):int32)) +
    16 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (128,32):int32) (word 8380417):int32)) +
    32 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (160,32):int32) (word 8380417):int32)) +
    64 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (192,32):int32) (word 8380417):int32)) +
    128 * bitval(bit 31 (word_sub (word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (224,32):int32) (word 8380417):int32))):byte) =
  LENGTH(FILTER (\c:int32. val c < 8380417)
    [word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (0,32):int32;
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (32,32);
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (64,32);
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (96,32);
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (128,32);
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (160,32);
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (192,32);
     word_subword (word_and q (word 226156397384342666605459106258636701594091082888230722833791023177481060351):int256) (224,32)])`,
  GEN_TAC THEN REWRITE_TAC[WORD_SUBWORD_AND] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[mldsa_mask_lemma] THEN
  MATCH_MP_TAC POPCNT_EQ_LENGTH_FILTER THEN
  REWRITE_TAC[VAL_WORD_ZX_23]);;

(* REJ_SAMPLE splits across a single 8-coefficient iteration *)
let REJ_SAMPLE_ITERATION = prove
 (`!inlist i.
    8 * (i + 1) <= LENGTH inlist
    ==> REJ_SAMPLE(SUB_LIST(0,8*(i+1)) inlist) =
        APPEND (REJ_SAMPLE(SUB_LIST(0,8*i) inlist))
               (REJ_SAMPLE(SUB_LIST(8*i,8) inlist))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `8*(i+1) = 8*i + 8`] THEN
  MP_TAC(ISPECL [`inlist:(24 word)list`; `8 * i`; `8`; `0`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REJ_SAMPLE_APPEND]);;

(* Full iteration bridge: split, length, and bound *)
let SIMD_ITERATION_BRIDGE = prove
 (`!inlist:(24 word)list i curlist curlen.
    REJ_SAMPLE(SUB_LIST(0,8*i) inlist) = curlist /\
    LENGTH curlist = curlen /\
    8*(i+1) <= LENGTH inlist
    ==> REJ_SAMPLE(SUB_LIST(0,8*(i+1)) inlist) =
        APPEND curlist (REJ_SAMPLE(SUB_LIST(8*i,8) inlist)) /\
        LENGTH(REJ_SAMPLE(SUB_LIST(0,8*(i+1)) inlist)) =
        curlen + LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) inlist)) /\
        LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) inlist)) <= 8`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8*(i+1) = 8*i + 8`] THEN
    MP_TAC(ISPECL [`inlist:(24 word)list`; `8*i`; `8`; `0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[REJ_SAMPLE_APPEND];
    REWRITE_TAC[ARITH_RULE `8*(i+1) = 8*i + 8`] THEN
    MP_TAC(ISPECL [`inlist:(24 word)list`; `8*i`; `8`; `0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[REJ_SAMPLE_APPEND; LENGTH_APPEND];
    REWRITE_TAC[REJ_SAMPLE] THEN
    W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN ARITH_TAC]);;

(* word_join of 8 consecutive 32-bit subwords reconstructs the original 256-bit word.
   Used by the VPERMD bridge to fold the VPERMD expression back to coeffs_ymm3. *)
let WORD_JOIN_SUBWORDS_256 = prove
 (`!q:int256.
    word_join
     (word_join (word_join ((word_subword q (224,32)):int32) ((word_subword q (192,32)):int32):int64)
                (word_join ((word_subword q (160,32)):int32) ((word_subword q (128,32)):int32):int64):int128)
     (word_join (word_join ((word_subword q (96,32)):int32) ((word_subword q (64,32)):int32):int64)
                (word_join ((word_subword q (32,32)):int32) ((word_subword q (0,32)):int32):int64):int128):int256 = q`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Standalone VPERMD bridge: given 8 bounds on subwords of q and the table lookup
   value of te, the VPERMD expansion of (q, te) mod 2^(32*popcount) equals
   num_of_wordlist(FILTER (val<Q) [subwords]).
   Packages VPERMD_TABLE_CORRECT + WORD_JOIN_SUBWORDS_256 into one MP_TAC-able form
   that eliminates the 256-case brute force (255 CHEATs) in the main proof. *)
let MLDSA_VPERMD_BRIDGE = prove
 (`!(q:int256) (te:int64).
     val(word_subword q (0,32):int32) < 8388608 /\
     val(word_subword q (32,32):int32) < 8388608 /\
     val(word_subword q (64,32):int32) < 8388608 /\
     val(word_subword q (96,32):int32) < 8388608 /\
     val(word_subword q (128,32):int32) < 8388608 /\
     val(word_subword q (160,32):int32) < 8388608 /\
     val(word_subword q (192,32):int32) < 8388608 /\
     val(word_subword q (224,32):int32) < 8388608 /\
     val te = (num_of_wordlist mldsa_rej_uniform_table DIV
       2 EXP (64 * (bitval(val(word_subword q (0,32):int32) < 8380417) +
                    2 * bitval(val(word_subword q (32,32):int32) < 8380417) +
                    4 * bitval(val(word_subword q (64,32):int32) < 8380417) +
                    8 * bitval(val(word_subword q (96,32):int32) < 8380417) +
                    16 * bitval(val(word_subword q (128,32):int32) < 8380417) +
                    32 * bitval(val(word_subword q (160,32):int32) < 8380417) +
                    64 * bitval(val(word_subword q (192,32):int32) < 8380417) +
                    128 * bitval(val(word_subword q (224,32):int32) < 8380417))))
       MOD 2 EXP 64
     ==>
     val(word_join
           (word_join
             (word_join ((word_subword q (32 * val(word_subword te (56,3):3 word), 32)):int32)
                        ((word_subword q (32 * val(word_subword te (48,3):3 word), 32)):int32):int64)
             (word_join ((word_subword q (32 * val(word_subword te (40,3):3 word), 32)):int32)
                        ((word_subword q (32 * val(word_subword te (32,3):3 word), 32)):int32):int64):int128)
           (word_join
             (word_join ((word_subword q (32 * val(word_subword te (24,3):3 word), 32)):int32)
                        ((word_subword q (32 * val(word_subword te (16,3):3 word), 32)):int32):int64)
             (word_join ((word_subword q (32 * val(word_subword te (8,3):3 word), 32)):int32)
                        ((word_subword q (32 * val(word_subword te (0,3):3 word), 32)):int32):int64):int128):int256) MOD
     2 EXP (32 * (bitval(val(word_subword q (0,32):int32) < 8380417) +
                  bitval(val(word_subword q (32,32):int32) < 8380417) +
                  bitval(val(word_subword q (64,32):int32) < 8380417) +
                  bitval(val(word_subword q (96,32):int32) < 8380417) +
                  bitval(val(word_subword q (128,32):int32) < 8380417) +
                  bitval(val(word_subword q (160,32):int32) < 8380417) +
                  bitval(val(word_subword q (192,32):int32) < 8380417) +
                  bitval(val(word_subword q (224,32):int32) < 8380417))) =
     num_of_wordlist(FILTER (\c:int32. val c < 8380417)
       [word_subword q (0,32); word_subword q (32,32);
        word_subword q (64,32); word_subword q (96,32);
        word_subword q (128,32); word_subword q (160,32);
        word_subword q (192,32); word_subword q (224,32)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [
    `word_subword (q:int256) (0,32):int32`;
    `word_subword (q:int256) (32,32):int32`;
    `word_subword (q:int256) (64,32):int32`;
    `word_subword (q:int256) (96,32):int32`;
    `word_subword (q:int256) (128,32):int32`;
    `word_subword (q:int256) (160,32):int32`;
    `word_subword (q:int256) (192,32):int32`;
    `word_subword (q:int256) (224,32):int32`;
    `te:int64`
  ] VPERMD_TABLE_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_JOIN_SUBWORDS_256] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  DISCH_THEN ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* REJ_SAMPLE list decomposition helpers for the post-loop proof.            *)
(* ------------------------------------------------------------------------- *)

(* REJ_SAMPLE of a list is APPEND of REJ_SAMPLE of a prefix and a suffix. *)
let REJ_SAMPLE_SPLIT = prove
 (`!(l:(24 word)list) n.
    REJ_SAMPLE l = APPEND (REJ_SAMPLE (SUB_LIST (0,n) l))
                          (REJ_SAMPLE (SUB_LIST (n, LENGTH l - n) l))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REJ_SAMPLE_APPEND] THEN
  MESON_TAC[SUB_LIST_TOPSPLIT]);;

(* If a prefix's REJ_SAMPLE has length 256, then the first 256 of REJ_SAMPLE
   of the full list equals REJ_SAMPLE of that prefix. Used in the post-loop
   JAE-exit case to conclude outlist = SUB_LIST (0,256) (REJ_SAMPLE inlist). *)
let REJ_SAMPLE_PREFIX_256 = prove
 (`!(inlist:(24 word)list) k.
    LENGTH (REJ_SAMPLE (SUB_LIST (0,k) inlist)) = 256
    ==> SUB_LIST (0,256) (REJ_SAMPLE inlist) = REJ_SAMPLE (SUB_LIST (0,k) inlist)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inlist:(24 word)list`; `k:num`] REJ_SAMPLE_SPLIT) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  MP_TAC(ISPECL
   [`REJ_SAMPLE (SUB_LIST (0,k) (inlist:(24 word)list))`;
    `REJ_SAMPLE (SUB_LIST (k, LENGTH inlist - k) (inlist:(24 word)list))`;
    `256`] SUB_LIST_APPEND_LEFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUB_LIST_REFL THEN
  ASM_REWRITE_TAC[LE_REFL]);;

(* When 256 <= LENGTH (REJ_SAMPLE prefix), SUB_LIST (0,256) of the full REJ_SAMPLE
   equals SUB_LIST (0,256) of just the REJ_SAMPLE of the prefix. *)
let REJ_SAMPLE_SUBLIST_256_BOUNDED = prove
 (`!(inlist:(24 word)list) k.
    256 <= LENGTH(REJ_SAMPLE (SUB_LIST (0,k) inlist))
    ==> SUB_LIST (0,256) (REJ_SAMPLE inlist) =
        SUB_LIST (0,256) (REJ_SAMPLE (SUB_LIST (0,k) inlist))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inlist:(24 word)list`; `k:num`] REJ_SAMPLE_SPLIT) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN
  ASM_REWRITE_TAC[]);;

(* Monotonicity: one more input element adds at most 1 to REJ_SAMPLE length. *)
let REJ_SAMPLE_STEP_LE = prove
 (`!(l:(24 word)list) k.
    LENGTH (REJ_SAMPLE (SUB_LIST (0, k + 1) l)) <=
    LENGTH (REJ_SAMPLE (SUB_LIST (0, k) l)) + 1`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `k + 1 <= LENGTH (l:(24 word)list)` THENL
   [MP_TAC(ISPECL [`l:(24 word)list`; `k:num`; `1:num`; `0:num`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REJ_SAMPLE_APPEND; LENGTH_APPEND; LE_ADD_LCANCEL] THEN
    REWRITE_TAC[REJ_SAMPLE] THEN
    W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN ARITH_TAC;
    SUBGOAL_THEN `SUB_LIST (0, k + 1) (l:(24 word)list) = l /\
                  LENGTH (l:(24 word)list) <= k`
      (fun th -> SUBST1_TAC(CONJUNCT1 th) THEN
                 ASM_SIMP_TAC[SUB_LIST_REFL; CONJUNCT2 th] THEN ARITH_TAC) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;

Printf.printf "=== defs_extra loaded ===\n%!";;

(* ========================================================================= *)
(* R9 bridge + JA resolvers.                                                 *)
(* ========================================================================= *)

(* Minimal defs — only things NOT in checkpoint *)

let R9_POPCNT_BRIDGE = prove
 (`!ymm3_26:int256.
   val(word_subword ymm3_26 (0,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (32,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (64,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (96,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (128,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (160,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (192,32):int32) < 8388608 /\
   val(word_subword ymm3_26 (224,32):int32) < 8388608
   ==> word(word_popcount
         (word_zx(word_zx(word
           (bitval(bit 31 (word_sub (word_subword ymm3_26 (0,32):int32) (word 8380417))) +
            2 * bitval(bit 31 (word_sub (word_subword ymm3_26 (32,32):int32) (word 8380417))) +
            4 * bitval(bit 31 (word_sub (word_subword ymm3_26 (64,32):int32) (word 8380417))) +
            8 * bitval(bit 31 (word_sub (word_subword ymm3_26 (96,32):int32) (word 8380417))) +
            16 * bitval(bit 31 (word_sub (word_subword ymm3_26 (128,32):int32) (word 8380417))) +
            32 * bitval(bit 31 (word_sub (word_subword ymm3_26 (160,32):int32) (word 8380417))) +
            64 * bitval(bit 31 (word_sub (word_subword ymm3_26 (192,32):int32) (word 8380417))) +
            128 * bitval(bit 31 (word_sub (word_subword ymm3_26 (224,32):int32) (word 8380417))))
          :byte):int32):int64)):int64 =
       word(LENGTH(FILTER (\c:int32. val c < 8380417)
         [word_subword ymm3_26 (0,32):int32;
          word_subword ymm3_26 (32,32);
          word_subword ymm3_26 (64,32);
          word_subword ymm3_26 (96,32);
          word_subword ymm3_26 (128,32);
          word_subword ymm3_26 (160,32);
          word_subword ymm3_26 (192,32);
          word_subword ymm3_26 (224,32)]))`,
  GEN_TAC THEN STRIP_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[SIGN_BIT_BITVAL] THEN
  MP_TAC(ISPECL
   [`word_subword (ymm3_26:int256) (0,32):int32`;
    `word_subword (ymm3_26:int256) (32,32):int32`;
    `word_subword (ymm3_26:int256) (64,32):int32`;
    `word_subword (ymm3_26:int256) (96,32):int32`;
    `word_subword (ymm3_26:int256) (128,32):int32`;
    `word_subword (ymm3_26:int256) (160,32):int32`;
    `word_subword (ymm3_26:int256) (192,32):int32`;
    `word_subword (ymm3_26:int256) (224,32):int32`]
   POPCNT_EQ_LENGTH_FILTER) THEN
  ASM_SIMP_TAC[SIGN_BIT_BITVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  IMP_REWRITE_TAC[WORD_POPCOUNT_WORD_ZX] THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN ARITH_TAC);;

(* JA branch resolution tactics from the proof file *)
let RESOLVE_JA_ONLY_TAC svar =
  fun th ->
    TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th' ->
      let c = concl th' in
      is_eq c && can (find_term is_cond) c &&
      can (find_term ((=) svar)) c &&
      can (find_term ((=) `RIP`)) c))) THEN
    ASSUME_TAC th;;

let RESOLVE_JA_CURLEN_TAC =
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    can (find_term ((=) `RIP`)) (concl th) && is_eq(concl th) &&
    can (find_term is_cond) (concl th))) THEN
  MATCH_MP_TAC(TAUT `~p ==> (if p then a else b) = b`) THEN
  REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
              VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_EQ_SUB_RADD; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  UNDISCH_TAC `curlen <= 248` THEN ARITH_TAC;;

let RESOLVE_JA_OFFSET_TAC =
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    can (find_term ((=) `RIP`)) (concl th) && is_eq(concl th) &&
    can (find_term is_cond) (concl th))) THEN
  MATCH_MP_TAC(TAUT `~p ==> (if p then a else b) = b`) THEN
  REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
              VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_EQ_SUB_RADD; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  UNDISCH_TAC `24 * i <= 808` THEN ARITH_TAC;;

Printf.printf "=== DEFS LOADED ===\n%!";;

(* ========================================================================= *)
(* PIVOT_VAL_EQ lemma.                                                       *)
(* ========================================================================= *)
(* SCALAR_BODY_LEMMA preamble (byte bridges + ACCEPT_REJ_SAMPLE_SINGLETON).   *)
(* ========================================================================= *)

let READ_3BYTES_EL = prove
 (`!(inlist:(24 word)list) (buf:int64) mem j n.
     LENGTH inlist = n /\ j < n /\ 3 * j + 3 <= 3 * n /\
     read(memory :> bytes(buf, 3 * n)) mem = num_of_wordlist inlist
     ==> read(memory :> bytes(word_add buf (word(3 * j)), 3)) mem =
         val(EL j inlist)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inlist:(24 word)list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[DIMINDEX_24] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  POP_ASSUM MP_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBGOAL_THEN
    `read (bytes (buf,3 * n)) (read memory mem) DIV 2 EXP (24 * j) =
     read (bytes (word_add buf (word (3*j)), 3 * n - 3*j)) (read memory mem)`
    SUBST1_TAC THENL
   [REWRITE_TAC[READ_BYTES_DIV; ARITH_RULE `24 * j = 8 * (3 * j)`] THEN
    REFL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `24 = 8 * 3`; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (3 * n - 3 * j) 3 = 3` SUBST1_TAC THENL
   [UNDISCH_TAC `3 * j + 3 <= 3 * n` THEN REWRITE_TAC[MIN] THEN ARITH_TAC;
    REFL_TAC]);;

(let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in
 output_string oc "SBL: READ_3BYTES_EL done, starting BYTE_BRIDGE_3BYTES\n"; close_out oc);;

(* Byte-to-coefficient bridge: 3 bytes of memory, mixed via bytes16 + bytes8
   + word_or (as the AVX2 scalar path does), equal val(EL j inlist). This is
   the semantic heart of the filter-rejection reasoning in the scalar body. *)
let BYTE_BRIDGE_3BYTES = prove
 (`!(inlist:(24 word)list) (buf:int64) s j n.
     LENGTH inlist = n /\ j < n /\ 3 * j + 3 <= 3 * n /\
     read(memory :> bytes(buf, 3 * n)) s = num_of_wordlist inlist
     ==>
     val(word_or
          (word_zx(read(memory :> bytes16 (word_add buf (word (3*j)))) s):(32)word)
          (word_shl
            (word_zx(read(memory :> bytes8 (word_add buf (word(3*j + 2)))) s):(32)word)
            16):(32)word):num
     = val(EL j inlist)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`inlist:(24 word)list`; `buf:int64`; `s:x86state`; `j:num`; `n:num`]
    READ_3BYTES_EL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(3:num) = 2 + 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[bytes16; bytes8; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  ABBREV_TAC
    `a = read (bytes (word_add buf (word ((2 + 1) * j)),2)) (read memory s)` THEN
  ABBREV_TAC
    `b = read (bytes (word_add buf (word ((2 + 1) * j + 2)),1)) (read memory s)` THEN
  SUBGOAL_THEN
    `word_add (word_add buf (word((2+1)*j))) (word 2):int64 =
     word_add buf (word ((2+1)*j + 2))` SUBST_ALL_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`word_add buf (word ((2 + 1) * j)):int64`; `2`;
                 `read memory s:int64->(8)word`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`word_add buf (word ((2 + 1) * j + 2)):int64`; `1`;
                 `read memory s:int64->(8)word`] READ_BYTES_BOUND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`word_zx(word a:(16)word):(32)word`;
                 `word_shl(word_zx(word b:(8)word):(32)word) 16`]
          VAL_WORD_OR_DISJOINT) THEN
  ANTS_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_16; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `a MOD 65536 = a` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `b MOD 256 = b` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `a MOD 4294967296 = a` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `a < 65536` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `b MOD 4294967296 = b` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `b < 256` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(65536 * b) MOD 4294967296 = 65536 * b` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `b < 256` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in
 output_string oc "SBL: BYTE_BRIDGE_3BYTES done, starting BYTE_BRIDGE_3BYTES_2STATE\n"; close_out oc);;

(* Two-state variant: the bytes16 and bytes8 reads can come from different
   states as long as both states have the same num_of_wordlist read at buf. *)
let BYTE_BRIDGE_3BYTES_2STATE = prove
 (`!(inlist:(24 word)list) (buf:int64) (s1:x86state) (s2:x86state) j n.
     LENGTH inlist = n /\ j < n /\ 3 * j + 3 <= 3 * n /\
     read(memory :> bytes(buf, 3 * n)) s1 = num_of_wordlist inlist /\
     read(memory :> bytes(buf, 3 * n)) s2 = num_of_wordlist inlist
     ==>
     val(word_or
          (word_zx(read(memory :> bytes16 (word_add buf (word (3*j)))) s1):(32)word)
          (word_shl
            (word_zx(read(memory :> bytes8 (word_add buf (word(3*j + 2)))) s2):(32)word)
            16):(32)word):num
     = val(EL j inlist)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `read(memory :> bytes8 (word_add buf (word (3*j + 2)):int64)) s2 =
     read(memory :> bytes8 (word_add buf (word (3*j + 2)):int64)) s1`
    SUBST1_TAC THENL
   [REWRITE_TAC[bytes8; READ_COMPONENT_COMPOSE; asword; through; read] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    SUBGOAL_THEN
      `!(s:x86state).
         read (memory :> bytes (word_add buf (word (3 * j + 2)),1)) s =
         (read(memory :> bytes(buf, 3 * n)) s DIV 2 EXP (8 * (3 * j + 2))) MOD
         2 EXP (8 * 1)`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
      REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
      SUBGOAL_THEN `MIN (3 * n - (3 * j + 2)) 1 = 1` SUBST1_TAC THENL
       [UNDISCH_TAC `3 * j + 3 <= 3 * n` THEN REWRITE_TAC[MIN] THEN ARITH_TAC;
        REFL_TAC];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC BYTE_BRIDGE_3BYTES THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]]);;

(* Bridge from a bytes32 word-read equation to a bytes(_,4) num-read
   equation at the same state. Used in the ACCEPT branch to convert the
   MOV store's bytes32 equation at s48 into a bytes(_,4) equation that
   VSTEPS can then propagate unchanged through s49 (ADD) and s50 (JMP). *)

(let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in
 output_string oc "SBL: BYTE_BRIDGE_3BYTES_2STATE done, starting BYTES32_TO_BYTES\n"; close_out oc);;

let BYTES32_TO_BYTES = prove
 (`!(mem:(x86state,int64->byte)component) (s:x86state) (a:int64) (w:(32)word).
      read(mem :> bytes32 a) s = w
      ==> read(mem :> bytes(a,4)) s = val w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  ABBREV_TAC
    `b = read (bytes (a,4))
            (read (mem:(x86state,int64->byte)component) s)` THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`a:int64`; `4`;
                 `(read (mem:(x86state,int64->byte)component) s):int64->(8)word`]
          READ_BYTES_BOUND) THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 4 = 32`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]));;

(* ACCEPT-branch singleton bridge: given the memory equations and the exact
   form of r8val (as it appears after X86_VSTEPS through state s46) with
   val r8val < 8380417, derive both:
   - the pivot: val r8val = val(EL (8*N+i) inlist) MOD 2^23
   - the filter conclusion: REJ_SAMPLE(SUB_LIST(8*N+i, 1) inlist) = [word(val r8val):int32]

   This packages the pivot + filter into one implication so it can be applied
   via MP_TAC without adding the intermediate pivot to the main goal's asl
   (which would pollute downstream ASM_REWRITE_TAC rewrites). *)

(let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in
 output_string oc "SBL: BYTES32_TO_BYTES done, starting ACCEPT_REJ_SAMPLE_SINGLETON\n"; close_out oc);;

let ACCEPT_REJ_SAMPLE_SINGLETON = prove
 (`!(inlist:(24 word)list) (buf:int64) (s1:x86state) (s2:x86state)
    (r8val:int64) (N:num) (i:num).
     LENGTH inlist = 280 /\
     8 * N + i < 280 /\
     3 * (8 * N + i) + 3 <= 3 * 280 /\
     read(memory :> bytes(buf, 3 * 280)) s1 = num_of_wordlist inlist /\
     read(memory :> bytes(buf, 3 * 280)) s2 = num_of_wordlist inlist /\
     val(r8val:int64) < 8380417 /\
     r8val = word_zx(word_and
            (word_zx (word_zx
             (word_or
              (word_zx (word_zx (word_zx
                (read(memory :> bytes16 (word_add buf (word (3*(8*N+i))))) s1)
                :(32)word):(64)word):(32)word)
              (word_zx (word_zx
               (word_shl
                (word_zx (word_zx (word_zx
                  (read(memory :> bytes8 (word_add buf (word (3*(8*N+i) + 2)))) s2)
                  :(32)word):(64)word):(32)word) 16)
               :(64)word):(32)word)
             :(32)word):(64)word):(32)word)
            (word 8388607:(32)word):(32)word):int64
     ==>
     val r8val = val(EL (8*N+i) inlist) MOD 2 EXP 23 /\
     REJ_SAMPLE(SUB_LIST(8*N + i, 1) inlist) = [word(val r8val):int32]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(r8val:int64) = val(EL (8*N+i) (inlist:(24 word)list)) MOD 2 EXP 23`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN
      `!(x:(32)word).
          word_and (word_zx (word_zx x:(64)word):(32)word)
                   (word 8388607:(32)word) =
          word_and x (word 8388607:(32)word)`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
      `!(x:(16)word).
          word_zx(word_zx(word_zx x:(32)word):(64)word):(32)word = word_zx x`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
      `!(x:(8)word).
          word_zx(word_zx(word_shl(word_zx(word_zx(word_zx x:(32)word):(64)word):(32)word) 16):(64)word):(32)word =
          word_shl(word_zx x:(32)word) 16`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONV_TAC WORD_BLAST; ALL_TAC] THEN
    SUBGOAL_THEN
      `!(w:(32)word). word 8388607:(32)word = word(2 EXP 23 - 1)`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    SUBGOAL_THEN
      `!(w:(32)word). val w MOD 2 EXP 23 MOD 18446744073709551616 = val w MOD 2 EXP 23`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
      MP_TAC(ARITH_RULE `!x. x MOD 2 EXP 23 < 8388608`) THEN
      DISCH_THEN(MP_TAC o SPEC `val(w:(32)word)`) THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`inlist:(24 word)list`; `buf:int64`; `s1:x86state`;
                  `s2:x86state`; `8*N+i:num`; `280`] BYTE_BRIDGE_3BYTES_2STATE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_1] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REJ_SAMPLE; MAP; FILTER] THEN
  SUBGOAL_THEN `val(word (val (EL (8*N+i) (inlist:(24 word)list)) MOD 2 EXP 23):int32) =
                val(r8val:int64)`
    SUBST1_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    SUBGOAL_THEN `val (EL (8*N+i) (inlist:(24 word)list)) MOD 2 EXP 23 MOD 2 EXP 32 =
                  val (EL (8*N+i) inlist) MOD 2 EXP 23`
      SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      MP_TAC(ARITH_RULE `!x. x MOD 2 EXP 23 < 8388608`) THEN
      DISCH_THEN(MP_TAC o SPEC `val(EL (8*N+i) (inlist:(24 word)list))`) THEN
      ARITH_TAC;
      FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM th])];
    ASM_REWRITE_TAC[]]);;

(let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in
 output_string oc "SBL: ACCEPT_REJ_SAMPLE_SINGLETON done, starting SCALAR_BODY_LEMMA\n"; close_out oc);;

(* ========================================================================= *)

(* PIVOT_VAL_EQ: key pivot lemma for the REJECT branch of scalar_body_lemma.

   Derived from ACCEPT_REJ_SAMPLE_SINGLETON by dropping the `val r8val < 8380417`
   premise and returning only the first conjunct.

   Rationale: the inline derivation of this fact in scalar_body_lemma.ml:816-858
   took 40+ minutes because it rewrites 217 x86-state assumptions via
   VAL_WORD_ZX_GEN + NUM_REDUCE_CONV. Proving it as a top-level lemma with
   WORD_BLAST normalizers runs in ~1s, then MP_TAC/ANTS_TAC inline is ~0.2s.

   Depends on ACCEPT_REJ_SAMPLE_SINGLETON, BYTE_BRIDGE_3BYTES_2STATE (from
   scalar_body_preamble.ml). *)

let stmt =
  let accept_concl = concl ACCEPT_REJ_SAMPLE_SINGLETON in
  let vars, body = strip_forall accept_concl in
  let prems, cncl = dest_imp body in
  let prem_list = conjuncts prems in
  (* Remove 'val r8val < 8380417' premise (index 5) *)
  let new_prems = list_mk_conj (List.filteri (fun n _ -> n <> 5) prem_list) in
  let new_concl = fst(dest_conj cncl) in
  list_mk_forall (vars, mk_imp(new_prems, new_concl));;

let PIVOT_VAL_EQ = prove(stmt,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
    `!(x:(32)word).
        word_and (word_zx (word_zx x:(64)word):(32)word)
                 (word 8388607:(32)word) =
        word_and x (word 8388607:(32)word)`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `!(x:(16)word).
        word_zx(word_zx(word_zx x:(32)word):(64)word):(32)word = word_zx x`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `!(x:(8)word).
        word_zx(word_zx(word_shl(word_zx(word_zx(word_zx x:(32)word):(64)word):(32)word) 16):(64)word):(32)word =
        word_shl(word_zx x:(32)word) 16`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `!(w:(32)word). word 8388607:(32)word = word(2 EXP 23 - 1)`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN
    `!(w:(32)word). val w MOD 2 EXP 23 MOD 18446744073709551616 = val w MOD 2 EXP 23`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ARITH_RULE `!x. x MOD 2 EXP 23 < 8388608`) THEN
    DISCH_THEN(MP_TAC o SPEC `val(w:(32)word)`) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`inlist:(24 word)list`; `buf:int64`; `s1:x86state`;
                `s2:x86state`; `8*N+i:num`; `280`] BYTE_BRIDGE_3BYTES_2STATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC NUM_REDUCE_CONV);;

Printf.printf "=== PIVOT_VAL_EQ loaded ===\n%!";;

(* ========================================================================= *)
(* MEMORY_CONJUNCT_CLOSURE lemma.                                            *)
(* ========================================================================= *)

(* MEMORY_CONJUNCT_CLOSURE — standalone lemma for closing the memory conjunct
   in Case B (ACCEPT i+1=K, curlen+1<256).

   After X86_STEPS to s54 + ENSURES_FINAL_STATE_TAC + ASM_REWRITE, the memory
   subgoal reduces to:
     read (memory :> bytes (res, 4*(curlen+1))) s = num_of_wordlist (APPEND curlist [wa])
   with asms:
     - curlen < 256
     - LENGTH curlist = curlen
     - read (memory :> bytes (res, 4*curlen)) s = num_of_wordlist curlist
     - read (memory :> bytes (word_add res (word (4*curlen)), 4)) s = val wa

   This lemma is specialized to wa:int32 so it matches the list type directly.
   Using it inline: MATCH_MP_TAC MEMORY_CONJUNCT_CLOSURE THEN ASM_REWRITE_TAC[] *)

let MEMORY_CONJUNCT_CLOSURE = prove
 (`!(res:int64) (s:x86state) (curlist:int32 list) (curlen:num) (wa:int32).
      curlen < 256 /\
      LENGTH curlist = curlen /\
      read (memory :> bytes (res, 4 * curlen)) s = num_of_wordlist curlist /\
      read (memory :> bytes (word_add res (word (4 * curlen)), 4)) s = val wa
      ==> read (memory :> bytes (res, 4 * (curlen + 1))) s =
          num_of_wordlist (APPEND curlist [wa])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `4 * (curlen + 1) = 4 * curlen + 4` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
  ASM_REWRITE_TAC[DIMINDEX_32; ARITH_RULE `8 * 4 * l = 32 * l`] THEN
  REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[ADD_0]);;

Printf.printf "=== MEMORY_CONJUNCT_CLOSURE loaded ===\n%!";;

(* ========================================================================= *)
(* Case B closure helpers (VAL_RCX_ADD3).                                    *)
(* ========================================================================= *)

(* Helper lemmas for Case B. *)

let VAL_RCX_ADD3 = prove
 (`!N i:num. 24 * N + 3 * i <= 837
             ==> val(word_add (word_zx (word (24*N+3*i):int64):(32)word) (word 3:(32)word))
                 = 24 * N + 3 * i + 3`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `!m. m <= 837 ==> m MOD 18446744073709551616 = m /\
                                 m MOD 4294967296 = m /\
                                 (m + 3) MOD 4294967296 = m + 3 /\
                                 (m + 3) MOD 18446744073709551616 = m + 3`
    MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `m <= 837` THEN ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `24 * N + 3 * i:num`)] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let VAL_RCX_ADD3_ZX = prove
 (`!N i:num. 24 * N + 3 * i <= 837
             ==> val(word_zx(word_zx(word_add (word_zx (word (24*N+3*i):int64):(32)word) (word 3:(32)word)):(64)word):(32)word)
                 = 24 * N + 3 * i + 3`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[VAL_RCX_ADD3] THEN
  SUBGOAL_THEN `(24 * N + 3 * i + 3) MOD 18446744073709551616 = 24 * N + 3 * i + 3 /\
                (24 * N + 3 * i + 3) MOD 4294967296 = 24 * N + 3 * i + 3`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `24 * N + 3 * i <= 837` THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

Printf.printf "=== Case B helpers loaded ===\n%!";;

(* ========================================================================= *)
(* SCALAR_BODY_LEMMA (per-iteration specification).                          *)
(* ========================================================================= *)

(* scalar_body_lemma.ml — proof of the scalar body subgoal.
   Main proof uses MATCH_MP_TAC SCALAR_BODY_LEMMA; the wiring is verified
   working at mldsa_rej_uniform.ml:1939.

   Status: structural proof loads in ~15s (down from 1hr) after extracting
   PIVOT_VAL_EQ.

   Dependencies (must be loaded BEFORE this file):
   - pivot_lemma.ml          — PIVOT_VAL_EQ
   - memory_conjunct_lemma.ml — MEMORY_CONJUNCT_CLOSURE
   - case_b_close.ml         — VAL_RCX_ADD3, VAL_RCX_ADD3_ZX

   3 remaining CHEAT_TACs (all in the ACCEPT i+1=K offset-exit arm):
   - count-exit branch: curlen+1=256 case (trivial closure, similar to Case A)
   - Case A: offset-exit with curlen+1=256
   - Case B: offset-exit with curlen+1<256 (the interesting case —
     interactively validated via case_b_script.ml with 0 CHEATs,
     but file-load has subtle seqapply interaction — see reject_progress.md)
*)

(* DBG tag — a no-op tactic that prints a message and current subgoal count.
   Use `DBG "tag" THEN tactic` to trace tactic progress in file-load contexts
   where interactive goal inspection isn't available. *)
(* LOG: append a message to the progress log file; returns tactic *)
let LOG (tag:string) : tactic =
  fun (asl, g) ->
    let oc = open_out_gen [Open_append; Open_creat] 0o644 "/tmp/sbl_progress.log" in
    output_string oc (tag ^ "\n"); close_out oc;
    ALL_TAC (asl, g);;

let DBG (tag:string) : tactic =
  fun (asl, g) ->
    let n = match !current_goalstack with
      | gs :: _ -> let (_, ls, _) = gs in List.length ls
      | [] -> -1 in
    let gs = string_of_term g in
    let preview = String.sub gs 0 (min 80 (String.length gs)) in
    Printf.printf "DBG %s | subgoals=%d | goal=%s\n%!" tag n preview;
    ALL_TAC (asl, g);;

(let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in
 output_string oc "SBL: starting READ_3BYTES_EL\n"; close_out oc);;

(* Extract 3 bytes of memory at offset 3*j from a 3*n-byte buffer (the natural
   byte size for a (24 word)list of length n: 24*n bits = 3*n bytes). *)
let SCALAR_BODY_LEMMA = prove
 (`!res buf table (inlist:(24 word)list) pc stackpointer N K i.
    LENGTH inlist = 280 /\
    nonoverlapping (word pc, 246) (res, 1024) /\
    nonoverlapping (word pc, 246) (buf, 840) /\
    nonoverlapping (word pc, 246) (table, 2048) /\
    nonoverlapping (res, 1024) (buf, 840) /\
    nonoverlapping (res, 1024) (table, 2048) /\
    nonoverlapping (stackpointer, 8) (res, 1024) /\
    24 * N <= 832 /\
    LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * N) inlist)) <= 256 /\
    i < K /\ ~(i = K) /\ 0 < K /\
    (!j. j < K
         ==> LENGTH(REJ_SAMPLE(SUB_LIST(0, 8*N + j) inlist)) < 256 /\
             24 * N + 3 * j <= 837) /\
    (256 <= LENGTH(REJ_SAMPLE(SUB_LIST(0, 8*N + K) inlist)) \/
     837 < 24 * N + 3 * K)
    ==>
    ensures x86
     (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_tmc) /\
          read RIP s = word(pc + 181) /\
          read RSP s = stackpointer /\
          read (memory :> bytes (buf,840)) s = num_of_wordlist inlist /\
          read (memory :> bytes (table,2048)) s =
            num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
          read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
          read YMM0 s =
            word 115366376096492355175489748997433888275274855593258845241081954797768348401920 /\
          read YMM1 s =
            word 226156397384342666605459106258636701594091082888230722833791023177481060351 /\
          read YMM2 s =
            word 225935595421087293402315996791205668696012104344015382954355885915737415681 /\
          (let outlist_i = REJ_SAMPLE(SUB_LIST(0, 8 * N + i) (inlist:(24 word)list)) in
           let outlen_i = LENGTH outlist_i in
           read RAX s = word outlen_i /\
           read RCX s = word(24 * N + 3 * i) /\
           read(memory :> bytes(res, 4 * outlen_i)) s = num_of_wordlist outlist_i))
     (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_tmc) /\
          read RIP s = word (if i + 1 < K then pc + 181 else pc + 242) /\
          read RSP s = stackpointer /\
          read (memory :> bytes (buf,840)) s = num_of_wordlist inlist /\
          read (memory :> bytes (table,2048)) s =
            num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
          read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
          read YMM0 s =
            word 115366376096492355175489748997433888275274855593258845241081954797768348401920 /\
          read YMM1 s =
            word 226156397384342666605459106258636701594091082888230722833791023177481060351 /\
          read YMM2 s =
            word 225935595421087293402315996791205668696012104344015382954355885915737415681 /\
          (let outlist_j = REJ_SAMPLE(SUB_LIST(0, 8 * N + (i+1)) (inlist:(24 word)list)) in
           let outlen_j = LENGTH outlist_j in
           read RAX s = word outlen_j /\
           read RCX s = word(24 * N + 3 * (i+1)) /\
           read(memory :> bytes(res, 4 * outlen_j)) s = num_of_wordlist outlist_j))
     (MAYCHANGE [RSP; RIP; RAX; RCX; R8; R9; R10] ,,
      MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4;
                 ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11;
                 ZMM12; ZMM13; ZMM14; ZMM15] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(res,1024)])`,
  W(fun _ -> (let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in output_string oc "SBL_PROOF:starting\n"; close_out oc); ALL_TAC) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  W(fun _ -> (let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in output_string oc "SBL_PROOF:after NONOVERLAPPING\n"; close_out oc); ALL_TAC) THEN
  (* Split the precondition conjunction: strip all conjuncts EXCEPT the final
     disjunction (which we keep as a single assumption for late use). *)
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC
           (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 ASSUME_TAC
             (CONJUNCTS_THEN2 ASSUME_TAC
              (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))))))) THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i:num < K`) o
    check (is_forall o concl)) THEN STRIP_TAC THEN
  ABBREV_TAC `curlist = REJ_SAMPLE(SUB_LIST(0, 8 * N + i) (inlist:(24 word)list))` THEN
  ABBREV_TAC `curlen = LENGTH(curlist:int32 list)` THEN
  SUBGOAL_THEN `curlen < 256` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen"; "curlist"] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
  ASM_REWRITE_TAC[] THEN
  W(fun _ -> (let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in output_string oc "SBL_PROOF:before ENSURES_INIT\n"; close_out oc); ALL_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  W(fun _ -> (let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in output_string oc "SBL_PROOF:after ENSURES_INIT\n"; close_out oc); ALL_TAC) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [36;37] THEN
  W(fun _ -> (let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in output_string oc "SBL_PROOF:after X86_STEPS [36;37]\n"; close_out oc); ALL_TAC) THEN
  SUBGOAL_THEN `read RIP s37 = word(pc + 188):int64`
    (fun th -> TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th' ->
       let c = concl th' in is_eq c && can (find_term is_cond) c &&
       can (find_term ((=) `s37:x86state`)) c &&
       can (find_term ((=) `RIP`)) c))) THEN ASSUME_TAC th) THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      can (find_term ((=) `RIP`)) (concl th) && is_eq(concl th) &&
      can (find_term is_cond) (concl th))) THEN
    MATCH_MP_TAC(TAUT `~p ==> (if p then (a:int64) else b) = b`) THEN
    REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
                VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD;
                DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_EQ_SUB_RADD; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    UNDISCH_TAC `curlen < 256` THEN ARITH_TAC; ALL_TAC] THEN
  W(fun _ -> (let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in output_string oc "SBL_PROOF:before X86_STEPS [38;39]\n"; close_out oc); ALL_TAC) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [38;39] THEN
  W(fun _ -> (let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in output_string oc "SBL_PROOF:after X86_STEPS [38;39]\n"; close_out oc); ALL_TAC) THEN
  SUBGOAL_THEN `read RIP s39 = word(pc + 196):int64`
    (fun th -> TRY(FIRST_X_ASSUM(K ALL_TAC o check (fun th' ->
       let c = concl th' in is_eq c && can (find_term is_cond) c &&
       can (find_term ((=) `s39:x86state`)) c &&
       can (find_term ((=) `RIP`)) c))) THEN ASSUME_TAC th) THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      can (find_term ((=) `RIP`)) (concl th) && is_eq(concl th) &&
      can (find_term is_cond) (concl th))) THEN
    MATCH_MP_TAC(TAUT `~p ==> (if p then (a:int64) else b) = b`) THEN
    REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
                VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD;
                DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_EQ_SUB_RADD; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    UNDISCH_TAC `24 * N + 3 * i <= 837` THEN ARITH_TAC; ALL_TAC] THEN
  W(fun _ -> (let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in output_string oc "SBL_PROOF:before X86_VSTEPS (40--46)\n"; close_out oc); ALL_TAC) THEN
  X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (40--46) THEN
  W(fun _ -> (let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in output_string oc "SBL_PROOF:after X86_VSTEPS (40--46)\n"; close_out oc); ALL_TAC) THEN
  ABBREV_TAC `r8val:int64 = read R8 s46` THEN
  W(fun _ -> (let oc = open_out_gen [Open_append;Open_creat] 0o644 "/tmp/sbl_progress.log" in output_string oc "SBL_PROOF:about to ASM_CASES_TAC r8val<8380417\n"; close_out oc); ALL_TAC) THEN
  ASM_CASES_TAC `val(r8val:int64) < 8380417` THENL
   [(* ACCEPT branch: val(r8val) < 8380417, so JAE not taken; store + ADD + JMP *)
    LOG "ACCEPT: enter" THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC [47] THEN
    LOG "ACCEPT: after VSTEPS [47]" THEN
    SUBGOAL_THEN `read RIP s47 = word(pc + 233):int64` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        is_eq(concl th) && can (find_term ((=) `read RIP s47`)) (concl th) &&
        can (find_term is_cond) (concl th))) THEN
      MATCH_MP_TAC(MESON[] `~p ==> (q = (if p then (a:int64) else b) ==> q = b)`) THEN
      (fun (asl, g) ->
         let t32 = `:(32)word` in
         let rec find_wa t =
           if is_comb t then
             let f, a = dest_comb t in
             if is_comb f && is_const (fst(dest_comb f)) &&
                fst(dest_const(fst(dest_comb f))) = "word_and" &&
                type_of t = t32 && is_comb a && is_const(fst(dest_comb a)) &&
                fst(dest_const(fst(dest_comb a))) = "word" &&
                (try dest_small_numeral(snd(dest_comb a)) = 8388607 with _ -> false)
             then Some t
             else match find_wa f with Some r -> Some r | None -> find_wa a
           else None in
         match find_wa g with
         | Some t ->
           ABBREV_TAC (mk_eq(mk_var("zval", t32), t)) (asl, g)
         | None -> failwith "zval abbrev: no match") THEN
      REWRITE_TAC[INT_VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN; VAL_WORD;
                  DIMINDEX_32; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `val(zval:(32)word) < 4294967296` ASSUME_TAC THENL
       [MP_TAC(ISPEC `zval:(32)word` VAL_BOUND) THEN
        REWRITE_TAC[DIMINDEX_32] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
        `val(zval:(32)word) MOD 18446744073709551616 MOD 4294967296 = val zval`
        SUBST1_TAC THENL
       [ASM_SIMP_TAC[MOD_LT;
          ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`]; ALL_TAC] THEN
      SUBGOAL_THEN `r8val:int64 = word_zx(zval:(32)word)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th ->
          let c = concl th in
          is_eq c && fst(dest_eq c) = `r8val:int64`)) THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          let c = concl th in
          is_eq c && snd(dest_eq c) = `zval:(32)word`)) THEN
        DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `val(r8val:int64) = val(zval:(32)word)` ASSUME_TAC THENL
       [UNDISCH_TAC `r8val:int64 = word_zx(zval:(32)word)` THEN
        DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
        REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THENL
       [UNDISCH_TAC `&8380417:int <= &(val(zval:(32)word))` THEN
        UNDISCH_TAC `val(r8val:int64) = val(zval:(32)word)` THEN
        UNDISCH_TAC `val(r8val:int64) < 8380417` THEN
        REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_LT;
                    GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC;
        INT_ARITH_TAC]; ALL_TAC] THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read RIP s47 = (if p then (a:int64) else b)`] THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read events s47 = CONS (EventJump (a, b)) c`] THEN
    LOG "ACCEPT: before VSTEPS [48]" THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC [48] THEN
    LOG "ACCEPT: after VSTEPS [48]" THEN
    (* Convert the MOV store's bytes32 equation at s48 into a bytes(_,4)
       equation, which VSTEPS can propagate through s49 (ADD) and s50 (JMP). *)
    SUBGOAL_THEN
      `read(memory :> bytes(word_add res (word(4 * val(word curlen:int64))),4))
             s48 = val(r8val:int64)`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP BYTES32_TO_BYTES o check (fun th ->
        let c = concl th in is_eq c &&
        can (find_term ((=) `bytes32`)) c &&
        can (find_term ((=) `s48:x86state`)) c)) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        let c = concl th in is_eq c &&
        can (find_term ((=) `r8val:int64`)) c &&
        fst(dest_eq c) = `r8val:int64`)) THEN
      DISCH_THEN(fun th ->
        REWRITE_TAC[th; VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      W(fun (_, g) ->
         let t32 = `:(32)word` in
         let rec find_wa t =
           if is_comb t then
             let f, a = dest_comb t in
             if is_comb f && is_const (fst(dest_comb f)) &&
                fst(dest_const(fst(dest_comb f))) = "word_and" &&
                type_of t = t32 && is_comb a && is_const(fst(dest_comb a)) &&
                fst(dest_const(fst(dest_comb a))) = "word" &&
                (try dest_small_numeral(snd(dest_comb a)) = 8388607
                 with _ -> false)
             then Some t
             else match find_wa f with Some r -> Some r | None -> find_wa a
           else None in
         match find_wa g with
         | Some t ->
           MP_TAC(ISPEC t VAL_BOUND) THEN
           REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV
         | None -> failwith "VAL_BOUND search") THEN
      DISCH_TAC THEN
      ASM_SIMP_TAC[MOD_LT;
        ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`];
      ALL_TAC] THEN
    LOG "ACCEPT: before VSTEPS [49;50]" THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC [49;50] THEN
    LOG "ACCEPT: after VSTEPS [49;50]" THEN
    SUBGOAL_THEN
      `REJ_SAMPLE(SUB_LIST(0, 8*N + i + 1) (inlist:(24 word)list)) =
       APPEND curlist (REJ_SAMPLE(SUB_LIST(8*N + i, 1) inlist))`
      ASSUME_TAC THENL
     [SUBGOAL_THEN `8 * N + i + 1 = (8 * N + i) + 1` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`inlist:(24 word)list`; `8 * N + i`; `1:num`; `0:num`]
        SUB_LIST_SPLIT) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `8 * N + i < 280` ASSUME_TAC THENL
     [UNDISCH_TAC `24 * N + 3 * i <= 837` THEN ARITH_TAC; ALL_TAC] THEN
    (* ACCEPT byte-bridge: apply ACCEPT_REJ_SAMPLE_SINGLETON with the precise
       hypotheses, gathered via narrow FIRST_X_ASSUM picks, to avoid the slow
       ASM_REWRITE_TAC across the 280+ assumption list. *)
    SUBGOAL_THEN
      `REJ_SAMPLE(SUB_LIST(8*N + i, 1) (inlist:(24 word)list)) =
       [word(val(r8val:int64)):int32]`
      ASSUME_TAC THENL
     [(* Normalize `1 * val(word(24*N+3*i))` → `3*(8*N+i)` so the r8val shape matches. *)
      SUBGOAL_THEN `1 * val(word (24 * N + 3 * i):int64) = 3 * (8 * N + i) /\
                    1 * val(word (24 * N + 3 * i):int64) + 2 = 3 * (8 * N + i) + 2`
        STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[MULT_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
        SUBGOAL_THEN `(24 * N + 3 * i) MOD 2 EXP 64 = 24 * N + 3 * i`
          SUBST1_TAC THENL
         [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `24 * N + 3 * i <= 837` THEN
          ARITH_TAC;
          ARITH_TAC];
        ALL_TAC] THEN
      (* Fetch the 7 hypotheses for ACCEPT_REJ_SAMPLE_SINGLETON and feed them
         directly, without ASM_REWRITE. *)
      MP_TAC(SPECL [`inlist:(24 word)list`; `buf:int64`; `s39:x86state`;
                    `s40:x86state`; `r8val:int64`; `N:num`; `i:num`]
              ACCEPT_REJ_SAMPLE_SINGLETON) THEN
      LOG "ACCEPT: after MP ACCEPT_REJ_SAMPLE_SINGLETON" THEN
      ANTS_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN
        REPEAT CONJ_TAC THENL
         [(* 1: LENGTH inlist = 280 *) FIRST_ASSUM ACCEPT_TAC;
          (* 2: 8*N+i < 280 *)
          UNDISCH_TAC `24 * N + 3 * i <= 837` THEN ARITH_TAC;
          (* 3: 3*(8*N+i)+3 <= 840 *)
          UNDISCH_TAC `24 * N + 3 * i <= 837` THEN ARITH_TAC;
          (* 4: mem read s39 *) FIRST_ASSUM ACCEPT_TAC;
          (* 5: mem read s40 *) FIRST_ASSUM ACCEPT_TAC;
          (* 6: val r8val < 8380417 *) FIRST_ASSUM ACCEPT_TAC;
          (* 7: r8val = word_zx(...(word 3*(8*N+i))...) — discharge via MP_TAC
             on the r8val equation from asl (which uses `1*val(word(24*N+3*i))`)
             and then ASM_REWRITE_TAC[] using the arith normalization. *)
          FIRST_ASSUM(MP_TAC o check (fun th ->
            let c = concl th in is_eq c && fst(dest_eq c) = `r8val:int64`)) THEN
          ASM_REWRITE_TAC[]];
        DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th])];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `REJ_SAMPLE(SUB_LIST(0, 8*N + i + 1) (inlist:(24 word)list)) =
       APPEND curlist [word(val(r8val:int64)):int32]`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    LOG "ACCEPT: before ASM_CASES i+1<K" THEN
    ASM_CASES_TAC `i + 1 < K` THENL
     [LOG "ACCEPT i+1<K: enter" THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      LOG "ACCEPT i+1<K: after ENSURES_FINAL_STATE+ASM_REWRITE" THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT CONJ_TAC THENL
       [(* RAX: word_zx(word_add(word_zx(word curlen))(word 1)) = word(curlen+1) *)
        REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
        REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD;
                    DIMINDEX_32; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        IMP_REWRITE_TAC[MOD_LT] THEN
        UNDISCH_TAC `curlen < 256` THEN ARITH_TAC;
        (* RCX: word_zx(word_add(word_zx(word(24*N+3*i)))(word 3)) = word(24*N+3*(i+1)) *)
        ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
        REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD;
                    DIMINDEX_32; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        IMP_REWRITE_TAC[MOD_LT] THEN
        UNDISCH_TAC `24 * N + 3 * i <= 837` THEN ARITH_TAC;
        (* Memory: bytes(res, 4*(curlen+1)) = num_of_wordlist (APPEND curlist [...]) *)
        SUBGOAL_THEN `4 * (curlen + 1) = 4 * curlen + 4` SUBST1_TAC THENL
         [ARITH_TAC; ALL_TAC] THEN
        (* Fold the RHS's big expanded word back to r8val *)
        FIRST_ASSUM(fun th -> let c = concl th in
          if is_eq c && fst(dest_eq c) = `r8val:int64`
          then GEN_REWRITE_TAC (RAND_CONV o DEPTH_CONV) [SYM th]
          else failwith "r8val fold") THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`;
                       `s50:x86state`; `curlist:int32 list`;
                       `[word(val(r8val:int64)):int32]`; `4 * curlen`; `4`]
          BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[DIMINDEX_32] THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          (* Single-element write: num_of_wordlist [word(val r8val):int32] =
             val(word(val r8val)) = val r8val (since < 2^32), and the bytes(_,4)
             equation is propagated from s48 through VSTEPS 49-50. *)
          REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
          SUBGOAL_THEN `val(word(val(r8val:int64)):int32) = val r8val`
            SUBST1_TAC THENL
           [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
            UNDISCH_TAC `val(r8val:int64) < 8380417` THEN ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `val(word curlen:int64) = curlen`
            (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
           [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
            UNDISCH_TAC `curlen < 256` THEN ARITH_TAC;
            ALL_TAC] THEN
          ASM_REWRITE_TAC[]];
        (* MAYCHANGE closure *)
        REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC];
      (* ACCEPT i+1=K branch: step through CMP EAX,256; JAE (pc+242) to reach
         pc+242, using the strengthened lemma's WOP disjunct *)
      LOG "ACCEPT i+1=K: enter" THEN
      SUBGOAL_THEN `i + 1 = K` ASSUME_TAC THENL
       [UNDISCH_TAC `~(i + 1 < K)` THEN UNDISCH_TAC `i < K` THEN ARITH_TAC;
        ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC [51;52] THEN
      LOG "ACCEPT i+1=K: after VSTEPS [51;52]" THEN
      (* Split on WOP disjunct: count-exit vs offset-exit *)
      FIRST_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th))) THENL
       [(* count-exit: 256 <= LENGTH(REJ_SAMPLE ...), so curlen+1 = 256.
          The ACCEPT branch has REJ_SAMPLE(0, 8*N+i+1) = APPEND curlist [r8val],
          and with i+1=K we get length = curlen+1, so 256 <= curlen+1.
          Combined with curlen < 256: curlen+1 = 256. *)
        LOG "ACCEPT i+1=K count-exit: enter" THEN
        SUBGOAL_THEN `curlen + 1 = 256` ASSUME_TAC THENL
         [UNDISCH_TAC `256 <= LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list)))` THEN
          UNDISCH_TAC `i + 1 = K` THEN DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN
          UNDISCH_TAC `REJ_SAMPLE (SUB_LIST (0,8 * N + i + 1) (inlist:(24 word)list)) =
                       APPEND curlist [word(val(r8val:int64)):int32]` THEN
          DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
          UNDISCH_TAC `LENGTH (curlist:int32 list) = curlen` THEN
          UNDISCH_TAC `curlen < 256` THEN ARITH_TAC;
          ALL_TAC] THEN
        LOG "count-exit: curlen+1=256 established" THEN
        SUBGOAL_THEN `read RIP s52 = word(pc + 242):int64` ASSUME_TAC THENL
         [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
            let c = concl th in
            is_eq c && can (find_term ((=) `read RIP s52`)) c &&
            can (find_term is_cond) c)) THEN
          MATCH_MP_TAC (TAUT `p ==> (if p then (a:int64) else b) = a`) THEN
          SUBGOAL_THEN `val(word_add (word_zx (word curlen:int64):(32)word) (word 1:(32)word)) = curlen + 1` ASSUME_TAC THENL
           [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            ASM_SIMP_TAC[MOD_LT; ARITH_RULE `curlen < 256 ==> curlen < 18446744073709551616`;
                         ARITH_RULE `curlen < 256 ==> curlen < 4294967296`;
                         ARITH_RULE `curlen < 256 ==> curlen + 1 < 4294967296`];
            ALL_TAC] THEN
          ASM_REWRITE_TAC[INT_VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN; VAL_WORD;
                          DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
          ALL_TAC] THEN
        LOG "count-exit: RIP s52 = pc+242 established" THEN
        DISCARD_MATCHING_ASSUMPTIONS [`read RIP s52 = (if p then (a:int64) else b)`] THEN
        DISCARD_MATCHING_ASSUMPTIONS [`read events s52 = CONS (EventJump (a, b)) c`] THEN
        ENSURES_FINAL_STATE_TAC THEN
        REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
        REPEAT CONJ_TAC THEN
        ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THENL
         [(* RAX *)
          REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
          REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD;
                      DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          IMP_REWRITE_TAC[MOD_LT] THEN
          UNDISCH_TAC `curlen < 256` THEN ARITH_TAC;
          (* RCX *)
          FIRST_X_ASSUM (SUBST1_TAC o SYM o check (fun th -> concl th = `i + 1 = K`)) THEN
          ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
          REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD;
                      DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          IMP_REWRITE_TAC[MOD_LT] THEN
          UNDISCH_TAC `24 * N + 3 * i <= 837` THEN ARITH_TAC;
          (* Memory: bytes(res, 4*(curlen+1)) = num_of_wordlist (APPEND curlist [...]) *)
          SUBGOAL_THEN `curlen + SUC 0 = curlen + 1` SUBST1_TAC THENL
           [ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `4 * (curlen + 1) = 4 * curlen + 4` SUBST1_TAC THENL
           [ARITH_TAC; ALL_TAC] THEN
          FIRST_ASSUM(fun th -> let c = concl th in
            if is_eq c && fst(dest_eq c) = `r8val:int64`
            then GEN_REWRITE_TAC (RAND_CONV o DEPTH_CONV) [SYM th]
            else failwith "r8val fold") THEN
          MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`;
                         `s52:x86state`; `curlist:int32 list`;
                         `[word(val(r8val:int64)):int32]`; `4 * curlen`; `4`]
            BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[DIMINDEX_32] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
            SUBGOAL_THEN `val(word(val(r8val:int64)):int32) = val r8val`
              SUBST1_TAC THENL
             [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
              UNDISCH_TAC `val(r8val:int64) < 8380417` THEN ARITH_TAC;
              ALL_TAC] THEN
            SUBGOAL_THEN `val(word curlen:int64) = curlen`
              (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
             [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
              UNDISCH_TAC `curlen < 256` THEN ARITH_TAC;
              ALL_TAC] THEN
            ASM_REWRITE_TAC[]];
          (* MAYCHANGE closure *)
          REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC];
        (* offset-exit: 837 < 24*N+3*K, sub-split on 256 <= curlen+1 *)
        LOG "ACCEPT i+1=K offset-exit: enter" THEN
        ASM_CASES_TAC `256 <= curlen + 1` THENL
         [(* Case A: curlen+1 = 256 (same output as count-exit). *)
          LOG "CaseA: enter" THEN
          SUBGOAL_THEN `curlen + 1 = 256` ASSUME_TAC THENL
           [UNDISCH_TAC `256 <= curlen + 1` THEN
            UNDISCH_TAC `curlen < 256` THEN ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `read RIP s52 = word(pc + 242):int64` ASSUME_TAC THENL
           [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
              let c = concl th in
              is_eq c && can (find_term ((=) `read RIP s52`)) c &&
              can (find_term is_cond) c)) THEN
            MATCH_MP_TAC (TAUT `p ==> (if p then (a:int64) else b) = a`) THEN
            SUBGOAL_THEN `val(word_add (word_zx (word curlen:int64):(32)word) (word 1:(32)word)) = curlen + 1` ASSUME_TAC THENL
             [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
              CONV_TAC NUM_REDUCE_CONV THEN
              ASM_SIMP_TAC[MOD_LT; ARITH_RULE `curlen < 256 ==> curlen < 18446744073709551616`;
                           ARITH_RULE `curlen < 256 ==> curlen < 4294967296`;
                           ARITH_RULE `curlen < 256 ==> curlen + 1 < 4294967296`];
              ALL_TAC] THEN
            ASM_REWRITE_TAC[INT_VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN; VAL_WORD;
                            DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
            ALL_TAC] THEN
          DISCARD_MATCHING_ASSUMPTIONS [`read RIP s52 = (if p then (a:int64) else b)`] THEN
          DISCARD_MATCHING_ASSUMPTIONS [`read events s52 = CONS (EventJump (a, b)) c`] THEN
          ENSURES_FINAL_STATE_TAC THEN
          REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
          REPEAT CONJ_TAC THEN
          ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THENL
           [(* RAX *)
            REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
            REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD;
                        DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            IMP_REWRITE_TAC[MOD_LT] THEN
            UNDISCH_TAC `curlen < 256` THEN ARITH_TAC;
            (* RCX *)
            FIRST_X_ASSUM (SUBST1_TAC o SYM o check (fun th -> concl th = `i + 1 = K`)) THEN
            ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
            REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD;
                        DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            IMP_REWRITE_TAC[MOD_LT] THEN
            UNDISCH_TAC `24 * N + 3 * i <= 837` THEN ARITH_TAC;
            (* Memory *)
            SUBGOAL_THEN `curlen + SUC 0 = curlen + 1` SUBST1_TAC THENL
             [ARITH_TAC; ALL_TAC] THEN
            SUBGOAL_THEN `4 * (curlen + 1) = 4 * curlen + 4` SUBST1_TAC THENL
             [ARITH_TAC; ALL_TAC] THEN
            FIRST_ASSUM(fun th -> let c = concl th in
              if is_eq c && fst(dest_eq c) = `r8val:int64`
              then GEN_REWRITE_TAC (RAND_CONV o DEPTH_CONV) [SYM th]
              else failwith "r8val fold") THEN
            MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`;
                           `s52:x86state`; `curlist:int32 list`;
                           `[word(val(r8val:int64)):int32]`; `4 * curlen`; `4`]
              BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
            ANTS_TAC THENL
             [ASM_REWRITE_TAC[DIMINDEX_32] THEN ARITH_TAC; ALL_TAC] THEN
            DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
             [ASM_REWRITE_TAC[];
              REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
              SUBGOAL_THEN `val(word(val(r8val:int64)):int32) = val r8val`
                SUBST1_TAC THENL
               [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
                UNDISCH_TAC `val(r8val:int64) < 8380417` THEN ARITH_TAC;
                ALL_TAC] THEN
              SUBGOAL_THEN `val(word curlen:int64) = curlen`
                (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
               [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
                UNDISCH_TAC `curlen < 256` THEN ARITH_TAC;
                ALL_TAC] THEN
              ASM_REWRITE_TAC[]];
            (* MAYCHANGE *)
            REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC];
          (* Case B: curlen+1 < 256 *)
          (* Case B: curlen+1 < 256. Step through CMP ECX,837; JA at s52,
             then X86_STEPS [53;54] after `wa` abbreviation, then close. *)
          LOG "CaseB: enter" THEN
          SUBGOAL_THEN `read RIP s52 = word(pc + 188):int64` ASSUME_TAC THENL
           [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
             let c = concl th in
             is_eq c && can (find_term ((=) `read RIP s52`)) c &&
             can (find_term is_cond) c)) THEN
            MATCH_MP_TAC (TAUT `~p ==> (if p then (a:int64) else b) = b`) THEN
            SUBGOAL_THEN `val(word_add (word_zx (word curlen:int64):(32)word) (word 1:(32)word)) = curlen + 1` ASSUME_TAC THENL
             [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
              CONV_TAC NUM_REDUCE_CONV THEN
              ASM_SIMP_TAC[MOD_LT; ARITH_RULE `curlen < 256 ==> curlen < 18446744073709551616`;
                           ARITH_RULE `curlen < 256 ==> curlen < 4294967296`;
                           ARITH_RULE `curlen < 256 ==> curlen + 1 < 4294967296`];
              ALL_TAC] THEN
            ASM_REWRITE_TAC[INT_VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN; VAL_WORD;
                            DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            ASM_SIMP_TAC[MOD_LT;
              ARITH_RULE `curlen < 256 ==> curlen + 1 < 18446744073709551616`;
              ARITH_RULE `curlen < 256 ==> curlen + 1 < 4294967296`;
              ARITH_RULE `256 < 4294967296`] THEN
            UNDISCH_TAC `~(256 <= curlen + 1)` THEN
            REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
            ALL_TAC] THEN
          LOG "CaseB: RIP s52 = pc+188" THEN
          DISCARD_MATCHING_ASSUMPTIONS [`read RIP s52 = (if p then (a:int64) else b)`] THEN
          DISCARD_MATCHING_ASSUMPTIONS [`read events s52 = CONS (EventJump (a, b)) c`] THEN
          (* Abbreviate word_and sub-expression as `wa` to preserve r8val def *)
          (fun (asl,g) ->
            let rec findit = function
              | [] -> failwith "no r8val def"
              | (_, th) :: rest ->
                 let c = concl th in
                 if is_eq c && (try fst(dest_var(fst(dest_eq c))) = "r8val" with _ -> false) then
                   let rhs = snd(dest_eq c) in
                   (try let _, inner = dest_comb rhs in
                        ABBREV_TAC (mk_eq(mk_var("wa", type_of inner), inner)) (asl,g)
                    with _ -> findit rest)
                 else findit rest
            in findit asl) THEN
          LOG "CaseB: wa abbreviated" THEN
          SUBGOAL_THEN `val(r8val:int64) = val(wa:(32)word)` ASSUME_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o check (fun th ->
              let c = concl th in
              is_eq c && (try fst(dest_var(fst(dest_eq c))) = "r8val" with _ -> false))) THEN
            DISCH_THEN SUBST1_TAC THEN
            MATCH_MP_TAC VAL_WORD_ZX THEN
            REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `word(val(r8val:int64)):(32)word = wa` ASSUME_TAC THENL
           [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST;
            ALL_TAC] THEN
          LOG "CaseB: before X86_STEPS [53;54]" THEN
          X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [53;54] THEN
          LOG "CaseB: after X86_STEPS [53;54]" THEN
          SUBGOAL_THEN `read RIP s54 = word(pc + 242):int64` ASSUME_TAC THENL
           [MP_TAC(SPECL [`N:num`; `i:num`] VAL_RCX_ADD3_ZX) THEN
            ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
            DISCH_TAC THEN
            FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
              let c = concl th in
              is_eq c && can (find_term ((=) `read RIP s54`)) c &&
              can (find_term is_cond) c)) THEN
            MATCH_MP_TAC (TAUT `p ==> (if p then (a:int64) else b) = a`) THEN
            REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_32] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            ASM_REWRITE_TAC[] THEN
            SUBGOAL_THEN `837 <= 24 * N + 3 * i + 3` (fun th -> REWRITE_TAC[th]) THENL
             [UNDISCH_TAC `837 < 24 * N + 3 * K` THEN
              UNDISCH_TAC `i + 1 = K` THEN ARITH_TAC;
              ALL_TAC] THEN
            SUBGOAL_THEN `~((24 * N + 3 * i + 3) - 837 = 0)`
              (fun th -> REWRITE_TAC[th]) THENL
             [UNDISCH_TAC `837 < 24 * N + 3 * K` THEN
              UNDISCH_TAC `i + 1 = K` THEN ARITH_TAC;
              ALL_TAC] THEN
            REWRITE_TAC[DE_MORGAN_THM; NOT_CLAUSES] THEN
            MP_TAC(SPECL [`837:num`; `24 * N + 3 * i + 3`] INT_OF_NUM_SUB) THEN
            ANTS_TAC THENL
             [UNDISCH_TAC `837 < 24 * N + 3 * K` THEN
              UNDISCH_TAC `i + 1 = K` THEN ARITH_TAC;
              ALL_TAC] THEN
            DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN INT_ARITH_TAC;
            ALL_TAC] THEN
          LOG "CaseB: RIP s54 = pc+242" THEN
          DISCARD_MATCHING_ASSUMPTIONS
            [`read RIP s54 = (if p then (a:int64) else b)`] THEN
          DISCARD_MATCHING_ASSUMPTIONS
            [`read events s54 = CONS (EventJump (a, b)) c`] THEN
          (* Pre-establish augmented memory invariant via MEMORY_CONJUNCT_CLOSURE *)
          SUBGOAL_THEN `val(word curlen:int64) = curlen`
            (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
           [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
            UNDISCH_TAC `curlen < 256` THEN ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN
            `read (memory :> bytes (res, 4 * (curlen + 1))) s54 =
             num_of_wordlist (APPEND curlist [word(val(r8val:int64)):int32])`
            ASSUME_TAC THENL
           [SUBGOAL_THEN `val(word(val(r8val:int64)):int32) = val r8val`
              ASSUME_TAC THENL
             [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
              UNDISCH_TAC `val(r8val:int64) < 8380417` THEN ARITH_TAC;
              ALL_TAC] THEN
            MATCH_MP_TAC MEMORY_CONJUNCT_CLOSURE THEN
            REPEAT CONJ_TAC THENL
             [FIRST_ASSUM ACCEPT_TAC;
              FIRST_ASSUM ACCEPT_TAC;
              FIRST_ASSUM ACCEPT_TAC;
              ONCE_REWRITE_TAC[ASSUME `val(word(val(r8val:int64)):int32) = val r8val`] THEN
              FIRST_ASSUM ACCEPT_TAC];
            ALL_TAC] THEN
          LOG "CaseB: mem conjunct established" THEN
          UNDISCH_THEN `r8val:int64 = word_zx(wa:(32)word)`
            (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
          ENSURES_FINAL_STATE_TAC THEN
          REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
          REPEAT CONJ_TAC THEN
          ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH;
            ARITH_RULE `curlen + SUC 0 = curlen + 1`] THENL
           [(* RAX *)
            ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
            REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD;
                        DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            IMP_REWRITE_TAC[MOD_LT] THEN
            UNDISCH_TAC `curlen < 256` THEN ARITH_TAC;
            (* RCX *)
            ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
            REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                        DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            IMP_REWRITE_TAC[MOD_LT] THEN
            UNDISCH_TAC `24 * N + 3 * i <= 837` THEN
            UNDISCH_TAC `i + 1 = K` THEN ARITH_TAC;
            (* MAYCHANGE *)
            REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC]]]];
    (* REJECT branch: val(r8val) >= 8380417, JAE taken to pc+181 *)
    LOG "REJECT: enter" THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC [47] THEN
    LOG "REJECT: after VSTEPS [47]" THEN
    SUBGOAL_THEN `read RIP s47 = word(pc + 181):int64` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th ->
        is_eq(concl th) && can (find_term ((=) `read RIP s47`)) (concl th) &&
        can (find_term is_cond) (concl th))) THEN
      MATCH_MP_TAC(MESON[] `p ==> (q = (if p then (a:int64) else b) ==> q = a)`) THEN
      SUBGOAL_THEN `8380417 <= val(r8val:int64)` ASSUME_TAC THENL
       [UNDISCH_TAC `~(val(r8val:int64) < 8380417)` THEN ARITH_TAC; ALL_TAC] THEN
      (fun (asl, g) ->
         let t32 = `:(32)word` in
         let rec find_wa t =
           if is_comb t then
             let f, a = dest_comb t in
             if is_comb f && is_const (fst(dest_comb f)) &&
                fst(dest_const(fst(dest_comb f))) = "word_and" &&
                type_of t = t32 && is_comb a && is_const(fst(dest_comb a)) &&
                fst(dest_const(fst(dest_comb a))) = "word" &&
                (try dest_small_numeral(snd(dest_comb a)) = 8388607 with _ -> false)
             then Some t
             else match find_wa f with Some r -> Some r | None -> find_wa a
           else None in
         match find_wa g with
         | Some t ->
           ABBREV_TAC (mk_eq(mk_var("zval", t32), t)) (asl, g)
         | None -> failwith "zval abbrev: no match") THEN
      REWRITE_TAC[INT_VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN; VAL_WORD;
                  DIMINDEX_32; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `val(zval:(32)word) < 4294967296` ASSUME_TAC THENL
       [MP_TAC(ISPEC `zval:(32)word` VAL_BOUND) THEN
        REWRITE_TAC[DIMINDEX_32] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
        `val(zval:(32)word) MOD 18446744073709551616 MOD 4294967296 = val zval`
        SUBST1_TAC THENL
       [ASM_SIMP_TAC[MOD_LT;
          ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`]; ALL_TAC] THEN
      SUBGOAL_THEN `r8val:int64 = word_zx(zval:(32)word)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th ->
          let c = concl th in
          is_eq c && fst(dest_eq c) = `r8val:int64`)) THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          let c = concl th in
          is_eq c && snd(dest_eq c) = `zval:(32)word`)) THEN
        DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `val(r8val:int64) = val(zval:(32)word)` ASSUME_TAC THENL
       [UNDISCH_TAC `r8val:int64 = word_zx(zval:(32)word)` THEN
        DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
        REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THENL
       [REFL_TAC;
        UNDISCH_TAC `~(&8380417:int <= &(val(zval:(32)word)))` THEN
        UNDISCH_TAC `val(r8val:int64) = val(zval:(32)word)` THEN
        UNDISCH_TAC `8380417 <= val(r8val:int64)` THEN
        REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ] THEN
        INT_ARITH_TAC]; ALL_TAC] THEN
    LOG "REJECT: after s47 RIP subgoal" THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read RIP s47 = (if p then (a:int64) else b)`] THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read events s47 = CONS (EventJump (a, b)) c`] THEN
    LOG "REJECT: after DISCARD s47" THEN
    SUBGOAL_THEN
      `REJ_SAMPLE(SUB_LIST(0, 8*N + i + 1) (inlist:(24 word)list)) =
       APPEND curlist (REJ_SAMPLE(SUB_LIST(8*N + i, 1) inlist))`
      ASSUME_TAC THENL
     [SUBGOAL_THEN `8 * N + i + 1 = (8 * N + i) + 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`inlist:(24 word)list`; `8 * N + i`; `1:num`; `0:num`] SUB_LIST_SPLIT) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `8 * N + i < 280` ASSUME_TAC THENL
     [UNDISCH_TAC `24 * N + 3 * i <= 837` THEN ARITH_TAC; ALL_TAC] THEN
    LOG "REJECT: before pivot lemma (using PIVOT_VAL_EQ)" THEN
    (* Pivot lemma: val r8val equals the 23 low bits of the list element.
       Use the extracted PIVOT_VAL_EQ top-level lemma for fast application. *)
    SUBGOAL_THEN `1 * val(word (24 * N + 3 * i):int64) = 3 * (8 * N + i) /\
                  1 * val(word (24 * N + 3 * i):int64) + 2 = 3 * (8 * N + i) + 2`
      STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `(24 * N + 3 * i) MOD 2 EXP 64 = 24 * N + 3 * i`
        SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `24 * N + 3 * i <= 837` THEN
        ARITH_TAC;
        ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `val(r8val:int64) = val(EL (8*N+i) (inlist:(24 word)list)) MOD 2 EXP 23`
      ASSUME_TAC THENL
     [MP_TAC(SPECL [`inlist:(24 word)list`; `buf:int64`; `s39:x86state`;
                    `s40:x86state`; `r8val:int64`; `N:num`; `i:num`]
               PIVOT_VAL_EQ) THEN
      ASM_REWRITE_TAC[ARITH_RULE `3 * 280 = 840`] THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `24 * N + 3 * i <= 837` THEN ARITH_TAC;
        DISCH_THEN ACCEPT_TAC];
      ALL_TAC] THEN
    LOG "REJECT: after pivot lemma" THEN
    SUBGOAL_THEN
      `REJ_SAMPLE(SUB_LIST(8 * N + i, 1) (inlist:(24 word)list)) = []`
      ASSUME_TAC THENL
     [REWRITE_TAC[SUB_LIST_1] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REJ_SAMPLE; MAP; FILTER] THEN
      REWRITE_TAC[VAL_MOD_23_EQ_AND] THEN
      COND_CASES_TAC THENL
       [SUBGOAL_THEN
          `val (word_and (word_zx (EL (8 * N + i) (inlist:(24 word)list)):int32)
                        (word 8388607):int32) =
           val(EL (8 * N + i) (inlist:(24 word)list)) MOD 2 EXP 23`
          SUBST_ALL_TAC THENL
         [REWRITE_TAC[GSYM VAL_MOD_23_EQ_AND; VAL_WORD; DIMINDEX_32] THEN
          MATCH_MP_TAC MOD_LT THEN
          MP_TAC(ISPEC `EL (8 * N + i) (inlist:(24 word)list)` VAL_BOUND) THEN
          REWRITE_TAC[DIMINDEX_24] THEN ARITH_TAC;
          ALL_TAC] THEN
        UNDISCH_TAC `~(val(r8val:int64) < 8380417)` THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC;
        REFL_TAC]; ALL_TAC] THEN
    LOG "REJECT: before SUBGOAL curlist" THEN
    SUBGOAL_THEN
      `REJ_SAMPLE(SUB_LIST(0, 8 * N + i + 1) (inlist:(24 word)list)) = curlist`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[APPEND_NIL]; ALL_TAC] THEN
    LOG "REJECT: before ASM_CASES i+1<K" THEN
    ASM_CASES_TAC `i + 1 < K` THENL
     [LOG "REJECT i+1<K: enter" THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      LOG "REJECT i+1<K: after ENSURES_FINAL_STATE" THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[APPEND_NIL] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [(* RCX: word_zx(word_add(word_zx(word(24*N+3*i)))(word 3)) = word(24*N+3*(i+1)) *)
        ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
        REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD;
                    DIMINDEX_32; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        IMP_REWRITE_TAC[MOD_LT] THEN
        UNDISCH_TAC `24 * N + 3 * i <= 837` THEN ARITH_TAC;
        (* MAYCHANGE closure *)
        REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC];
      (* i + 1 = K branch of REJECT — fully closed via WOP offset-exit.
         Mirrors Case B ACCEPT i+1=K: JA not taken on curlen<256, then
         CMP RCX,837 / JA taken to pc+242 using VAL_RCX_ADD3_ZX. *)
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [48] THEN
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [49] THEN
      SUBGOAL_THEN `read RIP s49 = word(pc + 188):int64` ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
         let c = concl th in
         is_eq c && can (find_term ((=) `read RIP s49`)) c &&
         can (find_term is_cond) c)) THEN
        MATCH_MP_TAC (TAUT `~p ==> (if p then (a:int64) else b) = b`) THEN
        REWRITE_TAC[INT_VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN; VAL_WORD;
                    DIMINDEX_32; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `curlen MOD 18446744073709551616 MOD 4294967296 = curlen`
          SUBST1_TAC THENL
         [ASM_SIMP_TAC[MOD_LT;
            ARITH_RULE `curlen < 256 ==> curlen < 18446744073709551616`;
            ARITH_RULE `curlen < 256 ==> curlen < 4294967296`];
          ALL_TAC] THEN
        SUBGOAL_THEN `~(&256:int <= &curlen)` ASSUME_TAC THENL
         [UNDISCH_TAC `curlen < 256` THEN
          REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `curlen < 256` THEN
        REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
        INT_ARITH_TAC; ALL_TAC] THEN
      DISCARD_MATCHING_ASSUMPTIONS
        [`read RIP s49 = (if p then (a:int64) else b)`] THEN
      DISCARD_MATCHING_ASSUMPTIONS
        [`read events s49 = CONS (EventJump (a, b)) c`] THEN
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [50] THEN
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [51] THEN
      FIRST_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th))) THENL
       [SUBGOAL_THEN `i + 1 = K` ASSUME_TAC THENL
         [UNDISCH_TAC `~(i + 1 < K)` THEN UNDISCH_TAC `i < K` THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `F` MP_TAC THENL
         [UNDISCH_TAC
            `256 <= LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list)))` THEN
          UNDISCH_TAC `REJ_SAMPLE (SUB_LIST (0,8 * N + i + 1) inlist) = curlist` THEN
          UNDISCH_TAC `i + 1 = K` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN
          DISCH_THEN SUBST1_TAC THEN
          UNDISCH_TAC `LENGTH (curlist:int32 list) = curlen` THEN
          UNDISCH_TAC `curlen < 256` THEN ARITH_TAC;
          MESON_TAC[]];
        SUBGOAL_THEN `i + 1 = K` ASSUME_TAC THENL
         [UNDISCH_TAC `~(i + 1 < K)` THEN UNDISCH_TAC `i < K` THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `read RIP s51 = word(pc + 242):int64` ASSUME_TAC THENL
         [MP_TAC(SPECL [`N:num`; `i:num`] VAL_RCX_ADD3_ZX) THEN
          ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
          DISCH_TAC THEN
          FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
            let c = concl th in
            is_eq c && can (find_term ((=) `read RIP s51`)) c &&
            can (find_term is_cond) c)) THEN
          MATCH_MP_TAC (TAUT `p ==> (if p then (a:int64) else b) = a`) THEN
          REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_32] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `837 <= 24 * N + 3 * i + 3` (fun th -> REWRITE_TAC[th]) THENL
           [UNDISCH_TAC `837 < 24 * N + 3 * K` THEN
            UNDISCH_TAC `i + 1 = K` THEN ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `~((24 * N + 3 * i + 3) - 837 = 0)`
            (fun th -> REWRITE_TAC[th]) THENL
           [UNDISCH_TAC `837 < 24 * N + 3 * K` THEN
            UNDISCH_TAC `i + 1 = K` THEN ARITH_TAC;
            ALL_TAC] THEN
          REWRITE_TAC[DE_MORGAN_THM; NOT_CLAUSES] THEN
          MP_TAC(SPECL [`837:num`; `24 * N + 3 * i + 3`] INT_OF_NUM_SUB) THEN
          ANTS_TAC THENL
           [UNDISCH_TAC `837 < 24 * N + 3 * K` THEN
            UNDISCH_TAC `i + 1 = K` THEN ARITH_TAC;
            ALL_TAC] THEN
          DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN INT_ARITH_TAC;
          ALL_TAC] THEN
        DISCARD_MATCHING_ASSUMPTIONS
          [`read RIP s51 = (if p then (a:int64) else b)`] THEN
        DISCARD_MATCHING_ASSUMPTIONS
          [`read events s51 = CONS (EventJump (a, b)) c`] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[APPEND_NIL] THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
         [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
          REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD;
                      DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          IMP_REWRITE_TAC[MOD_LT] THEN
          UNDISCH_TAC `24 * N + 3 * i <= 837` THEN
          UNDISCH_TAC `i + 1 = K` THEN ARITH_TAC;
          REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC]]]]);;

Printf.printf "=== SCALAR_BODY_LEMMA loaded (structural proof, 3 internal CHEATs in offset-exit arm) ===\n%!";;

(* ========================================================================= *)
(* Top-level MLDSA_REJ_UNIFORM_CORRECT proof.                                *)
(* ========================================================================= *)

let MLDSA_REJ_UNIFORM_CORRECT = prove
 (`!res buf table (inlist:(24 word)list) pc stackpointer.
    LENGTH inlist = 280 /\
    nonoverlapping (word pc, 246) (res, 1024) /\
    nonoverlapping (word pc, 246) (buf, 840) /\
    nonoverlapping (word pc, 246) (table, 2048) /\
    nonoverlapping (res, 1024) (buf, 840) /\
    nonoverlapping (res, 1024) (table, 2048) /\
    nonoverlapping (stackpointer, 8) (res, 1024)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_tmc) /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              C_ARGUMENTS [res; buf; table] s /\
              read(memory :> bytes(buf,840)) s = num_of_wordlist inlist /\
              read(memory :> bytes(table,2048)) s =
                num_of_wordlist(mldsa_rej_uniform_table:byte list))
         (\s. read RIP s = word(pc + 245) /\
              let outlist = SUB_LIST(0,256) (REJ_SAMPLE inlist) in
              let outlen = LENGTH outlist in
              C_RETURN s = word outlen /\
              read(memory :> bytes(res,4 * outlen)) s =
                num_of_wordlist outlist)
         (MAYCHANGE [RSP; RIP; RAX; RCX; R8; R9; R10] ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4;
                     ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11;
                     ZMM12; ZMM13; ZMM14; ZMM15] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(res,1024)])`,

  MAP_EVERY X_GEN_TAC
   [`res:int64`; `buf:int64`; `table:int64`;
    `inlist:(24 word)list`; `pc:num`;
    `stackpointer:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  STRIP_TAC THEN

  (* =================================================================== *)
  (* Phase 1: WOP to find loop iteration count N.                        *)
  (*                                                                     *)
  (* Thresholds 808/248 match the CMP instructions:                      *)
  (*   CMP eax, 0xF8 (248): JA exits if outlen > 248                    *)
  (*   CMP ecx, 0x328 (808): JA exits if offset > 808                   *)
  (* At m < N, negation gives: 24*(m+1) <= 832 /\ LENGTH(...) <= 248    *)
  (* IMPORTANT: use DISCH_THEN to avoid global NOT_LT rewrite.          *)
  (* =================================================================== *)

  SUBGOAL_THEN
   `?i. 832 < 24 * (i + 1) \/ 248 < LENGTH(REJ_SAMPLE(SUB_LIST(0,8 * i) inlist))`
  MP_TAC THENL
   [EXISTS_TAC `280:num` THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT] th)) THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES] THEN
    REWRITE_TAC[REJ_SAMPLE_EMPTY; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN

  (* =================================================================== *)
  (* Phase 2: ENSURES_WHILE_UP2_TAC for the SIMD loop.                  *)
  (*                                                                     *)
  (* Loop head: pc+104 (instruction 18: CMP eax,0xF8)                   *)
  (* Loop exit: pc+181 (instruction 36: scalar section entry)            *)
  (* UP2 automatically adds bytes_loaded to the invariant.               *)
  (* Bounds are derived from WOP inside the loop body, not stored.       *)
  (* =================================================================== *)

  ENSURES_WHILE_UP2_TAC `N:num` `pc + 104` `pc + 181`
   `\i s.
          read RSP s = stackpointer /\
          read (memory :> bytes (buf,840)) s = num_of_wordlist inlist /\
          read (memory :> bytes (table,2048)) s =
            num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
          read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
          read YMM0 s =
            word 115366376096492355175489748997433888275274855593258845241081954797768348401920 /\
          read YMM1 s =
            word 226156397384342666605459106258636701594091082888230722833791023177481060351 /\
          read YMM2 s =
            word 225935595421087293402315996791205668696012104344015382954355885915737415681 /\
          let outlist = REJ_SAMPLE(SUB_LIST(0,8*i) inlist) in
          let outlen = LENGTH outlist in
          read RAX s = word outlen /\
          read RCX s = word(24*i) /\
          read(memory :> bytes(res,4*outlen)) s = num_of_wordlist outlist` THEN
  ASM_REWRITE_TAC[LT_REFL] THEN REPEAT CONJ_TAC THENL

   [(* ================================================================= *)
    (* Subgoal 1: Pre-loop setup (instructions 1-17, pc -> pc+104)       *)
    (* FULLY PROVED                                                      *)
    (* ================================================================= *)
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (1--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY;
                LENGTH; num_of_wordlist] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_TRIVIAL] THEN
    CONV_TAC WORD_REDUCE_CONV;

    (* ================================================================= *)
    (* Subgoal 2: Loop body preservation (i -> i+1)                      *)
    (*                                                                   *)
    (* Structure:                                                        *)
    (*   (a) Derive bounds from WOP: curlen <= 248, 24*i <= 808          *)
    (*   (b) Simulate CMP+JA (instrs 18-19): resolve JA not taken       *)
    (*   (c) Simulate CMP+JA (instrs 20-21): resolve JA not taken       *)
    (*   (d) Simulate SIMD body (instrs 22-35)                           *)
    (*   (e) COND_CASES_TAC on i+1 < N                                  *)
    (*   (f) Semantic proof: relate SIMD to REJ_SAMPLE                   *)
    (* ================================================================= *)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN

    ABBREV_TAC `curlist = REJ_SAMPLE (SUB_LIST(0,8*i) inlist)` THEN
    ABBREV_TAC `curlen = LENGTH(curlist:int32 list)` THEN
    CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
    ASM_REWRITE_TAC[] THEN

    (* (a) Get bounds from WOP at i *)
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i:num < N`) o
      check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

    SUBGOAL_THEN `curlen <= 248` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `24 * i <= 808` ASSUME_TAC THENL
     [UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC; ALL_TAC] THEN

    ENSURES_INIT_TAC "s0" THEN

    (* (b) Instructions 18-19: CMP eax,0xF8; JA — not taken *)
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [18;19] THEN
    SUBGOAL_THEN `read RIP s19 = word(pc + 111):int64`
      (RESOLVE_JA_ONLY_TAC `s19:x86state`) THENL
     [RESOLVE_JA_CURLEN_TAC; ALL_TAC] THEN

    (* (c) Instructions 20-21: CMP ecx,0x328; JA — not taken *)
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [20;21] THEN
    SUBGOAL_THEN `read RIP s21 = word(pc + 119):int64`
      (RESOLVE_JA_ONLY_TAC `s21:x86state`) THENL
     [RESOLVE_JA_OFFSET_TAC; ALL_TAC] THEN

    (* (d) SIMD body: all verbose to preserve VMOVDQU→VPSHUFB→VPAND chain *)
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (22--29) THEN

    (* Abbreviate the 8 masked coefficients from YMM3 after VPAND *)
    (* Semantic bridge: use POPCNT_VMOVMSKPS_LEMMA to establish
       R9 = word(LENGTH(FILTER)) for the 8 masked dword lanes.
       The YMM3 at s26 = word_and(read YMM3 s25)(mask_broadcast).
       After ASM_REWRITE, the read R9 s29 expands to the popcount
       of the sign-bit mask, and the LEMMA matches directly. *)
    SUBGOAL_THEN
     `read R9 s29:int64 =
      word(LENGTH(FILTER (\c:int32. val c < 8380417)
        [word_subword (read YMM3 s26:int256) (0,32):int32;
         word_subword (read YMM3 s26) (32,32);
         word_subword (read YMM3 s26) (64,32);
         word_subword (read YMM3 s26) (96,32);
         word_subword (read YMM3 s26) (128,32);
         word_subword (read YMM3 s26) (160,32);
         word_subword (read YMM3 s26) (192,32);
         word_subword (read YMM3 s26) (224,32)]))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      CONV_TAC(LAND_CONV(REWR_CONV word_zx)) THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      AP_TERM_TAC THEN
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
        can (find_term ((=) `s25:x86state`)) (concl th) ||
        can (find_term ((=) `s26:x86state`)) (concl th) ||
        can (find_term ((=) `s27:x86state`)) (concl th) ||
        can (find_term ((=) `s28:x86state`)) (concl th) ||
        can (find_term ((=) `s29:x86state`)) (concl th)))) THEN
      SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64;
               ARITH_RULE `32 <= 64`] THEN
      SIMP_TAC[WORD_POPCOUNT_WORD_ZX; DIMINDEX_8; DIMINDEX_32;
               ARITH_RULE `8 <= 32`] THEN
      REWRITE_TAC[VMOVMSKPS_POPCOUNT_EQ; BIT_NESTED_JOIN_8] THEN
      REWRITE_TAC[POPCNT_VMOVMSKPS_LEMMA] THEN
      MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS `9` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `n <= 8 ==> n < 9`) THEN
        W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        ARITH_TAC];
      DISCARD_MATCHING_ASSUMPTIONS [`read R9 s = x`] THEN STRIP_TAC] THEN

    (* SIMD↔spec: prove BEFORE DISCARD while YMM3/buffer hyps available.
       newlen (the FILTER length over SIMD coefficients) = LENGTH(REJ_SAMPLE(...))
       This is the key semantic bridge: VPERMQ+VPSHUFB+VPAND = spec's MAP+FILTER.
       The result is state-independent and survives DISCARD_OLDSTATE_TAC.
       Approach: WORD_SIMPLE_SUBWORD_CONV reduces the 256-bit VPSHUFB chain
       to clean 8-bit byte extractions from the bytes256 memory read. Then
       bytes256 → bytes(32) → MOD 2^192 → num_of_wordlist(SUB_LIST). *)
    SUBGOAL_THEN
     `FILTER (\c:int32. val c < 8380417)
        [word_subword (read YMM3 s26:int256) (0,32):int32;
         word_subword (read YMM3 s26) (32,32);
         word_subword (read YMM3 s26) (64,32);
         word_subword (read YMM3 s26) (96,32);
         word_subword (read YMM3 s26) (128,32);
         word_subword (read YMM3 s26) (160,32);
         word_subword (read YMM3 s26) (192,32);
         word_subword (read YMM3 s26) (224,32)] =
      REJ_SAMPLE(SUB_LIST(8*i,8) inlist)`
    ASSUME_TAC THENL
     [REWRITE_TAC[REJ_SAMPLE] THEN
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
        can (find_term ((=) `newlen:num`)) (concl th) ||
        can (find_term ((=) `R9`)) (concl th)))) THEN
      REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
        let c = concl th in
        not(can (find_term ((=) `YMM3`)) c &&
            can (find_term ((=) (mk_var("s26",`:x86state`)))) c) &&
        not(can (find_term ((=) `inlist:(24 word)list`)) c &&
            can (find_term (fun t ->
              try fst(dest_const t) = "num_of_wordlist" with _ -> false)) c &&
            can (find_term ((=) (mk_var("s21",`:x86state`)))) c) &&
        (can (find_term (fun t -> try let s = fst(dest_var t) in
           String.length s > 0 && s.[0] = 's' && s <> "stackpointer"
           with _ -> false)) c ||
         can (find_term ((=) `MAYCHANGE`)) c ||
         can (find_term ((=) `bytes_loaded`)) c)))) THEN
      FIRST_X_ASSUM(fun th ->
        if can (find_term ((=) `YMM3`)) (concl th) &&
           can (find_term ((=) (mk_var("s26",`:x86state`)))) (concl th) &&
           is_eq(concl th)
        then GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [th]
        else failwith "") THEN
      CONV_TAC(TOP_DEPTH_CONV
        (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV)) THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      SUBGOAL_THEN `1 * val(word(24 * i):int64) = 24 * i` SUBST1_TAC THENL
       [REWRITE_TAC[MULT_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `24 * i <= 808` THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[BYTE_JOIN_ZX; BYTE_JOIN_SUBWORD_ZX;
                  bytes256; READ_COMPONENT_COMPOSE; asword; through; read] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      SUBGOAL_THEN
        `read(memory :> bytes(word_add buf (word(24*i)),24)) s21 =
         num_of_wordlist(SUB_LIST(8*i,8) (inlist:(24 word)list))`
      ASSUME_TAC THENL
       [REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_24] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        FIRST_ASSUM(fun th ->
          if is_eq(concl th) &&
             can (find_term (fun t ->
               try fst(dest_const t) = "num_of_wordlist" with _ -> false)) (concl th) &&
             not(can (find_term (fun t ->
               try fst(dest_const t) = "SUB_LIST" with _ -> false)) (concl th)) &&
             (let s = string_of_term(concl th) in
              let n = String.length s in
              let rec has840 j = j + 2 < n &&
                (s.[j] = '8' && s.[j+1] = '4' && s.[j+2] = '0' || has840 (j+1)) in
              has840 0)
          then GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [GSYM th]
          else failwith "") THEN
        REWRITE_TAC[GSYM READ_BYTES_DIV; GSYM READ_BYTES_MOD;
                    ARITH_RULE `8 * (24 * i) = 192 * i`;
                    ARITH_RULE `8 * 24 = 192`] THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `MIN (840 - 24 * i) 24 = 24` SUBST1_TAC THENL
         [REWRITE_TAC[MIN] THEN
          UNDISCH_TAC `24 * i <= 808` THEN ARITH_TAC;
          REWRITE_TAC[ARITH_RULE `24 * 8 * i = 8 * (24 * i)`] THEN
          GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
            [GSYM(NUM_REDUCE_CONV `2 EXP (8 * 24)`)] THEN
          REWRITE_TAC[READ_BYTES_DIV; READ_BYTES_MOD] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          SUBGOAL_THEN `MIN (840 - 24 * i) 24 = 24` SUBST1_TAC THENL
           [REWRITE_TAC[MIN] THEN
            UNDISCH_TAC `24 * i <= 808` THEN ARITH_TAC;
            REFL_TAC]];
        ALL_TAC] THEN
      SUBGOAL_THEN
        `read(bytes(word_add buf (word(24*i)),32))(read memory s21) MOD
         2 EXP 192 =
         num_of_wordlist(SUB_LIST(8*i,8) (inlist:(24 word)list))`
      MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
          [GSYM(NUM_REDUCE_CONV `8 * 24`)] THEN
        REWRITE_TAC[READ_BYTES_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[MIN; ARITH_RULE `24 <= 32`];
        ALL_TAC] THEN
      ABBREV_TAC
        `n32 = read(bytes(word_add buf (word(24*i)),32))(read memory s21)` THEN
      DISCH_TAC THEN
      ASM_REWRITE_TAC[VAL_MOD_23_EQ_AND; COEFF_FROM_BYTES;
                      EL_NUM_OF_WORDLIST; NUM_OF_WORDLIST_SUB_LIST;
                      DIMINDEX_24] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      (* COEFF_BYTE_JOIN_WORD converts byte_join coefficients to word(n MOD 2^256 DIV 2^ofs MOD 2^23).
         Use GEN_REWRITE with concrete instances for each of the 8 offsets. *)
      (* Combined COEFF + MOD_256_192: byte_join coeffs → word(n32 MOD 2^192 DIV 2^k MOD 2^23) *)
      GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV)
        (map (fun k ->
          let kterm = mk_small_numeral k in
          let coeff_th = CONV_RULE NUM_REDUCE_CONV
            (SPECL [`n32:num`; kterm] COEFF_BYTE_JOIN_WORD) in
          let mod_th = CONV_RULE NUM_REDUCE_CONV
            (SPECL [`n32:num`; kterm] MOD_256_192) in
          CONV_RULE NUM_REDUCE_CONV (TRANS coeff_th (AP_TERM `word:num->int32` mod_th)))
        [0;24;48;72;96;120;144;168]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
      (* Convert huge 2^192 numeral back to 2 EXP 192 so hypothesis can match *)
      REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 192`)] THEN
      ASM_REWRITE_TAC[] THEN
      (* Prove LENGTH(SUB_LIST(8*i,8) inlist) = 8 for REJ_SAMPLE_COEFFS *)
      SUBGOAL_THEN `LENGTH(SUB_LIST(8*i,8) (inlist:(24 word)list)) = 8`
        ASSUME_TAC THENL
       [REWRITE_TAC[LENGTH_SUB_LIST] THEN
        CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
        MATCH_MP_TAC(ARITH_RULE
          `8 * i + 8 <= l ==> MIN 8 (l - 8 * i) = 8`) THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[CONV_RULE NUM_REDUCE_CONV MAP_REJ_COEFFS];
      ALL_TAC] THEN

    (* Derive LENGTH from FILTER equality for the ABBREV *)
    FIRST_X_ASSUM(fun th ->
      if can (find_term (fun t -> try fst(dest_const t) = "FILTER" with _ -> false)) (concl th) &&
         can (find_term (fun t -> try fst(dest_const t) = "REJ_SAMPLE" with _ -> false)) (concl th) &&
         is_eq(concl th) &&
         not(can (find_term ((=) `LENGTH:(int32 list)->num`)) (concl th))
      then ASSUME_TAC th THEN ASSUME_TAC(AP_TERM `LENGTH:(int32 list)->num` th)
      else failwith "not filter_eq") THEN

    (* Abbreviate the FILTER length to prevent DISCARD from seeing s26 ref *)
    ABBREV_TAC `newlen = LENGTH(FILTER (\c:int32. val c < 8380417)
        [word_subword (read YMM3 s26:int256) (0,32):int32;
         word_subword (read YMM3 s26) (32,32);
         word_subword (read YMM3 s26) (64,32);
         word_subword (read YMM3 s26) (96,32);
         word_subword (read YMM3 s26) (128,32);
         word_subword (read YMM3 s26) (160,32);
         word_subword (read YMM3 s26) (192,32);
         word_subword (read YMM3 s26) (224,32)])` THEN

    (* The hypothesis `newlen = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) inlist))`
       already exists from the SIMD subgoal proof. It's state-free and
       survives DISCARD. No need to re-derive it. *)

    (* Derive FILTER = REJ_SAMPLE BEFORE ABBREVs, while all state hyps exist.
       The SIMD subgoal proved LENGTH equality. Now prove FILTER equality
       by using read YMM3 s26 = read YMM3 s29 (unchanged through s27-s29). *)
    SUBGOAL_THEN
      `FILTER (\c:int32. val c < 8380417)
         [word_subword (read YMM3 s29:int256) (0,32):int32;
          word_subword (read YMM3 s29) (32,32);
          word_subword (read YMM3 s29) (64,32);
          word_subword (read YMM3 s29) (96,32);
          word_subword (read YMM3 s29) (128,32);
          word_subword (read YMM3 s29) (160,32);
          word_subword (read YMM3 s29) (192,32);
          word_subword (read YMM3 s29) (224,32)] =
       REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list))`
    ASSUME_TAC THENL
     [(* Use the FILTER=REJ_SAMPLE hypothesis (s26 version) to reduce to
        FILTER P [s29 lanes] = FILTER P [s26 lanes], then ASM_REWRITE closes
        because read YMM3 s29 = read YMM3 s26 (same VPAND EXPR). *)
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "FILTER" with _ -> false)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "REJ_SAMPLE" with _ -> false)) (concl th) &&
        is_eq(concl th) &&
        not(can (find_term ((=) `LENGTH:(int32 list)->num`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN

    (* Save the 8 bounds val(word_subword (read YMM3 s29) (k,32)) < 8388608
       BEFORE ABBREV substitutes coeffs_ymm3. Otherwise these bounds are
       consumed as intermediate lemmas during CMP_MASK discharge and the
       later VPERMD block's Step F picker (which looks for
       `word_subword coeffs_ymm3 (k,32) ... < 8388608`) fails with Not_found. *)
    SUBGOAL_THEN
     `val(word_subword (read YMM3 s29:int256) (0,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (32,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (64,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (96,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (128,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (160,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (192,32):int32) < 8388608 /\
      val(word_subword (read YMM3 s29:int256) (224,32):int32) < 8388608`
     STRIP_ASSUME_TAC THENL
      [FIRST_ASSUM(fun th ->
         let c = concl th in
         if is_eq c &&
            (try fst(dest_const(fst(strip_comb(rhs c)))) = "word_and" with _ -> false) &&
            (try let ops,args = strip_comb(lhs c) in
                 fst(dest_const ops) = "read" &&
                 List.length args = 2 &&
                 fst(dest_const(List.hd args)) = "YMM3"
             with _ -> false)
         then SUBST1_TAC th
         else failwith "no YMM3 word_and") THEN
       REWRITE_TAC[WORD_SUBWORD_AND] THEN
       CONV_TAC(DEPTH_CONV(WORD_SIMPLE_SUBWORD_CONV ORELSEC WORD_NUM_RED_CONV)) THEN
       REPEAT CONJ_TAC THEN
       MATCH_MP_TAC(ARITH_RULE `n <= 8388607 ==> n < 8388608`) THEN
       REWRITE_TAC[VAL_WORD_AND_WORD_LE];
       ALL_TAC] THEN

    (* Ghost state: ABBREV key s29 values before DISCARD kills them. *)
    ABBREV_TAC `coeffs_ymm3:int256 = read YMM3 s29` THEN
    ABBREV_TAC `cmp_mask:int64 = read R8 s29` THEN
    ABBREV_TAC `table_entry:int64 =
      read (memory :> bytes64 (word_add table (word (8 * val (cmp_mask:int64))))) s29` THEN

    (* Preserve cmp_mask ↔ coefficient comparison relationship.
       cmp_mask encodes which coefficients pass val < Q via VMOVMSKPS.
       This connects cmp_mask to the FILTER predicate for the brute force. *)
    SUBGOAL_THEN
      `val(cmp_mask:int64) =
       bitval(val(word_subword (coeffs_ymm3:int256) (0,32):int32) < 8380417) +
       2 * bitval(val(word_subword (coeffs_ymm3:int256) (32,32):int32) < 8380417) +
       4 * bitval(val(word_subword (coeffs_ymm3:int256) (64,32):int32) < 8380417) +
       8 * bitval(val(word_subword (coeffs_ymm3:int256) (96,32):int32) < 8380417) +
       16 * bitval(val(word_subword (coeffs_ymm3:int256) (128,32):int32) < 8380417) +
       32 * bitval(val(word_subword (coeffs_ymm3:int256) (160,32):int32) < 8380417) +
       64 * bitval(val(word_subword (coeffs_ymm3:int256) (192,32):int32) < 8380417) +
       128 * bitval(val(word_subword (coeffs_ymm3:int256) (224,32):int32) < 8380417)`
      ASSUME_TAC THENL
     [(* Use CMP_MASK_CORRECT: rewrite H31 (cmp_mask ABBREV) using GSYM H30
        (coeffs_ymm3 ABBREV) to replace the VPAND chain with coeffs_ymm3,
        then apply the lemma directly. *)
      FIRST_ASSUM(fun h30 ->
        if is_eq(concl h30) && is_var(lhs(concl h30)) &&
           (try fst(dest_var(lhs(concl h30))) = "coeffs_ymm3" with _ -> false) &&
           (try fst(dest_const(fst(strip_comb(rhs(concl h30))))) = "word_and"
            with _ -> false)
        then
          FIRST_ASSUM(fun h31 ->
            if is_eq(concl h31) && is_var(lhs(concl h31)) &&
               (try fst(dest_var(lhs(concl h31))) = "cmp_mask" with _ -> false) &&
               (try fst(dest_const(fst(strip_comb(rhs(concl h31))))) = "word_zx"
                with _ -> false)
            then
              SUBST1_TAC(REWRITE_RULE[GSYM h30] h31)
            else failwith "not h31")
        else failwith "not h30") THEN
      (* Normalize the bit-31/word_subword/word-of-sum shape to match
         CMP_MASK_CORRECT's word_of_bits form: first collapse the
         bit 31 (word_subword x (k,32)) patterns via GSYM BIT_SUBWORD_256
         (so we see bit (32k+31) of the nested word_join), then fold the
         word(sum of bitvals) via GSYM VMOVMSKPS_BYTE_EQ into word_of_bits. *)
      REWRITE_TAC[GSYM BIT_SUBWORD_256; GSYM VMOVMSKPS_BYTE_EQ] THEN
      MATCH_MP_TAC(ISPECL [
        `word_subword (coeffs_ymm3:int256) (0,32):int32`;
        `word_subword (coeffs_ymm3:int256) (32,32):int32`;
        `word_subword (coeffs_ymm3:int256) (64,32):int32`;
        `word_subword (coeffs_ymm3:int256) (96,32):int32`;
        `word_subword (coeffs_ymm3:int256) (128,32):int32`;
        `word_subword (coeffs_ymm3:int256) (160,32):int32`;
        `word_subword (coeffs_ymm3:int256) (192,32):int32`;
        `word_subword (coeffs_ymm3:int256) (224,32):int32`
      ] CMP_MASK_CORRECT) THEN
      (* Prove val(word_subword coeffs_ymm3 (k,32)) < 8388608 for each k.
         coeffs_ymm3 = word_and(big)(mask) so word_subword distributes,
         mask subword = word 8388607, then VAL_WORD_AND_WORD_LE gives bound. *)
      FIRST_ASSUM(fun h30 ->
        if is_eq(concl h30) && is_var(lhs(concl h30)) &&
           (try fst(dest_var(lhs(concl h30))) = "coeffs_ymm3" with _ -> false) &&
           (try fst(dest_const(fst(strip_comb(rhs(concl h30))))) = "word_and"
            with _ -> false)
        then SUBST1_TAC h30
        else failwith "") THEN
      REWRITE_TAC[WORD_SUBWORD_AND] THEN
      CONV_TAC(DEPTH_CONV(WORD_SIMPLE_SUBWORD_CONV ORELSEC WORD_NUM_RED_CONV)) THEN
      REPEAT CONJ_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `n <= 8388607 ==> n < 8388608`) THEN
      REWRITE_TAC[VAL_WORD_AND_WORD_LE];
      ALL_TAC] THEN

    DISCARD_OLDSTATE_TAC "s29" THEN CLARIFY_TAC THEN
    (* Step 30-32 WITHOUT discard to keep VPERMD hypothesis chain *)
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (30--32) THEN
    SUBGOAL_THEN
      `val(read YMM3 s32:int256) MOD 2 EXP (32 * newlen) =
       num_of_wordlist(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))`
      ASSUME_TAC THENL
     [(* VPERMD: apply MLDSA_VPERMD_BRIDGE (proven in defs_extra.ml)
         — replaces the former 256-case brute force, eliminating 255 cheats. *)
      (* Step A: derive val(table_entry) = (table DIV 2^(64*val cmp_mask)) MOD 2^64 *)
      SUBGOAL_THEN
        `val(table_entry:int64) =
         (num_of_wordlist mldsa_rej_uniform_table DIV
          2 EXP (64 * val(cmp_mask:int64))) MOD 2 EXP 64`
        ASSUME_TAC THENL
       [SUBGOAL_THEN
          `val(read(memory :> bytes64(word_add table (word(8 * val(cmp_mask:int64))))) s32 :int64) =
           (num_of_wordlist mldsa_rej_uniform_table DIV 2 EXP (64 * val cmp_mask)) MOD 2 EXP 64`
          MP_TAC THENL
         [MATCH_MP_TAC TABLE_ENTRY_FROM_MEMORY THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            FIRST_X_ASSUM(fun th ->
              if can (find_term ((=) `bitval`)) (concl th) && is_eq(concl th) &&
                 (try fst(dest_var(rand(lhs(concl th)))) = "cmp_mask" with _ -> false)
              then SUBST1_TAC th else failwith "") THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (0,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (32,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (64,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (96,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (128,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (160,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (192,32):int32) < 8380417` BITVAL_BOUND) THEN
            MP_TAC(SPEC `val(word_subword (coeffs_ymm3:int256) (224,32):int32) < 8380417` BITVAL_BOUND) THEN
            ARITH_TAC];
          ASM_REWRITE_TAC[]]; ALL_TAC] THEN
      (* Step B: substitute read YMM3 s32 into goal (exposes the VPERMD expansion). *)
      FIRST_X_ASSUM (fun th ->
        let s = string_of_term (concl th) in
        let n = String.length s in
        let contains needle =
          let k = String.length needle in
          let rec scan i = i + k <= n && (String.sub s i k = needle || scan (i+1)) in
          scan 0 in
        if contains "read YMM3 s32" && is_eq(concl th) && not(contains "MAYCHANGE")
        then GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th] THEN ASSUME_TAC th
        else failwith "not ymm3 s32") THEN
      (* Step C: rewrite (32 * newlen) → (32 * bitval_sum) via newlen = LENGTH(FILTER)
         and FILTER=REJ_SAMPLE; also convert RHS REJ_SAMPLE → FILTER. *)
      (fun (asl, w) ->
        let contains_s needle s =
          let n = String.length needle in let m = String.length s in
          let rec scan i = i + n <= m && (String.sub s i n = needle || scan (i+1)) in
          scan 0 in
        let b k =
          let needle = Printf.sprintf "word_subword coeffs_ymm3 (%d,32)" k in
          snd(List.find (fun (_,th) ->
            let s = string_of_term (concl th) in
            contains_s needle s && contains_s "< 8388608" s && not(contains_s "==>" s)) asl) in
        let bounds = CONJ (b 0) (CONJ (b 32) (CONJ (b 64) (CONJ (b 96) (CONJ (b 128) (CONJ (b 160) (CONJ (b 192) (b 224))))))) in
        let flt_spec = ISPECL [
          `word_subword (coeffs_ymm3:int256) (0,32):int32`;
          `word_subword (coeffs_ymm3:int256) (32,32):int32`;
          `word_subword (coeffs_ymm3:int256) (64,32):int32`;
          `word_subword (coeffs_ymm3:int256) (96,32):int32`;
          `word_subword (coeffs_ymm3:int256) (128,32):int32`;
          `word_subword (coeffs_ymm3:int256) (160,32):int32`;
          `word_subword (coeffs_ymm3:int256) (192,32):int32`;
          `word_subword (coeffs_ymm3:int256) (224,32):int32`
        ] FILTER_LENGTH_8 in
        let length_filter_eq = MP flt_spec bounds in
        let newlen_def = snd(List.find (fun (_, th) ->
          is_eq(concl th) && is_var(lhs(concl th)) &&
          (try fst(dest_var(lhs(concl th))) = "newlen" with _ -> false)) asl) in
        let filter_rej_eq = snd(List.find (fun (_, th) ->
          let s = string_of_term (concl th) in
          contains_s "FILTER" s && contains_s "REJ_SAMPLE" s && is_eq(concl th) &&
          not(contains_s "LENGTH" s) && not(contains_s "==>" s)) asl) in
        let newlen_bitval = TRANS (TRANS newlen_def
          (AP_TERM `LENGTH:int32 list -> num` (SYM filter_rej_eq))) length_filter_eq in
        REWRITE_TAC[newlen_bitval; SYM filter_rej_eq] (asl, w)) THEN
      (* Step D: fold raw memory read back to table_entry, then collapse word_zx(word_zx ...) via
         WORD_SIMPLE_SUBWORD_CONV to expose word_subword table_entry (k,3). *)
      (fun (asl, w) ->
        let contains_s needle s =
          let n = String.length needle in let m = String.length s in
          let rec scan i = i + n <= m && (String.sub s i n = needle || scan (i+1)) in
          scan 0 in
        let cm_sym =
          let th = snd(List.find (fun (_, th) ->
            is_eq(concl th) &&
            (try fst(dest_var(rand(lhs(concl th)))) = "cmp_mask" with _ -> false) &&
            contains_s "bitval" (string_of_term (concl th))) asl) in
          SYM th in
        let te_eqs = List.filter_map (fun (_, th) ->
          let s = string_of_term (concl th) in
          if is_eq(concl th) && contains_s "table_entry" s && contains_s "bytes64" s
          then Some th else None) asl in
        (REWRITE_TAC[cm_sym] THEN REWRITE_TAC te_eqs THEN
         CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) (asl, w)) THEN
      (* Step E: apply MLDSA_VPERMD_BRIDGE specialized to coeffs_ymm3 and table_entry. *)
      MATCH_MP_TAC (ISPECL [`coeffs_ymm3:int256`; `table_entry:int64`] MLDSA_VPERMD_BRIDGE) THEN
      (* Step F: discharge the antecedent using targeted rewrites (bounds + te_val + cm_sym).
         Full ASM_REWRITE_TAC hangs on the large assumption list, but this focused
         set closes the 9 antecedent conjuncts in ~2s. *)
      W(fun (asl,_) ->
        let contains_s needle s =
          let n = String.length needle in let m = String.length s in
          let rec scan i = i + n <= m && (String.sub s i n = needle || scan (i+1)) in
          scan 0 in
        let b k =
          let needle = Printf.sprintf "word_subword coeffs_ymm3 (%d,32)" k in
          snd(List.find (fun (_,th) ->
            let s = string_of_term (concl th) in
            contains_s needle s && contains_s "< 8388608" s && not(contains_s "==>" s)) asl) in
        let cm_sym =
          let th = snd(List.find (fun (_, th) ->
            is_eq(concl th) &&
            (try fst(dest_var(rand(lhs(concl th)))) = "cmp_mask" with _ -> false) &&
            contains_s "bitval" (string_of_term (concl th))) asl) in
          SYM th in
        let te_val = snd(List.find (fun (_, th) ->
          is_eq(concl th) &&
          (try let l = lhs(concl th) in
               fst(dest_comb l) = `val:int64->num` &&
               fst(dest_var(rand l)) = "table_entry"
           with _ -> false) &&
          contains_s "DIV" (string_of_term (concl th))) asl) in
        REWRITE_TAC [b 0; b 32; b 64; b 96; b 128; b 160; b 192; b 224; te_val; cm_sym]);
      ALL_TAC] THEN
    (* VSTEPS for all 3 steps to preserve bytes256 + VPERMD hyps *)
    (fun gl -> Printf.printf "  LOOP[7c]: steps 33-35 (VSTEPS)\n%!"; ALL_TAC gl) THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (33--35) THEN
    (fun gl -> Printf.printf "  LOOP[8]: steps done\n%!"; ALL_TAC gl) THEN

    (* (e) COND_CASES_TAC: continue (i+1 < N) vs exit (~(i+1 < N)) *)
    (fun gl -> Printf.printf "  DEBUG[A]: before COND_CASES_TAC\n%!"; ALL_TAC gl) THEN
    COND_CASES_TAC THENL
     [(* i+1 < N: continue looping *)
      (fun gl -> Printf.printf "  DEBUG[B]: continue branch\n%!"; ALL_TAC gl) THEN
      (* Derive new region memory content BEFORE ENSURES consumes state.
         From the bytes256 write hypothesis (VMOVDQU step), derive:
           read(memory :> bytes(addr, 32)) sN = val(bytes256 RHS)
         with address normalized (val(word curlen) → curlen).
         This is used by VPERMD_MEMORY_BRIDGE in the memory store goal. *)
      (fun (asl,w) ->
        try
          (* Find bytes256 hyp with s35 and res in address *)
          let b256_th = snd(find (fun (_,th) ->
            is_eq(concl th) &&
            can (find_term (fun t -> try fst(dest_const t) = "bytes256" with _ -> false)) (concl th) &&
            can (find_term (fun t -> try fst(dest_var t) = "res" with _ -> false)) (concl th) &&
            can (find_term (fun t -> try fst(dest_var t) = "s35" with _ -> false)) (concl th) &&
            not(can (find_term (fun t -> try fst(dest_const t) = "MAYCHANGE" with _ -> false)) (concl th))) asl) in
          (* Find read YMM3 s35 = <expr> to get clean RHS *)
          let has_const name t = try fst(dest_const t) = name with _ -> false in
          let has_var name t = try fst(dest_var t) = name with _ -> false in
          let ymm3_s35 = snd(find (fun (_,th) ->
            is_eq(concl th) &&
            can (find_term (has_var "s35")) (lhs(concl th)) &&
            can (find_term (has_const "YMM3")) (lhs(concl th)) &&
            not(can (find_term (has_const "MOD")) (concl th)) &&
            not(can (find_term (has_const "bytes256")) (concl th))) asl) in
          (* Chain: bytes256 s35 = <expr> = YMM3 s35 by transitivity *)
          let b256_ymm3 = TRANS b256_th (SYM ymm3_s35) in
          (* Normalize address: val(word curlen) → curlen *)
          let curlen_bound = snd(find (fun (_,th) ->
            try concl th = `curlen <= 248` with _ -> false) asl) in
          let mk_norm dim_thm dim_val =
            let vwe = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[dim_thm] (INST_TYPE [dim_val,`:N`] VAL_WORD_EQ)) in
            let lt = CONV_RULE NUM_REDUCE_CONV
              (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 4294967296`) curlen_bound) in
            try MATCH_MP vwe lt with _ ->
              let lt64 = CONV_RULE NUM_REDUCE_CONV
                (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 18446744073709551616`) curlen_bound) in
              MATCH_MP vwe lt64 in
          let curlen_norm_32 = mk_norm DIMINDEX_32 `:32` in
          let curlen_norm_64 = mk_norm DIMINDEX_64 `:64` in
          let b256_norm = REWRITE_RULE[curlen_norm_32; curlen_norm_64] b256_ymm3 in
          (* Convert: val(bytes256 addr s35) = val(read YMM3 s35) + address normalize *)
          let val_eq = AP_TERM `val:int256->num` b256_norm in
          let bytes32_eq = CONV_RULE(LAND_CONV(
            REWRITE_CONV[READ_COMPONENT_COMPOSE; VAL_READ_BYTES256] THENC
            REWRITE_CONV[GSYM READ_COMPONENT_COMPOSE])) val_eq in
          (* Result: read(memory :> bytes(addr,32)) s35 = val(read YMM3 s35) *)
          ASSUME_TAC bytes32_eq (asl,w)
        with e ->
          Printf.printf "  PRE-ENSURES: derivation failed: %s\n%!" (Printexc.to_string e);
          ALL_TAC (asl,w)) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      (fun gl -> Printf.printf "  DEBUG[C]: after ASM_REWRITE, before let_CONV\n%!"; ALL_TAC gl) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      (fun gl -> Printf.printf "  DEBUG[D]: after let_CONV, before iteration bounds\n%!"; ALL_TAC gl) THEN
      (* Establish iteration bounds *)
      SUBGOAL_THEN `8 * (i + 1) <= LENGTH(inlist:(24 word)list)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC;
        ALL_TAC] THEN
      (fun gl -> Printf.printf "  DEBUG[E]: before FIRST_X_ASSUM newlen subst\n%!"; ALL_TAC gl) THEN
      (* Use the SIMD↔spec result: newlen = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8)))
         ABBREV_TAC replaced FILTER... with newlen in this hypothesis *)
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq(concl th) &&
        can (find_term ((=) `newlen:num`)) (concl th) &&
        can (find_term (fun t ->
          try fst(dest_const t) = "REJ_SAMPLE" with _ -> false)) (concl th))) THEN
      (fun gl -> Printf.printf "  DEBUG[F]: before SIMD_ITERATION_BRIDGE\n%!"; ALL_TAC gl) THEN
      (* Apply SIMD_ITERATION_BRIDGE to split REJ_SAMPLE across iterations *)
      MP_TAC(ISPECL [`inlist:(24 word)list`; `i:num`; `curlist:int32 list`; `curlen:num`]
        SIMD_ITERATION_BRIDGE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      (fun gl -> Printf.printf "  DEBUG[G]: before LENGTH_APPEND rewrite\n%!"; ALL_TAC gl) THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; NUM_OF_WORDLIST_APPEND] THEN
      (fun gl -> Printf.printf "  DEBUG[H]: before DISCARD state\n%!"; ALL_TAC gl) THEN
      (* Clean state hypotheses before word arithmetic — keep MAYCHANGE and memory *)
      DISCARD_ASSUMPTIONS_TAC (fun th ->
        let c = concl th in
        (can (term_match [] `read x s = (y:num)`) c &&
         not (can (find_term (fun t -> try fst(dest_const t) = "memory" with _ -> false)) c)) ||
        can (term_match [] `bytes_loaded x y z`) c ||
        can (term_match [] `read x s <=> y`) c) THEN
      ABBREV_TAC `lenrej = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) inlist))` THEN
      (fun gl -> Printf.printf "  DEBUG[I]: before REPEAT CONJ_TAC (data goals)\n%!"; ALL_TAC gl) THEN
      REPEAT CONJ_TAC THENL
       [(* RAX: word(curlen + lenrej) — word arithmetic.
           Use targeted UNDISCH (not ASM_ARITH_TAC — hangs on ~200 asl). *)
        REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                    DIMINDEX_32; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lenrej <= 8` THEN
        SPEC_TAC(`lenrej:num`, `l:num`) THEN GEN_TAC THEN
        SPEC_TAC(`curlen:num`, `c:num`) THEN GEN_TAC THEN
        REPEAT DISCH_TAC THEN
        SUBGOAL_THEN `c < 4294967296 /\ c < 18446744073709551616 /\
                      l < 4294967296 /\ l < 18446744073709551616 /\
                      c + l < 4294967296 /\ c + l < 18446744073709551616`
          STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `c <= 248` THEN UNDISCH_TAC `l <= 8` THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
        (* RCX: word(24*(i+1)) — word arithmetic *)
        REWRITE_TAC[ARITH_RULE `24 * (i + 1) = 24 * i + 24`] THEN
        REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                    DIMINDEX_32; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        UNDISCH_TAC `24 * i <= 808` THEN
        SPEC_TAC(`24 * i`, `n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
        SUBGOAL_THEN `n < 4294967296 /\ n < 18446744073709551616 /\
                      n + 24 < 4294967296 /\ n + 24 < 18446744073709551616`
          STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `n <= 808` THEN ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
        (* Memory store: use VPERMD_MEMORY_BRIDGE
           We have (from PRE-ENSURES):
             read(memory :> bytes(addr, 32)) s35 = val(read YMM3 sN)
           And (from VPERMD):
             val(read YMM3 sN) MOD 2^(32*lenrej) = num_of_wordlist(REJ_SAMPLE(...))
           VPERMD_MEMORY_BRIDGE chains these to close the sub-read goal. *)
        (fun gl -> Printf.printf "  MEMSTORE: VPERMD_MEMORY_BRIDGE\n%!"; ALL_TAC gl) THEN
        REWRITE_TAC[DIMINDEX_32;
                    ARITH_RULE `4 * (curlen + lenrej) = 4 * curlen + 4 * lenrej`;
                    ARITH_RULE `32 * curlen = 8 * (4 * curlen)`] THEN
        REWRITE_TAC[MEMORY_BYTES_SPLIT] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
        (* Goal: read(bytes(addr, 4*lenrej)) s35 = num_of_wordlist(REJ_SAMPLE(...))
           Use VPERMD_MEMORY_BRIDGE with the PRE-ENSURES bytes32 hypothesis.
           First find the hypothesis, then build the full closing tactic. *)
        (fun (asl,w) ->
          (* Find bytes32 hyp, VPERMD MOD hyp, lenrej bound, then forward-chain *)
          try
            (* 1. bytes32 hypothesis: read(bytes(addr,32)) s35 = vr *)
            let has_const name t = try fst(dest_const t) = name with _ -> false in
            let has_var name t = try fst(dest_var t) = name with _ -> false in
            let bytes32_hyp = snd(List.find (fun (_,th) ->
              is_eq(concl th) &&
              can (find_term (fun t -> try dest_numeral t = Num.num_of_int 32 with _ -> false)) (lhs(concl th)) &&
              can (find_term (fun t -> try fst(dest_var t) = "s35" with _ -> false)) (lhs(concl th)) &&
              can (find_term (fun t -> try fst(dest_var t) = "res" with _ -> false)) (lhs(concl th)) &&
              not(can (find_term (fun t -> try fst(dest_const t) = "bytes256" with _ -> false)) (lhs(concl th)))) asl) in
            (* Find newlen = lenrej hypothesis *)
            let newlen_eq = snd(List.find (fun (_,th) ->
              try is_eq(concl th) && has_var "newlen" (lhs(concl th)) &&
                  has_var "lenrej" (rhs(concl th))
              with _ -> false) asl) in
            (* Find VPERMD MOD hyp: val(YMM3 sN) MOD 2^(32*newlen) = num_of_wordlist(...)
               May be for s34 or s33 — find the most recent one *)
            let vpermd_hyp_raw = snd(List.find (fun (_,th) ->
              is_eq(concl th) &&
              can (find_term (has_const "MOD")) (concl th) &&
              can (find_term (has_var "newlen")) (concl th) &&
              can (find_term (has_const "num_of_wordlist")) (concl th)) asl) in
            (* Normalize: replace newlen with lenrej *)
            let vpermd_hyp_1 = REWRITE_RULE[newlen_eq] vpermd_hyp_raw in
            (* The VPERMD hyp may use a different state (s34) than bytes32 (s35).
               Bridge: find read YMM3 s35 = E and read YMM3 s34 = E, chain them. *)
            let vpermd_hyp = try
              (* Find read YMM3 sN = <int256 expr> — require int256 RHS and YMM3 on LHS *)
              let is_ymm3_read th =
                is_eq(concl th) &&
                type_of(rhs(concl th)) = `:int256` &&
                can (find_term (has_const "YMM3")) (lhs(concl th)) in
              let ymm35 = snd(List.find (fun (_,th) ->
                is_ymm3_read th &&
                can (find_term (has_var "s35")) (lhs(concl th))) asl) in
              let ymm34 = snd(List.find (fun (_,th) ->
                is_ymm3_read th &&
                can (find_term (has_var "s34")) (lhs(concl th))) asl) in
              (* read YMM3 s35 = E, read YMM3 s34 = E => read YMM3 s35 = read YMM3 s34 *)
              let ymm_eq = TRANS ymm35 (SYM ymm34) in
              let val_eq = AP_TERM `val:int256->num` ymm_eq in
              (* Rewrite s34 → s35 in the VPERMD hypothesis *)
              REWRITE_RULE[GSYM val_eq] vpermd_hyp_1
            with _ ->
              vpermd_hyp_1 in
            (* 3. lenrej <= 8: directly available *)
            let lenrej_bound = snd(List.find (fun (_,th) ->
              try is_binary "<=" (concl th) &&
                  has_var "lenrej" (lhand(concl th)) &&
                  dest_small_numeral(rand(concl th)) = 8
              with _ -> false) asl) in
            (* Forward chain: MATCH_MP VPERMD_MEMORY_BRIDGE (bytes32 /\ mod /\ bound) *)
            let bridge = MATCH_MP VPERMD_MEMORY_BRIDGE
              (CONJ bytes32_hyp (CONJ vpermd_hyp lenrej_bound)) in
            REWRITE_TAC[bridge] (asl,w)
          with e ->
            Printf.printf "  MEMSTORE: failed (%s)\n%!" (Printexc.to_string e);
            failwith "memstore bridge derivation failed")];

      (* ~(i+1 < N): exit to pc+181.
         Approach: instead of DISJ_CASES on the outer disjunct, first derive
         N = i+1, then ASM_CASES on `248 < curlen + lenrej`:
           * if true: count-exit fires (JAE at s37 to pc+181) — same as old J2
           * if false: offset-exit path — VSTEPS 38-39 do CMP ecx/JA exit
         This avoids the artificial J1/J2 split that required a separate
         offset-exit proof. *)
      (fun gl -> Printf.printf "  DEBUG[J]: exit branch\n%!"; ALL_TAC gl) THEN
      SUBGOAL_THEN `N = i + 1` ASSUME_TAC THENL
       [UNDISCH_TAC `~(i + 1 < N)` THEN UNDISCH_TAC `i:num < N` THEN ARITH_TAC;
        ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (36--37) THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [(* J1: offset exit (832 < 24 * (N + 1) disjunct holds).
           Split on whether count-exit ALSO fires:
             * J1-A: 248 < curlen + lr  → JAE at s37 fires directly, same as J2.
             * J1-B: curlen + lr <= 248 → JAE falls through, CMP ecx/JA at s38-39
                     fires because 808 < 24*(i+1) (from disjunct + N=i+1). *)
        ASM_CASES_TAC
          `248 < curlen + LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))`
        THENL
         [(* J1-A: JAE at s37 fires. Derive J2's precondition, run J2 body. *)
          SUBGOAL_THEN
            `248 < LENGTH(REJ_SAMPLE(SUB_LIST(0,8 * N) (inlist:(24 word)list)))`
            ASSUME_TAC THENL
           [MP_TAC(ISPECL [`inlist:(24 word)list`; `i:num`; `curlist:int32 list`;
                            `curlen:num`] SIMD_ITERATION_BRIDGE) THEN
            ANTS_TAC THENL
             [ASM_REWRITE_TAC[] THEN
              UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC;
              ALL_TAC] THEN
            STRIP_TAC THEN
            ASM_REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                            SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; LENGTH_APPEND;
                            ADD_CLAUSES];
            ALL_TAC] THEN
          (* J1-A body is identical to J2 body; run through it.
             Must keep this in sync if J2 body changes. *)
          SUBGOAL_THEN `newlen <= 8` ASSUME_TAC THENL
           [MP_TAC(ISPECL [`inlist:(24 word)list`; `i:num`; `curlist:int32 list`;
                           `curlen:num`] SIMD_ITERATION_BRIDGE) THEN
            ANTS_TAC THENL
             [ASM_REWRITE_TAC[] THEN
              UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC;
              ALL_TAC] THEN
            STRIP_TAC THEN ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          (fun (asl,w) ->
            try
              let has_const name t = try fst(dest_const t) = name with _ -> false in
              let has_var name t = try fst(dest_var t) = name with _ -> false in
              let b256_th = snd(find (fun (_,th) ->
                is_eq(concl th) &&
                can (find_term (has_const "bytes256")) (lhs(concl th)) &&
                not(can (find_term (has_const "MAYCHANGE")) (concl th))) asl) in
              let b256_state = find_term (fun t ->
                try let n = fst(dest_var t) in
                    String.length n > 1 && n.[0] = 's' && type_of t = `:x86state`
                with _ -> false) (lhs(concl b256_th)) in
              let b256_state_name = fst(dest_var b256_state) in
              let ymm_th = snd(find (fun (_,th) ->
                is_eq(concl th) && type_of(rhs(concl th)) = `:int256` &&
                can (find_term (has_const "YMM3")) (lhs(concl th)) &&
                can (find_term (has_var b256_state_name)) (lhs(concl th))) asl) in
              let b256_ymm3 = TRANS b256_th (SYM ymm_th) in
              let curlen_bound = snd(find (fun (_,th) ->
                try concl th = `curlen <= 248` with _ -> false) asl) in
              let vwe32 = CONV_RULE NUM_REDUCE_CONV
                (REWRITE_RULE[DIMINDEX_32] (INST_TYPE [`:32`,`:N`] VAL_WORD_EQ)) in
              let vwe64 = CONV_RULE NUM_REDUCE_CONV
                (REWRITE_RULE[DIMINDEX_64] (INST_TYPE [`:64`,`:N`] VAL_WORD_EQ)) in
              let cn32 = MATCH_MP vwe32 (CONV_RULE NUM_REDUCE_CONV
                (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 4294967296`)
                  curlen_bound)) in
              let cn64 = MATCH_MP vwe64 (CONV_RULE NUM_REDUCE_CONV
                (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 18446744073709551616`)
                  curlen_bound)) in
              let b256_norm = REWRITE_RULE[cn32; cn64] b256_ymm3 in
              let val_eq = AP_TERM `val:int256->num` b256_norm in
              let bytes32_eq = CONV_RULE(LAND_CONV(
                REWRITE_CONV[READ_COMPONENT_COMPOSE; VAL_READ_BYTES256] THENC
                REWRITE_CONV[GSYM READ_COMPONENT_COMPOSE])) val_eq in
              let vpermd_raw = snd(List.find (fun (_,th) ->
                is_eq(concl th) &&
                can (find_term (has_const "MOD")) (concl th) &&
                can (find_term (has_const "num_of_wordlist")) (concl th) &&
                can (find_term (has_var "newlen")) (concl th)) asl) in
              let is_ymm3_read th =
                is_eq(concl th) && type_of(rhs(concl th)) = `:int256` &&
                can (find_term (has_const "YMM3")) (lhs(concl th)) in
              let vpermd_states = List.filter (fun v ->
                let n = fst(dest_var v) in String.length n > 1 && n.[0] = 's' &&
                type_of v = `:x86state`) (frees(concl vpermd_raw)) in
              let vp_state_name = fst(dest_var(List.hd vpermd_states)) in
              let vpermd = try
                let ymm_b32 = snd(List.find (fun (_,th) ->
                  is_ymm3_read th &&
                  can (find_term (has_var b256_state_name))
                    (lhs(concl th))) asl) in
                let ymm_vp = snd(List.find (fun (_,th) ->
                  is_ymm3_read th &&
                  can (find_term (has_var vp_state_name))
                    (lhs(concl th))) asl) in
                let ymm_eq = TRANS ymm_b32 (SYM ymm_vp) in
                let val_eq = AP_TERM `val:int256->num` ymm_eq in
                REWRITE_RULE[GSYM val_eq] vpermd_raw
              with _ -> vpermd_raw in
              let newlen_bound = snd(List.find (fun (_,th) ->
                try is_binary "<=" (concl th) &&
                    (has_var "newlen" (lhand(concl th))) &&
                    dest_small_numeral(rand(concl th)) = 8
                with _ -> false) asl) in
              let bridge = MATCH_MP VPERMD_MEMORY_BRIDGE
                (CONJ bytes32_eq (CONJ vpermd newlen_bound)) in
              ASSUME_TAC bridge (asl,w)
            with _ -> failwith "J1-A PRE-ENSURES") THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `N = i + 1` (fun th ->
            REWRITE_TAC[th; ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                           ARITH_RULE `24 * (i + 1) = 24 * i + 24`]) THENL
           [UNDISCH_TAC `~(i + 1 < N)` THEN UNDISCH_TAC `i:num < N` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; LENGTH_APPEND;
                          NUM_OF_WORDLIST_APPEND] THEN
          REWRITE_TAC[ADD_CLAUSES] THEN
          ABBREV_TAC
            `lr = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
          SUBGOAL_THEN `lr <= 8` ASSUME_TAC THENL
           [EXPAND_TAC "lr" THEN REWRITE_TAC[REJ_SAMPLE] THEN
            TRANS_TAC LE_TRANS `LENGTH(MAP (\x:24 word. word(val x MOD 2 EXP 23):int32) (SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
            REWRITE_TAC[LENGTH_FILTER; LENGTH_MAP; LENGTH_SUB_LIST] THEN
            ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `248 < curlen + lr` ASSUME_TAC THENL
           [EXPAND_TAC "lr" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC) THEN
          (fun (asl, w) ->
            try
              let newlen_eq_lr = snd(List.find (fun (_, th) ->
                let c = concl th in
                is_eq c &&
                (try fst(dest_var(lhs c)) = "newlen" with _ -> false) &&
                (try fst(dest_var(rhs c)) = "lr" with _ -> false)) asl) in
              RULE_ASSUM_TAC (REWRITE_RULE [newlen_eq_lr]) (asl, w)
            with _ -> ALL_TAC (asl, w)) THEN
          DISCARD_ASSUMPTIONS_TAC (fun th ->
            let c = concl th in
            let fvs = frees c in
            let has_const name t = try fst(dest_const t) = name with _ -> false in
            not(is_eq c &&
                can (find_term (has_const "read")) c &&
                can (find_term (has_const "bytes")) c) &&
            (not (forall (fun v -> type_of v = `:num`) fvs) ||
             exists (fun v -> let n = fst(dest_var v) in
               n = "N" || n = "newlen" || n = "curlist") fvs ||
             is_forall c)) THEN
          REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC(TAUT `p ==> (if p then a else b) = a`) THEN
            REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
                        VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                          curlen < 18446744073709551616 /\
                          lr < 18446744073709551616 /\
                          curlen + lr < 4294967296 /\
                          curlen + lr < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lr <= 8` THEN
              ARITH_TAC; ALL_TAC] THEN
            SUBGOAL_THEN `248 <= curlen + lr` ASSUME_TAC THENL
             [UNDISCH_TAC `248 < curlen + lr` THEN ARITH_TAC; ALL_TAC] THEN
            SUBGOAL_THEN `(curlen + lr) - 248 < 18446744073709551616`
              ASSUME_TAC THENL
             [UNDISCH_TAC `curlen + lr < 18446744073709551616` THEN ARITH_TAC;
              ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT; MOD_MOD_REFL] THEN
            UNDISCH_TAC `248 < curlen + lr` THEN ARITH_TAC;
            REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                          curlen < 18446744073709551616 /\
                          lr < 18446744073709551616 /\
                          curlen + lr < 4294967296 /\
                          curlen + lr < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lr <= 8` THEN
              ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
            REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            UNDISCH_TAC `24 * i <= 808` THEN
            SPEC_TAC(`24 * i`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
            SUBGOAL_THEN `n < 4294967296 /\ n < 18446744073709551616 /\
                          n + 24 < 4294967296 /\
                          n + 24 < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `n <= 808` THEN ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
            REWRITE_TAC[DIMINDEX_32;
                        ARITH_RULE `4 * (curlen + lr) = 4 * curlen + 4 * lr`;
                        ARITH_RULE `32 * curlen = 8 * (4 * curlen)`] THEN
            REWRITE_TAC[MEMORY_BYTES_SPLIT] THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
            ASM_REWRITE_TAC[] THEN NO_TAC];

          (* J1-B: JAE at s37 falls through to pc+111. VSTEPS 38-39 do CMP ecx/JA
             and exit to pc+181 because 808 < 24*(i+1) (from offset disjunct). *)
          ABBREV_TAC
            `lr = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
          SUBGOAL_THEN `lr <= 8` ASSUME_TAC THENL
           [EXPAND_TAC "lr" THEN REWRITE_TAC[REJ_SAMPLE] THEN
            TRANS_TAC LE_TRANS `LENGTH(MAP (\x:24 word. word(val x MOD 2 EXP 23):int32) (SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
            REWRITE_TAC[LENGTH_FILTER; LENGTH_MAP; LENGTH_SUB_LIST] THEN
            ARITH_TAC;
            ALL_TAC] THEN
          (* Resolve RIP s37 = word(pc + 111) via COND simplification *)
          SUBGOAL_THEN `read RIP s37 = word(pc + 111):int64` MP_TAC THENL
           [FIRST_X_ASSUM(fun th ->
              if can (find_term ((=) `read RIP s37`)) (concl th) &&
                 is_eq(concl th)
              then SUBST1_TAC th else failwith "") THEN
            MATCH_MP_TAC(TAUT `~p ==> (if p then a else b) = b`) THEN
            REWRITE_TAC[DE_MORGAN_THM; NOT_CLAUSES;
                        VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                          curlen < 18446744073709551616 /\
                          lr < 18446744073709551616 /\
                          curlen + lr < 4294967296 /\
                          curlen + lr < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lr <= 8` THEN
              ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT; MOD_MOD_REFL] THEN
            UNDISCH_TAC `~(248 < curlen + lr)` THEN
            ARITH_TAC;
            ALL_TAC] THEN
          DISCH_THEN ASSUME_TAC THEN
          FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
            let c = concl th in
            can (find_term ((=) `read RIP s37`)) c && is_eq c &&
            can (find_term (fun t ->
              try fst(dest_const t) = "COND" with _ -> false)) (rhs c))) THEN
          X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_EXEC (38--39) THEN
          (* Resolve RIP s39 = word(pc + 181) via JA analysis *)
          SUBGOAL_THEN `read RIP s39 = word(pc + 181):int64` MP_TAC THENL
           [FIRST_X_ASSUM(fun th ->
              if can (find_term ((=) `read RIP s39`)) (concl th) &&
                 is_eq(concl th)
              then SUBST1_TAC th else failwith "") THEN
            MATCH_MP_TAC(TAUT `p ==> (if p then a else b) = a`) THEN
            REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
                        VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            SUBGOAL_THEN `24 * i < 4294967296 /\ 24 * i < 18446744073709551616 /\
                          24 * i + 24 < 4294967296 /\
                          24 * i + 24 < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `24 * i <= 808` THEN ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT; MOD_MOD_REFL] THEN
            UNDISCH_TAC `832 < 24 * (N + 1)` THEN
            UNDISCH_TAC `N = i + 1` THEN ARITH_TAC;
            ALL_TAC] THEN
          DISCH_THEN ASSUME_TAC THEN
          FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
            let c = concl th in
            can (find_term ((=) `read RIP s39`)) c && is_eq c &&
            can (find_term (fun t ->
              try fst(dest_const t) = "COND" with _ -> false)) (rhs c))) THEN
          (* Rest mirrors J2's body, adapted for s39 *)
          SUBGOAL_THEN `newlen <= 8` ASSUME_TAC THENL
           [MP_TAC(ISPECL [`inlist:(24 word)list`; `i:num`; `curlist:int32 list`;
                           `curlen:num`] SIMD_ITERATION_BRIDGE) THEN
            ANTS_TAC THENL
             [ASM_REWRITE_TAC[] THEN
              UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC;
              ALL_TAC] THEN
            STRIP_TAC THEN ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          (fun (asl,w) ->
            try
              let has_const name t = try fst(dest_const t) = name with _ -> false in
              let has_var name t = try fst(dest_var t) = name with _ -> false in
              let b256_th = snd(find (fun (_,th) ->
                is_eq(concl th) &&
                can (find_term (has_const "bytes256")) (lhs(concl th)) &&
                not(can (find_term (has_const "MAYCHANGE")) (concl th))) asl) in
              let b256_state = find_term (fun t ->
                try let n = fst(dest_var t) in
                    String.length n > 1 && n.[0] = 's' && type_of t = `:x86state`
                with _ -> false) (lhs(concl b256_th)) in
              let b256_state_name = fst(dest_var b256_state) in
              let ymm_th = snd(find (fun (_,th) ->
                is_eq(concl th) && type_of(rhs(concl th)) = `:int256` &&
                can (find_term (has_const "YMM3")) (lhs(concl th)) &&
                can (find_term (has_var b256_state_name)) (lhs(concl th))) asl) in
              let b256_ymm3 = TRANS b256_th (SYM ymm_th) in
              let curlen_bound = snd(find (fun (_,th) ->
                try concl th = `curlen <= 248` with _ -> false) asl) in
              let vwe32 = CONV_RULE NUM_REDUCE_CONV
                (REWRITE_RULE[DIMINDEX_32] (INST_TYPE [`:32`,`:N`] VAL_WORD_EQ)) in
              let vwe64 = CONV_RULE NUM_REDUCE_CONV
                (REWRITE_RULE[DIMINDEX_64] (INST_TYPE [`:64`,`:N`] VAL_WORD_EQ)) in
              let cn32 = MATCH_MP vwe32 (CONV_RULE NUM_REDUCE_CONV
                (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 4294967296`)
                  curlen_bound)) in
              let cn64 = MATCH_MP vwe64 (CONV_RULE NUM_REDUCE_CONV
                (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 18446744073709551616`)
                  curlen_bound)) in
              let b256_norm = REWRITE_RULE[cn32; cn64] b256_ymm3 in
              let val_eq = AP_TERM `val:int256->num` b256_norm in
              let bytes32_eq = CONV_RULE(LAND_CONV(
                REWRITE_CONV[READ_COMPONENT_COMPOSE; VAL_READ_BYTES256] THENC
                REWRITE_CONV[GSYM READ_COMPONENT_COMPOSE])) val_eq in
              let vpermd_raw = snd(List.find (fun (_,th) ->
                is_eq(concl th) &&
                can (find_term (has_const "MOD")) (concl th) &&
                can (find_term (has_const "num_of_wordlist")) (concl th) &&
                can (find_term (has_var "newlen")) (concl th)) asl) in
              let is_ymm3_read th =
                is_eq(concl th) && type_of(rhs(concl th)) = `:int256` &&
                can (find_term (has_const "YMM3")) (lhs(concl th)) in
              let vpermd_states = List.filter (fun v ->
                let n = fst(dest_var v) in String.length n > 1 && n.[0] = 's' &&
                type_of v = `:x86state`) (frees(concl vpermd_raw)) in
              let vp_state_name = fst(dest_var(List.hd vpermd_states)) in
              let vpermd = try
                let ymm_b32 = snd(List.find (fun (_,th) ->
                  is_ymm3_read th &&
                  can (find_term (has_var b256_state_name))
                    (lhs(concl th))) asl) in
                let ymm_vp = snd(List.find (fun (_,th) ->
                  is_ymm3_read th &&
                  can (find_term (has_var vp_state_name))
                    (lhs(concl th))) asl) in
                let ymm_eq = TRANS ymm_b32 (SYM ymm_vp) in
                let val_eq = AP_TERM `val:int256->num` ymm_eq in
                REWRITE_RULE[GSYM val_eq] vpermd_raw
              with _ -> vpermd_raw in
              let newlen_bound = snd(List.find (fun (_,th) ->
                try is_binary "<=" (concl th) &&
                    (has_var "newlen" (lhand(concl th))) &&
                    dest_small_numeral(rand(concl th)) = 8
                with _ -> false) asl) in
              let bridge = MATCH_MP VPERMD_MEMORY_BRIDGE
                (CONJ bytes32_eq (CONJ vpermd newlen_bound)) in
              ASSUME_TAC bridge (asl,w)
            with _ -> failwith "J1-B PRE-ENSURES") THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `N = i + 1` (fun th ->
            REWRITE_TAC[th; ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                           ARITH_RULE `24 * (i + 1) = 24 * i + 24`]) THENL
           [UNDISCH_TAC `~(i + 1 < N)` THEN UNDISCH_TAC `i:num < N` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; LENGTH_APPEND;
                          NUM_OF_WORDLIST_APPEND] THEN
          REWRITE_TAC[ADD_CLAUSES] THEN
          (* lr already abbreviated in J1-B prologue *)
          ASM_REWRITE_TAC[] THEN
          REPEAT CONJ_TAC THENL
           [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                          curlen < 18446744073709551616 /\
                          lr < 18446744073709551616 /\
                          curlen + lr < 4294967296 /\
                          curlen + lr < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lr <= 8` THEN
              ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
            REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                        VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
            CONV_TAC NUM_REDUCE_CONV THEN
            UNDISCH_TAC `24 * i <= 808` THEN
            SPEC_TAC(`24 * i`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
            SUBGOAL_THEN `n < 4294967296 /\ n < 18446744073709551616 /\
                          n + 24 < 4294967296 /\
                          n + 24 < 18446744073709551616`
              STRIP_ASSUME_TAC THENL
             [UNDISCH_TAC `n <= 808` THEN ARITH_TAC; ALL_TAC] THEN
            ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
            REWRITE_TAC[DIMINDEX_32;
                        ARITH_RULE `4 * (curlen + lr) = 4 * curlen + 4 * lr`;
                        ARITH_RULE `32 * curlen = 8 * (4 * curlen)`] THEN
            REWRITE_TAC[MEMORY_BYTES_SPLIT] THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
            (fun (asl, w) ->
              try
                let newlen_eq_lr = snd(List.find (fun (_, th) ->
                  let c = concl th in
                  is_eq c &&
                  (try fst(dest_var(lhs c)) = "newlen" with _ -> false) &&
                  (try fst(dest_var(rhs c)) = "lr" with _ -> false)) asl) in
                RULE_ASSUM_TAC (REWRITE_RULE [newlen_eq_lr]) (asl, w)
              with _ -> ALL_TAC (asl, w)) THEN
            ASM_REWRITE_TAC[] THEN NO_TAC]];
        (* J2: 248 < LENGTH(REJ_SAMPLE(SUB_LIST(0,8*N))): count exit *)
        (* Prelude: establish newlen <= 8, needed by PRE-ENSURES *)
        SUBGOAL_THEN `newlen <= 8` ASSUME_TAC THENL
         [MP_TAC(ISPECL [`inlist:(24 word)list`; `i:num`; `curlist:int32 list`;
                         `curlen:num`] SIMD_ITERATION_BRIDGE) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `24 * (i + 1) <= 832` THEN ARITH_TAC;
            ALL_TAC] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        (* PRE-ENSURES: derive full VPERMD bridge result before ENSURES_FINAL_STATE_TAC.
           Build: read(bytes(word_add res (word(4*curlen)), 4*newlen)) sN =
                  num_of_wordlist(REJ_SAMPLE(SUB_LIST(8*i,8) inlist))
           so that ASM_REWRITE_TAC can use it after ENSURES_FINAL_STATE_TAC *)
        (fun (asl,w) ->
          try
            let has_const name t = try fst(dest_const t) = name with _ -> false in
            let has_var name t = try fst(dest_var t) = name with _ -> false in
            (* 1. Derive bytes32 eq: read(bytes(addr,32)) sN = val(YMM3 sN) *)
            let b256_th = snd(find (fun (_,th) ->
              is_eq(concl th) &&
              can (find_term (has_const "bytes256")) (lhs(concl th)) &&
              not(can (find_term (has_const "MAYCHANGE")) (concl th))) asl) in
            let b256_state = find_term (fun t ->
              try let n = fst(dest_var t) in
                  String.length n > 1 && n.[0] = 's' && type_of t = `:x86state`
              with _ -> false) (lhs(concl b256_th)) in
            let b256_state_name = fst(dest_var b256_state) in
            let ymm_th = snd(find (fun (_,th) ->
              is_eq(concl th) && type_of(rhs(concl th)) = `:int256` &&
              can (find_term (has_const "YMM3")) (lhs(concl th)) &&
              can (find_term (has_var b256_state_name)) (lhs(concl th))) asl) in
            let b256_ymm3 = TRANS b256_th (SYM ymm_th) in
            let curlen_bound = snd(find (fun (_,th) ->
              try concl th = `curlen <= 248` with _ -> false) asl) in
            let vwe32 = CONV_RULE NUM_REDUCE_CONV
              (REWRITE_RULE[DIMINDEX_32] (INST_TYPE [`:32`,`:N`] VAL_WORD_EQ)) in
            let vwe64 = CONV_RULE NUM_REDUCE_CONV
              (REWRITE_RULE[DIMINDEX_64] (INST_TYPE [`:64`,`:N`] VAL_WORD_EQ)) in
            let cn32 = MATCH_MP vwe32 (CONV_RULE NUM_REDUCE_CONV
              (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 4294967296`) curlen_bound)) in
            let cn64 = MATCH_MP vwe64 (CONV_RULE NUM_REDUCE_CONV
              (MATCH_MP (ARITH_RULE `n <= 248 ==> n < 18446744073709551616`) curlen_bound)) in
            let b256_norm = REWRITE_RULE[cn32; cn64] b256_ymm3 in
            let val_eq = AP_TERM `val:int256->num` b256_norm in
            let bytes32_eq = CONV_RULE(LAND_CONV(
              REWRITE_CONV[READ_COMPONENT_COMPOSE; VAL_READ_BYTES256] THENC
              REWRITE_CONV[GSYM READ_COMPONENT_COMPOSE])) val_eq in
            (* 2. Get VPERMD MOD hyp and bridge states *)
            let vpermd_raw = snd(List.find (fun (_,th) ->
              is_eq(concl th) &&
              can (find_term (has_const "MOD")) (concl th) &&
              can (find_term (has_const "num_of_wordlist")) (concl th) &&
              can (find_term (has_var "newlen")) (concl th)) asl) in
            let is_ymm3_read th =
              is_eq(concl th) && type_of(rhs(concl th)) = `:int256` &&
              can (find_term (has_const "YMM3")) (lhs(concl th)) in
            let vpermd_states = List.filter (fun v ->
              let n = fst(dest_var v) in String.length n > 1 && n.[0] = 's' &&
              type_of v = `:x86state`) (frees(concl vpermd_raw)) in
            let vp_state_name = fst(dest_var(List.hd vpermd_states)) in
            let vpermd = try
              let ymm_b32 = snd(List.find (fun (_,th) ->
                is_ymm3_read th &&
                can (find_term (has_var b256_state_name)) (lhs(concl th))) asl) in
              let ymm_vp = snd(List.find (fun (_,th) ->
                is_ymm3_read th &&
                can (find_term (has_var vp_state_name)) (lhs(concl th))) asl) in
              let ymm_eq = TRANS ymm_b32 (SYM ymm_vp) in
              REWRITE_RULE[GSYM(AP_TERM `val:int256->num` ymm_eq)] vpermd_raw
            with _ -> vpermd_raw in
            (* 3. Get newlen <= 8 *)
            let newlen_bound = snd(List.find (fun (_,th) ->
              try is_binary "<=" (concl th) &&
                  (has_var "newlen" (lhand(concl th))) &&
                  dest_small_numeral(rand(concl th)) = 8
              with _ -> false) asl) in
            (* 4. Forward chain VPERMD_MEMORY_BRIDGE *)
            let bridge = MATCH_MP VPERMD_MEMORY_BRIDGE
              (CONJ bytes32_eq (CONJ vpermd newlen_bound)) in
            Printf.printf "  J2 PRE-ENSURES: full bridge derived!\n%!";
            ASSUME_TAC bridge (asl,w)
          with e ->
            Printf.printf "  J2 PRE-ENSURES: failed at step (%s)\n%!" (Printexc.to_string e);
            (* Debug: count bytes256, res hyps *)
            let n_b256 = List.length (List.filter (fun (_,th) ->
              can (find_term (fun t -> try fst(dest_const t) = "bytes256" with _ -> false)) (concl th)) asl) in
            let n_res = List.length (List.filter (fun (_,th) ->
              can (find_term (fun t -> try fst(dest_var t) = "res" with _ -> false)) (concl th)) asl) in
            Printf.printf "  J2 PRE-ENSURES: %d bytes256 hyps, %d res hyps\n%!" n_b256 n_res;
            ALL_TAC (asl,w)) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
        (* Substitute N = i+1 *)
        SUBGOAL_THEN `N = i + 1` (fun th ->
          REWRITE_TAC[th; ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                         ARITH_RULE `24 * (i + 1) = 24 * i + 24`]) THENL
         [UNDISCH_TAC `~(i + 1 < N)` THEN UNDISCH_TAC `i:num < N` THEN
          ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; LENGTH_APPEND;
                        NUM_OF_WORDLIST_APPEND] THEN
        REWRITE_TAC[ADD_CLAUSES] THEN
        ABBREV_TAC `lr = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
        SUBGOAL_THEN `lr <= 8` ASSUME_TAC THENL
         [EXPAND_TAC "lr" THEN REWRITE_TAC[REJ_SAMPLE] THEN
          TRANS_TAC LE_TRANS `LENGTH(MAP (\x:24 word. word(val x MOD 2 EXP 23):32 word) (SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
          REWRITE_TAC[LENGTH_FILTER; LENGTH_MAP; LENGTH_SUB_LIST] THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `248 < curlen + lr` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o check (fun th ->
            can (find_term (fun t -> try fst(dest_const t) = "REJ_SAMPLE" with _ -> false)) (concl th) &&
            can (find_term (fun t -> try dest_small_numeral t > 200 with _ -> false)) (concl th))) THEN
          SUBGOAL_THEN `N = i + 1` (fun th -> REWRITE_TAC[th; ARITH_RULE `8 * (i + 1) = 8 * i + 8`]) THENL
           [UNDISCH_TAC `~(i + 1 < N)` THEN UNDISCH_TAC `i:num < N` THEN ARITH_TAC;
            ALL_TAC] THEN
          ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; LENGTH_APPEND] THEN
          REWRITE_TAC[ADD_CLAUSES] THEN EXPAND_TAC "lr" THEN ARITH_TAC;
          ALL_TAC] THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC) THEN
        (* Rewrite bridge with newlen = lr BEFORE DISCARD eats the connection *)
        (fun (asl, w) ->
          try
            let newlen_eq_lr = snd(List.find (fun (_, th) ->
              let c = concl th in
              is_eq c &&
              (try fst(dest_var(lhs c)) = "newlen" with _ -> false) &&
              (try fst(dest_var(rhs c)) = "lr" with _ -> false)) asl) in
            RULE_ASSUM_TAC (REWRITE_RULE [newlen_eq_lr]) (asl, w)
          with _ -> ALL_TAC (asl, w)) THEN
        DISCARD_ASSUMPTIONS_TAC (fun th ->
          let c = concl th in
          let fvs = frees c in
          let has_const name t = try fst(dest_const t) = name with _ -> false in
          (* Keep: bridge (REJ_SAMPLE/read/bytes) AND invariant (read/bytes, curlist RHS) *)
          not(is_eq c &&
              can (find_term (has_const "read")) c &&
              can (find_term (has_const "bytes")) c) &&
          (not (forall (fun v -> type_of v = `:num`) fvs) ||
           exists (fun v -> let n = fst(dest_var v) in
             n = "N" || n = "newlen" || n = "curlist") fvs ||
           is_forall c)) THEN
        REPEAT CONJ_TAC THENL
         [(* 1. JA conditional.
             Use targeted UNDISCH instead of ASM_ARITH_TAC to avoid hanging
             on the ~200-assumption list. *)
          MATCH_MP_TAC(TAUT `p ==> (if p then a else b) = a`) THEN
          REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM;
                      VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD_ADD;
                      VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                        curlen < 18446744073709551616 /\ lr < 18446744073709551616 /\
                        curlen + lr < 4294967296 /\ curlen + lr < 18446744073709551616`
            STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lr <= 8` THEN
            ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `248 <= curlen + lr` ASSUME_TAC THENL
           [UNDISCH_TAC `248 < curlen + lr` THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `(curlen + lr) - 248 < 18446744073709551616` ASSUME_TAC THENL
           [UNDISCH_TAC `curlen + lr < 18446744073709551616` THEN ARITH_TAC;
            ALL_TAC] THEN
          ASM_SIMP_TAC[MOD_LT; MOD_MOD_REFL] THEN
          UNDISCH_TAC `248 < curlen + lr` THEN ARITH_TAC;
          (* 2. RAX *)
          REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                      VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          SUBGOAL_THEN `curlen < 4294967296 /\ lr < 4294967296 /\
                        curlen < 18446744073709551616 /\ lr < 18446744073709551616 /\
                        curlen + lr < 4294967296 /\ curlen + lr < 18446744073709551616`
            STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `curlen <= 248` THEN UNDISCH_TAC `lr <= 8` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
          (* 3. RCX *)
          REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD;
                      VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          UNDISCH_TAC `24 * i <= 808` THEN
          SPEC_TAC(`24 * i`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
          SUBGOAL_THEN `n < 4294967296 /\ n < 18446744073709551616 /\
                        n + 24 < 4294967296 /\ n + 24 < 18446744073709551616`
            STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `n <= 808` THEN ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
          (* 4. Memory store — bridge theorem from PRE-ENSURES is in assumptions *)
          (fun gl -> Printf.printf "  MEMSTORE(J2): using bridge from PRE-ENSURES\n%!"; ALL_TAC gl) THEN
          REWRITE_TAC[DIMINDEX_32;
                      ARITH_RULE `4 * (curlen + lr) = 4 * curlen + 4 * lr`;
                      ARITH_RULE `32 * curlen = 8 * (4 * curlen)`] THEN
          REWRITE_TAC[MEMORY_BYTES_SPLIT] THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[EQ_ADD_LCANCEL; EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
          ASM_REWRITE_TAC[] THEN NO_TAC]]];

    (* ================================================================= *)
    (* Subgoal 3: Post-loop                                              *)
    (* ================================================================= *)
    (fun gl -> Printf.printf "  DEBUG[K]: post-loop\n%!"; ALL_TAC gl) THEN
    (* ================================================================= *)
    (* Subgoal 3: Post-loop (scalar loop + VZEROUPPER + RET)             *)
    (*                                                                   *)
    (* Entry: pc+181 with REJ_SAMPLE(SUB_LIST(0,8*N)) accumulated.      *)
    (* Code structure:                                                  *)
    (*   pc+181: CMP eax,256; JAE vzeroupper                           *)
    (*   pc+188: CMP ecx,837; JA vzeroupper                            *)
    (*   pc+196..240: scalar coefficient loop (≤ 8 iterations)         *)
    (*   pc+242: VZEROUPPER                                             *)
    (*                                                                   *)
    (* Preparation: abbreviate outlist/outlen, establish bounds.        *)
    (* ================================================================= *)
    (fun gl -> Printf.printf "  DEBUG[L]: post-loop preamble start\n%!"; ALL_TAC gl) THEN
    CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
    MAP_EVERY ABBREV_TAC
     [`outlist = REJ_SAMPLE (SUB_LIST (0,8 * N) inlist)`;
      `outlen = LENGTH(outlist:int32 list)`] THEN
    (* Save LENGTH(REJ_SAMPLE(...)) = outlen before ABBREV consumes the connection *)
    SUBGOAL_THEN
     `LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * N) (inlist:(24 word)list))) = outlen`
     ASSUME_TAC THENL
     [UNDISCH_TAC `REJ_SAMPLE (SUB_LIST (0,8 * N) (inlist:(24 word)list)) = outlist` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `LENGTH (outlist:int32 list) = outlen` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    (* Derive 24*N <= 832 and LENGTH(REJ_SAMPLE(SUB_LIST(0, 8*(N-1)))) <= 248 *)
    SUBGOAL_THEN
     `24 * N <= 832 /\
      LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * (N - 1)) (inlist:(24 word)list))) <= 248`
     STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
      ANTS_TAC THENL [UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(N - 1) + 1 = N` SUBST1_TAC THENL
       [UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    (* Derive outlen <= 256 via SIMD_ITERATION_BRIDGE at (N-1) *)
    SUBGOAL_THEN `outlen <= 256` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`inlist:(24 word)list`; `N - 1`;
                     `REJ_SAMPLE(SUB_LIST(0, 8*(N-1)) (inlist:(24 word)list))`;
                     `LENGTH(REJ_SAMPLE(SUB_LIST(0, 8*(N-1)) (inlist:(24 word)list)))`]
        SIMD_ITERATION_BRIDGE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[] THEN
        SUBGOAL_THEN `N - 1 + 1 = N` SUBST1_TAC THENL
         [UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `LENGTH (inlist:(24 word)list) = 280` THEN
        UNDISCH_TAC `24 * N <= 832` THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `N - 1 + 1 = N` SUBST1_TAC THENL
       [UNDISCH_TAC `~(N = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN
      UNDISCH_TAC
        `LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * N) (inlist:(24 word)list))) = outlen` THEN
      UNDISCH_TAC
        `LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N) (inlist:(24 word)list))) =
         LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * (N - 1)) inlist)) +
         LENGTH (REJ_SAMPLE (SUB_LIST (8 * (N - 1),8) inlist))` THEN
      UNDISCH_TAC
        `LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * (N - 1)) (inlist:(24 word)list))) <= 248` THEN
      UNDISCH_TAC
        `LENGTH (REJ_SAMPLE (SUB_LIST (8 * (N - 1),8) (inlist:(24 word)list))) <= 8` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    (fun gl -> Printf.printf "  DEBUG[M]: bounds derived, before WOP\n%!"; ALL_TAC gl) THEN
    (* Characterize the number of scalar iterations K via WOP.
       K = smallest j such that LENGTH(REJ_SAMPLE(SUB_LIST(0,8*N+j))) >= 256 OR 837 < 24*N+3*j. *)
    SUBGOAL_THEN
      `?j. 256 <= LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * N + j) (inlist:(24 word)list))) \/
           837 < 24 * N + 3 * j`
      MP_TAC THENL
     [EXISTS_TAC `280:num` THEN DISJ2_TAC THEN
      UNDISCH_TAC `24 * N <= 832` THEN ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th ->
      ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LE; NOT_LT] th)) THEN
    (fun gl -> Printf.printf "  DEBUG[N]: WOP done, K defined\n%!"; ALL_TAC gl) THEN
    (* Case split: K = 0 (no scalar iterations) vs K > 0 (scalar loop) *)
    ASM_CASES_TAC `K = 0` THENL
     [(fun gl -> Printf.printf "  DEBUG[O]: K=0 case\n%!"; ALL_TAC gl) THEN
      (* K = 0: Must have outlen = 256 (since 24*N <= 832 rules out offset exit at K=0). *)
      SUBGOAL_THEN `outlen = 256` ASSUME_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `K = 0`; ADD_CLAUSES; MULT_CLAUSES]) THEN
        UNDISCH_TAC
          `256 <= LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N) (inlist:(24 word)list))) \/
           837 < 24 * N` THEN
        UNDISCH_TAC
          `LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * N) (inlist:(24 word)list))) = outlen` THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        UNDISCH_TAC `outlen <= 256` THEN
        UNDISCH_TAC `24 * N <= 832` THEN ARITH_TAC;
        ALL_TAC] THEN
      (* Apply case A proof: JAE fires to pc+242 *)
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [40;41] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `outlen = 256`]) THEN
      FIRST_X_ASSUM(fun th ->
        if (try let s = string_of_term (concl th) in String.length s > 20 &&
                String.sub s 0 11 = "read RIP s4" with _ -> false) &&
           is_eq(concl th)
        then ASSUME_TAC(CONV_RULE(RAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) th)
        else failwith "not RIP") THEN
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [55] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `SUB_LIST (0,256) (REJ_SAMPLE (inlist:(24 word)list)) =
                    REJ_SAMPLE (SUB_LIST (0, 8 * N) inlist)`
        ASSUME_TAC THENL
       [MATCH_MP_TAC REJ_SAMPLE_PREFIX_256 THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
        `REJ_SAMPLE (SUB_LIST (0,8 * N) (inlist:(24 word)list)) = outlist` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `LENGTH (outlist:int32 list) = outlen` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[];

      (fun gl -> Printf.printf "  DEBUG[P]: K>0 case, before WHILE_UP2\n%!"; ALL_TAC gl) THEN
      (* K > 0: scalar loop runs K times. Use ENSURES_WHILE_UP2_TAC. *)
      ENSURES_WHILE_UP2_TAC `K:num` `pc + 181` `pc + 242`
        `\i s. read RSP s = stackpointer /\
               read (memory :> bytes (buf,840)) s = num_of_wordlist inlist /\
               read (memory :> bytes (table,2048)) s =
                 num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
               read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
               read YMM0 s =
                 word 115366376096492355175489748997433888275274855593258845241081954797768348401920 /\
               read YMM1 s =
                 word 226156397384342666605459106258636701594091082888230722833791023177481060351 /\
               read YMM2 s =
                 word 225935595421087293402315996791205668696012104344015382954355885915737415681 /\
               (let outlist_i = REJ_SAMPLE(SUB_LIST(0, 8 * N + i) (inlist:(24 word)list)) in
                let outlen_i = LENGTH outlist_i in
                read RAX s = word outlen_i /\
                read RCX s = word(24 * N + 3 * i) /\
                read(memory :> bytes(res, 4 * outlen_i)) s = num_of_wordlist outlist_i)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [(fun gl -> Printf.printf "  DEBUG[Q]: WHILE init\n%!"; ALL_TAC gl) THEN
        (* Init: precond -> invariant @ 0 *)
        ENSURES_INIT_TAC "s0" THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN ASM_REWRITE_TAC[];

        (fun gl -> Printf.printf "  DEBUG[R]: WHILE body via SCALAR_BODY_LEMMA\n%!"; ALL_TAC gl) THEN
        (* Body: invariant @ i -> invariant @ (i+1) at pc+181 or pc+242.
           Discharge via SCALAR_BODY_LEMMA, which packages the full iteration:
             CMP eax,256; JAE (not taken), CMP ecx,837; JA (not taken),
             MOVZX + OR + AND + ADD + CMP Q + JAE (either back or continue),
             MOV + ADD + JMP back.
           The wrapper specializes N,K,i,inlist,res,buf,table,pc,stackpointer.
           The (forall j < K. ...) precondition is discharged from the WOP
           assumption `!m. m < K ==> ~(256 <= LENGTH(...)) /\ ~(837 < 24*N+3*m)`. *)
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        REWRITE_TAC[GSYM SOME_FLAGS] THEN
        MATCH_MP_TAC SCALAR_BODY_LEMMA THEN
        ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
        CONJ_TAC THENL
         [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
          ASM_REWRITE_TAC[] THEN ARITH_TAC;
          (* WOP disjunct at K *)
          FIRST_X_ASSUM(MATCH_ACCEPT_TAC o check (fun th ->
            let c = concl th in is_disj c &&
            can (find_term ((=) `256 <= LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list)))`)) c))];

        (fun gl -> Printf.printf "  DEBUG[S]: WHILE post\n%!"; ALL_TAC gl) THEN
        (* Post: invariant @ K -> postcondition.
           At i=K, exit condition fires. RIP = pc+242 (vzeroupper). *)
        ENSURES_INIT_TAC "s0" THEN
        (* Break out the invariant conjunction *)
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
        FIRST_X_ASSUM(fun th ->
          let c = concl th in
          if is_conj c && (try can (find_term ((=) `LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list)))`)) c with _ -> false)
          then STRIP_ASSUME_TAC th else failwith "not inv") THEN
        (* VZEROUPPER *)
        X86_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [55] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        (fun gl -> Printf.printf "  DEBUG[T]: post - before DISJ_CASES\n%!"; ALL_TAC gl) THEN
        (* The disjunct at K: either count-exit (256 <= outlen_K) or offset-exit (837 < 24*N+3*K) *)
        FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
         [(fun gl -> Printf.printf "  DEBUG[U]: post count-exit\n%!"; ALL_TAC gl) THEN
          (* count-exit case: 256 <= outlen_K. Since outlen is monotonic +0/+1 per scalar iter,
             and outlen_{K-1} < 256 (from WOP), we have outlen_K = 256. *)
          SUBGOAL_THEN
            `LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list))) = 256`
            ASSUME_TAC THENL
           [(* Monotonicity: LENGTH(REJ_SAMPLE(SUB_LIST(0, 8*N + K-1))) < 256 (from WOP)
               and REJ_SAMPLE_STEP_LE gives LENGTH(...K) <= LENGTH(...K-1) + 1 <= 256.
               Combined with 256 <= LENGTH(...K) gives equality. *)
            FIRST_X_ASSUM(MP_TAC o SPEC `K - 1`) THEN
            ANTS_TAC THENL [UNDISCH_TAC `~(K = 0)` THEN ARITH_TAC; ALL_TAC] THEN
            MP_TAC(ISPECL [`inlist:(24 word)list`; `8 * N + K - 1`] REJ_SAMPLE_STEP_LE) THEN
            SUBGOAL_THEN `(8 * N + K - 1) + 1 = 8 * N + K` SUBST1_TAC THENL
             [UNDISCH_TAC `~(K = 0)` THEN ARITH_TAC; ALL_TAC] THEN
            UNDISCH_TAC
              `256 <= LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list)))` THEN
            ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `SUB_LIST (0,256) (REJ_SAMPLE (inlist:(24 word)list)) =
                        REJ_SAMPLE (SUB_LIST (0, 8 * N + K) inlist)`
            ASSUME_TAC THENL
           [MATCH_MP_TAC REJ_SAMPLE_PREFIX_256 THEN ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `SUB_LIST (0,256) (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list))) =
                        REJ_SAMPLE (SUB_LIST (0,8 * N + K) inlist)`
            SUBST1_TAC THENL
           [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[LE_REFL];
            ALL_TAC] THEN
          (* Rewrite memory hyp using LENGTH = 256 *)
          RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
            `LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list))) = 256`]) THEN
          ASM_REWRITE_TAC[];

          (fun gl -> Printf.printf "  DEBUG[V]: post offset-exit\n%!"; ALL_TAC gl) THEN
          (* offset-exit case: 837 < 24*N+3*K. Need to handle whether count-exit also fires. *)
          ASM_CASES_TAC
            `256 <= LENGTH(REJ_SAMPLE(SUB_LIST(0, 8 * N + K) (inlist:(24 word)list)))`
          THENL
           [(fun gl -> Printf.printf "  DEBUG[W]: post both-exits\n%!"; ALL_TAC gl) THEN
            (* Both conditions: 256 <= outlen_K. Derive outlen_K = 256 via monotonicity,
               then reduce to case A. *)
            SUBGOAL_THEN
              `LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list))) = 256`
              ASSUME_TAC THENL
             [FIRST_X_ASSUM(MP_TAC o SPEC `K - 1`) THEN
              ANTS_TAC THENL [UNDISCH_TAC `~(K = 0)` THEN ARITH_TAC; ALL_TAC] THEN
              MP_TAC(ISPECL [`inlist:(24 word)list`; `8 * N + K - 1`] REJ_SAMPLE_STEP_LE) THEN
              SUBGOAL_THEN `(8 * N + K - 1) + 1 = 8 * N + K` SUBST1_TAC THENL
               [UNDISCH_TAC `~(K = 0)` THEN ARITH_TAC; ALL_TAC] THEN
              UNDISCH_TAC
                `256 <= LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list)))` THEN
              ARITH_TAC;
              ALL_TAC] THEN
            SUBGOAL_THEN `SUB_LIST (0,256) (REJ_SAMPLE (inlist:(24 word)list)) =
                          REJ_SAMPLE (SUB_LIST (0, 8 * N + K) inlist)`
              ASSUME_TAC THENL
             [MATCH_MP_TAC REJ_SAMPLE_PREFIX_256 THEN ASM_REWRITE_TAC[];
              ALL_TAC] THEN
            ASM_REWRITE_TAC[] THEN
            SUBGOAL_THEN `SUB_LIST (0,256) (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list))) =
                          REJ_SAMPLE (SUB_LIST (0,8 * N + K) inlist)`
              SUBST1_TAC THENL
             [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[LE_REFL];
              ALL_TAC] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
              `LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list))) = 256`]) THEN
            ASM_REWRITE_TAC[];

            (fun gl -> Printf.printf "  DEBUG[X]: post offset-only\n%!"; ALL_TAC gl) THEN
            (* Only offset-exit: outlen_K < 256 and 24*N+3*K > 837.
               Then 8*N+K >= 280 (bytes consumed past input), so SUB_LIST = inlist. *)
            SUBGOAL_THEN `SUB_LIST (0, 8 * N + K) (inlist:(24 word)list) = inlist`
              SUBST1_TAC THENL
             [MATCH_MP_TAC SUB_LIST_REFL THEN
              UNDISCH_TAC `LENGTH (inlist:(24 word)list) = 280` THEN
              UNDISCH_TAC `837 < 24 * N + 3 * K` THEN ARITH_TAC;
              ALL_TAC] THEN
            SUBGOAL_THEN `LENGTH (REJ_SAMPLE (inlist:(24 word)list)) <= 256`
              ASSUME_TAC THENL
             [UNDISCH_TAC
                `~(256 <= LENGTH (REJ_SAMPLE (SUB_LIST (0,8 * N + K) (inlist:(24 word)list))))` THEN
              SUBGOAL_THEN `SUB_LIST (0, 8 * N + K) (inlist:(24 word)list) = inlist`
                SUBST1_TAC THENL
               [MATCH_MP_TAC SUB_LIST_REFL THEN
                UNDISCH_TAC `LENGTH (inlist:(24 word)list) = 280` THEN
                UNDISCH_TAC `837 < 24 * N + 3 * K` THEN ARITH_TAC;
                ALL_TAC] THEN
              ARITH_TAC;
              ALL_TAC] THEN
            SUBGOAL_THEN `SUB_LIST (0,256) (REJ_SAMPLE (inlist:(24 word)list)) = REJ_SAMPLE inlist`
              SUBST1_TAC THENL
             [MATCH_MP_TAC SUB_LIST_REFL THEN ASM_REWRITE_TAC[];
              ALL_TAC] THEN
            REWRITE_TAC[] THEN
            (* Memory closure: rewrite SUB_LIST = inlist in the memory hypothesis and accept.
               We have to build the SUB_LIST_REFL fact without `prove` (which starts a fresh
               proof without access to current asl hypotheses). *)
            (fun (asl, w) ->
              try
                let has_const name t = try fst(dest_const t) = name with _ -> false in
                let has_var name t = try fst(dest_var t) = name with _ -> false in
                let mem_hyp = snd(List.find (fun (_, th) ->
                  let c = concl th in
                  is_eq c &&
                  can (find_term (has_const "REJ_SAMPLE")) c &&
                  can (find_term (has_const "bytes")) c &&
                  can (find_term (has_const "memory")) c &&
                  can (find_term (has_var "res")) c) asl) in
                let len280 = snd(List.find (fun (_, th) ->
                  concl th = `LENGTH (inlist:(24 word)list) = 280`) asl) in
                let off837 = snd(List.find (fun (_, th) ->
                  concl th = `837 < 24 * N + 3 * K`) asl) in
                let bound_th = MP (MP
                  (ARITH_RULE `LENGTH (inlist:(24 word)list) = 280
                               ==> 837 < 24 * N + 3 * K
                               ==> LENGTH inlist <= 8 * N + K`) len280) off837 in
                let sub_eq = MATCH_MP
                  (ISPECL [`inlist:(24 word)list`; `8 * N + K`] SUB_LIST_REFL)
                  bound_th in
                let mem_hyp' = REWRITE_RULE[sub_eq] mem_hyp in
                ACCEPT_TAC mem_hyp' (asl, w)
              with _ -> failwith "memory finalize failed")]]]]]);;
(* DISABLED: original count exit + post-loop for debugging *)
(* ORIGINAL_J2:
        (* The first JA fires because curlen + newlen > 248 *)
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
        (* Resolve the JA conditional: prove curlen + newlen > 248 *)
        (* Key fact: curlen + newlen = LENGTH(REJ_SAMPLE(SUB_LIST(0,8*N))) > 248 *)
        SUBGOAL_THEN `248 < curlen + LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))`
          ASSUME_TAC THENL
         [MP_TAC(ASSUME `248 < LENGTH(REJ_SAMPLE(SUB_LIST(0,8 * N) inlist))`) THEN
          SUBGOAL_THEN `N = i + 1`
            (fun th -> REWRITE_TAC[th; ARITH_RULE `8 * (i + 1) = 8 * i + 8`]) THENL
           [UNDISCH_TAC `~(i + 1 < N)` THEN UNDISCH_TAC `i:num < N` THEN ARITH_TAC;
            ALL_TAC] THEN
          ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; LENGTH_APPEND;
                          ADD_CLAUSES] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        (* Use the bound to resolve the JA word comparison.
           Generalize over curlen and newlen to pure arithmetic. *)
        ABBREV_TAC `lr = LENGTH(REJ_SAMPLE(SUB_LIST(8*i,8) (inlist:(24 word)list)))` THEN
        UNDISCH_TAC `248 < curlen + lr` THEN
        UNDISCH_TAC `curlen <= 248` THEN
        SUBGOAL_THEN `lr <= 8` MP_TAC THENL
         [EXPAND_TAC "lr" THEN
          MP_TAC(ISPECL [`inlist:(24 word)list`; `i:num`; `curlist:int32 list`; `curlen:num`]
            SIMD_ITERATION_BRIDGE) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        (* Generalize to pure arithmetic, then resolve word comparison *)
        SPEC_TAC(`lr:num`, `lr:num`) THEN GEN_TAC THEN
        SPEC_TAC(`curlen:num`, `c:num`) THEN GEN_TAC THEN
        REPEAT DISCH_TAC THEN
        REWRITE_TAC[NOT_CLAUSES; DE_MORGAN_THM] THEN
        REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_SUB_CASES; VAL_WORD_ADD;
                    VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `c MOD 4294967296 = c /\ lr MOD 4294967296 = lr`
          (fun th -> REWRITE_TAC[th]) THENL
         [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `c MOD 18446744073709551616 = c /\
                      lr MOD 18446744073709551616 = lr`
          (fun th -> REWRITE_TAC[th]) THENL
         [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(c + lr) MOD 18446744073709551616 = c + lr`
          (fun th -> REWRITE_TAC[th]) THENL
         [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[MOD_MOD_REFL] THEN
        SUBGOAL_THEN `248 <= c + lr` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_OF_NUM_SUB THEN ASM_REWRITE_TAC[];
          ASM_ARITH_TAC]]];

    (fun gl -> Printf.printf "  DEBUG[K]: reached post-loop section\n%!"; ALL_TAC gl) THEN
    (* ================================================================= *)
    (* Subgoal 3: Post-loop (scalar loop + VZEROUPPER + RET)             *)
    (*                                                                   *)
    (* Entry: pc+181 with REJ_SAMPLE(SUB_LIST(0,8*N)) accumulated.      *)
    (* Code: CMP eax,256; JNB vzeroupper                                 *)
    (*        CMP ecx,837; JA vzeroupper                                 *)
    (*        scalar coefficient loop (MOVZX+SHL+OR+AND+CMP+JNB+MOV)    *)
    (*        VZEROUPPER; (implicit RET via BUTLAST)                     *)
    (* ================================================================= *)
    CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
    MAP_EVERY ABBREV_TAC
     [`outlist = REJ_SAMPLE (SUB_LIST (0,8 * N) inlist)`;
      `outlen = LENGTH(outlist:int32 list)`] THEN
    (* Bound outlen for word arithmetic *)
    SUBGOAL_THEN `outlen <= 280` ASSUME_TAC THENL
     [EXPAND_TAC "outlen" THEN EXPAND_TAC "outlist" THEN
      REWRITE_TAC[REJ_SAMPLE] THEN
      W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
      REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    CHEAT_TAC  --- end of disabled code *)
