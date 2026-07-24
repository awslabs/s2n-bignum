(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Use hint to correct high bits of decomposition (ML-DSA, param 44).        *)
(* x86_64 AVX2 variant (GAMMA2 = (Q-1)/88).                                  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* x86-specific SIMD block/lane memory lemmas (typed over x86state, so kept
   here rather than in the arch-shared common/mlkem_mldsa.ml). Depend on
   ADDR_SPLIT and pack8 from that shared file. *)

(* A coefficient (bytes32) read is the matching lane of the block (bytes256) read. *)
let BLOCK_SPLIT = prove(
  `!p:int64 s:x86state b. !k. k < 8 ==>
      read (memory :> bytes32 (word_add p (word(4*(8*b+k))))) s =
      word_subword (read (memory :> bytes256 (word_add p (word(32*b)))) s) (32*k,32):int32`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV(READ_MEMORY_MERGE_CONV 3))) THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [ADDR_SPLIT] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_RULE `word_add q (word 0) = q`] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* The block (bytes256) read assembles from its eight coefficient reads. *)
let PACK8_MERGE = prove(
  `!(x:num->int32) p:int64 s:x86state b.
      b < 32 /\
      (!i. i < 256 ==> read(memory :> bytes32(word_add p (word(4*i)))) s = x i)
      ==> read (memory :> bytes256 (word_add p (word(32*b)))) s = pack8 x b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pack8] THEN
  CONV_TAC(LAND_CONV(READ_MEMORY_MERGE_CONV 3)) THEN
  SUBGOAL_THEN
   `!k. k < 8 ==> read (memory :> bytes32 (word_add (word_add p (word(32*b))) (word(4*k)))) (s:x86state) = x(8*b+k)`
   (fun th ->
      MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th) THEN
      MP_TAC(SPEC `4` th) THEN MP_TAC(SPEC `5` th) THEN MP_TAC(SPEC `6` th) THEN MP_TAC(SPEC `7` th)) THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM ADDR_SPLIT] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `8*b+k` th)) THEN
    ANTS_TAC THENL [UNDISCH_TAC `b:num<32` THEN UNDISCH_TAC `k:num<8` THEN ARITH_TAC; SIMP_TAC[]];
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_RULE `word_add q (word 0) = q`] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC]);;

(**** print_literal_from_elf "x86/mldsa/mldsa_poly_use_hint_88.o";;
 ****)

let mldsa_poly_use_hint_88_mc = define_assert_from_elf
 "mldsa_poly_use_hint_88_mc" "x86/mldsa/mldsa_poly_use_hint_88.o"
(* BYTECODE START *)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb9; 0x7f; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 127)) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc5; 0xd1; 0xef; 0xed;  (* VPXOR (%_% xmm5) (%_% xmm5) (%_% xmm5) *)
  0x41; 0xb8; 0x0b; 0x2c; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 11275)) *)
  0xc4; 0x41; 0x79; 0x6e; 0xc0;
                           (* VMOVD (%_% xmm8) (% r8d) *)
  0xc4; 0x42; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm8) (%_% xmm8) *)
  0xc5; 0xf9; 0x6e; 0xe1;  (* VMOVD (%_% xmm4) (% ecx) *)
  0xb9; 0x00; 0x6c; 0x7e; 0x00;
                           (* MOV (% ecx) (Imm32 (word 8285184)) *)
  0x41; 0xb9; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r9d) (Imm32 (word 128)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xf9;
                           (* VMOVD (%_% xmm7) (% r9d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xff;
                           (* VPBROADCASTD (%_% ymm7) (%_% xmm7) *)
  0x41; 0xba; 0x2b; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 43)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xf2;
                           (* VMOVD (%_% xmm6) (% r10d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xf6;
                           (* VPBROADCASTD (%_% ymm6) (%_% xmm6) *)
  0xc5; 0xf9; 0x6e; 0xd9;  (* VMOVD (%_% xmm3) (% ecx) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xe4;
                           (* VPBROADCASTD (%_% ymm4) (%_% xmm4) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xc5; 0xfd; 0x6f; 0x07;  (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0x0e;  (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0x5d; 0xfe; 0xd0;  (* VPADDD (%_% ymm10) (%_% ymm4) (%_% ymm0) *)
  0xc4; 0xc1; 0x2d; 0x72; 0xd2; 0x07;
                           (* VPSRLD (%_% ymm10) (%_% ymm10) (Imm8 (word 7)) *)
  0xc4; 0x41; 0x2d; 0xe4; 0xd0;
                           (* VPMULHUW (%_% ymm10) (%_% ymm10) (%_% ymm8) *)
  0xc4; 0x62; 0x2d; 0x0b; 0xd7;
                           (* VPMULHRSW (%_% ymm10) (%_% ymm10) (%_% ymm7) *)
  0xc5; 0x7d; 0x66; 0xdb;  (* VPCMPGTD (%_% ymm11) (%_% ymm0) (%_% ymm3) *)
  0xc4; 0x41; 0x25; 0xdf; 0xca;
                           (* VPANDN (%_% ymm9) (%_% ymm11) (%_% ymm10) *)
  0xc4; 0xc1; 0x1d; 0x72; 0xf2; 0x01;
                           (* VPSLLD (%_% ymm12) (%_% ymm10) (Imm8 (word 1)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xe2;
                           (* VPADDD (%_% ymm12) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xc1; 0x2d; 0x72; 0xf4; 0x05;
                           (* VPSLLD (%_% ymm10) (%_% ymm12) (Imm8 (word 5)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd4;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm12) *)
  0xc4; 0xc1; 0x2d; 0x72; 0xf2; 0x0b;
                           (* VPSLLD (%_% ymm10) (%_% ymm10) (Imm8 (word 11)) *)
  0xc4; 0xc1; 0x7d; 0xfa; 0xc2;
                           (* VPSUBD (%_% ymm0) (%_% ymm0) (%_% ymm10) *)
  0xc4; 0xc1; 0x7d; 0xfe; 0xc3;
                           (* VPADDD (%_% ymm0) (%_% ymm0) (%_% ymm11) *)
  0xc5; 0xfd; 0x66; 0xc5;  (* VPCMPGTD (%_% ymm0) (%_% ymm0) (%_% ymm5) *)
  0xc5; 0xfd; 0xdf; 0xc1;  (* VPANDN (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0x72; 0xf0; 0x01;
                           (* VPSLLD (%_% ymm0) (%_% ymm0) (Imm8 (word 1)) *)
  0xc5; 0xf5; 0xfa; 0xc0;  (* VPSUBD (%_% ymm0) (%_% ymm1) (%_% ymm0) *)
  0xc4; 0xc1; 0x7d; 0xfe; 0xc1;
                           (* VPADDD (%_% ymm0) (%_% ymm0) (%_% ymm9) *)
  0xc4; 0xe3; 0x7d; 0x4c; 0xc6; 0x00;
                           (* VPBLENDVB (%_% ymm0) (%_% ymm0) (%_% ymm6) (%_% ymm0) *)
  0xc5; 0xfd; 0x66; 0xce;  (* VPCMPGTD (%_% ymm1) (%_% ymm0) (%_% ymm6) *)
  0xc5; 0xf5; 0xdf; 0xc0;  (* VPANDN (%_% ymm0) (%_% ymm1) (%_% ymm0) *)
  0xc5; 0xfd; 0x7f; 0x07;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm0) *)
  0x48; 0x83; 0xc7; 0x20;  (* ADD (% rdi) (Imm8 (word 32)) *)
  0x48; 0x83; 0xc6; 0x20;  (* ADD (% rsi) (Imm8 (word 32)) *)
  0x48; 0x83; 0xc0; 0x20;  (* ADD (% rax) (Imm8 (word 32)) *)
  0x48; 0x3d; 0x00; 0x04; 0x00; 0x00;
                           (* CMP (% rax) (Imm32 (word 1024)) *)
  0x0f; 0x85; 0x75; 0xff; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294967157)) *)
  0xc3                     (* RET *)
];;
(* BYTECODE END *)

let mldsa_poly_use_hint_88_tmc =
  define_trimmed "mldsa_poly_use_hint_88_tmc" mldsa_poly_use_hint_88_mc;;

let MLDSA_POLY_USE_HINT_88_EXEC =
  X86_MK_CORE_EXEC_RULE mldsa_poly_use_hint_88_tmc;;

(* ========================================================================= *)
(* Per-element scalar correctness chain for the x86_64 AVX2 poly_use_hint_88  *)
(* routine (ML-DSA-44, GAMMA2 = (Q-1)/88, 2*GAMMA2 = 190464). The numeric     *)
(* Barrett model and the pure num/int decompose lemmas are specific to this   *)
(* x86_64 proof; the x86 lane decomposition mirrors the poly_use_hint_32      *)
(* proof with the 88 constants.                                               *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Numeric (code-aligned) form of UseHint, matching the Barrett computation  *)
(* performed by the assembly. Bridged to the FIPS 204 spec mldsa_use_hint_88 *)
(* via MLDSA_USE_HINT_88_EQUIV below.                                         *)
(* ------------------------------------------------------------------------- *)
let mldsa_use_hint_88_code = new_definition
  `mldsa_use_hint_88_code (a:num) (h:num) =
   let a1_raw = ((((a + 127) DIV 128) * 11275 + 8388608) DIV 16777216) in
   let a1 = if a1_raw > 43 then 0 else a1_raw in
   let a0:int = &a - &a1 * &190464 in
   let a0' = if a0 > &4190208 then a0 - &8380417 else a0 in
   if h = 0 then a1
   else if a0' > &0 then if a1 = 43 then 0 else a1 + 1
   else if a1 = 0 then 43 else a1 - 1`;;

(* ========================================================================= *)
(* Arithmetic bridge: the assembly's two rounding steps (vpmulhuw by 11275   *)
(* giving m16 = (t*11275) DIV 2^16, then vpmulhrsw by 128 giving             *)
(* ((m16*128) DIV 2^14 + 1) DIV 2) equal the single code-form Barrett        *)
(* division (t*11275 + 2^23) DIV 2^24.                                       *)
(* ========================================================================= *)

let MUL_DIV_128 = prove(`!m. (m * 128) DIV 16384 = m DIV 128`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `16384 = 128 * 128`] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN SIMP_TAC[DIV_MULT; ARITH_RULE `~(128=0)`]);;

let A1_TWOSTEP_88 = prove(`!t. ((((t * 11275) DIV 65536) * 128) DIV 16384 + 1) DIV 2 =
                            (t * 11275 + 8388608) DIV 16777216`,
  GEN_TAC THEN REWRITE_TAC[MUL_DIV_128] THEN
  REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`t * 11275`; `8388608`] ROUND_DIV) THEN
  REWRITE_TAC[ARITH_RULE `~(8388608 = 0)`; ARITH_RULE `2 * 8388608 = 16777216`]);;

(* ------------------------------------------------------------------------- *)
(* x86 lane lemmas (vpsrld $7 / vpmulhuw 11275 / vpmulhrsw 128).             *)
(* ------------------------------------------------------------------------- *)

(* Lane lemma: high 16 bits of the unsigned 16x16->32 multiply by 11275. *)
let LANE_MULHUW_88 = prove(`!u:16 word. val u < 65536 ==>
   val(word_subword (word_mul ((word_zx u):int32) ((word_zx (word 11275:16 word)):int32)) (16,16):16 word)
   = (val u * 11275) DIV 65536`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(word_mul ((word_zx (u:16 word)):int32) ((word_zx (word 11275:16 word)):int32)) = val u * 11275` SUBST1_TAC THENL
  [REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ZX_GEN; DIMINDEX_16; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
   SUBGOAL_THEN `val(u:16 word) MOD 4294967296 = val u` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `u:16 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `val(word 11275:16 word) = 11275` SUBST1_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `u:16 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN
  SUBGOAL_THEN `val(u:16 word) * 11275 < 65536 * 65536` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(65536 = 0)`] THEN ARITH_TAC);;

(* Lane lemma: the vpmulhrsw rounding-multiply lane by 128, for a 16-bit input
   below 11265 (the range of the m16 = high16(t*11275) intermediate). *)
let LANE_MULHRSW_88 = prove(`!u:16 word. val u < 11265 ==>
   val(word_subword (word_add (word_ushr (word_mul ((word_sx u):int32)((word_sx (word 128:16 word)):int32)) 14) (word 1:int32)) (1,16) :16 word)
   = ((val u * 128) DIV 16384 + 1) DIV 2`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val((word_sx (u:16 word)):int32) = val u` ASSUME_TAC THENL
  [MATCH_MP_TAC VAL_WORD_SX_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val((word_sx (word 128:16 word)):int32) = 128` ASSUME_TAC THENL
  [SUBGOAL_THEN `val(word 128:16 word) = 128` ASSUME_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
   ASM_SIMP_TAC[VAL_WORD_SX_SMALL; ARITH_RULE `128 < 32768`]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_mul ((word_sx (u:16 word)):int32)((word_sx (word 128:16 word)):int32)) = val u * 128` ASSUME_TAC THENL
  [REWRITE_TAC[VAL_WORD_MUL] THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(word_add (word_ushr (word_mul ((word_sx (u:16 word)):int32)((word_sx (word 128:16 word)):int32)) 14) (word 1:int32)) = (val u * 128) DIV 16384 + 1` SUBST1_TAC THENL
  [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_USHR; VAL_WORD; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   MATCH_MP_TAC MOD_LT THEN
   SUBGOAL_THEN `(val(u:16 word) * 128) DIV 16384 <= 88` MP_TAC THENL
   [SUBGOAL_THEN `val(u:16 word) * 128 < 11265 * 128` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(16384=0)`] THEN ARITH_TAC; ALL_TAC] THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN
  SUBGOAL_THEN `(val(u:16 word) * 128) DIV 16384 + 1 <= 89` MP_TAC THENL
  [SUBGOAL_THEN `(val(u:16 word) * 128) DIV 16384 <= 88` MP_TAC THENL
   [SUBGOAL_THEN `val(u:16 word) * 128 < 11265 * 128` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(16384=0)`] THEN ARITH_TAC; ALL_TAC] THEN ARITH_TAC; ALL_TAC] THEN
  ARITH_TAC);;

(* Composed per-lane Barrett a1: the full x86 decompose a1 lane (pre-shift t via
   VAL_T, vpmulhuw by 11275 via LANE_MULHUW_88, vpmulhrsw by 128 via
   LANE_MULHRSW_88) on a coefficient a:int32 with val a < Q equals the code-form
   a1 Barrett value ((val a + 127) DIV 128 * 11275 + 8388608) DIV 16777216. *)
let A1_LANE_88 = prove(`!a:int32. val a < 8380417 ==>
   val(word_subword
        (word_add
          (word_ushr
            (word_mul
              ((word_sx
                 (word_subword
                   (word_mul
                     ((word_zx
                        (word_subword
                          (word_ushr (word_add (word 127) a) 7) (0,16)
                          :16 word)):int32)
                     (word 11275:int32))
                   (16,16) :16 word)):int32)
              (word 128:int32))
            14)
          (word 1:int32))
        (1,16) :16 word)
   = ((val a + 127) DIV 128 * 11275 + 8388608) DIV 16777216`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(word 11275:int32) = word_zx (word 11275:16 word)` SUBST1_TAC THENL
  [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `(word 128:int32) = word_sx (word 128:16 word)` SUBST1_TAC THENL
  [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  ABBREV_TAC `t = (val(a:int32) + 127) DIV 128` THEN
  SUBGOAL_THEN `t < 65473` ASSUME_TAC THENL
  [EXPAND_TAC "t" THEN
   MATCH_MP_TAC(ARITH_RULE `x <= 8380543 ==> x DIV 128 < 65473`) THEN
   ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
    `u0 = word_subword
            (word_ushr (word_add (word 127) (a:int32)) 7) (0,16) :16 word` THEN
  SUBGOAL_THEN `val(u0:16 word) = t` ASSUME_TAC THENL
  [EXPAND_TAC "u0" THEN
   REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
   MP_TAC(SPEC `a:int32` VAL_T) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[ARITH_RULE `2 EXP 0 = 1`; DIV_1] THEN
   MATCH_MP_TAC MOD_LT THEN EXPAND_TAC "t" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(u0:16 word) < 65536` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `val(word_subword
          (word_mul ((word_zx (u0:16 word)):int32)
                    ((word_zx (word 11275:16 word)):int32)) (16,16) :16 word)
     = (t * 11275) DIV 65536`
    ASSUME_TAC THENL
  [MP_TAC(SPEC `u0:16 word` LANE_MULHUW_88) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
    `m16 = word_subword
             (word_mul ((word_zx (u0:16 word)):int32)
                       ((word_zx (word 11275:16 word)):int32)) (16,16) :16 word` THEN
  SUBGOAL_THEN `val(m16:16 word) = (t * 11275) DIV 65536` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(m16:16 word) < 11265` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(65536 = 0)`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `m16:16 word` LANE_MULHRSW_88) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_ACCEPT_TAC A1_TWOSTEP_88);;

(* ------------------------------------------------------------------------- *)
(* Decompose num lemmas (arch-independent).                                   *)
(* ------------------------------------------------------------------------- *)

let A1_BOUND_88 = prove(
  `!a. a < 8380417
   ==> ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216 <= 44`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `128` (SPEC `8380416 + 127` (SPEC `a + 127` DIV_MONO))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ABBREV_TAC `d = (a + 127) DIV 128` THEN
  MP_TAC(SPEC `16777216` (SPEC `751819508` (SPEC `d * 11275 + 8388608` DIV_MONO))) THEN
  ANTS_TAC THENL
  [SUBGOAL_THEN `d * 11275 <= 65472 * 11275` MP_TAC THENL
   [ASM_SIMP_TAC[LE_MULT_RCANCEL]; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let A1_BOUND_NOWRAP_88 = prove(
  `!a. a <= 8285184
   ==> ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216 <= 43`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `128` (SPEC `8285184 + 127` (SPEC `a + 127` DIV_MONO))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ABBREV_TAC `d = (a + 127) DIV 128` THEN
  MP_TAC(SPEC `16777216` (SPEC `738196808` (SPEC `d * 11275 + 8388608` DIV_MONO))) THEN
  ANTS_TAC THENL
  [SUBGOAL_THEN `d * 11275 <= 64728 * 11275` MP_TAC THENL
   [ASM_SIMP_TAC[LE_MULT_RCANCEL]; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

(* Barrett equivalence for _88: 45-interval case analysis *)
let BARRETT_INTERVAL_88 = prove(
  `!a lo hi k.
    lo <= a /\ a <= hi /\
    k * 16777216 <= (lo + 127) DIV 128 * 11275 + 8388608 /\
    (hi + 127) DIV 128 * 11275 + 8388608 < (k + 1) * 16777216
    ==> ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216 = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC DIV_SANDWICH THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THENL
  [TRANS_TAC LE_TRANS `(lo + 127) DIV 128 * 11275 + 8388608` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ARITH_RULE `x + 8388608 <= y + 8388608 <=> x <= y`] THEN
   REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
   MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC;
   TRANS_TAC LET_TRANS `(hi + 127) DIV 128 * 11275 + 8388608` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ARITH_RULE `x + 8388608 <= y + 8388608 <=> x <= y`] THEN
   REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
   MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC]);;

let A1_WRAP_88 = prove(
  `!a. 8285184 < a /\ a < 8380417
   ==> ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216 = 44`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `44 <= ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216`
    ASSUME_TAC THENL
  [MP_TAC(SPEC `128` (SPEC `a + 127` (SPEC `8285185 + 127` DIV_MONO))) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
   ABBREV_TAC `d = (a + 127) DIV 128` THEN
   MP_TAC(SPEC `16777216` (SPEC `d * 11275 + 8388608` (SPEC `738208083` DIV_MONO))) THEN
   ANTS_TAC THENL
   [SUBGOAL_THEN `64729 * 11275 <= d * 11275` MP_TAC THENL
    [ASM_SIMP_TAC[LE_MULT_RCANCEL]; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPEC `a:num` A1_BOUND_88) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_ARITH_TAC);;

let A0_UPPER_88 = prove(
  `!a. a <= 8285184
   ==> a < (((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216 + 1) * 190464`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `nv = ((a + 127) DIV 128 * 11275 + 8388608) DIV 16777216` THEN
  SUBGOAL_THEN `nv * 16777216 <= (a + 127) DIV 128 * 11275 + 8388608` ASSUME_TAC THENL
  [EXPAND_TAC "nv" THEN MP_TAC(SPECL [`(a + 127) DIV 128 * 11275 + 8388608`; `16777216`] (CONJUNCT1 DIVISION_SIMP)) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a + 127) DIV 128 <= 64728` ASSUME_TAC THENL
  [MP_TAC(SPEC `128` (SPEC `8285184 + 127` (SPEC `a + 127` DIV_MONO))) THEN ANTS_TAC THENL [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `nv * 16777216 <= 64728 * 11275 + 8388608` ASSUME_TAC THENL
  [SUBGOAL_THEN `(a + 127) DIV 128 * 11275 <= 64728 * 11275` MP_TAC THENL [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `nv <= 43` ASSUME_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* x86 helper lemmas (BITBLAST), value form of the a1 lane, threshold/sign.  *)
(* ------------------------------------------------------------------------- *)

let A1_LANE_VAL_88 = prove(
  `!a:int32. val a < 8380417
    ==> val(word_zx (word_subword
              (word_add (word_ushr (word_mul (word_sx (word_subword
                 (word_mul (word_zx (word_subword (word_ushr (word_add (word 127) a) 7) (0,16) :16 word) :int32)
                    (word 11275:int32)) (16,16) :16 word) :int32) (word 128:int32)) 14) (word 1:int32)) (1,16) :16 word) :int32)
        = ((val a + 127) DIV 128 * 11275 + 8388608) DIV 16777216`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `val(word_subword
              (word_add (word_ushr (word_mul (word_sx (word_subword
                 (word_mul (word_zx (word_subword (word_ushr (word_add (word 127) (a:int32)) 7) (0,16) :16 word) :int32)
                    (word 11275:int32)) (16,16) :16 word) :int32) (word 128:int32)) 14) (word 1:int32)) (1,16) :16 word)
    = ((val(a:int32) + 127) DIV 128 * 11275 + 8388608) DIV 16777216`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC A1_LANE_88 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN MP_TAC(SPEC `val(a:int32)` A1_BOUND_88) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let WORD_IGT_THRESHOLD_88 = BITBLAST_RULE
  `!a:int32. val a < 8380417 ==> (word_igt a (word 8285184:int32) <=> val a > 8285184)`;;

let WRAP_A0_NEGATIVE_88 = BITBLAST_RULE
  `!a:int32. val a < 8380417 /\ val a > 8285184
   ==> bit 31 (word_add (word_sub a (word 8380416:int32)) (word 4294967295:int32))`;;

let WORD_SUB_SIGN_BARE_88 = BITBLAST_RULE
  `!a:int32 b:int32. val b <= 8189952 /\ val a <= 8285184 ==>
   ((bit 31 (word_sub a b) \/ word_sub a b = word 0) <=> val a <= val b)`;;

(* Sign / threshold helpers for tmp = a1' + delta*h (delta in {+1,-1}). *)
let WORD_ILT_0_SMALL = BITBLAST_RULE
  `!x:int32. val x <= 43 ==> ~(word_ilt x (word 0))`;;
let WORD_IGT_43_BOUND = BITBLAST_RULE
  `!x:int32. val x <= 43 ==> ~(word_igt x (word 43:int32))`;;
let WORD_IGT_43_ADD1 = BITBLAST_RULE
  `!x:int32. val x <= 42 ==> ~(word_igt (word_add x (word 1:int32)) (word 43:int32))`;;
let WORD_ILT_0_ADD1 = BITBLAST_RULE
  `!x:int32. val x <= 42 ==> ~(word_ilt (word_add x (word 1:int32)) (word 0:int32))`;;
let WORD_IGT_43_SUB1 = BITBLAST_RULE
  `!x:int32. val x <= 43 /\ ~(val x = 0) ==>
   ~(word_igt (word_add x (word 4294967295:int32)) (word 43:int32))`;;
let WORD_ILT_0_SUB1 = BITBLAST_RULE
  `!x:int32. val x <= 43 /\ ~(val x = 0) ==>
   ~(word_ilt (word_add x (word 4294967295:int32)) (word 0:int32))`;;

let WORD_AND_FULL_32 = BITBLAST_RULE `!x:int32. word_and x (word 4294967295) = x`;;

(* Final-clamp leaf results, evaluated at a1 = word nv (nv <= 43).  These are the
   value of the vpblendvb/vpcmpgtd/vpandn clamp for the three reachable deltas:
   h=0 (tmp = nv), h=1 with a0>0 (tmp = nv+1), h=1 with a0<=0 (tmp = nv-1, or -1
   wrapping to 43 at nv=0).  Types are pinned to int32 throughout to avoid type
   invention when these are MATCH_MP_TAC'd into the element proof. *)
let TMP_RESULT_H0 = prove(
 `!nv:num. nv <= 43 ==>
    val(word_and
          (if word_ilt (word nv:int32) (word 0:int32) then (word 43:int32) else (word nv:int32))
          (word_not (word_neg (word (bitval (word_igt
            (if word_ilt (word nv:int32) (word 0:int32) then (word 43:int32) else (word nv:int32))
            (word 43:int32))):int32))))
      = nv`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(word_ilt (word nv:int32) (word 0:int32))` ASSUME_TAC THENL
   [MATCH_MP_TAC WORD_ILT_0_SMALL THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `nv MOD 4294967296 = nv` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `~(word_igt (word nv:int32) (word 43:int32))` ASSUME_TAC THENL
   [MATCH_MP_TAC WORD_IGT_43_BOUND THEN REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `nv MOD 4294967296 = nv` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_AND_FULL_32] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC);;

let TMP_RESULT_POS = prove(
 `!nv:num. nv <= 43 ==>
    val(word_and
          (if word_ilt (word_add (word nv:int32) (word 1:int32)) (word 0:int32)
           then (word 43:int32) else word_add (word nv:int32) (word 1:int32))
          (word_not (word_neg (word (bitval (word_igt
            (if word_ilt (word_add (word nv:int32) (word 1:int32)) (word 0:int32)
             then (word 43:int32) else word_add (word nv:int32) (word 1:int32))
            (word 43:int32))):int32))))
      = (if nv = 43 then 0 else nv + 1)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `nv = 43` THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV
   ;
    SUBGOAL_THEN `val(word nv:int32) <= 42` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `nv MOD 4294967296 = nv` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `nv <= 43` THEN UNDISCH_TAC `~(nv = 43)` THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `word nv:int32` WORD_ILT_0_ADD1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `word nv:int32` WORD_IGT_43_ADD1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[WORD_AND_FULL_32] THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `nv MOD 4294967296 = nv` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC]);;

let TMP_RESULT_NEG = prove(
 `!nv:num. nv <= 43 ==>
    val(word_and
          (if word_ilt (word_add (word nv:int32) (word 4294967295:int32)) (word 0:int32)
           then (word 43:int32) else word_add (word nv:int32) (word 4294967295:int32))
          (word_not (word_neg (word (bitval (word_igt
            (if word_ilt (word_add (word nv:int32) (word 4294967295:int32)) (word 0:int32)
             then (word 43:int32) else word_add (word nv:int32) (word 4294967295:int32))
            (word 43:int32))):int32))))
      = (if nv = 0 then 43 else nv - 1)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `nv = 0` THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV
   ;
    SUBGOAL_THEN `val(word nv:int32) <= 43 /\ ~(val(word nv:int32) = 0)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `nv MOD 4294967296 = nv` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `word nv:int32` WORD_ILT_0_SUB1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `word nv:int32` WORD_IGT_43_SUB1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[WORD_AND_FULL_32] THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `nv MOD 4294967296 = nv` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nv + 4294967295 = (nv - 1) + 1 * 4294967296` SUBST1_TAC THENL
     [UNDISCH_TAC `~(nv = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `nv <= 43` THEN ARITH_TAC]);;

(* h = 1 leaf for general delta sign b = (a0 <= 0): the vpblendvb/clamp value at
   a1 = word nv with delta = word_or(word_neg(word(bitval b)))(word 1). *)
let H1_LEAF = prove(
 `!nv:num b:bool. nv <= 43 ==>
    val(word_and
          (if word_ilt (word_add (word nv:int32) (word_or (word_neg (word (bitval b):int32)) (word 1:int32))) (word 0:int32)
           then (word 43:int32)
           else word_add (word nv:int32) (word_or (word_neg (word (bitval b):int32)) (word 1:int32)))
          (word_not (word_neg (word (bitval (word_igt
            (if word_ilt (word_add (word nv:int32) (word_or (word_neg (word (bitval b):int32)) (word 1:int32))) (word 0:int32)
             then (word 43:int32)
             else word_add (word nv:int32) (word_or (word_neg (word (bitval b):int32)) (word 1:int32)))
            (word 43:int32))):int32))))
      = (if b then (if nv = 0 then 43 else nv - 1) else (if nv = 43 then 0 else nv + 1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THENL
   [MATCH_MP_TAC TMP_RESULT_NEG THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC TMP_RESULT_POS THEN ASM_REWRITE_TAC[]]);;

(* Reconcile the H1_LEAF result (keyed on b = a0 <= 0) with the code RHS
   (keyed on a0 > 0): the two if-forms are equal since the conditions are
   complementary and the branches are swapped. *)
let H1_RHS = prove(
 `!x:int (A:num) B. (if ~(&0 < x) then A else B) = (if &0 < x then B else A)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 < x:int` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The per-element x86 word model of UseHint (param 44), matching the scalar *)
(* form one coefficient lane computes.  Structure mirrors                    *)
(* mldsa_use_hint_32_x86_asm but with the 88 constants:                      *)
(*   t      = (a + 127) >>u 7                          (vpaddd 127, vpsrld 7) *)
(*   m16    = high16(t * 11275)                                  (vpmulhuw)  *)
(*   a1lane = ((m16 * 128) >> 14 + 1) >> 1   [bits (1,16)]       (vpmulhrsw) *)
(*   a1     = zx a1lane                                                      *)
(*   m      = (a > 8285184 ? -1 : 0)                            (vpcmpgtd)   *)
(*   a1'    = a1 & ~m                                           (vpandn)     *)
(*   a0     = a - a1*190464 + m   (190464 via the 3*/31*/2048 shift chain)   *)
(*   delta  = (a0 <= 0 ? -1 : +1)                                            *)
(*   tmp    = a1' + delta*h                                                  *)
(*   tmp2   = (tmp < 0 ? 43 : tmp)     (vpblendvb against 43; only tmp=-1    *)
(*                                      reaches the negative selection)      *)
(*   result = (tmp2 > 43 ? 0 : tmp2)            (vpcmpgtd 43, vpandn)        *)
(* ------------------------------------------------------------------------- *)
let mldsa_use_hint_88_x86_asm = new_definition
  `mldsa_use_hint_88_x86_asm (a:int32) (h:int32) : int32 =
   let t = word_ushr (word_add (word 127) a) 7 in
   let m16 = word_subword
               (word_mul (word_zx (word_subword t (0,16) :16 word) :int32)
                         (word 11275)) (16,16) :16 word in
   let a1lane = word_subword
                  (word_add
                    (word_ushr (word_mul (word_sx m16 :int32) (word 128)) 14)
                    (word 1)) (1,16) :16 word in
   let a1 = word_zx a1lane :int32 in
   let m:int32 = (if word_igt a (word 8285184) then word 4294967295
                  else word 0) in
   let a1' = word_and a1 (word_not m) in
   let a0 = word_add (word_sub a (word_mul a1 (word 190464))) m in
   let delta:int32 = word_or (word_neg(word(bitval(word_ile a0 (word 0)))))
                             (word 1) in
   let tmp = word_add a1' (word_mul delta h) in
   let tmp2:int32 = if word_ilt tmp (word 0) then word 43 else tmp in
   let neg_mask:int32 = word_neg(word(bitval(word_igt tmp2 (word 43)))) in
   word_and tmp2 (word_not neg_mask)`;;

(* ------------------------------------------------------------------------- *)
(* Element correctness (value form): the per-lane x86 word model equals the  *)
(* scalar code form for one coefficient, for val a < Q and val h <= 1.       *)
(* Case split is wrap (a > 8285184 => a1 lane = 44, masked to 0) vs no-wrap; *)
(* the no-wrap case further splits on h and on the a0-sign delta.            *)
(* ------------------------------------------------------------------------- *)
let ELEMENT_CORRECT_88 = prove(
  `!a:int32 h:int32.
     val a < 8380417 /\ val h <= 1
     ==> val(mldsa_use_hint_88_x86_asm a h) = mldsa_use_hint_88_code (val a) (val h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mldsa_use_hint_88_x86_asm; mldsa_use_hint_88_code] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nv = ((val(a:int32) + 127) DIV 128 * 11275 + 8388608) DIV 16777216` THEN
  ABBREV_TAC
   `a1w:int32 =
      word_zx (word_subword
        (word_add (word_ushr (word_mul (word_sx (word_subword
                 (word_mul (word_zx (word_subword
                    (word_ushr (word_add (word 127) (a:int32)) 7) (0,16) :16 word) :int32)
                    (word 11275)) (16,16) :16 word) :int32)
              (word 128)) 14) (word 1)) (1,16) :16 word) :int32` THEN
  SUBGOAL_THEN `val(a1w:int32) = nv` ASSUME_TAC THENL
   [EXPAND_TAC "a1w" THEN EXPAND_TAC "nv" THEN
    MATCH_MP_TAC A1_LANE_VAL_88 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `nv <= 44` ASSUME_TAC THENL
   [MP_TAC(SPEC `val(a:int32)` A1_BOUND_88) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `word_igt (a:int32) (word 8285184:int32) <=> val a > 8285184`
    SUBST1_TAC THENL
   [MP_TAC(SPEC `a:int32` WORD_IGT_THRESHOLD_88) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `val(a:int32) > 8285184` THEN ASM_REWRITE_TAC[] THENL
  [
    (* WRAP ZONE: nv = 44, a1 lane masked to 0. *)
    SUBGOAL_THEN `nv = 44` SUBST_ALL_TAC THENL
     [MP_TAC(SPEC `val(a:int32)` A1_WRAP_88) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `a1w:int32 = word 44` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `a1w:int32 = word 44` then SUBST_ALL_TAC th else failwith "no") THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `word_and (word 44:int32) (word_not (word 4294967295)) = word 0` SUBST1_TAC THENL
     [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `word_mul (word 44:int32) (word 190464) = word 8380416` SUBST1_TAC THENL
     [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `word_ile (word_add (word_sub (a:int32) (word 8380416)) (word 4294967295)) (word 0)` ASSUME_TAC THENL
     [REWRITE_TAC[WORD_ILE_ZERO_32] THEN DISJ1_TAC THEN
      MP_TAC(SPEC `a:int32` WRAP_A0_NEGATIVE_88) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV THEN
    ASM_CASES_TAC `val(h:int32) = 0` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `h:int32 = word 0` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONV_TAC WORD_REDUCE_CONV;
      SUBGOAL_THEN `h:int32 = word 1` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM VAL_EQ_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[INT_MUL_LZERO; INT_SUB_RZERO] THEN
      SUBGOAL_THEN `(&(val(a:int32)):int) > &4190208` ASSUME_TAC THENL
       [MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_GT; INT_GT](ASSUME `val(a:int32) > 8285184`)) THEN INT_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((&(val(a:int32)) - &8380417:int) > &0)` ASSUME_TAC THENL
       [MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT](ASSUME `val(a:int32) < 8380417`)) THEN INT_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[]]
  ;
    (* NO-WRAP ZONE: mask = 0, a1' = a1 lane = nv <= 43. *)
    SUBGOAL_THEN `nv <= 43` ASSUME_TAC THENL
     [MP_TAC(SPEC `val(a:int32)` A1_BOUND_NOWRAP_88) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(if nv > 43 then 0 else nv) = nv` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_NOT_0; WORD_AND_REFL; WORD_ADD_0] THEN
    SUBGOAL_THEN `val(word_mul (a1w:int32) (word 190464:int32)) = nv * 190464` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_MUL; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `val(word 190464:int32) = 190464` SUBST1_TAC THENL
       [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC MOD_LT THEN
      SUBGOAL_THEN `nv * 190464 <= 43 * 190464` MP_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC;
        CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `nv * 190464 <= 8189952` ASSUME_TAC THENL
     [SUBGOAL_THEN `nv * 190464 <= 43 * 190464` MP_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC;
        CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `val(word_mul (a1w:int32) (word 190464:int32)) <= 8189952` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
      `word_ile (word_sub (a:int32) (word_mul a1w (word 190464:int32))) (word 0)
       <=> ~(&(val a) - &nv * &190464 > (&0:int))` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_ILE_ZERO_32] THEN
      SUBGOAL_THEN
        `(bit 31 (word_sub (a:int32) (word_mul a1w (word 190464:int32))) \/
          word_sub a (word_mul a1w (word 190464:int32)) = word 0)
         <=> val a <= val(word_mul a1w (word 190464:int32))`
        SUBST1_TAC THENL
       [MATCH_MP_TAC WORD_SUB_SIGN_BARE_88 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `val(a:int32) <= nv * 190464` THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_MUL]
          (REWRITE_RULE[GSYM INT_OF_NUM_LE]
            (ASSUME `val(a:int32) <= nv * 190464`))) THEN INT_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `nv * 190464 < val(a:int32)` ASSUME_TAC THENL
         [UNDISCH_TAC `~(val(a:int32) <= nv * 190464)` THEN ARITH_TAC; ALL_TAC] THEN
        MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_MUL]
          (REWRITE_RULE[GSYM INT_OF_NUM_LT]
            (ASSUME `nv * 190464 < val(a:int32)`))) THEN INT_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(int_gt (&(val(a:int32)) - &nv * &190464) (&4190208))` ASSUME_TAC THENL
     [REWRITE_TAC[INT_GT; INT_NOT_LT] THEN
      MP_TAC(SPEC `val(a:int32)` A0_UPPER_88) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_MUL;
        GSYM INT_OF_NUM_ADD] (ASSUME `val(a:int32) < (nv + 1) * 190464`)) THEN
      INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_GT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INT_GT]) THEN ASM_REWRITE_TAC[] THEN
    (* Replace a1w by word nv everywhere (val a1w = nv, nv <= 43). *)
    SUBGOAL_THEN `a1w:int32 = word nv` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `val(h:int32) = 0` THEN ASM_REWRITE_TAC[] THENL
     [
      (* h = 0: tmp = a1' = nv, no correction; leaf via TMP_RESULT_H0 *)
      SUBGOAL_THEN `h:int32 = word 0` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[WORD_MUL_0; WORD_ADD_0] THEN
      MATCH_MP_TAC TMP_RESULT_H0 THEN ASM_REWRITE_TAC[]
     ;
      (* h = 1: tmp = nv + delta, delta = word_or(word_neg(word(bitval(a0<=0))))(word 1).
         The whole vpblendvb/clamp value is given by H1_LEAF with
         b = ~(&(val a) - &nv * &190464 > &0) (which equals a0 <= 0); the code RHS
         then matches by case analysis on b. *)
      SUBGOAL_THEN `h:int32 = word 1` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM VAL_EQ_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[WORD_MUL_1_32] THEN
      MP_TAC(SPECL [`nv:num`; `~((&0:int) < &(val(a:int32)) - &nv * &190464)`] H1_LEAF) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `nv <= 43` THEN ARITH_TAC;
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN MATCH_ACCEPT_TAC H1_RHS]]]);;

(* Word form, directly usable in the loop body discharge. *)
let ELEMENT_CORRECT_WORD_88 = prove(
  `!a:int32 h:int32.
     val a < 8380417 /\ val h <= 1
     ==> mldsa_use_hint_88_x86_asm a h =
         word(mldsa_use_hint_88_code (val a) (val h))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  AP_TERM_TAC THEN MP_TAC(SPECL [`a:int32`; `h:int32`] ELEMENT_CORRECT_88) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ========================================================================= *)
(* FIPS 204 = code-aligned equivalence (arch-independent).                   *)
(* The decompose r1/r0 lemmas and tactics below are pure num/int.            *)
(* ========================================================================= *)

(* The per-variant divisor is 2*GAMMA2 = 190464. The generic Barrett DIV/MOD
   tactics are shared from mldsa_utils.ml. *)
let LINEARIZE_DIV_MOD_TAC_88 = LINEARIZE_DIV_MOD_BY_TAC 190464;;
let DIV_190464_TAC k = DIV_EQ_K_BY_TAC 190464 k;;
let DIV_MOD_TO_DIV_TAC_88 = DIV_MOD_TO_DIV_BY_TAC 190464;;

let DECOMPOSE_R1_LOWER_TAC_88 =
  SUBGOAL_THEN `~((&r:int) - &(r MOD 190464) = &8380416)` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_EQ] THEN LINEARIZE_DIV_MOD_TAC_88;
   ALL_TAC] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_DIV; NUM_OF_INT_OF_NUM] THEN
  DIV_MOD_TO_DIV_TAC_88 THEN
  CONV_TAC SYM_CONV THEN
  LINEARIZE_DIV_MOD_TAC_88;;

let DECOMPOSE_R1_UPPER_TAC_88 =
  SUBGOAL_THEN `r MOD 190464 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r MOD 190464 < 190464` ASSUME_TAC THENL
  [MP_TAC(SPECL [`r:num`; `190464`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((&r:int) - (&(r MOD 190464) - &190464) = &8380416)` (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[INT_ARITH `(a:int) - (b - c) = d <=> a + c - b = d`] THEN
   ASM_SIMP_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB; INT_OF_NUM_EQ] THEN
   LINEARIZE_DIV_MOD_TAC_88; ALL_TAC] THEN
  SUBGOAL_THEN `(&r:int) - (&(r MOD 190464) - &190464) =
                &(r - r MOD 190464 + 190464)` SUBST1_TAC THENL
  [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_ADD] THEN
   INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_DIV; NUM_OF_INT_OF_NUM] THEN
  MP_TAC(SPECL [`r:num`; `190464`] (CONJUNCT1 DIVISION_SIMP)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r - r MOD 190464 + 190464 = 190464 * (r DIV 190464 + 1)`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`190464`; `r DIV 190464 + 1`] DIV_MULT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `r MOD 190464` (concl th) ||
    free_in `r DIV 190464` (concl th)))) THEN
  MP_TAC(SPECL [`r:num`; `190464`] (CONJUNCT1 DIVISION_SIMP)) THEN
  SPEC_TAC(`r MOD 190464`, `m:num`) THEN
  SPEC_TAC(`r DIV 190464`, `q:num`) THEN
  REPEAT GEN_TAC THEN ASM_ARITH_TAC;;

let DECOMPOSE_R1_NOWRAP_TAC_88 =
  ASM_CASES_TAC `r MOD 190464 * 2 <= 190464` THEN ASM_REWRITE_TAC[] THEN
  TRY DECOMPOSE_R1_LOWER_TAC_88 THEN TRY DECOMPOSE_R1_UPPER_TAC_88;;

let DECOMPOSE_88_R1_EQUIV = time prove(
  `!r. r < 8380417 ==>
   (let a1_raw = ((r + 127) DIV 128 * 11275 + 8388608) DIV 16777216 in
    if a1_raw > 43 then 0 else a1_raw) =
   decompose_88_r1 r`,
  GEN_TAC THEN DISCH_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `r <= 8285184` THENL
  [ALL_TAC;
   (* Wrap zone *)
   SUBGOAL_THEN `8285184 < r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `decompose_88_r1 r = 0` SUBST1_TAC THENL
   [REWRITE_TAC[decompose_88_r1; mldsa_decompose_88; mldsa_cmod] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN `r MOD 190464 <= r` ASSUME_TAC THENL
    [MESON_TAC[MOD_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `r MOD 190464 < 190464` ASSUME_TAC THENL
    [MP_TAC(SPECL [`r:num`; `190464`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `r MOD 190464 * 2 <= 190464` THEN ASM_REWRITE_TAC[] THENL
    [(* Lower wrap: r DIV 190464 = 44 *)
     SUBGOAL_THEN `r DIV 190464 = 44` ASSUME_TAC THENL
     [DIV_190464_TAC 44; ALL_TAC] THEN
     SUBGOAL_THEN `44 * 190464 + r MOD 190464 = r` MP_TAC THENL
     [MP_TAC(SPECL [`r:num`; `190464`] (CONJUNCT1 DIVISION_SIMP)) THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_EQ] THEN
     ASM_ARITH_TAC;
     (* Upper wrap: r DIV 190464 = 43 *)
     SUBGOAL_THEN `r DIV 190464 = 43` ASSUME_TAC THENL
     [DIV_190464_TAC 43; ALL_TAC] THEN
     SUBGOAL_THEN `43 * 190464 + r MOD 190464 = r` MP_TAC THENL
     [MP_TAC(SPECL [`r:num`; `190464`] (CONJUNCT1 DIVISION_SIMP)) THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `(&r:int) - (&(r MOD 190464) - &190464) =
                   &(r - r MOD 190464 + 190464)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_ADD] THEN
      INT_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
   MP_TAC(SPEC `r:num` A1_WRAP_88) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV] THEN
  (* Nowrap zone: Barrett <= 43, so if > 43 then 0 else Barrett = Barrett *)
  SUBGOAL_THEN `((r + 127) DIV 128 * 11275 + 8388608) DIV 16777216 <= 43`
    ASSUME_TAC THENL
  [MATCH_MP_TAC A1_BOUND_NOWRAP_88 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(((r + 127) DIV 128 * 11275 + 8388608) DIV 16777216 > 43)`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (* Nowrap zone: unfold and do interval cascade *)
  REWRITE_TAC[decompose_88_r1; mldsa_decompose_88; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `r MOD 190464 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r MOD 190464 < 190464` ASSUME_TAC THENL
  [MP_TAC(SPECL [`r:num`; `190464`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  let intervals = [
    (0, 95232); (95233, 285696); (285697, 476160); (476161, 666624);
    (666625, 857088); (857089, 1047552); (1047553, 1238016);
    (1238017, 1428480); (1428481, 1618944); (1618945, 1809408);
    (1809409, 1999872); (1999873, 2190336); (2190337, 2380800);
    (2380801, 2571264); (2571265, 2761728); (2761729, 2952192);
    (2952193, 3142656); (3142657, 3333120); (3333121, 3523584);
    (3523585, 3714048); (3714049, 3904512); (3904513, 4094976);
    (4094977, 4285440); (4285441, 4475904); (4475905, 4666368);
    (4666369, 4856832); (4856833, 5047296); (5047297, 5237760);
    (5237761, 5428224); (5428225, 5618688); (5618689, 5809152);
    (5809153, 5999616); (5999617, 6190080); (6190081, 6380544);
    (6380545, 6571008); (6571009, 6761472); (6761473, 6951936);
    (6951937, 7142400); (7142401, 7332864); (7332865, 7523328);
    (7523329, 7713792); (7713793, 7904256); (7904257, 8094720);
    (8094721, 8285184)] in
  let mk_le hi =
    mk_comb(mk_comb(`(<=):num->num->bool`, mk_var("r",`:num`)),
            mk_small_numeral hi) in
  let apply_interval k (lo, hi) =
    let th = SPECL [`r:num`; mk_small_numeral lo;
                    mk_small_numeral hi; mk_small_numeral k]
                   BARRETT_INTERVAL_88 in
    MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DECOMPOSE_R1_NOWRAP_TAC_88 in
  let rec cascade k = function
    | [(lo,hi)] -> apply_interval k (lo,hi)
    | (lo,hi)::rest ->
        ASM_CASES_TAC (mk_le hi) THENL
        [apply_interval k (lo,hi); cascade (k+1) rest]
    | [] -> failwith "empty" in
  cascade 0 intervals);;

let R1_IS_DIV_LOWER_88 = prove(
  `!r. r < 8380417 /\ r MOD 190464 * 2 <= 190464 /\
       ~((&r:int) - &(r MOD 190464) = &8380416) ==>
   (let a1_raw = ((r + 127) DIV 128 * 11275 + 8388608) DIV 16777216 in
    if a1_raw > 43 then 0 else a1_raw) = r DIV 190464`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_88_R1_EQUIV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPEC `r:num` LOWER_NONWRAP_R1_88) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let R1_IS_DIV_PLUS1_UPPER_88 = prove(
  `!r. r < 8380417 /\ ~(r MOD 190464 * 2 <= 190464) /\
       ~((&r:int) - (&(r MOD 190464) - &190464) = &8380416) ==>
   (let a1_raw = ((r + 127) DIV 128 * 11275 + 8388608) DIV 16777216 in
    if a1_raw > 43 then 0 else a1_raw) = r DIV 190464 + 1`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_88_R1_EQUIV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPEC `r:num` UPPER_NONWRAP_R1_88) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let R0_SIGN_UPPER_NOWRAP_TAC_88 =
  MP_TAC(SPEC `r:num` R1_IS_DIV_PLUS1_UPPER_88) THEN
  ANTS_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPECL [`r:num`; `190464`] INT_MOD_RESIDUE)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `(a:int) - (b + &1) * c = a - b * c - c`] THEN
  REWRITE_TAC[INT_ARITH `x - &190464 > &0 <=> x > &190464`;
              INT_ARITH `x - &190464 - &8380417 > &0 <=> x > &8570881`;
              INT_OF_NUM_GT] THEN
  ASM_ARITH_TAC;;

let R0_SIGN_LOWER_NOWRAP_TAC_88 =
  MP_TAC(SPEC `r:num` R1_IS_DIV_LOWER_88) THEN
  ANTS_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPECL [`r:num`; `190464`] INT_MOD_RESIDUE)) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `x - &8380417 > &0 <=> x > &8380417`;
              INT_OF_NUM_GT] THEN
  ASM_ARITH_TAC;;

let R0_SIGN_WRAP_TAC_88 =
  SUBGOAL_THEN `8285184 < r` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (fun th ->
     can (find_term (fun t -> t = `&8380416:int`)) (concl th) &&
     not(is_neg(concl th)))) THEN
   ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_EQ;
     INT_ARITH `(a:int) - (b - c) = d <=> a + c - b = d`;
     GSYM INT_OF_NUM_ADD] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_88_R1_EQUIV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[decompose_88_r1; mldsa_decompose_88; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[INT_MUL_LZERO; INT_SUB_RZERO] THEN
  REWRITE_TAC[INT_ARITH `x - &1 > &0 <=> x > &1`;
              INT_ARITH `(x - &190464) - &1 > &0 <=> x > &190465`;
              INT_ARITH `x - &8380417 > &0 <=> x > &8380417`;
              INT_OF_NUM_GT] THEN
  ASM_ARITH_TAC;;

let DECOMPOSE_88_R0_SIGN = time prove(
  `!r. r < 8380417 ==>
    let a1_raw = ((r + 127) DIV 128 * 11275 + 8388608) DIV 16777216 in
    let a1 = if a1_raw > 43 then 0 else a1_raw in
    let a0':int = if (&r:int) - &a1 * &190464 > &4190208
                  then &r - &a1 * &190464 - &8380417
                  else &r - &a1 * &190464 in
    (decompose_88_r0 r > &0 <=> a0' > &0) /\
    (decompose_88_r0 r <= &0 <=> ~(a0' > &0))`,
  GEN_TAC THEN DISCH_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_ARITH `(x:int) <= &0 <=> ~(x > &0)`] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> (p <=> q) /\ (~p <=> ~q)`) THEN
  REWRITE_TAC[decompose_88_r0; mldsa_decompose_88; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[SND; FST] THEN
  SUBGOAL_THEN `r MOD 190464 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r MOD 190464 < 190464` ASSUME_TAC THENL
  [MP_TAC(SPECL [`r:num`; `190464`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r MOD 190464 * 2 <= 190464` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY R0_SIGN_LOWER_NOWRAP_TAC_88 THEN
  TRY R0_SIGN_UPPER_NOWRAP_TAC_88 THEN
  TRY R0_SIGN_WRAP_TAC_88 THEN
  TRY(
    (* Contradiction: lower nowrap with > 4190208 *)
    MP_TAC(SPEC `r:num` R1_IS_DIV_LOWER_88) THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_TAC THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
      (SPECL [`r:num`; `190464`] INT_MOD_RESIDUE)) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(&r:int) - &((let a1_raw = ((r + 127) DIV 128 * 11275 + 8388608) DIV 16777216 in
      if a1_raw > 43 then 0 else a1_raw)) * &190464 = &(r MOD 190464)` ASSUME_TAC THENL
    [CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(&(r MOD 190464) > (&4190208:int))` MP_TAC THENL
    [REWRITE_TAC[INT_NOT_LT; INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[INT_OF_NUM_GT] THEN ASM_ARITH_TAC
  ));;

let MLDSA_USE_HINT_88_EQUIV = prove(
  `!r h. r < 8380417 /\ h <= 1
         ==> mldsa_use_hint_88 h r = mldsa_use_hint_88_code r h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MLDSA_USE_HINT_88_UNFOLD] THEN
  REWRITE_TAC[mldsa_use_hint_88_code] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_88_R1_EQUIV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_88_R0_SIGN) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ASM_CASES_TAC `h = 0` THENL
  [ASM_REWRITE_TAC[ARITH_RULE `~(0 = 1)`]; ALL_TAC] THEN
  SUBGOAL_THEN `h = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `decompose_88_r0 r > &0` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
(* ========================================================================= *)
(* 88 framework + store-discharge + correctness chain.                       *)
(* Loaded on top of the 88 program defs and the per-element scalar chain.    *)
(* The YMM constant map is {ymm8=11275, ymm4=127, ymm7=128, ymm6=43,         *)
(* ymm3=8285184, ymm5=0}; the a1<=43 reduction and the VPBLENDVB clamp are   *)
(* handled by UH88_STORE_DISCHARGE_TAC.                                      *)
(* ========================================================================= *)

(* a1 * 2*GAMMA2 = a1*190464 built by the (3a<<5 - 3a)<<11 shift chain. *)
let SHL_190464 = BITBLAST_RULE
  `!a:int32. word_shl (word_sub (word_shl (word_add (word_shl a 1) a) 5) (word_add (word_shl a 1) a)) 11 =
             word_mul a (word 190464)`;;

(* The (16,16) high half of the VPMULHRSW lane uses multiplier (word 0), so it
   contributes nothing: the high a1 lane is zero. *)
let A1HI_ZERO_88 = BITBLAST_RULE
  `word_subword
    (word_add
      (word_ushr
        (word_mul
          (word_sx (word_subword
            (word_mul (word_zx (word_subword
               (word_ushr (word_add (word 127) (x:int32)) 7) (16,16) :16 word) :int32)
               (word 0)) (16,16) :16 word) :int32)
          (word 0)) 14)
      (word 1)) (1,16) :16 word = word 0`;;

(* The final >43 clamp in the andn form equals the model's neg-mask form. *)
let TAIL_CLOSE_88 = prove
 (`!z:int32. word_and (word_not (if word_igt z (word 43) then word 4294967295 else word 0)) z =
             word_and z (word_not (word_neg (word (bitval (word_igt z (word 43))))))`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_BLAST);;

(* Commutativity closer used after the surface rewrites line up the lane. *)
let LANE_AC_CLOSE_88 = prove
 (`!d y m a:int32. word_add (word_mul d y) (word_and (word_not m) a) =
                   word_add (word_and a (word_not m)) (word_mul d y)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let WORD_ILT_45 = BITBLAST_RULE `!V:int32. val V <= 45 ==> ~(word_ilt V (word 0))`;;

(* word_subword distributes through word_not on each 32-bit lane. *)
let UH88_WSN = map (fun n -> prove(
    subst [mk_small_numeral n, `n:num`]
      `!z:int256. word_subword(word_not z) (n,32):int32 = word_not(word_subword z (n,32))`,
    GEN_TAC THEN MATCH_MP_TAC WORD_SUBWORD_NOT THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_256] THEN ARITH_TAC)) [0;32;64;96;128;160;192;224];;

(* VPBLENDVB lane collapse: the post-blend byte-mux of a 32-bit lane (43 if the
   lane is negative, else the lane itself) collapses to the clamp-against-43,
   for a lane value below 46 or equal to -1.  The four bytes of the blend select
   43 / 0 by the lane's per-byte sign bits. *)
let BLEND_COLLAPSE_LE45 = BITBLAST_RULE
  `val(V:int32) <= 45
   ==> word (val (if bit 7 V then word 43 else word_subword V (0,8):byte) * 1 +
             val (if bit 15 V then word 0 else word_subword V (8,8):byte) * 256 +
             val (if bit 23 V then word 0 else word_subword V (16,8):byte) * 65536 +
             val (if bit 31 V then word 0 else word_subword V (24,8):byte) * 16777216) = V`;;

let BLEND_COLLAPSE = prove
 (`val(V:int32) <= 45 \/ V = word 4294967295
   ==> word (val (if bit 7 V then word 43 else word_subword V (0,8):byte) * 1 +
             val (if bit 15 V then word 0 else word_subword V (8,8):byte) * 256 +
             val (if bit 23 V then word 0 else word_subword V (16,8):byte) * 65536 +
             val (if bit 31 V then word 0 else word_subword V (24,8):byte) * 16777216) =
       (if word_ilt V (word 0) then word 43 else V)`,
  STRIP_TAC THENL
   [MP_TAC(SPEC `V:int32` (GEN `V:int32` BLEND_COLLAPSE_LE45)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[WORD_ILT_45];
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(BINOP_CONV(TRY_CONV(LAND_CONV NUM_REDUCE_CONV))) THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV]);;
let BLEND_COLLAPSE_GEN = GEN `V:int32` BLEND_COLLAPSE;;

(* ------------------------------------------------------------------------- *)
(* The post-VPBLENDVB store discharge.  The store goal has the form          *)
(*   word_and (word_not (word_join_of_8 (if word_igt (word_subword B (32k,32)) *)
(*   (word 43) then -1 else 0))) B = simd8 mldsa_use_hint_88_x86_asm av hv   *)
(* where B (the post-blend abbreviation, word(SUM val(byte_i)*256^i)) is     *)
(* defined by a chain of abbreviation assumptions feeding from PRE (the      *)
(* pre-blend value).  The tactic distributes the equality to the 32-bit      *)
(* lanes, bridges each word_subword B (32k,32) to the clamp form via byte    *)
(* extraction + BLEND_COLLAPSE, then collapses the per-lane chain to lane    *)
(* model and discharges via the LUH/RANGE lane lemmas built from the goal.   *)
(* ------------------------------------------------------------------------- *)

(* Per-lane byte-MOD extraction over 32 abstract byte values, lane k. *)
let UH88_BYTEMOD_LANE =
  let bvars = map (fun i -> mk_var("b"^string_of_int i, `:num`)) (0--31) in
  let pow256 i = mk_numeral(Num.power_num (Num.num_of_int 256) (Num.num_of_int i)) in
  let mkadd l = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b) l in
  let mkmul a b = mk_binop `( * ):num->num->num` a b in
  let bigsum_v = mkadd (map (fun i -> mkmul (el i bvars) (pow256 i)) (0--31)) in
  let lane0_v = mkadd [mkmul (el 0 bvars) `1`; mkmul (el 1 bvars) `256`;
                       mkmul (el 2 bvars) `65536`; mkmul (el 3 bvars) `16777216`] in
  let bounds = end_itlist (fun a b -> mk_conj(a,b)) (map (fun b -> mk_binop `(<):num->num->bool` b `256`) bvars) in
  let regroup_th = ARITH_RULE (mk_eq(bigsum_v, mk_binop `(+):num->num->num` lane0_v
      (mkmul `4294967296` (mkadd (map (fun i -> mkmul (el i bvars) (pow256 (i-4))) (4--31)))))) in
  fun k ->
  if k=0 then
    prove(mk_imp(bounds, mk_eq(mk_binop `MOD` (mk_binop `DIV` bigsum_v `2 EXP 0`) `2 EXP 32`, lane0_v)),
      STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[DIV_1] THEN ONCE_REWRITE_TAC[regroup_th] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC)
  else
  let off = 4*k in
  let lower = mkadd (map (fun i -> mkmul (el i bvars) (pow256 i)) (0--(off-1))) in
  let upper = mkadd (map (fun i -> mkmul (el i bvars) (pow256 (i-off))) (off--31)) in
  let lane = mkadd [mkmul (el off bvars) `1`; mkmul (el (off+1) bvars) `256`;
                    mkmul (el (off+2) bvars) `65536`; mkmul (el (off+3) bvars) `16777216`] in
  let p256_4k = pow256 off in
  let split_big = mk_eq(bigsum_v, mk_binop `(+):num->num->num` lower (mkmul p256_4k upper)) in
  let conc = mk_eq(mk_binop `MOD` (mk_binop `DIV` bigsum_v (mk_binop `EXP` `2` (mk_small_numeral(32*k)))) `2 EXP 32`, lane) in
  let div_prefix =
    STRIP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [ARITH_RULE split_big] THEN
    SUBGOAL_THEN (mk_binop `(<):num->num->bool` lower p256_4k) ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE (mk_neg(mk_eq(p256_4k,`0`)))] THEN
    ASM_SIMP_TAC[DIV_LT] THEN REWRITE_TAC[ADD_CLAUSES] in
  if off+4 > 31 then
    prove(mk_imp(bounds,conc), div_prefix THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC)
  else
  let uppertail = mkadd (map (fun i -> mkmul (el i bvars) (pow256 (i-off-4))) ((off+4)--31)) in
  let split_up = mk_eq(upper, mk_binop `(+):num->num->num` lane (mkmul `4294967296` uppertail)) in
  prove(mk_imp(bounds,conc),
    div_prefix THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ARITH_RULE split_up] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let UH88_BYTEMOD_LANES = map UH88_BYTEMOD_LANE (0--7);;

(* Relabel a single lane byte of PRE to the per-lane subword V form. *)
let uh88_byte_relabel pre k m c =
  let tmpl = `(if bit pbit (pp:int256) then (cc:byte) else word_subword pp (ppos,8):byte) =
              (if bit vbit (word_subword pp (lane,32):int32) then (cc:byte)
               else word_subword (word_subword pp (lane,32):int32) (vpos,8):byte)` in
  let inst = subst [ mk_small_numeral(32*k+8*m+7), `pbit:num`;
                     mk_small_numeral(8*m+7), `vbit:num`;
                     mk_small_numeral(32*k+8*m), `ppos:num`;
                     mk_small_numeral(8*m), `vpos:num`;
                     mk_small_numeral(32*k), `lane:num`;
                     c, `cc:byte`; pre, `pp:int256` ] tmpl in
  BITBLAST_RULE inst;;

let UH88_STORE_DISCHARGE_TAC : tactic =
  fun (asl,w) ->
    if not(is_eq w) || not(can(find_term(fun t->try fst(dest_const(fst(strip_comb t)))="simd8" with _->false)) w)
    then failwith "not store goal" else
    let isu t = is_var t && (let v=fst(dest_var t) in String.length v>0 && v.[0]='_') in
    let chaindefs = List.filter_map (fun (_,th)-> let c=concl th in if is_eq c && isu(rand c) then Some th else None) asl in
    let chain_syms = map SYM chaindefs in
    let collapse = TOP_DEPTH_CONV (WORD_SIMPLE_SUBWORD_CONV ORELSEC
                     GEN_REWRITE_CONV I [WORD_SUBWORD_AND] ORELSEC
                     FIRST_CONV (map (fun th -> GEN_REWRITE_CONV I [th]) UH88_WSN)) in
    let onelevel = GEN_REWRITE_CONV ONCE_DEPTH_CONV chain_syms THENC collapse in
    let nchain = List.length chaindefs in
    let lane_collapse t = let c0 = collapse t in
      let rec iter th n = if n=0 then th else iter (TRANS th (onelevel(rand(concl th)))) (n-1) in
      iter c0 (nchain+2) in
    let bdef = List.find (fun th -> let l=lhs(concl th) in (try fst(dest_const(fst(strip_comb l)))="word" with _->false)) chaindefs in
    let bvar = rand(concl bdef) in
    let bytesum = rand(lhs(concl bdef)) in
    let prevar = find_term (fun t -> isu t && type_of t=`:int256` && not(t=bvar)) bytesum in
    let bound_hyp = snd(List.find (fun (_,th)-> try concl th = `!k. k < 8 ==> val(word_subword (hv:int256) (32*k,32):int32) <= 1` with _->false) asl) in
    let bvals = map lhand (striplist (dest_binop `(+):num->num->num`) bytesum) in
    let xk k = mk_comb(mk_comb(`word_subword:int256->num#num->int32`,`av:int256`),mk_pair(mk_small_numeral(32*k),`32`)) in
    let yk k = mk_comb(mk_comb(`word_subword:int256->num#num->int32`,`hv:int256`),mk_pair(mk_small_numeral(32*k),`32`)) in
    let bndk k = CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
       (MP (SPEC (mk_small_numeral k) bound_hyp) (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral k) `8`)))) in
    let vk k = mk_comb(mk_comb(`word_subword:int256->num#num->int32`,prevar),mk_pair(mk_small_numeral(32*k),`32`)) in
    let vcollk k = lane_collapse (vk k) in
    let surfaceT0 = rand(concl(vcollk 0)) in
    let surfaceTxy = subst [`x:int32`, xk 0; `y:int32`, yk 0] surfaceT0 in
    let luh_lhs = subst [surfaceTxy,`tt:int32`]
      `word_and (word_not (if word_igt (if word_ilt (tt:int32) (word 0) then word 43 else tt) (word 43)
                           then word 4294967295 else word 0)) (if word_ilt (tt:int32) (word 0) then word 43 else tt)` in
    let LUH0 = prove(mk_imp(`val(y:int32) <= 1`, mk_eq(luh_lhs, `mldsa_use_hint_88_x86_asm x y`)),
      DISCH_TAC THEN REWRITE_TAC[mldsa_use_hint_88_x86_asm] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[SHL_190464] THEN
      REWRITE_TAC[A1HI_ZERO_88; JOIN_ZERO_ZX] THEN ASM_SIMP_TAC[DELTA_EQ_BOUNDED] THEN
      REWRITE_TAC[LANE_AC_CLOSE_88] THEN REWRITE_TAC[TAIL_CLOSE_88]) in
    let LUH_GEN = GENL [`x:int32`;`y:int32`] LUH0 in
    let a1p_term = (match snd(strip_comb surfaceTxy) with [_;a]->a|_->failwith "T") in
    let dsh_term = (match snd(strip_comb surfaceTxy) with [s0;_]->rand s0|_->failwith "T") in
    let A1P_BOUND = BITBLAST_RULE (mk_binop `(<=):num->num->bool` (mk_comb(`val:int32->num`,a1p_term)) `44`) in
    let RANGE_FINAL_BB = BITBLAST_RULE
      `!A1P:int32 DSH:int32. val A1P <= 44 /\ (DSH = word 0 \/ DSH = word 2)
         ==> (val(word_add (word_sub (word 1) DSH) A1P) <= 45 \/
              word_add (word_sub (word 1) DSH) A1P = word 4294967295)` in
    let Y0_BB = BITBLAST_RULE `!A1P:int32. val A1P <= 44 ==> val(word_add (word_sub (word 0) (word 0)) A1P) <= 45` in
    let DSH_VALS = BITBLAST_RULE (mk_imp(`val(y:int32) <= 1`,
                     mk_disj(mk_eq(dsh_term,`word 0:int32`), mk_eq(dsh_term,`word 2:int32`)))) in
    let range_goal = mk_imp(`val(y:int32) <= 1`,
       mk_disj(mk_binop `(<=):num->num->bool` (mk_comb(`val:int32->num`,surfaceTxy)) `45`,
               mk_eq(surfaceTxy,`word 4294967295:int32`))) in
    let RANGE0 = prove(range_goal,
      DISCH_TAC THEN ABBREV_TAC (mk_eq(`A1P:int32`, a1p_term)) THEN
      SUBGOAL_THEN `val(A1P:int32) <= 44` ASSUME_TAC THENL
       [EXPAND_TAC "A1P" THEN ACCEPT_TAC A1P_BOUND; ALL_TAC] THEN
      SUBGOAL_THEN `(y:int32) = word 0 \/ y = word 1` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `val(y:int32) <= 1` THEN SPEC_TAC(`y:int32`,`y:int32`) THEN
        REWRITE_TAC[GSYM VAL_EQ_0; GSYM VAL_EQ_1] THEN ARITH_TAC; ALL_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[WORD_AND_0; WORD_SHL_0] THENL
       [DISJ1_TAC THEN MATCH_MP_TAC Y0_BB THEN ASM_REWRITE_TAC[];
        MP_TAC DSH_VALS THEN ASM_REWRITE_TAC[] THEN
        ABBREV_TAC (mk_eq(`DSH:int32`, dsh_term)) THEN DISCH_TAC THEN
        MATCH_MP_TAC RANGE_FINAL_BB THEN ASM_REWRITE_TAC[]]) in
    let RANGE_GEN = GENL [`x:int32`;`y:int32`] RANGE0 in
    let mk_blane k =
      let subB = mk_comb(mk_comb(`word_subword:int256->num#num->int32`,bvar),mk_pair(mk_small_numeral(32*k),`32`)) in
      let thA1 = GEN_REWRITE_CONV ONCE_DEPTH_CONV [GSYM bdef] subB in
      let inst_wsw = PART_MATCH (lhs o snd o dest_imp) WORD_SUBWORD_WORD (rand(concl thA1)) in
      let side_th = EQT_ELIM((REWRITE_CONV[DIMINDEX_256] THENC NUM_REDUCE_CONV)(fst(dest_imp(concl inst_wsw)))) in
      let stepA = TRANS thA1 (MP inst_wsw side_th) in
      let bml_i = INST (map2 (fun i bv -> (bv, mk_var("b"^string_of_int i,`:num`))) (0--31) bvals) (List.nth UH88_BYTEMOD_LANES k) in
      let bounds_th = end_itlist CONJ (map (fun bv -> CONV_RULE(RAND_CONV NUM_REDUCE_CONV)(REWRITE_RULE[DIMINDEX_8](ISPEC (rand bv) VAL_BOUND))) bvals) in
      let stepB = TRANS stepA (AP_TERM `word:num->int32` (MP bml_i bounds_th)) in
      let relabels = map (fun m -> uh88_byte_relabel prevar k m (if m=0 then `word 43:byte` else `word 0:byte`)) (0--3) in
      let stepC = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV relabels))) stepB in
      let v = vk k in
      let rng = ONCE_REWRITE_RULE[SYM(vcollk k)] (MP (SPECL [xk k;yk k] RANGE_GEN) (bndk k)) in
      let bc = MP (SPEC v BLEND_COLLAPSE_GEN) rng in
      TRANS stepC bc in
    let blanes = map mk_blane (0--7) in
    let vcolls = map vcollk (0--7) in
    let luhs = map (fun k -> MP (SPECL [xk k;yk k] LUH_GEN) (bndk k)) (0--7) in
    (MATCH_MP_TAC LANES8_EQ THEN CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[WORD_SUBWORD_AND] THEN REWRITE_TAC UH88_WSN THEN
     CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     REWRITE_TAC[simd8;simd4;simd2;DIMINDEX_32] THEN
     CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
     REWRITE_TAC blanes THEN REWRITE_TAC vcolls THEN REWRITE_TAC luhs) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Broadcast constants as 256-bit duplicates of their 32-bit lane value.     *)
(* ------------------------------------------------------------------------- *)
let DUPLITS_88 = map (fun (n,c) -> prove(mk_eq(mk_comb(`word:num->int256`, mk_numeral(Num.num_of_string n)),
                                            mk_comb(`word_duplicate:int32->int256`, c)), CONV_TAC WORD_BLAST))
  ["3423913227525323174502430081042878883520180111764122672559515536195711", `word 127:int32`;
   "303973398742897785767833851683137475682598667402680969552035729689816075", `word 11275:int32`;
   "3450873174198750916033945278531405488902228774061477969193842430181504", `word 128:int32`;
   "1159277706957392885855153492006644031428092478786277755276056441389099", `word 43:int32`;
   "223368118819536749293045209988780814485663464087451345989979032820788390912", `word 8285184:int32`];;

(* ------------------------------------------------------------------------- *)
(* Loop body (one iteration).                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLY_USE_HINT_88_BODY_BLOCK_TAC : tactic =
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`a:int64`;`i:num`] ALIGNED_BLOCK) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`h:int64`;`i:num`] ALIGNED_BLOCK) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes256 (word_add a (word(32*i)))) s0 = xb i` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if can (term_match []
        `!b. i <= b /\ b < 32 ==> read(memory :> bytes256(word_add a (word(32*b)))) s0 = xb b`) (concl th)
      then MP_TAC(SPEC `i:num` th) else failwith "no") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes256 (word_add h (word(32*i)))) s0 = yb i` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if can (term_match []
        `!b. b < 32 ==> read(memory :> bytes256(word_add h (word(32*b)))) s0 = yb b`) (concl th)
      then MP_TAC(SPEC `i:num` th) else failwith "no") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. k < 8 ==> val(word_subword ((yb:num->int256) i) (32*k,32):int32) <= 1` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if can (term_match []
        `!b k. b < 32 /\ k < 8 ==> val(word_subword ((yb:num->int256) b) (32*k,32):int32) <= 1`) (concl th)
      then MP_TAC(SPECL [`i:num`;`k:num`] th) else failwith "no") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!b. i+1 <= b /\ b < 32 ==> read(memory :> bytes256(word_add a (word(32*b)))) s0 = xb b`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th -> if can (term_match []
        `!b. i <= b /\ b < 32 ==> read(memory :> bytes256(word_add a (word(32*b)))) s0 = xb b`) (concl th)
      then MP_TAC(SPEC `b:num` th) else failwith "no") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
  EVERY (map (fun n -> X86_STEPS_TAC MLDSA_POLY_USE_HINT_88_EXEC [n] THEN SIMD_SIMPLIFY_TAC[] THEN ABBREV_BIG_TAC) (1--28)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN CONV_TAC WORD_RULE) THEN
  TRY(X_GEN_TAC `b:num` THEN DISCH_TAC THEN ASM_CASES_TAC `b < i` THENL
       [UNDISCH_TAC `b:num < i` THEN
        UNDISCH_TAC `!b. b < i ==> read (memory :> bytes256 (word_add a (word (32 * b)))) s28 = simd8 mldsa_use_hint_88_x86_asm (xb b) (yb b)` THEN
        MESON_TAC[];
        SUBGOAL_THEN `b:num = i` SUBST_ALL_TAC THENL
         [UNDISCH_TAC `b:num < i + 1` THEN UNDISCH_TAC `~(b:num < i)` THEN ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(fun th ->
          try let l,_ = dest_eq (concl th) in
              if l = `read (memory :> bytes256 (word_add a (word (32 * i)))) s28`
              then SUBST1_TAC th else failwith "no"
          with _ -> failwith "no") THEN
        ABBREV_TAC `av:int256 = (xb:num->int256) i` THEN
        ABBREV_TAC `hv:int256 = (yb:num->int256) i` THEN
        UH88_STORE_DISCHARGE_TAC]) THEN
  TRY(REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      FIRST_ASSUM(fun th -> if concl th = `i < 32` then MP_TAC th else failwith "no") THEN
      SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Block-function correctness.                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLY_USE_HINT_88_BLOCK_CORRECT = prove
 (`!a h xb yb pc.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, 0xdd) (a, 1024) /\ nonoverlapping (a, 1024) (h, 1024) /\
    (!b k. b < 32 /\ k < 8 ==> val(word_subword (yb b:int256) (32*k,32):int32) <= 1)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mldsa_poly_use_hint_88_tmc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [a; h] s /\
               (!b. b < 32 ==> read(memory :> bytes256(word_add a (word(32 * b)))) s = xb b) /\
               (!b. b < 32 ==> read(memory :> bytes256(word_add h (word(32 * b)))) s = yb b))
          (\s. read RIP s = word(pc + 0xdd) /\
               (!b. b < 32 ==>
                      read(memory :> bytes256(word_add a (word(32 * b)))) s =
                        simd8 mldsa_use_hint_88_x86_asm (xb b) (yb b)))
          (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
           MAYCHANGE [RAX; RCX; RDI; RSI; R8; R9; R10] ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6;
                      ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(a, 1024)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`;`h:int64`;`xb:num->int256`;`yb:num->int256`;`pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              fst MLDSA_POLY_USE_HINT_88_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_WHILE_PUP_TAC `32` `pc + 0x52` `pc + 0xd7`
   `\i s.
      (read RDI s = word_add a (word(32 * i)) /\
       read RSI s = word_add h (word(32 * i)) /\
       read RAX s = word(32 * i) /\
       read YMM8 s = (word_duplicate (word 11275:int32):int256) /\
       read YMM4 s = (word_duplicate (word 127:int32):int256) /\
       read YMM7 s = (word_duplicate (word 128:int32):int256) /\
       read YMM6 s = (word_duplicate (word 43:int32):int256) /\
       read YMM3 s = (word_duplicate (word 8285184:int32):int256) /\
       read YMM5 s = (word 0:int256) /\
       (!b. b < 32 ==> read(memory :> bytes256(word_add h (word(32 * b)))) s = yb b) /\
       (!b. i <= b /\ b < 32
            ==> read(memory :> bytes256(word_add a (word(32 * b)))) s = xb b) /\
       (!b. b < i
            ==> read(memory :> bytes256(word_add a (word(32 * b)))) s =
                simd8 mldsa_use_hint_88_x86_asm (xb b) (yb b)))
      /\
      (read ZF s <=> i = 32)` THEN
  REWRITE_TAC[ARITH_RULE `~(32 = 0)`] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THENL
  [
   REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
   ENSURES_INIT_TAC "s0" THEN
   X86_STEPS_TAC MLDSA_POLY_USE_HINT_88_EXEC (1--17) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC DUPLITS_88 THEN
   REWRITE_TAC[ARITH_RULE `b < 0 <=> F`; LE_0] THEN ASM_REWRITE_TAC[]
  ;
   MLDSA_POLY_USE_HINT_88_BODY_BLOCK_TAC
  ;
   REPEAT STRIP_TAC THEN X86_SIM_TAC MLDSA_POLY_USE_HINT_88_EXEC (1--1)
  ;
   REWRITE_TAC[ARITH_RULE `32 <= b /\ b < 32 <=> F`] THEN
   ENSURES_INIT_TAC "s0" THEN
   X86_STEPS_TAC MLDSA_POLY_USE_HINT_88_EXEC (1--1) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]
  ]);;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem (coefficient form, FIPS 204 UseHint).            *)
(* This must be kept in sync with the CBMC specification in                  *)
(* mldsa/src/native/x86_64/src/arith_native_x86_64.h                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLY_USE_HINT_88_CORRECT = prove
 (`!a h x y pc.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, 0xdd) (a, 1024) /\ nonoverlapping (a, 1024) (h, 1024)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mldsa_poly_use_hint_88_tmc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [a; h] s /\
               (!i. i < 256 ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 256 ==> read(memory :> bytes32(word_add h (word(4 * i)))) s = y i) /\
               (!i. i < 256 ==> val(x i:int32) < 8380417) /\
               (!i. i < 256 ==> val(y i:int32) <= 1))
          (\s. read RIP s = word(pc + 0xdd) /\
               (!i. i < 256 ==>
                      read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        word(mldsa_use_hint_88 (val(y i)) (val(x i)))) /\
               (!i. i < 256 ==>
                      val(read(memory :> bytes32(word_add a (word(4 * i)))) s) < 44))
          (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
           MAYCHANGE [RAX; RCX; RDI; RSI; R8; R9; R10] ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6;
                      ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(a, 1024)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`;`h:int64`;`x:num->int32`;`y:num->int32`;`pc:num`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `(!i. i < 256 ==> val(x i:int32) < 8380417) /\
                 (!i. i < 256 ==> val(y i:int32) <= 1)`
  THENL
  [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
   MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
   MAP_EVERY EXISTS_TAC
    [`\s. bytes_loaded s (word pc) (BUTLAST mldsa_poly_use_hint_88_tmc) /\
          read RIP s = word pc /\
          C_ARGUMENTS [a; h] s /\
          (!b. b < 32 ==> read(memory :> bytes256(word_add a (word(32 * b)))) s = pack8 x b) /\
          (!b. b < 32 ==> read(memory :> bytes256(word_add h (word(32 * b)))) s = pack8 y b)`;
     `\s. read RIP s = word(pc + 0xdd) /\
          (!b. b < 32 ==>
                 read(memory :> bytes256(word_add a (word(32 * b)))) s =
                   simd8 mldsa_use_hint_88_x86_asm (pack8 x b) (pack8 y b))`] THEN
   CONJ_TAC THENL
   [
    X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC `b:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC PACK8_MERGE THEN ASM_REWRITE_TAC[]
   ;
    CONJ_TAC THENL
    [
     X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN
       `!i. i < 256 ==>
              read(memory :> bytes32(word_add a (word(4 * i)))) s =
                mldsa_use_hint_88_x86_asm (x i) (y i)`
       ASSUME_TAC THENL
      [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
       SUBGOAL_THEN `4 * i = 4 * (8 * (i DIV 8) + i MOD 8)` SUBST1_TAC THENL
        [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
       MP_TAC(SPECL [`a:int64`;`s:x86state`;`i DIV 8`;`i MOD 8`] BLOCK_SPLIT) THEN
       ANTS_TAC THENL [SIMP_TAC[DIVISION; ARITH_EQ]; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN
       FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `i DIV 8` th)) THEN
       ANTS_TAC THENL [UNDISCH_TAC `i:num < 256` THEN ARITH_TAC; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN
       MP_TAC(SPECL [`mldsa_use_hint_88_x86_asm`;`pack8 x (i DIV 8)`;`pack8 y (i DIV 8)`;`i MOD 8`] SIMD8_LANE) THEN
       ANTS_TAC THENL [SIMP_TAC[DIVISION; ARITH_EQ]; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN
       MP_TAC(SPECL [`x:num->int32`;`i DIV 8`;`i MOD 8`] PACK8_LANE) THEN
       ANTS_TAC THENL [SIMP_TAC[DIVISION; ARITH_EQ]; ALL_TAC] THEN
       MP_TAC(SPECL [`y:num->int32`;`i DIV 8`;`i MOD 8`] PACK8_LANE) THEN
       ANTS_TAC THENL [SIMP_TAC[DIVISION; ARITH_EQ]; ALL_TAC] THEN
       DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
       SUBGOAL_THEN `8 * (i DIV 8) + i MOD 8 = i` SUBST1_TAC THENL
        [ARITH_TAC; REFL_TAC]; ALL_TAC] THEN
     CONJ_TAC THENL
     [
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `i:num` th)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `val(x (i:num):int32) < 8380417 /\ val(y (i:num):int32) <= 1` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(SPECL [`x (i:num):int32`;`y (i:num):int32`] ELEMENT_CORRECT_WORD_88) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      AP_TERM_TAC THEN
      MP_TAC(SPECL [`val(x (i:num):int32)`;`val(y (i:num):int32)`] MLDSA_USE_HINT_88_EQUIV) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])
     ;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `i:num` th)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `val(x (i:num):int32) < 8380417 /\ val(y (i:num):int32) <= 1` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(SPECL [`x (i:num):int32`;`y (i:num):int32`] ELEMENT_CORRECT_WORD_88) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      MATCH_MP_TAC(ARITH_RULE `n < 44 ==> n MOD 4294967296 < 44`) THEN
      REWRITE_TAC[mldsa_use_hint_88_code] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_ARITH_TAC
     ]
    ;
     MATCH_MP_TAC MLDSA_POLY_USE_HINT_88_BLOCK_CORRECT THEN
     ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     MP_TAC(SPECL [`y:num->int32`;`b:num`;`k:num`] PACK8_LANE) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
     FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `8 * b + k` th)) THEN
     ANTS_TAC THENL [UNDISCH_TAC `b:num < 32` THEN UNDISCH_TAC `k:num < 8` THEN ARITH_TAC;
                     REWRITE_TAC[]]
    ]]
  ;
   MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
   EXISTS_TAC `\s:x86state. F` THEN
   REWRITE_TAC[ENSURES_TRIVIAL] THEN
   GEN_TAC THEN POP_ASSUM MP_TAC THEN MESON_TAC[]]);;

(* ========================================================================= *)
(* Public subroutine correctness (with return).                              *)
(* ========================================================================= *)

let MLDSA_POLY_USE_HINT_88_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a h x y pc stackpointer returnaddress.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_tmc) (a, 1024) /\
    nonoverlapping (a, 1024) (h, 1024) /\
    nonoverlapping (stackpointer, 8) (a, 1024)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_poly_use_hint_88_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; h] s /\
               (!i. i < 256 ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 256 ==> read(memory :> bytes32(word_add h (word(4 * i)))) s = y i) /\
               (!i. i < 256 ==> val(x i:int32) < 8380417) /\
               (!i. i < 256 ==> val(y i:int32) <= 1))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (!i. i < 256 ==>
                      read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        word(mldsa_use_hint_88 (val(y i)) (val(x i)))) /\
               (!i. i < 256 ==>
                      val(read(memory :> bytes32(word_add a (word(4 * i)))) s) < 44))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a, 1024)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_poly_use_hint_88_tmc MLDSA_POLY_USE_HINT_88_CORRECT);;

let MLDSA_POLY_USE_HINT_88_SUBROUTINE_CORRECT = prove
 (`!a h x y pc stackpointer returnaddress.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_mc) (a, 1024) /\
    nonoverlapping (a, 1024) (h, 1024) /\
    nonoverlapping (stackpointer, 8) (a, 1024)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_poly_use_hint_88_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; h] s /\
               (!i. i < 256 ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 256 ==> read(memory :> bytes32(word_add h (word(4 * i)))) s = y i) /\
               (!i. i < 256 ==> val(x i:int32) < 8380417) /\
               (!i. i < 256 ==> val(y i:int32) <= 1))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (!i. i < 256 ==>
                      read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        word(mldsa_use_hint_88 (val(y i)) (val(x i)))) /\
               (!i. i < 256 ==>
                      val(read(memory :> bytes32(word_add a (word(4 * i)))) s) < 44))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a, 1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLY_USE_HINT_88_NOIBT_SUBROUTINE_CORRECT));;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(* Signature tuple for mldsa_poly_use_hint_88 (reads a and h, writes a in place),
   given inline to avoid touching the shared subroutine_signatures.ml table. *)
let mldsa_poly_use_hint_88_signature =
  ([(* args *)
     ("a", "int32_t[static 256]", "false");
     ("h", "int32_t[static 256]", "true")],
   "void",
   [(* input buffers *) ("a", "256", 4); ("h", "256", 4)],
   [(* output buffers *) ("a", "256", 4)],
   [(* temporary buffers *)]);;

let NORMALIZE_AND_EXPAND_YMM_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN EXPAND_MAYCHANGE_YMM_REGS_TAC;;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mldsa_poly_use_hint_88_signature
    (REWRITE_RULE[SOME_FLAGS] MLDSA_POLY_USE_HINT_88_CORRECT)
    MLDSA_POLY_USE_HINT_88_EXEC;;

let MLDSA_POLY_USE_HINT_88_SAFE =
  REWRITE_RULE [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS]
  (time prove
   (full_spec,
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
    GEN_PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
      ~tac_before_maychange_simp:NORMALIZE_AND_EXPAND_YMM_TAC
      MLDSA_POLY_USE_HINT_88_EXEC
      [BYTES_LOADED_APPEND_CLAUSE] X86_SINGLE_STEP_TAC));;

let MLDSA_POLY_USE_HINT_88_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a h pc stackpointer returnaddress.
          aligned 32 a /\ aligned 32 h /\
          nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_tmc) (a, 1024) /\
          nonoverlapping (a, 1024) (h, 1024) /\
          nonoverlapping (stackpointer, 8) (a, 1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_poly_use_hint_88_tmc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a; h] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a h pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,1024; h,1024; stackpointer,8]
                                               [a,1024; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_poly_use_hint_88_tmc MLDSA_POLY_USE_HINT_88_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_POLY_USE_HINT_88_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a h pc stackpointer returnaddress.
          aligned 32 a /\ aligned 32 h /\
          nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_mc) (a, 1024) /\
          nonoverlapping (a, 1024) (h, 1024) /\
          nonoverlapping (stackpointer, 8) (a, 1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_poly_use_hint_88_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a; h] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a h pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [a,1024; h,1024; stackpointer,8]
                                               [a,1024; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLY_USE_HINT_88_NOIBT_SUBROUTINE_SAFE));;


(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* The low halves of xmm6..xmm12 are callee-saved under the Microsoft x64    *)
(* ABI, so the Windows variant spills them (plus rdi/rsi) to a 128-byte      *)
(* stack frame in the prologue and restores them in the epilogue. The core   *)
(* SysV body is spliced in via BIGSTEP and the epilogue reasoned directly.   *)
(* ------------------------------------------------------------------------- *)

let mldsa_poly_use_hint_88_windows_mc = define_from_elf
   "mldsa_poly_use_hint_88_windows_mc" "x86/mldsa/mldsa_poly_use_hint_88.obj";;

let mldsa_poly_use_hint_88_windows_tmc =
  define_trimmed "mldsa_poly_use_hint_88_windows_tmc" mldsa_poly_use_hint_88_windows_mc;;

let MLDSA_POLY_USE_HINT_88_WINDOWS_TMC_EXEC =
  X86_MK_EXEC_RULE mldsa_poly_use_hint_88_windows_tmc;;

let MLDSA_POLY_USE_HINT_88_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a h x y pc stackpointer returnaddress.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_windows_tmc) (a, 1024) /\
    nonoverlapping (a, 1024) (h, 1024) /\
    nonoverlapping (word_sub stackpointer (word 128), 136) (a, 1024) /\
    nonoverlapping (word_sub stackpointer (word 128), 136) (h, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_windows_tmc)
                   (word_sub stackpointer (word 128), 128)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_poly_use_hint_88_windows_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [a; h] s /\
               (!i. i < 256 ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 256 ==> read(memory :> bytes32(word_add h (word(4 * i)))) s = y i) /\
               (!i. i < 256 ==> val(x i:int32) < 8380417) /\
               (!i. i < 256 ==> val(y i:int32) <= 1))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (!i. i < 256 ==>
                      read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        word(mldsa_use_hint_88 (val(y i)) (val(x i)))) /\
               (!i. i < 256 ==>
                      val(read(memory :> bytes32(word_add a (word(4 * i)))) s) < 44))
          (MAYCHANGE [RSP] ,,
           WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 128), 128)] ,,
           MAYCHANGE [memory :> bytes(a, 1024)])`,
  REPLICATE_TAC 5 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 128 THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fst MLDSA_POLY_USE_HINT_88_WINDOWS_TMC_EXEC] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN

  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "init_xmm6" `ZMM6 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm7" `ZMM7 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm8" `ZMM8 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm9" `ZMM9 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm10" `ZMM10 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm11" `ZMM11 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm12" `ZMM12 :> bottomhalf :> bottomhalf` THEN

  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM [YMM6;YMM7;YMM8;YMM9;YMM10;YMM11;YMM12]) THEN

  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN
  GHOST_INTRO_TAC `init_ymm11:int256` `read YMM11` THEN
  GHOST_INTRO_TAC `init_ymm12:int256` `read YMM12` THEN

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_POLY_USE_HINT_88_WINDOWS_TMC_EXEC (1--12) THEN

  MP_TAC(SPECL [`a:int64`; `h:int64`; `x:num->int32`; `y:num->int32`; `pc + 62`]
    MLDSA_POLY_USE_HINT_88_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; ALL; NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC MLDSA_POLY_USE_HINT_88_WINDOWS_TMC_EXEC "s13" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mldsa_poly_use_hint_88_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mldsa_poly_use_hint_88_tmc))
     62));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s13`;
    `ymm7_epilog = read YMM7 s13`;
    `ymm8_epilog = read YMM8 s13`;
    `ymm9_epilog = read YMM9 s13`;
    `ymm10_epilog = read YMM10 s13`;
    `ymm11_epilog = read YMM11 s13`;
    `ymm12_epilog = read YMM12 s13`] THEN

  X86_STEPS_TAC MLDSA_POLY_USE_HINT_88_WINDOWS_TMC_EXEC (22--32) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLDSA_POLY_USE_HINT_88_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a h x y pc stackpointer returnaddress.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_windows_mc) (a, 1024) /\
    nonoverlapping (a, 1024) (h, 1024) /\
    nonoverlapping (word_sub stackpointer (word 128), 136) (a, 1024) /\
    nonoverlapping (word_sub stackpointer (word 128), 136) (h, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_windows_mc)
                   (word_sub stackpointer (word 128), 128)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_poly_use_hint_88_windows_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [a; h] s /\
               (!i. i < 256 ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 256 ==> read(memory :> bytes32(word_add h (word(4 * i)))) s = y i) /\
               (!i. i < 256 ==> val(x i:int32) < 8380417) /\
               (!i. i < 256 ==> val(y i:int32) <= 1))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (!i. i < 256 ==>
                      read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        word(mldsa_use_hint_88 (val(y i)) (val(x i)))) /\
               (!i. i < 256 ==>
                      val(read(memory :> bytes32(word_add a (word(4 * i)))) s) < 44))
          (MAYCHANGE [RSP] ,,
           WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 128), 128)] ,,
           MAYCHANGE [memory :> bytes(a, 1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLY_USE_HINT_88_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Memory safety of Windows ABI version.                                      *)
(* Follows the mldsa_decompose_88 template: ASSUME_CALLEE_SAFETY_TAC on the   *)
(* SysV safety theorem, then the same ENSURES_PRESERVED/BIGSTEP prologue as   *)
(* the Windows CORRECT proof, finishing with DISCHARGE_SAFETY_PROPERTY_TAC.   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLY_USE_HINT_88_NOIBT_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events. forall e a h pc stackpointer returnaddress.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_windows_tmc) (a, 1024) /\
    nonoverlapping (a, 1024) (h, 1024) /\
    nonoverlapping (word_sub stackpointer (word 128), 136) (a, 1024) /\
    nonoverlapping (word_sub stackpointer (word 128), 136) (h, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_windows_tmc)
                   (word_sub stackpointer (word 128), 128)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_poly_use_hint_88_windows_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [a; h] s /\
               read events s = e)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a h pc (word_sub stackpointer (word 128)) returnaddress /\
                    memaccess_inbounds e2
                      [a,1024; h,1024; word_sub stackpointer (word 128),136]
                      [a,1024; word_sub stackpointer (word 128),136]))
          (MAYCHANGE [RSP] ,,
           WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 128), 128)] ,,
           MAYCHANGE [memory :> bytes(a, 1024)])`,
  ASSUME_CALLEE_SAFETY_TAC MLDSA_POLY_USE_HINT_88_SAFE "H_subth" THEN
  META_EXISTS_TAC THEN

  REPLICATE_TAC 4 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 128 THEN
  REPEAT GEN_TAC THEN

  REWRITE_TAC[fst MLDSA_POLY_USE_HINT_88_WINDOWS_TMC_EXEC] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN

  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "init_xmm6" `ZMM6 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm7" `ZMM7 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm8" `ZMM8 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm9" `ZMM9 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm10" `ZMM10 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm11" `ZMM11 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm12" `ZMM12 :> bottomhalf :> bottomhalf` THEN

  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM [YMM6;YMM7;YMM8;YMM9;YMM10;YMM11;YMM12]) THEN

  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN
  GHOST_INTRO_TAC `init_ymm11:int256` `read YMM11` THEN
  GHOST_INTRO_TAC `init_ymm12:int256` `read YMM12` THEN

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_POLY_USE_HINT_88_WINDOWS_TMC_EXEC (1--12) THEN

  W(fun (asl,w) ->
    let current_events = filter_map (fun (_,ath) -> let t = concl ath in
      if is_eq t && is_read_events (lhs t) then Some (rhs t)
      else None) asl in
    if length current_events <> 1
    then failwith "More than 'read events .. = ..?'"
    else
      REMOVE_THEN "H_subth"
        (MP_TAC o SPECL [hd current_events; `a:int64`; `h:int64`; `pc + 62`]))
  THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC MLDSA_POLY_USE_HINT_88_WINDOWS_TMC_EXEC "s13" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mldsa_poly_use_hint_88_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mldsa_poly_use_hint_88_tmc))
     62));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s13`;
    `ymm7_epilog = read YMM7 s13`;
    `ymm8_epilog = read YMM8 s13`;
    `ymm9_epilog = read YMM9 s13`;
    `ymm10_epilog = read YMM10 s13`;
    `ymm11_epilog = read YMM11 s13`;
    `ymm12_epilog = read YMM12 s13`] THEN

  X86_STEPS_TAC MLDSA_POLY_USE_HINT_88_WINDOWS_TMC_EXEC (22--32) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ DISCHARGE_SAFETY_PROPERTY_TAC; ALL_TAC ] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLDSA_POLY_USE_HINT_88_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events. forall e a h pc stackpointer returnaddress.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_windows_mc) (a, 1024) /\
    nonoverlapping (a, 1024) (h, 1024) /\
    nonoverlapping (word_sub stackpointer (word 128), 136) (a, 1024) /\
    nonoverlapping (word_sub stackpointer (word 128), 136) (h, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_88_windows_mc)
                   (word_sub stackpointer (word 128), 128)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_poly_use_hint_88_windows_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [a; h] s /\
               read events s = e)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a h pc (word_sub stackpointer (word 128)) returnaddress /\
                    memaccess_inbounds e2
                      [a,1024; h,1024; word_sub stackpointer (word 128),136]
                      [a,1024; word_sub stackpointer (word 128),136]))
          (MAYCHANGE [RSP] ,,
           WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 128), 128)] ,,
           MAYCHANGE [memory :> bytes(a, 1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLY_USE_HINT_88_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
