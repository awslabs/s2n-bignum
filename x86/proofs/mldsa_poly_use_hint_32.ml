(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Use hint to correct high bits of decomposition (ML-DSA, param 65/87).     *)
(* x86_64 AVX2 variant (GAMMA2 = (Q-1)/32).                                  *)
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

(**** print_literal_from_elf "x86/mldsa/mldsa_poly_use_hint_32.o";;
 ****)

let mldsa_poly_use_hint_32_mc = define_assert_from_elf
 "mldsa_poly_use_hint_32_mc" "x86/mldsa/mldsa_poly_use_hint_32.o"
(* BYTECODE START *)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb9; 0x7f; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 127)) *)
  0x41; 0xb8; 0x01; 0x04; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 1025)) *)
  0xc4; 0x41; 0x79; 0x6e; 0xc0;
                           (* VMOVD (%_% xmm8) (% r8d) *)
  0xc4; 0x42; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm8) (%_% xmm8) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc5; 0xc9; 0xef; 0xf6;  (* VPXOR (%_% xmm6) (%_% xmm6) (%_% xmm6) *)
  0xc5; 0xf9; 0x6e; 0xe9;  (* VMOVD (%_% xmm5) (% ecx) *)
  0xb9; 0x00; 0xe1; 0x7b; 0x00;
                           (* MOV (% ecx) (Imm32 (word 8118528)) *)
  0x41; 0xb9; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% r9d) (Imm32 (word 512)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xf9;
                           (* VMOVD (%_% xmm7) (% r9d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xff;
                           (* VPBROADCASTD (%_% ymm7) (%_% xmm7) *)
  0xc5; 0xf9; 0x6e; 0xe1;  (* VMOVD (%_% xmm4) (% ecx) *)
  0xb9; 0x0f; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 15)) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xed;
                           (* VPBROADCASTD (%_% ymm5) (%_% xmm5) *)
  0xc5; 0xf9; 0x6e; 0xd9;  (* VMOVD (%_% xmm3) (% ecx) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xe4;
                           (* VPBROADCASTD (%_% ymm4) (%_% xmm4) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0xc5; 0xfd; 0x6f; 0x07;  (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0x16;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xd5; 0xfe; 0xc8;  (* VPADDD (%_% ymm1) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xf5; 0x72; 0xd1; 0x07;
                           (* VPSRLD (%_% ymm1) (%_% ymm1) (Imm8 (word 7)) *)
  0xc4; 0xc1; 0x75; 0xe4; 0xc8;
                           (* VPMULHUW (%_% ymm1) (%_% ymm1) (%_% ymm8) *)
  0xc4; 0xe2; 0x75; 0x0b; 0xcf;
                           (* VPMULHRSW (%_% ymm1) (%_% ymm1) (%_% ymm7) *)
  0xc5; 0x7d; 0x66; 0xdc;  (* VPCMPGTD (%_% ymm11) (%_% ymm0) (%_% ymm4) *)
  0xc5; 0x25; 0xdf; 0xc9;  (* VPANDN (%_% ymm9) (%_% ymm11) (%_% ymm1) *)
  0xc5; 0xad; 0x72; 0xf1; 0x0a;
                           (* VPSLLD (%_% ymm10) (%_% ymm1) (Imm8 (word 10)) *)
  0xc5; 0xad; 0xfa; 0xc9;  (* VPSUBD (%_% ymm1) (%_% ymm10) (%_% ymm1) *)
  0xc5; 0xf5; 0x72; 0xf1; 0x09;
                           (* VPSLLD (%_% ymm1) (%_% ymm1) (Imm8 (word 9)) *)
  0xc5; 0xfd; 0xfa; 0xc1;  (* VPSUBD (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc4; 0xc1; 0x7d; 0xfe; 0xc3;
                           (* VPADDD (%_% ymm0) (%_% ymm0) (%_% ymm11) *)
  0xc5; 0xfd; 0x66; 0xc6;  (* VPCMPGTD (%_% ymm0) (%_% ymm0) (%_% ymm6) *)
  0xc5; 0xfd; 0xdf; 0xc2;  (* VPANDN (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0x72; 0xf0; 0x01;
                           (* VPSLLD (%_% ymm0) (%_% ymm0) (Imm8 (word 1)) *)
  0xc5; 0xed; 0xfa; 0xd0;  (* VPSUBD (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc4; 0xc1; 0x6d; 0xfe; 0xd1;
                           (* VPADDD (%_% ymm2) (%_% ymm2) (%_% ymm9) *)
  0xc5; 0xed; 0xdb; 0xd3;  (* VPAND (%_% ymm2) (%_% ymm2) (%_% ymm3) *)
  0xc5; 0xfd; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0x48; 0x83; 0xc7; 0x20;  (* ADD (% rdi) (Imm8 (word 32)) *)
  0x48; 0x83; 0xc6; 0x20;  (* ADD (% rsi) (Imm8 (word 32)) *)
  0x48; 0x83; 0xc0; 0x20;  (* ADD (% rax) (Imm8 (word 32)) *)
  0x48; 0x3d; 0x00; 0x04; 0x00; 0x00;
                           (* CMP (% rax) (Imm32 (word 1024)) *)
  0x75; 0x94;              (* JNE (Imm8 (word 148)) *)
  0xc3                     (* RET *)
];;
(* BYTECODE END *)

let mldsa_poly_use_hint_32_tmc =
  define_trimmed "mldsa_poly_use_hint_32_tmc" mldsa_poly_use_hint_32_mc;;

let MLDSA_POLY_USE_HINT_32_EXEC =
  X86_MK_CORE_EXEC_RULE mldsa_poly_use_hint_32_tmc;;

(* ------------------------------------------------------------------------- *)
(* Numeric (code-aligned) form of UseHint, matching the Barrett computation  *)
(* performed by the assembly. Bridged to the FIPS 204 spec                   *)
(* (mldsa_use_hint_32 in mldsa_specs.ml) by MLDSA_USE_HINT_32_EQUIV below.   *)
(* The decompose helper lemmas (A1_BOUND, A1_WRAP, BARRETT_INTERVAL_32) and  *)
(* the DIV/MOD equivalence tactics are specific to this x86_64 proof.         *)
(* ------------------------------------------------------------------------- *)

let mldsa_use_hint_32_code = new_definition
  `mldsa_use_hint_32_code (a:num) (h:num) =
   let a1 = ((((a + 127) DIV 128) * 1025 + 2097152) DIV 4194304) MOD 16 in
   let a0:int = &a - &a1 * &523776 in
   let a0' = if a0 > &4190208 then a0 - &8380417 else a0 in
   if h = 0 then a1
   else if a0' > &0 then (a1 + 1) MOD 16
   else (a1 + 15) MOD 16`;;

let A1_BOUND = prove(
  `!a. a < 8380417
   ==> ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304 <= 16`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `128` (SPEC `8380416 + 127` (SPEC `a + 127` DIV_MONO))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ABBREV_TAC `d = (a + 127) DIV 128` THEN
  MP_TAC(SPEC `4194304` (SPEC `69205952` (SPEC `d * 1025 + 2097152` DIV_MONO))) THEN
  ANTS_TAC THENL
  [SUBGOAL_THEN `d * 1025 <= 65472 * 1025` MP_TAC THENL
   [ASM_SIMP_TAC[LE_MULT_RCANCEL]; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let A1_WRAP = prove(
  `!a. 8118528 < a /\ a < 8380417
   ==> ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304 = 16`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 <= ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304`
    ASSUME_TAC THENL
  [MP_TAC(SPEC `128` (SPEC `a + 127` (SPEC `8118529 + 127` DIV_MONO))) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
   ABBREV_TAC `d = (a + 127) DIV 128` THEN
   MP_TAC(SPEC `4194304` (SPEC `d * 1025 + 2097152` (SPEC `67108977` DIV_MONO))) THEN
   ANTS_TAC THENL
   [SUBGOAL_THEN `63427 * 1025 <= d * 1025` MP_TAC THENL
    [ASM_SIMP_TAC[LE_MULT_RCANCEL]; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPEC `a:num` A1_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_ARITH_TAC);;

let BARRETT_INTERVAL_32 = prove(
  `!a lo hi k.
    lo <= a /\ a <= hi /\
    k * 4194304 <= (lo + 127) DIV 128 * 1025 + 2097152 /\
    (hi + 127) DIV 128 * 1025 + 2097152 < (k + 1) * 4194304
    ==> ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304 = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC DIV_SANDWICH THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THENL
  [TRANS_TAC LE_TRANS `(lo + 127) DIV 128 * 1025 + 2097152` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ARITH_RULE `x + 2097152 <= y + 2097152 <=> x <= y`] THEN
   REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
   MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC;
   TRANS_TAC LET_TRANS `(hi + 127) DIV 128 * 1025 + 2097152` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ARITH_RULE `x + 2097152 <= y + 2097152 <=> x <= y`] THEN
   REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
   MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC]);;

(* The per-variant divisor is 2*GAMMA2 = 523776. The generic Barrett DIV/MOD
   tactics are shared from mldsa_utils.ml. *)
let LINEARIZE_DIV_MOD_TAC = LINEARIZE_DIV_MOD_BY_TAC 523776;;
let DIV_523776_TAC k = DIV_EQ_K_BY_TAC 523776 k;;
let DIV_MOD_TO_DIV_TAC = DIV_MOD_TO_DIV_BY_TAC 523776;;

(* Lower half nowrap: dismiss wrap cond, reduce, prove r DIV 523776 = k *)
let DECOMPOSE_R1_LOWER_TAC =
  SUBGOAL_THEN `~((&r:int) - &(r MOD 523776) = &8380416)` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_EQ] THEN LINEARIZE_DIV_MOD_TAC;
   ALL_TAC] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_DIV; NUM_OF_INT_OF_NUM] THEN
  DIV_MOD_TO_DIV_TAC THEN
  CONV_TAC SYM_CONV THEN
  LINEARIZE_DIV_MOD_TAC;;

(* Upper half nowrap: dismiss wrap cond, reduce, prove r DIV 523776 + 1 = k *)
let DECOMPOSE_R1_UPPER_TAC =
  SUBGOAL_THEN `r MOD 523776 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r MOD 523776 < 523776` ASSUME_TAC THENL
  [MP_TAC(SPECL [`r:num`; `523776`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((&r:int) - (&(r MOD 523776) - &523776) = &8380416)` (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[INT_ARITH `(a:int) - (b - c) = d <=> a + c - b = d`] THEN
   ASM_SIMP_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB; INT_OF_NUM_EQ] THEN
   LINEARIZE_DIV_MOD_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&r:int) - (&(r MOD 523776) - &523776) =
                &(r - r MOD 523776 + 523776)` SUBST1_TAC THENL
  [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_ADD] THEN
   INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_DIV; NUM_OF_INT_OF_NUM] THEN
  MP_TAC(SPECL [`r:num`; `523776`] (CONJUNCT1 DIVISION_SIMP)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r - r MOD 523776 + 523776 = 523776 * (r DIV 523776 + 1)`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`523776`; `r DIV 523776 + 1`] DIV_MULT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `r MOD 523776` (concl th) ||
    free_in `r DIV 523776` (concl th)))) THEN
  MP_TAC(SPECL [`r:num`; `523776`] (CONJUNCT1 DIVISION_SIMP)) THEN
  SPEC_TAC(`r MOD 523776`, `m:num`) THEN
  SPEC_TAC(`r DIV 523776`, `q:num`) THEN
  REPEAT GEN_TAC THEN ASM_ARITH_TAC;;

let DECOMPOSE_R1_NOWRAP_TAC =
  ASM_CASES_TAC `r MOD 523776 * 2 <= 523776` THEN ASM_REWRITE_TAC[] THEN
  TRY DECOMPOSE_R1_LOWER_TAC THEN TRY DECOMPOSE_R1_UPPER_TAC;;

let DECOMPOSE_32_R1_EQUIV = time prove(
  `!r. r < 8380417 ==>
   (((r + 127) DIV 128 * 1025 + 2097152) DIV 4194304) MOD 16 =
   decompose_32_r1 r`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `r <= 8118528` THENL
  [ALL_TAC;
   (* Wrap zone *)
   SUBGOAL_THEN `8118528 < r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `decompose_32_r1 r = 0` SUBST1_TAC THENL
   [REWRITE_TAC[decompose_32_r1; mldsa_decompose_32; mldsa_cmod] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN `r MOD 523776 <= r` ASSUME_TAC THENL
    [MESON_TAC[MOD_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `r MOD 523776 < 523776` ASSUME_TAC THENL
    [MP_TAC(SPECL [`r:num`; `523776`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `r MOD 523776 * 2 <= 523776` THEN ASM_REWRITE_TAC[] THENL
    [(* Lower wrap: r DIV 523776 = 16 *)
     SUBGOAL_THEN `r DIV 523776 = 16` ASSUME_TAC THENL
     [DIV_523776_TAC 16; ALL_TAC] THEN
     SUBGOAL_THEN `16 * 523776 + r MOD 523776 = r` MP_TAC THENL
     [MP_TAC(SPECL [`r:num`; `523776`] (CONJUNCT1 DIVISION_SIMP)) THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_EQ] THEN
     ASM_ARITH_TAC;
     (* Upper wrap: r DIV 523776 = 15 *)
     SUBGOAL_THEN `r DIV 523776 = 15` ASSUME_TAC THENL
     [DIV_523776_TAC 15; ALL_TAC] THEN
     SUBGOAL_THEN `15 * 523776 + r MOD 523776 = r` MP_TAC THENL
     [MP_TAC(SPECL [`r:num`; `523776`] (CONJUNCT1 DIVISION_SIMP)) THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `(&r:int) - (&(r MOD 523776) - &523776) =
                   &(r - r MOD 523776 + 523776)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_ADD] THEN
      INT_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
   MP_TAC(SPEC `r:num` A1_WRAP) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV] THEN
  (* Nowrap zone: unfold and do interval cascade *)
  REWRITE_TAC[decompose_32_r1; mldsa_decompose_32; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `r MOD 523776 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r MOD 523776 < 523776` ASSUME_TAC THENL
  [MP_TAC(SPECL [`r:num`; `523776`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  let intervals = [
    (0, 261888); (261889, 785664); (785665, 1309440);
    (1309441, 1833216); (1833217, 2356992); (2356993, 2880768);
    (2880769, 3404544); (3404545, 3928320); (3928321, 4452096);
    (4452097, 4975872); (4975873, 5499648); (5499649, 6023424);
    (6023425, 6547200); (6547201, 7070976); (7070977, 7594752);
    (7594753, 8118528)] in
  let mk_le hi =
    mk_comb(mk_comb(`(<=):num->num->bool`, mk_var("r",`:num`)),
            mk_small_numeral hi) in
  let apply_interval k (lo, hi) =
    let th = SPECL [`r:num`; mk_small_numeral lo;
                    mk_small_numeral hi; mk_small_numeral k]
                   BARRETT_INTERVAL_32 in
    MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DECOMPOSE_R1_NOWRAP_TAC in
  let rec cascade k = function
    | [(lo,hi)] -> apply_interval k (lo,hi)
    | (lo,hi)::rest ->
        ASM_CASES_TAC (mk_le hi) THENL
        [apply_interval k (lo,hi); cascade (k+1) rest]
    | [] -> failwith "empty" in
  cascade 0 intervals);;

let R1_IS_DIV_LOWER = prove(
  `!r. r < 8380417 /\ r MOD 523776 * 2 <= 523776 /\
       ~((&r:int) - &(r MOD 523776) = &8380416) ==>
   (((r + 127) DIV 128 * 1025 + 2097152) DIV 4194304) MOD 16 = r DIV 523776`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_32_R1_EQUIV) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `r:num` LOWER_NONWRAP_R1) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let R1_IS_DIV_PLUS1_UPPER = prove(
  `!r. r < 8380417 /\ ~(r MOD 523776 * 2 <= 523776) /\
       ~((&r:int) - (&(r MOD 523776) - &523776) = &8380416) ==>
   (((r + 127) DIV 128 * 1025 + 2097152) DIV 4194304) MOD 16 =
   r DIV 523776 + 1`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_32_R1_EQUIV) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `r:num` UPPER_NONWRAP_R1) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* Upper nowrap: substitute Barrett = r DIV 523776 + 1, use INT_MOD_RESIDUE *)
let R0_SIGN_UPPER_NOWRAP_TAC =
  MP_TAC(SPEC `r:num` R1_IS_DIV_PLUS1_UPPER) THEN
  ANTS_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPECL [`r:num`; `523776`] INT_MOD_RESIDUE)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `(a:int) - (b + &1) * c = a - b * c - c`] THEN
  REWRITE_TAC[INT_ARITH `x - &523776 > &0 <=> x > &523776`;
              INT_ARITH `x - &523776 - &8380417 > &0 <=> x > &8904193`;
              INT_OF_NUM_GT] THEN
  ASM_ARITH_TAC;;

(* Lower nowrap: substitute Barrett = r DIV 523776, use INT_MOD_RESIDUE *)
let R0_SIGN_LOWER_NOWRAP_TAC =
  MP_TAC(SPEC `r:num` R1_IS_DIV_LOWER) THEN
  ANTS_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPECL [`r:num`; `523776`] INT_MOD_RESIDUE)) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `x - &8380417 > &0 <=> x > &8380417`;
              INT_OF_NUM_GT] THEN
  ASM_ARITH_TAC;;

(* Wrap: derive 8118528 < r, use DECOMPOSE_32_R1_EQUIV to get Barrett = 0 *)
let R0_SIGN_WRAP_TAC =
  SUBGOAL_THEN `8118528 < r` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (fun th ->
     can (find_term (fun t -> t = `&8380416:int`)) (concl th) &&
     not(is_neg(concl th)))) THEN
   ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_EQ;
     INT_ARITH `(a:int) - (b - c) = d <=> a + c - b = d`;
     GSYM INT_OF_NUM_ADD] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_32_R1_EQUIV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[decompose_32_r1; mldsa_decompose_32; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[INT_MUL_LZERO; INT_SUB_RZERO] THEN
  REWRITE_TAC[INT_ARITH `x - &1 > &0 <=> x > &1`;
              INT_ARITH `(x - &523776) - &1 > &0 <=> x > &523777`;
              INT_ARITH `x - &8380417 > &0 <=> x > &8380417`;
              INT_OF_NUM_GT] THEN
  ASM_ARITH_TAC;;

let DECOMPOSE_32_R0_SIGN = time prove(
  `!r. r < 8380417 ==>
    let a1 = (((r + 127) DIV 128 * 1025 + 2097152) DIV 4194304) MOD 16 in
    let a0':int = if (&r:int) - &a1 * &523776 > &4190208
                  then &r - &a1 * &523776 - &8380417
                  else &r - &a1 * &523776 in
    (decompose_32_r0 r > &0 <=> a0' > &0) /\
    (decompose_32_r0 r <= &0 <=> ~(a0' > &0))`,
  GEN_TAC THEN DISCH_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_ARITH `(x:int) <= &0 <=> ~(x > &0)`] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> (p <=> q) /\ (~p <=> ~q)`) THEN
  REWRITE_TAC[decompose_32_r0; mldsa_decompose_32; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[SND; FST] THEN
  SUBGOAL_THEN `r MOD 523776 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r MOD 523776 < 523776` ASSUME_TAC THENL
  [MP_TAC(SPECL [`r:num`; `523776`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r MOD 523776 * 2 <= 523776` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY R0_SIGN_LOWER_NOWRAP_TAC THEN
  TRY R0_SIGN_UPPER_NOWRAP_TAC THEN
  TRY R0_SIGN_WRAP_TAC THEN
  TRY(
    (* Contradiction: lower nowrap with > 4190208 *)
    MP_TAC(SPEC `r:num` R1_IS_DIV_LOWER) THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
      (SPECL [`r:num`; `523776`] INT_MOD_RESIDUE)) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(&r:int) - &((((r + 127) DIV 128 * 1025 + 2097152) DIV
      4194304) MOD 16) * &523776 = &(r MOD 523776)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(&(r MOD 523776) > (&4190208:int))` MP_TAC THENL
    [REWRITE_TAC[INT_NOT_LT; INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[INT_OF_NUM_GT] THEN ASM_ARITH_TAC
  ));;

let MLDSA_USE_HINT_32_EQUIV = prove(
  `!r h. r < 8380417 /\ h <= 1
         ==> mldsa_use_hint_32 h r = mldsa_use_hint_32_code r h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MLDSA_USE_HINT_32_UNFOLD] THEN
  REWRITE_TAC[mldsa_use_hint_32_code] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_32_R1_EQUIV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_32_R0_SIGN) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ASM_CASES_TAC `h = 0` THENL
  [ASM_REWRITE_TAC[ARITH_RULE `~(0 = 1)`]; ALL_TAC] THEN
  SUBGOAL_THEN `h = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `decompose_32_r0 r > &0` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Element-level correctness: the per-coefficient word computed by the       *)
(* assembly equals the FIPS 204 UseHint of the input.                        *)
(* The assembly evaluates the code-aligned Barrett form directly             *)
(* (vpmulhuw + vpmulhrsw), which agrees with mldsa_use_hint_32_code; the     *)
(* code form equals the FIPS spec by MLDSA_USE_HINT_32_EQUIV.                *)
(* ------------------------------------------------------------------------- *)

(* Lane lemma: high 16 bits of the unsigned 16x16->32 multiply by 1025.      *)
let LANE_MULHUW = prove(`!u:16 word. val u < 65536 ==>
   val(word_subword (word_mul ((word_zx u):int32) ((word_zx (word 1025:16 word)):int32)) (16,16):16 word)
   = (val u * 1025) DIV 65536`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(word_mul ((word_zx (u:16 word)):int32) ((word_zx (word 1025:16 word)):int32)) = val u * 1025` SUBST1_TAC THENL
  [REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ZX_GEN; DIMINDEX_16; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
   SUBGOAL_THEN `val(u:16 word) MOD 4294967296 = val u` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `u:16 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `val(word 1025:16 word) = 1025` SUBST1_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `u:16 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN
  SUBGOAL_THEN `val(u:16 word) * 1025 < 65536 * 65536` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(65536 = 0)`] THEN ARITH_TAC);;

(* Lane lemma: the vpmulhrsw rounding-multiply lane by 512, for a 16-bit input
   below 1024 (the range of the m16 = round(t/B) intermediate). This is the
   second Barrett step:  a1_lane = ((m16 * 512) >> 14 + 1) >> 1. *)
let LANE_MULHRSW = prove(`!u:16 word. val u < 1024 ==>
   val(word_subword (word_add (word_ushr (word_mul ((word_sx u):int32)((word_sx (word 512:16 word)):int32)) 14) (word 1:int32)) (1,16) :16 word)
   = ((val u * 512) DIV 16384 + 1) DIV 2`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val((word_sx (u:16 word)):int32) = val u` ASSUME_TAC THENL
  [MATCH_MP_TAC VAL_WORD_SX_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val((word_sx (word 512:16 word)):int32) = 512` ASSUME_TAC THENL
  [SUBGOAL_THEN `val(word 512:16 word) = 512` ASSUME_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
   ASM_SIMP_TAC[VAL_WORD_SX_SMALL; ARITH_RULE `512 < 32768`]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_mul ((word_sx (u:16 word)):int32)((word_sx (word 512:16 word)):int32)) = val u * 512` ASSUME_TAC THENL
  [REWRITE_TAC[VAL_WORD_MUL] THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(word_add (word_ushr (word_mul ((word_sx (u:16 word)):int32)((word_sx (word 512:16 word)):int32)) 14) (word 1:int32)) = (val u * 512) DIV 16384 + 1` SUBST1_TAC THENL
  [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_USHR; VAL_WORD; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
   CONV_TAC NUM_REDUCE_CONV THEN
   MATCH_MP_TAC MOD_LT THEN
   SUBGOAL_THEN `(val(u:16 word) * 512) DIV 16384 <= 31` MP_TAC THENL
   [SUBGOAL_THEN `val(u:16 word) * 512 < 1024 * 512` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(16384=0)`] THEN ARITH_TAC; ALL_TAC] THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN
  SUBGOAL_THEN `(val(u:16 word) * 512) DIV 16384 + 1 <= 32` MP_TAC THENL
  [SUBGOAL_THEN `(val(u:16 word) * 512) DIV 16384 <= 31` MP_TAC THENL
   [SUBGOAL_THEN `val(u:16 word) * 512 < 1024 * 512` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(16384=0)`] THEN ARITH_TAC; ALL_TAC] THEN ARITH_TAC; ALL_TAC] THEN
  ARITH_TAC);;

(* Arithmetic bridge: the assembly's two rounding steps (vpmulhuw by 1025 giving
   m16 = (t*1025) DIV 2^16, then vpmulhrsw by 512 giving ((m16*512) DIV 2^14 + 1) DIV 2)
   equal the single code-form Barrett division (t*1025 + 2^21) DIV 2^22. *)
let MUL_DIV_512 = prove(`!m. (m * 512) DIV 16384 = m DIV 32`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `16384 = 512 * 32`] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN SIMP_TAC[DIV_MULT; ARITH_RULE `~(512=0)`]);;

let A1_TWOSTEP = prove(`!t. ((((t * 1025) DIV 65536) * 512) DIV 16384 + 1) DIV 2 =
                            (t * 1025 + 2097152) DIV 4194304`,
  GEN_TAC THEN REWRITE_TAC[MUL_DIV_512] THEN
  REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`t * 1025`; `2097152`] ROUND_DIV) THEN
  REWRITE_TAC[ARITH_RULE `~(2097152 = 0)`; ARITH_RULE `2 * 2097152 = 4194304`]);;

(* Composed per-lane Barrett a1: the full x86 decompose a1 lane (pre-shift t via
   VAL_T, vpmulhuw by 1025 via LANE_MULHUW, vpmulhrsw by 512 via LANE_MULHRSW) on
   a coefficient a:int32 with val a < Q equals the code-form a1 Barrett value
   ((val a + 127) DIV 128 * 1025 + 2097152) DIV 4194304. The (16,16)/(0,16) lane
   selections pick the relevant 16-bit halves; the multipliers appear as raw int32
   numerals (word 1025)/(word 512), bridged to the word_zx/word_sx lane forms of the
   helper lemmas by WORD_REDUCE_CONV. *)
let A1_LANE = prove(`!a:int32. val a < 8380417 ==>
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
                     (word 1025:int32))
                   (16,16) :16 word)):int32)
              (word 512:int32))
            14)
          (word 1:int32))
        (1,16) :16 word)
   = ((val a + 127) DIV 128 * 1025 + 2097152) DIV 4194304`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(word 1025:int32) = word_zx (word 1025:16 word)` SUBST1_TAC THENL
  [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `(word 512:int32) = word_sx (word 512:16 word)` SUBST1_TAC THENL
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
                    ((word_zx (word 1025:16 word)):int32)) (16,16) :16 word)
     = (t * 1025) DIV 65536`
    ASSUME_TAC THENL
  [MP_TAC(SPEC `u0:16 word` LANE_MULHUW) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
    `m16 = word_subword
             (word_mul ((word_zx (u0:16 word)):int32)
                       ((word_zx (word 1025:16 word)):int32)) (16,16) :16 word` THEN
  SUBGOAL_THEN `val(m16:16 word) = (t * 1025) DIV 65536` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(m16:16 word) < 1024` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(65536 = 0)`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `m16:16 word` LANE_MULHRSW) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_ACCEPT_TAC A1_TWOSTEP);;

(* ------------------------------------------------------------------------- *)
(* Decompose bound (no-wrap) and a0 upper bound, arch-independent num lemmas *)
(* shared with the AArch64 proof.                                            *)
(* ------------------------------------------------------------------------- *)
let A1_BOUND_NOWRAP = prove(
  `!a. a <= 8118528
   ==> ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304 <= 15`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `128` (SPEC `8118528 + 127` (SPEC `a + 127` DIV_MONO))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ABBREV_TAC `d = (a + 127) DIV 128` THEN
  MP_TAC(SPEC `4194304` (SPEC `67108802` (SPEC `d * 1025 + 2097152` DIV_MONO))) THEN
  ANTS_TAC THENL
  [SUBGOAL_THEN `d * 1025 <= 63426 * 1025` MP_TAC THENL
   [ASM_SIMP_TAC[LE_MULT_RCANCEL]; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let A0_UPPER_32 = prove(
  `!a. a <= 8118528
   ==> a < (((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304 + 1) * 523776`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `nv = ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304` THEN
  SUBGOAL_THEN `nv * 4194304 <= (a + 127) DIV 128 * 1025 + 2097152` ASSUME_TAC THENL
  [EXPAND_TAC "nv" THEN
   MP_TAC(SPECL [`(a + 127) DIV 128 * 1025 + 2097152`; `4194304`] (CONJUNCT1 DIVISION_SIMP)) THEN
   ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a + 127) DIV 128 <= 63426` ASSUME_TAC THENL
  [MP_TAC(SPEC `128` (SPEC `8118528 + 127` (SPEC `a + 127` DIV_MONO))) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `nv * 4194304 <= 63426 * 1025 + 2097152` ASSUME_TAC THENL
  [SUBGOAL_THEN `(a + 127) DIV 128 * 1025 <= 63426 * 1025` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `nv <= 15` ASSUME_TAC THENL
  [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The per-element x86 word model of UseHint (param 65/87), matching the     *)
(* scalar form SIMD_SIMPLIFY produces for one coefficient lane, plus the     *)
(* value/threshold lemmas used by ELEMENT_CORRECT.                           *)
(* ------------------------------------------------------------------------- *)
let mldsa_use_hint_32_x86_asm = new_definition
  `mldsa_use_hint_32_x86_asm (a:int32) (h:int32) : int32 =
   let t = word_ushr (word_add (word 127) a) 7 in
   let m16 = word_subword
               (word_mul (word_zx (word_subword t (0,16) :16 word) :int32)
                         (word 1025)) (16,16) :16 word in
   let a1lane = word_subword
                  (word_add
                    (word_ushr (word_mul (word_sx m16 :int32) (word 512)) 14)
                    (word 1)) (1,16) :16 word in
   let a1 = word_zx a1lane :int32 in
   let m:int32 = (if word_igt a (word 8118528) then word 4294967295
                  else word 0) in
   let a1' = word_and a1 (word_not m) in
   let a0 = word_add (word_sub a (word_mul a1 (word 523776))) m in
   let delta:int32 = word_or (word_neg(word(bitval(word_ile a0 (word 0)))))
                             (word 1) in
   word_and (word_add a1' (word_mul delta h)) (word 15)`;;

let A1_LANE_VAL = prove(
  `!a:int32. val a < 8380417
    ==> val(word_zx (word_subword
              (word_add (word_ushr (word_mul (word_sx (word_subword
                 (word_mul (word_zx (word_subword (word_ushr (word_add (word 127) a) 7) (0,16) :16 word) :int32)
                    (word 1025:int32)) (16,16) :16 word) :int32) (word 512:int32)) 14) (word 1:int32)) (1,16) :16 word) :int32)
        = ((val a + 127) DIV 128 * 1025 + 2097152) DIV 4194304`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `val(word_subword
              (word_add (word_ushr (word_mul (word_sx (word_subword
                 (word_mul (word_zx (word_subword (word_ushr (word_add (word 127) (a:int32)) 7) (0,16) :16 word) :int32)
                    (word 1025:int32)) (16,16) :16 word) :int32) (word 512:int32)) 14) (word 1:int32)) (1,16) :16 word)
    = ((val(a:int32) + 127) DIV 128 * 1025 + 2097152) DIV 4194304`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC A1_LANE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN MP_TAC(SPEC `val(a:int32)` A1_BOUND) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let WORD_IGT_THRESHOLD_X86_32 = BITBLAST_RULE
  `!a:int32. val a < 8380417 ==> (word_igt a (word 8118528:int32) <=> val a > 8118528)`;;

let WRAP_A0_NEGATIVE_X86 = BITBLAST_RULE
  `!a:int32. val a < 8380417 /\ val a > 8118528
   ==> bit 31 (word_add (word_sub a (word 8380416:int32)) (word 4294967295:int32))`;;

(* Bare (no +word 0) sign form, used in the no-wrap a0-sign bridge. *)
let WORD_SUB_SIGN_BARE = BITBLAST_RULE
  `!a:int32 b:int32. val b <= 7856640 /\ val a <= 8118528 ==>
   ((bit 31 (word_sub a b) \/ word_sub a b = word 0) <=> val a <= val b)`;;

(* Small word identities used to simplify the lane after the wrap/no-wrap mask
   is resolved (these specific shapes are not in the standard word library). *)
let WORD_ADD_LID = WORD_RULE `!x:N word. word_add (word 0) x = x`;;
let WORD_SUB_RZERO = WORD_RULE `!x:N word. word_sub x (word 0) = x`;;

(* word_ile against 0 reduces to "sign bit set or value zero". *)
let WORD_ILE_ZERO_X86_32 = WORD_ILE_ZERO_32;;

(* ------------------------------------------------------------------------- *)
(* Element correctness (value form): the per-lane x86 word model equals the  *)
(* scalar FIPS UseHint code for one coefficient, for val a < Q, val h <= 1.  *)
(* Case split is wrap (a > 87*GAMMA2 => a1 lane = 16, masked 0) vs no-wrap.  *)
(* ------------------------------------------------------------------------- *)
let ELEMENT_CORRECT = prove(
  `!a:int32 h:int32.
     val a < 8380417 /\ val h <= 1
     ==> val(mldsa_use_hint_32_x86_asm a h) = mldsa_use_hint_32_code (val a) (val h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mldsa_use_hint_32_x86_asm; mldsa_use_hint_32_code] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nv = ((val(a:int32) + 127) DIV 128 * 1025 + 2097152) DIV 4194304` THEN
  ABBREV_TAC
   `a1w:int32 =
      word_zx (word_subword
        (word_add (word_ushr (word_mul (word_sx (word_subword
                 (word_mul (word_zx (word_subword
                    (word_ushr (word_add (word 127) (a:int32)) 7) (0,16) :16 word) :int32)
                    (word 1025)) (16,16) :16 word) :int32)
              (word 512)) 14) (word 1)) (1,16) :16 word) :int32` THEN
  SUBGOAL_THEN `val(a1w:int32) = nv` ASSUME_TAC THENL
   [EXPAND_TAC "a1w" THEN EXPAND_TAC "nv" THEN
    MATCH_MP_TAC A1_LANE_VAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `nv <= 16` ASSUME_TAC THENL
   [MP_TAC(SPEC `val(a:int32)` A1_BOUND) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `word_igt (a:int32) (word 8118528:int32) <=> val a > 8118528`
    SUBST1_TAC THENL
   [MP_TAC(SPEC `a:int32` WORD_IGT_THRESHOLD_X86_32) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `val(a:int32) > 8118528` THEN ASM_REWRITE_TAC[] THENL
  [
    (* WRAP ZONE: nv = 16, a1 lane masked to 0. *)
    SUBGOAL_THEN `nv = 16` SUBST_ALL_TAC THENL
     [MP_TAC(SPEC `val(a:int32)` A1_WRAP) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `a1w:int32 = word 16` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `word_and (word 16:int32) (word_not (word 4294967295)) = word 0` SUBST1_TAC THENL
     [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `word_mul (word 16:int32) (word 523776) = word 8380416` SUBST1_TAC THENL
     [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[WORD_ADD_LID] THEN
    SUBGOAL_THEN `word_ile (word_add (word_sub (a:int32) (word 8380416)) (word 4294967295)) (word 0)` ASSUME_TAC THENL
     [REWRITE_TAC[WORD_ILE_ZERO_X86_32] THEN DISJ1_TAC THEN
      MP_TAC(SPEC `a:int32` WRAP_A0_NEGATIVE_X86) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
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
       [MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_GT; INT_GT](ASSUME `val(a:int32) > 8118528`)) THEN INT_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((&(val(a:int32)) - &8380417:int) > &0)` ASSUME_TAC THENL
       [MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT](ASSUME `val(a:int32) < 8380417`)) THEN INT_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[]]
  ;
    (* NO-WRAP ZONE: mask = 0, a1' = a1 lane = nv <= 15. *)
    SUBGOAL_THEN `nv <= 15` ASSUME_TAC THENL
     [MP_TAC(SPEC `val(a:int32)` A1_BOUND_NOWRAP) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `nv MOD 16 = nv` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_NOT_0; WORD_AND_REFL] THEN
    REWRITE_TAC[WORD_MUL_0; WORD_SUB_RZERO; WORD_ADD_0; WORD_ADD_LID] THEN
    SUBGOAL_THEN `val(word_mul (a1w:int32) (word 523776:int32)) = nv * 523776`
      ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_MUL; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `val(word 523776:int32) = 523776` SUBST1_TAC THENL
       [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC MOD_LT THEN
      SUBGOAL_THEN `nv * 523776 <= 15 * 523776` MP_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC;
        CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `nv * 523776 <= 7856640` ASSUME_TAC THENL
     [SUBGOAL_THEN `nv * 523776 <= 15 * 523776` MP_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC;
        CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `val(word_mul (a1w:int32) (word 523776:int32)) <= 7856640`
      ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
      `word_ile (word_sub (a:int32) (word_mul a1w (word 523776:int32))) (word 0)
       <=> ~(&(val a) - &nv * &523776 > &0)` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_ILE_ZERO_X86_32] THEN
      MP_TAC(ISPECL [`a:int32`; `word_mul (a1w:int32) (word 523776:int32)`]
        WORD_SUB_SIGN_BARE) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `val(a:int32) <= nv * 523776` THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_MUL]
          (REWRITE_RULE[GSYM INT_OF_NUM_LE]
            (ASSUME `val(a:int32) <= nv * 523776`))) THEN INT_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `nv * 523776 < val(a:int32)` ASSUME_TAC THENL
         [UNDISCH_TAC `~(val(a:int32) <= nv * 523776)` THEN ARITH_TAC; ALL_TAC] THEN
        MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_MUL]
          (REWRITE_RULE[GSYM INT_OF_NUM_LT]
            (ASSUME `nv * 523776 < val(a:int32)`))) THEN INT_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(int_gt (&(val(a:int32)) - &nv * &523776) (&4190208))`
      ASSUME_TAC THENL
     [REWRITE_TAC[INT_GT; INT_NOT_LT] THEN
      MP_TAC(SPEC `val(a:int32)` A0_UPPER_32) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_MUL;
        GSYM INT_OF_NUM_ADD] (ASSUME `val(a:int32) < (nv + 1) * 523776`)) THEN
      INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_GT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INT_GT]) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `val(h:int32) = 0` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `h:int32 = word 0` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[WORD_MUL_0; WORD_ADD_0; WORD_AND_ONES_32] THEN
      REWRITE_TAC[VAL_WORD_AND_15_32] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `h:int32 = word 1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_MUL_1_32] THEN
    ASM_CASES_TAC `&0 < &(val(a:int32)) - &nv * &523776` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `~(&(val(a:int32)) - &nv * &523776 > &0) <=> F` SUBST1_TAC THENL
       [REWRITE_TAC[INT_GT] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[VAL_WORD_AND_15_32; VAL_WORD_ADD; DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`; ARITH_RULE `4294967296 = 2 EXP 32`;
                  MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[VAL_WORD_1];
      SUBGOAL_THEN `~(&(val(a:int32)) - &nv * &523776 > &0) <=> T` SUBST1_TAC THENL
       [REWRITE_TAC[INT_GT] THEN POP_ASSUM MP_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[VAL_WORD_AND_15_32; VAL_WORD_ADD; DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`; ARITH_RULE `4294967296 = 2 EXP 32`;
                  MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
      REWRITE_TAC[ARITH_RULE `4294967295 = 15 + 268435455 * 16`;
                  ARITH_RULE `n + (15 + 268435455 * 16) = (n + 15) + 268435455 * 16`;
                  MOD_MULT_ADD]]] THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

(* Word form, directly usable in the loop body discharge. *)
let ELEMENT_CORRECT_WORD = prove(
  `!a:int32 h:int32.
     val a < 8380417 /\ val h <= 1
     ==> mldsa_use_hint_32_x86_asm a h = word(mldsa_use_hint_32_code (val a) (val h))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  AP_TERM_TAC THEN
  MP_TAC(SPECL [`a:int32`; `h:int32`] ELEMENT_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ------------------------------------------------------------------------- *)
(* Per-lane bridge from the raw SIMD-simplified body output to the lane model. *)
(* These convert the assembly's surface encodings (shift-based multiply, the *)
(* zero high half of the 16x16->32 multiply, the h-(andnot dlt h)<<1 delta)  *)
(* into the mldsa_use_hint_32_x86_asm model form.                            *)
(* ------------------------------------------------------------------------- *)

(* a1 * 2*GAMMA2 = a1*523776 computed as (a1<<10 - a1)<<9. *)
let SHL_523776 = BITBLAST_RULE
  `!a:int32. word_shl (word_sub (word_shl a 10) a) 9 = word_mul a (word 523776)`;;

(* The high 16-bit half of the VPMULHRSW lane uses multiplier (word 0), so it
   contributes nothing: the high a1 lane is zero. *)
let A1HI_ZERO = BITBLAST_RULE
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

(* Final commutativity closer used after the surface rewrites line up the lane. *)
let LANE_AC_CLOSE = prove
 (`!d m a:int32. word_and (word_add d (word_and m a)) (word 15) =
                 word_and (word_add (word_and a m) d) (word 15)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Distribution of the final vpand-by-15 (a 256-bit broadcast) over the SIMD
   word_join tree, pushing the &15 mask down to each 32-bit lane.  Used to line
   up the assembly's whole-vector mask with the per-lane &15 of the lane model. *)
let ANDDUP_256 = prove
 (`!a b:int128. word_and (word_join a b:int256) (word_duplicate (word 15:int32)) =
     word_join (word_and a (word_duplicate (word 15:int32):int128))
               (word_and b (word_duplicate (word 15:int32):int128))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let ANDDUP_128 = prove
 (`!a b:int64. word_and (word_join a b:int128) (word_duplicate (word 15:int32)) =
     word_join (word_and a (word_duplicate (word 15:int32):int64))
               (word_and b (word_duplicate (word 15:int32):int64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let ANDDUP_64 = prove
 (`!a b:int32. word_and (word_join a b:int64) (word_duplicate (word 15:int32)) =
     word_join (word_and a (word_duplicate (word 15:int32):int32))
               (word_and b (word_duplicate (word 15:int32):int32))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let DUP15_32 = prove
 (`word_duplicate (word 15:int32):int32 = word 15`, CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Discharge of the 256-bit block store: rewrite the raw SIMD result back to *)
(* simd8 mldsa_use_hint_32_x86_asm on the input lanes, using the per-lane    *)
(* hint bounds.                                                              *)
(* ------------------------------------------------------------------------- *)

(* word_subword distributes through word_not on each 32-bit lane. *)
let UH32_WSN = map (fun n -> prove(
    subst [mk_small_numeral n, `n:num`]
      `!z:int256. word_subword(word_not z) (n,32):int32 = word_not(word_subword z (n,32))`,
    GEN_TAC THEN MATCH_MP_TAC WORD_SUBWORD_NOT THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_256] THEN ARITH_TAC)) [0;32;64;96;128;160;192;224];;

(* Discharge of the 256-bit store equality: distribute the final &15 mask to
   each 32-bit lane, isolate the eight lanes, and rewrite each raw lane to the
   lane model via the LANE_USE_HINT bridge (built on the fly from the goal's own
   lane 0, instantiated at each of the eight 32-bit offsets and discharged from
   the per-lane hint bound). *)
let UH32_STORE_DISCHARGE_TAC : tactic =
  fun (asl,w) ->
    if not(is_eq w) ||
       not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="simd8" with _->false)) w)
    then failwith "not the store goal" else
    let bignum = rand (lhs w) in
    let dup15_lit = prove(mk_eq(bignum,`word_duplicate (word 15:int32):int256`), CONV_TAC WORD_BLAST) in
    let phase1 =
      REWRITE_TAC[dup15_lit] THEN REWRITE_TAC[ANDDUP_256;ANDDUP_128;ANDDUP_64;DUP15_32] THEN
      REWRITE_TAC([WORD_SUBWORD_AND;WORD_SUBWORD_OR] @ UH32_WSN) THEN
      CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) in
    let phase2 (asl2,w2) =
      let lhsI = lhs w2 in
      let rec deepest t = if (try fst(dest_const(fst(strip_comb t)))="word_join" with _->false) then deepest(rand t) else t in
      let lane0_raw = deepest lhsI in
      let a1lane_x = `word_subword (word_add (word_ushr (word_mul (word_sx (word_subword (word_mul (word_zx (word_subword (word_ushr (word_add (word 127) (x:int32)) 7) (0,16) :16 word) :int32) (word 1025)) (16,16) :16 word) :int32) (word 512)) 14) (word 1)) (1,16) :16 word` in
      let a0term = `word_add (word_sub x (word_mul (A:int32) (word 523776))) (if word_igt x (word 8118528) then word 4294967295 else word 0)` in
      let lane0_fn = subst [`x:int32`,`word_subword (av:int256) (0,32):int32`; `y:int32`,`word_subword (hv:int256) (0,32):int32`] lane0_raw in
      let luh = prove(
        mk_imp(`val(y:int32) <= 1`, mk_eq(lane0_fn, list_mk_comb(`mldsa_use_hint_32_x86_asm`,[`x:int32`;`y:int32`]))),
        DISCH_TAC THEN REWRITE_TAC[mldsa_use_hint_32_x86_asm] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[SHL_523776] THEN REWRITE_TAC[A1HI_ZERO; JOIN_ZERO_ZX] THEN
        ABBREV_TAC (mk_eq(`A:int32`, mk_comb(`word_zx:(16)word->int32`, a1lane_x))) THEN
        MP_TAC(SPECL [a0term; `y:int32`] DELTA_EQ_BOUNDED) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN MATCH_ACCEPT_TAC LANE_AC_CLOSE) in
      let lane_gen = GENL [`x:int32`;`y:int32`] luh in
      let bound_hyp = snd(find (fun (_,th) -> try concl th = `!k. k < 8 ==> val(word_subword (hv:int256) (32*k,32):int32) <= 1` with _->false) asl2) in
      let bridges = map (fun k ->
        let off = mk_small_numeral (32*k) in
        let xk = mk_comb(mk_comb(`word_subword:int256->num#num->int32`,`av:int256`),mk_pair(off,`32`)) in
        let yk = mk_comb(mk_comb(`word_subword:int256->num#num->int32`,`hv:int256`),mk_pair(off,`32`)) in
        let raw_bnd = MP (SPEC (mk_small_numeral k) bound_hyp)
                         (EQT_ELIM(NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral k) `8`))) in
        let raw_bnd = CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) raw_bnd in
        MP (SPECL [xk;yk] lane_gen) raw_bnd) (0--7) in
      (REWRITE_TAC[simd8;simd4;simd2;DIMINDEX_32] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
       REWRITE_TAC bridges THEN
       CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV)) (asl2,w2) in
    (phase1 THEN phase2) (asl,w);;

(* Broadcast constants as 256-bit duplicates of their 32-bit lane value. *)
let DUPLITS = map (fun (n,c) -> prove(mk_eq(mk_comb(`word:num->int256`, mk_numeral(Num.num_of_string n)),
                                            mk_comb(`word_duplicate:int32->int256`, c)), CONV_TAC WORD_BLAST))
  ["3423913227525323174502430081042878883520180111764122672559515536195711", `word 127:int32`;
   "27633945340263435069803077425739770516599878854789179050185066335437825", `word 1025:int32`;
   "13803492696795003664135781114125621955608915096245911876775369720726016", `word 512:int32`;
   "218875081946729975600369013236132924539112762223623301674088649976692072704", `word 8118528:int32`;
   "404399200101416122972727962327899080730729934460329449514903409786895", `word 15:int32`];;

(* ------------------------------------------------------------------------- *)
(* Loop body (one iteration): block i is read, eight UseHints are computed   *)
(* in the YMM lanes, and the corrected block is stored back; pointers and the *)
(* loop counter advance by one block.  Blocks below i (already done) and at  *)
(* or above i+1 (untouched) are preserved by the single 256-bit store.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLY_USE_HINT_32_BODY_BLOCK_TAC : tactic =
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
  EVERY (map (fun n -> X86_STEPS_TAC MLDSA_POLY_USE_HINT_32_EXEC [n] THEN SIMD_SIMPLIFY_TAC[]) (1--24)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN CONV_TAC WORD_RULE) THEN
  TRY(X_GEN_TAC `b:num` THEN DISCH_TAC THEN ASM_CASES_TAC `b < i` THENL
       [UNDISCH_TAC `b:num < i` THEN
        UNDISCH_TAC `!b. b < i ==> read (memory :> bytes256 (word_add a (word (32 * b)))) s24 = simd8 mldsa_use_hint_32_x86_asm (xb b) (yb b)` THEN
        MESON_TAC[];
        SUBGOAL_THEN `b:num = i` SUBST_ALL_TAC THENL
         [UNDISCH_TAC `b:num < i + 1` THEN UNDISCH_TAC `~(b:num < i)` THEN ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(fun th ->
          try let l,_ = dest_eq (concl th) in
              if l = `read (memory :> bytes256 (word_add a (word (32 * i)))) s24`
              then SUBST1_TAC th else failwith "no"
          with _ -> failwith "no") THEN
        ABBREV_TAC `av:int256 = (xb:num->int256) i` THEN
        ABBREV_TAC `hv:int256 = (yb:num->int256) i` THEN
        UH32_STORE_DISCHARGE_TAC]) THEN
  TRY(REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      FIRST_ASSUM(fun th -> if concl th = `i < 32` then MP_TAC th else failwith "no") THEN
      SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Block-function correctness: the routine maps each 256-bit input block     *)
(* through the SIMD UseHint, over 32 loop iterations.                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLY_USE_HINT_32_BLOCK_CORRECT = prove
 (`!a h xb yb pc.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, 0xbc) (a, 1024) /\ nonoverlapping (a, 1024) (h, 1024) /\
    (!b k. b < 32 /\ k < 8 ==> val(word_subword (yb b:int256) (32*k,32):int32) <= 1)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mldsa_poly_use_hint_32_tmc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [a; h] s /\
               (!b. b < 32 ==> read(memory :> bytes256(word_add a (word(32 * b)))) s = xb b) /\
               (!b. b < 32 ==> read(memory :> bytes256(word_add h (word(32 * b)))) s = yb b))
          (\s. read RIP s = word(pc + 0xbc) /\
               (!b. b < 32 ==>
                      read(memory :> bytes256(word_add a (word(32 * b)))) s =
                        simd8 mldsa_use_hint_32_x86_asm (xb b) (yb b)))
          (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
           MAYCHANGE [RAX; RCX; RDI; RSI; R8; R9] ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5;
                      ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(a, 1024)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`;`h:int64`;`xb:num->int256`;`yb:num->int256`;`pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              fst MLDSA_POLY_USE_HINT_32_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN REWRITE_TAC[SOME_FLAGS] THEN
  ENSURES_WHILE_PUP_TAC `32` `pc + 0x50` `pc + 0xba`
   `\i s.
      (read RDI s = word_add a (word(32 * i)) /\
       read RSI s = word_add h (word(32 * i)) /\
       read RAX s = word(32 * i) /\
       read YMM5 s = (word_duplicate (word 127:int32):int256) /\
       read YMM8 s = (word_duplicate (word 1025:int32):int256) /\
       read YMM7 s = (word_duplicate (word 512:int32):int256) /\
       read YMM4 s = (word_duplicate (word 8118528:int32):int256) /\
       read YMM6 s = (word 0:int256) /\
       read YMM3 s = (word_duplicate (word 15:int32):int256) /\
       (!b. b < 32 ==> read(memory :> bytes256(word_add h (word(32 * b)))) s = yb b) /\
       (!b. i <= b /\ b < 32
            ==> read(memory :> bytes256(word_add a (word(32 * b)))) s = xb b) /\
       (!b. b < i
            ==> read(memory :> bytes256(word_add a (word(32 * b)))) s =
                simd8 mldsa_use_hint_32_x86_asm (xb b) (yb b)))
      /\
      (read ZF s <=> i = 32)` THEN
  REWRITE_TAC[ARITH_RULE `~(32 = 0)`] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THENL
  [
   (* INIT: run the constant-setup block to the loop top. *)
   REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
   ENSURES_INIT_TAC "s0" THEN
   X86_STEPS_TAC MLDSA_POLY_USE_HINT_32_EXEC (1--17) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC DUPLITS THEN
   REWRITE_TAC[ARITH_RULE `b < 0 <=> F`; LE_0] THEN ASM_REWRITE_TAC[]
  ;
   (* BODY *)
   MLDSA_POLY_USE_HINT_32_BODY_BLOCK_TAC
  ;
   (* BACKEDGE *)
   REPEAT STRIP_TAC THEN X86_SIM_TAC MLDSA_POLY_USE_HINT_32_EXEC (1--1)
  ;
   (* EXIT: the invariant at i = 32 is the postcondition. *)
   REWRITE_TAC[ARITH_RULE `32 <= b /\ b < 32 <=> F`] THEN
   ENSURES_INIT_TAC "s0" THEN
   X86_STEPS_TAC MLDSA_POLY_USE_HINT_32_EXEC (1--1) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]
  ]);;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem (coefficient form, FIPS 204 UseHint).            *)
(* Input bounds appear as preconditions; the result is stated directly.      *)
(* This must be kept in sync with the CBMC specification in                  *)
(* mldsa/src/native/x86_64/src/arith_native_x86_64.h                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLY_USE_HINT_32_CORRECT = prove
 (`!a h x y pc.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, 0xbc) (a, 1024) /\ nonoverlapping (a, 1024) (h, 1024)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mldsa_poly_use_hint_32_tmc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [a; h] s /\
               (!i. i < 256 ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 256 ==> read(memory :> bytes32(word_add h (word(4 * i)))) s = y i) /\
               (!i. i < 256 ==> val(x i:int32) < 8380417) /\
               (!i. i < 256 ==> val(y i:int32) <= 1))
          (\s. read RIP s = word(pc + 0xbc) /\
               (!i. i < 256 ==>
                      read(memory :> bytes32(word_add a (word(4 * i)))) s =
                        word(mldsa_use_hint_32 (val(y i)) (val(x i)))) /\
               (!i. i < 256 ==>
                      val(read(memory :> bytes32(word_add a (word(4 * i)))) s) < 16))
          (MAYCHANGE [RIP] ,, MAYCHANGE [events] ,,
           MAYCHANGE [RAX; RCX; RDI; RSI; R8; R9] ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5;
                      ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bytes(a, 1024)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`;`h:int64`;`x:num->int32`;`y:num->int32`;`pc:num`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `(!i. i < 256 ==> val(x i:int32) < 8380417) /\
                 (!i. i < 256 ==> val(y i:int32) <= 1)`
  THENL
  [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
   MATCH_MP_TAC ENSURES_PREPOSTCONDITION_THM THEN
   MAP_EVERY EXISTS_TAC
   [`\s. bytes_loaded s (word pc) (BUTLAST mldsa_poly_use_hint_32_tmc) /\
         read RIP s = word pc /\
         C_ARGUMENTS [a; h] s /\
         (!b. b < 32 ==> read(memory :> bytes256(word_add a (word(32 * b)))) s = pack8 x b) /\
         (!b. b < 32 ==> read(memory :> bytes256(word_add h (word(32 * b)))) s = pack8 y b)`;
    `\s. read RIP s = word(pc + 0xbc) /\
         (!b. b < 32 ==>
                read(memory :> bytes256(word_add a (word(32 * b)))) s =
                  simd8 mldsa_use_hint_32_x86_asm (pack8 x b) (pack8 y b))`] THEN
  CONJ_TAC THENL
  [
   (* precondition strengthening: coefficient reads ==> block reads *)
   X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THEN X_GEN_TAC `b:num` THEN DISCH_TAC THEN
   MATCH_MP_TAC PACK8_MERGE THEN ASM_REWRITE_TAC[]
  ;
   CONJ_TAC THENL
   [
    (* postcondition weakening: block result ==> coefficient FIPS result + bound *)
    X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `!i. i < 256 ==>
             read(memory :> bytes32(word_add a (word(4 * i)))) s =
               mldsa_use_hint_32_x86_asm (x i) (y i)`
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
      MP_TAC(SPECL [`mldsa_use_hint_32_x86_asm`;`pack8 x (i DIV 8)`;`pack8 y (i DIV 8)`;`i MOD 8`] SIMD8_LANE) THEN
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
     MP_TAC(SPECL [`x (i:num):int32`;`y (i:num):int32`] ELEMENT_CORRECT_WORD) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
     AP_TERM_TAC THEN
     MP_TAC(SPECL [`val(x (i:num):int32)`;`val(y (i:num):int32)`] MLDSA_USE_HINT_32_EQUIV) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])
    ;
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `i:num` th)) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN SUBST1_TAC THEN
     SUBGOAL_THEN `val(x (i:num):int32) < 8380417 /\ val(y (i:num):int32) <= 1` STRIP_ASSUME_TAC THENL
      [ASM_SIMP_TAC[]; ALL_TAC] THEN
     MP_TAC(SPECL [`x (i:num):int32`;`y (i:num):int32`] ELEMENT_CORRECT_WORD) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
     CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
     MATCH_MP_TAC(ARITH_RULE `n < 16 ==> n MOD 4294967296 < 16`) THEN
     REWRITE_TAC[mldsa_use_hint_32_code] THEN
     CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
     REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]
    ]
   ;
    (* the block-function correctness specialised at xb = pack8 x, yb = pack8 y *)
    MATCH_MP_TAC MLDSA_POLY_USE_HINT_32_BLOCK_CORRECT THEN
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

let MLDSA_POLY_USE_HINT_32_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a h x y pc stackpointer returnaddress.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_tmc) (a, 1024) /\
    nonoverlapping (a, 1024) (h, 1024) /\
    nonoverlapping (stackpointer, 8) (a, 1024)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_poly_use_hint_32_tmc /\
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
                        word(mldsa_use_hint_32 (val(y i)) (val(x i)))) /\
               (!i. i < 256 ==>
                      val(read(memory :> bytes32(word_add a (word(4 * i)))) s) < 16))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a, 1024)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_poly_use_hint_32_tmc MLDSA_POLY_USE_HINT_32_CORRECT);;

let MLDSA_POLY_USE_HINT_32_SUBROUTINE_CORRECT = prove
 (`!a h x y pc stackpointer returnaddress.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_mc) (a, 1024) /\
    nonoverlapping (a, 1024) (h, 1024) /\
    nonoverlapping (stackpointer, 8) (a, 1024)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_poly_use_hint_32_mc /\
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
                        word(mldsa_use_hint_32 (val(y i)) (val(x i)))) /\
               (!i. i < 256 ==>
                      val(read(memory :> bytes32(word_add a (word(4 * i)))) s) < 16))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a, 1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLY_USE_HINT_32_NOIBT_SUBROUTINE_CORRECT));;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(* Signature tuple for mldsa_poly_use_hint_32 (reads a and h, writes a in place),
   given inline to avoid touching the shared subroutine_signatures.ml table. *)
let mldsa_poly_use_hint_32_signature =
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
    mldsa_poly_use_hint_32_signature
    (REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS]
       MLDSA_POLY_USE_HINT_32_CORRECT)
    MLDSA_POLY_USE_HINT_32_EXEC;;

let MLDSA_POLY_USE_HINT_32_SAFE =
  REWRITE_RULE [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS]
  (time prove
   (full_spec,
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
    GEN_PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
      ~tac_before_maychange_simp:NORMALIZE_AND_EXPAND_YMM_TAC
      MLDSA_POLY_USE_HINT_32_EXEC
      [BYTES_LOADED_APPEND_CLAUSE] X86_SINGLE_STEP_TAC));;

let MLDSA_POLY_USE_HINT_32_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a h pc stackpointer returnaddress.
          aligned 32 a /\ aligned 32 h /\
          nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_tmc) (a, 1024) /\
          nonoverlapping (a, 1024) (h, 1024) /\
          nonoverlapping (stackpointer, 8) (a, 1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_poly_use_hint_32_tmc /\
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
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_poly_use_hint_32_tmc MLDSA_POLY_USE_HINT_32_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_POLY_USE_HINT_32_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a h pc stackpointer returnaddress.
          aligned 32 a /\ aligned 32 h /\
          nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_mc) (a, 1024) /\
          nonoverlapping (a, 1024) (h, 1024) /\
          nonoverlapping (stackpointer, 8) (a, 1024)
          ==> ensures x86
               (\s.
                    bytes_loaded s (word pc) mldsa_poly_use_hint_32_mc /\
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
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLY_USE_HINT_32_NOIBT_SUBROUTINE_SAFE));;


(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* The low halves of xmm6..xmm11 are callee-saved under the Microsoft x64    *)
(* ABI, so the Windows variant spills them (plus rdi/rsi) to a 112-byte      *)
(* stack frame in the prologue and restores them in the epilogue. The core   *)
(* SysV body is spliced in via BIGSTEP and the epilogue reasoned directly.   *)
(* ------------------------------------------------------------------------- *)

let mldsa_poly_use_hint_32_windows_mc = define_from_elf
   "mldsa_poly_use_hint_32_windows_mc" "x86/mldsa/mldsa_poly_use_hint_32.obj";;

let mldsa_poly_use_hint_32_windows_tmc =
  define_trimmed "mldsa_poly_use_hint_32_windows_tmc" mldsa_poly_use_hint_32_windows_mc;;

let MLDSA_POLY_USE_HINT_32_WINDOWS_TMC_EXEC =
  X86_MK_EXEC_RULE mldsa_poly_use_hint_32_windows_tmc;;

let MLDSA_POLY_USE_HINT_32_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a h x y pc stackpointer returnaddress.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_windows_tmc) (a, 1024) /\
    nonoverlapping (a, 1024) (h, 1024) /\
    nonoverlapping (word_sub stackpointer (word 112), 120) (a, 1024) /\
    nonoverlapping (word_sub stackpointer (word 112), 120) (h, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_windows_tmc)
                   (word_sub stackpointer (word 112), 112)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_poly_use_hint_32_windows_tmc /\
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
                        word(mldsa_use_hint_32 (val(y i)) (val(x i)))) /\
               (!i. i < 256 ==>
                      val(read(memory :> bytes32(word_add a (word(4 * i)))) s) < 16))
          (MAYCHANGE [RSP] ,,
           WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 112), 112)] ,,
           MAYCHANGE [memory :> bytes(a, 1024)])`,
  REPLICATE_TAC 5 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 112 THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fst MLDSA_POLY_USE_HINT_32_WINDOWS_TMC_EXEC] THEN
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

  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM [YMM6;YMM7;YMM8;YMM9;YMM10;YMM11]) THEN

  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN
  GHOST_INTRO_TAC `init_ymm11:int256` `read YMM11` THEN

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_POLY_USE_HINT_32_WINDOWS_TMC_EXEC (1--11) THEN

  MP_TAC(SPECL [`a:int64`; `h:int64`; `x:num->int32`; `y:num->int32`; `pc + 53`]
    MLDSA_POLY_USE_HINT_32_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; ALL; NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC MLDSA_POLY_USE_HINT_32_WINDOWS_TMC_EXEC "s12" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mldsa_poly_use_hint_32_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mldsa_poly_use_hint_32_tmc))
     53));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s12`;
    `ymm7_epilog = read YMM7 s12`;
    `ymm8_epilog = read YMM8 s12`;
    `ymm9_epilog = read YMM9 s12`;
    `ymm10_epilog = read YMM10 s12`;
    `ymm11_epilog = read YMM11 s12`] THEN

  X86_STEPS_TAC MLDSA_POLY_USE_HINT_32_WINDOWS_TMC_EXEC (20--29) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLDSA_POLY_USE_HINT_32_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a h x y pc stackpointer returnaddress.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_windows_mc) (a, 1024) /\
    nonoverlapping (a, 1024) (h, 1024) /\
    nonoverlapping (word_sub stackpointer (word 112), 120) (a, 1024) /\
    nonoverlapping (word_sub stackpointer (word 112), 120) (h, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_windows_mc)
                   (word_sub stackpointer (word 112), 112)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_poly_use_hint_32_windows_mc /\
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
                        word(mldsa_use_hint_32 (val(y i)) (val(x i)))) /\
               (!i. i < 256 ==>
                      val(read(memory :> bytes32(word_add a (word(4 * i)))) s) < 16))
          (MAYCHANGE [RSP] ,,
           WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 112), 112)] ,,
           MAYCHANGE [memory :> bytes(a, 1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLY_USE_HINT_32_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Memory safety of Windows ABI version.                                      *)
(* Follows the mldsa_decompose_88 template: ASSUME_CALLEE_SAFETY_TAC on the   *)
(* SysV safety theorem, then the same ENSURES_PRESERVED/BIGSTEP prologue as   *)
(* the Windows CORRECT proof, finishing with DISCHARGE_SAFETY_PROPERTY_TAC.   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLY_USE_HINT_32_NOIBT_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events. forall e a h pc stackpointer returnaddress.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_windows_tmc) (a, 1024) /\
    nonoverlapping (a, 1024) (h, 1024) /\
    nonoverlapping (word_sub stackpointer (word 112), 120) (a, 1024) /\
    nonoverlapping (word_sub stackpointer (word 112), 120) (h, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_windows_tmc)
                   (word_sub stackpointer (word 112), 112)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_poly_use_hint_32_windows_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [a; h] s /\
               read events s = e)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a h pc (word_sub stackpointer (word 112)) returnaddress /\
                    memaccess_inbounds e2
                      [a,1024; h,1024; word_sub stackpointer (word 112),120]
                      [a,1024; word_sub stackpointer (word 112),120]))
          (MAYCHANGE [RSP] ,,
           WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 112), 112)] ,,
           MAYCHANGE [memory :> bytes(a, 1024)])`,
  ASSUME_CALLEE_SAFETY_TAC MLDSA_POLY_USE_HINT_32_SAFE "H_subth" THEN
  META_EXISTS_TAC THEN

  REPLICATE_TAC 4 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 112 THEN
  REPEAT GEN_TAC THEN

  REWRITE_TAC[fst MLDSA_POLY_USE_HINT_32_WINDOWS_TMC_EXEC] THEN
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

  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM [YMM6;YMM7;YMM8;YMM9;YMM10;YMM11]) THEN

  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN
  GHOST_INTRO_TAC `init_ymm11:int256` `read YMM11` THEN

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_POLY_USE_HINT_32_WINDOWS_TMC_EXEC (1--11) THEN

  W(fun (asl,w) ->
    let current_events = filter_map (fun (_,ath) -> let t = concl ath in
      if is_eq t && is_read_events (lhs t) then Some (rhs t)
      else None) asl in
    if length current_events <> 1
    then failwith "More than 'read events .. = ..?'"
    else
      REMOVE_THEN "H_subth"
        (MP_TAC o SPECL [hd current_events; `a:int64`; `h:int64`; `pc + 53`]))
  THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC MLDSA_POLY_USE_HINT_32_WINDOWS_TMC_EXEC "s12" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mldsa_poly_use_hint_32_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mldsa_poly_use_hint_32_tmc))
     53));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s12`;
    `ymm7_epilog = read YMM7 s12`;
    `ymm8_epilog = read YMM8 s12`;
    `ymm9_epilog = read YMM9 s12`;
    `ymm10_epilog = read YMM10 s12`;
    `ymm11_epilog = read YMM11 s12`] THEN

  X86_STEPS_TAC MLDSA_POLY_USE_HINT_32_WINDOWS_TMC_EXEC (20--29) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ DISCHARGE_SAFETY_PROPERTY_TAC; ALL_TAC ] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLDSA_POLY_USE_HINT_32_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events. forall e a h pc stackpointer returnaddress.
    aligned 32 a /\ aligned 32 h /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_windows_mc) (a, 1024) /\
    nonoverlapping (a, 1024) (h, 1024) /\
    nonoverlapping (word_sub stackpointer (word 112), 120) (a, 1024) /\
    nonoverlapping (word_sub stackpointer (word 112), 120) (h, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_windows_mc)
                   (word_sub stackpointer (word 112), 112)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_poly_use_hint_32_windows_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [a; h] s /\
               read events s = e)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a h pc (word_sub stackpointer (word 112)) returnaddress /\
                    memaccess_inbounds e2
                      [a,1024; h,1024; word_sub stackpointer (word 112),120]
                      [a,1024; word_sub stackpointer (word 112),120]))
          (MAYCHANGE [RSP] ,,
           WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 112), 112)] ,,
           MAYCHANGE [memory :> bytes(a, 1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POLY_USE_HINT_32_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
