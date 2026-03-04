(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise multiplication and accumulation of polynomials in ML-DSA NTT    *)
(* x86 AVX2 implementation: c[i] = MontReduce(sum_{k=0}^{3} a_k[i]*b_k[i]) *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(*** print_literal_from_elf "x86/mldsa/mldsa_pointwise_acc_l4.o";;
 ***)

let mldsa_pointwise_acc_l4_mc = define_assert_from_elf "mldsa_pointwise_acc_l4_mc" "x86/mldsa/mldsa_pointwise_acc_l4.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xc5; 0xfd; 0x6f; 0x41; 0x20;
                           (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rcx,32))) *)
  0xc5; 0xfd; 0x6f; 0x09;  (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rcx,0))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc5; 0xfd; 0x6f; 0x36;  (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0x7d; 0x6f; 0x46; 0x20;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0x7d; 0x6f; 0x12;  (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0x7d; 0x6f; 0x62; 0x20;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0xc5; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd0; 0x20;
                           (* VPSRLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xda;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm12) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc2; 0x45; 0x28; 0xfb;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x42; 0x3d; 0x28; 0xc4;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x42; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0xd6;  (* VMOVDQA (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xfd; 0x6f; 0xdf;  (* VMOVDQA (%_% ymm3) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0xc4;  (* VMOVDQA (%_% ymm4) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0xcd;  (* VMOVDQA (%_% ymm5) (%_% ymm9) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0x00; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,1024))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x20; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,1056))) *)
  0xc5; 0x7d; 0x6f; 0x92; 0x00; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,1024))) *)
  0xc5; 0x7d; 0x6f; 0xa2; 0x20; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,1056))) *)
  0xc5; 0xc5; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd0; 0x20;
                           (* VPSRLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xda;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm12) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc2; 0x45; 0x28; 0xfb;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x42; 0x3d; 0x28; 0xc4;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x42; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xcd; 0xd4; 0xd2;  (* VPADDQ (%_% ymm2) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0xd4; 0xdb;  (* VPADDQ (%_% ymm3) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xbd; 0xd4; 0xe4;  (* VPADDQ (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0xb5; 0xd4; 0xed;  (* VPADDQ (%_% ymm5) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0x00; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,2048))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x20; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,2080))) *)
  0xc5; 0x7d; 0x6f; 0x92; 0x00; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,2048))) *)
  0xc5; 0x7d; 0x6f; 0xa2; 0x20; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,2080))) *)
  0xc5; 0xc5; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd0; 0x20;
                           (* VPSRLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xda;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm12) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc2; 0x45; 0x28; 0xfb;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x42; 0x3d; 0x28; 0xc4;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x42; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xcd; 0xd4; 0xd2;  (* VPADDQ (%_% ymm2) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0xd4; 0xdb;  (* VPADDQ (%_% ymm3) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xbd; 0xd4; 0xe4;  (* VPADDQ (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0xb5; 0xd4; 0xed;  (* VPADDQ (%_% ymm5) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0xfd; 0x6f; 0xb6; 0x00; 0x0c; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,3072))) *)
  0xc5; 0x7d; 0x6f; 0x86; 0x20; 0x0c; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rsi,3104))) *)
  0xc5; 0x7d; 0x6f; 0x92; 0x00; 0x0c; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,3072))) *)
  0xc5; 0x7d; 0x6f; 0xa2; 0x20; 0x0c; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,3104))) *)
  0xc5; 0xc5; 0x73; 0xd6; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm6) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x35; 0x73; 0xd0; 0x20;
                           (* VPSRLQ (%_% ymm9) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xda;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm12) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc2; 0x45; 0x28; 0xfb;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x42; 0x3d; 0x28; 0xc4;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm12) *)
  0xc4; 0x42; 0x35; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xcd; 0xd4; 0xd2;  (* VPADDQ (%_% ymm2) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0xc5; 0xd4; 0xdb;  (* VPADDQ (%_% ymm3) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xbd; 0xd4; 0xe4;  (* VPADDQ (%_% ymm4) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0xb5; 0xd4; 0xed;  (* VPADDQ (%_% ymm5) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm0) (%_% ymm2) *)
  0xc4; 0xe2; 0x7d; 0x28; 0xfb;
                           (* VPMULDQ (%_% ymm7) (%_% ymm0) (%_% ymm3) *)
  0xc4; 0x62; 0x7d; 0x28; 0xc4;
                           (* VPMULDQ (%_% ymm8) (%_% ymm0) (%_% ymm4) *)
  0xc4; 0x62; 0x7d; 0x28; 0xcd;
                           (* VPMULDQ (%_% ymm9) (%_% ymm0) (%_% ymm5) *)
  0xc4; 0xe2; 0x75; 0x28; 0xf6;
                           (* VPMULDQ (%_% ymm6) (%_% ymm1) (%_% ymm6) *)
  0xc4; 0xe2; 0x75; 0x28; 0xff;
                           (* VPMULDQ (%_% ymm7) (%_% ymm1) (%_% ymm7) *)
  0xc4; 0x42; 0x75; 0x28; 0xc0;
                           (* VPMULDQ (%_% ymm8) (%_% ymm1) (%_% ymm8) *)
  0xc4; 0x42; 0x75; 0x28; 0xc9;
                           (* VPMULDQ (%_% ymm9) (%_% ymm1) (%_% ymm9) *)
  0xc5; 0xed; 0xfb; 0xd6;  (* VPSUBQ (%_% ymm2) (%_% ymm2) (%_% ymm6) *)
  0xc5; 0xe5; 0xfb; 0xdf;  (* VPSUBQ (%_% ymm3) (%_% ymm3) (%_% ymm7) *)
  0xc4; 0xc1; 0x5d; 0xfb; 0xe0;
                           (* VPSUBQ (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x55; 0xfb; 0xe9;
                           (* VPSUBQ (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc5; 0xed; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xe3; 0x6d; 0x02; 0xd3; 0xaa;
                           (* VPBLENDD (%_% ymm2) (%_% ymm2) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xe3; 0x5d; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0x48; 0x83; 0xc6; 0x40;  (* ADD (% rsi) (Imm8 (word 64)) *)
  0x48; 0x83; 0xc2; 0x40;  (* ADD (% rdx) (Imm8 (word 64)) *)
  0x48; 0x83; 0xc7; 0x40;  (* ADD (% rdi) (Imm8 (word 64)) *)
  0x83; 0xc0; 0x01;        (* ADD (% eax) (Imm8 (word 1)) *)
  0x83; 0xf8; 0x10;        (* CMP (% eax) (Imm8 (word 16)) *)
  0x0f; 0x82; 0x3a; 0xfe; 0xff; 0xff;
                           (* JB (Imm32 (word 4294966842)) *)
  0xc3                     (* RET *)
];;

let mldsa_pointwise_acc_l4_tmc = define_trimmed "mldsa_pointwise_acc_l4_tmc" mldsa_pointwise_acc_l4_mc;;
let MLDSA_POINTWISE_ACC_L4_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_pointwise_acc_l4_tmc;;

(* ========================================================================= *)
(* Specification                                                             *)
(* ========================================================================= *)

let mldsa_pointwise_acc_l4 = define
 `mldsa_pointwise_acc_l4 (f:num->int) (g:num->int) i =
    ((f i * g i +
      f (i + 256) * g (i + 256) +
      f (i + 512) * g (i + 512) +
      f (i + 768) * g (i + 768)) *
     &(inverse_mod 8380417 4294967296)) rem &8380417`;;

let mldsa_pointwise_acc_l4_consts = define
 `mldsa_pointwise_acc_l4_consts:int list =
   [&8380417; &8380417; &8380417; &8380417;
    &8380417; &8380417; &8380417; &8380417;
    &58728449; &58728449; &58728449; &58728449;
    &58728449; &58728449; &58728449; &58728449]`;;

(* ========================================================================= *)
(* Auxiliary lemmas                                                          *)
(* ========================================================================= *)

let IVAL_WORD_MUL_SX32_64 = prove(
 `!x:int32 y:int32.
    abs(ival x) <= &75423752 /\ abs(ival y) <= &75423752
    ==> ival(word_mul (word_sx x:int64) (word_sx y:int64)) = ival x * ival y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_mul a b:int64 = iword(ival a * ival b)`] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `abs(ival(x:int32) * ival(y:int32)) <= &5688742365757504` MP_TAC THENL
   [REWRITE_TAC[INT_ABS_MUL] THEN
    MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&75423752 * &75423752:int` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_MUL2 THEN ASM_REWRITE_TAC[INT_ABS_POS];
      CONV_TAC INT_REDUCE_CONV];
    REWRITE_TAC[INT_ABS_BOUNDS] THEN CONV_TAC INT_REDUCE_CONV THEN
    INT_ARITH_TAC]);;

let Q_MUL_COMM = WORD_RULE
 `word_mul (word 8380417:int64) x = word_mul x (word 8380417:int64)`;;

let USHR32_SUBWORD = WORD_BLAST
 `word_subword (word_ushr (x:int64) 32) (0,32):int32 = word_subword x (32,32)`;;
let DUP32_SUBWORD = WORD_BLAST
 `word_subword (word_duplicate (word_subword (x:int64) (32,32):int32):int64) (0,32):int32
  = word_subword x (32,32)`;;

let WORD_JOIN_SUBWORD = WORD_BLAST
 `word_subword (word_join (a:int32) (b:int32):int64) (32,32):int32 = a`;;

(* ========================================================================= *)
(* Correctness proof                                                         *)
(* ========================================================================= *)

let MLDSA_POINTWISE_ACC_L4_CORRECT = prove
 (`!c a b consts x y pc.
    aligned 32 c /\
    aligned 32 a /\
    aligned 32 b /\
    aligned 32 consts /\
    nonoverlapping (word pc, 0x1D2) (c, 1024) /\
    nonoverlapping (word pc, 0x1D2) (a, 4096) /\
    nonoverlapping (word pc, 0x1D2) (b, 4096) /\
    nonoverlapping (word pc, 0x1D2) (consts, 64) /\
    nonoverlapping (c, 1024) (a, 4096) /\
    nonoverlapping (c, 1024) (b, 4096) /\
    nonoverlapping (c, 1024) (consts, 64) /\
    nonoverlapping (a, 4096) (b, 4096) /\
    nonoverlapping (a, 4096) (consts, 64) /\
    nonoverlapping (b, 4096) (consts, 64)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mldsa_pointwise_acc_l4_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [c; a; b; consts] s /\
              wordlist_from_memory(consts,16) s =
                MAP (iword: int -> 32 word) mldsa_pointwise_acc_l4_consts /\
              (!i. i < 1024 ==> abs(ival(x i)) <= &8380416) /\
              (!i. i < 1024 ==> abs(ival(y i)) <= &75423752) /\
              (!i. i < 1024 ==>
                read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
              (!i. i < 1024 ==>
                read(memory :> bytes32(word_add b (word(4 * i)))) s = y i))
          (\s. read RIP s = word(pc + 0x1D1) /\
              (!i. i < 256 ==>
                let zi = read(memory :> bytes32(word_add c (word(4 * i)))) s in
                (ival zi == mldsa_pointwise_acc_l4 (ival o x) (ival o y) i)
                  (mod &8380417) /\
                abs(ival zi) <= &8380416))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                      ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
           MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(c, 1024)])`,

  MAP_EVERY X_GEN_TAC
    [`c:int64`; `a:int64`; `b:int64`; `consts:int64`;
     `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  SUBGOAL_THEN
    `!i. i < 1024 ==> abs(ival((x:num->int32) i)) <= &75423752`
    ASSUME_TAC THENL
  [GEN_TAC THEN DISCH_TAC THEN
   MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&8380416:int` THEN
   CONJ_TAC THENL [ASM_MESON_TAC[]; CONV_TAC INT_REDUCE_CONV];
   ALL_TAC] THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [SOME_FLAGS; fst MLDSA_POINTWISE_ACC_L4_TMC_EXEC] THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `init_ymm2:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `init_ymm3:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `init_ymm4:int256` `read YMM4` THEN
  GHOST_INTRO_TAC `init_ymm5:int256` `read YMM5` THEN
  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN
  GHOST_INTRO_TAC `init_ymm11:int256` `read YMM11` THEN
  GHOST_INTRO_TAC `init_ymm12:int256` `read YMM12` THEN
  GHOST_INTRO_TAC `init_ymm13:int256` `read YMM13` THEN
  GHOST_INTRO_TAC `init_ymm14:int256` `read YMM14` THEN
  GHOST_INTRO_TAC `init_ymm15:int256` `read YMM15` THEN

  MAP_EVERY (fun n ->
    let vname = "init_c" ^ string_of_int n in
    GHOST_INTRO_TAC (mk_var(vname, `:int256`))
      (subst[mk_small_numeral(32*n),`n:num`]
        `read (memory :> bytes256(word_add c (word n)))`))
    (0--31) THEN
  ENSURES_INIT_TAC "s0" THEN

  MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add a (word n))) s0`)) (0--127))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  STRIP_TAC THEN

  MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add b (word n))) s0`)) (0--127))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  STRIP_TAC THEN

  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN

  FIRST_X_ASSUM(MP_TAC o CONV_RULE (LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  REWRITE_TAC[mldsa_pointwise_acc_l4_consts; MAP; CONS_11] THEN
  STRIP_TAC THEN
  MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add consts (word n))) s0`)) (0--1))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 consts) s = z`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  STRIP_TAC THEN

  (* Product bounds (tight: 8380416 * 75423752 = 632082418040832) *)
  SUBGOAL_THEN
   `!i. i < 1024 ==>
     abs(ival(word_mul (word_sx ((x:num->int32) i):int64)
                       (word_sx ((y:num->int32) i):int64))) <= &632082418040832`
   ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`(x:num->int32) i`; `(y:num->int32) i`] IVAL_WORD_MUL_SX32_64) THEN
   ANTS_TAC THENL
    [ASM_MESON_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
   REWRITE_TAC[INT_ABS_MUL] THEN
   MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&8380416 * &75423752:int` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC INT_LE_MUL2 THEN REWRITE_TAC[INT_ABS_POS] THEN ASM_MESON_TAC[];
     CONV_TAC INT_REDUCE_CONV];
   ALL_TAC] THEN

  MAP_EVERY (fun n -> X86_STEPS_TAC MLDSA_POINTWISE_ACC_L4_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[mldsa_pointwise_montred])
        (1--1411) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read qqq s1411:int256 = xxx`) o concl))) THEN

  CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[USHR32_SUBWORD; DUP32_SUBWORD] THEN
  REWRITE_TAC[Q_MUL_COMM; GSYM mldsa_pointwise_montred] THEN
  REWRITE_TAC[WORD_JOIN_SUBWORD] THEN
  
  W(fun (asl,w) ->
    let lfn = PROCESS_BOUND_ASSUMPTIONS
      (CONJUNCTS(tryfind (CONV_RULE EXPAND_CASES_CONV o snd) asl))
    in
    let prove_group =
      W(fun (asl,w) ->
        let mr = rand(lhand(rator(lhand w))) in
        MP_TAC(ASM_CONGBOUND_RULE lfn mr) THEN
        MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
         [REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 8380417 4294967296`] THEN
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
          REWRITE_TAC[GSYM INT_REM_EQ; o_THM; mldsa_pointwise_acc_l4;
                       INVERSE_MOD_CONV `inverse_mod 8380417 4294967296`] THEN
          CONV_TAC INT_REM_DOWN_CONV THEN
          CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
          REPEAT(W(fun (_,w) ->
            let prod = find_term
              (can (term_match []
                `ival(word_mul (word_sx (x:int32):int64) (word_sx (y:int32)))`)) w in
            let wm = rand prod in
            let xi = rand(rand(rator wm)) in
            let yi = rand(rand wm) in
            SUBGOAL_THEN (mk_eq(prod,
              mk_binop `( * ):int->int->int`
                (mk_comb(`ival:int32->int`, xi))
                (mk_comb(`ival:int32->int`, yi)))) SUBST1_TAC THENL
             [MATCH_MP_TAC IVAL_WORD_MUL_SX32_64 THEN
              CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
              ALL_TAC])) THEN
          CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
          AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC;
          REWRITE_TAC[INT_ABS_BOUNDS] THEN
          MATCH_MP_TAC(INT_ARITH
           `l':int <= l /\ u <= u'
            ==> l <= x /\ x <= u ==> l' <= x /\ x <= u'`) THEN
          CONV_TAC INT_REDUCE_CONV])
    in
    REPEAT(W(fun (_,w) ->
      if length(conjuncts w) > 2 then CONJ_TAC else NO_TAC)) THEN
    prove_group));;

(* ========================================================================= *)
(* Subroutine form                                                           *)
(* ========================================================================= *)

let MLDSA_POINTWISE_ACC_L4_NOIBT_SUBROUTINE_CORRECT = prove
 (`!c a b consts x y pc stackpointer returnaddress.
    aligned 32 c /\
    aligned 32 a /\
    aligned 32 b /\
    aligned 32 consts /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_acc_l4_tmc) (c, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_acc_l4_tmc) (a, 4096) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_acc_l4_tmc) (b, 4096) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_acc_l4_tmc) (consts, 64) /\
    nonoverlapping (c, 1024) (a, 4096) /\
    nonoverlapping (c, 1024) (b, 4096) /\
    nonoverlapping (c, 1024) (consts, 64) /\
    nonoverlapping (a, 4096) (b, 4096) /\
    nonoverlapping (a, 4096) (consts, 64) /\
    nonoverlapping (b, 4096) (consts, 64) /\
    nonoverlapping (stackpointer, 8) (c, 1024) /\
    nonoverlapping (stackpointer, 8) (a, 4096) /\
    nonoverlapping (stackpointer, 8) (b, 4096) /\
    nonoverlapping (stackpointer, 8) (consts, 64)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_pointwise_acc_l4_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [c; a; b; consts] s /\
              wordlist_from_memory(consts,16) s =
                MAP (iword: int -> 32 word) mldsa_pointwise_acc_l4_consts /\
              (!i. i < 1024 ==> abs(ival(x i)) <= &8380416) /\
              (!i. i < 1024 ==> abs(ival(y i)) <= &75423752) /\
              (!i. i < 1024 ==>
                read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
              (!i. i < 1024 ==>
                read(memory :> bytes32(word_add b (word(4 * i)))) s = y i))
          (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (!i. i < 256 ==>
                let zi = read(memory :> bytes32(word_add c (word(4 * i)))) s in
                (ival zi == mldsa_pointwise_acc_l4 (ival o x) (ival o y) i)
                  (mod &8380417) /\
                abs(ival zi) <= &8380416))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(c, 1024)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_pointwise_acc_l4_tmc
    (CONV_RULE TWEAK_CONV MLDSA_POINTWISE_ACC_L4_CORRECT));;

let MLDSA_POINTWISE_ACC_L4_SUBROUTINE_CORRECT = prove
 (`!c a b consts x y pc stackpointer returnaddress.
    aligned 32 c /\
    aligned 32 a /\
    aligned 32 b /\
    aligned 32 consts /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_acc_l4_mc) (c, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_acc_l4_mc) (a, 4096) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_acc_l4_mc) (b, 4096) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_acc_l4_mc) (consts, 64) /\
    nonoverlapping (c, 1024) (a, 4096) /\
    nonoverlapping (c, 1024) (b, 4096) /\
    nonoverlapping (c, 1024) (consts, 64) /\
    nonoverlapping (a, 4096) (b, 4096) /\
    nonoverlapping (a, 4096) (consts, 64) /\
    nonoverlapping (b, 4096) (consts, 64) /\
    nonoverlapping (stackpointer, 8) (c, 1024) /\
    nonoverlapping (stackpointer, 8) (a, 4096) /\
    nonoverlapping (stackpointer, 8) (b, 4096) /\
    nonoverlapping (stackpointer, 8) (consts, 64)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_pointwise_acc_l4_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [c; a; b; consts] s /\
              wordlist_from_memory(consts,16) s =
                MAP (iword: int -> 32 word) mldsa_pointwise_acc_l4_consts /\
              (!i. i < 1024 ==> abs(ival(x i)) <= &8380416) /\
              (!i. i < 1024 ==> abs(ival(y i)) <= &75423752) /\
              (!i. i < 1024 ==>
                read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
              (!i. i < 1024 ==>
                read(memory :> bytes32(word_add b (word(4 * i)))) s = y i))
          (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (!i. i < 256 ==>
                let zi = read(memory :> bytes32(word_add c (word(4 * i)))) s in
                (ival zi == mldsa_pointwise_acc_l4 (ival o x) (ival o y) i)
                  (mod &8380417) /\
                abs(ival zi) <= &8380416))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(c, 1024)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
    (CONV_RULE TWEAK_CONV MLDSA_POINTWISE_ACC_L4_NOIBT_SUBROUTINE_CORRECT)));;
