(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise multiplication of polynomials in NTT domain for ML-DSA.         *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(*** print_literal_from_elf "x86/mldsa/mldsa_pointwise.o";;
 ***)

let mldsa_pointwise_mc = define_assert_from_elf "mldsa_pointwise_mc" "x86/mldsa/mldsa_pointwise.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xc5; 0xfd; 0x6f; 0x01;  (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rcx,0))) *)
  0xc5; 0xfd; 0x6f; 0x49; 0x20;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rcx,32))) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0xc5; 0xfd; 0x6f; 0x16;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xfd; 0x6f; 0x66; 0x20;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xfd; 0x6f; 0x76; 0x40;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rsi,64))) *)
  0xc5; 0x7d; 0x6f; 0x12;  (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0x7d; 0x6f; 0x62; 0x20;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0x7d; 0x6f; 0x72; 0x40;
                           (* VMOVDQA (%_% ymm14) (Memop Word256 (%% (rdx,64))) *)
  0xc5; 0xe5; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xd5; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm4) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x16; 0xfe;  (* VMOVSHDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xc1; 0x25; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm11) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0xc1; 0x15; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm13) (%_% ymm12) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xfe;
                           (* VMOVSHDUP (%_% ymm15) (%_% ymm14) *)
  0xc4; 0xc2; 0x6d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc2; 0x65; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc2; 0x55; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc2; 0x4d; 0x28; 0xf6;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0xc2; 0x45; 0x28; 0xff;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm15) *)
  0xc4; 0x62; 0x7d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm0) (%_% ymm2) *)
  0xc4; 0x62; 0x7d; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm11) (%_% ymm0) (%_% ymm3) *)
  0xc4; 0x62; 0x7d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm0) (%_% ymm4) *)
  0xc4; 0x62; 0x7d; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm0) (%_% ymm5) *)
  0xc4; 0x62; 0x7d; 0x28; 0xf6;
                           (* VPMULDQ (%_% ymm14) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0x62; 0x7d; 0x28; 0xff;
                           (* VPMULDQ (%_% ymm15) (%_% ymm0) (%_% ymm7) *)
  0xc4; 0x42; 0x75; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm1) (%_% ymm10) *)
  0xc4; 0x42; 0x75; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm11) (%_% ymm1) (%_% ymm11) *)
  0xc4; 0x42; 0x75; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm1) (%_% ymm12) *)
  0xc4; 0x42; 0x75; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm1) (%_% ymm13) *)
  0xc4; 0x42; 0x75; 0x28; 0xf6;
                           (* VPMULDQ (%_% ymm14) (%_% ymm1) (%_% ymm14) *)
  0xc4; 0x42; 0x75; 0x28; 0xff;
                           (* VPMULDQ (%_% ymm15) (%_% ymm1) (%_% ymm15) *)
  0xc4; 0xc1; 0x6d; 0xfb; 0xd2;
                           (* VPSUBQ (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc1; 0x65; 0xfb; 0xdb;
                           (* VPSUBQ (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfb; 0xe4;
                           (* VPSUBQ (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc1; 0x55; 0xfb; 0xed;
                           (* VPSUBQ (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfb; 0xf6;
                           (* VPSUBQ (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc4; 0xc1; 0x45; 0xfb; 0xff;
                           (* VPSUBQ (%_% ymm7) (%_% ymm7) (%_% ymm15) *)
  0xc5; 0xed; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xdd; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm4) (%_% ymm4) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xe3; 0x6d; 0x02; 0xd3; 0xaa;
                           (* VPBLENDD (%_% ymm2) (%_% ymm2) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xe3; 0x5d; 0x02; 0xe5; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm5) (Imm8 (word 170)) *)
  0xc4; 0xe3; 0x4d; 0x02; 0xf7; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x77; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm6) *)
  0x48; 0x83; 0xc7; 0x60;  (* ADD (% rdi) (Imm8 (word 96)) *)
  0x48; 0x83; 0xc6; 0x60;  (* ADD (% rsi) (Imm8 (word 96)) *)
  0x48; 0x83; 0xc2; 0x60;  (* ADD (% rdx) (Imm8 (word 96)) *)
  0x83; 0xc0; 0x01;        (* ADD (% eax) (Imm8 (word 1)) *)
  0x83; 0xf8; 0x0a;        (* CMP (% eax) (Imm8 (word 10)) *)
  0x0f; 0x82; 0x07; 0xff; 0xff; 0xff;
                           (* JB (Imm32 (word 4294967047)) *)
  0xc5; 0xfd; 0x6f; 0x16;  (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,0))) *)
  0xc5; 0xfd; 0x6f; 0x66; 0x20;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0x7d; 0x6f; 0x12;  (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdx,0))) *)
  0xc5; 0x7d; 0x6f; 0x62; 0x20;
                           (* VMOVDQA (%_% ymm12) (Memop Word256 (%% (rdx,32))) *)
  0xc5; 0xe5; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xd5; 0x73; 0xd4; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm4) (Imm8 (word 32)) *)
  0xc4; 0x41; 0x7e; 0x16; 0xda;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xec;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm12) *)
  0xc4; 0xc2; 0x6d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc2; 0x65; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc2; 0x5d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc2; 0x55; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x7d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm0) (%_% ymm2) *)
  0xc4; 0x62; 0x7d; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm11) (%_% ymm0) (%_% ymm3) *)
  0xc4; 0x62; 0x7d; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm0) (%_% ymm4) *)
  0xc4; 0x62; 0x7d; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm0) (%_% ymm5) *)
  0xc4; 0x42; 0x75; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm1) (%_% ymm10) *)
  0xc4; 0x42; 0x75; 0x28; 0xdb;
                           (* VPMULDQ (%_% ymm11) (%_% ymm1) (%_% ymm11) *)
  0xc4; 0x42; 0x75; 0x28; 0xe4;
                           (* VPMULDQ (%_% ymm12) (%_% ymm1) (%_% ymm12) *)
  0xc4; 0x42; 0x75; 0x28; 0xed;
                           (* VPMULDQ (%_% ymm13) (%_% ymm1) (%_% ymm13) *)
  0xc4; 0xc1; 0x6d; 0xfb; 0xd2;
                           (* VPSUBQ (%_% ymm2) (%_% ymm2) (%_% ymm10) *)
  0xc4; 0xc1; 0x65; 0xfb; 0xdb;
                           (* VPSUBQ (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfb; 0xe4;
                           (* VPSUBQ (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc4; 0xc1; 0x55; 0xfb; 0xed;
                           (* VPSUBQ (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0xed; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm2) (%_% ymm2) (Imm8 (word 32)) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xe3; 0x65; 0x02; 0xd2; 0x55;
                           (* VPBLENDD (%_% ymm2) (%_% ymm3) (%_% ymm2) (Imm8 (word 85)) *)
  0xc4; 0xe3; 0x55; 0x02; 0xe4; 0x55;
                           (* VPBLENDD (%_% ymm4) (%_% ymm5) (%_% ymm4) (Imm8 (word 85)) *)
  0xc5; 0xfd; 0x7f; 0x17;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc3                     (* RET *)
];;

let mldsa_pointwise_tmc = define_trimmed "mldsa_pointwise_tmc" mldsa_pointwise_mc;;
let MLDSA_POINTWISE_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_pointwise_tmc;;

(* ------------------------------------------------------------------------- *)
(* Constants table: qinv (for Montgomery reduction) and Q (modulus)          *)
(* Both broadcasted 8 times for SIMD processing                             *)
(* ------------------------------------------------------------------------- *)

let mldsa_pointwise_consts = define
 `mldsa_pointwise_consts:int list =
   [&58728449; &58728449; &58728449; &58728449;
    &58728449; &58728449; &58728449; &58728449;
    &8380417; &8380417; &8380417; &8380417;
    &8380417; &8380417; &8380417; &8380417]`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof - Interactive version                                  *)
(* ------------------------------------------------------------------------- *)

g `!r a b consts x y pc.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 b /\
    aligned 32 consts /\
    nonoverlapping (word pc, 0x0199) (r, 1024) /\
    nonoverlapping (word pc, 0x0199) (a, 1024) /\
    nonoverlapping (word pc, 0x0199) (b, 1024) /\
    nonoverlapping (word pc, 0x0199) (consts, 64) /\
    nonoverlapping (r, 1024) (a, 1024) /\
    nonoverlapping (r, 1024) (b, 1024) /\
    nonoverlapping (r, 1024) (consts, 64) /\
    nonoverlapping (a, 1024) (b, 1024) /\
    nonoverlapping (a, 1024) (consts, 64) /\
    nonoverlapping (b, 1024) (consts, 64)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mldsa_pointwise_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [r; a; b; consts] s /\
              wordlist_from_memory(consts,16) s = 
                MAP (iword: int -> 32 word) mldsa_pointwise_consts /\
              (!i. i < 256 ==> abs(ival(x i)) <= &8380416) /\
              (!i. i < 256 ==> abs(ival(y i)) <= &8380416) /\
              (!i. i < 256 ==> 
                read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
              (!i. i < 256 ==> 
                read(memory :> bytes32(word_add b (word(4 * i)))) s = y i))
          (\s. read RIP s = word(pc + 0x0198) /\
              (!i. i < 256 ==>
                let zi = read(memory :> bytes32(word_add r (word(4 * i)))) s in
                (ival zi == mldsa_pointwise (ival o x) (ival o y) i)
                  (mod &8380417) /\
                abs(ival zi) <= &8380416))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; 
                      ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
           MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [memory :> bytes(r, 1024)])`;;

(*** Setup phase ***)
e(MAP_EVERY X_GEN_TAC 
    [`r:int64`; `a:int64`; `b:int64`; `consts:int64`; 
     `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [SOME_FLAGS; fst MLDSA_POINTWISE_TMC_EXEC]);;

(*** PHASE 2: Ghost variables - track all YMM register initial state ***)
e(GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
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
  ENSURES_INIT_TAC "s0");;

(*** Load and restructure memory from array a ***)
e(MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add a (word n))) s0`)) (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  STRIP_TAC);;

(*** Load and restructure memory from array b ***)
e(MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add b (word n))) s0`)) (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 b) s = y`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  STRIP_TAC);;

(*** Load constants (qinv and Q) ***)
e(FIRST_X_ASSUM(MP_TAC o CONV_RULE (LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  REWRITE_TAC[mldsa_pointwise_consts; MAP; CONS_11] THEN
  STRIP_TAC THEN
  MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add consts (word n))) s0`)) (0--1))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 consts) s = z`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  STRIP_TAC);;

(*** PHASE 6: Execute - simulate assembly with SIMD simplification ***)
e(MAP_EVERY (fun n -> X86_STEPS_TAC MLDSA_POINTWISE_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_ABBREV_TAC[mldsa_montmul] [])
        (1--543) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(*** Split 256-bit results back into 32-bit chunks ***)
e(REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read qqq s:int256 = xxx`) o concl))));;

(*** PHASE 8: Expand output cases ***)
e(CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[INT_ABS_BOUNDS; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  ASM_REWRITE_TAC[]);;

(*** Collect Montgomery multiplication abbreviations ***)
e(W(fun (asl,w) ->
     let asms =
        map snd (filter (is_local_definition [mldsa_montmul] o concl o snd) asl) in
     MP_TAC(end_itlist CONJ (rev asms)) THEN
     MAP_EVERY (fun t -> UNDISCH_THEN (concl t) (K ALL_TAC)) asms));;

(*** Simplify word operations ***)
e(REWRITE_TAC[WORD_BLAST `word_subword (x:int32) (0,32) = x`] THEN
  REWRITE_TAC[WORD_BLAST `word_subword (x:int64) (0,64) = x`] THEN
  REWRITE_TAC[WORD_BLAST
   `word_subword (word_ushr (word_join (h:int32) (l:int32):int64) 32) (0,32) = h`] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  STRIP_TAC);;

(*** Final verification: prove correctness and bounds ***)
e(CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  W(fun (asl,w) ->
    let lfn = PROCESS_BOUND_ASSUMPTIONS
      (CONJUNCTS(tryfind (CONV_RULE EXPAND_CASES_CONV o snd) asl))
    and asms =
      map snd (filter (is_local_definition [mldsa_montmul] o concl o snd) asl) in
    let lfn' = LOCAL_CONGBOUND_RULE lfn (rev asms) in

    REPEAT(GEN_REWRITE_TAC I
     [TAUT `p /\ q /\ r /\ s <=> (p /\ q /\ r) /\ s`] THEN CONJ_TAC) THEN
    W(MP_TAC o ASM_CONGBOUND_RULE lfn' o rand o lhand o rator o lhand o snd) THEN
   (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 8380417 4294967296`] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN 
      CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
      MATCH_MP_TAC(INT_ARITH
       `l':int <= l /\ u <= u'
        ==> l <= x /\ x <= u ==> l' <= x /\ x <= u'`) THEN
      CONV_TAC INT_REDUCE_CONV])));;

(* let MLDSA_POINTWISE_CORRECT = top_thm();; *)
