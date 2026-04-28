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


(* ========================================================================= *)
(* Correctness proof                                                         *)
(* ========================================================================= *)

let MLDSA_POINTWISE_CORRECT = prove
 (`!r a b consts x y pc.
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
              (!i. i < 256 ==> abs(ival(x i)) <= &75423752) /\
              (!i. i < 256 ==> abs(ival(y i)) <= &75423752) /\
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
           MAYCHANGE [memory :> bytes(r, 1024)])`,

  (* Setup - strip quantifiers, introduce preconditions *)
  MAP_EVERY X_GEN_TAC
    [`r:int64`; `a:int64`; `b:int64`; `consts:int64`;
     `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [SOME_FLAGS; fst MLDSA_POINTWISE_TMC_EXEC] THEN

  (* Ghost variables for YMM registers *)
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

  (* Ghost reads from output region r (32 x 256-bit = 1024 bytes) *)
  MAP_EVERY (fun n ->
    let vname = "init_r" ^ string_of_int n in
    GHOST_INTRO_TAC (mk_var(vname, `:int256`))
      (subst[mk_small_numeral(32*n),`n:num`]
        `read (memory :> bytes256(word_add r (word n)))`))
    (0--31) THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Merge memory reads from array a *)
  MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add a (word n))) s0`)) (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  STRIP_TAC THEN

  (* Merge memory reads from array b *)
  MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add b (word n))) s0`)) (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  STRIP_TAC THEN

  (* Discard bytes32 reads (a and b are now merged into bytes256) *)
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN

  (* Merge constants memory *)
  FIRST_X_ASSUM(MP_TAC o CONV_RULE (LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  REWRITE_TAC[mldsa_pointwise_consts; MAP; CONS_11] THEN
  STRIP_TAC THEN
  MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add consts (word n))) s0`)) (0--1))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 consts) s = z`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  STRIP_TAC THEN

  (* Add product bounds as assumptions *)
  SUBGOAL_THEN
   `!i. i < 256 ==>
     abs(ival(word_mul (word_sx ((x:num->int32) i):int64)
                       (word_sx ((y:num->int32) i):int64))) <= &5688742365757504`
   ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`(x:num->int32) i`; `(y:num->int32) i`] IVAL_WORD_MUL_SX32_64) THEN
   ANTS_TAC THENL
    [ASM_MESON_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
   REWRITE_TAC[INT_ABS_MUL] THEN
   MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&75423752 * &75423752:int` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC INT_LE_MUL2 THEN REWRITE_TAC[INT_ABS_POS] THEN ASM_MESON_TAC[];
     CONV_TAC INT_REDUCE_CONV];
   ALL_TAC] THEN

  (* Execute all 543 instructions with SIMD simplification *)
  MAP_EVERY (fun n -> X86_STEPS_TAC MLDSA_POINTWISE_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[mldsa_pointwise_montred])
        (1--543) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN

  (* Split bytes256 -> bytes32 *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read qqq s543:int256 = xxx`) o concl))) THEN

  (* Expand output cases, substitute, collapse subwords, fold *)
  CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[USHR32_SUBWORD; DUP32_SUBWORD] THEN
  REWRITE_TAC[Q_MUL_COMM; GSYM mldsa_pointwise_montred] THEN
  REWRITE_TAC[WORD_JOIN_SUBWORD] THEN

  (* Prove postcondition - congruence + bounds for each coefficient *)
  W(fun (asl,w) ->
    let lfn = PROCESS_BOUND_ASSUMPTIONS
      (CONJUNCTS(tryfind (CONV_RULE EXPAND_CASES_CONV o snd) asl))
    in
    let prove_group =
      W(fun (asl,w) ->
        let mr = rand(lhand(rator(lhand w))) in
        MP_TAC(ASM_CONGBOUND_RULE lfn mr) THEN
        MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
         [(* Congruence branch *)
          REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 8380417 4294967296`] THEN
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
          REWRITE_TAC[GSYM INT_REM_EQ; o_THM; mldsa_pointwise;
                       INVERSE_MOD_CONV `inverse_mod 8380417 4294967296`] THEN
          CONV_TAC INT_REM_DOWN_CONV THEN
          W(fun (_,w) ->
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
              AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC]);
          (* Bounds branch *)
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

let MLDSA_POINTWISE_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a b consts x y pc stackpointer returnaddress.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 b /\
    aligned 32 consts /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_tmc) (r, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_tmc) (a, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_tmc) (b, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_tmc) (consts, 64) /\
    nonoverlapping (r, 1024) (a, 1024) /\
    nonoverlapping (r, 1024) (b, 1024) /\
    nonoverlapping (r, 1024) (consts, 64) /\
    nonoverlapping (a, 1024) (b, 1024) /\
    nonoverlapping (a, 1024) (consts, 64) /\
    nonoverlapping (b, 1024) (consts, 64) /\
    nonoverlapping (stackpointer, 8) (r, 1024) /\
    nonoverlapping (stackpointer, 8) (a, 1024) /\
    nonoverlapping (stackpointer, 8) (b, 1024) /\
    nonoverlapping (stackpointer, 8) (consts, 64)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_pointwise_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [r; a; b; consts] s /\
              wordlist_from_memory(consts,16) s =
                MAP (iword: int -> 32 word) mldsa_pointwise_consts /\
              (!i. i < 256 ==> abs(ival(x i)) <= &75423752) /\
              (!i. i < 256 ==> abs(ival(y i)) <= &75423752) /\
              (!i. i < 256 ==>
                read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
              (!i. i < 256 ==>
                read(memory :> bytes32(word_add b (word(4 * i)))) s = y i))
          (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (!i. i < 256 ==>
                let zi = read(memory :> bytes32(word_add r (word(4 * i)))) s in
                (ival zi == mldsa_pointwise (ival o x) (ival o y) i)
                  (mod &8380417) /\
                abs(ival zi) <= &8380416))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(r, 1024)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_pointwise_tmc
    (CONV_RULE TWEAK_CONV MLDSA_POINTWISE_CORRECT));;

let MLDSA_POINTWISE_SUBROUTINE_CORRECT = prove
 (`!r a b consts x y pc stackpointer returnaddress.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 b /\
    aligned 32 consts /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_mc) (r, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_mc) (a, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_mc) (b, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_mc) (consts, 64) /\
    nonoverlapping (r, 1024) (a, 1024) /\
    nonoverlapping (r, 1024) (b, 1024) /\
    nonoverlapping (r, 1024) (consts, 64) /\
    nonoverlapping (a, 1024) (b, 1024) /\
    nonoverlapping (a, 1024) (consts, 64) /\
    nonoverlapping (b, 1024) (consts, 64) /\
    nonoverlapping (stackpointer, 8) (r, 1024) /\
    nonoverlapping (stackpointer, 8) (a, 1024) /\
    nonoverlapping (stackpointer, 8) (b, 1024) /\
    nonoverlapping (stackpointer, 8) (consts, 64)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_pointwise_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [r; a; b; consts] s /\
              wordlist_from_memory(consts,16) s =
                MAP (iword: int -> 32 word) mldsa_pointwise_consts /\
              (!i. i < 256 ==> abs(ival(x i)) <= &75423752) /\
              (!i. i < 256 ==> abs(ival(y i)) <= &75423752) /\
              (!i. i < 256 ==>
                read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
              (!i. i < 256 ==>
                read(memory :> bytes32(word_add b (word(4 * i)))) s = y i))
          (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (!i. i < 256 ==>
                let zi = read(memory :> bytes32(word_add r (word(4 * i)))) s in
                (ival zi == mldsa_pointwise (ival o x) (ival o y) i)
                  (mod &8380417) /\
                abs(ival zi) <= &8380416))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(r, 1024)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
    (CONV_RULE TWEAK_CONV MLDSA_POINTWISE_NOIBT_SUBROUTINE_CORRECT)));;

(* ========================================================================= *)
(* Windows ABI subroutine form                                               *)
(* ========================================================================= *)

let mldsa_pointwise_windows_mc = define_from_elf
   "mldsa_pointwise_windows_mc" "x86/mldsa/mldsa_pointwise.obj";;

let mldsa_pointwise_windows_tmc =
  define_trimmed "mldsa_pointwise_windows_tmc" mldsa_pointwise_windows_mc;;

let MLDSA_POINTWISE_WINDOWS_TMC_EXEC =
  X86_MK_EXEC_RULE mldsa_pointwise_windows_tmc;;

let MLDSA_POINTWISE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!r a b consts x y pc stackpointer returnaddress.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 b /\
    aligned 32 consts /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_windows_tmc) (r, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_windows_tmc) (a, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_windows_tmc) (b, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_windows_tmc) (consts, 64) /\
    nonoverlapping (r, 1024) (a, 1024) /\
    nonoverlapping (r, 1024) (b, 1024) /\
    nonoverlapping (r, 1024) (consts, 64) /\
    nonoverlapping (a, 1024) (b, 1024) /\
    nonoverlapping (a, 1024) (consts, 64) /\
    nonoverlapping (b, 1024) (consts, 64) /\
    nonoverlapping (word_sub stackpointer (word 192),200) (r, 1024) /\
    nonoverlapping (word_sub stackpointer (word 192),200) (a, 1024) /\
    nonoverlapping (word_sub stackpointer (word 192),200) (b, 1024) /\
    nonoverlapping (word_sub stackpointer (word 192),200) (consts, 64) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_windows_tmc)
                   (word_sub stackpointer (word 192),192)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_pointwise_windows_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [r; a; b; consts] s /\
              wordlist_from_memory(consts,16) s =
                MAP (iword: int -> 32 word) mldsa_pointwise_consts /\
              (!i. i < 256 ==> abs(ival(x i)) <= &75423752) /\
              (!i. i < 256 ==> abs(ival(y i)) <= &75423752) /\
              (!i. i < 256 ==>
                read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
              (!i. i < 256 ==>
                read(memory :> bytes32(word_add b (word(4 * i)))) s = y i))
          (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (!i. i < 256 ==>
                let zi = read(memory :> bytes32(word_add r (word(4 * i)))) s in
                (ival zi == mldsa_pointwise (ival o x) (ival o y) i)
                  (mod &8380417) /\
                abs(ival zi) <= &8380416))
          (MAYCHANGE [RSP] ,,
           WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 192),192)] ,,
           MAYCHANGE [memory :> bytes(r, 1024)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  REPLICATE_TAC 7 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 192 THEN REPEAT GEN_TAC THEN

  REWRITE_TAC[fst MLDSA_POINTWISE_WINDOWS_TMC_EXEC] THEN
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
  ENSURES_PRESERVED_TAC "init_xmm13" `ZMM13 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm14" `ZMM14 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm15" `ZMM15 :> bottomhalf :> bottomhalf` THEN

  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM
    [YMM6;YMM7;YMM8;YMM9;YMM10;YMM11;YMM12;YMM13;YMM14;YMM15]) THEN

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

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

  (* Execute Windows prologue: 18 instructions *)
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_POINTWISE_WINDOWS_TMC_EXEC (1--18) THEN

  (* Reuse the Unix proof for the core pointwise computation *)
  MP_TAC(SPECL
    [`r:int64`; `a:int64`; `b:int64`; `consts:int64`;
     `x:num->int32`; `y:num->int32`; `pc + 106`]
    (CONV_RULE(ONCE_DEPTH_CONV(REWRITE_CONV
       [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS]))
      (CONV_RULE TWEAK_CONV MLDSA_POINTWISE_CORRECT))) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

  (* Execute core computation as one big step *)
  X86_BIGSTEP_TAC MLDSA_POINTWISE_WINDOWS_TMC_EXEC "s19" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mldsa_pointwise_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mldsa_pointwise_tmc))
     106));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  (* Capture final YMM states before epilogue *)
  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s19`;
    `ymm7_epilog = read YMM7 s19`;
    `ymm8_epilog = read YMM8 s19`;
    `ymm9_epilog = read YMM9 s19`;
    `ymm10_epilog = read YMM10 s19`;
    `ymm11_epilog = read YMM11 s19`;
    `ymm12_epilog = read YMM12 s19`;
    `ymm13_epilog = read YMM13 s19`;
    `ymm14_epilog = read YMM14 s19`;
    `ymm15_epilog = read YMM15 s19`] THEN

  (* Execute Windows epilogue: 15 instructions including RET *)
  X86_STEPS_TAC MLDSA_POINTWISE_WINDOWS_TMC_EXEC (20--34) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLDSA_POINTWISE_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!r a b consts x y pc stackpointer returnaddress.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 b /\
    aligned 32 consts /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_windows_mc) (r, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_windows_mc) (a, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_windows_mc) (b, 1024) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_windows_mc) (consts, 64) /\
    nonoverlapping (r, 1024) (a, 1024) /\
    nonoverlapping (r, 1024) (b, 1024) /\
    nonoverlapping (r, 1024) (consts, 64) /\
    nonoverlapping (a, 1024) (b, 1024) /\
    nonoverlapping (a, 1024) (consts, 64) /\
    nonoverlapping (b, 1024) (consts, 64) /\
    nonoverlapping (word_sub stackpointer (word 192),200) (r, 1024) /\
    nonoverlapping (word_sub stackpointer (word 192),200) (a, 1024) /\
    nonoverlapping (word_sub stackpointer (word 192),200) (b, 1024) /\
    nonoverlapping (word_sub stackpointer (word 192),200) (consts, 64) /\
    nonoverlapping (word pc,LENGTH mldsa_pointwise_windows_mc)
                   (word_sub stackpointer (word 192),192)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_pointwise_windows_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [r; a; b; consts] s /\
              wordlist_from_memory(consts,16) s =
                MAP (iword: int -> 32 word) mldsa_pointwise_consts /\
              (!i. i < 256 ==> abs(ival(x i)) <= &75423752) /\
              (!i. i < 256 ==> abs(ival(y i)) <= &75423752) /\
              (!i. i < 256 ==>
                read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
              (!i. i < 256 ==>
                read(memory :> bytes32(word_add b (word(4 * i)))) s = y i))
          (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              (!i. i < 256 ==>
                let zi = read(memory :> bytes32(word_add r (word(4 * i)))) s in
                (ival zi == mldsa_pointwise (ival o x) (ival o y) i)
                  (mod &8380417) /\
                abs(ival zi) <= &8380416))
          (MAYCHANGE [RSP] ,,
           WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 192),192)] ,,
           MAYCHANGE [memory :> bytes(r, 1024)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
    (CONV_RULE TWEAK_CONV MLDSA_POINTWISE_NOIBT_WINDOWS_SUBROUTINE_CORRECT)));;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mldsa_pointwise_x86" subroutine_signatures)
    MLDSA_POINTWISE_CORRECT
    MLDSA_POINTWISE_TMC_EXEC;;

let MLDSA_POINTWISE_SAFE =
  REWRITE_RULE [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS]
  (time prove
   (full_spec,
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; SOME_FLAGS] THEN
    PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
      MLDSA_POINTWISE_TMC_EXEC));;

let MLDSA_POINTWISE_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a b consts pc stackpointer returnaddress.
          aligned 32 r /\ aligned 32 a /\ aligned 32 b /\ aligned 32 consts /\
          nonoverlapping (word pc, LENGTH mldsa_pointwise_tmc) (r, 1024) /\
          nonoverlapping (word pc, LENGTH mldsa_pointwise_tmc) (a, 1024) /\
          nonoverlapping (word pc, LENGTH mldsa_pointwise_tmc) (b, 1024) /\
          nonoverlapping (word pc, LENGTH mldsa_pointwise_tmc) (consts, 64) /\
          nonoverlapping (r, 1024) (a, 1024) /\ nonoverlapping (r, 1024) (b, 1024) /\
          nonoverlapping (r, 1024) (consts, 64) /\ nonoverlapping (a, 1024) (b, 1024) /\
          nonoverlapping (a, 1024) (consts, 64) /\ nonoverlapping (b, 1024) (consts, 64) /\
          nonoverlapping (stackpointer, 8) (r, 1024) /\
          nonoverlapping (stackpointer, 8) (a, 1024) /\
          nonoverlapping (stackpointer, 8) (b, 1024) /\
          nonoverlapping (stackpointer, 8) (consts, 64)
          ==> ensures x86
               (\s. bytes_loaded s (word pc) mldsa_pointwise_tmc /\
                    read RIP s = word pc /\ read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a; b; consts] s /\ read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2. read events s = APPEND e2 e /\
                         e2 = f_events r a b consts pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                           [a,1024; b,1024; consts,64; r,1024; stackpointer,8]
                           [r,1024; stackpointer,8]))
               (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_pointwise_tmc
    MLDSA_POINTWISE_SAFE THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_POINTWISE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a b consts pc stackpointer returnaddress.
          aligned 32 r /\ aligned 32 a /\ aligned 32 b /\ aligned 32 consts /\
          nonoverlapping (word pc, LENGTH mldsa_pointwise_mc) (r, 1024) /\
          nonoverlapping (word pc, LENGTH mldsa_pointwise_mc) (a, 1024) /\
          nonoverlapping (word pc, LENGTH mldsa_pointwise_mc) (b, 1024) /\
          nonoverlapping (word pc, LENGTH mldsa_pointwise_mc) (consts, 64) /\
          nonoverlapping (r, 1024) (a, 1024) /\ nonoverlapping (r, 1024) (b, 1024) /\
          nonoverlapping (r, 1024) (consts, 64) /\ nonoverlapping (a, 1024) (b, 1024) /\
          nonoverlapping (a, 1024) (consts, 64) /\ nonoverlapping (b, 1024) (consts, 64) /\
          nonoverlapping (stackpointer, 8) (r, 1024) /\
          nonoverlapping (stackpointer, 8) (a, 1024) /\
          nonoverlapping (stackpointer, 8) (b, 1024) /\
          nonoverlapping (stackpointer, 8) (consts, 64)
          ==> ensures x86
               (\s. bytes_loaded s (word pc) mldsa_pointwise_mc /\
                    read RIP s = word pc /\ read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a; b; consts] s /\ read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2. read events s = APPEND e2 e /\
                         e2 = f_events r a b consts pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                           [a,1024; b,1024; consts,64; r,1024; stackpointer,8]
                           [r,1024; stackpointer,8]))
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLDSA_POINTWISE_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POINTWISE_NOIBT_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events. forall e r a b consts pc stackpointer returnaddress.
        aligned 32 r /\ aligned 32 a /\ aligned 32 b /\ aligned 32 consts /\
        nonoverlapping (word pc, LENGTH mldsa_pointwise_windows_tmc) (r, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_pointwise_windows_tmc) (a, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_pointwise_windows_tmc) (b, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_pointwise_windows_tmc) (consts, 64) /\
        nonoverlapping (r, 1024) (a, 1024) /\ nonoverlapping (r, 1024) (b, 1024) /\
        nonoverlapping (r, 1024) (consts, 64) /\ nonoverlapping (a, 1024) (b, 1024) /\
        nonoverlapping (a, 1024) (consts, 64) /\ nonoverlapping (b, 1024) (consts, 64) /\
        nonoverlapping (word_sub stackpointer (word 192),200) (r, 1024) /\
        nonoverlapping (word_sub stackpointer (word 192),200) (a, 1024) /\
        nonoverlapping (word_sub stackpointer (word 192),200) (b, 1024) /\
        nonoverlapping (word_sub stackpointer (word 192),200) (consts, 64) /\
        nonoverlapping (word pc, LENGTH mldsa_pointwise_windows_tmc)
                       (word_sub stackpointer (word 192),192)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) mldsa_pointwise_windows_tmc /\
                  read RIP s = word pc /\ read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [r; a; b; consts] s /\ read events s = e)
              (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2. read events s = APPEND e2 e /\
                        e2 = f_events r a b consts pc
                               (word_sub stackpointer (word 192)) returnaddress /\
                        memaccess_inbounds e2
                          [a,1024; b,1024; consts,64;
                           r,1024; word_sub stackpointer (word 192),200]
                          [r,1024; word_sub stackpointer (word 192),200]))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 192), 192)] ,,
               MAYCHANGE [memory :> bytes(r, 1024)])`,

  ASSUME_CALLEE_SAFETY_TAC MLDSA_POINTWISE_SAFE "H_subth" THEN
  META_EXISTS_TAC THEN
  REPLICATE_TAC 6 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 192 THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[fst MLDSA_POINTWISE_WINDOWS_TMC_EXEC] THEN
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
  ENSURES_PRESERVED_TAC "init_xmm13" `ZMM13 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm14" `ZMM14 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm15" `ZMM15 :> bottomhalf :> bottomhalf` THEN

  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM
    [YMM6;YMM7;YMM8;YMM9;YMM10;YMM11;YMM12;YMM13;YMM14;YMM15]) THEN
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

  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_POINTWISE_WINDOWS_TMC_EXEC (1--18) THEN
  
  W(fun (asl,w) ->
    let current_events = List.filter_map (fun (_,ath) -> let t = concl ath in
      if is_eq t && is_read_events (lhs t) then Some (rhs t)
      else None) asl in
    if length current_events <> 1
    then failwith "More than 'read events .. = ..?'"
    else
      REMOVE_THEN "H_subth"
        (MP_TAC o SPECL [hd current_events; `r:int64`; `a:int64`; `b:int64`;
                         `consts:int64`; `pc + 106`]))
  THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
  X86_BIGSTEP_TAC MLDSA_POINTWISE_WINDOWS_TMC_EXEC "s19" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mldsa_pointwise_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mldsa_pointwise_tmc))
     106));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN
  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s19`; `ymm7_epilog = read YMM7 s19`;
    `ymm8_epilog = read YMM8 s19`; `ymm9_epilog = read YMM9 s19`;
    `ymm10_epilog = read YMM10 s19`; `ymm11_epilog = read YMM11 s19`;
    `ymm12_epilog = read YMM12 s19`; `ymm13_epilog = read YMM13 s19`;
    `ymm14_epilog = read YMM14 s19`; `ymm15_epilog = read YMM15 s19`] THEN
  X86_STEPS_TAC MLDSA_POINTWISE_WINDOWS_TMC_EXEC (20--34) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ DISCHARGE_SAFETY_PROPERTY_TAC; ALL_TAC ] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLDSA_POINTWISE_WINDOWS_SUBROUTINE_SAFE = prove
 (`exists f_events. forall e r a b consts pc stackpointer returnaddress.
        aligned 32 r /\ aligned 32 a /\ aligned 32 b /\ aligned 32 consts /\
        nonoverlapping (word pc, LENGTH mldsa_pointwise_windows_mc) (r, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_pointwise_windows_mc) (a, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_pointwise_windows_mc) (b, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_pointwise_windows_mc) (consts, 64) /\
        nonoverlapping (r, 1024) (a, 1024) /\ nonoverlapping (r, 1024) (b, 1024) /\
        nonoverlapping (r, 1024) (consts, 64) /\ nonoverlapping (a, 1024) (b, 1024) /\
        nonoverlapping (a, 1024) (consts, 64) /\ nonoverlapping (b, 1024) (consts, 64) /\
        nonoverlapping (word_sub stackpointer (word 192),200) (r, 1024) /\
        nonoverlapping (word_sub stackpointer (word 192),200) (a, 1024) /\
        nonoverlapping (word_sub stackpointer (word 192),200) (b, 1024) /\
        nonoverlapping (word_sub stackpointer (word 192),200) (consts, 64) /\
        nonoverlapping (word pc, LENGTH mldsa_pointwise_windows_mc)
                       (word_sub stackpointer (word 192),192)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) mldsa_pointwise_windows_mc /\
                  read RIP s = word pc /\ read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [r; a; b; consts] s /\ read events s = e)
              (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2. read events s = APPEND e2 e /\
                        e2 = f_events r a b consts pc
                               (word_sub stackpointer (word 192)) returnaddress /\
                        memaccess_inbounds e2
                          [a,1024; b,1024; consts,64;
                           r,1024; word_sub stackpointer (word 192),200]
                          [r,1024; word_sub stackpointer (word 192),200]))
              (MAYCHANGE [RSP] ,,
               WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(word_sub stackpointer (word 192), 192)] ,,
               MAYCHANGE [memory :> bytes(r, 1024)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
    MLDSA_POINTWISE_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
