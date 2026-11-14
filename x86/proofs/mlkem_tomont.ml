(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing nonnegative remainders.    *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* print_literal_from_elf "x86/mlkem/mlkem_tomont.o";; *)

let mlkem_tomont_mc =
  define_assert_from_elf "mlkem_tomont_mc" "x86/mlkem/mlkem_tomont.o"
  [
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xb8; 0x49; 0x50; 0x49; 0x50;
                           (* MOV (% eax) (Imm32 (word 1346981961)) *)
  0xc5; 0xf9; 0x6e; 0xc8;  (* VMOVD (%_% xmm1) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc9;
                           (* VPBROADCASTD (%_% ymm1) (%_% xmm1) *)
  0xb8; 0x49; 0x05; 0x49; 0x05;
                           (* MOV (% eax) (Imm32 (word 88671561)) *)
  0xc5; 0xf9; 0x6e; 0xd0;  (* VMOVD (%_% xmm2) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0xc5; 0xfd; 0x6f; 0x1f;  (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0x67; 0x20;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0x6f; 0x40;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0x77; 0x60;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0x65; 0xd5; 0xd9;  (* VPMULLW (%_% ymm11) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0xe5; 0xda;  (* VPMULHW (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc5; 0x5d; 0xd5; 0xe1;  (* VPMULLW (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xe5; 0xe2;  (* VPMULHW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe4;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x55; 0xd5; 0xe9;  (* VPMULLW (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xe5; 0xea;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x15; 0xe5; 0xe8;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xed;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0x4d; 0xd5; 0xf1;  (* VPMULLW (%_% ymm14) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xcd; 0xe5; 0xf2;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0x0d; 0xe5; 0xf0;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf6;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc5; 0x45; 0xd5; 0xf9;  (* VPMULLW (%_% ymm15) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0xc5; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x05; 0xe5; 0xf8;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xff;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm15) *)
  0xc5; 0x3d; 0xd5; 0xd9;  (* VPMULLW (%_% ymm11) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xe5; 0xc2;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc3;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm11) *)
  0xc5; 0x35; 0xd5; 0xe1;  (* VPMULLW (%_% ymm12) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xe5; 0xca;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xcc;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0x2d; 0xd5; 0xe9;  (* VPMULLW (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc5; 0x2d; 0xe5; 0xd2;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc5; 0x15; 0xe5; 0xe8;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xd5;
                           (* VPSUBW (%_% ymm10) (%_% ymm10) (%_% ymm13) *)
  0xc5; 0xfd; 0x7f; 0x1f;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm3) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x6f; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0x77; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm10) *)
  0xc5; 0xfd; 0x6f; 0x9f; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0x65; 0xd5; 0xd9;  (* VPMULLW (%_% ymm11) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0xe5; 0xda;  (* VPMULHW (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc4; 0xc1; 0x65; 0xf9; 0xdb;
                           (* VPSUBW (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc5; 0x5d; 0xd5; 0xe1;  (* VPMULLW (%_% ymm12) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0xe5; 0xe2;  (* VPMULHW (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0xc1; 0x5d; 0xf9; 0xe4;
                           (* VPSUBW (%_% ymm4) (%_% ymm4) (%_% ymm12) *)
  0xc5; 0x55; 0xd5; 0xe9;  (* VPMULLW (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0xe5; 0xea;  (* VPMULHW (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc5; 0x15; 0xe5; 0xe8;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0xc1; 0x55; 0xf9; 0xed;
                           (* VPSUBW (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0x4d; 0xd5; 0xf1;  (* VPMULLW (%_% ymm14) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0xcd; 0xe5; 0xf2;  (* VPMULHW (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc5; 0x0d; 0xe5; 0xf0;  (* VPMULHW (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0xc1; 0x4d; 0xf9; 0xf6;
                           (* VPSUBW (%_% ymm6) (%_% ymm6) (%_% ymm14) *)
  0xc5; 0x45; 0xd5; 0xf9;  (* VPMULLW (%_% ymm15) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0xc5; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc5; 0x05; 0xe5; 0xf8;  (* VPMULHW (%_% ymm15) (%_% ymm15) (%_% ymm0) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xff;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm15) *)
  0xc5; 0x3d; 0xd5; 0xd9;  (* VPMULLW (%_% ymm11) (%_% ymm8) (%_% ymm1) *)
  0xc5; 0x3d; 0xe5; 0xc2;  (* VPMULHW (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc5; 0x25; 0xe5; 0xd8;  (* VPMULHW (%_% ymm11) (%_% ymm11) (%_% ymm0) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc3;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm11) *)
  0xc5; 0x35; 0xd5; 0xe1;  (* VPMULLW (%_% ymm12) (%_% ymm9) (%_% ymm1) *)
  0xc5; 0x35; 0xe5; 0xca;  (* VPMULHW (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc5; 0x1d; 0xe5; 0xe0;  (* VPMULHW (%_% ymm12) (%_% ymm12) (%_% ymm0) *)
  0xc4; 0x41; 0x35; 0xf9; 0xcc;
                           (* VPSUBW (%_% ymm9) (%_% ymm9) (%_% ymm12) *)
  0xc5; 0x2d; 0xd5; 0xe9;  (* VPMULLW (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc5; 0x2d; 0xe5; 0xd2;  (* VPMULHW (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc5; 0x15; 0xe5; 0xe8;  (* VPMULHW (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x41; 0x2d; 0xf9; 0xd5;
                           (* VPSUBW (%_% ymm10) (%_% ymm10) (%_% ymm13) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm3) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm10) *)
  0xc3                     (* RET *)
];;

let mlkem_tomont_tmc = define_trimmed "mlkem_tomont_tmc" mlkem_tomont_mc;;
let mlkem_tomont_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_tomont_tmc;;

let MLKEM_TOMONT_CORRECT = prove(
  `!a x pc.
        aligned 32 a /\
        nonoverlapping (word pc, 544) (a, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mlkem_tomont_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = word (pc + 544) /\
                  !i. i < 256
                    ==> let z_i = read(memory :> bytes16
                                     (word_add a (word (2 * i)))) s in
                        (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                        abs(ival z_i) <= &3328)
             (MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,512)] ,,
              MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8;
                         ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15])`,
  REWRITE_TAC[fst mlkem_tomont_TMC_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS] THEN

  (* Split quantified assumptions into separate cases *)
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
    (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `init_ymm2:int256` `read YMM2` THEN

  ENSURES_INIT_TAC "s0" THEN

  (* Rewrite memory-read assumptions from 16-bit granularity
   * to 256-bit granularity. *)
  MEMORY_256_FROM_16_TAC "a" 16 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  STRIP_TAC THEN

  (* Symbolic execution *)
  MAP_EVERY (fun n -> X86_STEPS_TAC mlkem_tomont_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[ntt_montmul])
            (1--105) THEN
  
  ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN
  ASM_REWRITE_TAC[] THEN

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

  (* Split quantified post-condition into separate cases *)
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC [WORD_ADD_0] THEN

  (* Forget all assumptions *)
  POP_ASSUM_LIST (K ALL_TAC) THEN

  (* We have two goals per index: A congruence goal and a bounds goal.
     Split by index, but keep congruence & bounds goal together. *)
  REPEAT (W(fun (asl, w) ->
    if length(conjuncts w) > 3 then CONJ_TAC else NO_TAC)) THEN

  (* At this point, we have, for every polynomial coefficient, a subgoal
     with 2 conjuncts, one regarding functional correctness of the coefficient,
     another regarding its absolute value. *)

  (* Instantiate general congruence and bounds rule for Montgomery multiplication
   * so it matches the current goal, and add as new assumption. *)
  W (MP_TAC o CONGBOUND_RULE o rand o rand o rator o rator o lhand o snd) THEN
  ASM_REWRITE_TAC [o_THM; tomont_3329] THEN

  MATCH_MP_TAC MONO_AND THEN (CONJ_TAC THENL
  [
      (* Correctness *)
      REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 3329 65536`] THEN
      REWRITE_TAC [GSYM INT_REM_EQ] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN

      REWRITE_TAC[INT_REM_EQ] THEN
      REWRITE_TAC [REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC
    ;
      (* Bound *)
      REWRITE_TAC [INT_ABS_BOUNDS] THEN
      (* The bound we obtain from the generic theorem about Montgomery
       * multiplication is stronger than what we need -- weaken it. *)
      MATCH_MP_TAC(INT_ARITH
        `l':int <= l /\ u <= u'
         ==> l <= t /\ t <= u ==> l' <= t /\ t <= u'`) THEN
      CONV_TAC INT_REDUCE_CONV
  ])
);;

let MLKEM_TOMONT_NOIBT_SUBROUTINE_CORRECT = prove(
  `!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_tomont_tmc) (a, 512) /\
        nonoverlapping (stackpointer, 8) (a, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tomont_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                    ==> let z_i = read(memory :> bytes16
                                     (word_add a (word (2 * i)))) s in
                        (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                        abs(ival z_i) <= &3328)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`, 
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_tomont_tmc MLKEM_TOMONT_CORRECT);;

let MLKEM_TOMONT_SUBROUTINE_CORRECT = prove(
  `!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_tomont_mc) (a, 512) /\
        nonoverlapping (stackpointer, 8) (a, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tomont_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                    ==> let z_i = read(memory :> bytes16
                                     (word_add a (word (2 * i)))) s in
                        (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                        abs(ival z_i) <= &3328)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`, 
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_TOMONT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)
(* print_literal_from_elf "x86/mlkem/mlkem_tomont.obj";; *)

let mlkem_tomont_windows_mc = define_from_elf
    "mlkem_tomont_windows_mc" "x86/mlkem/mlkem_tomont.obj";;

let mlkem_tomont_windows_tmc = define_trimmed
    "mlkem_tomont_windows_tmc" mlkem_tomont_windows_mc;;

let mlkem_tomont_windows_tmc_EXEC = X86_MK_EXEC_RULE mlkem_tomont_windows_tmc;;

let MLKEM_TOMONT_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove(
  `!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_tomont_windows_tmc) (a, 512) /\
        nonoverlapping (word_sub stackpointer (word 176), 184) (a, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_tomont_windows_tmc)
                       (word_sub stackpointer (word 176), 176)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tomont_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                    ==> let z_i = read(memory :> bytes16
                                     (word_add a (word (2 * i)))) s in
                        (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                        abs(ival z_i) <= &3328)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176), 176)] ,,
              MAYCHANGE [memory :> bytes(a,512)])`, 
  REPLICATE_TAC 3 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 176 THEN
  REPEAT GEN_TAC THEN

  REWRITE_TAC[fst mlkem_tomont_windows_tmc_EXEC] THEN
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
  X86_STEPS_TAC mlkem_tomont_windows_tmc_EXEC (1--15) THEN

  MP_TAC(SPECL [`a:int64`; `x:num->int16`; `pc + 92`]
    MLKEM_TOMONT_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

  X86_BIGSTEP_TAC mlkem_tomont_windows_tmc_EXEC "s16" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mlkem_tomont_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mlkem_tomont_tmc))
     92));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s16`;
    `ymm7_epilog = read YMM7 s16`;
    `ymm8_epilog = read YMM8 s16`;
    `ymm9_epilog = read YMM9 s16`;
    `ymm10_epilog = read YMM10 s16`;
    `ymm11_epilog = read YMM11 s16`;
    `ymm12_epilog = read YMM12 s16`;
    `ymm13_epilog = read YMM13 s16`;
    `ymm14_epilog = read YMM14 s16`;
    `ymm15_epilog = read YMM15 s16`] THEN

  X86_STEPS_TAC mlkem_tomont_windows_tmc_EXEC (17--30) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLKEM_TOMONT_WINDOWS_SUBROUTINE_CORRECT = prove(
  `!a x pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_tomont_windows_mc) (a, 512) /\
        nonoverlapping (word_sub stackpointer (word 176), 184) (a, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_tomont_windows_mc)
                       (word_sub stackpointer (word 176), 176)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tomont_windows_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                    ==> let z_i = read(memory :> bytes16
                                     (word_add a (word (2 * i)))) s in
                        (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                        abs(ival z_i) <= &3328)
             (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 176), 176)] ,,
              MAYCHANGE [memory :> bytes(a,512)])`, 
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_TOMONT_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;
