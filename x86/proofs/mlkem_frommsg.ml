(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 32-byte message to a polynomial.                          *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "x86/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "x86/mlkem/mlkem_frommsg.o";;
 ****)

let mlkem_frommsg_mc = define_assert_from_elf
  "mlkem_frommsg_mc" "x86/mlkem/mlkem_frommsg.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x81; 0x06; 0x81; 0x06;
                           (* MOV (% eax) (Imm32 (word 109119105)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0x48; 0xb8; 0x00; 0x80; 0x00; 0x40; 0x00; 0x20; 0x00; 0x10;
                           (* MOV (% rax) (Imm64 (word 1152956690052710400)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xc8;
                           (* VMOVQ (%_% xmm1) (% rax) *)
  0x48; 0xb8; 0x00; 0x08; 0x00; 0x04; 0x00; 0x02; 0x00; 0x01;
                           (* MOV (% rax) (Imm64 (word 72059793128294400)) *)
  0xc4; 0xe3; 0xf1; 0x22; 0xc8; 0x01;
                           (* VPINSRQ (%_% xmm1) (%_% xmm1) (% rax) (Imm8 (word 1)) *)
  0x48; 0xb8; 0x80; 0x00; 0x40; 0x00; 0x20; 0x00; 0x10; 0x00;
                           (* MOV (% rax) (Imm64 (word 4503737070518400)) *)
  0xc4; 0xe1; 0xf9; 0x6e; 0xd0;
                           (* VMOVQ (%_% xmm2) (% rax) *)
  0x48; 0xb8; 0x08; 0x00; 0x04; 0x00; 0x02; 0x00; 0x01; 0x00;
                           (* MOV (% rax) (Imm64 (word 281483566907400)) *)
  0xc4; 0xe3; 0xe9; 0x22; 0xd0; 0x01;
                           (* VPINSRQ (%_% xmm2) (%_% xmm2) (% rax) (Imm8 (word 1)) *)
  0xc4; 0xe3; 0x75; 0x38; 0xca; 0x01;
                           (* VINSERTI128 (%_% ymm1) (%_% ymm1) (%_% xmm2) (Imm8 (word 1)) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x16;
                           (* VPBROADCASTW (%_% ymm2) (Memop Word (%% (rsi,0))) *)
  0xc5; 0xed; 0xd5; 0xd1;  (* VPMULLW (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xed; 0x71; 0xe2; 0x0f;
                           (* VPSRAW (%_% ymm2) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0xed; 0xdb; 0xd0;  (* VPAND (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x17;  (* VMOVDQU (Memop Word256 (%% (rdi,0))) (%_% ymm2) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x5e; 0x02;
                           (* VPBROADCASTW (%_% ymm3) (Memop Word (%% (rsi,2))) *)
  0xc5; 0xe5; 0xd5; 0xd9;  (* VPMULLW (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0x71; 0xe3; 0x0f;
                           (* VPSRAW (%_% ymm3) (%_% ymm3) (Imm8 (word 15)) *)
  0xc5; 0xe5; 0xdb; 0xd8;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x5f; 0x20;
                           (* VMOVDQU (Memop Word256 (%% (rdi,32))) (%_% ymm3) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x66; 0x04;
                           (* VPBROADCASTW (%_% ymm4) (Memop Word (%% (rsi,4))) *)
  0xc5; 0xdd; 0xd5; 0xe1;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xe4; 0x0f;
                           (* VPSRAW (%_% ymm4) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0xdd; 0xdb; 0xe0;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x67; 0x40;
                           (* VMOVDQU (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x6e; 0x06;
                           (* VPBROADCASTW (%_% ymm5) (Memop Word (%% (rsi,6))) *)
  0xc5; 0xd5; 0xd5; 0xe9;  (* VPMULLW (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0x71; 0xe5; 0x0f;
                           (* VPSRAW (%_% ymm5) (%_% ymm5) (Imm8 (word 15)) *)
  0xc5; 0xd5; 0xdb; 0xe8;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x6f; 0x60;
                           (* VMOVDQU (Memop Word256 (%% (rdi,96))) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x56; 0x08;
                           (* VPBROADCASTW (%_% ymm2) (Memop Word (%% (rsi,8))) *)
  0xc5; 0xed; 0xd5; 0xd1;  (* VPMULLW (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xed; 0x71; 0xe2; 0x0f;
                           (* VPSRAW (%_% ymm2) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0xed; 0xdb; 0xd0;  (* VPAND (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x97; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,128))) (%_% ymm2) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x5e; 0x0a;
                           (* VPBROADCASTW (%_% ymm3) (Memop Word (%% (rsi,10))) *)
  0xc5; 0xe5; 0xd5; 0xd9;  (* VPMULLW (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0x71; 0xe3; 0x0f;
                           (* VPSRAW (%_% ymm3) (%_% ymm3) (Imm8 (word 15)) *)
  0xc5; 0xe5; 0xdb; 0xd8;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x9f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,160))) (%_% ymm3) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x66; 0x0c;
                           (* VPBROADCASTW (%_% ymm4) (Memop Word (%% (rsi,12))) *)
  0xc5; 0xdd; 0xd5; 0xe1;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xe4; 0x0f;
                           (* VPSRAW (%_% ymm4) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0xdd; 0xdb; 0xe0;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,192))) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x6e; 0x0e;
                           (* VPBROADCASTW (%_% ymm5) (Memop Word (%% (rsi,14))) *)
  0xc5; 0xd5; 0xd5; 0xe9;  (* VPMULLW (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0x71; 0xe5; 0x0f;
                           (* VPSRAW (%_% ymm5) (%_% ymm5) (Imm8 (word 15)) *)
  0xc5; 0xd5; 0xdb; 0xe8;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xaf; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,224))) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x56; 0x10;
                           (* VPBROADCASTW (%_% ymm2) (Memop Word (%% (rsi,16))) *)
  0xc5; 0xed; 0xd5; 0xd1;  (* VPMULLW (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xed; 0x71; 0xe2; 0x0f;
                           (* VPSRAW (%_% ymm2) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0xed; 0xdb; 0xd0;  (* VPAND (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x97; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,256))) (%_% ymm2) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x5e; 0x12;
                           (* VPBROADCASTW (%_% ymm3) (Memop Word (%% (rsi,18))) *)
  0xc5; 0xe5; 0xd5; 0xd9;  (* VPMULLW (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0x71; 0xe3; 0x0f;
                           (* VPSRAW (%_% ymm3) (%_% ymm3) (Imm8 (word 15)) *)
  0xc5; 0xe5; 0xdb; 0xd8;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x9f; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,288))) (%_% ymm3) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x66; 0x14;
                           (* VPBROADCASTW (%_% ymm4) (Memop Word (%% (rsi,20))) *)
  0xc5; 0xdd; 0xd5; 0xe1;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xe4; 0x0f;
                           (* VPSRAW (%_% ymm4) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0xdd; 0xdb; 0xe0;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,320))) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x6e; 0x16;
                           (* VPBROADCASTW (%_% ymm5) (Memop Word (%% (rsi,22))) *)
  0xc5; 0xd5; 0xd5; 0xe9;  (* VPMULLW (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0x71; 0xe5; 0x0f;
                           (* VPSRAW (%_% ymm5) (%_% ymm5) (Imm8 (word 15)) *)
  0xc5; 0xd5; 0xdb; 0xe8;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xaf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,352))) (%_% ymm5) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x56; 0x18;
                           (* VPBROADCASTW (%_% ymm2) (Memop Word (%% (rsi,24))) *)
  0xc5; 0xed; 0xd5; 0xd1;  (* VPMULLW (%_% ymm2) (%_% ymm2) (%_% ymm1) *)
  0xc5; 0xed; 0x71; 0xe2; 0x0f;
                           (* VPSRAW (%_% ymm2) (%_% ymm2) (Imm8 (word 15)) *)
  0xc5; 0xed; 0xdb; 0xd0;  (* VPAND (%_% ymm2) (%_% ymm2) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x97; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,384))) (%_% ymm2) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x5e; 0x1a;
                           (* VPBROADCASTW (%_% ymm3) (Memop Word (%% (rsi,26))) *)
  0xc5; 0xe5; 0xd5; 0xd9;  (* VPMULLW (%_% ymm3) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0xe5; 0x71; 0xe3; 0x0f;
                           (* VPSRAW (%_% ymm3) (%_% ymm3) (Imm8 (word 15)) *)
  0xc5; 0xe5; 0xdb; 0xd8;  (* VPAND (%_% ymm3) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0x9f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,416))) (%_% ymm3) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x66; 0x1c;
                           (* VPBROADCASTW (%_% ymm4) (Memop Word (%% (rsi,28))) *)
  0xc5; 0xdd; 0xd5; 0xe1;  (* VPMULLW (%_% ymm4) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0xdd; 0x71; 0xe4; 0x0f;
                           (* VPSRAW (%_% ymm4) (%_% ymm4) (Imm8 (word 15)) *)
  0xc5; 0xdd; 0xdb; 0xe0;  (* VPAND (%_% ymm4) (%_% ymm4) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xa7; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,448))) (%_% ymm4) *)
  0xc4; 0xe2; 0x7d; 0x79; 0x6e; 0x1e;
                           (* VPBROADCASTW (%_% ymm5) (Memop Word (%% (rsi,30))) *)
  0xc5; 0xd5; 0xd5; 0xe9;  (* VPMULLW (%_% ymm5) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0xd5; 0x71; 0xe5; 0x0f;
                           (* VPSRAW (%_% ymm5) (%_% ymm5) (Imm8 (word 15)) *)
  0xc5; 0xd5; 0xdb; 0xe8;  (* VPAND (%_% ymm5) (%_% ymm5) (%_% ymm0) *)
  0xc5; 0xfe; 0x7f; 0xaf; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQU (Memop Word256 (%% (rdi,480))) (%_% ymm5) *)
  0xc5; 0xf8; 0x77;        (* VZEROUPPER *)
  0xc3                     (* RET *)
];;

let mlkem_frommsg_tmc = define_trimmed "mlkem_frommsg_tmc" mlkem_frommsg_mc;;

let MLKEM_FROMMSG_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_frommsg_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. Each coefficient is a bit of one of the sixteen 16-bit *)
(* words of the message as loaded, moved to the top by a multiplication,     *)
(* spread over the lane by an arithmetic shift and masked with 1665.         *)
(* ------------------------------------------------------------------------- *)

let FROMMSG_COND = prove
 (`!b. word((3329 * bitval b + 1) DIV 2):int16 =
       if b then word 1665 else word 0`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_FROMMSG_CORRECT = prove
 (`!r a n pc.
        ALL (nonoverlapping (r,512)) [(word pc,503); (a,32)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mlkem_frommsg_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,32)) s = n)
             (\s. read RIP s = word(pc + 503) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
             (MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                         ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14;
                         ZMM15] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              fst MLKEM_FROMMSG_TMC_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The sixteen 16-bit words of the message, as loaded ***)

  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `32`; `n:num`; mk_small_numeral(2 * k);
                    `s0:x86state`] READ_MEMORY_BYTES16_OF_NUM_EXP in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th) (0--15))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:256`,`:N`] WORD16_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:256)`; ARITH] THEN
  STRIP_TAC THEN

  (*** Simulate the whole thing ***)

  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_FROMMSG_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (1--93) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient is a bit of word n ***)

  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `i:num`]
    (INST_TYPE [`:256`,`:N`] NUM_BIT_AS_WORD_BIT)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_CONV `dimindex(:256)`] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[FROMMSG_COND] THEN
  UNDISCH_TAC `i < 256` THEN SPEC_TAC(`i:num`,`i:num`) THEN

  (*** Split the stored vectors into the coefficients ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
   check (can (term_match [] `read (memory :> bytes256 a) s = xxx`) o
          concl))) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s93" THEN
  SPEC_TAC(`word n:256 word`,`w:256 word`) THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the IBT landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_FROMMSG_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_frommsg_tmc); (a,32); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_frommsg_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,32)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_frommsg_tmc MLKEM_FROMMSG_CORRECT);;

let MLKEM_FROMMSG_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [(word pc,LENGTH mlkem_frommsg_mc); (a,32); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_frommsg_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,32)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_FROMMSG_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_frommsg" subroutine_signatures)
    MLKEM_FROMMSG_CORRECT
    MLKEM_FROMMSG_TMC_EXEC;;

let MLKEM_FROMMSG_SAFE = time prove
 (`exists f_events.
    forall e r a pc.
        ALL (nonoverlapping (r,512)) [word pc,503; a,32]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) (BUTLAST mlkem_frommsg_tmc) /\
                 read RIP s = word pc /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s.
                 read RIP s = word (pc + 503) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a r pc /\
                      memaccess_inbounds e2 [a,32; r,512] [r,512]))
            (MAYCHANGE [RIP] ,,
             MAYCHANGE [RAX] ,,
             MAYCHANGE
             [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9;
              ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
             MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_FROMMSG_TMC_EXEC);;

let MLKEM_FROMMSG_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e r a pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [word pc,LENGTH mlkem_frommsg_tmc; a,32; stackpointer,8]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mlkem_frommsg_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a r pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,32; r,512; stackpointer,8]
                      [r,512; stackpointer,8]))
            (\s s'. true)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_frommsg_tmc MLKEM_FROMMSG_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_FROMMSG_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e r a pc stackpointer returnaddress.
        ALL (nonoverlapping (r,512))
            [word pc,LENGTH mlkem_frommsg_mc; a,32; stackpointer,8]
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) mlkem_frommsg_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events a r pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,32; r,512; stackpointer,8]
                      [r,512; stackpointer,8]))
            (\s s'. true)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MLKEM_FROMMSG_NOIBT_SUBROUTINE_SAFE));;
