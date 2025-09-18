(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ------------------------------------------------------------------------- *)
(* Encoding the registers and flags as an 80-element list of numbers.        *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/base.ml";;

let regfile = new_definition
 `regfile s =
   [val(read RAX s); val(read RCX s); val(read RDX s); val(read RBX s);
    bitval(read CF s) +  4 * bitval(read PF s) + 16 * bitval(read AF s) +
    64 * bitval(read ZF s) + 128 * bitval(read SF s) +
    2048 * bitval(read OF s);
    val(read RBP s); val(read RSI s); val(read RDI s); val(read R8 s);
    val(read R9 s); val(read R10 s); val(read R11 s); val(read R12 s);
    val(read R13 s); val(read R14 s); val(read R15 s);
    val(word_subword (read YMM0 s) (0,64):int64);
    val(word_subword (read YMM0 s) (64,64):int64);
    val(word_subword (read YMM0 s) (128,64):int64);
    val(word_subword (read YMM0 s) (192,64):int64);
    val(word_subword (read YMM1 s) (0,64):int64);
    val(word_subword (read YMM1 s) (64,64):int64);
    val(word_subword (read YMM1 s) (128,64):int64);
    val(word_subword (read YMM1 s) (192,64):int64);
    val(word_subword (read YMM2 s) (0,64):int64);
    val(word_subword (read YMM2 s) (64,64):int64);
    val(word_subword (read YMM2 s) (128,64):int64);
    val(word_subword (read YMM2 s) (192,64):int64);
    val(word_subword (read YMM3 s) (0,64):int64);
    val(word_subword (read YMM3 s) (64,64):int64);
    val(word_subword (read YMM3 s) (128,64):int64);
    val(word_subword (read YMM3 s) (192,64):int64);
    val(word_subword (read YMM4 s) (0,64):int64);
    val(word_subword (read YMM4 s) (64,64):int64);
    val(word_subword (read YMM4 s) (128,64):int64);
    val(word_subword (read YMM4 s) (192,64):int64);
    val(word_subword (read YMM5 s) (0,64):int64);
    val(word_subword (read YMM5 s) (64,64):int64);
    val(word_subword (read YMM5 s) (128,64):int64);
    val(word_subword (read YMM5 s) (192,64):int64);
    val(word_subword (read YMM6 s) (0,64):int64);
    val(word_subword (read YMM6 s) (64,64):int64);
    val(word_subword (read YMM6 s) (128,64):int64);
    val(word_subword (read YMM6 s) (192,64):int64);
    val(word_subword (read YMM7 s) (0,64):int64);
    val(word_subword (read YMM7 s) (64,64):int64);
    val(word_subword (read YMM7 s) (128,64):int64);
    val(word_subword (read YMM7 s) (192,64):int64);
    val(word_subword (read YMM8 s) (0,64):int64);
    val(word_subword (read YMM8 s) (64,64):int64);
    val(word_subword (read YMM8 s) (128,64):int64);
    val(word_subword (read YMM8 s) (192,64):int64);
    val(word_subword (read YMM9 s) (0,64):int64);
    val(word_subword (read YMM9 s) (64,64):int64);
    val(word_subword (read YMM9 s) (128,64):int64);
    val(word_subword (read YMM9 s) (192,64):int64);
    val(word_subword (read YMM10 s) (0,64):int64);
    val(word_subword (read YMM10 s) (64,64):int64);
    val(word_subword (read YMM10 s) (128,64):int64);
    val(word_subword (read YMM10 s) (192,64):int64);
    val(word_subword (read YMM11 s) (0,64):int64);
    val(word_subword (read YMM11 s) (64,64):int64);
    val(word_subword (read YMM11 s) (128,64):int64);
    val(word_subword (read YMM11 s) (192,64):int64);
    val(word_subword (read YMM12 s) (0,64):int64);
    val(word_subword (read YMM12 s) (64,64):int64);
    val(word_subword (read YMM12 s) (128,64):int64);
    val(word_subword (read YMM12 s) (192,64):int64);
    val(word_subword (read YMM13 s) (0,64):int64);
    val(word_subword (read YMM13 s) (64,64):int64);
    val(word_subword (read YMM13 s) (128,64):int64);
    val(word_subword (read YMM13 s) (192,64):int64);
    val(word_subword (read YMM14 s) (0,64):int64);
    val(word_subword (read YMM14 s) (64,64):int64);
    val(word_subword (read YMM14 s) (128,64):int64);
    val(word_subword (read YMM14 s) (192,64):int64);
    val(word_subword (read YMM15 s) (0,64):int64);
    val(word_subword (read YMM15 s) (64,64):int64);
    val(word_subword (read YMM15 s) (128,64):int64);
    val(word_subword (read YMM15 s) (192,64):int64);
    val(word_subword (read (memory :> bytes256(read RSP s)) s) (0,64):int64);
    val(word_subword (read (memory :> bytes256(read RSP s)) s) (64,64):int64);
    val(word_subword (read (memory :> bytes256(read RSP s)) s) (128,64):int64);
    val(word_subword (read (memory :> bytes256(read RSP s)) s) (192,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 32))) s) (0,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 32))) s) (64,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 32))) s) (128,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 32))) s) (192,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 64))) s) (0,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 64))) s) (64,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 64))) s) (128,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 64))) s) (192,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 96))) s) (0,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 96))) s) (64,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 96))) s) (128,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 96))) s) (192,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 128))) s) (0,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 128))) s) (64,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 128))) s) (128,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 128))) s) (192,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 160))) s) (0,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 160))) s) (64,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 160))) s) (128,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 160))) s) (192,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 192))) s) (0,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 192))) s) (64,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 192))) s) (128,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 192))) s) (192,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 224))) s) (0,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 224))) s) (64,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 224))) s) (128,64):int64);
    val(word_subword (read (memory :> bytes256(word_add (read RSP s) (word 224))) s) (192,64):int64)
    ]`;;

let FLAGENCODING_11 = prove
 (`bitval b0 + 4 * bitval b1 + 16 * bitval b2 +
   64 * bitval b3 + 128 * bitval b4 + 2048 * bitval b5 = n <=>
   n < 4096 /\
   (b0 <=> ODD n) /\
   ~ODD(n DIV 2) /\
   (b1 <=> ODD(n DIV 4)) /\
   ~ODD(n DIV 8) /\
   (b2 <=> ODD(n DIV 16)) /\
   ~ODD(n DIV 32) /\
   (b3 <=> ODD(n DIV 64)) /\
   (b4 <=> ODD(n DIV 128)) /\
   ~ODD(n DIV 256) /\
   ~ODD(n DIV 512) /\
   ~ODD(n DIV 1024) /\
   (b5 <=> ODD(n DIV 2048))`,
  REWRITE_TAC[bitval] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  (EQ_TAC THENL [DISCH_THEN(SUBST1_TAC o SYM) THEN ARITH_TAC; ALL_TAC]) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP MOD_LT) THEN
  REWRITE_TAC[ARITH_RULE
   `4096 = 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2`] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN REWRITE_TAC[DIV_DIV] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[MOD_2_CASES; GSYM NOT_ODD] THEN ARITH_TAC);;

let YMMENCODING_REGROUP = prove
 (`(!(y:256 word) (y0:int64) (y1:int64) (y2:int64) (y3:int64).
    word_subword y (0,64) = y0 /\
    word_subword y (64,64) = y1 /\
    word_subword y (128,64) = y2 /\
    word_subword y (192,64) = y3 <=>
    y = word_join (word_join y3 y2:128 word) (word_join y1 y0:128 word)) /\
   (!(y:256 word) (y0:int64) (y1:int64) (y2:int64) (y3:int64) P.
    word_subword y (0,64) = y0 /\
    word_subword y (64,64) = y1 /\
    word_subword y (128,64) = y2 /\
    word_subword y (192,64) = y3 /\
    P <=>
    y = word_join (word_join y3 y2:128 word) (word_join y1 y0:128 word) /\ P)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_256] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
  REWRITE_TAC[CONJ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Random numbers with random bit density, random state for simulating.      *)
(* ------------------------------------------------------------------------- *)

let random_boold d = Random.int 64 < d;;

let randomnd n density =
    funpow n (fun n ->
      (if random_boold density then num_1 else num_0) +/ num_2 */ n) num_0;;

let random64() = randomnd 64 (Random.int 65);;

let random_regstate () =
  let d = Random.int 65 in
  map (fun _ -> randomnd 64 d) (0--3) @
  [num(Random.int 256 land 0b11010101)] @
  map (fun _ -> randomnd 64 d) (5--79) @
  map (fun _ -> randomnd 64 d) (80--111);;

(* ------------------------------------------------------------------------- *)
(* Generate random instance of instruction class itself.                     *)
(* ------------------------------------------------------------------------- *)

let random_instruction iclasses =
  el (Random.int (length iclasses)) iclasses;;

(* ------------------------------------------------------------------------- *)
(* The iclasses to simulate.                                                 *)
(* x86-insns.ml is generated by 'make x86-insns.ml'.                         *)
(* ------------------------------------------------------------------------- *)

loadt "x86/x86-insns.ml";;

let iclasses = iclasses @

(*** The elements here were added manually for additional checks. ***)

[[0x48; 0x0f; 0xb7; 0xc2];  (* MOVZX (% rax) (% dx) *)
 [0x0f; 0xb7; 0xc2];        (* MOVZX (% eax) (% dx) *)
 [0x48; 0x0f; 0xb6; 0xc2];  (* MOVZX (% rax) (% dl) *)
 [0x0f; 0xb6; 0xc2];        (* MOVZX (% eax) (% dl) *)
 [0x0f; 0xb6; 0xc6];        (* MOVZX (% eax) (% dh) *)
 [0x48; 0x0f; 0xbf; 0xc2];  (* MOVSX (% rax) (% dx) *)
 [0x0f; 0xbf; 0xc2];        (* MOVSX (% eax) (% dx) *)
 [0x48; 0x0f; 0xbe; 0xc2];  (* MOVSX (% rax) (% dl) *)
 [0x0f; 0xbe; 0xc2];        (* MOVSX (% eax) (% dl) *)
 [0x0f; 0xbe; 0xc6];        (* MOVSX (% eax) (% dh) *)
 [0x48; 0x63; 0xc2];        (* MOVSX (% rax) (% edx) *)
 [0x63; 0xc2];              (* MOVSX (% eax) (% edx) *)
 [0x48; 0x0f; 0xb7; 0xc9];  (* MOVZX (% rcx) (% cx) *)
 [0x0f; 0xb7; 0xc9];        (* MOVZX (% ecx) (% cx) *)
 [0x48; 0x0f; 0xb6; 0xc9];  (* MOVZX (% rcx) (% cl) *)
 [0x0f; 0xb6; 0xc9];        (* MOVZX (% ecx) (% cl) *)
 [0x0f; 0xb6; 0xcd];        (* MOVZX (% ecx) (% ch) *)
 [0x48; 0x0f; 0xbf; 0xc9];  (* MOVSX (% rcx) (% cx) *)
 [0x0f; 0xbf; 0xc9];        (* MOVSX (% ecx) (% cx) *)
 [0x48; 0x0f; 0xbe; 0xc9];  (* MOVSX (% rcx) (% cl) *)
 [0x0f; 0xbe; 0xc9];        (* MOVSX (% ecx) (% cl) *)
 [0x0f; 0xbe; 0xcd];        (* MOVSX (% ecx) (% ch) *)
 [0x48; 0x63; 0xc9];        (* MOVSX (% rcx) (% ecx) *)
 [0x63; 0xc9];              (* MOVSX (% ecx) (% ecx) *)
 [0x48; 0x0f; 0xb7; 0xf7];  (* MOVZX (% rsi) (% di) *)
 [0x0f; 0xb7; 0xf7];        (* MOVZX (% esi) (% di) *)
 [0x48; 0x0f; 0xb6; 0xf7];  (* MOVZX (% rsi) (% dil) *)
 [0x40; 0x0f; 0xb6; 0xf7];  (* MOVZX (% esi) (% dil) *)
 [0x0f; 0xb6; 0xf6];        (* MOVZX (% esi) (% dh) *)
 [0x48; 0x0f; 0xbf; 0xf7];  (* MOVSX (% rsi) (% di) *)
 [0x0f; 0xbf; 0xf7];        (* MOVSX (% esi) (% di) *)
 [0x48; 0x0f; 0xbe; 0xf7];  (* MOVSX (% rsi) (% dil) *)
 [0x40; 0x0f; 0xbe; 0xf7];  (* MOVSX (% esi) (% dil) *)
 [0x0f; 0xbe; 0xf7];        (* MOVSX (% esi) (% bh) *)
 [0x48; 0x63; 0xf7];        (* MOVSX (% rsi) (% edi) *)
 [0x63; 0xf7];              (* MOVSX (% esi) (% edi) *)
 [0x4c; 0x0f; 0xb7; 0xfa];  (* MOVZX (% r15) (% dx) *)
 [0x44; 0x0f; 0xb7; 0xfa];  (* MOVZX (% r15d) (% dx) *)
 [0x4c; 0x0f; 0xb6; 0xfa];  (* MOVZX (% r15) (% dl) *)
 [0x44; 0x0f; 0xb6; 0xfa];  (* MOVZX (% r15d) (% dl) *)
 [0x4c; 0x0f; 0xbf; 0xfa];  (* MOVSX (% r15) (% dx) *)
 [0x44; 0x0f; 0xbf; 0xfa];  (* MOVSX (% r15d) (% dx) *)
 [0x4c; 0x0f; 0xbe; 0xfa];  (* MOVSX (% r15) (% dl) *)
 [0x44; 0x0f; 0xbe; 0xfa];  (* MOVSX (% r15d) (% dl) *)
 [0x4c; 0x63; 0xfa];        (* MOVSX (% r15) (% edx) *)
 [0x44; 0x63; 0xfa];        (* MOVSX (% r15d) (% edx) *)
 [0x66; 0x0f; 0x6e; 0xc0]; (* MOVD xmm0, eax *)
 [0x66; 0x0f; 0x6e; 0xc8]; (* MOVD xmm1, eax *)
 [0x66; 0x0f; 0x6e; 0xd1]; (* MOVD xmm2, ecx *)
 [0x66; 0x0f; 0x6e; 0xda]; (* MOVD xmm3, edx *)
 [0x66; 0x0f; 0x6e; 0xe3]; (* MOVD xmm4, ebx *)
 [0x66; 0x0f; 0x6e; 0xee]; (* MOVD xmm5, esi *)
 [0x66; 0x0f; 0x6e; 0xf7]; (* MOVD xmm6, edi *)
 [0x66; 0x44; 0x0f; 0x6e; 0xc0]; (* MOVD xmm8, eax *)
 [0x66; 0x44; 0x0f; 0x6e; 0xc8]; (* MOVD xmm9, eax *)
 [0x66; 0x44; 0x0f; 0x6e; 0xd1]; (* MOVD xmm10, ecx *)
 [0x66; 0x44; 0x0f; 0x6e; 0xda]; (* MOVD xmm11, edx *)
 [0x66; 0x44; 0x0f; 0x6e; 0xe3]; (* MOVD xmm12, ebx *)
 [0x66; 0x44; 0x0f; 0x6e; 0xee]; (* MOVD xmm13, esi *)
 [0x66; 0x44; 0x0f; 0x6e; 0xf7]; (* MOVD xmm14, edi *)
 [0x66; 0x45; 0x0f; 0x6e; 0xf8]; (* MOVD xmm15, r8d *)
 [0x66; 0x0f; 0x7e; 0xc0]; (* MOVD eax, xmm0 *)
 [0x66; 0x0f; 0x7e; 0xc8]; (* MOVD eax, xmm1 *)
 [0x66; 0x0f; 0x7e; 0xd1]; (* MOVD ecx, xmm2 *)
 [0x66; 0x0f; 0x7e; 0xda]; (* MOVD edx, xmm3 *)
 [0x66; 0x0f; 0x7e; 0xe3]; (* MOVD ebx, xmm4 *)
 [0x66; 0x0f; 0x7e; 0xee]; (* MOVD esi, xmm5 *)
 [0x66; 0x0f; 0x7e; 0xf7]; (* MOVD edi, xmm6 *)
 [0x66; 0x44; 0x0f; 0x7e; 0xc0]; (* MOVD eax, xmm8 *)
 [0x66; 0x44; 0x0f; 0x7e; 0xc8]; (* MOVD eax, xmm9 *)
 [0x66; 0x44; 0x0f; 0x7e; 0xd1]; (* MOVD ecx, xmm10 *)
 [0x66; 0x44; 0x0f; 0x7e; 0xda]; (* MOVD edx, xmm11 *)
 [0x66; 0x44; 0x0f; 0x7e; 0xe3]; (* MOVD ebx, xmm12 *)
 [0x66; 0x44; 0x0f; 0x7e; 0xee]; (* MOVD esi, xmm13 *)
 [0x66; 0x44; 0x0f; 0x7e; 0xf7]; (* MOVD edi, xmm14 *)
 [0x66; 0x45; 0x0f; 0x7e; 0xf8]; (* MOVD r8d, xmm15 *)
 [0xc5; 0xe9; 0xeb; 0xcb];       (* VPOR (%_% xmm1) (%_% xmm2) (%_% xmm3) *)
 [0xc5; 0xd5; 0xeb; 0xe6];       (* VPOR (%_% ymm4) (%_% ymm5) (%_% ymm6) *)
 [0xc4; 0xc1; 0x39; 0xeb; 0xf9]; (* VPOR (%_% xmm7) (%_% xmm8) (%_% xmm9) *)
 [0xc4; 0x41; 0x25; 0xeb; 0xd4]; (* VPOR (%_% ymm10) (%_% ymm11) (%_% ymm12) *)
 [0xc4; 0x41; 0x09; 0xeb; 0xef]; (* VPOR (%_% xmm13) (%_% xmm14) (%_% xmm15) *)
 [0xc4; 0xc1; 0x3d; 0xeb; 0xc7]; (* VPOR (%_% ymm0) (%_% ymm8) (%_% ymm15) *)
 [0xc5; 0xd9; 0xeb; 0xe4];       (* VPOR (%_% xmm4) (%_% xmm4) (%_% xmm4) *)
 [0xc5; 0xcd; 0xeb; 0xf6];       (* VPOR (%_% ymm6) (%_% ymm6) (%_% ymm6) *)
 [0xc5; 0xe9; 0xef; 0xcb];       (* VPXOR (%_% xmm1) (%_% xmm2) (%_% xmm3) *)
 [0xc5; 0xed; 0xef; 0xcb];       (* VPXOR (%_% ymm1) (%_% ymm2) (%_% ymm3) *)
 [0xc4; 0x41; 0x31; 0xef; 0xd0]; (* VPXOR (%_% xmm10) (%_% xmm9) (%_% xmm8) *)
 [0xc4; 0x41; 0x35; 0xef; 0xd0]; (* VPXOR (%_% ymm10) (%_% ymm9) (%_% ymm8) *)
 [0xc4; 0x41; 0x09; 0xef; 0xef]; (* VPXOR (%_% xmm13) (%_% xmm14) (%_% xmm15) *)
 [0xc4; 0x41; 0x0d; 0xef; 0xef]; (* VPXOR (%_% ymm13) (%_% ymm14) (%_% ymm15) *)
 [0x48; 0x87; 0xfe]; (* XCHG (% rsi) (%rdi) *)
 [0x87; 0xfe]; (* XCHG (% esi) (%edi) *)
 [0x66; 0x87; 0xfe]; (* XCHG (% si) (%di) *)
 [0x66; 0x87; 0xfe]; (* XCHG (% si) (%di) *)
 [0x40; 0x86; 0xfe]; (* XCHG (% sil) (%dil) *)
 (* TODO: remove these tests once the AES-XTS program is integrated *)
 [0x66; 0x0f; 0x38; 0xdc; 0xc1]; (*AESENC (%_% xmm0) (%_% xmm1) *)
 [0x66; 0x0f; 0x38; 0xdc; 0xda]; (*AESENC (%_% xmm3) (%_% xmm2) *)
 [0x66; 0x0f; 0x38; 0xdc; 0xdb]; (*AESENC (%_% xmm3) (%_% xmm3) *)
 [0x66; 0x0f; 0x38; 0xdd; 0xe5]; (*AESENCLAST (%_% xmm4) (%_% xmm5) *)
 [0x66; 0x0f; 0x38; 0xdd; 0xfe]; (*AESENCLAST (%_% xmm7) (%_% xmm6) *)
 [0x66; 0x0f; 0x38; 0xdd; 0xff]; (*AESENCLAST (%_% xmm7) (%_% xmm7) *)
 [0x66; 0x45; 0x0f; 0x38; 0xde; 0xc1]; (*AESDEC (%_% xmm8) (%_% xmm9) *)
 [0x66; 0x45; 0x0f; 0x38; 0xde; 0xda]; (*AESDEC (%_% xmm11) (%_% xmm10) *)
 [0x66; 0x41; 0x0f; 0x38; 0xde; 0xfb]; (*AESDEC (%_% xmm7) (%_% xmm11) *)
 [0x66; 0x45; 0x0f; 0x38; 0xdf; 0xe5]; (*AESDECLAST (%_% xmm12) (%_% xmm13) *)
 [0x66; 0x45; 0x0f; 0x38; 0xdf; 0xfe]; (*AESDECLAST (%_% xmm15) (%_% xmm14) *)
 [0x66; 0x44; 0x0f; 0x38; 0xdf; 0xff]; (*AESDECLAST (%_% xmm15) (%_% xmm7) *)
 [0x66; 0x0f; 0x3a; 0xdf; 0xc8; 0x01]; (*AESKEYGENASSIST (%_% xmm1) (%_% xmm0) (Imm8 (word 1)) *)
 [0x66; 0x0f; 0x3a; 0xdf; 0xf8; 0xff]; (*AESKEYGENASSIST (%_% xmm15) (%_% xmm0) (Imm8 (word 255)) *)
 [0x66; 0x0f; 0x3a; 0xdf; 0xdc; 0x19]; (*AESKEYGENASSIST (%_% xmm3) (%_% xmm12) (Imm8 (word 25)) *)
 [0x66; 0x0f; 0x70; 0xc9; 0x55]; (*PSHUFD (%_% xmm1) (%_% xmm1) (Imm8 (word 85)) *)
 [0x66; 0x44; 0x0f; 0x70; 0xca; 0x5f]; (*PSHUFD (%_% xmm9) (%_% xmm2) (Imm8 (word 95)) *)
 [0x66; 0x0f; 0xef; 0xd3]; (*PXOR (%_% xmm2) (%_% xmm3) *)
 [0x66; 0x41; 0x0f; 0xef; 0xff]; (*PXOR (%_% xmm7) (%_% xmm15) *)
 [0x66; 0x0f; 0xdb; 0xd3]; (*PAND (%_% xmm2) (%_% xmm3) *)
 [0x66; 0x41; 0x0f; 0xdb; 0xff]; (*PAND (%_% xmm7) (%_% xmm15) *)
 [0x66; 0x0f; 0xfe; 0xd3]; (*PADDD (%_% xmm2) (%_% xmm3) *)
 [0x66; 0x41; 0x0f; 0xfe; 0xff]; (*PADDD (%_% xmm7) (%_% xmm15) *)
 [0x66; 0x0f; 0xd4; 0xd3]; (*PADDQ (%_% xmm2) (%_% xmm3) *)
 [0x66; 0x41; 0x0f; 0xd4; 0xff]; (*PADDQ (%_% xmm7) (%_% xmm15) *)
 [0x66; 0x0f; 0x72; 0xe1; 0x1f]; (*PSRAD (%_% xmm1) (Imm8 (word 31)) *)
 [0x66; 0x41; 0x0f; 0x72; 0xe4; 0x38]; (*PSRAD (%_% xmm12) (Imm8 (word 56)) *)
 [0x66; 0x45; 0x0f; 0x66; 0xfe]; (*PCMPGTD (%_% xmm15) (%_% xmm14) *)
 [0x66; 0x0f; 0x66; 0xcb]; (*PCMPGTD (%_% xmm1) (%_% xmm3) *)
 [0x66; 0x90]; (* NOP *)
 [0x0f; 0x1f; 0x4f; 0x00]; (* NOP_N (Memop Doubleword (%% (rdi,0))) *)
 [0x66; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00]; (* NOP_N (Memop Word (%%%% (rax,0,rax))) *)
 [0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00]; (* NOP_N (Memop Word (%%%% (rax,0,rax))) *)
 [0x66; 0x66; 0x2e; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00]; (* NOP_N (Memop Word (%%%% (rax,0,rax))) *)
 [0xc5; 0xf9; 0x6f; 0xca]; (* VMOVDQA xmm1, xmm2 *)
 [0xc5; 0xf9; 0x6f; 0xd3]; (* VMOVDQA xmm2, xmm3 *)
 [0xc5; 0xf9; 0x6f; 0xdc]; (* VMOVDQA xmm3, xmm4 *)
 [0xc5; 0xf9; 0x7f; 0xd1]; (* VMOVDQA xmm1, xmm2 *)
 [0xc5; 0xf9; 0x7f; 0xda]; (* VMOVDQA xmm2, xmm3 *)
 [0xc5; 0xfd; 0x6f; 0xca]; (* VMOVDQA ymm1, ymm2 *)
 [0xc5; 0xfd; 0x6f; 0xd3]; (* VMOVDQA ymm2, ymm3 *)
 [0xc5; 0xfd; 0x6f; 0xdc]; (* VMOVDQA ymm3, ymm4 *)
 [0xc5; 0xfd; 0x7f; 0xd1]; (* VMOVDQA ymm1, ymm2 *)
 [0xc5; 0xfd; 0x7f; 0xda]; (* VMOVDQA ymm2, ymm3 *)
 [0xc5; 0xfa; 0x6f; 0xca];       (* VMOVDQU (%_% xmm1) (%_% xmm2)   *)
 [0xc4; 0x41; 0x7e; 0x6f; 0xfe]; (* VMOVDQU (%_% ymm15) (%_% ymm14) *)
 [0xc5; 0xfa; 0x6f; 0xff];       (* VMOVDQU (%_% xmm7) (%_% xmm7)   *)
 [0xc4; 0x41; 0x7e; 0x6f; 0xc0]; (* VMOVDQU (%_% ymm8) (%_% ymm8)   *)
 [0xc5; 0x7a; 0x7f; 0xe8];       (* VMOVDQU (%_% xmm0) (%_% xmm13)  *)
 [0xc5; 0x7e; 0x7f; 0xff];       (* VMOVDQU (%_% ymm7) (%_% ymm15)  *)
 [0xc4; 0x41; 0x79; 0x6f; 0xc1]; (* VMOVDQA xmm8, xmm9 *)
 [0xc4; 0x41; 0x7d; 0x6f; 0xca]; (* VMOVDQA ymm8, ymm10 *)
 [0xc5; 0xfe; 0x12; 0xc1]; (* VMOVSLDUP ymm0, ymm1 *)
 [0xc5; 0xfe; 0x12; 0xca]; (* VMOVSLDUP ymm1, ymm2 *)
 [0xc5; 0xfe; 0x12; 0xd3]; (* VMOVSLDUP ymm2, ymm3 *)
 [0xc5; 0xfe; 0x12; 0xdc]; (* VMOVSLDUP ymm3, ymm4 *)
 [0xc4; 0x41; 0x7e; 0x12; 0xc1]; (* VMOVSLDUP ymm8, ymm9 *)
 [0xc4; 0x41; 0x7e; 0x12; 0xd3]; (* VMOVSLDUP ymm10, ymm11 *)
 [0xc4; 0x41; 0x7e; 0x12; 0xe5]; (* VMOVSLDUP ymm12, ymm13 *)
 [0xc4; 0x41; 0x7e; 0x12; 0xf7]; (* VMOVSLDUP ymm14, ymm15 *)
 [0xc5; 0xfa; 0x12; 0xc1]; (* VMOVSLDUP xmm0, xmm1 *)
 [0xc5; 0xfa; 0x12; 0xca]; (* VMOVSLDUP xmm1, xmm2 *)
 [0xc5; 0xfa; 0x12; 0xd3]; (* VMOVSLDUP xmm2, xmm3 *)
 [0xc5; 0xfa; 0x12; 0xdc]; (* VMOVSLDUP xmm3, xmm4 *)
 [0xc4; 0x41; 0x7a; 0x12; 0xc1]; (* VMOVSLDUP xmm8, xmm9 *)
 [0xc4; 0x41; 0x7a; 0x12; 0xd3]; (* VMOVSLDUP xmm10, xmm11 *)
 [0xc4; 0x41; 0x7a; 0x12; 0xe5]; (* VMOVSLDUP xmm12, xmm13 *)
 [0xc4; 0x41; 0x7a; 0x12; 0xf7]; (* VMOVSLDUP xmm14, xmm15 *)
 [0xc5; 0xfe; 0x16; 0xc1]; (* VMOVSHDUP ymm0, ymm1 *)
 [0xc5; 0xfe; 0x16; 0xca]; (* VMOVSHDUP ymm1, ymm2 *)
 [0xc5; 0xfe; 0x16; 0xd3]; (* VMOVSHDUP ymm2, ymm3 *)
 [0xc5; 0xfe; 0x16; 0xdc]; (* VMOVSHDUP ymm3, ymm4 *)
 [0xc4; 0x41; 0x7e; 0x16; 0xc1]; (* VMOVSHDUP ymm8, ymm9 *)
 [0xc4; 0x41; 0x7e; 0x16; 0xd3]; (* VMOVSHDUP ymm10, ymm11 *)
 [0xc4; 0x41; 0x7e; 0x16; 0xe5]; (* VMOVSHDUP ymm12, ymm13 *)
 [0xc4; 0x41; 0x7e; 0x16; 0xf7]; (* VMOVSHDUP ymm14, ymm15 *)
 [0xc5; 0xfd; 0xfe; 0xc1]; (* VPADDD ymm0, ymm0, ymm1 *)
 [0xc5; 0xf5; 0xfe; 0xca]; (* VPADDD ymm1, ymm1, ymm2 *)
 [0xc5; 0xed; 0xfe; 0xd3]; (* VPADDD ymm2, ymm2, ymm3 *)
 [0xc5; 0xe5; 0xfe; 0xdc]; (* VPADDD ymm3, ymm3, ymm4 *)
 [0xc5; 0xe9; 0xfe; 0xcb]; (* VPADDD (%_% xmm1) (%_% xmm2) (%_% xmm3) *)
 [0xc5; 0xf9; 0xfe; 0xff]; (* VPADDD (%_% xmm7) (%_% xmm0) (%_% xmm7) *)
 [0xc4; 0x41; 0x7d; 0xfe; 0xc1]; (* VPADDD ymm8, ymm8, ymm9 *)
 [0xc4; 0x41; 0x6d; 0xfe; 0xd3]; (* VPADDD ymm10, ymm10, ymm11 *)
 [0xc4; 0x41; 0x5d; 0xfe; 0xe5]; (* VPADDD ymm12, ymm12, ymm13 *)
 [0xc4; 0x41; 0x4d; 0xfe; 0xf7]; (* VPADDD ymm14, ymm14, ymm15 *)
 [0xc4; 0x41; 0x19; 0xfe; 0xdd]; (* VPADDD (%_% xmm11) (%_% xmm12) (%_% xmm13) *)
 [0xc4; 0x41; 0x11; 0xfe; 0xfc]; (* VPADDD (%_% xmm15) (%_% xmm13) (%_% xmm12) *)
 [0xc5; 0xfd; 0xfa; 0xc1]; (* VPSUBD ymm0, ymm0, ymm1 *)
 [0xc5; 0xf5; 0xfa; 0xca]; (* VPSUBD ymm1, ymm1, ymm2 *)
 [0xc5; 0xed; 0xfa; 0xd3]; (* VPSUBD ymm2, ymm2, ymm3 *)
 [0xc5; 0xe5; 0xfa; 0xdc]; (* VPSUBD ymm3, ymm3, ymm4 *)
 [0xc5; 0xf9; 0xfa; 0xc1]; (* VPSUBD xmm0, xmm0, xmm1 *)
 [0xc5; 0xf1; 0xfa; 0xca]; (* VPSUBD xmm1, xmm1, xmm2 *)
 [0xc5; 0xe9; 0xfa; 0xd3]; (* VPSUBD xmm2, xmm2, xmm3 *)
 [0xc5; 0xe1; 0xfa; 0xdc]; (* VPSUBD xmm3, xmm3, xmm4 *)
 [0xc4; 0x41; 0x7d; 0xfa; 0xc1]; (* VPSUBD ymm8, ymm8, ymm9 *)
 [0xc4; 0x41; 0x6d; 0xfa; 0xd3]; (* VPSUBD ymm10, ymm10, ymm11 *)
 [0xc4; 0x41; 0x5d; 0xfa; 0xe5]; (* VPSUBD ymm12, ymm12, ymm13 *)
 [0xc4; 0x41; 0x4d; 0xfa; 0xf7]; (* VPSUBD ymm14, ymm14, ymm15 *)
 [0xc4; 0x41; 0x39; 0xfa; 0xc1]; (* VPSUBD xmm8, xmm8, xmm9 *)
 [0xc4; 0x41; 0x29; 0xfa; 0xd3]; (* VPSUBD xmm10, xmm10, xmm11 *)
 [0xc4; 0x41; 0x19; 0xfa; 0xe5]; (* VPSUBD xmm12, xmm12, xmm13 *)
 [0xc4; 0x41; 0x09; 0xfa; 0xf7]; (* VPSUBD xmm14, xmm14, xmm15 *)
 [0xc5; 0x81; 0xf9; 0xf6]; (* VPSUBW (%_% xmm6) (%_% xmm15) (%_% xmm6) *)
 [0xc5; 0x85; 0xf9; 0xf6]; (* VPSUBW (%_% ymm6) (%_% ymm15) (%_% ymm6) *)
 [0xc5; 0x45; 0xfd; 0xd9]; (* VPADDW (%_% ymm11) (%_% ymm7) (%_% ymm11) *)
 [0xc5; 0x41; 0xfd; 0xd9]; (* VPADDW (%_% ymm11) (%_% ymm7) (%_% ymm11) *)
 [0xc4; 0xe3; 0x7d; 0x02; 0xc1; 0xff]; (* VPBLENDD ymm0, ymm0, ymm1, 0xff *)
 [0xc4; 0xe3; 0x75; 0x02; 0xca; 0x00]; (* VPBLENDD ymm1, ymm1, ymm2, 0x00 *)
 [0xc4; 0xe3; 0x6d; 0x02; 0xd3; 0x55]; (* VPBLENDD ymm2, ymm2, ymm3, 0x55 *)
 [0xc4; 0xe3; 0x65; 0x02; 0xdc; 0xaa]; (* VPBLENDD ymm3, ymm3, ymm4, 0xaa *)
 [0xc4; 0xe3; 0x5d; 0x02; 0xe5; 0x0f]; (* VPBLENDD ymm4, ymm4, ymm5, 0x0f *)
 [0xc4; 0xe3; 0x55; 0x02; 0xee; 0xf0]; (* VPBLENDD ymm5, ymm5, ymm6, 0xf0 *)
 [0xc4; 0x43; 0x7d; 0x02; 0xc1; 0xf0]; (* VPBLENDD ymm8, ymm8, ymm9, 0xf0 *)
 [0xc4; 0x43; 0x5d; 0x02; 0xd3; 0x33]; (* VPBLENDD ymm10, ymm10, ymm11, 0x33 *)
 [0xc4; 0x43; 0x3d; 0x02; 0xe5; 0xcc]; (* VPBLENDD ymm12, ymm12, ymm13, 0xcc *)
 [0xc4; 0x43; 0x1d; 0x02; 0xf7; 0x3c]; (* VPBLENDD ymm14, ymm14, ymm15, 0x3c *)
 [0xc4; 0xe3; 0x79; 0x02; 0xc1; 0x0f]; (* VPBLENDD xmm0, xmm0, xmm1, 0x0f *)
 [0xc4; 0xe3; 0x71; 0x02; 0xca; 0x00]; (* VPBLENDD xmm1, xmm1, xmm2, 0x00 *)
 [0xc4; 0xe3; 0x69; 0x02; 0xd3; 0x05]; (* VPBLENDD xmm2, xmm2, xmm3, 0x05 *)
 [0xc4; 0xe3; 0x61; 0x02; 0xdc; 0x0a]; (* VPBLENDD xmm3, xmm3, xmm4, 0x0a *)
 [0xc4; 0x43; 0x39; 0x02; 0xc1; 0x0a]; (* VPBLENDD xmm8, xmm8, xmm9, 0x0a *)
 [0xc4; 0x43; 0x59; 0x02; 0xd3; 0x0c]; (* VPBLENDD xmm10, xmm10, xmm11, 0x0c *)
 [0xc4; 0x43; 0x19; 0x02; 0xe5; 0x06]; (* VPBLENDD xmm12, xmm12, xmm13, 0x06 *)
 [0xc4; 0x43; 0x09; 0x02; 0xf7; 0x03]; (* VPBLENDD xmm14, xmm14, xmm15, 0x03 *)
 [0xc4; 0xc3; 0x69; 0x0e; 0xcf; 0x13]; (* VPBLENDW (%_% xmm1) (%_% xmm2) (%_% xmm15) (Imm8 (word 19)) *)
 [0xc4; 0xc3; 0x5d; 0x0e; 0xde; 0x1b]; (* VPBLENDW (%_% ymm3) (%_% ymm4) (%_% ymm14) (Imm8 (word 27)) *)
 [0xc4; 0x43; 0x19; 0x0e; 0xd5; 0x00]; (* VPBLENDW (%_% xmm10) (%_% xmm12) (%_% xmm13) (Imm8 (word 0)) *)
 [0xc4; 0x43; 0x0d; 0x0e; 0xff; 0xff]; (* VPBLENDW (%_% ymm15) (%_% ymm14) (%_% ymm15) (Imm8 (word 255)) *)
 [0xc4; 0xe3; 0x49; 0x0e; 0xfd; 0xde]; (* VPBLENDW (%_% xmm7) (%_% xmm6) (%_% xmm5) (Imm8 (word 222)) *)
 [0xc4; 0x43; 0x3d; 0x0e; 0xcf; 0x65]; (* VPBLENDW (%_% ymm9) (%_% ymm8) (%_% ymm15) (Imm8 (word 101)) *)
 [0xc4; 0xe2; 0x79; 0x58; 0xc1]; (* VPBROADCASTD xmm0, xmm1 *)
 [0xc4; 0xe2; 0x79; 0x58; 0xca]; (* VPBROADCASTD xmm1, xmm2 *)
 [0xc4; 0xe2; 0x7d; 0x58; 0xd3]; (* VPBROADCASTD ymm2, xmm3 *)
 [0xc4; 0x42; 0x7d; 0x58; 0xe5]; (* VPBROADCASTD ymm12, xmm13 *)
 [0xc4; 0x42; 0x79; 0x58; 0xc1]; (* VPBROADCASTD xmm8, xmm9 *)
 [0xc4; 0x42; 0x79; 0x58; 0xd3]; (* VPBROADCASTD xmm10, xmm11 *)
 [0xc4; 0xe2; 0x79; 0x58; 0xfc]; (* VPBROADCASTD xmm7, xmm4 *)
 [0xc4; 0x62; 0x79; 0x58; 0xef]; (* VPBROADCASTD xmm13, xmm7 *)
 [0xc4; 0xe2; 0x7d; 0x59; 0xc1]; (* VPBROADCASTQ ymm0, xmm1 *)
 [0xc4; 0xe2; 0x7d; 0x59; 0xca]; (* VPBROADCASTQ ymm1, xmm2 *)
 [0xc4; 0xe2; 0x7d; 0x59; 0xd3]; (* VPBROADCASTQ ymm2, xmm3 *)
 [0xc4; 0xe2; 0x7d; 0x59; 0xdc]; (* VPBROADCASTQ ymm3, xmm4 *)
 [0xc4; 0x62; 0x7d; 0x59; 0xc1]; (* VPBROADCASTQ ymm8, xmm9 *)
 [0xc4; 0x62; 0x7d; 0x59; 0xd3]; (* VPBROADCASTQ ymm10, xmm11 *)
 [0xc4; 0x62; 0x7d; 0x59; 0xe5]; (* VPBROADCASTQ ymm12, xmm13 *)
 [0xc4; 0x62; 0x7d; 0x59; 0xf7]; (* VPBROADCASTQ ymm14, xmm15 *)
 [0xc4; 0xe2; 0x79; 0x59; 0xc1]; (* VPBROADCASTQ xmm0, xmm1 *)
 [0xc4; 0xe2; 0x79; 0x59; 0xca]; (* VPBROADCASTQ xmm1, xmm2 *)
 [0xc4; 0xe2; 0x79; 0x59; 0xd3]; (* VPBROADCASTQ xmm2, xmm3 *)
 [0xc4; 0xe2; 0x79; 0x59; 0xdc]; (* VPBROADCASTQ xmm3, xmm4 *)
 [0xc4; 0x62; 0x79; 0x59; 0xc1]; (* VPBROADCASTQ xmm8, xmm9 *)
 [0xc4; 0x62; 0x79; 0x59; 0xd3]; (* VPBROADCASTQ xmm10, xmm11 *)
 [0xc4; 0x62; 0x79; 0x59; 0xe5]; (* VPBROADCASTQ xmm12, xmm13 *)
 [0xc4; 0x62; 0x79; 0x59; 0xf7]; (* VPBROADCASTQ xmm14, xmm15 *)
 [0xc4; 0xc2; 0x5d; 0x36; 0xde]; (* VPERMD (%_% ymm3) (%_% ymm4) (%_% ymm14) *)
 [0xc4; 0xe2; 0x75; 0x36; 0xc2]; (* VPERMD (%_% ymm0) (%_% ymm1) (%_% ymm2) *)
 [0xc4; 0xc2; 0x45; 0x36; 0xe8]; (* VPERMD (%_% ymm5) (%_% ymm7) (%_% ymm8) *)
 [0xc4; 0xc2; 0x35; 0x36; 0xf2]; (* VPERMD (%_% ymm6) (%_% ymm9) (%_% ymm10) *)
 [0xc4; 0xc2; 0x1d; 0x36; 0xc3]; (* VPERMD (%_% ymm0) (%_% ymm12) (%_% ymm11) *)
 [0xc4; 0x42; 0x0d; 0x36; 0xfd]; (* VPERMD (%_% ymm15) (%_% ymm14) (%_% ymm13) *)
 [0xc4; 0xe3; 0xfd; 0x00; 0xc1; 0x4e]; (* VPERMQ ymm0, ymm1, 0x4e *)
 [0xc4; 0xe3; 0xfd; 0x00; 0xd2; 0x1b]; (* VPERMQ ymm2, ymm2, 0x1b *)
 [0xc4; 0xe3; 0xfd; 0x00; 0xdb; 0x93]; (* VPERMQ ymm3, ymm3, 0x93 *)
 [0xc4; 0x43; 0xfd; 0x00; 0xc1; 0x27]; (* VPERMQ ymm8, ymm9, 0x27 *)
 [0xc4; 0x43; 0xfd; 0x00; 0xd3; 0xe4]; (* VPERMQ ymm10, ymm11, 0xe4 *)
 [0xc4; 0x43; 0xfd; 0x00; 0xe5; 0x72]; (* VPERMQ ymm12, ymm13, 0x72 *)
 [0xc4; 0x43; 0xfd; 0x00; 0xf7; 0x39]; (* VPERMQ ymm14, ymm15, 0x39 *)
 [0xc4; 0xe3; 0xfd; 0x00; 0xc0; 0x00]; (* VPERMQ ymm0, ymm0, 0x00 (identity) *)
 [0xc4; 0xe3; 0xfd; 0x00; 0xc9; 0xff]; (* VPERMQ ymm1, ymm1, 0xff (all from q3) *)
 [0xc4; 0xe3; 0x75; 0x46; 0xd3; 0x20]; (* VPERM2I128 ymm2, ymm1, ymm3, 0x20 *)
 [0xc4; 0xe3; 0x6d; 0x46; 0xe4; 0x31]; (* VPERM2I128 ymm4, ymm2, ymm4, 0x31 *)
 [0xc4; 0xe3; 0x65; 0x46; 0xed; 0x02]; (* VPERM2I128 ymm5, ymm3, ymm5, 0x02 *)
 [0xc4; 0x43; 0x3d; 0x46; 0xc1; 0x13]; (* VPERM2I128 ymm8, ymm8, ymm9, 0x13 *)
 [0xc4; 0x43; 0x2d; 0x46; 0xd3; 0x30]; (* VPERM2I128 ymm10, ymm10, ymm11, 0x30 *)
 [0xc4; 0x43; 0x1d; 0x46; 0xe5; 0x21]; (* VPERM2I128 ymm12, ymm12, ymm13, 0x21 *)
 [0xc4; 0x43; 0x0d; 0x46; 0xf7; 0x12]; (* VPERM2I128 ymm14, ymm14, ymm15, 0x12 *)
 [0xc4; 0xe3; 0x7d; 0x46; 0xc0; 0x00]; (* VPERM2I128 ymm0, ymm0, ymm0, 0x00 (identity) *)
 [0xc4; 0xe3; 0x75; 0x46; 0xca; 0x01]; (* VPERM2I128 ymm1, ymm1, ymm2, 0x01 (swap lanes) *)
 [0xc4; 0xe3; 0x75; 0x46; 0xd3; 0x08]; (* VPERM2I128 ymm2, ymm1, ymm3, 0x08 (zero low lane) *)
 [0xc4; 0xe3; 0x6d; 0x46; 0xe4; 0x18]; (* VPERM2I128 ymm4, ymm2, ymm4, 0x18 (zero high lane) *)
 [0xc4; 0xe3; 0x65; 0x46; 0xed; 0x88]; (* VPERM2I128 ymm5, ymm3, ymm5, 0x88 (zero both lanes) *)
 [0xc4; 0x62; 0x09; 0x00; 0xec]; (* VPSHUFB (%_% xmm13) (%_% xmm14) (%_% xmm4) *)
 [0xc4; 0xc2; 0x5d; 0x00; 0xde]; (* VPSHUFB (%_% ymm3) (%_% ymm4) (%_% ymm14) *)
 [0xc4; 0xc2; 0x31; 0x00; 0xf8]; (* VPSHUFB (%_% xmm7) (%_% xmm9) (%_% xmm8) *)
 [0xc4; 0xe2; 0x75; 0x00; 0xc2]; (* VPSHUFB (%_% ymm0) (%_% ymm1) (%_% ymm2) *)
 [0xc4; 0x42; 0x01; 0x00; 0xff]; (* VPSHUFB (%_% xmm15) (%_% xmm15) (%_% xmm15) *)
 [0xc4; 0xc2; 0x45; 0x00; 0xe8]; (* VPSHUFB (%_% ymm5) (%_% ymm7) (%_% ymm8) *)
 [0xc4; 0xe2; 0x79; 0x00; 0xca]; (* VPSHUFB (%_% xmm1) (%_% xmm0) (%_% xmm2) *)
 [0xc4; 0xc2; 0x35; 0x00; 0xf2]; (* VPSHUFB (%_% ymm6) (%_% ymm9) (%_% ymm10) *)
 [0xc4; 0xe2; 0x79; 0x00; 0xca]; (* VPSHUFB (%_% xmm1) (%_% xmm0) (%_% xmm2) *)
 [0xc4; 0xc2; 0x1d; 0x00; 0xc3]; (* VPSHUFB (%_% ymm0) (%_% ymm12) (%_% ymm11) *)
 [0xc4; 0xe2; 0x79; 0x00; 0xe4]; (* VPSHUFB (%_% xmm4) (%_% xmm0) (%_% xmm4) *)
 [0xc4; 0x42; 0x0d; 0x00; 0xfd]; (* VPSHUFB (%_% ymm15) (%_% ymm14) (%_% ymm13) *)
 [0xc4; 0xe2; 0xfd; 0x28; 0xc1]; (* VPMULDQ ymm0, ymm0, ymm1 *)
 [0xc4; 0xe2; 0xf5; 0x28; 0xca]; (* VPMULDQ ymm1, ymm1, ymm2 *)
 [0xc4; 0xe2; 0xed; 0x28; 0xd3]; (* VPMULDQ ymm2, ymm2, ymm3 *)
 [0xc4; 0xe2; 0xe5; 0x28; 0xdc]; (* VPMULDQ ymm3, ymm3, ymm4 *)
 [0xc4; 0x62; 0xfd; 0x28; 0xc1]; (* VPMULDQ ymm8, ymm8, ymm9 *)
 [0xc4; 0x62; 0xf5; 0x28; 0xca]; (* VPMULDQ ymm10, ymm10, ymm11 *)
 [0xc4; 0x62; 0xed; 0x28; 0xd3]; (* VPMULDQ ymm12, ymm12, ymm13 *)
 [0xc4; 0x62; 0xe5; 0x28; 0xdc]; (* VPMULDQ ymm14, ymm14, ymm15 *)
 [0xc4; 0xe2; 0x79; 0x28; 0xc1]; (* VPMULDQ xmm0, xmm0, xmm1 *)
 [0xc4; 0xe2; 0x71; 0x28; 0xca]; (* VPMULDQ xmm1, xmm1, xmm2 *)
 [0xc4; 0xe2; 0x69; 0x28; 0xd3]; (* VPMULDQ xmm2, xmm2, xmm3 *)
 [0xc4; 0xe2; 0x61; 0x28; 0xdc]; (* VPMULDQ xmm3, xmm3, xmm4 *)
 [0xc4; 0x62; 0x79; 0x28; 0xc1]; (* VPMULDQ xmm8, xmm8, xmm9 *)
 [0xc4; 0x62; 0x71; 0x28; 0xca]; (* VPMULDQ xmm10, xmm10, xmm11 *)
 [0xc4; 0x62; 0x69; 0x28; 0xd3]; (* VPMULDQ xmm12, xmm12, xmm13 *)
 [0xc4; 0x62; 0x61; 0x28; 0xdc]; (* VPMULDQ xmm14, xmm14, xmm15 *)
 [0xc5; 0x45; 0xe5; 0xfb]; (* VPMULHW (%_% ymm15) (%_% ymm7) (%_% ymm3) *)
 [0xc5; 0x41; 0xe5; 0xfb]; (* VPMULHW (%_% xmm15) (%_% xmm7) (%_% xmm3) *)
 [0xc4; 0xe2; 0x7d; 0x40; 0xc1]; (* VPMULLD ymm0, ymm0, ymm1 *)
 [0xc4; 0xe2; 0x75; 0x40; 0xca]; (* VPMULLD ymm1, ymm1, ymm2 *)
 [0xc4; 0xe2; 0x6d; 0x40; 0xd3]; (* VPMULLD ymm2, ymm2, ymm3 *)
 [0xc4; 0xe2; 0x65; 0x40; 0xdc]; (* VPMULLD ymm3, ymm3, ymm4 *)
 [0xc4; 0xe2; 0x79; 0x40; 0xc1]; (* VPMULLD xmm0, xmm0, xmm1 *)
 [0xc4; 0xe2; 0x71; 0x40; 0xca]; (* VPMULLD xmm1, xmm1, xmm2 *)
 [0xc4; 0xe2; 0x69; 0x40; 0xd3]; (* VPMULLD xmm2, xmm2, xmm3 *)
 [0xc4; 0xe2; 0x61; 0x40; 0xdc]; (* VPMULLD xmm3, xmm3, xmm4 *)
 [0xc4; 0x42; 0x3d; 0x40; 0xc1]; (* VPMULLD ymm8, ymm8, ymm9 *)
 [0xc4; 0x42; 0x2d; 0x40; 0xd3]; (* VPMULLD ymm10, ymm10, ymm11 *)
 [0xc4; 0x42; 0x1d; 0x40; 0xe5]; (* VPMULLD ymm12, ymm12, ymm13 *)
 [0xc4; 0x42; 0x0d; 0x40; 0xf7]; (* VPMULLD ymm14, ymm14, ymm15 *)
 [0xc4; 0x42; 0x39; 0x40; 0xc1]; (* VPMULLD xmm8, xmm8, xmm9 *)
 [0xc4; 0x42; 0x29; 0x40; 0xd3]; (* VPMULLD xmm10, xmm10, xmm11 *)
 [0xc4; 0x42; 0x19; 0x40; 0xe5]; (* VPMULLD xmm12, xmm12, xmm13 *)
 [0xc4; 0x42; 0x09; 0x40; 0xf7]; (* VPMULLD xmm14, xmm14, xmm15 *)
 [0xc4; 0xc1; 0x7d; 0xd5; 0xc9]; (* VPMULLW (%_% ymm1) (%_% ymm0) (%_% ymm9) *)
 [0xc4; 0xc1; 0x79; 0xd5; 0xc9]; (* VPMULLW (%_% xmm1) (%_% xmm0) (%_% xmm9) *)
 [0xc5; 0xa1; 0xdb; 0xd2]; (* VPAND (%_% xmm2) (%_% xmm11) (%_% xmm2) *)
 [0xc5; 0xa5; 0xdb; 0xd2]; (* VPAND (%_% ymm2) (%_% ymm11) (%_% ymm2) *)
 [0xc5; 0xfd; 0x73; 0xd1; 0x01;]; (* VPSRLQ (%_% ymm0) (%_% ymm1) (Imm8 (word 1)) *)
 [0xc4; 0xc1; 0x7d; 0x73; 0xd0; 0x08;]; (* VPSRLQ (%_% ymm0) (%_% ymm8) (Imm8 (word 8)) *)
 [0xc5; 0xf5; 0x73; 0xd0; 0x10;]; (* VPSRLQ (%_% ymm1) (%_% ymm0) (Imm8 (word 16)) *)
 [0xc4; 0xc1; 0x75; 0x73; 0xd7; 0x1f;]; (* VPSRLQ (%_% ymm1) (%_% ymm15) (Imm8 (word 31)) *)
 [0xc5; 0xed; 0x73; 0xd6; 0x20;]; (* VPSRLQ (%_% ymm2) (%_% ymm6) (Imm8 (word 32)) *)
 [0xc4; 0xc1; 0x6d; 0x73; 0xd6; 0x2f;]; (* VPSRLQ (%_% ymm2) (%_% ymm14) (Imm8 (word 47)) *)
 [0xc5; 0xe5; 0x73; 0xd3; 0x3f;]; (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 63)) *)
 [0xc4; 0xc1; 0x05; 0x73; 0xd6; 0x40;]; (* VPSRLQ (%_% ymm15) (%_% ymm14) (Imm8 (word 64)) *)
 [0xc5; 0xf9; 0x73; 0xd1; 0x01;]; (* VPSRLQ (%_% xmm0) (%_% xmm1) (Imm8 (word 1)) *)
 [0xc4; 0xc1; 0x79; 0x73; 0xd7; 0x0f;]; (* VPSRLQ (%_% xmm0) (%_% xmm15) (Imm8 (word 15)) *)
 [0xc5; 0xf1; 0x73; 0xd4; 0x20;]; (* VPSRLQ (%_% xmm1) (%_% xmm4) (Imm8 (word 32)) *)
 [0xc4; 0xc1; 0x71; 0x73; 0xd4; 0x3f;]; (* VPSRLQ (%_% xmm1) (%_% xmm12) (Imm8 (word 63)) *)
 [0xc5; 0xfd; 0x71; 0xe1; 0x01;]; (* VPSRAW (%_% ymm0) (%_% ymm1) (Imm8 (word 1)) *)
 [0xc4; 0xc1; 0x7d; 0x71; 0xe0; 0x08;]; (* VPSRAW (%_% ymm0) (%_% ymm8) (Imm8 (word 8)) *)
 [0xc5; 0xf5; 0x71; 0xe0; 0x10;]; (* VPSRAW (%_% ymm1) (%_% ymm0) (Imm8 (word 16)) *)
 [0xc4; 0xc1; 0x75; 0x71; 0xe7; 0x1f;]; (* VPSRAW (%_% ymm1) (%_% ymm15) (Imm8 (word 31)) *)
 [0xc5; 0xed; 0x71; 0xe6; 0x26;]; (* VPSRAW (%_% ymm2) (%_% ymm6) (Imm8 (word 38)) *)
 [0xc4; 0xc1; 0x6d; 0x71; 0xe6; 0x2e;]; (* VPSRAW (%_% ymm2) (%_% ymm14) (Imm8 (word 46)) *)
 [0xc5; 0xe5; 0x71; 0xe3; 0x33;]; (* VPSRAW (%_% ymm3) (%_% ymm3) (Imm8 (word 51)) *)
 [0xc4; 0xc1; 0x05; 0x71; 0xe6; 0xfe;]; (* VPSRAW (%_% ymm15) (%_% ymm14) (Imm8 (word 254)) *)
 [0xc5; 0xfd; 0x71; 0xd1; 0x01;]; (* VPSRLW (%_% ymm0) (%_% ymm1) (Imm8 (word 1)) *)
 [0xc4; 0xc1; 0x7d; 0x71; 0xd7; 0x0f;]; (* VPSRLW (%_% ymm0) (%_% ymm15) (Imm8 (word 15)) *)
 [0xc5; 0xf5; 0x71; 0xd4; 0x14;]; (* VPSRLW (%_% ymm1) (%_% ymm4) (Imm8 (word 20)) *)
 [0xc4; 0xc1; 0x75; 0x71; 0xd4; 0x1c;]; (* VPSRLW (%_% ymm1) (%_% ymm12) (Imm8 (word 28)) *)
 [0xc5; 0xed; 0x71; 0xd3; 0x23;]; (* VPSRLW (%_% ymm2) (%_% ymm3) (Imm8 (word 35)) *)
 [0xc4; 0xc1; 0x6d; 0x71; 0xd0; 0x28;]; (* VPSRLW (%_% ymm2) (%_% ymm8) (Imm8 (word 40)) *)
 [0xc5; 0xe5; 0x71; 0xd7; 0x37;]; (* VPSRLW (%_% ymm3) (%_% ymm7) (Imm8 (word 55)) *)
 [0xc4; 0xc1; 0x05; 0x71; 0xd7; 0xff]; (* VPSRLW (%_% ymm15) (%_% ymm15) (Imm8 (word 255)) *)
 [0xc5; 0xfd; 0x72; 0xe1; 0x01]; (* VPSRAD ymm0, ymm1, 1 *)
 [0xc5; 0xfd; 0x72; 0xe1; 0x10]; (* VPSRAD ymm0, ymm1, 16 *)
 [0xc5; 0xf5; 0x72; 0xe0; 0x1f]; (* VPSRAD ymm1, ymm0, 31 *)
 [0xc4; 0xc1; 0x3d; 0x72; 0xe0; 0x08]; (* VPSRAD ymm8, ymm0, 8 *)
 [0xc4; 0xc1; 0x7d; 0x72; 0xe0; 0x0c]; (* VPSRAD ymm0, ymm8, 12 *)
 [0xc4; 0x41; 0x2d; 0x72; 0xe4; 0x10]; (* VPSRAD ymm10, ymm12, 16 *)
 [0xc4; 0x41; 0x15; 0x72; 0xe1; 0x18]; (* VPSRAD ymm13, ymm9, 24 *)
 [0xc4; 0x41; 0x05; 0x72; 0xe7; 0x1f]; (* VPSRAD ymm15, ymm15, 31 *)
 [0xc5; 0xfd; 0x73; 0xf1; 0x01]; (* VPSLLQ ymm0, ymm1, 1 *)
 [0xc5; 0xfd; 0x73; 0xf1; 0x10]; (* VPSLLQ ymm0, ymm1, 16 *)
 [0xc5; 0xf5; 0x73; 0xf0; 0x3f]; (* VPSLLQ ymm1, ymm0, 63 *)
 [0xc5; 0xf9; 0x73; 0xf1; 0x01]; (* VPSLLQ xmm0, xmm1, 1 *)
 [0xc4; 0xc1; 0x3d; 0x73; 0xf0; 0x08]; (* VPSLLQ ymm8, ymm0, 8 *)
 [0xc4; 0xc1; 0x7d; 0x73; 0xf0; 0x0c]; (* VPSLLQ ymm0, ymm8, 12 *)
 [0xc4; 0x41; 0x2d; 0x73; 0xf4; 0x10]; (* VPSLLQ ymm10, ymm12, 16 *)
 [0xc4; 0x41; 0x15; 0x73; 0xf1; 0x18]; (* VPSLLQ ymm13, ymm9, 24 *)
 [0xc4; 0x41; 0x05; 0x73; 0xf7; 0x3f]; (* VPSLLQ ymm15, ymm15, 63 *)
 [0xc4; 0xc1; 0x79; 0x73; 0xf0; 0x20]; (* VPSLLQ xmm0, xmm8, 32 *)
 [0xc4; 0x41; 0x01; 0x73; 0xf7; 0x3f]; (* VPSLLQ xmm15, xmm15, 63 *)
 [0xc5; 0xf1; 0x71; 0xf2; 0x0b]; (* VPSLLW (%_% xmm1) (%_% xmm2) (Imm8 (word 11)) *)
 [0xc5; 0xd5; 0x71; 0xf5; 0x00]; (* VPSLLW (%_% ymm5) (%_% ymm5) (Imm8 (word 0)) *)
 [0xc4; 0xc1; 0x41; 0x71; 0xf1; 0x10]; (* VPSLLW (%_% xmm7) (%_% xmm9) (Imm8 (word 16)) *)
 [0xc4; 0xc1; 0x3d; 0x71; 0xf2; 0x11]; (* VPSLLW (%_% ymm8) (%_% ymm10) (Imm8 (word 17)) *)
 [0xc4; 0xc1; 0x09; 0x71; 0xf5; 0x21]; (* VPSLLW (%_% xmm14) (%_% xmm13) (Imm8 (word 33)) *)
 [0xc4; 0xc1; 0x1d; 0x71; 0xf7; 0x06]; (* VPSLLW (%_% ymm12) (%_% ymm15) (Imm8 (word 6)) *)
 [0xc4; 0xc1; 0x29; 0x71; 0xf3; 0xff]; (* VPSLLW (%_% xmm10) (%_% xmm11) (Imm8 (word 255)) *)
 [0xc5; 0xa5; 0x71; 0xf0; 0x80]; (* VPSLLW (%_% ymm11) (%_% ymm0) (Imm8 (word 128)) *)
 [0xc5; 0xf1; 0x72; 0xf2; 0x0b]; (* VPSLLD (%_% xmm1) (%_% xmm2) (Imm8 (word 11)) *)
 [0xc5; 0xd5; 0x72; 0xf5; 0x00]; (* VPSLLD (%_% ymm5) (%_% ymm5) (Imm8 (word 0)) *)
 [0xc4; 0xc1; 0x41; 0x72; 0xf1; 0x10]; (* VPSLLD (%_% xmm7) (%_% xmm9) (Imm8 (word 16)) *)
 [0xc4; 0xc1; 0x3d; 0x72; 0xf2; 0x11]; (* VPSLLD (%_% ymm8) (%_% ymm10) (Imm8 (word 17)) *)
 [0xc4; 0xc1; 0x09; 0x72; 0xf5; 0x21]; (* VPSLLD (%_% xmm14) (%_% xmm13) (Imm8 (word 33)) *)
 [0xc4; 0xc1; 0x1d; 0x72; 0xf7; 0x06]; (* VPSLLD (%_% ymm12) (%_% ymm15) (Imm8 (word 6)) *)
 [0xc4; 0xc1; 0x29; 0x72; 0xf3; 0xff]; (* VPSLLD (%_% xmm10) (%_% xmm11) (Imm8 (word 255)) *)
 [0xc5; 0xa5; 0x72; 0xf0; 0x80]; (* VPSLLD (%_% ymm11) (%_% ymm0) (Imm8 (word 128)) *)
 [0xc5; 0xf1; 0x72; 0xd2; 0x0b]; (* VPSRLD (%_% xmm1) (%_% xmm2) (Imm8 (word 11)) *)
 [0xc5; 0xd5; 0x72; 0xd5; 0x00]; (* VPSRLD (%_% ymm5) (%_% ymm5) (Imm8 (word 0)) *)
 [0xc4; 0xc1; 0x41; 0x72; 0xd1; 0x10]; (* VPSRLD (%_% xmm7) (%_% xmm9) (Imm8 (word 16)) *)
 [0xc4; 0xc1; 0x3d; 0x72; 0xd2; 0x11]; (* VPSRLD (%_% ymm8) (%_% ymm10) (Imm8 (word 17)) *)
 [0xc4; 0xc1; 0x09; 0x72; 0xd5; 0x21]; (* VPSRLD (%_% xmm14) (%_% xmm13) (Imm8 (word 33)) *)
 [0xc4; 0xc1; 0x1d; 0x72; 0xd7; 0x06]; (* VPSRLD (%_% ymm12) (%_% ymm15) (Imm8 (word 6)) *)
 [0xc4; 0xc1; 0x29; 0x72; 0xd3; 0xff]; (* VPSRLD (%_% xmm10) (%_% xmm11) (Imm8 (word 255)) *)
 [0xc5; 0xa5; 0x72; 0xd0; 0x80]; (* VPSRLD (%_% ymm11) (%_% ymm0) (Imm8 (word 128)) *)
 [0xc5; 0xfd; 0x6d; 0xc1]; (* VPUNPCKHQDQ ymm0, ymm0, ymm1 *)
 [0xc5; 0xf5; 0x6d; 0xca]; (* VPUNPCKHQDQ ymm1, ymm1, ymm2 *)
 [0xc5; 0xed; 0x6d; 0xd3]; (* VPUNPCKHQDQ ymm2, ymm2, ymm3 *)
 [0xc5; 0xe5; 0x6d; 0xdc]; (* VPUNPCKHQDQ ymm3, ymm3, ymm4 *)
 [0xc5; 0xf9; 0x6d; 0xc1]; (* VPUNPCKHQDQ xmm0, xmm0, xmm1 *)
 [0xc5; 0xf1; 0x6d; 0xca]; (* VPUNPCKHQDQ xmm1, xmm1, xmm2 *)
 [0xc5; 0xe9; 0x6d; 0xd3]; (* VPUNPCKHQDQ xmm2, xmm2, xmm3 *)
 [0xc4; 0x41; 0x7d; 0x6d; 0xc1]; (* VPUNPCKHQDQ ymm8, ymm8, ymm9 *)
 [0xc4; 0x41; 0x79; 0x6d; 0xc1]; (* VPUNPCKHQDQ xmm8, xmm8, xmm9 *)
 [0xc5; 0xfd; 0x6c; 0xc1]; (* VPUNPCKLQDQ ymm0, ymm0, ymm1 *)
 [0xc5; 0xf5; 0x6c; 0xca]; (* VPUNPCKLQDQ ymm1, ymm1, ymm2 *)
 [0xc5; 0xed; 0x6c; 0xd3]; (* VPUNPCKLQDQ ymm2, ymm2, ymm3 *)
 [0xc5; 0xe5; 0x6c; 0xdc]; (* VPUNPCKLQDQ ymm3, ymm3, ymm4 *)
 [0xc4; 0x41; 0x7d; 0x6c; 0xc1]; (* VPUNPCKLQDQ ymm8, ymm8, ymm9 *)
 [0xc4; 0x41; 0x6d; 0x6c; 0xd3]; (* VPUNPCKLQDQ ymm10, ymm10, ymm11 *)
 [0xc4; 0x41; 0x5d; 0x6c; 0xe5]; (* VPUNPCKLQDQ ymm12, ymm12, ymm13 *)
 [0xc4; 0x41; 0x4d; 0x6c; 0xf7]; (* VPUNPCKLQDQ ymm14, ymm14, ymm15 *)
 [0xc5; 0xf9; 0x6c; 0xc1]; (* VPUNPCKLQDQ xmm0, xmm0, xmm1 *)
 [0xc5; 0xf1; 0x6c; 0xca]; (* VPUNPCKLQDQ xmm1, xmm1, xmm2 *)
 [0xc5; 0xe9; 0x6c; 0xd3]; (* VPUNPCKLQDQ xmm2, xmm2, xmm3 *)
 [0xc4; 0x41; 0x79; 0x6c; 0xc1]; (* VPUNPCKLQDQ xmm8, xmm8, xmm9 *)
];;

(* ------------------------------------------------------------------------- *)
(* Run a random example.                                                     *)
(* ------------------------------------------------------------------------- *)

let template =
 `nonoverlapping (word pc,LENGTH ibytes) (stackpointer,256)
  ==> ensures x86
     (\s. bytes_loaded s (word pc) ibytes /\
          additional_assumptions /\
          read RIP s = word pc /\
          read RSP s = stackpointer /\
          regfile s = input_state)
     (\s. read RSP s = stackpointer /\
          regfile s = output_state)
     (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RBX; RBP; RSI; RDI;
                 R8; R9; R10; R11; R12; R13; R14; R15] ,,
      MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7;
                 ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
      MAYCHANGE [memory :> bytes(stackpointer,256)] ,,
      MAYCHANGE SOME_FLAGS)`;;

let num_two_to_64 = Num.num_of_string "18446744073709551616";;

let rec split_first_n (ls: 'a list) (n: int) =
  if n = 0 then ([], ls)
  else match ls with
    | h::t -> let l1, l2 = split_first_n t (n-1) in (h::l1, l2)
    | [] -> failwith "n cannot be smaller than the length of ls";;

let only_undefinedness =
  let zx_tm = `word_zx:int32->int64` in
  let is_undefname s =
     String.length s >= 10 && String.sub s 0 10 = "undefined_" in
  let is_undef t = is_var t && is_undefname (fst(dest_var t)) in
  let is_nundef tm = match tm with
      Comb(Comb(Const("=",_),l),r) when is_undef l -> true
    | Comb(Comb(Const("=",_),Comb(z,l)),r) when z = zx_tm && is_undef l -> true
    | Comb(Const("~",_),l) when is_undef l -> true
    | _ -> is_undef tm in
  forall is_nundef o conjuncts;;

(* This makes MESON quiet. *)
verbose := false;;

(*** Before and after tactics for goals that either do or don't involve
 *** memory operations (memop = they do). Non-memory ones are simpler and
 *** quicker; the memory ones do some more elaborate fiddling with format
 *** of memory assumptions to maximize their usability.
 ***)

let extra_simp_tac =
  REWRITE_TAC[WORD_RULE `word_sub x (word_add x y):N word = word_neg y`;
              WORD_RULE `word_sub y (word_add x y):N word = word_neg x`;
              WORD_RULE `word_sub (word_add x y) x:N word = y`;
              WORD_RULE `word_sub (word_add x y) y:N word = x`] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REWRITE_TAC[];;

let tac_before memop =
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[regfile; CONS_11; FLAGENCODING_11; VAL_WORD_GALOIS] THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[YMMENCODING_REGROUP] THEN CONV_TAC(DEPTH_CONV WORD_JOIN_CONV) THEN
  REWRITE_TAC[SOME_FLAGS] THEN ONCE_REWRITE_TAC[MESON[]
   `read RSP s = stackpointer /\ P (read RSP s) s <=>
    read RSP s = stackpointer /\ P stackpointer s`] THEN
  ENSURES_INIT_TAC "s0" THEN
  (if memop then MAP_EVERY MEMORY_SPLIT_TAC (0--4) else ALL_TAC)
and tac_main (memopidx: int option) mc states =
  begin match memopidx with
  | Some idx ->
    let states1, states2 = chop_list idx states in
    (if states1 <> [] then X86_STEPS_TAC mc states1 else ALL_TAC) THEN
    (if states2 <> [] then X86_VSTEPS_TAC mc states2 else ALL_TAC)
  | None -> X86_STEPS_TAC mc states
  end
and tac_after memop =
  (* MEMORY_SPLIT_TAC will split out the memory write to the stack.
   Assumptions for flags that involves memory reads of more than one byte
   (for example, ADD for byte64) will not be splitted out into bytes by
   MEMORY_SPLIT_TAC. Instead, the flag expression is only treated until
   it gets into the goal. After it gets into the goal, the first
   READ_MEMORY_FULLMERGE_CONV will split the memory read in the goal that
   represents the flag changes. After that we simplify/rewrite the goal.
   Given that the MEMORY_SPLIT_TAC splits out the memory write to the stack,
   the rewrites pick that up and turn the memory read in the flag expression
   into its RHS, which again isn't in byte form (but rather byte64 for the ADD
   example). To further assist, we will perform the READ_MEMORY_FULLMERGE_CONV
   and rewrite/simplification again for spliting out the memory read and
   simplify the goal. *)
  (if memop then MAP_EVERY MEMORY_SPLIT_TAC (0--4) else ALL_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (if memop then CONV_TAC(ONCE_DEPTH_CONV READ_MEMORY_FULLMERGE_CONV)
   else ALL_TAC) THEN
  ASM_REWRITE_TAC[] THEN extra_simp_tac THEN
  (if memop then CONV_TAC(ONCE_DEPTH_CONV READ_MEMORY_FULLMERGE_CONV)
   else ALL_TAC) THEN
  ASM_REWRITE_TAC[] THEN extra_simp_tac THEN
  ALL_TAC;;

(* A function that decodes a list of bytes into an x86 instruction.
 Could be used for figuring out if an instruction exist in s2n-bignum. *)
let decode_inst ibytes =
  let ibyteterm =
     mk_flist(map (curry mk_comb `word:num->byte` o mk_small_numeral) ibytes) in
  let execth = X86_MK_EXEC_RULE(REFL ibyteterm) in
  let decoded = mk_flist
     (map (rand o rand o snd o strip_forall o concl o Option.get)
       (filter Option.is_some (Array.to_list (snd execth)))) in
  let _ = print_term decoded in
  decoded;;

(*** Cosimulate a list of x86_64 instruction codes against hardware.
 *** To pass, the formal simulation has to agree with the hardware,
 *** only modify the 256-byte buffer [RSP,..,RSP+255] and also
 *** leave the final RSP value the same as the initial value, though
 *** it can be modified in between.
 ***)

let cosimulate_instructions (memopidx: int option) (add_assum: bool) ibytes_list =
  let ibyte_to_icode_fn =
    fun ibyte -> (itlist (fun h t -> num h +/ num 256 */ t) (List.rev ibyte) num_0) in
  let icodes = map ibyte_to_icode_fn ibytes_list in
  let icodestring =
    end_itlist (fun s t -> s^","^t) (map string_of_num_hex icodes) in
  let _ =
    (Format.print_string("Cosimulating "^icodestring);
     Format.print_newline()) in

  let ibytes = itlist (fun a b -> a @ b) ibytes_list [] in

  let ibyteterm =
    mk_flist(map (curry mk_comb `word:num->byte` o mk_small_numeral) ibytes) in

  let input_state = random_regstate() in

  let outfile = Filename.temp_file "x86simulator" ".out" in

  let command =
    "x86/proofs/x86simulate '" ^
    end_itlist (fun s t -> s ^ "," ^ t) (map string_of_int ibytes) ^
    "' " ^
    end_itlist (fun s t -> s ^ " " ^ t) (map string_of_num input_state) ^
    " >" ^ outfile in

  let _ = Sys.command command in
  (*** This branch determines whether the actual simulation worked ***)
  (*** In each branch we try to confirm that we likewise do or don't ***)

  if strings_of_file outfile <> [] then
    let resultstring = string_of_file outfile in

    let output_state_raw =
      map (fun (Ident s) -> num_of_string s)
          (lex(explode resultstring)) in

    (* Synthesize q registers from two 64 ints *)
    let output_state = output_state_raw in

    let add_assum_subst =
      if add_assum
      then `aligned 16 (stackpointer:int64):bool`,`additional_assumptions:bool`
      else `T:bool`,`additional_assumptions:bool` in
    let goal = subst
      [ibyteterm,`ibytes:byte list`;
       mk_flist(map mk_numeral input_state),`input_state:num list`;
       mk_flist(map mk_numeral output_state),`output_state:num list`;
       add_assum_subst]
      template in

    let execth = X86_MK_EXEC_RULE(REFL ibyteterm) in

    let inst_th = Option.get (snd execth).(0) in
    let decoded = mk_flist
      (map (rand o rand o snd o strip_forall o concl o Option.get)
        (filter Option.is_some (Array.to_list (snd execth)))) in

    let result =
      match
       (PURE_REWRITE_TAC [fst execth] THEN
        (tac_before (memopidx <> None) THEN
         tac_main memopidx execth (1--length icodes) THEN
         tac_after (memopidx <> None)))
       ([],goal)
      with
        _,[_,endres],_ ->
         (if endres = `T` || only_undefinedness endres then
            (Format.print_string "Modulo undefinedness "; true)
          else
            let _,[_,gsd],_ =
             (REWRITE_TAC[regfile; CONS_11; FLAGENCODING_11; VAL_WORD_GALOIS] THEN
              REWRITE_TAC[DIMINDEX_64; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
              REWRITE_TAC[SOME_FLAGS]) ([], goal) in
             (print_qterm gsd; Format.print_newline(); false))
     | _,[],_ -> true in
    (decoded,result)
  else
    let decoded = mk_flist(map mk_numeral icodes) in
    decoded,not(can X86_MK_EXEC_RULE(REFL ibyteterm));;

(*** Pick random instances from register-to-register iclasses and run ***)

let run_random_regsimulation () =
  let ibytes:int list = random_instruction iclasses in
  cosimulate_instructions None false [ibytes];;

(* ------------------------------------------------------------------------- *)
(* Setting up safe self-contained tests for memory accessing instructions.   *)
(* ------------------------------------------------------------------------- *)

(* Auxiliary instructions are for making sure operand registers don't depend
   on RSP. This is because RSP in the theorem statement is an arbitrary value
   represented by `stackpointer`. However in actual machine run, it is a
   concrete value. If certain register's value depends on RSP value then the
   machine run and the instruction modeling result won't match. *)

let rand_scale_index index_bound rest =
  let index = if rest = 0 then 0 else Random.int (min rest index_bound) in
  let log2_int = fun x -> int_of_float (Float.log2 (float_of_int x)) in
  let scale =
    (if index = 0 then Random.int 4
     else
       let scale_range = (log2_int (rest/index)) + 1 in
         Random.int (min scale_range 4)) in
  let rest = rest - index * int_of_float (2.0 ** (float_of_int scale)) in
  [rest, scale, index]

(* Mode: base + scale*index + displacement
   Fixed: use of registers, operand size = 64, displacement size = 8
   Randomized: addressing mode parameters *)
let cosimulate_mem_full_harness(opcode) = fun () ->
   (* disp8 is sign-extended *)
   let base = Random.int 128 in
   let rest = 248 - base in
   let [rest, scale, index] = rand_scale_index 128 rest in
   (* disp8 is sign-extended *)
   let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
   let sib = scale * int_of_float (2.0**6.0) + 0b001011 in
   [[0x48; 0xc7; 0xc1; index; 0x00; 0x00; 0x00]; (* MOV rcx, index *)
    [0x48; 0x89; 0xda]; (* MOV rdx, rbx *)
    [0x48; 0x8d; 0x5c; 0x24; base]; (* LEA rbx, [rsp+base] *)
    [0x48] @ opcode @ [0x44; sib; disp];  (* INST [rbx + scale*rcx + displacement], rax *)
    [0x48; 0x89; 0xd3]; (* MOV rbx, rdx *)
   ];;

(* Mode: base + displacement
   Fixed: use of registers, operand size = 64, displacement size = 8
   Randomized: addressing mode parameters
   *)
let cosimulate_mem_base_disp_harness(opcode) = fun () ->
  (* disp8 is sign-extended *)
  let stack_start = Random.int 128 in
  let rest = 248 - stack_start in
  let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
  [[0x48; 0x89; 0xda]; (* MOV rdx, rbx *)
   [0x48; 0x8d; 0x5c; 0x24; stack_start]; (* LEA rbx, [rsp+stack_start] *)
   [0x48] @ opcode @ [0x43; disp];  (* INST [rbx + displacement], rax *)
   [0x48; 0x89; 0xd3]; (* MOV rbx, rdx *)
  ];;

(* Mode: base (rsp) + scale*index + displacement
   Fixed: use of registers, operand size = 64
   Randomized: addressing mode parameters *)
let cosimulate_mem_rsp_harness(opcode) = fun () ->
  let [rest, scale, index] = rand_scale_index 128 248 in
  (* disp8 is a sign-extended *)
  let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
  let sib = scale * int_of_float (2.0**6.0) + 0b001100 in
  [[0x48; 0xc7; 0xc1; index; 0x00; 0x00; 0x00]; (* MOV rcx, index *)
   [0x48] @ opcode @ [0x44; sib; disp];  (* INST [rsp + scale*rcx + displacement], rax *)
  ];;

(* Mode: base + scale*index + displacement
   Fixed: use of registers, operand size = 64
   Randomized: addressing mode parameters *)
let cosimulate_mul_full_harness() = fun () ->
  (* disp8 is sign-extended *)
  let base = Random.int 128 in
  let rest = 248 - base in
  let [rest, scale, index] = rand_scale_index 128 rest in
  (* disp8 is sign-extended *)
  let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
  let sib = scale * int_of_float (2.0**6.0) + 0b001011 in
  [[0x48; 0xc7; 0xc1; index; 0x00; 0x00; 0x00]; (* MOV rcx, index *)
   [0x48; 0x89; 0xd8]; (* MOV r8, rbx *)
   [0x48; 0x8d; 0x5c; 0x24; base]; (* LEA rbx, [rsp+base] *)
   [0x48; 0xf7; 0x64; sib; disp];  (* MUL [rbx + scale*rcx + displacement] *)
   [0x4c; 0x89; 0xc3]; (* MOV rbx, r8 *)
  ];;

(* Mode: base + displacement
   Fixed: use of registers, operand size = 64
   Randomized: addressing mode parameters
  *)
let cosimulate_mul_base_disp_harness() = fun () ->
  (* disp8 is sign-extended *)
  let stack_start = Random.int 128 in
  let rest = 248 - stack_start in
  let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
  [[0x48; 0x89; 0xd8]; (* MOV r8, rbx *)
   [0x48; 0x8d; 0x5c; 0x24; stack_start]; (* LEA rbx, [rsp+stack_start] *)
   [0x48; 0xf7; 0x63; disp];  (* MUL [rbx + displacement] *)
   [0x4c; 0x89; 0xc3]; (* MOV rbx, r8 *)
  ];;

(* Mode: base (rsp) + scale*index + displacement
   Fixed: use of registers, operand size = 64
   Randomized: addressing mode parameters *)
let cosimulate_mul_rsp_harness() = fun () ->
   let [rest, scale, index] = rand_scale_index 128 248 in
   (* disp8 is a sign-extended *)
   let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
   let sib = scale * int_of_float (2.0**6.0) + 0b001100 in
   [[0x48; 0xc7; 0xc1; index; 0x00; 0x00; 0x00]; (* MOV rcx, index *)
    [0x48; 0xf7; 0x64; sib; disp];  (* MUL [rsp + scale*rcx + displacement], rax *)
   ];;

(* Fixed: operand size = 64 *)
let cosimulate_push_harness() = fun () ->
  let reg = Random.int 6 in
  let push_inst = 0x50 + reg in
  if reg = 4 then
    [[0x48; 0x8d; 0x64; 0x24; 0x10]; (* lea rsp, [rsp + 16] *)
     [0x48; 0x8b; 0x44; 0x24; 0xf8]; (* mov rax, [rsp - 8] *)
     [push_inst]; (* push rsp *)
     [0x48; 0x8b; 0x24; 0x24]; (* mov rsp, [rsp] *)
     [0x48; 0x89; 0x44; 0x24; 0xf8]; (* mov [rsp - 8], rax *)
     [0x48; 0x8d; 0x64; 0x24; 0xf0]; (* lea rsp, [rsp - 16] *)
    ]
  else
    [[0x48; 0x8d; 0x64; 0x24; 0x10]; (* lea rsp, [rsp + 16] *)
     [push_inst]; (* push REG *)
     [0x48; 0x8d; 0x64; 0x24; 0xf8] (* lea rsp, [rsp - 8] *)
    ];;

(* Fixed: operand size = 64 *)
let cosimulate_pop_harness() = fun () ->
  let reg = Random.int 6 in
  let pop_inst = 0x58 + reg in
  if reg = 4 then
    [[0x48; 0x8d; 0x64; 0x24; 0x10]; (* lea rsp, [rsp + 16] *)
     [0x48; 0x8b; 0x04; 0x24]; (* mov rax, [rsp] *)
     [0x48; 0x89; 0x24; 0x24]; (* mov [rsp], rsp *)
     [pop_inst]; (* pop rsp *)
     [0x48; 0x89; 0x04; 0x24]; (* mov [rsp], rax *)
     [0x48; 0x8d; 0x64; 0x24; 0xf0] (* lea rsp, [rsp - 16] *)
    ]
  else
    [[0x48; 0x8d; 0x64; 0x24; 0x10]; (* lea rsp, [rsp + 16] *)
     [pop_inst]; (* pop REG *)
     [0x48; 0x8d; 0x64; 0x24; 0xe8] (* lea rsp, [rsp - 24] *)
    ];;

(* Mode: base + scale*index + displacement
   Fixed: use of registers, displacement size = 8
   Randomized: addressing mode parameters *)
let cosimulate_sse_mov_unaligned_full_harness(pfx, opcode) = fun () ->
   (* disp8 is sign-extended *)
   let base = Random.int 128 in
   let rest = 240 - base in
   let [rest, scale, index] = rand_scale_index 128 rest in
   (* disp8 is sign-extended *)
   let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
   let sib = scale * int_of_float (2.0**6.0) + 0b001011 in
   let rex = if Random.int 2 = 0 then [0x44] else [] in
   [[0x48; 0xc7; 0xc1; index; 0x00; 0x00; 0x00]; (* MOV rcx, index *)
    [0x48; 0x89; 0xda]; (* MOV rdx, rbx *)
    [0x48; 0x8d; 0x5c; 0x24; base]; (* LEA rbx, [rsp+base] *)
    pfx @ rex @ opcode @ [0x4c; sib; disp];  (* INST [rbx + scale*rcx + displacement], imm1/9 *)
    [0x48; 0x89; 0xd3]; (* MOV rbx, rdx *)
   ];;

(* Mode: base + displacement
   Fixed: use of registers, displacement size = 8
   Randomized: addressing mode parameters
   *)
let cosimulate_sse_mov_unaligned_base_disp_harness(pfx, opcode) = fun () ->
  (* disp8 is sign-extended *)
  let stack_start = Random.int 128 in
  let rest = 240 - stack_start in
  let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
  let rex = if Random.int 2 = 0 then [0x44] else [] in
  [[0x48; 0x89; 0xda]; (* MOV rdx, rbx *)
   [0x48; 0x8d; 0x5c; 0x24; stack_start]; (* LEA rbx, [rsp+stack_start] *)
   pfx @ rex @ opcode @ [0x4b; disp];  (* INST [rbx + displacement], imm1/9 *)
   [0x48; 0x89; 0xd3]; (* MOV rbx, rdx *)
  ];;

(* Mode: base (rsp) + scale*index + displacement
   Fixed: use of registers
   Randomized: addressing mode parameters *)
let cosimulate_sse_mov_unaligned_rsp_harness(pfx, opcode) = fun () ->
  let [rest, scale, index] = rand_scale_index 128 240 in
  (* disp8 is a sign-extended *)
  let disp = if rest = 0 then 0 else Random.int (min 128 rest) in
  let sib = scale * int_of_float (2.0**6.0) + 0b001100 in
  let rex = if Random.int 2 = 0 then [0x44] else [] in
  [[0x48; 0xc7; 0xc1; index; 0x00; 0x00; 0x00]; (* MOV rcx, index *)
   pfx @ rex @ opcode @ [0x4c; sib; disp];  (* INST [rsp + scale*rcx + displacement], imm1/9 *)
  ];;

(* Mode: base + scale*index + displacement
   Fixed: use of registers, displacement size = 8
   Randomized: addressing mode parameters
   Note: address should be 16-aligned *)
let cosimulate_sse_mov_aligned_full_harness(pfx, opcode) = fun () ->
   (* Divide 256 by 16 because the address needs to be 16bytes aligned. *)
   let base = Random.int 8 in
   let rest = 15 - base in
   let [rest, scale, index] = rand_scale_index 8 rest in
   (* disp8 is sign-extended *)
   let disp = if rest = 0 then 0 else Random.int (min 8 rest) in
   let sib = scale * int_of_float (2.0**6.0) + 0b001011 in
   let rex = if Random.int 2 = 0 then [0x44] else [] in
   [[0x48; 0xc7; 0xc1; index*16; 0x00; 0x00; 0x00]; (* MOV rcx, index *)
    [0x48; 0x89; 0xda]; (* MOV rdx, rbx *)
    [0x48; 0x8d; 0x5c; 0x24; base*16]; (* LEA rbx, [rsp+base] *)
    pfx @ rex @ opcode @ [0x4c; sib; disp*16];  (* INST [rbx + scale*rcx + displacement], imm1/9 *)
    [0x48; 0x89; 0xd3]; (* MOV rbx, rdx *)
   ];;

(* Mode: base + displacement
   Fixed: use of registers, displacement size = 8
   Randomized: addressing mode parameters
   Note: address should be 16-aligned
   *)
let cosimulate_sse_mov_aligned_base_disp_harness(pfx, opcode) = fun () ->
  (* disp8 is sign-extended *)
  let stack_start = Random.int 8 in
  let rest = 15 - stack_start in
  let disp = if rest = 0 then 0 else Random.int (min 8 rest) in
  let rex = if Random.int 2 = 0 then [0x44] else [] in
  [[0x48; 0x89; 0xda]; (* MOV rdx, rbx *)
   [0x48; 0x8d; 0x5c; 0x24; stack_start*16]; (* LEA rbx, [rsp+stack_start] *)
   pfx @ rex @ opcode @ [0x4b; disp*16];  (* INST [rbx + displacement], imm1/9 *)
   [0x48; 0x89; 0xd3]; (* MOV rbx, rdx *)
  ];;

(* Mode: base (rsp) + scale*index + displacement
   Fixed: use of registers
   Randomized: addressing mode parameters
   Note: address should be 16-aligned
*)
let cosimulate_sse_mov_aligned_rsp_harness(pfx, opcode) = fun () ->
  let [rest, scale, index] = rand_scale_index 8 15 in
  (* disp8 is a sign-extended *)
  let disp = if rest = 0 then 0 else Random.int (min 8 rest) in
  let sib = scale * int_of_float (2.0**6.0) + 0b001100 in
  let rex = if Random.int 2 = 0 then [0x44] else [] in
  [[0x48; 0xc7; 0xc1; index*16; 0x00; 0x00; 0x00]; (* MOV rcx, index *)
   pfx @ rex @ opcode @ [0x4c; sib; disp*16];  (* INST [rsp + scale*rcx + displacement], imm1/9 *)
  ];;

(* Each mem simulation is a pair consists of a list of instructions
  to execute and a bool representing whether additional assumptions
  are needed. Currently the additional assumption is for stack
  alignment for certain instructions. To make the tests more diverse
  the evaluation of harnesses are deferred until an instruction is
  chosen from mem_iclasses *)
let mem_iclasses = [
  (* ADC r/m64, r64 *)
  (cosimulate_mem_full_harness([0x11]), false);
  (cosimulate_mem_base_disp_harness([0x11]), false);
  (cosimulate_mem_rsp_harness([0x11]), false);
  (* ADC r64, r/m64 *)
  (cosimulate_mem_full_harness([0x13]), false);
  (cosimulate_mem_base_disp_harness([0x13]), false);
  (cosimulate_mem_rsp_harness([0x013]), false);
  (* ADD r/m64, r64 *)
  (cosimulate_mem_full_harness([0x01]), false);
  (cosimulate_mem_base_disp_harness([0x01]), false);
  (cosimulate_mem_rsp_harness([0x01]), false);
  (* ADD r64, r/m64 *)
  (cosimulate_mem_full_harness([0x03]), false);
  (cosimulate_mem_base_disp_harness([0x03]), false);
  (cosimulate_mem_rsp_harness([0x03]), false);
  (* CMOVA r64, r/m64 *)
  (cosimulate_mem_full_harness([0x0F; 0x47]), false);
  (cosimulate_mem_base_disp_harness([0x0F; 0x47]), false);
  (cosimulate_mem_rsp_harness([0x0F; 0x47]), false);
  (* CMOVB r64, r/m64 *)
  (cosimulate_mem_full_harness([0x0F; 0x42]), false);
  (cosimulate_mem_base_disp_harness([0x0F; 0x42]), false);
  (cosimulate_mem_rsp_harness([0x0F; 0x42]), false);
  (* MOV r/m64, r64 *)
  (cosimulate_mem_full_harness([0x89]), false);
  (cosimulate_mem_base_disp_harness([0x89]), false);
  (cosimulate_mem_rsp_harness([0x89]), false);
  (* MOV r64, r/m64 *)
  (cosimulate_mem_full_harness([0x8B]), false);
  (cosimulate_mem_base_disp_harness([0x8B]), false);
  (cosimulate_mem_rsp_harness([0x8B]), false);
  (* MOVAPS xmm1, xmm2/m128 *)
  (cosimulate_sse_mov_aligned_full_harness([], [0x0f; 0x28]), true);
  (cosimulate_sse_mov_aligned_base_disp_harness([], [0x0f; 0x28]), true);
  (cosimulate_sse_mov_aligned_rsp_harness([], [0x0f; 0x28]), true);
  (* MOVAPS xmm2/m128, xmm1 *)
  (cosimulate_sse_mov_aligned_full_harness([], [0x0f; 0x29]), true);
  (cosimulate_sse_mov_aligned_base_disp_harness([], [0x0f; 0x29]), true);
  (cosimulate_sse_mov_aligned_rsp_harness([], [0x0f; 0x29]), true);
  (* MOVDQA xmm1, xmm2/m128 *)
  (cosimulate_sse_mov_aligned_full_harness([0x66], [0x0f; 0x6f]), true);
  (cosimulate_sse_mov_aligned_base_disp_harness([0x66], [0x0f; 0x6f]), true);
  (cosimulate_sse_mov_aligned_rsp_harness([0x66], [0x0f; 0x6f]), true);
  (* MOVDQA xmm2/m128, xmm1 *)
  (cosimulate_sse_mov_aligned_full_harness([0x66], [0x0f; 0x7f]), true);
  (cosimulate_sse_mov_aligned_base_disp_harness([0x66], [0x0f; 0x7f]), true);
  (cosimulate_sse_mov_aligned_rsp_harness([0x66], [0x0f; 0x7f]), true);
  (* MOVDQU xmm1, xmm2/m128 *)
  (cosimulate_sse_mov_unaligned_full_harness([0xf3], [0x0f; 0x6f]), false);
  (cosimulate_sse_mov_unaligned_base_disp_harness([0xf3], [0x0f; 0x6f]), false);
  (cosimulate_sse_mov_unaligned_rsp_harness([0xf3], [0x0f; 0x6f]), false);
  (* MOVDQU xmm2/m128, xmm1 *)
  (cosimulate_sse_mov_unaligned_full_harness([0xf3], [0x0f; 0x7f]), false);
  (cosimulate_sse_mov_unaligned_base_disp_harness([0xf3], [0x0f; 0x7f]), false);
  (cosimulate_sse_mov_unaligned_rsp_harness([0xf3], [0x0f; 0x7f]), false);
  (* MOVUPS xmm1, xmm2/m128 *)
  (cosimulate_sse_mov_unaligned_full_harness([], [0x0f; 0x10]), false);
  (cosimulate_sse_mov_unaligned_base_disp_harness([], [0x0f; 0x10]), false);
  (cosimulate_sse_mov_unaligned_rsp_harness([], [0x0f; 0x10]), false);
  (* MOVUPS xmm2/m128, xmm1 *)
  (cosimulate_sse_mov_unaligned_full_harness([], [0x0f; 0x11]), false);
  (cosimulate_sse_mov_unaligned_base_disp_harness([], [0x0f; 0x11]), false);
  (cosimulate_sse_mov_unaligned_rsp_harness([], [0x0f; 0x11]), false);
  (* MUL r/m64 *)
  (cosimulate_mul_full_harness(), false);
  (cosimulate_mul_base_disp_harness(), false);
  (cosimulate_mul_rsp_harness(), false);
  (* OR r/m64, r64 *)
  (cosimulate_mem_full_harness([0x09]), false);
  (cosimulate_mem_base_disp_harness([0x09]), false);
  (cosimulate_mem_rsp_harness([0x09]), false);
  (* OR r64, r/m64 *)
  (cosimulate_mem_full_harness([0x0B]), false);
  (cosimulate_mem_base_disp_harness([0x0B]), false);
  (cosimulate_mem_rsp_harness([0x0B]), false);
  (* PUSH r64 *)
  (cosimulate_push_harness(), false);
  (* POP r64 *)
  (cosimulate_pop_harness(), false);
  (* SBB r/m64, r64 *)
  (cosimulate_mem_full_harness([0x19]), false);
  (cosimulate_mem_base_disp_harness([0x19]), false);
  (cosimulate_mem_rsp_harness([0x19]), false);
  (* SBB r64, r/m64 *)
  (cosimulate_mem_full_harness([0x1B]), false);
  (cosimulate_mem_base_disp_harness([0x1B]), false);
  (cosimulate_mem_rsp_harness([0x1B]), false);
  (* SUB r/m64, r64 *)
  (cosimulate_mem_full_harness([0x29]), false);
  (cosimulate_mem_base_disp_harness([0x29]), false);
  (cosimulate_mem_rsp_harness([0x29]), false);
  (* SUB r64, r/m64 *)
  (cosimulate_mem_full_harness([0x2B]), false);
  (cosimulate_mem_base_disp_harness([0x2B]), false);
  (cosimulate_mem_rsp_harness([0x2B]), false);
  (* XOR r/m64, r64 *)
  (cosimulate_mem_full_harness([0x31]), false);
  (cosimulate_mem_base_disp_harness([0x31]), false);
  (cosimulate_mem_rsp_harness([0x31]), false);
  (* XOR r64, r/m64 *)
  (cosimulate_mem_full_harness([0x33]), false);
  (cosimulate_mem_base_disp_harness([0x33]), false);
  (cosimulate_mem_rsp_harness([0x33]), false);
  ];;

let run_random_memopsimulation() =
  let deferred_icodes,add_assum = el (Random.int (length mem_iclasses)) mem_iclasses in
  let icodes = deferred_icodes() in
  let l = length icodes in
  let _ = assert (l >= 2) in
  let memop_index = if l >= 6 then l - 4 else l - 2 in
  cosimulate_instructions (Some memop_index) add_assum icodes;;

(* ------------------------------------------------------------------------- *)
(* Keep running tests till a failure happens then return it.                 *)
(* ------------------------------------------------------------------------- *)

let run_random_simulation() =
  if Random.int 100 < 90 then
    let decoded, result = run_random_regsimulation() in
    decoded,result,true
  else
    let decoded, result = run_random_memopsimulation() in
    decoded,result,false;;

let time_limit_sec = 2400.0;;
let tested_reg_instances = ref 0;;
let tested_mem_instances = ref 0;;

let rec run_random_simulations start_t =
  let decoded,result,isreg = run_random_simulation() in
  if result then begin
    tested_reg_instances := !tested_reg_instances + (if isreg then 1 else 0);
    tested_mem_instances := !tested_mem_instances + (if isreg then 0 else 1);
    let fey = if is_numeral decoded
              then " (fails correctly) instruction code " else " " in
    let _ = Format.print_string("OK:" ^ fey ^ string_of_term decoded);
            Format.print_newline() in
    let now_t = Sys.time() in
    if now_t -. start_t > time_limit_sec then
      let _ = Printf.printf "Finished (time limit: %fs, tested reg instances: %d, tested mem instances: %d, total: %d)\n"
          time_limit_sec !tested_reg_instances !tested_mem_instances
          (!tested_reg_instances + !tested_mem_instances) in
      None
    else run_random_simulations start_t
  end
  else Some (decoded,result);;

(*** Depending on the degree of repeatability wanted.
 *** After a few experiments I'm now going full random.
 ***
 *** Random.init(Hashtbl.hash (Sys.getenv "HOST"));;
 ***)

Random.self_init();;

let start_t = Sys.time() (* unit is sec *) in
  match run_random_simulations start_t with
  | Some (t,_) -> Printf.printf "Error: term `%s`" (string_of_term t); failwith "simulator"
  | None -> ();;
