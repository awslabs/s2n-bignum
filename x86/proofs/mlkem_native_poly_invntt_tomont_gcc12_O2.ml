(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform from ML-KEM.                           *)
(* This is the code for mlkem_poly_invntt_tomont from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). Unlike the hand-written kernel, it reads its own *)
(* vectors of constants and table of zetas from the read-only data rather    *)
(* than taking tables as arguments.                                          *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "common/int_linear.ml";;

(**** print_literal_relocs_from_elf
        ~map_symbol_name:(function
          | "mlk_zetas" -> "mlk_zetas_data"
          | _ -> "mlkem_native_poly_invntt_tomont_gcc12_O2_data")
        "x86/mlkem_native/mlkem_native_poly_invntt_tomont_gcc12_O2.o";;
 ****)

let mlkem_native_poly_invntt_tomont_gcc12_O2_mc,
    mlkem_native_poly_invntt_tomont_gcc12_O2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "mlk_zetas" -> "mlk_zetas_data"
      | "mlkem_native_poly_invntt_tomont_gcc12_O2_constants" ->
          "mlkem_native_poly_invntt_tomont_gcc12_O2_data"
      | "WHOLE_READONLY" -> "mlkem_native_poly_invntt_tomont_gcc12_O2_rodata"
      | s -> failwith ("unknown symbol: " ^ s))
    "mlkem_native_poly_invntt_tomont_gcc12_O2_mc"
    "x86/mlkem_native/mlkem_native_poly_invntt_tomont_gcc12_O2.o"
(fun b ADDR -> [b[
  0x41; 0x57;              (* PUSH (% r15) *)
  0x66; 0x0f; 0x6f; 0x2d];
  ADDR ("mlkem_native_poly_invntt_tomont_gcc12_O2_data",(28)); b[
                           (* MOVDQA (%_% xmm5) (Memop Word128 (Riprel (word_sx
                                (iword
                                (&mlkem_native_poly_invntt_tomont_gcc12_O2_data
                                - (&pc + -- &22)))))) *)
  0x48; 0x8d; 0x97; 0x00; 0x02; 0x00; 0x00;
                           (* LEA (% rdx) (%% (rdi,512)) *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x66; 0x0f; 0x6f; 0x35];
  ADDR ("mlkem_native_poly_invntt_tomont_gcc12_O2_data",(-4)); b[
                           (* MOVDQA (%_% xmm6) (Memop Word128 (Riprel (word_sx
                                (iword
                                (&mlkem_native_poly_invntt_tomont_gcc12_O2_data
                                - (&pc + &30)))))) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x66; 0x0f; 0x6f; 0x25];
  ADDR ("mlkem_native_poly_invntt_tomont_gcc12_O2_data",(12)); b[
                           (* MOVDQA (%_% xmm4) (Memop Word128 (Riprel (word_sx
                                (iword
                                (&mlkem_native_poly_invntt_tomont_gcc12_O2_data
                                - (&pc + &24)))))) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x49; 0x89; 0xfc;        (* MOV (% r12) (% rdi) *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x90;                    (* NOP *)
  0xf3; 0x0f; 0x6f; 0x18;  (* MOVDQU (%_% xmm3) (Memop Word128 (%% (rax,0))) *)
  0xf3; 0x0f; 0x6f; 0x00;  (* MOVDQU (%_% xmm0) (Memop Word128 (%% (rax,0))) *)
  0x48; 0x83; 0xc0; 0x10;  (* ADD (% rax) (Imm8 (word 16)) *)
  0x66; 0x0f; 0xd5; 0xdd;  (* PMULLW (%_% xmm3) (%_% xmm5) *)
  0x66; 0x0f; 0xe5; 0xc5;  (* PMULHW (%_% xmm0) (%_% xmm5) *)
  0x66; 0x0f; 0x6f; 0xfb;  (* MOVDQA (%_% xmm7) (%_% xmm3) *)
  0x66; 0x0f; 0x69; 0xd8;  (* PUNPCKHWD (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x61; 0xf8;  (* PUNPCKLWD (%_% xmm7) (%_% xmm0) *)
  0x66; 0x0f; 0x6f; 0xc7;  (* MOVDQA (%_% xmm0) (%_% xmm7) *)
  0x66; 0x0f; 0x6f; 0xcf;  (* MOVDQA (%_% xmm1) (%_% xmm7) *)
  0x66; 0x0f; 0x61; 0xc3;  (* PUNPCKLWD (%_% xmm0) (%_% xmm3) *)
  0x66; 0x0f; 0x69; 0xcb;  (* PUNPCKHWD (%_% xmm1) (%_% xmm3) *)
  0x66; 0x0f; 0x6f; 0xd0;  (* MOVDQA (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x61; 0xc1;  (* PUNPCKLWD (%_% xmm0) (%_% xmm1) *)
  0x66; 0x0f; 0x69; 0xd1;  (* PUNPCKHWD (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x61; 0xc2;  (* PUNPCKLWD (%_% xmm0) (%_% xmm2) *)
  0x66; 0x0f; 0xd5; 0xc6;  (* PMULLW (%_% xmm0) (%_% xmm6) *)
  0x66; 0x0f; 0x6f; 0xd0;  (* MOVDQA (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x6f; 0xc8;  (* MOVDQA (%_% xmm1) (%_% xmm0) *)
  0x66; 0x0f; 0xe5; 0xcc;  (* PMULHW (%_% xmm1) (%_% xmm4) *)
  0x66; 0x0f; 0xd5; 0xd4;  (* PMULLW (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0x6f; 0xc2;  (* MOVDQA (%_% xmm0) (%_% xmm2) *)
  0x66; 0x0f; 0x69; 0xd1;  (* PUNPCKHWD (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x61; 0xc1;  (* PUNPCKLWD (%_% xmm0) (%_% xmm1) *)
  0x66; 0x0f; 0x6f; 0xca;  (* MOVDQA (%_% xmm1) (%_% xmm2) *)
  0x66; 0x0f; 0xfe; 0xc7;  (* PADDD (%_% xmm0) (%_% xmm7) *)
  0x66; 0x0f; 0xfe; 0xcb;  (* PADDD (%_% xmm1) (%_% xmm3) *)
  0x66; 0x0f; 0x72; 0xe1; 0x10;
                           (* PSRAD (%_% xmm1) (Imm8 (word 16)) *)
  0x66; 0x0f; 0x72; 0xe0; 0x10;
                           (* PSRAD (%_% xmm0) (Imm8 (word 16)) *)
  0x66; 0x0f; 0x6f; 0xd0;  (* MOVDQA (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x61; 0xc1;  (* PUNPCKLWD (%_% xmm0) (%_% xmm1) *)
  0x66; 0x0f; 0x69; 0xd1;  (* PUNPCKHWD (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x6f; 0xc8;  (* MOVDQA (%_% xmm1) (%_% xmm0) *)
  0x66; 0x0f; 0x69; 0xca;  (* PUNPCKHWD (%_% xmm1) (%_% xmm2) *)
  0x66; 0x0f; 0x61; 0xc2;  (* PUNPCKLWD (%_% xmm0) (%_% xmm2) *)
  0x66; 0x0f; 0x61; 0xc1;  (* PUNPCKLWD (%_% xmm0) (%_% xmm1) *)
  0x0f; 0x11; 0x40; 0xf0;  (* MOVUPS (Memop Word128 (%%
                                     (rax,18446744073709551600))) (%_% xmm0) *)
  0x48; 0x39; 0xd0;        (* CMP (% rax) (% rdx) *)
  0x0f; 0x85; 0x61; 0xff; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294967137)) *)
  0x41; 0xb9; 0x5c; 0x06; 0x00; 0x00;
                           (* MOV (% r9d) (Imm32 (word 1628)) *)
  0xb9; 0x07; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 7)) *)
  0x41; 0xbf; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r15d) (Imm32 (word 1)) *)
  0x4d; 0x8d; 0x74; 0x24; 0x02;
                           (* LEA (% r14) (%% (r12,2)) *)
  0x4c; 0x8d; 0x2d]; ADDR ("mlk_zetas_data",(-4)); b[
                           (* LEA (% r13) (Riprel (word_sx (iword
                                  (&mlk_zetas_data - (&pc + &236))))) *)
  0x45; 0x0f; 0xbf; 0xc1;  (* MOVSX (% r8d) (% r9w) *)
  0xbf; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% edi) (Imm32 (word 256)) *)
  0x45; 0x89; 0xfa;        (* MOV (% r10d) (% r15d) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0xd3; 0xef;              (* SHR (% edi) (% cl) *)
  0x41; 0xd3; 0xe2;        (* SHL (% r10d) (% cl) *)
  0x41; 0x83; 0xea; 0x01;  (* SUB (% r10d) (Imm8 (word 1)) *)
  0x8d; 0x1c; 0x3f;        (* LEA (% ebx) (%%% (rdi,0,rdi)) *)
  0x0f; 0x1f; 0x80; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x41; 0x83; 0xea; 0x01;  (* SUB (% r10d) (Imm8 (word 1)) *)
  0x39; 0xfe;              (* CMP (% esi) (% edi) *)
  0x0f; 0x83; 0x81; 0x00; 0x00; 0x00;
                           (* JAE (Imm32 (word 129)) *)
  0x89; 0xf8;              (* MOV (% eax) (% edi) *)
  0x41; 0x89; 0xf1;        (* MOV (% r9d) (% esi) *)
  0x89; 0x74; 0x24; 0xf4;  (* MOV (Memop Doubleword (%%
                                  (rsp,18446744073709551604))) (% esi) *)
  0x49; 0x8d; 0x14; 0x44;  (* LEA (% rdx) (%%% (r12,1,rax)) *)
  0x89; 0xf8;              (* MOV (% eax) (% edi) *)
  0x4b; 0x8d; 0x0c; 0x4c;  (* LEA (% rcx) (%%% (r12,1,r9)) *)
  0x29; 0xf0;              (* SUB (% eax) (% esi) *)
  0x83; 0xe8; 0x01;        (* SUB (% eax) (Imm8 (word 1)) *)
  0x4c; 0x01; 0xc8;        (* ADD (% rax) (% r9) *)
  0x49; 0x8d; 0x2c; 0x46;  (* LEA (% rbp) (%%% (r14,1,rax)) *)
  0x48; 0x89; 0xee;        (* MOV (% rsi) (% rbp) *)
  0x66; 0x90;              (* NOP *)
  0x44; 0x0f; 0xb7; 0x09;  (* MOVZX (% r9d) (Memop Word (%% (rcx,0))) *)
  0x0f; 0xb7; 0x2a;        (* MOVZX (% ebp) (Memop Word (%% (rdx,0))) *)
  0x48; 0x83; 0xc1; 0x02;  (* ADD (% rcx) (Imm8 (word 2)) *)
  0x48; 0x83; 0xc2; 0x02;  (* ADD (% rdx) (Imm8 (word 2)) *)
  0x44; 0x01; 0xcd;        (* ADD (% ebp) (% r9d) *)
  0x0f; 0xbf; 0xc5;        (* MOVSX (% eax) (% bp) *)
  0x69; 0xc0; 0xbf; 0x4e; 0x00; 0x00;
                           (* IMUL3 (% eax) (% eax,Imm32 (word 20159)) *)
  0x05; 0x00; 0x00; 0x00; 0x02;
                           (* ADD (% eax) (Imm32 (word 33554432)) *)
  0xc1; 0xf8; 0x1a;        (* SAR (% eax) (Imm8 (word 26)) *)
  0x66; 0x69; 0xc0; 0xff; 0xf2;
                           (* IMUL3 (% ax) (% ax,Imm16 (word 62207)) *)
  0x01; 0xe8;              (* ADD (% eax) (% ebp) *)
  0x66; 0x89; 0x41; 0xfe;  (* MOV (Memop Word (%% (rcx,18446744073709551614)))
                                  (% ax) *)
  0x0f; 0xb7; 0x42; 0xfe;  (* MOVZX (% eax) (Memop Word (%%
                                    (rdx,18446744073709551614))) *)
  0x44; 0x29; 0xc8;        (* SUB (% eax) (% r9d) *)
  0x44; 0x0f; 0xbf; 0xc8;  (* MOVSX (% r9d) (% ax) *)
  0x45; 0x0f; 0xaf; 0xc8;  (* IMUL (% r9d) (% r8d) *)
  0x66; 0x41; 0x69; 0xc1; 0x01; 0xf3;
                           (* IMUL3 (% ax) (% r9w,Imm16 (word 62209)) *)
  0x98;                    (* MOVSX (% eax) (% ax) *)
  0x69; 0xc0; 0xff; 0xf2; 0xff; 0xff;
                           (* IMUL3 (% eax) (% eax,Imm32 (word 4294963967)) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0xc1; 0xf8; 0x10;        (* SAR (% eax) (Imm8 (word 16)) *)
  0x66; 0x89; 0x42; 0xfe;  (* MOV (Memop Word (%% (rdx,18446744073709551614)))
                                  (% ax) *)
  0x48; 0x39; 0xf1;        (* CMP (% rcx) (% rsi) *)
  0x75; 0xa7;              (* JNE (Imm8 (word 167)) *)
  0x8b; 0x74; 0x24; 0xf4;  (* MOV (% esi) (Memop Doubleword (%%
                                  (rsp,18446744073709551604))) *)
  0x01; 0xde;              (* ADD (% esi) (% ebx) *)
  0x01; 0xdf;              (* ADD (% edi) (% ebx) *)
  0x81; 0xfe; 0xff; 0x00; 0x00; 0x00;
                           (* CMP (% esi) (Imm32 (word 255)) *)
  0x77; 0x17;              (* JA (Imm8 (word 23)) *)
  0x44; 0x89; 0xd0;        (* MOV (% eax) (% r10d) *)
  0x45; 0x0f; 0xbf; 0x44; 0x45; 0x00;
                           (* MOVSX (% r8d) (Memop Word (%%% (r13,1,rax))) *)
  0xe9; 0x59; 0xff; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294967129)) *)
  0x66; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x44; 0x89; 0xd9;        (* MOV (% ecx) (% r11d) *)
  0x83; 0xe9; 0x01;        (* SUB (% ecx) (Imm8 (word 1)) *)
  0x74; 0x13;              (* JE (Imm8 (word 19)) *)
  0x44; 0x89; 0xf8;        (* MOV (% eax) (% r15d) *)
  0xd3; 0xe0;              (* SHL (% eax) (% cl) *)
  0x83; 0xe8; 0x01;        (* SUB (% eax) (Imm8 (word 1)) *)
  0x45; 0x0f; 0xbf; 0x44; 0x45; 0x00;
                           (* MOVSX (% r8d) (Memop Word (%%% (r13,1,rax))) *)
  0xe9; 0x15; 0xff; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294967061)) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0xc3                     (* RET *)
]]);;


let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_poly_invntt_tomont_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* The computation done by the C code, with its 16-bit and 32-bit integer    *)
(* arithmetic. The coefficients are first scaled by a Montgomery             *)
(* multiplication by 1441 = 2^25 mod 3329, in a loop that the compiler has   *)
(* vectorized. Then the inverse NTT is done in 7 layers, for l = 7 down to   *)
(* 1, layer l consisting of 2^(l-1) blocks of 2^(9-l) consecutive            *)
(* coefficients. A block uses one zeta to do butterflies on pairs of         *)
(* coefficients 2^(8-l) apart, independently, with a Barrett reduction of    *)
(* the sums.                                                                 *)
(* ------------------------------------------------------------------------- *)

let invntt_scale_c = define
 `invntt_scale_c (x:num->int16) i =
    montred_scalar(word_mul (word_sx(x i)) (word 1441))`;;

let invntt_fqmul_c = define
 `invntt_fqmul_c (z:int16) (y:int16) =
    montred_scalar(word_mul (word_sx y) (word_sx z))`;;

let invntt_block_c = define
 `invntt_block_c (z:int16) start len (m:num->int16) i =
    if start <= i /\ i < start + len
    then barred(word_add (m i) (m(i + len)))
    else if start + len <= i /\ i < start + 2 * len
    then invntt_fqmul_c z (word_sub (m i) (m(i - len)))
    else m i`;;

let invntt_blocks_c = define
 `invntt_blocks_c l 0 (r:num->int16) = r /\
  invntt_blocks_c l (SUC b) r =
    invntt_block_c (iword(EL (2 EXP l - 1 - b) mlk_zetas))
                   (2 * 2 EXP (8 - l) * b) (2 EXP (8 - l))
                   (invntt_blocks_c l b r)`;;

let invntt_layers_c = define
 `invntt_layers_c 0 (x:num->int16) = x /\
  invntt_layers_c (SUC n) x =
    invntt_blocks_c (7 - n) (2 EXP (6 - n)) (invntt_layers_c n x)`;;

(* ------------------------------------------------------------------------- *)
(* The vectors of constants in the read-only data.                           *)
(* ------------------------------------------------------------------------- *)

let INVNTT_CONSTANTS_LOADED = prove
 (`!c s. bytes_loaded s (word c) mlkem_native_poly_invntt_tomont_gcc12_O2_data
         ==> read(memory :> bytes128(word c)) s =
             word 0xf301f301f301f301f301f301f301f301 /\
             read(memory :> bytes128(word(c + 16))) s =
             word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
             read(memory :> bytes128(word(c + 32))) s =
             word 0x05a105a105a105a105a105a105a105a1`,
  let dth = find
   (fun th -> name_of(lhs(concl th)) =
              "mlkem_native_poly_invntt_tomont_gcc12_O2_data")
   mlkem_native_poly_invntt_tomont_gcc12_O2_data in
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[WORD_ADD_0]
   `word c:int64 = word_add (word c) (word 0)`] THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC; WORD_ADD_0] THEN
  MAP_EVERY (fun k ->
     MP_TAC(SPECL [`word c:int64`;
                   `mlkem_native_poly_invntt_tomont_gcc12_O2_data`;
                   k; `s:x86state`] BYTES_LOADED_BYTES128))
   [`0`; `16`; `32`] THEN
  ASM_REWRITE_TAC[CONV_RULE(RAND_CONV LENGTH_CONV)
               (AP_TERM `LENGTH:byte list->num` dth)] THEN
  REWRITE_TAC[dth; num_of_bytelist] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The value computed in each lane of the scaling. The compiler forms the    *)
(* 32-bit products from the 16-bit high and low halves given by PMULHW and   *)
(* PMULLW, which it interleaves and later de-interleaves with PUNPCKLWD and  *)
(* PUNPCKHWD.                                                                *)
(* ------------------------------------------------------------------------- *)

let INVNTT_LANE_FORM = prove
 (`!x:int16.
     word_subword
      (word_ishr
        (word_add
          (word_join
            (word_subword
              (word_mul (word_sx (word_mul (word_mul x (word 1441))
                                           (word 62209)):int32)
                        (word 4294963967))
              (16,16):int16)
            (word_mul (word_mul (word_mul x (word 1441)) (word 62209))
                      (word 62207)):int32)
          (word_join
            (word_subword (word_mul (word_sx x:int32) (word 1441))
                          (16,16):int16)
            (word_mul x (word 1441)):int32))
        16)
      (0,16):int16 =
     montred_scalar (word_mul (word_sx x) (word 1441))`,
  GEN_TAC THEN
  MP_TAC(ISPECL
   [`word_mul (word_mul (x:int16) (word 1441)) (word 62209):int16`;
    `word 62207:int16`] WORD_JOIN_MULHI_MULLO) THEN
  MP_TAC(ISPECL [`x:int16`; `word 1441:int16`] WORD_JOIN_MULHI_MULLO) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM MONTRED_X86_SCALAR; montred_x86] THEN
  SIMP_TAC[WORD_ZX_MUL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  REWRITE_TAC[WORD_BLAST `word_zx(word_sx (x:int16):int32) = x`] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[WORD_BLAST `word_subword (y:int32) (0,16):int16 = word_zx y`]);;

(* ------------------------------------------------------------------------- *)
(* Some word lemmas for the butterflies.                                     *)
(* ------------------------------------------------------------------------- *)

(*** The Barrett reduction as compiled, multiplying the bottom 16 bits of
 *** the quotient by -3329 in a 16-bit register and then adding the 32-bit
 *** sum, of which only the bottom 16 bits matter
 ***)

let INVNTT_BARRETT_GCC12_O2 = prove
 (`!(h:48 word) (p:int16) (y:int32).
     word_zx(word_add (word_zx (word_join h p:int64):int32) y):int16 =
     word_add (word_zx y) p`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[WORD_ZX_ADD; WORD_ZX_ZX_GEN; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64;
           ARITH] THEN
  REWRITE_TAC[WORD_ZX_JOIN_48_16; WORD_ADD_SYM]);;

(*** The 16-bit sum or difference of coefficients, formed in 32 bits ***)

let WORD_ZX_ADD_ZX_ZX_16 = prove
 (`!u t:int16. word_zx(word_add (word_zx u) (word_zx t):int32):int16 =
               word_add u t`,
  SIMP_TAC[WORD_ZX_ADD; WORD_ZX_ZX; WORD_ZX_TRIVIAL; DIMINDEX_16; DIMINDEX_32;
           ARITH]);;

let WORD_ZX_SUB_ZX_ZX_16 = prove
 (`!u t:int16. word_zx(word_sub (word_zx u) (word_zx t):int32):int16 =
               word_sub u t`,
  SIMP_TAC[WORD_ZX_SUB; WORD_ZX_ZX; WORD_ZX_TRIVIAL; DIMINDEX_16; DIMINDEX_32;
           ARITH]);;

(* ------------------------------------------------------------------------- *)
(* One block, from its setup through the inner loop.                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK = prove
 (`!a consts zetas pc sbase z start len k m w11 w15.
     ALL (nonoverlapping (a,512))
         [(word pc,0x1e6); (word zetas,256); (sbase,4)] /\
     ALL (nonoverlapping (sbase,4)) [(word pc,0x1e6); (word zetas,256)] /\
     1 <= len /\ start + 2 * len <= 256 /\ 1 <= k /\ k < 256
     ==> ensures x86
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_invntt_tomont_gcc12_O2_mc
                    pc consts zetas) /\
               read RIP s = word(pc + 0x110) /\
               read RSI s = word start /\ read RDI s = word(start + len) /\
               read R10 s = word k /\
               read R8 s = word_zx(word_sx z:int32) /\
               read RBX s = word(2 * len) /\
               read R12 s = a /\ read R14 s = word_add a (word 2) /\
               read R13 s = word zetas /\
               read R11 s = w11 /\ read R15 s = w15 /\
               read RSP s = word_add sbase (word 12) /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_invntt_tomont_gcc12_O2_mc
                    pc consts zetas) /\
               read RIP s = word(pc + 0x19d) /\
               read RSI s = word start /\ read RDI s = word(start + len) /\
               read R10 s = word(k - 1) /\
               read R8 s = word_zx(word_sx z:int32) /\
               read RBX s = word(2 * len) /\
               read R12 s = a /\ read R14 s = word_add a (word 2) /\
               read R13 s = word zetas /\
               read R11 s = w11 /\ read R15 s = w15 /\
               read RSP s = word_add sbase (word 12) /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_block_c z start len m i))
          (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; R9; R10; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512); memory :> bytes(sbase,4)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The inner loop, RCX and RDX pointing at the lower and upper ***)
  (*** coefficients and RSI at the end of the upper ones           ***)

  ENSURES_WHILE_UP_TAC `len:num` `pc + 0x140` `pc + 0x194`
   `\jj s. bytes_loaded s (word pc)
             (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
           read RCX s = word_add a (word(2 * (start + jj))) /\
           read RDX s = word_add a (word(2 * (start + len + jj))) /\
           read RSI s = word_add a (word(2 * (start + len))) /\
           read RDI s = word(start + len) /\
           read R10 s = word(k - 1) /\
           read R8 s = word_zx(word_sx z:int32) /\
           read RBX s = word(2 * len) /\
           read R12 s = a /\ read R14 s = word_add a (word 2) /\
           read R13 s = word zetas /\
           read R11 s = w11 /\ read R15 s = w15 /\
           read RSP s = word_add sbase (word 12) /\
           read (memory :> bytes32 sbase) s = word start /\
           (!k. k < 128
                ==> read(memory :> bytes16(word_add (word zetas)
                                                    (word(2 * k)))) s =
                    iword(EL k mlk_zetas)) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    if start <= i /\ i < start + jj \/
                       start + len <= i /\ i < start + len + jj
                    then invntt_block_c z start len m i else m i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Setting up the pointers for the inner loop ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (3--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN WORD_SMALL_TAC;

    (*** The inner loop body, one butterfly ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `m:num->int16` (concl th)
      then MP_TAC(SPEC `start + jj:num` th) THEN
           MP_TAC(SPEC `start + len + jj:num` th) THEN
           ASSUME_TAC(BETA_RULE(MATCH_MP (SPEC
             `\i. ~(i = start + jj) /\ ~(i = start + len + jj)`
             (MESON[] `!R P Q. (!i:num. P i ==> Q i)
                               ==> (!i. P i /\ R i ==> Q i)`)) th))
      else failwith "") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LT_REFL; ARITH_RULE
     `jj < len
      ==> ~(start <= start + len + jj /\ start + len + jj < start + jj) /\
          ~(start + len <= start + len + jj /\
            start + len + jj < start + len + jj)`] THEN
    DISCH_TAC THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LT_REFL; ARITH_RULE
     `jj < len
      ==> ~(start <= start + jj /\ start + jj < start + jj) /\
          ~(start + len <= start + jj /\ start + jj < start + len + jj)`] THEN
    DISCH_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--22) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i = start + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LE_ADD; ARITH_RULE `start + jj < start + jj + 1`] THEN
      MLKEM_NATIVE_WORD_SIMP_TAC THEN
      REWRITE_TAC[INVNTT_BARRETT_GCC12_O2; WORD_ZX_ADD_ZX_ZX_16] THEN
      REWRITE_TAC[BARRED_GCC12_O2] THEN
      REWRITE_TAC[invntt_block_c; LE_ADD; LT_ADD_LCANCEL] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_AC; WORD_ADD_SYM];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = start + len + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `start + len + jj < start + len + jj + 1`;
                  ARITH_RULE `start + len <= start + len + jj`] THEN
      MLKEM_NATIVE_WORD_SIMP_TAC THEN
      REWRITE_TAC[MONTRED_X86_FOLD; WORD_ZX_SUB_ZX_ZX_16] THEN
      REWRITE_TAC[invntt_block_c; invntt_fqmul_c] THEN
      SUBGOAL_THEN
       `~(start <= start + len + jj /\ start + len + jj < start + len) /\
        start + len <= start + len + jj /\
        start + len + jj < start + 2 * len`
       (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `jj < len` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(start + len + jj) - len = start + jj`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY UNDISCH_TAC [`~(i = start + jj)`; `~(i = start + len + jj)`] THEN
    ARITH_TAC;

    (*** The inner loop back-edge ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The inner loop exit and the end of the block, restoring RSI ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[invntt_block_c] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One layer, with the blocks in a loop (except for the last layer).         *)
(* ------------------------------------------------------------------------- *)

(*** Assertions at the block head for layer l, block b, and at the block
 *** end for layer l after block b, with the block counters not yet updated
 ***)

let invntt_blockhead_tm,invntt_blockend_tm =
  let headtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
        read RSI s = word(2 * LEN * B) /\
        read RDI s = word(2 * LEN * B + LEN) /\
        read R10 s = word(2 EXP L - 1 - B) /\
        read R8 s =
        word_zx(word_sx(iword(EL (2 EXP L - 1 - B) mlk_zetas):int16):int32) /\
        read RBX s = word(2 * LEN) /\
        read R12 s = a /\ read R14 s = word_add a (word 2) /\
        read R13 s = word zetas /\
        read R11 s = word L /\ read R15 s = word 1 /\
        read RSP s = word_add sbase (word 12) /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_blocks_c L B r i)`
  and endtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
        read RSI s = word(2 * LEN * B) /\
        read RDI s = word(2 * LEN * B + LEN) /\
        read R10 s = word(2 EXP L - 1 - B - 1) /\
        read RBX s = word(2 * LEN) /\
        read R12 s = a /\ read R14 s = word_add a (word 2) /\
        read R13 s = word zetas /\
        read R11 s = word L /\ read R15 s = word 1 /\
        read RSP s = word_add sbase (word 12) /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_blocks_c L (B + 1) r i)` in
  let mk tm l b =
    let len = mk_small_numeral(1 lsl (8 - l)) in
    let tm' = subst [mk_small_numeral l,`L:num`; len,`LEN:num`; b,`B:num`]
                    tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l b -> mk headtm l b),(fun l b -> mk endtm l b);;

(*** Apply the block lemma at the head of block b of layer l ***)

let INVNTT_BLOCK_TAC l b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (8 - l)),`LEN:num`;
      b,`B:num`] t))) in
  let th = SPECL
   [`a:int64`; `consts:num`; `zetas:num`; `pc:num`; `sbase:int64`;
    red `iword(EL (2 EXP L - 1 - B) mlk_zetas):int16`;
    red `2 * LEN * B`; red `LEN:num`; red `2 EXP L - 1 - B`;
    red `invntt_blocks_c L B r`; red `word L:int64`; `word 1:int64`]
   MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 invntt_blocks_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ENSURES_WEAKEN_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth] THEN
    REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** The layer head, setting up the registers for the first block ***)

let INVNTT_LAYERHEAD_TAC l =
  ENSURES_SEQUENCE_TAC `pc + 0x110` (invntt_blockhead_tm l `0`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[invntt_blocks_c] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** Going from the end of block i to the head of block i + 1, loading
 *** its zeta, and the exit from the block loop at the end of the layer
 ***)

let INVNTT_BLOCKBACK_TAC l =
  let idx = rhs(concl(NUM_REDUCE_CONV
   (subst [mk_small_numeral l,`L:num`] `2 EXP L - 1 - i - 1`))) in
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--3) THEN
  W32_DECIDE_FLAGS_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (4--5) THEN
  W64_ZX_SMALL_TAC THEN VAL_INT64_TAC idx THEN
  READ_INSTANCE_TAC (subst [idx,`n:num`]
   `read (memory :> bytes16 (word_add (word zetas) (word (2 * n)))) s5 =
    iword(EL n mlk_zetas)`) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (6--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `!n i. n - i - 1 = n - (i + 1)`] THEN
  REPEAT CONJ_TAC THEN
  (WORD_SMALL_TAC ORELSE (REPEAT AP_TERM_TAC THEN SIMPLE_ARITH_TAC));;

let INVNTT_LAYEREXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--3) THEN
  W32_DECIDE_FLAGS_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (4--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The whole layer l (counting down from 7) ***)

let INVNTT_LAYER_TAC l =
  INVNTT_LAYERHEAD_TAC l THEN
  ENSURES_SEQUENCE_TAC `pc + 0x19d` (invntt_blockend_tm l `0`) THEN
  CONJ_TAC THENL
   [INVNTT_BLOCK_TAC l `0`;
    if l = 1 then INVNTT_LAYEREXIT_TAC else
    ENSURES_WHILE_UP_TAC (mk_small_numeral(1 lsl (l - 1) - 1))
      `pc + 0x19d` `pc + 0x19d`
      (mk_abs(`i:num`,invntt_blockend_tm l `i:num`)) THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_SEQUENCE_TAC `pc + 0x110` (invntt_blockhead_tm l `i + 1`) THEN
      CONJ_TAC THENL
       [INVNTT_BLOCKBACK_TAC l; INVNTT_BLOCK_TAC l `i + 1`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[];
      INVNTT_LAYEREXIT_TAC]];;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYER = prove
 (`!a consts zetas pc sbase l r.
     ALL (nonoverlapping (a,512))
         [(word pc,0x1e6); (word zetas,256); (sbase,4)] /\
     ALL (nonoverlapping (sbase,4)) [(word pc,0x1e6); (word zetas,256)] /\
     l < 7
     ==> ensures x86
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_invntt_tomont_gcc12_O2_mc
                    pc consts zetas) /\
               read RIP s = word(pc + 0xf0) /\
               read RCX s = word(l + 1) /\
               read R8 s =
               word_zx(word_sx(iword(EL (2 EXP (l + 1) - 1) mlk_zetas)
                               :int16):int32) /\
               read R12 s = a /\ read R14 s = word_add a (word 2) /\
               read R13 s = word zetas /\ read R15 s = word 1 /\
               read RSP s = word_add sbase (word 12) /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        r i))
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_invntt_tomont_gcc12_O2_mc
                    pc consts zetas) /\
               read RIP s = word(pc + 0x1c0) /\
               read R11 s = word(l + 1) /\
               read R12 s = a /\ read R14 s = word_add a (word 2) /\
               read R13 s = word zetas /\ read R15 s = word 1 /\
               read RSP s = word_add sbase (word 12) /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_blocks_c (l + 1) (2 EXP l) r i))
          (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                      RBX; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512); memory :> bytes(sbase,4)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) MP_TAC) THEN
  SPEC_TAC(`l:num`,`l:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
  (map INVNTT_LAYER_TAC (1--7)));;

(* ------------------------------------------------------------------------- *)
(* All the layers, after the scaling of the coefficients.                    *)
(* ------------------------------------------------------------------------- *)

(*** Assertions at the layer head and layer end for layer l ***)

let invntt_layerhead_tm,invntt_layerend_tm =
  let headtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
        read RCX s = word L /\
        read R8 s =
        word_zx(word_sx(iword(EL (2 EXP L - 1) mlk_zetas):int16):int32) /\
        read R12 s = a /\ read R14 s = word_add a (word 2) /\
        read R13 s = word zetas /\ read R15 s = word 1 /\
        read RSP s = word_add sbase (word 12) /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_layers_c (7 - L) x i)`
  and endtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
        read R11 s = word L /\
        read R12 s = a /\ read R14 s = word_add a (word 2) /\
        read R13 s = word zetas /\ read R15 s = word 1 /\
        read RSP s = word_add sbase (word 12) /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 invntt_layers_c (8 - L) x i)` in
  let mk tm l =
    let tm' = subst [mk_small_numeral l,`L:num`] tm in
    rhs(concl(NUM_REDUCE_CONV tm')) in
  (fun l -> mk headtm l),(fun l -> mk endtm l);;

(*** Apply the lemma for layer l at its head ***)

let INVNTT_LAYER_APPLY_TAC l =
  let th = SPECL [`a:int64`; `consts:num`; `zetas:num`; `pc:num`;
                  `sbase:int64`; mk_small_numeral(l - 1);
                  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`]
                     `invntt_layers_c (7 - L) x`)))]
                 MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYER in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral(7 - l),`n:num`]
          (SPEC_ALL(CONJUNCT2 invntt_layers_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN ENSURES_WEAKEN_TAC THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** Going from the end of layer l to the head of the next layer ***)

let INVNTT_LAYERBACK_TAC l =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mlk_zetas` (concl th)
    then MP_TAC(CONV_RULE NUM_REDUCE_CONV
                  (SPEC (mk_small_numeral(1 lsl (l - 1) - 1)) th))
    else failwith "") THEN
  REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYERS = prove
 (`!a consts zetas (x:num->int16) pc sbase.
    riprel32_within_bounds zetas (pc + 236) /\
    ALL (nonoverlapping (a,512))
        [(word pc,0x1e6); (word zetas,256); (sbase,4)] /\
    ALL (nonoverlapping (sbase,4)) [(word pc,0x1e6); (word zetas,256)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
           read RIP s = word(pc + 0xcf) /\
           read R12 s = a /\ read RSP s = word_add sbase (word 12) /\
           (!k. k < 128
                ==> read(memory :> bytes16(word_add (word zetas)
                                                    (word(2 * k)))) s =
                    iword(EL k mlk_zetas)) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read RIP s = word(pc + 0x1db) /\
           read RSP s = word_add sbase (word 12) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    invntt_layers_c 7 x i))
      (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                  RBX; RBP; R13; R14; R15] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512); memory :> bytes(sbase,4)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `consts:num`; `zetas:num`; `x:num->int16`; `pc:num`;
    `sbase:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Initialization, including the address of the table ***)

  ENSURES_SEQUENCE_TAC `pc + 0xf0` (invntt_layerhead_tm 7) THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--5) THEN
    MP_TAC(CONJUNCT1(SPECL [`pc:num`; `236`; `0`; `zetas:num`]
      RIP_REL_ADDR_FOLD)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (6--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[CONJUNCT1 invntt_layers_c] THEN
    REWRITE_TAC[mlk_zetas] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV);
    ALL_TAC] THEN

  (*** The layers, with the loop back to the head between them ***)

  MAP_EVERY (fun l ->
    ENSURES_SEQUENCE_TAC `pc + 0x1c0` (invntt_layerend_tm l) THEN
    CONJ_TAC THENL [INVNTT_LAYER_APPLY_TAC l; ALL_TAC] THEN
    if l = 1 then ALL_TAC else
    ENSURES_SEQUENCE_TAC `pc + 0xf0` (invntt_layerhead_tm (l - 1)) THEN
    CONJ_TAC THENL [INVNTT_LAYERBACK_TAC l; ALL_TAC]) (rev(1--7)) THEN

  (*** The exit after the last layer ***)

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The computation of the C code gives the inverse NTT, within the same      *)
(* bounds as the hand-written kernel. In fact all the coefficients stay      *)
(* below 3329 in absolute value, because of the reductions in every layer.   *)
(* ------------------------------------------------------------------------- *)

let INVNTT_BLOCKS_C_CLOSED = prove
 (`!l b r i.
     invntt_blocks_c l b r i =
     if i < 2 * 2 EXP (8 - l) * b
     then let z = iword(EL (2 EXP l - 1 - i DIV (2 * 2 EXP (8 - l)))
                           mlk_zetas) in
          if i MOD (2 * 2 EXP (8 - l)) < 2 EXP (8 - l)
          then barred(word_add (r i) (r(i + 2 EXP (8 - l))))
          else invntt_fqmul_c z (word_sub (r i) (r(i - 2 EXP (8 - l))))
     else r i`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[invntt_blocks_c; MULT_CLAUSES; CONJUNCT1 LT] THEN
  REWRITE_TAC[invntt_block_c] THEN
  SUBGOAL_THEN `1 <= 2 EXP (8 - l)` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `n = 2 EXP (8 - l)` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MULT_CLAUSES; LEFT_ADD_DISTRIB] THEN
  ASM_CASES_TAC `2 * n * b <= i /\ i < 2 * n * b + 2 * n` THENL
   [SUBGOAL_THEN `i DIV (2 * n) = b /\ i MOD (2 * n) = i - 2 * n * b`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 * n * b <= i /\ i < 2 * n * b + 2 * n
      ==> ~(i < 2 * n * b) /\ ~(i + n < 2 * n * b) /\
          i < 2 * n * b + 2 * n`] THEN
    ASM_CASES_TAC `i < 2 * n * b + n` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 * n * b <= i /\ i < 2 * n * b + n ==> i - 2 * n * b < n`;
     ARITH_RULE `~(i < 2 * n * b + n) ==> ~(i - 2 * n * b < n)`;
     ARITH_RULE `~(i < 2 * n * b + n) ==> ~(i - n < 2 * n * b)`] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE
     `~(p <= i /\ i < p + 2 * n)
      ==> ~(p <= i /\ i < p + n) /\ ~(p + n <= i /\ i < p + 2 * n)`] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let INVNTT_LAYERS_C_STEP = prove
 (`!n x i.
     n < 7 /\ i < 256
     ==> invntt_layers_c (SUC n) x i =
         let z = iword(EL (2 EXP (7 - n) - 1 -
                           i DIV (2 * 2 EXP (8 - (7 - n)))) mlk_zetas) in
         if i MOD (2 * 2 EXP (8 - (7 - n))) < 2 EXP (8 - (7 - n))
         then barred(word_add (invntt_layers_c n x i)
                        (invntt_layers_c n x (i + 2 EXP (8 - (7 - n)))))
         else invntt_fqmul_c z
                (word_sub (invntt_layers_c n x i)
                          (invntt_layers_c n x (i - 2 EXP (8 - (7 - n)))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[invntt_layers_c; INVNTT_BLOCKS_C_CLOSED] THEN
  SUBGOAL_THEN `2 * 2 EXP (8 - (7 - n)) * 2 EXP (6 - n) = 256`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 7 ==> 8 - (7 - n) + 6 - n = 7`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLK_ZETAS_ELS =
  map (fun k -> (REWRITE_CONV[mlk_zetas] THENC EL_CONV)
                 (mk_comb(mk_comb(`EL:num->int list->int`,mk_small_numeral k),
                          `mlk_zetas`))) (0--127);;

(*** The equation for coefficient i after layer n + 1, starting from the ***)
(*** scaled coefficients.                                                ***)

let INVNTT_LAYER_EQUATION =
  let conv =
    NUM_REDUCE_CONV THENC TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV(CONJUNCT1 invntt_layers_c :: invntt_scale_c ::
                 MLK_ZETAS_ELS) THENC
    ONCE_DEPTH_CONV WORD_IWORD_CONV THENC REWRITE_CONV[invntt_fqmul_c] THENC
    DEPTH_CONV WORD_RED_CONV in
  fun n i ->
    let th = SPECL [mk_small_numeral n; `invntt_scale_c x`;
                    mk_small_numeral i] INVNTT_LAYERS_C_STEP in
    let th' = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
    CONV_RULE(BINOP_CONV conv) th';;

(*** The congruences and bounds for all the layers, in order ***)

let INVNTT_LAYERS_CONGBOUND =
  MLKEM_NATIVE_LOCAL_CONGBOUND_RULE undefined
   (map (fun (n,i) -> SYM(INVNTT_LAYER_EQUATION n i))
        (List.concat (map (fun n -> map (fun i -> (n,i)) (0--255)) (0--6))));;

let INVNTT_FINAL_TAC =
  W(fun (asl,w) ->
    let tm = find_term
      (can (term_match [] `invntt_layers_c 7 (invntt_scale_c x) i`)) w in
    let th = apply INVNTT_LAYERS_CONGBOUND tm in
    if not(fst(dest_const(repeat rator w)) = "int_le") then
      MP_TAC(CONJUNCT1 th) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV INVERSE_NTT_CONV) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN INT_LINEAR_CONG_TAC
    else
      MP_TAC(CONJUNCT2 th) THEN INT_ARITH_TAC);;

let INVNTT_LAYERS_C_CORRECT = prove
 (`!x i. i < 256
         ==> (ival(invntt_layers_c 7 (invntt_scale_c x) i) ==
              inverse_ntt (ival o x) i) (mod &3329) /\
             abs(ival(invntt_layers_c 7 (invntt_scale_c x) i)) <= &26624`,
  GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  REPEAT CONJ_TAC THEN INVNTT_FINAL_TAC);;


(* ------------------------------------------------------------------------- *)
(* The scaling of the coefficients at the start, which also saves the        *)
(* callee-saved registers on the stack. The stack is described relative to  *)
(* the address sbase of the red-zone slot that the layers use later, with    *)
(* the return address at sbase + 60.                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE = prove
 (`!a consts zetas (x:num->int16) pc sbase w15 w14 w13 w12 wbp wbx.
    aligned 16 (word consts:int64) /\
    riprel32_within_bounds (consts + 32) (pc + 10) /\
    riprel32_within_bounds consts (pc + 30) /\
    riprel32_within_bounds (consts + 16) (pc + 40) /\
    ALL (nonoverlapping (a,512))
        [(word pc,0x1e6); (word consts,48); (word_add sbase (word 12),48)] /\
    ALL (nonoverlapping (word_add sbase (word 12),48))
        [(word pc,0x1e6); (word consts,48)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
           read RIP s = word pc /\
           read RDI s = a /\ read RSP s = word_add sbase (word 60) /\
           read R15 s = w15 /\ read R14 s = w14 /\ read R13 s = w13 /\
           read R12 s = w12 /\ read RBP s = wbp /\ read RBX s = wbx /\
           read(memory :> bytes128(word consts)) s =
           word 0xf301f301f301f301f301f301f301f301 /\
           read(memory :> bytes128(word(consts + 16))) s =
           word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
           read(memory :> bytes128(word(consts + 32))) s =
           word 0x05a105a105a105a105a105a105a105a1 /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read RIP s = word(pc + 0xcf) /\
           read R12 s = a /\ read RSP s = word_add sbase (word 12) /\
           read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
           read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
           read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
           read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
           read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
           read(memory :> bytes64(word_add sbase (word 12))) s = wbx /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    invntt_scale_c x i))
      (MAYCHANGE [RIP; RAX; RDX; RSP; R12] ,,
       MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512);
                  memory :> bytes(word_add sbase (word 12),48)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `consts:num`; `zetas:num`; `x:num->int16`; `pc:num`;
    `sbase:int64`; `w15:int64`; `w14:int64`; `w13:int64`; `w12:int64`;
    `wbp:int64`; `wbx:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x30` `pc + 0xc6`
   `\i s. read RAX s = word_add a (word(16 * i)) /\
          read RDX s = word_add a (word 512) /\
          read R12 s = a /\ read RSP s = word_add sbase (word 12) /\
          read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
          read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
          read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
          read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
          read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
          read(memory :> bytes64(word_add sbase (word 12))) s = wbx /\
          read XMM5 s = word 0x05a105a105a105a105a105a105a105a1 /\
          read XMM6 s = word 0xf301f301f301f301f301f301f301f301 /\
          read XMM4 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
          (!j. 8 * i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   invntt_scale_c x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, loading the constants and saving registers ***)

    RIPREL_FOLD_TAC `consts:num` `10` `-- &22:int` `32` THEN
    RIPREL_FOLD_TAC `consts:num` `30` `&30:int` `0` THEN
    RIPREL_FOLD_TAC `consts:num` `40` `&24:int` `16` THEN
    SUBGOAL_THEN `aligned 16 (word(consts + 16):int64) /\
                  aligned 16 (word(consts + 32):int64)` STRIP_ASSUME_TAC
    THENL
     [REWRITE_TAC[WORD_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[XMM4; XMM5; XMM6; READ_ZEROTOP_128] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[];

    (*** The loop body, for 8 coefficients loaded as one 128-bit word ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm7_init:int256` `read YMM7` THEN
    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    XMM_EXISTSTOP_TAC "top5" `YMM5` THEN
    XMM_EXISTSTOP_TAC "top6" `YMM6` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [MATCH_MP CHUNK8_INPUT_SPLIT (ASSUME `i < 32`)]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add a (word(16 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[]) (1--37) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
             concl)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[XMM4; XMM5; XMM6; READ_ZEROTOP_128] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
    REWRITE_TAC[CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    ASM_REWRITE_TAC[invntt_scale_c; INVNTT_LANE_FORM];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word (16 * i)))
                     (word_add a (word 512)):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y) = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 16 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `invntt_scale_c` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. Since the callee-saved registers are saved after the   *)
(* start, this is stated directly for the whole subroutine, with the scaling *)
(* and the layers as big steps. The proof works with the address sbase of    *)
(* the red-zone slot, 60 bytes below the stack pointer on entry.             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!a consts zetas x pc stackpointer returnaddress.
    aligned 16 (word consts:int64) /\
    riprel32_within_bounds (consts + 32) (pc + 10) /\
    riprel32_within_bounds consts (pc + 30) /\
    riprel32_within_bounds (consts + 16) (pc + 40) /\
    riprel32_within_bounds zetas (pc + 236) /\
    ALL (nonoverlapping (a,512))
        [(word pc,0x1e6); (word consts,48); (word zetas,256)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 60),68))
        [(word pc,0x1e6); (word consts,48); (word zetas,256); (a,512)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word consts)
             mlkem_native_poly_invntt_tomont_gcc12_O2_data /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 256
               ==> let zi =
                     read(memory :> bytes16(word_add a (word(2 * i)))) s in
                   (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                   abs(ival zi) <= &26624)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,512);
                  memory :> bytes(word_sub stackpointer (word 60),60)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `consts:num`; `zetas:num`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 60 THEN
  MAP_EVERY X_GEN_TAC [`sbase:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INVNTT_CONSTANTS_LOADED) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED) THEN

  (*** The scaling, which also saves the registers ***)

  MP_TAC(SPECL [`a:int64`; `consts:num`; `zetas:num`; `x:num->int16`;
                `pc:num`; `sbase:int64`; `r15_init:int64`; `r14_init:int64`;
                `r13_init:int64`; `r12_init:int64`; `rbp_init:int64`;
                `rbx_init:int64`]
         MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  X86_BIGSTEP_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC "s1" THEN

  (*** The layers ***)

  MP_TAC(SPECL [`a:int64`; `consts:num`; `zetas:num`; `invntt_scale_c x`;
                `pc:num`; `sbase:int64`]
         MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYERS) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  X86_BIGSTEP_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC "s2" THEN

  (*** Restoring the registers and returning ***)

  X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (3--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INVNTT_LAYERS_C_CORRECT]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This follows the structure of the  *)
(* correctness proof, with the events of a block and of each layer given by  *)
(* functions obtained from the corresponding lemmas. All the lemmas use the  *)
(* same regions as the whole subroutine, which also includes the stack.      *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** One block, from its setup through the inner loop ***)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_SAFE = prove
 (`exists f_ev_blk.
   forall e a consts zetas pc sbase start len k w11 rs
          retaddr w15 w14 w13 w12 wbp wbx.
     ALL (nonoverlapping (a,512)) [(word pc,0x1e6); (word zetas,256)] /\
     ALL (nonoverlapping (sbase,68))
         [(word pc,0x1e6); (word zetas,256); (a,512)] /\
     1 <= len /\ start + 2 * len <= 256 /\ 1 <= k /\ k < 256
     ==> ensures x86
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_invntt_tomont_gcc12_O2_mc
                    pc consts zetas) /\
               read RIP s = word(pc + 0x110) /\
               read RSI s = word start /\ read RDI s = word(start + len) /\
               read R10 s = word k /\ read RBX s = word(2 * len) /\
               read R12 s = a /\ read R14 s = word_add a (word 2) /\
               read R13 s = word zetas /\
               read R11 s = w11 /\ read R15 s = rs /\
               read RSP s = word_add sbase (word 12) /\
               read(memory :> bytes64(word_add sbase (word 60))) s = retaddr /\
               read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
               read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
               read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
               read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
               read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
               read(memory :> bytes64(word_add sbase (word 12))) s = wbx /\
               read events s = e)
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_invntt_tomont_gcc12_O2_mc
                    pc consts zetas) /\
               read RIP s = word(pc + 0x19d) /\
               read RSI s = word start /\ read RDI s = word(start + len) /\
               read R10 s = word(k - 1) /\ read RBX s = word(2 * len) /\
               read R12 s = a /\ read R14 s = word_add a (word 2) /\
               read R13 s = word zetas /\
               read R11 s = w11 /\ read R15 s = rs /\
               read RSP s = word_add sbase (word 12) /\
               read(memory :> bytes64(word_add sbase (word 60))) s = retaddr /\
               read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
               read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
               read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
               read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
               read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
               read(memory :> bytes64(word_add sbase (word 12))) s = wbx /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a consts zetas pc sbase start len /\
                 memaccess_inbounds e2
                  [a,512; word consts,48; word zetas,256; sbase,68]
                  [a,512; sbase,60])
          (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; R9; R10; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512); memory :> bytes(sbase,4)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (consts:num) (zetas:num) (pc:num) (sbase:int64) (start:num)
     (len:num).
      APPEND (f_ev_blkend a consts zetas pc sbase start len)
        (APPEND (ENUMERATEL len
                   (\j. f_ev_bfly a consts zetas pc sbase start len j))
                (f_ev_blkhead a consts zetas pc sbase start len))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + 0x140` `pc + 0x199`
   `\j s. read RCX s = word_add a (word(2 * (start + j))) /\
          read RDX s = word_add a (word(2 * (start + len + j))) /\
          read RSI s = word_add a (word(2 * (start + len))) /\
          read RDI s = word(start + len) /\
          read R10 s = word(k - 1) /\ read RBX s = word(2 * len) /\
          read R12 s = a /\ read R14 s = word_add a (word 2) /\
          read R13 s = word zetas /\
          read R11 s = w11 /\ read R15 s = rs /\
          read RSP s = word_add sbase (word 12) /\
          read(memory :> bytes64(word_add sbase (word 60))) s = retaddr /\
          read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
          read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
          read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
          read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
          read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
          read(memory :> bytes64(word_add sbase (word 12))) s = wbx /\
          read (memory :> bytes32 sbase) s = word start` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Setting up the pointers for the inner loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (3--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The inner loop body, one butterfly, and the loop test ***)

    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--22) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_add a (word x)) (word y):int64 =
      word_add a (word(x + y))`]) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (23--23) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (24--24) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(2 * (start + j) + 2 = 2 * (start + len)) <=> j + 1 < len`
     SUBST_ALL_TAC THENL
     [UNDISCH_TAC `j < len` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The end of the block, restoring RSI ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let INVNTT_GCC12_O2_BLOCK_EVENTS =
  new_specification ["x86_invntt_gcc12_O2_block_events"]
                    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_SAFE;;

(*** One layer, for each of the seven layers ***)

let lsafe_goal l =
  let tm =
  `exists f_ev_lay.
    forall e a consts zetas pc sbase retaddr w15 w14 w13 w12 wbp wbx.
     ALL (nonoverlapping (a,512)) [(word pc,0x1e6); (word zetas,256)] /\
     ALL (nonoverlapping (sbase,68))
         [(word pc,0x1e6); (word zetas,256); (a,512)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_invntt_tomont_gcc12_O2_mc
                    pc consts zetas) /\
               read RIP s = word(pc + 0xf0) /\
               read RCX s = word L /\
               read R12 s = a /\ read R14 s = word_add a (word 2) /\
               read R13 s = word zetas /\ read R15 s = word 1 /\
               read RSP s = word_add sbase (word 12) /\
               read(memory :> bytes64(word_add sbase (word 60))) s = retaddr /\
               read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
               read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
               read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
               read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
               read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
               read(memory :> bytes64(word_add sbase (word 12))) s = wbx /\
               read events s = e)
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_invntt_tomont_gcc12_O2_mc
                    pc consts zetas) /\
               read RIP s = word(pc + 0x1c0) /\
               read R11 s = word L /\
               read R12 s = a /\ read R14 s = word_add a (word 2) /\
               read R13 s = word zetas /\ read R15 s = word 1 /\
               read RSP s = word_add sbase (word 12) /\
               read(memory :> bytes64(word_add sbase (word 60))) s = retaddr /\
               read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
               read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
               read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
               read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
               read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
               read(memory :> bytes64(word_add sbase (word 12))) s = wbx /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_lay a consts zetas pc sbase /\
                 memaccess_inbounds e2
                  [a,512; word consts,48; word zetas,256; sbase,68]
                  [a,512; sbase,60])
          (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11;
                      RBX; RBP] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512); memory :> bytes(sbase,4)])` in
  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm)));;

(*** The event template for layer l ***)

let lsafe_template l =
  let len = mk_small_numeral(1 lsl (8 - l)) in
  if l = 1 then
   subst [len,`LEN:num`]
   `\(a:int64) (consts:num) (zetas:num) (pc:num) (sbase:int64).
      APPEND (f_ev_ltest0 a consts zetas pc sbase)
       (APPEND (x86_invntt_gcc12_O2_block_events a consts zetas pc sbase
                  0 LEN)
               (f_ev_lhead a consts zetas pc sbase))
     :(uarch_event)list`
  else
   subst [len,`LEN:num`; mk_small_numeral(1 lsl (l - 1) - 1),`K:num`]
   `\(a:int64) (consts:num) (zetas:num) (pc:num) (sbase:int64).
      APPEND (f_ev_lexit a consts zetas pc sbase)
       (APPEND
         (ENUMERATEL K
           (\i. APPEND (f_ev_ltest a consts zetas pc sbase i)
                 (APPEND (x86_invntt_gcc12_O2_block_events a consts zetas pc
                            sbase (2 * LEN * (i + 1)) LEN)
                         (f_ev_lzeta a consts zetas pc sbase i))))
         (APPEND (f_ev_ltest0 a consts zetas pc sbase)
           (APPEND (x86_invntt_gcc12_O2_block_events a consts zetas pc
                      sbase 0 LEN)
                   (f_ev_lhead a consts zetas pc sbase))))
     :(uarch_event)list`;;

(*** The block lemma for block b of layer l ***)

let invntt_block_events_inst l b ev =
  let red t = rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (8 - l)),`LEN:num`;
      b,`B:num`] t))) in
  SPECL [ev; `a:int64`; `consts:num`; `zetas:num`; `pc:num`;
         `sbase:int64`; red `2 * LEN * B`; red `LEN:num`;
         red `2 EXP L - 1 - B`; red `word L:int64`; `word 1:int64`;
         `retaddr:int64`; `w15:int64`; `w14:int64`; `w13:int64`;
         `w12:int64`; `wbp:int64`; `wbx:int64`]
        INVNTT_GCC12_O2_BLOCK_EVENTS;;

(*** Register state at the head of block b, which is also the state after
 *** the test at the end of the previous block when it continues
 ***)

let lsafe_blockhead_tm =
  let headtm =
   `\s. bytes_loaded s (word pc)
          (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
        read RSI s = word(2 * LEN * B) /\
        read RDI s = word(2 * LEN * B + LEN) /\
        read R10 s = word(2 EXP L - 1 - B) /\ read RBX s = word(2 * LEN) /\
        read R12 s = a /\ read R14 s = word_add a (word 2) /\
        read R13 s = word zetas /\
        read R11 s = word L /\ read R15 s = word 1 /\
        read RSP s = word_add sbase (word 12) /\
        read(memory :> bytes64(word_add sbase (word 60))) s = retaddr /\
        read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
        read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
        read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
        read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
        read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
        read(memory :> bytes64(word_add sbase (word 12))) s = wbx` in
  fun l b ->
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (8 - l)),`LEN:num`;
      b,`B:num`] headtm)));;

(*** Simulation of a short piece of straight-line code with flags, where
 *** a final conditional branch may depend on whether i + 1 < k, with the
 *** zero extension of 32-bit results simplified for an index
 ***)

let LSAFE_SIM_TAC k pre_tac n =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN pre_tac THEN
  MAP_EVERY (fun i ->
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC [i] THEN
    TRY W32_DECIDE_FLAGS_TAC THEN TRY W64_ZX_SMALL_TAC) (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  (fun (asl,w) ->
     match find_terms is_cond w with
       [] -> ALL_TAC (asl,w)
     | tms ->
         let c = rand(rator(rator(hd(sort (fun a b -> free_in b a) tms)))) in
         let p = subst [k,`K:num`] `i + 1 < K` in
         if c = p then ALL_TAC (asl,w) else
         ((SUBGOAL_THEN (mk_eq(c,p))
            SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
          (SUBGOAL_THEN (mk_eq(c,mk_neg p))
            SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC])) (asl,w)) THEN
  REWRITE_TAC[ARITH_RULE `!n i. n - i - 1 = n - (i + 1)`] THEN
  REPEAT(CONJ_TAC THENL
   [REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    (WORD_SMALL_TAC ORELSE SIMPLE_ARITH_TAC ORELSE
     (AP_TERM_TAC THEN SIMPLE_ARITH_TAC));
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The whole safety proof for layer l ***)

let INVNTT_LAYER_SAFE_TAC l =
  let k = mk_small_numeral(1 lsl (l - 1) - 1) in
  let idx = rhs(concl(NUM_REDUCE_CONV
   (subst [mk_small_numeral l,`L:num`] `2 EXP L - 1 - (i + 1)`))) in
  let blk0_tac =
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x19d`
     (rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`;
        mk_small_numeral(1 lsl (8 - l)),`LEN:num`]
       `\s. bytes_loaded s (word pc)
              (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
            read RSI s = word 0 /\ read RDI s = word LEN /\
            read R10 s = word(2 EXP L - 1 - 1) /\
            read RBX s = word(2 * LEN) /\
            read R12 s = a /\ read R14 s = word_add a (word 2) /\
            read R13 s = word zetas /\
            read R11 s = word L /\ read R15 s = word 1 /\
            read RSP s = word_add sbase (word 12) /\
            read(memory :> bytes64(word_add sbase (word 60))) s = retaddr /\
            read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
            read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
            read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
            read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
            read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
            read(memory :> bytes64(word_add sbase (word 12))) s = wbx`)))) THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x110` (lsafe_blockhead_tm l `0`) THEN
      CONJ_TAC THENL
       [LSAFE_SIM_TAC k ALL_TAC 9;
        EVENTS_LEMMA_TAC (invntt_block_events_inst l `0`)];
      LSAFE_SIM_TAC k ALL_TAC 4] in
  CONCRETIZE_F_EVENTS_TAC (lsafe_template l) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  if l = 1 then blk0_tac else
  ENSURES_EVENTS_WHILE_UP2_TAC k `pc + 0x1a9` `pc + 0x1c0`
   (mk_abs(`i:num`,lsafe_blockhead_tm l `i + 1`)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC[ENUMERATEL; APPEND] THEN CONV_TAC NUM_REDUCE_CONV THEN
    blk0_tac;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x19d`
     (rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`;
        mk_small_numeral(1 lsl (8 - l)),`LEN:num`]
       `\s. bytes_loaded s (word pc)
              (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
            read RSI s = word(2 * LEN * (i + 1)) /\
            read RDI s = word(2 * LEN * (i + 1) + LEN) /\
            read R10 s = word(2 EXP L - 1 - (i + 1) - 1) /\
            read RBX s = word(2 * LEN) /\
            read R12 s = a /\ read R14 s = word_add a (word 2) /\
            read R13 s = word zetas /\
            read R11 s = word L /\ read R15 s = word 1 /\
            read RSP s = word_add sbase (word 12) /\
            read(memory :> bytes64(word_add sbase (word 60))) s = retaddr /\
            read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
            read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
            read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
            read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
            read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
            read(memory :> bytes64(word_add sbase (word 12))) s = wbx`)))) THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x110`
        (lsafe_blockhead_tm l `i + 1`) THEN
      CONJ_TAC THENL
       [LSAFE_SIM_TAC k (VAL_INT64_TAC idx) 3;
        EVENTS_LEMMA_TAC (invntt_block_events_inst l `i + 1`)];
      LSAFE_SIM_TAC k ALL_TAC 4];
    LSAFE_SIM_TAC k ALL_TAC 0];;

let INVNTT_GCC12_O2_LAYER_EVENTS =
  map (fun l ->
        new_specification
         ["x86_invntt_gcc12_O2_layer_events_" ^ string_of_int l]
         (prove(lsafe_goal l,INVNTT_LAYER_SAFE_TAC l)))
      (1--7);;

(*** The scaling at the start, including saving the registers ***)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE_SAFE = prove
 (`exists f_ev_scale.
    forall e a consts zetas pc sbase w15 w14 w13 w12 wbp wbx retaddr.
     aligned 16 (word consts:int64) /\
     riprel32_within_bounds (consts + 32) (pc + 10) /\
     riprel32_within_bounds consts (pc + 30) /\
     riprel32_within_bounds (consts + 16) (pc + 40) /\
     ALL (nonoverlapping (a,512)) [(word pc,0x1e6); (word consts,48)] /\
     ALL (nonoverlapping (sbase,68))
         [(word pc,0x1e6); (word consts,48); (a,512)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_invntt_tomont_gcc12_O2_mc
                    pc consts zetas) /\
               read RIP s = word pc /\
               read RDI s = a /\ read RSP s = word_add sbase (word 60) /\
               read R15 s = w15 /\ read R14 s = w14 /\ read R13 s = w13 /\
               read R12 s = w12 /\ read RBP s = wbp /\ read RBX s = wbx /\
               read(memory :> bytes64(word_add sbase (word 60))) s =
               retaddr /\
               read events s = e)
          (\s. bytes_loaded s (word pc)
                 (mlkem_native_poly_invntt_tomont_gcc12_O2_mc
                    pc consts zetas) /\
               read RIP s = word(pc + 0xcf) /\
               read R12 s = a /\ read RSP s = word_add sbase (word 12) /\
               read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
               read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
               read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
               read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
               read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
               read(memory :> bytes64(word_add sbase (word 12))) s = wbx /\
               read(memory :> bytes64(word_add sbase (word 60))) s =
               retaddr /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_scale a consts zetas pc sbase /\
                 memaccess_inbounds e2
                  [a,512; word consts,48; word zetas,256; sbase,68]
                  [a,512; sbase,60])
          (MAYCHANGE [RIP; RAX; RDX; RSP; R12] ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512);
                      memory :> bytes(word_add sbase (word 12),48)])`,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (consts:num) (zetas:num) (pc:num) (sbase:int64).
      APPEND (f_ev_sexit a consts zetas pc sbase)
        (APPEND (ENUMERATEL 32 (\i. f_ev_sloop a consts zetas pc sbase i))
                (f_ev_sprol a consts zetas pc sbase))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  RIPREL_FOLD_TAC `consts:num` `10` `-- &22:int` `32` THEN
  RIPREL_FOLD_TAC `consts:num` `30` `&30:int` `0` THEN
  RIPREL_FOLD_TAC `consts:num` `40` `&24:int` `16` THEN
  SUBGOAL_THEN `aligned 16 (word(consts + 16):int64) /\
                aligned 16 (word(consts + 32):int64)` STRIP_ASSUME_TAC
  THENL
   [REWRITE_TAC[WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x30` `pc + 0xcf`
   `\i s. read RAX s = word_add a (word(16 * i)) /\
          read RDX s = word_add a (word 512) /\
          read R12 s = a /\ read RSP s = word_add sbase (word 12) /\
          read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
          read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
          read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
          read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
          read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
          read(memory :> bytes64(word_add sbase (word 12))) s = wbx /\
          read(memory :> bytes64(word_add sbase (word 60))) s = retaddr` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    LSAFE_SIM_TAC `1` ALL_TAC 0] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--39) THEN
  SUBGOAL_THEN
   `~(val (word_add (word_add a (word (16 * i))) (word 16):int64) =
      val (word_add a (word 512):int64)) <=> i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 16 * i + 16 < 2 EXP 64`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let INVNTT_GCC12_O2_SCALE_EVENTS =
  new_specification ["x86_invntt_gcc12_O2_scale_events"]
                    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE_SAFE;;

(*** The whole code, which has the same signature as mlkem_intt, with ***)
(*** the vectors of constants and table of zetas as read-only objects ***)

let invntt_top_template =
  let lay l = list_mk_comb
   (mk_const("x86_invntt_gcc12_O2_layer_events_" ^ string_of_int l,[]),
    [`a:int64`;`consts:num`;`zetas:num`;`pc:num`;`sbase:int64`])
  and scale = `x86_invntt_gcc12_O2_scale_events a consts zetas pc sbase`
  and fev n =
    list_mk_comb
     (mk_var(n,`:int64->num->num->num->int64->int64->(uarch_event)list`),
      [`a:int64`;`consts:num`;`zetas:num`;`pc:num`;`sbase:int64`;
       `returnaddress:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain l acc =
    let acc' = app (lay l) acc in
    if l = 1 then acc' else
    chain (l - 1) (app (fev ("f_ev_back" ^ string_of_int l)) acc') in
  let body = app (fev "f_ev_fin") (chain 7 (app (fev "f_ev_init") scale)) in
  list_mk_abs([`a:int64`;`consts:num`;`zetas:num`;`pc:num`;`sbase:int64`;
               `returnaddress:int64`],body);;

let invntt_safe_layerhead_tm,invntt_safe_layerend_tm,invntt_safe_scaleend_tm =
  let saved =
   `read(memory :> bytes64(word_add sbase (word 60))) s = returnaddress /\
    read(memory :> bytes64(word_add sbase (word 52))) s = r15_init /\
    read(memory :> bytes64(word_add sbase (word 44))) s = r14_init /\
    read(memory :> bytes64(word_add sbase (word 36))) s = r13_init /\
    read(memory :> bytes64(word_add sbase (word 28))) s = r12_init /\
    read(memory :> bytes64(word_add sbase (word 20))) s = rbp_init /\
    read(memory :> bytes64(word_add sbase (word 12))) s = rbx_init` in
  let headtm = mk_abs(`s:x86state`,mk_conj
   (`bytes_loaded s (word pc)
       (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
     read RCX s = word L /\
     read R12 s = a /\ read R14 s = word_add a (word 2) /\
     read R13 s = word zetas /\ read R15 s = word 1 /\
     read RSP s = word_add sbase (word 12)`,saved))
  and endtm = mk_abs(`s:x86state`,mk_conj
   (`bytes_loaded s (word pc)
       (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
     read R11 s = word L /\
     read R12 s = a /\ read R14 s = word_add a (word 2) /\
     read R13 s = word zetas /\ read R15 s = word 1 /\
     read RSP s = word_add sbase (word 12)`,saved))
  and stm = mk_abs(`s:x86state`,mk_conj
   (`bytes_loaded s (word pc)
       (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
     read R12 s = a /\ read RSP s = word_add sbase (word 12)`,saved)) in
  let mk tm l =
    rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm))) in
  (fun l -> mk headtm l),(fun l -> mk endtm l),stm;;

let invntt_layer_events_inst l ev =
  SPECL [ev; `a:int64`; `consts:num`; `zetas:num`; `pc:num`; `sbase:int64`;
         `returnaddress:int64`; `r15_init:int64`; `r14_init:int64`;
         `r13_init:int64`; `r12_init:int64`; `rbp_init:int64`;
         `rbx_init:int64`]
        (el (l - 1) INVNTT_GCC12_O2_LAYER_EVENTS);;

let INVNTT_SAFE_TOP_TAC =
  CONCRETIZE_F_EVENTS_TAC invntt_top_template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `consts:num`; `zetas:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 60 THEN
  MAP_EVERY X_GEN_TAC [`sbase:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)] THEN

  (*** Restoring the registers and returning after the last layer ***)

  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x1c0` (invntt_safe_layerend_tm 1) THEN
  CONJ_TAC THENL [ALL_TAC; LSAFE_SIM_TAC `1` ALL_TAC 10] THEN

  (*** The layers, with the code between them ***)

  MAP_EVERY (fun l ->
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xf0` (invntt_safe_layerhead_tm l) THEN
    CONJ_TAC THENL
     [ALL_TAC; EVENTS_LEMMA_TAC (invntt_layer_events_inst l)] THEN
    if l = 7 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x1c0`
      (invntt_safe_layerend_tm (l + 1)) THEN
    CONJ_TAC THENL [ALL_TAC; LSAFE_SIM_TAC `1` ALL_TAC 8]) (1--7) THEN

  (*** The scaling, and the setup for the first layer ***)

  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xcf` invntt_safe_scaleend_tm THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`e:(uarch_event)list`; `a:int64`; `consts:num`;
                  `zetas:num`; `pc:num`; `sbase:int64`;
                  `r15_init:int64`; `r14_init:int64`; `r13_init:int64`;
                  `r12_init:int64`; `rbp_init:int64`; `rbx_init:int64`;
                  `returnaddress:int64`]
                 INVNTT_GCC12_O2_SCALE_EVENTS) THEN
    ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
    DISCH_THEN ENSURES_WEAKEN_TAC THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      SUBSUMED_MAYCHANGE_TAC];
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--5) THEN
    MP_TAC(CONJUNCT1(SPECL [`pc:num`; `236`; `0`; `zetas:num`]
      RIP_REL_ADDR_FOLD)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (6--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** The specification is that of mk_safety_spec for the C signature of
 *** mlkem_intt with the vectors of constants and the table of zetas as
 *** read-only objects
 ***)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e a consts zetas pc stackpointer returnaddress.
       aligned 16 (word consts:int64) /\
       riprel32_within_bounds (consts + 32) (pc + 10) /\
       riprel32_within_bounds consts (pc + 30) /\
       riprel32_within_bounds (consts + 16) (pc + 40) /\
       riprel32_within_bounds zetas (pc + 236) /\
       ALL (nonoverlapping (a,512))
           [word pc,0x1e6; word consts,48; word zetas,256] /\
       ALL (nonoverlapping (word_sub stackpointer (word 60),68))
           [word pc,0x1e6; word consts,48; word zetas,256; a,512]
       ==> ensures x86
           (\s. bytes_loaded s (word pc)
                  (mlkem_native_poly_invntt_tomont_gcc12_O2_mc
                     pc consts zetas) /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                bytes_loaded s (word consts)
                  mlkem_native_poly_invntt_tomont_gcc12_O2_data /\
                bytes_loaded s (word zetas) mlk_zetas_data /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a consts zetas pc
                         (word_sub stackpointer (word 60)) returnaddress /\
                  memaccess_inbounds e2
                   [a,512; word consts,48; word zetas,256;
                    word_sub stackpointer (word 60),68]
                   [a,512; word_sub stackpointer (word 60),60])
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 60),60)])`,
  INVNTT_SAFE_TOP_TAC);;
