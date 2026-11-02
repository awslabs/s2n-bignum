(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation.                                                 *)
(* This is the code for mlkem_keccakf1600_permute from mlkem-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). Unlike the hand-written kernels, it reads its    *)
(* own table of round constants from the read-only data rather than taking   *)
(* it as an argument, and it does two rounds in each iteration of its loop.  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/keccak_spec.ml";;

(**** print_literal_relocs_from_elf
        "x86/mlkem_native/mlkem_native_keccakf1600_permute_gcc12_O2.o";;
 ****)

let mlkem_native_keccakf1600_permute_gcc12_O2_mc,
    mlkem_native_keccakf1600_permute_gcc12_O2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "WHOLE_READONLY" | "mlk_KeccakF_RoundConstants" ->
          "mlkem_native_keccakf1600_permute_gcc12_O2_data"
      | s -> failwith ("unknown symbol: " ^ s))
    "mlkem_native_keccakf1600_permute_gcc12_O2_mc"
    "x86/mlkem_native/mlkem_native_keccakf1600_permute_gcc12_O2.o"
(fun b ADDR -> [b[
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x48; 0x83; 0xec; 0x58;  (* SUB (% rsp) (Imm8 (word 88)) *)
  0x48; 0x8b; 0x57; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rdi,8))) *)
  0x4c; 0x8b; 0x6f; 0x18;  (* MOV (% r13) (Memop Quadword (%% (rdi,24))) *)
  0x4c; 0x8b; 0x3f;        (* MOV (% r15) (Memop Quadword (%% (rdi,0))) *)
  0x4c; 0x8b; 0x67; 0x60;  (* MOV (% r12) (Memop Quadword (%% (rdi,96))) *)
  0x48; 0x89; 0x54; 0x24; 0x90;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551504))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x10;  (* MOV (% rdx) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x89; 0x54; 0x24; 0x98;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551512))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x20;  (* MOV (% rdx) (Memop Quadword (%% (rdi,32))) *)
  0x48; 0x89; 0x54; 0x24; 0xa0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551520))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x28;  (* MOV (% rdx) (Memop Quadword (%% (rdi,40))) *)
  0x48; 0x89; 0x54; 0x24; 0xa8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551528))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x30;  (* MOV (% rdx) (Memop Quadword (%% (rdi,48))) *)
  0x48; 0x89; 0x54; 0x24; 0xb0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551536))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x38;  (* MOV (% rdx) (Memop Quadword (%% (rdi,56))) *)
  0x48; 0x89; 0x54; 0x24; 0xb8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551544))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x40;  (* MOV (% rdx) (Memop Quadword (%% (rdi,64))) *)
  0x48; 0x89; 0x54; 0x24; 0xc0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551552))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x48;  (* MOV (% rdx) (Memop Quadword (%% (rdi,72))) *)
  0x48; 0x89; 0x54; 0x24; 0xc8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551560))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x50;  (* MOV (% rdx) (Memop Quadword (%% (rdi,80))) *)
  0x48; 0x89; 0x54; 0x24; 0xd0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551568))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x58;  (* MOV (% rdx) (Memop Quadword (%% (rdi,88))) *)
  0x48; 0x89; 0x54; 0x24; 0xd8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551576))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x68;  (* MOV (% rdx) (Memop Quadword (%% (rdi,104))) *)
  0x48; 0x89; 0x54; 0x24; 0xe0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551584))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x70;  (* MOV (% rdx) (Memop Quadword (%% (rdi,112))) *)
  0x4c; 0x89; 0x6c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r13) *)
  0x4c; 0x8b; 0x98; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rax,144))) *)
  0x48; 0x89; 0x54; 0x24; 0xe8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551592))) (% rdx) *)
  0x48; 0x8b; 0x57; 0x78;  (* MOV (% rdx) (Memop Quadword (%% (rdi,120))) *)
  0x48; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rax) *)
  0x48; 0x8b; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rdi,128))) *)
  0x48; 0x89; 0x54; 0x24; 0xf0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551600))) (% rdx) *)
  0x48; 0x8b; 0x90; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rax,136))) *)
  0x4c; 0x8b; 0xb0; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r14) (Memop Quadword (%% (rax,160))) *)
  0x4c; 0x8b; 0x80; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rax,176))) *)
  0x48; 0x89; 0x54; 0x24; 0xf8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551608))) (% rdx) *)
  0x48; 0x8b; 0x90; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rax,152))) *)
  0x48; 0x8b; 0x98; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rax,192))) *)
  0x48; 0x89; 0x14; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rdx) *)
  0x48; 0x8b; 0x90; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rax,168))) *)
  0x48; 0x89; 0x54; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rdx) *)
  0x48; 0x8b; 0x90; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rax,184))) *)
  0x48; 0x89; 0x54; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rdx) *)
  0x48; 0x8d; 0x15];
  ADDR ("mlkem_native_keccakf1600_permute_gcc12_O2_data",(-4)); b[
                           (* LEA (% rdx) (Riprel (word_sx (iword
                               (&mlkem_native_keccakf1600_permute_gcc12_O2_data
                               - (&pc + &244))))) *)
  0x48; 0x89; 0x54; 0x24; 0x88;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551496))) (% rdx) *)
  0x0f; 0x1f; 0x80; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x48; 0x8b; 0x4c; 0x24; 0xa8;
                           (* MOV (% rcx) (Memop Quadword (%%
                                  (rsp,18446744073709551528))) *)
  0x48; 0x8b; 0x44; 0x24; 0xd0;
                           (* MOV (% rax) (Memop Quadword (%%
                                  (rsp,18446744073709551568))) *)
  0x48; 0x8b; 0x74; 0x24; 0xf0;
                           (* MOV (% rsi) (Memop Quadword (%%
                                  (rsp,18446744073709551600))) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x90;
                           (* MOV (% r13) (Memop Quadword (%%
                                  (rsp,18446744073709551504))) *)
  0x4c; 0x31; 0xf9;        (* XOR (% rcx) (% r15) *)
  0x48; 0x8b; 0x54; 0x24; 0xd8;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551576))) *)
  0x48; 0x8b; 0x6c; 0x24; 0x08;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0x31; 0xc1;        (* XOR (% rcx) (% rax) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x18;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x8b; 0x54; 0x24; 0x98;
                           (* MOV (% r10) (Memop Quadword (%%
                                  (rsp,18446744073709551512))) *)
  0x48; 0x31; 0xf1;        (* XOR (% rcx) (% rsi) *)
  0x48; 0x8b; 0x74; 0x24; 0xb0;
                           (* MOV (% rsi) (Memop Quadword (%%
                                  (rsp,18446744073709551536))) *)
  0x48; 0x8b; 0x44; 0x24; 0xf8;
                           (* MOV (% rax) (Memop Quadword (%%
                                  (rsp,18446744073709551608))) *)
  0x4c; 0x31; 0xf1;        (* XOR (% rcx) (% r14) *)
  0x49; 0x31; 0xf5;        (* XOR (% r13) (% rsi) *)
  0x48; 0x8b; 0x74; 0x24; 0xe0;
                           (* MOV (% rsi) (Memop Quadword (%%
                                  (rsp,18446744073709551584))) *)
  0x49; 0x31; 0xd5;        (* XOR (% r13) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xc0;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551552))) *)
  0x49; 0x31; 0xfd;        (* XOR (% r13) (% rdi) *)
  0x49; 0x31; 0xed;        (* XOR (% r13) (% rbp) *)
  0x49; 0x31; 0xd1;        (* XOR (% r9) (% rdx) *)
  0x48; 0x8b; 0x6c; 0x24; 0xb8;
                           (* MOV (% rbp) (Memop Quadword (%%
                                  (rsp,18446744073709551544))) *)
  0x48; 0x8b; 0x54; 0x24; 0x10;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,16))) *)
  0x49; 0x31; 0xf1;        (* XOR (% r9) (% rsi) *)
  0x49; 0x31; 0xea;        (* XOR (% r10) (% rbp) *)
  0x4d; 0x31; 0xd9;        (* XOR (% r9) (% r11) *)
  0x48; 0x8b; 0x6c; 0x24; 0xc8;
                           (* MOV (% rbp) (Memop Quadword (%%
                                  (rsp,18446744073709551560))) *)
  0x49; 0x31; 0xd1;        (* XOR (% r9) (% rdx) *)
  0x4d; 0x31; 0xe2;        (* XOR (% r10) (% r12) *)
  0x48; 0x8b; 0x54; 0x24; 0xa0;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551520))) *)
  0x49; 0x31; 0xc2;        (* XOR (% r10) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0xe8;
                           (* MOV (% rax) (Memop Quadword (%%
                                  (rsp,18446744073709551592))) *)
  0x48; 0x31; 0xea;        (* XOR (% rdx) (% rbp) *)
  0x4c; 0x89; 0xed;        (* MOV (% rbp) (% r13) *)
  0x4d; 0x31; 0xc2;        (* XOR (% r10) (% r8) *)
  0x48; 0x31; 0xc2;        (* XOR (% rdx) (% rax) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xd1; 0xc5;        (* ROL (% rbp) (Imm8 (word 1)) *)
  0x4c; 0x89; 0xd6;        (* MOV (% rsi) (% r10) *)
  0x48; 0xd1; 0xc6;        (* ROL (% rsi) (Imm8 (word 1)) *)
  0x48; 0x31; 0xc2;        (* XOR (% rdx) (% rax) *)
  0x48; 0x31; 0xce;        (* XOR (% rsi) (% rcx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x48; 0xd1; 0xc1;        (* ROL (% rcx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xda;        (* XOR (% rdx) (% rbx) *)
  0x48; 0xd1; 0xc0;        (* ROL (% rax) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc9;        (* XOR (% rcx) (% r9) *)
  0x48; 0x31; 0xd5;        (* XOR (% rbp) (% rdx) *)
  0x48; 0xd1; 0xc2;        (* ROL (% rdx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x4c; 0x31; 0xd2;        (* XOR (% rdx) (% r10) *)
  0x4c; 0x8b; 0x54; 0x24; 0xb0;
                           (* MOV (% r10) (Memop Quadword (%%
                                  (rsp,18446744073709551536))) *)
  0x49; 0x31; 0xef;        (* XOR (% r15) (% rbp) *)
  0x4d; 0x89; 0xf9;        (* MOV (% r9) (% r15) *)
  0x49; 0x31; 0xf2;        (* XOR (% r10) (% rsi) *)
  0x49; 0xc1; 0xca; 0x14;  (* ROR (% r10) (Imm8 (word 20)) *)
  0x49; 0x31; 0xc4;        (* XOR (% r12) (% rax) *)
  0x49; 0x31; 0xd3;        (* XOR (% r11) (% rdx) *)
  0x48; 0x31; 0xcb;        (* XOR (% rbx) (% rcx) *)
  0x4d; 0x89; 0xd7;        (* MOV (% r15) (% r10) *)
  0x49; 0xc1; 0xcc; 0x15;  (* ROR (% r12) (Imm8 (word 21)) *)
  0x48; 0x31; 0xf7;        (* XOR (% rdi) (% rsi) *)
  0x49; 0x31; 0xc0;        (* XOR (% r8) (% rax) *)
  0x49; 0xc1; 0xc3; 0x15;  (* ROL (% r11) (Imm8 (word 21)) *)
  0x49; 0xf7; 0xd7;        (* NOT (% r15) *)
  0x48; 0xc1; 0xc3; 0x0e;  (* ROL (% rbx) (Imm8 (word 14)) *)
  0x48; 0xc1; 0xcf; 0x13;  (* ROR (% rdi) (Imm8 (word 19)) *)
  0x4d; 0x89; 0xfd;        (* MOV (% r13) (% r15) *)
  0x4c; 0x8b; 0x7c; 0x24; 0x88;
                           (* MOV (% r15) (Memop Quadword (%%
                                  (rsp,18446744073709551496))) *)
  0x49; 0xc1; 0xc8; 0x03;  (* ROR (% r8) (Imm8 (word 3)) *)
  0x4d; 0x21; 0xe5;        (* AND (% r13) (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0xb0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551536))) (% r13) *)
  0x4d; 0x8b; 0x2f;        (* MOV (% r13) (Memop Quadword (%% (r15,0))) *)
  0x4d; 0x31; 0xcd;        (* XOR (% r13) (% r9) *)
  0x4d; 0x89; 0xef;        (* MOV (% r15) (% r13) *)
  0x4c; 0x8b; 0x6c; 0x24; 0xb0;
                           (* MOV (% r13) (Memop Quadword (%%
                                  (rsp,18446744073709551536))) *)
  0x4d; 0x31; 0xef;        (* XOR (% r15) (% r13) *)
  0x4d; 0x89; 0xe5;        (* MOV (% r13) (% r12) *)
  0x49; 0xf7; 0xd5;        (* NOT (% r13) *)
  0x4d; 0x21; 0xdd;        (* AND (% r13) (% r11) *)
  0x4d; 0x31; 0xd5;        (* XOR (% r13) (% r10) *)
  0x4c; 0x89; 0x6c; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% r13) *)
  0x4d; 0x89; 0xdd;        (* MOV (% r13) (% r11) *)
  0x49; 0xf7; 0xd5;        (* NOT (% r13) *)
  0x49; 0x21; 0xdd;        (* AND (% r13) (% rbx) *)
  0x4d; 0x31; 0xe5;        (* XOR (% r13) (% r12) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x4c; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% r13) *)
  0x4d; 0x21; 0xcc;        (* AND (% r12) (% r9) *)
  0x49; 0xf7; 0xd1;        (* NOT (% r9) *)
  0x4d; 0x21; 0xd1;        (* AND (% r9) (% r10) *)
  0x4d; 0x31; 0xdc;        (* XOR (% r12) (% r11) *)
  0x4c; 0x8b; 0x5c; 0x24; 0xd0;
                           (* MOV (% r11) (Memop Quadword (%%
                                  (rsp,18446744073709551568))) *)
  0x4d; 0x89; 0xca;        (* MOV (% r10) (% r9) *)
  0x4c; 0x8b; 0x4c; 0x24; 0x18;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x89; 0x64; 0x24; 0xb0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551536))) (% r12) *)
  0x49; 0x89; 0xfc;        (* MOV (% r12) (% rdi) *)
  0x49; 0x31; 0xda;        (* XOR (% r10) (% rbx) *)
  0x49; 0x31; 0xeb;        (* XOR (% r11) (% rbp) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x4c; 0x89; 0x54; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r10) *)
  0x4c; 0x8b; 0x54; 0x24; 0xc8;
                           (* MOV (% r10) (Memop Quadword (%%
                                  (rsp,18446744073709551560))) *)
  0x49; 0xc1; 0xc3; 0x03;  (* ROL (% r11) (Imm8 (word 3)) *)
  0x49; 0x31; 0xd1;        (* XOR (% r9) (% rdx) *)
  0x49; 0xc1; 0xc1; 0x1c;  (* ROL (% r9) (Imm8 (word 28)) *)
  0x49; 0x31; 0xca;        (* XOR (% r10) (% rcx) *)
  0x49; 0xc1; 0xc2; 0x14;  (* ROL (% r10) (Imm8 (word 20)) *)
  0x4c; 0x89; 0xd3;        (* MOV (% rbx) (% r10) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x4c; 0x21; 0xdb;        (* AND (% rbx) (% r11) *)
  0x4c; 0x31; 0xcb;        (* XOR (% rbx) (% r9) *)
  0x48; 0x89; 0x5c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rbx) *)
  0x4c; 0x89; 0xdb;        (* MOV (% rbx) (% r11) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x21; 0xfb;        (* AND (% rbx) (% rdi) *)
  0x4c; 0x31; 0xd3;        (* XOR (% rbx) (% r10) *)
  0x48; 0x89; 0x5c; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rbx) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x4c; 0x21; 0xc3;        (* AND (% rbx) (% r8) *)
  0x49; 0x31; 0xee;        (* XOR (% r14) (% rbp) *)
  0x49; 0x89; 0xdc;        (* MOV (% r12) (% rbx) *)
  0x49; 0xc1; 0xc6; 0x12;  (* ROL (% r14) (Imm8 (word 18)) *)
  0x4d; 0x31; 0xdc;        (* XOR (% r12) (% r11) *)
  0x4d; 0x89; 0xc3;        (* MOV (% r11) (% r8) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4c; 0x89; 0x64; 0x24; 0xd0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551568))) (% r12) *)
  0x48; 0x8b; 0x5c; 0x24; 0xa8;
                           (* MOV (% rbx) (Memop Quadword (%%
                                  (rsp,18446744073709551528))) *)
  0x4d; 0x21; 0xcb;        (* AND (% r11) (% r9) *)
  0x49; 0xf7; 0xd1;        (* NOT (% r9) *)
  0x4d; 0x21; 0xd1;        (* AND (% r9) (% r10) *)
  0x49; 0x31; 0xfb;        (* XOR (% r11) (% rdi) *)
  0x48; 0x8b; 0x7c; 0x24; 0x90;
                           (* MOV (% rdi) (Memop Quadword (%%
                                  (rsp,18446744073709551504))) *)
  0x48; 0x31; 0xeb;        (* XOR (% rbx) (% rbp) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0xb8;
                           (* MOV (% r8) (Memop Quadword (%%
                                  (rsp,18446744073709551544))) *)
  0x4c; 0x89; 0x5c; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r11) *)
  0x48; 0xc1; 0xcb; 0x1c;  (* ROR (% rbx) (Imm8 (word 28)) *)
  0x4c; 0x8b; 0x5c; 0x24; 0xe0;
                           (* MOV (% r11) (Memop Quadword (%%
                                  (rsp,18446744073709551584))) *)
  0x48; 0x31; 0xf7;        (* XOR (% rdi) (% rsi) *)
  0x4c; 0x89; 0x4c; 0x24; 0xc8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551560))) (% r9) *)
  0x49; 0x31; 0xc0;        (* XOR (% r8) (% rax) *)
  0x4c; 0x8b; 0x0c; 0x24;  (* MOV (% r9) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0xd1; 0xc7;        (* ROL (% rdi) (Imm8 (word 1)) *)
  0x49; 0xc1; 0xc0; 0x06;  (* ROL (% r8) (Imm8 (word 6)) *)
  0x49; 0x31; 0xd3;        (* XOR (% r11) (% rdx) *)
  0x4d; 0x89; 0xc2;        (* MOV (% r10) (% r8) *)
  0x49; 0xc1; 0xc3; 0x19;  (* ROL (% r11) (Imm8 (word 25)) *)
  0x49; 0x31; 0xc9;        (* XOR (% r9) (% rcx) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x4d; 0x89; 0xdd;        (* MOV (% r13) (% r11) *)
  0x49; 0xc1; 0xc1; 0x08;  (* ROL (% r9) (Imm8 (word 8)) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x49; 0xf7; 0xd5;        (* NOT (% r13) *)
  0x49; 0x31; 0xfa;        (* XOR (% r10) (% rdi) *)
  0x4c; 0x89; 0x54; 0x24; 0xb8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551544))) (% r10) *)
  0x4d; 0x89; 0xea;        (* MOV (% r10) (% r13) *)
  0x4d; 0x89; 0xcd;        (* MOV (% r13) (% r9) *)
  0x4d; 0x21; 0xca;        (* AND (% r10) (% r9) *)
  0x49; 0xf7; 0xd5;        (* NOT (% r13) *)
  0x4d; 0x31; 0xc2;        (* XOR (% r10) (% r8) *)
  0x4c; 0x89; 0x14; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r10) *)
  0x4d; 0x89; 0xea;        (* MOV (% r10) (% r13) *)
  0x4d; 0x21; 0xf2;        (* AND (% r10) (% r14) *)
  0x4d; 0x31; 0xda;        (* XOR (% r10) (% r11) *)
  0x4d; 0x89; 0xf3;        (* MOV (% r11) (% r14) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x49; 0x21; 0xfb;        (* AND (% r11) (% rdi) *)
  0x48; 0xf7; 0xd7;        (* NOT (% rdi) *)
  0x4c; 0x21; 0xc7;        (* AND (% rdi) (% r8) *)
  0x4d; 0x31; 0xcb;        (* XOR (% r11) (% r9) *)
  0x4c; 0x8b; 0x44; 0x24; 0xa0;
                           (* MOV (% r8) (Memop Quadword (%%
                                  (rsp,18446744073709551520))) *)
  0x4c; 0x8b; 0x4c; 0x24; 0xd8;
                           (* MOV (% r9) (Memop Quadword (%%
                                  (rsp,18446744073709551576))) *)
  0x4c; 0x31; 0xf7;        (* XOR (% rdi) (% r14) *)
  0x4c; 0x89; 0x5c; 0x24; 0xe0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551584))) (% r11) *)
  0x4c; 0x8b; 0x74; 0x24; 0x98;
                           (* MOV (% r14) (Memop Quadword (%%
                                  (rsp,18446744073709551512))) *)
  0x48; 0x89; 0x7c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rdi) *)
  0x48; 0x8b; 0x7c; 0x24; 0xf8;
                           (* MOV (% rdi) (Memop Quadword (%%
                                  (rsp,18446744073709551608))) *)
  0x49; 0x31; 0xc8;        (* XOR (% r8) (% rcx) *)
  0x49; 0x31; 0xf1;        (* XOR (% r9) (% rsi) *)
  0x49; 0xc1; 0xc1; 0x0a;  (* ROL (% r9) (Imm8 (word 10)) *)
  0x49; 0xc1; 0xc0; 0x1b;  (* ROL (% r8) (Imm8 (word 27)) *)
  0x48; 0x31; 0xc7;        (* XOR (% rdi) (% rax) *)
  0x4c; 0x31; 0xf0;        (* XOR (% rax) (% r14) *)
  0x4c; 0x8b; 0x74; 0x24; 0xc0;
                           (* MOV (% r14) (Memop Quadword (%%
                                  (rsp,18446744073709551552))) *)
  0x49; 0x89; 0xfc;        (* MOV (% r12) (% rdi) *)
  0x48; 0x8b; 0x7c; 0x24; 0x10;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xc1; 0xc8; 0x02;  (* ROR (% rax) (Imm8 (word 2)) *)
  0x49; 0xc1; 0xc4; 0x0f;  (* ROL (% r12) (Imm8 (word 15)) *)
  0x48; 0x31; 0xd7;        (* XOR (% rdi) (% rdx) *)
  0x4d; 0x89; 0xe5;        (* MOV (% r13) (% r12) *)
  0x4c; 0x31; 0xf2;        (* XOR (% rdx) (% r14) *)
  0x4c; 0x8b; 0x74; 0x24; 0xe8;
                           (* MOV (% r14) (Memop Quadword (%%
                                  (rsp,18446744073709551592))) *)
  0x49; 0x89; 0xfb;        (* MOV (% r11) (% rdi) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x49; 0xf7; 0xd5;        (* NOT (% r13) *)
  0x48; 0xc1; 0xca; 0x09;  (* ROR (% rdx) (Imm8 (word 9)) *)
  0x48; 0xf7; 0xd7;        (* NOT (% rdi) *)
  0x49; 0xc1; 0xcb; 0x08;  (* ROR (% r11) (Imm8 (word 8)) *)
  0x4c; 0x31; 0xf1;        (* XOR (% rcx) (% r14) *)
  0x4c; 0x21; 0xcf;        (* AND (% rdi) (% r9) *)
  0x4d; 0x21; 0xdd;        (* AND (% r13) (% r11) *)
  0x48; 0xc1; 0xc9; 0x19;  (* ROR (% rcx) (Imm8 (word 25)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4d; 0x31; 0xcd;        (* XOR (% r13) (% r9) *)
  0x48; 0x89; 0x7c; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rdi) *)
  0x4c; 0x89; 0xcf;        (* MOV (% rdi) (% r9) *)
  0x4d; 0x89; 0xd9;        (* MOV (% r9) (% r11) *)
  0x49; 0xf7; 0xd1;        (* NOT (% r9) *)
  0x48; 0xf7; 0xd7;        (* NOT (% rdi) *)
  0x4d; 0x21; 0xc1;        (* AND (% r9) (% r8) *)
  0x49; 0xf7; 0xd0;        (* NOT (% r8) *)
  0x4c; 0x21; 0xe7;        (* AND (% rdi) (% r12) *)
  0x49; 0x21; 0xd8;        (* AND (% r8) (% rbx) *)
  0x48; 0x31; 0xdf;        (* XOR (% rdi) (% rbx) *)
  0x4d; 0x31; 0xe1;        (* XOR (% r9) (% r12) *)
  0x4c; 0x8b; 0x64; 0x24; 0x20;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,32))) *)
  0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
  0x49; 0x89; 0xcb;        (* MOV (% r11) (% rcx) *)
  0x48; 0x8b; 0x4c; 0x24; 0xf0;
                           (* MOV (% rcx) (Memop Quadword (%%
                                  (rsp,18446744073709551600))) *)
  0x4c; 0x89; 0x44; 0x24; 0xd8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551576))) (% r8) *)
  0x48; 0x31; 0xcd;        (* XOR (% rbp) (% rcx) *)
  0x48; 0x8b; 0x4c; 0x24; 0x08;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,8))) *)
  0x48; 0xc1; 0xcd; 0x17;  (* ROR (% rbp) (Imm8 (word 23)) *)
  0x48; 0x31; 0xce;        (* XOR (% rsi) (% rcx) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0xc1; 0xc6; 0x02;  (* ROL (% rsi) (Imm8 (word 2)) *)
  0x48; 0xf7; 0xd1;        (* NOT (% rcx) *)
  0x49; 0x89; 0xf0;        (* MOV (% r8) (% rsi) *)
  0x4c; 0x89; 0xde;        (* MOV (% rsi) (% r11) *)
  0x4c; 0x21; 0xd9;        (* AND (% rcx) (% r11) *)
  0x48; 0xf7; 0xd6;        (* NOT (% rsi) *)
  0x4d; 0x89; 0xc6;        (* MOV (% r14) (% r8) *)
  0x48; 0x31; 0xc1;        (* XOR (% rcx) (% rax) *)
  0x48; 0x21; 0xee;        (* AND (% rsi) (% rbp) *)
  0x49; 0xf7; 0xd6;        (* NOT (% r14) *)
  0x48; 0x89; 0x4c; 0x24; 0xe8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551592))) (% rcx) *)
  0x48; 0x31; 0xd6;        (* XOR (% rsi) (% rdx) *)
  0x48; 0x89; 0xf3;        (* MOV (% rbx) (% rsi) *)
  0x48; 0x89; 0xee;        (* MOV (% rsi) (% rbp) *)
  0x48; 0xf7; 0xd6;        (* NOT (% rsi) *)
  0x48; 0x89; 0x5c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rbx) *)
  0x4c; 0x21; 0xc6;        (* AND (% rsi) (% r8) *)
  0x4c; 0x31; 0xde;        (* XOR (% rsi) (% r11) *)
  0x4d; 0x89; 0xf3;        (* MOV (% r11) (% r14) *)
  0x49; 0x21; 0xc3;        (* AND (% r11) (% rax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x4d; 0x89; 0xde;        (* MOV (% r14) (% r11) *)
  0x49; 0x31; 0xee;        (* XOR (% r14) (% rbp) *)
  0x48; 0x21; 0xd0;        (* AND (% rax) (% rdx) *)
  0x48; 0x8b; 0x6c; 0x24; 0x10;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x8b; 0x14; 0x24;  (* MOV (% rdx) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x31; 0xc0;        (* XOR (% rax) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x89; 0x74; 0x24; 0xf0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551600))) (% r14) *)
  0x4c; 0x8b; 0x74; 0x24; 0xb8;
                           (* MOV (% r14) (Memop Quadword (%%
                                  (rsp,18446744073709551544))) *)
  0x4d; 0x31; 0xf8;        (* XOR (% r8) (% r15) *)
  0x4d; 0x31; 0xf0;        (* XOR (% r8) (% r14) *)
  0x49; 0x31; 0xe8;        (* XOR (% r8) (% rbp) *)
  0x48; 0x8b; 0x6c; 0x24; 0x28;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,40))) *)
  0x49; 0x31; 0xc8;        (* XOR (% r8) (% rcx) *)
  0x48; 0x8b; 0x4c; 0x24; 0x18;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,24))) *)
  0x49; 0x31; 0xcc;        (* XOR (% r12) (% rcx) *)
  0x49; 0x31; 0xd4;        (* XOR (% r12) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xd0;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551568))) *)
  0x4c; 0x8b; 0x5c; 0x24; 0xb0;
                           (* MOV (% r11) (Memop Quadword (%%
                                  (rsp,18446744073709551536))) *)
  0x4c; 0x89; 0x6c; 0x24; 0xf8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551608))) (% r13) *)
  0x49; 0x31; 0xfc;        (* XOR (% r12) (% rdi) *)
  0x4c; 0x8b; 0x74; 0x24; 0xf0;
                           (* MOV (% r14) (Memop Quadword (%%
                                  (rsp,18446744073709551600))) *)
  0x48; 0x31; 0xd5;        (* XOR (% rbp) (% rdx) *)
  0x49; 0x31; 0xdc;        (* XOR (% r12) (% rbx) *)
  0x48; 0x8b; 0x5c; 0x24; 0x40;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,64))) *)
  0x48; 0x8b; 0x54; 0x24; 0xc8;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551560))) *)
  0x4c; 0x31; 0xd5;        (* XOR (% rbp) (% r10) *)
  0x4c; 0x31; 0xed;        (* XOR (% rbp) (% r13) *)
  0x4c; 0x8b; 0x6c; 0x24; 0xe0;
                           (* MOV (% r13) (Memop Quadword (%%
                                  (rsp,18446744073709551584))) *)
  0x49; 0x31; 0xdb;        (* XOR (% r11) (% rbx) *)
  0x48; 0x8b; 0x5c; 0x24; 0x48;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,72))) *)
  0x48; 0x31; 0xf5;        (* XOR (% rbp) (% rsi) *)
  0x4d; 0x31; 0xeb;        (* XOR (% r11) (% r13) *)
  0x48; 0x31; 0xda;        (* XOR (% rdx) (% rbx) *)
  0x48; 0x8b; 0x5c; 0x24; 0x30;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,48))) *)
  0x49; 0x89; 0xed;        (* MOV (% r13) (% rbp) *)
  0x4d; 0x31; 0xcb;        (* XOR (% r11) (% r9) *)
  0x49; 0xd1; 0xc5;        (* ROL (% r13) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xf3;        (* XOR (% r11) (% r14) *)
  0x4c; 0x8b; 0x74; 0x24; 0xd8;
                           (* MOV (% r14) (Memop Quadword (%%
                                  (rsp,18446744073709551576))) *)
  0x48; 0x31; 0xda;        (* XOR (% rdx) (% rbx) *)
  0x4d; 0x31; 0xc5;        (* XOR (% r13) (% r8) *)
  0x4c; 0x89; 0xdb;        (* MOV (% rbx) (% r11) *)
  0x49; 0xd1; 0xc0;        (* ROL (% r8) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xf2;        (* XOR (% rdx) (% r14) *)
  0x4d; 0x89; 0xe6;        (* MOV (% r14) (% r12) *)
  0x48; 0xd1; 0xc3;        (* ROL (% rbx) (Imm8 (word 1)) *)
  0x4d; 0x31; 0xd8;        (* XOR (% r8) (% r11) *)
  0x48; 0x31; 0xc2;        (* XOR (% rdx) (% rax) *)
  0x49; 0xd1; 0xc6;        (* ROL (% r14) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xe3;        (* XOR (% rbx) (% r12) *)
  0x49; 0x31; 0xd6;        (* XOR (% r14) (% rdx) *)
  0x48; 0xd1; 0xc2;        (* ROL (% rdx) (Imm8 (word 1)) *)
  0x48; 0x31; 0xea;        (* XOR (% rdx) (% rbp) *)
  0x48; 0x89; 0xcd;        (* MOV (% rbp) (% rcx) *)
  0x4d; 0x31; 0xf7;        (* XOR (% r15) (% r14) *)
  0x49; 0x31; 0xda;        (* XOR (% r10) (% rbx) *)
  0x4c; 0x31; 0xed;        (* XOR (% rbp) (% r13) *)
  0x4d; 0x89; 0xfb;        (* MOV (% r11) (% r15) *)
  0x49; 0xc1; 0xca; 0x15;  (* ROR (% r10) (Imm8 (word 21)) *)
  0x49; 0x31; 0xd1;        (* XOR (% r9) (% rdx) *)
  0x48; 0xc1; 0xcd; 0x14;  (* ROR (% rbp) (Imm8 (word 20)) *)
  0x49; 0xc1; 0xc1; 0x15;  (* ROL (% r9) (Imm8 (word 21)) *)
  0x4c; 0x31; 0xc0;        (* XOR (% rax) (% r8) *)
  0x4c; 0x31; 0xef;        (* XOR (% rdi) (% r13) *)
  0x48; 0xc1; 0xc0; 0x0e;  (* ROL (% rax) (Imm8 (word 14)) *)
  0x49; 0x89; 0xef;        (* MOV (% r15) (% rbp) *)
  0x48; 0xc1; 0xcf; 0x13;  (* ROR (% rdi) (Imm8 (word 19)) *)
  0x48; 0x31; 0xde;        (* XOR (% rsi) (% rbx) *)
  0x49; 0xf7; 0xd7;        (* NOT (% r15) *)
  0x48; 0xc1; 0xce; 0x03;  (* ROR (% rsi) (Imm8 (word 3)) *)
  0x4d; 0x89; 0xfc;        (* MOV (% r12) (% r15) *)
  0x4c; 0x8b; 0x7c; 0x24; 0x88;
                           (* MOV (% r15) (Memop Quadword (%%
                                  (rsp,18446744073709551496))) *)
  0x4d; 0x21; 0xd4;        (* AND (% r12) (% r10) *)
  0x49; 0x8b; 0x4f; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (r15,8))) *)
  0x4c; 0x31; 0xd9;        (* XOR (% rcx) (% r11) *)
  0x49; 0x89; 0xcf;        (* MOV (% r15) (% rcx) *)
  0x48; 0x8b; 0x4c; 0x24; 0xe8;
                           (* MOV (% rcx) (Memop Quadword (%%
                                  (rsp,18446744073709551592))) *)
  0x4d; 0x31; 0xe7;        (* XOR (% r15) (% r12) *)
  0x4d; 0x89; 0xd4;        (* MOV (% r12) (% r10) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x4d; 0x21; 0xcc;        (* AND (% r12) (% r9) *)
  0x49; 0x31; 0xec;        (* XOR (% r12) (% rbp) *)
  0x4c; 0x89; 0x64; 0x24; 0x90;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551504))) (% r12) *)
  0x4d; 0x89; 0xcc;        (* MOV (% r12) (% r9) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x49; 0x21; 0xc4;        (* AND (% r12) (% rax) *)
  0x4d; 0x31; 0xd4;        (* XOR (% r12) (% r10) *)
  0x49; 0x89; 0xc2;        (* MOV (% r10) (% rax) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x4c; 0x89; 0x64; 0x24; 0x98;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551512))) (% r12) *)
  0x4c; 0x8b; 0x64; 0x24; 0x20;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,32))) *)
  0x4d; 0x21; 0xda;        (* AND (% r10) (% r11) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x49; 0x21; 0xeb;        (* AND (% r11) (% rbp) *)
  0x4d; 0x31; 0xca;        (* XOR (% r10) (% r9) *)
  0x4c; 0x8b; 0x4c; 0x24; 0xc8;
                           (* MOV (% r9) (Memop Quadword (%%
                                  (rsp,18446744073709551560))) *)
  0x49; 0x31; 0xc3;        (* XOR (% r11) (% rax) *)
  0x4c; 0x89; 0x54; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% r10) *)
  0x4c; 0x8b; 0x54; 0x24; 0xb8;
                           (* MOV (% r10) (Memop Quadword (%%
                                  (rsp,18446744073709551544))) *)
  0x4c; 0x89; 0x5c; 0x24; 0xa0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551520))) (% r11) *)
  0x4c; 0x8b; 0x5c; 0x24; 0xb0;
                           (* MOV (% r11) (Memop Quadword (%%
                                  (rsp,18446744073709551536))) *)
  0x4d; 0x31; 0xc1;        (* XOR (% r9) (% r8) *)
  0x49; 0xc1; 0xc1; 0x14;  (* ROL (% r9) (Imm8 (word 20)) *)
  0x4d; 0x31; 0xf2;        (* XOR (% r10) (% r14) *)
  0x49; 0x31; 0xd3;        (* XOR (% r11) (% rdx) *)
  0x49; 0xc1; 0xc2; 0x03;  (* ROL (% r10) (Imm8 (word 3)) *)
  0x4c; 0x89; 0xd8;        (* MOV (% rax) (% r11) *)
  0x4d; 0x89; 0xcb;        (* MOV (% r11) (% r9) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x48; 0xc1; 0xc0; 0x1c;  (* ROL (% rax) (Imm8 (word 28)) *)
  0x4d; 0x21; 0xd3;        (* AND (% r11) (% r10) *)
  0x49; 0x31; 0xc3;        (* XOR (% r11) (% rax) *)
  0x4c; 0x89; 0x5c; 0x24; 0xa8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551528))) (% r11) *)
  0x4d; 0x89; 0xd3;        (* MOV (% r11) (% r10) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x49; 0x21; 0xfb;        (* AND (% r11) (% rdi) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4c; 0x31; 0xf1;        (* XOR (% rcx) (% r14) *)
  0x4d; 0x31; 0xcb;        (* XOR (% r11) (% r9) *)
  0x48; 0xc1; 0xc1; 0x12;  (* ROL (% rcx) (Imm8 (word 18)) *)
  0x4c; 0x89; 0x5c; 0x24; 0xb0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551536))) (% r11) *)
  0x49; 0x89; 0xfb;        (* MOV (% r11) (% rdi) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x49; 0x21; 0xf3;        (* AND (% r11) (% rsi) *)
  0x4d; 0x31; 0xd3;        (* XOR (% r11) (% r10) *)
  0x49; 0x89; 0xf2;        (* MOV (% r10) (% rsi) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x4c; 0x89; 0x5c; 0x24; 0xb8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551544))) (% r11) *)
  0x49; 0x21; 0xc2;        (* AND (% r10) (% rax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0x31; 0xfa;        (* XOR (% r10) (% rdi) *)
  0x4c; 0x21; 0xc8;        (* AND (% rax) (% r9) *)
  0x48; 0x8b; 0x7c; 0x24; 0xe0;
                           (* MOV (% rdi) (Memop Quadword (%%
                                  (rsp,18446744073709551584))) *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x4c; 0x89; 0x54; 0x24; 0xc0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551552))) (% r10) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x49; 0x31; 0xf3;        (* XOR (% r11) (% rsi) *)
  0x48; 0x31; 0xd7;        (* XOR (% rdi) (% rdx) *)
  0x48; 0x8b; 0x74; 0x24; 0xd0;
                           (* MOV (% rsi) (Memop Quadword (%%
                                  (rsp,18446744073709551568))) *)
  0x48; 0xd1; 0xc0;        (* ROL (% rax) (Imm8 (word 1)) *)
  0x49; 0x89; 0xf9;        (* MOV (% r9) (% rdi) *)
  0x48; 0x8b; 0x7c; 0x24; 0xd8;
                           (* MOV (% rdi) (Memop Quadword (%%
                                  (rsp,18446744073709551576))) *)
  0x4c; 0x89; 0x5c; 0x24; 0xc8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551560))) (% r11) *)
  0x48; 0x31; 0xde;        (* XOR (% rsi) (% rbx) *)
  0x49; 0xc1; 0xc1; 0x19;  (* ROL (% r9) (Imm8 (word 25)) *)
  0x48; 0xc1; 0xc6; 0x06;  (* ROL (% rsi) (Imm8 (word 6)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x48; 0xc1; 0xc7; 0x08;  (* ROL (% rdi) (Imm8 (word 8)) *)
  0x49; 0x89; 0xf2;        (* MOV (% r10) (% rsi) *)
  0x49; 0x89; 0xfc;        (* MOV (% r12) (% rdi) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x4d; 0x21; 0xca;        (* AND (% r10) (% r9) *)
  0x49; 0xf7; 0xd4;        (* NOT (% r12) *)
  0x49; 0x31; 0xc2;        (* XOR (% r10) (% rax) *)
  0x49; 0x21; 0xcc;        (* AND (% r12) (% rcx) *)
  0x4c; 0x89; 0x54; 0x24; 0xd0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551568))) (% r10) *)
  0x4d; 0x31; 0xcc;        (* XOR (% r12) (% r9) *)
  0x4d; 0x89; 0xca;        (* MOV (% r10) (% r9) *)
  0x49; 0x89; 0xc9;        (* MOV (% r9) (% rcx) *)
  0x49; 0xf7; 0xd1;        (* NOT (% r9) *)
  0x49; 0xf7; 0xd2;        (* NOT (% r10) *)
  0x49; 0x21; 0xc1;        (* AND (% r9) (% rax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x49; 0x21; 0xfa;        (* AND (% r10) (% rdi) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x49; 0x31; 0xf9;        (* XOR (% r9) (% rdi) *)
  0x49; 0x31; 0xf2;        (* XOR (% r10) (% rsi) *)
  0x48; 0x89; 0xc7;        (* MOV (% rdi) (% rax) *)
  0x4c; 0x89; 0x54; 0x24; 0xd8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551576))) (% r10) *)
  0x48; 0x31; 0xcf;        (* XOR (% rdi) (% rcx) *)
  0x4c; 0x89; 0x4c; 0x24; 0xe0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551584))) (% r9) *)
  0x48; 0x89; 0x7c; 0x24; 0xe8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551592))) (% rdi) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x48; 0x8b; 0x74; 0x24; 0x38;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x8b; 0x0c; 0x24;  (* MOV (% r9) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x8b; 0x54; 0x24; 0xf8;
                           (* MOV (% r10) (Memop Quadword (%%
                                  (rsp,18446744073709551608))) *)
  0x4c; 0x31; 0xc0;        (* XOR (% rax) (% r8) *)
  0x48; 0x8b; 0x4c; 0x24; 0xf0;
                           (* MOV (% rcx) (Memop Quadword (%%
                                  (rsp,18446744073709551600))) *)
  0x4c; 0x31; 0xf6;        (* XOR (% rsi) (% r14) *)
  0x48; 0xc1; 0xc0; 0x1b;  (* ROL (% rax) (Imm8 (word 27)) *)
  0x48; 0x8b; 0x6c; 0x24; 0x28;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,40))) *)
  0x48; 0xc1; 0xce; 0x1c;  (* ROR (% rsi) (Imm8 (word 28)) *)
  0x4d; 0x31; 0xe9;        (* XOR (% r9) (% r13) *)
  0x49; 0x31; 0xda;        (* XOR (% r10) (% rbx) *)
  0x48; 0x31; 0xd1;        (* XOR (% rcx) (% rdx) *)
  0x49; 0xc1; 0xc2; 0x0f;  (* ROL (% r10) (Imm8 (word 15)) *)
  0x48; 0xc1; 0xc9; 0x08;  (* ROR (% rcx) (Imm8 (word 8)) *)
  0x48; 0x89; 0xf7;        (* MOV (% rdi) (% rsi) *)
  0x48; 0x31; 0xeb;        (* XOR (% rbx) (% rbp) *)
  0x49; 0xc1; 0xc1; 0x0a;  (* ROL (% r9) (Imm8 (word 10)) *)
  0x4d; 0x89; 0xd3;        (* MOV (% r11) (% r10) *)
  0x48; 0xf7; 0xd7;        (* NOT (% rdi) *)
  0x48; 0xc1; 0xcb; 0x02;  (* ROR (% rbx) (Imm8 (word 2)) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4c; 0x21; 0xcf;        (* AND (% rdi) (% r9) *)
  0x49; 0x21; 0xcb;        (* AND (% r11) (% rcx) *)
  0x48; 0x31; 0xc7;        (* XOR (% rdi) (% rax) *)
  0x4d; 0x31; 0xcb;        (* XOR (% r11) (% r9) *)
  0x48; 0x89; 0x7c; 0x24; 0xf0;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551600))) (% rdi) *)
  0x4c; 0x89; 0xcf;        (* MOV (% rdi) (% r9) *)
  0x4c; 0x89; 0x5c; 0x24; 0xf8;
                           (* MOV (Memop Quadword (%%
                                  (rsp,18446744073709551608))) (% r11) *)
  0x49; 0x89; 0xcb;        (* MOV (% r11) (% rcx) *)
  0x48; 0xf7; 0xd7;        (* NOT (% rdi) *)
  0x49; 0xf7; 0xd3;        (* NOT (% r11) *)
  0x4c; 0x21; 0xd7;        (* AND (% rdi) (% r10) *)
  0x49; 0x21; 0xc3;        (* AND (% r11) (% rax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x31; 0xf7;        (* XOR (% rdi) (% rsi) *)
  0x48; 0x21; 0xf0;        (* AND (% rax) (% rsi) *)
  0x48; 0x8b; 0x74; 0x24; 0x08;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,8))) *)
  0x4d; 0x31; 0xd3;        (* XOR (% r11) (% r10) *)
  0x49; 0x89; 0xc1;        (* MOV (% r9) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x31; 0xc9;        (* XOR (% r9) (% rcx) *)
  0x48; 0x8b; 0x4c; 0x24; 0x48;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x31; 0xee;        (* XOR (% rsi) (% r13) *)
  0x48; 0x31; 0xd0;        (* XOR (% rax) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0x10;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0xc1; 0xc6; 0x02;  (* ROL (% rsi) (Imm8 (word 2)) *)
  0x4c; 0x89; 0x0c; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% r9) *)
  0x4c; 0x31; 0xc1;        (* XOR (% rcx) (% r8) *)
  0x48; 0xc1; 0xc8; 0x09;  (* ROR (% rax) (Imm8 (word 9)) *)
  0x48; 0xc1; 0xc9; 0x19;  (* ROR (% rcx) (Imm8 (word 25)) *)
  0x4c; 0x31; 0xf2;        (* XOR (% rdx) (% r14) *)
  0x49; 0x89; 0xc6;        (* MOV (% r14) (% rax) *)
  0x49; 0x89; 0xc8;        (* MOV (% r8) (% rcx) *)
  0x48; 0xc1; 0xca; 0x17;  (* ROR (% rdx) (Imm8 (word 23)) *)
  0x49; 0xf7; 0xd6;        (* NOT (% r14) *)
  0x49; 0xf7; 0xd0;        (* NOT (% r8) *)
  0x49; 0x21; 0xce;        (* AND (% r14) (% rcx) *)
  0x49; 0x21; 0xd0;        (* AND (% r8) (% rdx) *)
  0x49; 0x31; 0xde;        (* XOR (% r14) (% rbx) *)
  0x49; 0x31; 0xc0;        (* XOR (% r8) (% rax) *)
  0x4c; 0x89; 0x44; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% r8) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x49; 0xf7; 0xd0;        (* NOT (% r8) *)
  0x49; 0x21; 0xf0;        (* AND (% r8) (% rsi) *)
  0x49; 0x31; 0xc8;        (* XOR (% r8) (% rcx) *)
  0x48; 0x89; 0xf1;        (* MOV (% rcx) (% rsi) *)
  0x48; 0xf7; 0xd1;        (* NOT (% rcx) *)
  0x48; 0x21; 0xd9;        (* AND (% rcx) (% rbx) *)
  0x48; 0xf7; 0xd3;        (* NOT (% rbx) *)
  0x48; 0x83; 0x44; 0x24; 0x88; 0x10;
                           (* ADD (Memop Quadword (%%
                                  (rsp,18446744073709551496))) (Imm8 (word 16))
                                  *)
  0x48; 0x21; 0xc3;        (* AND (% rbx) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x88;
                           (* MOV (% rax) (Memop Quadword (%%
                                  (rsp,18446744073709551496))) *)
  0x48; 0x31; 0xd1;        (* XOR (% rcx) (% rdx) *)
  0x48; 0x8d; 0x15];
  ADDR ("mlkem_native_keccakf1600_permute_gcc12_O2_data",(188)); b[
                           (* LEA (% rdx) (Riprel (word_sx (iword
                               (&mlkem_native_keccakf1600_permute_gcc12_O2_data
                               - (&pc + &1819))))) *)
  0x48; 0x89; 0x4c; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rcx) *)
  0x48; 0x31; 0xf3;        (* XOR (% rbx) (% rsi) *)
  0x48; 0x39; 0xc2;        (* CMP (% rdx) (% rax) *)
  0x0f; 0x85; 0x14; 0xf9; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294965524)) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x48; 0x8b; 0x54; 0x24; 0x90;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551504))) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x18;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x89; 0x50; 0x08;  (* MOV (Memop Quadword (%% (rax,8))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0x98;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551512))) *)
  0x4c; 0x89; 0x38;        (* MOV (Memop Quadword (%% (rax,0))) (% r15) *)
  0x48; 0x89; 0x50; 0x10;  (* MOV (Memop Quadword (%% (rax,16))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xa0;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551520))) *)
  0x4c; 0x89; 0x68; 0x18;  (* MOV (Memop Quadword (%% (rax,24))) (% r13) *)
  0x48; 0x89; 0x50; 0x20;  (* MOV (Memop Quadword (%% (rax,32))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xa8;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551528))) *)
  0x4c; 0x89; 0x60; 0x60;  (* MOV (Memop Quadword (%% (rax,96))) (% r12) *)
  0x48; 0x89; 0x50; 0x28;  (* MOV (Memop Quadword (%% (rax,40))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xb0;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551536))) *)
  0x48; 0x89; 0xb8; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rax,128))) (% rdi) *)
  0x48; 0x89; 0x50; 0x30;  (* MOV (Memop Quadword (%% (rax,48))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xb8;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551544))) *)
  0x48; 0x89; 0x50; 0x38;  (* MOV (Memop Quadword (%% (rax,56))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xc0;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551552))) *)
  0x48; 0x89; 0x50; 0x40;  (* MOV (Memop Quadword (%% (rax,64))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xc8;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551560))) *)
  0x48; 0x89; 0x50; 0x48;  (* MOV (Memop Quadword (%% (rax,72))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xd0;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551568))) *)
  0x48; 0x89; 0x50; 0x50;  (* MOV (Memop Quadword (%% (rax,80))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xd8;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551576))) *)
  0x48; 0x89; 0x50; 0x58;  (* MOV (Memop Quadword (%% (rax,88))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xe0;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551584))) *)
  0x48; 0x89; 0x50; 0x68;  (* MOV (Memop Quadword (%% (rax,104))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xe8;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551592))) *)
  0x48; 0x89; 0x50; 0x70;  (* MOV (Memop Quadword (%% (rax,112))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xf0;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551600))) *)
  0x48; 0x89; 0x50; 0x78;  (* MOV (Memop Quadword (%% (rax,120))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0xf8;
                           (* MOV (% rdx) (Memop Quadword (%%
                                  (rsp,18446744073709551608))) *)
  0x4c; 0x89; 0x98; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rax,144))) (% r11) *)
  0x48; 0x89; 0x90; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rax,136))) (% rdx) *)
  0x48; 0x8b; 0x54; 0x24; 0x08;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x89; 0x88; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rax,152))) (% r9) *)
  0x4c; 0x89; 0xb0; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rax,160))) (% r14) *)
  0x48; 0x89; 0x90; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rax,168))) (% rdx) *)
  0x4c; 0x89; 0x80; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rax,176))) (% r8) *)
  0x48; 0x89; 0x88; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rax,184))) (% rcx) *)
  0x48; 0x89; 0x98; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rax,192))) (% rbx) *)
  0x48; 0x83; 0xc4; 0x58;  (* ADD (% rsp) (Imm8 (word 88)) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0xc3                     (* RET *)
]]);;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_keccakf1600_permute_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* Reading the round constants from the table.                               *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES64_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int64 list) n j s:x86state.
        read (memory :> bytes(a,8 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes64(word_add a (word(8 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int64 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read c s`) (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `64 * j = 8 * (8 * j)`;
              ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let KECCAK_RC_DATA = prove
 (`num_of_bytelist mlkem_native_keccakf1600_permute_gcc12_O2_data =
   num_of_wordlist round_constants`,
  REWRITE_TAC[hd mlkem_native_keccakf1600_permute_gcc12_O2_data;
              round_constants] THEN
  REWRITE_TAC[num_of_bytelist; num_of_wordlist] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let KECCAK_RC_BYTES = prove
 (`!rc s.
        bytes_loaded s (word rc) mlkem_native_keccakf1600_permute_gcc12_O2_data
        ==> read (memory :> bytes(word rc,192)) s =
            num_of_wordlist round_constants`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; KECCAK_RC_DATA;
              CONV_RULE(RAND_CONV LENGTH_CONV)
               (AP_TERM `LENGTH:byte list->num`
                  (hd mlkem_native_keccakf1600_permute_gcc12_O2_data))]);;

let LENGTH_ROUND_CONSTANTS = prove
 (`LENGTH round_constants = 24`,
  REWRITE_TAC[round_constants; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** The address of the end of the table, as computed for the loop test ***)

let KECCAK_RC_END_FOLD = prove
 (`!pc rc. riprel32_within_bounds (rc + 192) (pc + 2011)
           ==> word(val(word(pc + 2011):int64) +
                    val(word_sx(iword(&rc - (&pc + &1819)):int32):int64))
               :int64 =
               word(rc + 192)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&rc - (&pc + &1819):int = &(rc + 192) - (&pc + &2011)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC;
    MATCH_MP_TAC(CONJUNCT1(SPECL [`pc:num`; `2011`; `0`; `rc + 192`]
                   RIP_REL_ADDR_FOLD)) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the loop body, which does two rounds. As each lane of the     *)
(* first round is computed, it is replaced by a variable E_j abbreviating    *)
(* the corresponding lane in the specification, so that the second round     *)
(* and the final checks are about one round only. The lanes are recognized   *)
(* by evaluating both sides at random values, before proving the equations   *)
(* with KECCAK_BITBLAST_TAC.                                                 *)
(* ------------------------------------------------------------------------- *)

(*** Introduce ghost variables for the state reads in a list ***)

let GHOST_STATELIST_TAC =
  W(fun (asl,w) ->
        let regreads = dest_list(find_term is_list w) in
        let ghostvars = make_args "Ai_" [] (map type_of regreads) in
        EVERY(map2 GHOST_INTRO_TAC ghostvars (map rator regreads)));;

(*** Evaluation of 64-bit word expressions, with random values for atoms ***)

let eval64 =
  let atom_vals = Hashtbl.create 100 and memo = Hashtbl.create 10000 in
  let rand64 () =
    Int64.logor (Int64.shift_left (Int64.of_int (Random.bits ())) 34)
     (Int64.logor (Int64.shift_left (Int64.of_int (Random.bits ())) 4)
                  (Int64.of_int (Random.bits () land 15))) in
  let atom_val t =
    try Hashtbl.find atom_vals t with Not_found ->
      let v = rand64 () in Hashtbl.add atom_vals t v; v in
  let ror64 x n =
    if n = 0 then x else
    Int64.logor (Int64.shift_right_logical x n)
                (Int64.shift_left x (64 - n)) in
  let int64_of_num n =
    let v = ref 0L in
    String.iter (fun c -> v := Int64.add (Int64.mul !v 10L)
                                (Int64.of_int (Char.code c - 48)))
                (string_of_num n);
    !v in
  let rec eval t =
    try Hashtbl.find memo t with Not_found ->
    let v = match t with
      Comb(Comb(Const("word_xor",_),x),y) -> Int64.logxor (eval x) (eval y)
    | Comb(Comb(Const("word_and",_),x),y) -> Int64.logand (eval x) (eval y)
    | Comb(Comb(Const("word_or",_),x),y) -> Int64.logor (eval x) (eval y)
    | Comb(Const("word_not",_),x) -> Int64.lognot (eval x)
    | Comb(Comb(Const("word_ror",_),x),n) ->
        ror64 (eval x) (dest_small_numeral n)
    | Comb(Comb(Const("word_rol",_),x),n) ->
        ror64 (eval x) ((64 - dest_small_numeral n) mod 64)
    | Comb(Comb(Const("word_subword",_),
                Comb(Comb(Const("word_join",_),x),y)),p)
        when dest_small_numeral(rand p) = 64 ->
        let pos = dest_small_numeral(lhand p) in
        if pos = 0 then eval y else
        Int64.logor (Int64.shift_right_logical (eval y) pos)
                    (Int64.shift_left (eval x) (64 - pos))
    | Comb(Const("word",_),n) when is_numeral n ->
        int64_of_num(dest_numeral n)
    | _ -> atom_val t in
    Hashtbl.add memo t v; v in
  eval;;

(*** Expansion of one round of the specification as an explicit list ***)

let keccak_spec_round_conv =
  REWRITE_CONV[keccak_round] THENC TOP_DEPTH_CONV let_CONV THENC
  ONCE_DEPTH_CONV EL_CONV;;

(*** The abbreviations E_j for the lanes after the first round ***)

let KECCAK_INTRO_ABBREVS_TAC =
  W(fun (asl,w) ->
    let ais = map (fun j -> mk_var("Ai_"^string_of_int j,`:int64`)) (0--24) in
    let tm = mk_comb(mk_comb(`keccak_round`,`EL (2 * i) round_constants`),
                     mk_list(ais,`:int64`)) in
    let specs = dest_list(rhs(concl(keccak_spec_round_conv tm))) in
    let evs = map (fun j -> mk_var("E_"^string_of_int j,`:int64`)) (0--24) in
    MAP_EVERY (fun (e,t) -> ABBREV_TAC(mk_eq(e,t))) (zip evs specs));;

let keccak_abbrevs asl =
  mapfilter (fun (_,th) ->
    let c = concl th in
    let v = rhs c in
    if is_var v && String.length (fst(dest_var v)) > 2 &&
       String.sub (fst(dest_var v)) 0 2 = "E_"
    then (v,lhs c) else failwith "") asl;;

(*** After a step, replace any value that is a lane of the first round ***)

let KECCAK_ABBREV_STEP_TAC =
  let int64_ty = `:int64` in
  W(fun (asl,w) ->
    let s = rand w in
    let evals = map (fun (e,sp) -> (eval64 sp,(e,sp))) (keccak_abbrevs asl) in
    let cands = mapfilter (fun (_,th) ->
       let c = concl th in
       if is_eq c && is_comb(lhs c) && rand(lhs c) = s &&
          type_of(rhs c) = int64_ty && not(is_var(rhs c))
       then let (e,sp) = assoc (eval64(rhs c)) evals in (c,e,sp)
       else failwith "") asl in
    MAP_EVERY (fun (c,e,sp) ->
       let eqth = TRANS (prove(mk_eq(rhs c,sp),KECCAK_BITBLAST_TAC))
                        (ASSUME(mk_eq(sp,e))) in
       FIRST_X_ASSUM(fun th -> if concl th = c then ASSUME_TAC(TRANS th eqth)
                               else failwith "")) cands);;

(*** The final check of the lanes, now in terms of the E_j ***)

let KECCAK_SECOND_ROUND_TAC =
  CONV_TAC(RAND_CONV(REWRITE_CONV
   [ARITH_RULE `2 * (i + 1) = (2 * i + 1) + 1`; keccak])) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && is_list(lhs(concl th))
    then CONV_TAC(RAND_CONV(REWRITE_CONV[GSYM th]))
    else failwith "") THEN
  CONV_TAC(RAND_CONV(RAND_CONV keccak_spec_round_conv)) THEN
  W(fun (asl,w) ->
    REWRITE_TAC(map (fun (e,sp) -> ASSUME(mk_eq(sp,e)))
                    (keccak_abbrevs asl))) THEN
  CONV_TAC(RAND_CONV keccak_spec_round_conv) THEN
  REWRITE_TAC[CONS_11] THEN REPEAT CONJ_TAC THEN KECCAK_BITBLAST_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, for the whole subroutine, with the invariant of the    *)
(* loop stated relative to the lowest address sbase of the stack used, the   *)
(* red-zone slot holding the pointer into the table of round constants.      *)
(* ------------------------------------------------------------------------- *)

(*** The lanes in row-major order at the head and the end of the loop. At
 *** the end, lanes 19 and 23 are also in R9 and RCX, which the code stores
 *** back to the state after the last iteration.
 ***)

let keccak_lanes_str =
 "[read R15 s;
   read (memory :> bytes64(word_add sbase (word 8))) s;
   read (memory :> bytes64(word_add sbase (word 16))) s;
   read (memory :> bytes64(word_add sbase (word 144))) s;
   read (memory :> bytes64(word_add sbase (word 24))) s;
   read (memory :> bytes64(word_add sbase (word 32))) s;
   read (memory :> bytes64(word_add sbase (word 40))) s;
   read (memory :> bytes64(word_add sbase (word 48))) s;
   read (memory :> bytes64(word_add sbase (word 56))) s;
   read (memory :> bytes64(word_add sbase (word 64))) s;
   read (memory :> bytes64(word_add sbase (word 72))) s;
   read (memory :> bytes64(word_add sbase (word 80))) s;
   read R12 s;
   read (memory :> bytes64(word_add sbase (word 88))) s;
   read (memory :> bytes64(word_add sbase (word 96))) s;
   read (memory :> bytes64(word_add sbase (word 104))) s;
   read RDI s;
   read (memory :> bytes64(word_add sbase (word 112))) s;
   read R11 s;
   read (memory :> bytes64(word_add sbase (word 120))) s;
   read R14 s;
   read (memory :> bytes64(word_add sbase (word 128))) s;
   read R8 s;
   read (memory :> bytes64(word_add sbase (word 136))) s;
   read RBX s]";;

let keccak_inv = parse_term ("\\i s.
  (read RSP s = word_add sbase (word 120) /\\
   read (memory :> bytes64(word_add sbase (word 256))) s = returnaddress /\\
   read (memory :> bytes64(word_add sbase (word 248))) s = r15_init /\\
   read (memory :> bytes64(word_add sbase (word 240))) s = r14_init /\\
   read (memory :> bytes64(word_add sbase (word 232))) s = r13_init /\\
   read (memory :> bytes64(word_add sbase (word 224))) s = r12_init /\\
   read (memory :> bytes64(word_add sbase (word 216))) s = rbp_init /\\
   read (memory :> bytes64(word_add sbase (word 208))) s = rbx_init /\\
   read (memory :> bytes64(word_add sbase (word 200))) s = a /\\
   read (memory :> bytes64 sbase) s = word_add (word rc) (word(16 * i)) /\\
   read (memory :> bytes(word rc,192)) s = num_of_wordlist round_constants /\\
   " ^ keccak_lanes_str ^ " = keccak (2 * i) A) /\\
  (0 < i
   ==> read R9 s = read (memory :> bytes64(word_add sbase (word 120))) s /\\
       read RCX s = read (memory :> bytes64(word_add sbase (word 136))) s /\\
       (read ZF s <=> i = 12))");;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!a rc A pc stackpointer returnaddress.
        riprel32_within_bounds rc (pc + 0xf4) /\
        riprel32_within_bounds (rc + 192) (pc + 0x7db) /\
        ALL (nonoverlapping (word_sub stackpointer (word 256),264))
            [(word pc,0x8ce); (a,200); (word rc,192)] /\
        nonoverlapping (a,200) (word pc,0x8ce)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    (mlkem_native_keccakf1600_permute_gcc12_O2_mc pc rc) /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  bytes_loaded s (word rc)
                    mlkem_native_keccakf1600_permute_gcc12_O2_data /\
                  wordlist_from_memory(a,25) s = A)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  wordlist_from_memory(a,25) s = keccak 24 A)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,200);
                         memory :> bytes(word_sub stackpointer (word 256),
                                         256)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `rc:num`; `A:int64 list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 256 THEN
  MAP_EVERY X_GEN_TAC [`sbase:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The register saves ***)

  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)] THEN

  (*** The loop, with the test at the end, doing two rounds each time ***)

  ENSURES_WHILE_PUP_TAC `12` `pc + 0x100` `pc + 0x7e6` keccak_inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant, including the table address ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP KECCAK_RC_BYTES) THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (a,8 * 25)) s0` THEN
    FIRST_ASSUM(MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC (1--53) THEN
    MP_TAC(CONJUNCT1(SPECL [`pc:num`; `244`; `0`; `rc:num`]
      RIP_REL_ADDR_FOLD)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC (54--55) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[keccak; MULT_CLAUSES; WORD_ADD_0; LT_REFL];

    (*** Preservation of the invariant, including the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_STATELIST_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ISPECL [`word rc:int64`; `round_constants`; `24`; `2 * i + 1`;
                   `s0:x86state`] READ_MEMORY_BYTES64_NUM_OF_WORDLIST) THEN
    MP_TAC(ISPECL [`word rc:int64`; `round_constants`; `24`; `2 * i`;
                   `s0:x86state`] READ_MEMORY_BYTES64_NUM_OF_WORDLIST) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ASM_REWRITE_TAC[LENGTH_ROUND_CONSTANTS] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 12 ==> 2 * i < 24 /\ 2 * i + 1 < 24`] THEN
    REWRITE_TAC[ARITH_RULE
     `8 * (2 * i) = 16 * i /\ 8 * (2 * i + 1) = 16 * i + 8`] THEN
    REPEAT DISCH_TAC THEN
    KECCAK_INTRO_ABBREVS_TAC THEN
    MAP_EVERY (fun n ->
      X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC [n] THEN
      KECCAK_ABBREV_STEP_TAC) (1--498) THEN
    MP_TAC(SPECL [`pc:num`; `rc:num`] KECCAK_RC_END_FOLD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s498" THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      KECCAK_SECOND_ROUND_TAC;
      DISCH_TAC THEN REWRITE_TAC[WORD_ADD] THEN
      REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
        word_sub x (word_add y z)`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 12 ==> 16 * i + 16 < 18446744073709551616`] THEN
      ASM_ARITH_TAC];

    (*** The trivial loop-back goal ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The writeback tail ***)

    GHOST_STATELIST_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC (1--51) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for the   *)
(* AArch64 code. The loop is that of the correctness proof, but with the     *)
(* loop test and branch at the end of the body, as ENSURES_EVENTS_WHILE_UP2_ *)
(* TAC requires; the events of the last iteration include the branch out of  *)
(* the loop. The theorem of constant time and memory safety alone follows.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let keccak_inv_cs = parse_term ("\\i s.
   read RSP s = word_add sbase (word 120) /\\
   read (memory :> bytes64(word_add sbase (word 256))) s = returnaddress /\\
   read (memory :> bytes64(word_add sbase (word 248))) s = r15_init /\\
   read (memory :> bytes64(word_add sbase (word 240))) s = r14_init /\\
   read (memory :> bytes64(word_add sbase (word 232))) s = r13_init /\\
   read (memory :> bytes64(word_add sbase (word 224))) s = r12_init /\\
   read (memory :> bytes64(word_add sbase (word 216))) s = rbp_init /\\
   read (memory :> bytes64(word_add sbase (word 208))) s = rbx_init /\\
   read (memory :> bytes64(word_add sbase (word 200))) s = a /\\
   read (memory :> bytes64 sbase) s = word_add (word rc) (word(16 * i)) /\\
   read (memory :> bytes(word rc,192)) s = num_of_wordlist round_constants /\\
   " ^ keccak_lanes_str ^ " = keccak (2 * i) A /\\
   (0 < i
    ==> read R9 s = read (memory :> bytes64(word_add sbase (word 120))) s /\\
        read RCX s = read (memory :> bytes64(word_add sbase (word 136))) s)");;

let KECCAK_CS_TEST = prove
 (`!rc i. i < 12
          ==> (val(word_sub (word(rc + 192))
                            (word_add (word_add (word rc) (word (16 * i)))
                                      (word 16)):int64) = 0 <=>
               ~(i + 1 < 12))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_ADD] THEN
  REWRITE_TAC[WORD_RULE
   `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
    word_sub x (word_add y z)`] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `i < 12 ==> 16 * i + 16 < 18446744073709551616`] THEN
  ASM_ARITH_TAC);;

let KECCAK_CS_INTRO_TAC =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (rc:num) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     APPEND (f_ev_epil a rc pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL 12
          (\i. f_ev_loop a rc pc stackpointer returnaddress i))
        (f_ev_prol a rc pc stackpointer returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `rc:num`; `A:int64 list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 256 THEN
  MAP_EVERY X_GEN_TAC [`sbase:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)];;

let KECCAK_CS_INIT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP KECCAK_RC_BYTES) THEN
  BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (a,8 * 25)) s0` THEN
  FIRST_ASSUM(MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC (1--53) THEN
  MP_TAC(CONJUNCT1(SPECL [`pc:num`; `244`; `0`; `rc:num`]
    RIP_REL_ADDR_FOLD)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC (54--55) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[keccak; MULT_CLAUSES; WORD_ADD_0; LT_REFL] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KECCAK_CS_BODY1_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  GHOST_STATELIST_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MP_TAC(ISPECL [`word rc:int64`; `round_constants`; `24`; `2 * i + 1`;
                 `s0:x86state`] READ_MEMORY_BYTES64_NUM_OF_WORDLIST) THEN
  MP_TAC(ISPECL [`word rc:int64`; `round_constants`; `24`; `2 * i`;
                 `s0:x86state`] READ_MEMORY_BYTES64_NUM_OF_WORDLIST) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[LENGTH_ROUND_CONSTANTS] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 12 ==> 2 * i < 24 /\ 2 * i + 1 < 24`] THEN
  REWRITE_TAC[ARITH_RULE
   `8 * (2 * i) = 16 * i /\ 8 * (2 * i + 1) = 16 * i + 8`] THEN
  REPEAT DISCH_TAC THEN
  KECCAK_INTRO_ABBREVS_TAC THEN
  MAP_EVERY (fun n ->
    X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC [n] THEN
    KECCAK_ABBREV_STEP_TAC) (1--498) THEN
  MP_TAC(SPECL [`pc:num`; `rc:num`] KECCAK_RC_END_FOLD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`rc:num`; `i:num`] KECCAK_CS_TEST)
                                 (ASSUME `i < 12`)]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC [499];;

let KECCAK_CS_BODY2_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s499" THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [KECCAK_SECOND_ROUND_TAC; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KECCAK_CS_TAIL_TAC =
  REWRITE_TAC[] THEN GHOST_STATELIST_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC (1--50) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_SUBROUTINE_FULL = prove
 (`exists f_events.
       forall e a rc A pc stackpointer returnaddress.
           riprel32_within_bounds rc (pc + 0xf4) /\
           riprel32_within_bounds (rc + 192) (pc + 0x7db) /\
           ALL (nonoverlapping (word_sub stackpointer (word 256),264))
               [(word pc,0x8ce); (a,200); (word rc,192)] /\
           nonoverlapping (a,200) (word pc,0x8ce)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      (mlkem_native_keccakf1600_permute_gcc12_O2_mc pc rc) /\
                    read RIP s = word pc /\
                    bytes_loaded s (word rc)
                      mlkem_native_keccakf1600_permute_gcc12_O2_data /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    wordlist_from_memory(a,25) s = A /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    wordlist_from_memory(a,25) s = keccak 24 A /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a rc pc
                                (word_sub stackpointer (word 256))
                                returnaddress /\
                         memaccess_inbounds e2
                           [a,200; word rc,192;
                            word_sub stackpointer (word 256),264]
                           [a,200; word_sub stackpointer (word 256),256]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,200);
                           memory :> bytes(word_sub stackpointer (word 256),
                                           256)])`,
  KECCAK_CS_INTRO_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `12` `pc + 0x100` `pc + 0x7ec`
   keccak_inv_cs THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    KECCAK_CS_INIT_TAC;
    KECCAK_CS_BODY1_TAC THEN KECCAK_CS_BODY2_TAC;
    KECCAK_CS_TAIL_TAC]);;

let ENSURES_WEAKEN_RULE = prove
 (`!step P P' Q Q' C:A->A->bool.
        ensures step P Q C
        ==> (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s)
            ==> ensures step P' Q' C`,
  MESON_TAC[ENSURES_PREPOSTCONDITION_THM]);;

(*** The specification is that of mk_safety_spec for the C signature of
 *** mlkem_keccakf1600_permute, with the table of round constants as a
 *** read-only object, and with the return address in the stack region
 *** that is read and the final stack pointer as for the other subroutines.
 ***)

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e a rc pc stackpointer returnaddress.
           riprel32_within_bounds rc (pc + 0xf4) /\
           riprel32_within_bounds (rc + 192) (pc + 0x7db) /\
           ALL (nonoverlapping (word_sub stackpointer (word 256),264))
               [(word pc,0x8ce); (a,200); (word rc,192)] /\
           nonoverlapping (a,200) (word pc,0x8ce)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      (mlkem_native_keccakf1600_permute_gcc12_O2_mc pc rc) /\
                    read RIP s = word pc /\
                    bytes_loaded s (word rc)
                      mlkem_native_keccakf1600_permute_gcc12_O2_data /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a rc pc
                                (word_sub stackpointer (word 256))
                                returnaddress /\
                         memaccess_inbounds e2
                           [a,200; word rc,192;
                            word_sub stackpointer (word 256),264]
                           [a,200; word_sub stackpointer (word 256),256]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,200);
                           memory :> bytes(word_sub stackpointer (word 256),
                                           256)])`,
  MP_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `rc:num`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  DISCH_TAC THEN
  GHOST_INTRO_TAC `A:int64 list`
   `wordlist_from_memory(a,25):x86state->int64 list` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `rc:num`; `A:int64 list`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image, at address 0x3e70, with the table of    *)
(* round constants at 0x80c0 (see mlkem_native_libmlkem_gcc12_O2.ml).        *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_keccakf1600_permute_gcc12_O2_mc
    0x3e70 [0x80c0];;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_RC_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE
    (hd mlkem_native_keccakf1600_permute_gcc12_O2_data) 0x80c0;;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a A pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 256),264))
            [(word pc,0x82a0); (a,200)] /\
        nonoverlapping (a,200) (word pc,0x82a0)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x3e70) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  wordlist_from_memory(a,25) s = A)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  wordlist_from_memory(a,25) s = keccak 24 A)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,200);
                         memory :> bytes(word_sub stackpointer (word 256),
                                         256)])`,
  MLKEM_NATIVE_IMAGE_TAC
   (INST [`pc + 0x3e70`,`pc:num`; `pc + 0x80c0`,`rc:num`]
     (SPEC_ALL MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_SUBROUTINE_CORRECT))
   [MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IN_IMAGE;
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_RC_IN_IMAGE]);;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (word_sub stackpointer (word 256),264))
               [(word pc,0x82a0); (a,200)] /\
           nonoverlapping (a,200) (word pc,0x82a0)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x3e70) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc
                                (word_sub stackpointer (word 256))
                                returnaddress /\
                         memaccess_inbounds e2
                           [a,200; word (pc + 0x80c0),192;
                            word_sub stackpointer (word 256),264]
                           [a,200; word_sub stackpointer (word 256),256]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,200);
                           memory :> bytes(word_sub stackpointer (word 256),
                                           256)])`,
  MLKEM_NATIVE_IMAGE_SAFE_TAC
   MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_SUBROUTINE_SAFE
   [`pc + 0x3e70`,`pc:num`; `pc + 0x80c0`,`rc:num`]
   [MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IN_IMAGE;
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_RC_IN_IMAGE]);;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (`exists f_events.
       forall e a A pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (word_sub stackpointer (word 256),264))
               [(word pc,0x82a0); (a,200)] /\
           nonoverlapping (a,200) (word pc,0x82a0)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x3e70) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    wordlist_from_memory(a,25) s = A /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    wordlist_from_memory(a,25) s = keccak 24 A /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc
                                (word_sub stackpointer (word 256))
                                returnaddress /\
                         memaccess_inbounds e2
                           [a,200; word (pc + 0x80c0),192;
                            word_sub stackpointer (word 256),264]
                           [a,200; word_sub stackpointer (word 256),256]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,200);
                           memory :> bytes(word_sub stackpointer (word 256),
                                           256)])`,
  MLKEM_NATIVE_IMAGE_SAFE_TAC
   MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_SUBROUTINE_FULL
   [`pc + 0x3e70`,`pc:num`; `pc + 0x80c0`,`rc:num`]
   [MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IN_IMAGE;
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_RC_IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* The same for the state as a 1600-bit word, read by wbytes, with the       *)
(* permutation keccak_f1600 of common/fips202.ml (see                        *)
(* utils/keccak_fips202.ml), and tactics for callers, which carry the state  *)
(* between calls as 200 bytes.                                               *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/utils/keccak_fips202.ml";;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600 =
  prove
 (`!a (S:1600 word) pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (word_sub stackpointer (word 256),264))
            [(word pc,0x82a0); (a,200)] /\
        nonoverlapping (a,200) (word pc,0x82a0)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x3e70) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> wbytes a) s = S)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes a) s = keccak_f1600 S)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,200);
                         memory :> bytes(word_sub stackpointer (word 256),
                                         256)])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `wordlist_of_num 25 (val(S:1600 word)):int64 list`;
                `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (MESON[ENSURES_PREPOSTCONDITION_THM]
   `ensures step P Q C
    ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
        ==> ensures step P' Q' C`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_KECCAK] THEN SIMP_TAC[];
    MESON_TAC[KECCAK_F1600_MEMORY]]);;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600 =
  prove
 (`exists f_events.
       forall e a (S:1600 word) pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (word_sub stackpointer (word 256),264))
               [(word pc,0x82a0); (a,200)] /\
           nonoverlapping (a,200) (word pc,0x82a0)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x3e70) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read (memory :> wbytes a) s = S /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    read (memory :> wbytes a) s = keccak_f1600 S /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc
                                (word_sub stackpointer (word 256))
                                returnaddress /\
                         memaccess_inbounds e2
                           [a,200; word (pc + 0x80c0),192;
                            word_sub stackpointer (word 256),264]
                           [a,200; word_sub stackpointer (word 256),256]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,200);
                           memory :> bytes(word_sub stackpointer (word 256),
                                           256)])`,
  MP_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`;
    `wordlist_of_num 25 (val(S:1600 word)):int64 list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (MESON[ENSURES_PREPOSTCONDITION_THM]
   `ensures step P Q C
    ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
        ==> ensures step P' Q' C`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_KECCAK] THEN SIMP_TAC[];
    MESON_TAC[KECCAK_F1600_MEMORY]]);;

(*** The state at a as a 1600-bit word, from it as 200 bytes ***)

let KECCAK_STATE_AT_TAC a =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),_)),
           Comb(Const("val",_),_))
        when aa = mk_pair(a,`200`) ->
          ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] th)
    | _ -> NO_TAC);;

(*** Apply ttac to the 1600-bit word for the state at a ***)

let KECCAK_STATE_THEN a (ttac:term->tactic) =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("wbytes",_),aa))),_)),v)
        when aa = a -> ttac v
    | _ -> NO_TAC);;
