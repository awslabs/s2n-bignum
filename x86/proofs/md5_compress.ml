(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* MD5 block compression, scalar x86-64 (md5_compress).                      *)
(*                                                                           *)
(* The function processes num_blocks 64-byte input blocks, updating the      *)
(* 4-doubleword MD5 chaining state in place.                                 *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/md5_bridge.ml";;  (* Layer-1 spec + Layer-2 bridges *)

(**** print_literal_from_elf "x86/md5/md5_compress.o";;
 ****)

let md5_compress_mc = define_assert_from_elf
  "md5_compress_mc" "x86/md5/md5_compress.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x89; 0xfd;        (* MOV (% rbp) (% rdi) *)
  0x48; 0xc1; 0xe2; 0x06;  (* SHL (% rdx) (Imm8 (word 6)) *)
  0x48; 0x8d; 0x3c; 0x16;  (* LEA (% rdi) (%%% (rsi,0,rdx)) *)
  0x8b; 0x45; 0x00;        (* MOV (% eax) (Memop Doubleword (%% (rbp,0))) *)
  0x8b; 0x5d; 0x04;        (* MOV (% ebx) (Memop Doubleword (%% (rbp,4))) *)
  0x8b; 0x4d; 0x08;        (* MOV (% ecx) (Memop Doubleword (%% (rbp,8))) *)
  0x8b; 0x55; 0x0c;        (* MOV (% edx) (Memop Doubleword (%% (rbp,12))) *)
  0x48; 0x39; 0xfe;        (* CMP (% rsi) (% rdi) *)
  0x0f; 0x84; 0xa2; 0x08; 0x00; 0x00;
                           (* JE (Imm32 (word 2210)) *)
  0x41; 0x89; 0xc0;        (* MOV (% r8d) (% eax) *)
  0x41; 0x89; 0xd9;        (* MOV (% r9d) (% ebx) *)
  0x41; 0x89; 0xce;        (* MOV (% r14d) (% ecx) *)
  0x41; 0x89; 0xd7;        (* MOV (% r15d) (% edx) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x78; 0xa4; 0x6a; 0xd7;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &680876936)) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x04;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,4))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x07;        (* ROL (% eax) (Imm8 (word 7)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x56; 0xb7; 0xc7; 0xe8;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &389564586)) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x08;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,8))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0c;        (* ROL (% edx) (Imm8 (word 12)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0xdb; 0x70; 0x20; 0x24;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,&606105819)) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x0c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,12))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x11;        (* ROL (% ecx) (Imm8 (word 17)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0xee; 0xce; 0xbd; 0xc1;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &1044525330)) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x8b; 0x56; 0x10;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,16))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x16;        (* ROL (% ebx) (Imm8 (word 22)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0xaf; 0x0f; 0x7c; 0xf5;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &176418897)) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x14;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,20))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x07;        (* ROL (% eax) (Imm8 (word 7)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x2a; 0xc6; 0x87; 0x47;
                           (* LEA (% edx) (%%%% (rdx,0,r10,&1200080426)) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x18;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,24))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0c;        (* ROL (% edx) (Imm8 (word 12)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x13; 0x46; 0x30; 0xa8;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &1473231341)) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x1c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,28))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x11;        (* ROL (% ecx) (Imm8 (word 17)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x01; 0x95; 0x46; 0xfd;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &45705983)) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x8b; 0x56; 0x20;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,32))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x16;        (* ROL (% ebx) (Imm8 (word 22)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0xd8; 0x98; 0x80; 0x69;
                           (* LEA (% eax) (%%%% (rax,0,r10,&1770035416)) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x24;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,36))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x07;        (* ROL (% eax) (Imm8 (word 7)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0xaf; 0xf7; 0x44; 0x8b;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &1958414417)) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x28;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,40))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0c;        (* ROL (% edx) (Imm8 (word 12)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0xb1; 0x5b; 0xff; 0xff;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &42063)) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x2c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,44))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x11;        (* ROL (% ecx) (Imm8 (word 17)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0xbe; 0xd7; 0x5c; 0x89;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &1990404162)) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x8b; 0x56; 0x30;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,48))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x16;        (* ROL (% ebx) (Imm8 (word 22)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x22; 0x11; 0x90; 0x6b;
                           (* LEA (% eax) (%%%% (rax,0,r10,&1804603682)) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x34;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,52))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x07;        (* ROL (% eax) (Imm8 (word 7)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x93; 0x71; 0x98; 0xfd;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &40341101)) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x38;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,56))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0c;        (* ROL (% edx) (Imm8 (word 12)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x8e; 0x43; 0x79; 0xa6;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &1502002290)) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x3c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,60))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x11;        (* ROL (% ecx) (Imm8 (word 17)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x21; 0x08; 0xb4; 0x49;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,&1236535329)) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x16;        (* ROL (% ebx) (Imm8 (word 22)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x44; 0x8b; 0x56; 0x04;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,4))) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x84; 0x10; 0x62; 0x25; 0x1e; 0xf6;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &165796510)) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x18;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,24))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x44; 0x01; 0xe0;        (* ADD (% eax) (% r12d) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0xc1; 0xc0; 0x05;        (* ROL (% eax) (Imm8 (word 5)) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x94; 0x12; 0x40; 0xb3; 0x40; 0xc0;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &1069501632)) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x2c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,44))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x44; 0x01; 0xe2;        (* ADD (% edx) (% r12d) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0xc1; 0xc2; 0x09;        (* ROL (% edx) (Imm8 (word 9)) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x8c; 0x11; 0x51; 0x5a; 0x5e; 0x26;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,&643717713)) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x44; 0x01; 0xe1;        (* ADD (% ecx) (% r12d) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0xc1; 0xc1; 0x0e;        (* ROL (% ecx) (Imm8 (word 14)) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x9c; 0x13; 0xaa; 0xc7; 0xb6; 0xe9;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &373897302)) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x14;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,20))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x44; 0x01; 0xe3;        (* ADD (% ebx) (% r12d) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0xc1; 0xc3; 0x14;        (* ROL (% ebx) (Imm8 (word 20)) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x84; 0x10; 0x5d; 0x10; 0x2f; 0xd6;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &701558691)) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x28;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,40))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x44; 0x01; 0xe0;        (* ADD (% eax) (% r12d) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0xc1; 0xc0; 0x05;        (* ROL (% eax) (Imm8 (word 5)) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x94; 0x12; 0x53; 0x14; 0x44; 0x02;
                           (* LEA (% edx) (%%%% (rdx,0,r10,&38016083)) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x3c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,60))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x44; 0x01; 0xe2;        (* ADD (% edx) (% r12d) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0xc1; 0xc2; 0x09;        (* ROL (% edx) (Imm8 (word 9)) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x8c; 0x11; 0x81; 0xe6; 0xa1; 0xd8;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &660478335)) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x44; 0x8b; 0x56; 0x10;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,16))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x44; 0x01; 0xe1;        (* ADD (% ecx) (% r12d) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0xc1; 0xc1; 0x0e;        (* ROL (% ecx) (Imm8 (word 14)) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x9c; 0x13; 0xc8; 0xfb; 0xd3; 0xe7;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &405537848)) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x24;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,36))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x44; 0x01; 0xe3;        (* ADD (% ebx) (% r12d) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0xc1; 0xc3; 0x14;        (* ROL (% ebx) (Imm8 (word 20)) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x84; 0x10; 0xe6; 0xcd; 0xe1; 0x21;
                           (* LEA (% eax) (%%%% (rax,0,r10,&568446438)) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x38;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,56))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x44; 0x01; 0xe0;        (* ADD (% eax) (% r12d) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0xc1; 0xc0; 0x05;        (* ROL (% eax) (Imm8 (word 5)) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x94; 0x12; 0xd6; 0x07; 0x37; 0xc3;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &1019803690)) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x0c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,12))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x44; 0x01; 0xe2;        (* ADD (% edx) (% r12d) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0xc1; 0xc2; 0x09;        (* ROL (% edx) (Imm8 (word 9)) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x8c; 0x11; 0x87; 0x0d; 0xd5; 0xf4;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &187363961)) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x44; 0x8b; 0x56; 0x20;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,32))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x44; 0x01; 0xe1;        (* ADD (% ecx) (% r12d) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0xc1; 0xc1; 0x0e;        (* ROL (% ecx) (Imm8 (word 14)) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x9c; 0x13; 0xed; 0x14; 0x5a; 0x45;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,&1163531501)) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x44; 0x8b; 0x56; 0x34;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,52))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x44; 0x01; 0xe3;        (* ADD (% ebx) (% r12d) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0xc1; 0xc3; 0x14;        (* ROL (% ebx) (Imm8 (word 20)) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x84; 0x10; 0x05; 0xe9; 0xe3; 0xa9;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &1444681467)) *)
  0x41; 0x21; 0xdc;        (* AND (% r12d) (% ebx) *)
  0x41; 0x21; 0xcb;        (* AND (% r11d) (% ecx) *)
  0x44; 0x8b; 0x56; 0x08;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,8))) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x44; 0x01; 0xe0;        (* ADD (% eax) (% r12d) *)
  0x41; 0x89; 0xcc;        (* MOV (% r12d) (% ecx) *)
  0xc1; 0xc0; 0x05;        (* ROL (% eax) (Imm8 (word 5)) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x94; 0x12; 0xf8; 0xa3; 0xef; 0xfc;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &51403784)) *)
  0x41; 0x21; 0xc4;        (* AND (% r12d) (% eax) *)
  0x41; 0x21; 0xdb;        (* AND (% r11d) (% ebx) *)
  0x44; 0x8b; 0x56; 0x1c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,28))) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x44; 0x01; 0xe2;        (* ADD (% edx) (% r12d) *)
  0x41; 0x89; 0xdc;        (* MOV (% r12d) (% ebx) *)
  0xc1; 0xc2; 0x09;        (* ROL (% edx) (Imm8 (word 9)) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x8c; 0x11; 0xd9; 0x02; 0x6f; 0x67;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,&1735328473)) *)
  0x41; 0x21; 0xd4;        (* AND (% r12d) (% edx) *)
  0x41; 0x21; 0xc3;        (* AND (% r11d) (% eax) *)
  0x44; 0x8b; 0x56; 0x30;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,48))) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x44; 0x01; 0xe1;        (* ADD (% ecx) (% r12d) *)
  0x41; 0x89; 0xc4;        (* MOV (% r12d) (% eax) *)
  0xc1; 0xc1; 0x0e;        (* ROL (% ecx) (Imm8 (word 14)) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0xf7; 0xd3;        (* NOT (% r11d) *)
  0x42; 0x8d; 0x9c; 0x13; 0x8a; 0x4c; 0x2a; 0x8d;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &1926607734)) *)
  0x41; 0x21; 0xcc;        (* AND (% r12d) (% ecx) *)
  0x41; 0x21; 0xd3;        (* AND (% r11d) (% edx) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x44; 0x01; 0xe3;        (* ADD (% ebx) (% r12d) *)
  0x41; 0x89; 0xd4;        (* MOV (% r12d) (% edx) *)
  0xc1; 0xc3; 0x14;        (* ROL (% ebx) (Imm8 (word 20)) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x44; 0x8b; 0x56; 0x14;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,20))) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x42; 0x39; 0xfa; 0xff;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &378558)) *)
  0x44; 0x8b; 0x56; 0x20;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,32))) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x04;        (* ROL (% eax) (Imm8 (word 4)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x81; 0xf6; 0x71; 0x87;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &2022574463)) *)
  0x44; 0x8b; 0x56; 0x2c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,44))) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0b;        (* ROL (% edx) (Imm8 (word 11)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x22; 0x61; 0x9d; 0x6d;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,&1839030562)) *)
  0x44; 0x8b; 0x56; 0x38;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,56))) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x10;        (* ROL (% ecx) (Imm8 (word 16)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x0c; 0x38; 0xe5; 0xfd;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &35309556)) *)
  0x44; 0x8b; 0x56; 0x04;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,4))) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x17;        (* ROL (% ebx) (Imm8 (word 23)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x44; 0xea; 0xbe; 0xa4;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &1530992060)) *)
  0x44; 0x8b; 0x56; 0x10;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,16))) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x04;        (* ROL (% eax) (Imm8 (word 4)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0xa9; 0xcf; 0xde; 0x4b;
                           (* LEA (% edx) (%%%% (rdx,0,r10,&1272893353)) *)
  0x44; 0x8b; 0x56; 0x1c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,28))) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0b;        (* ROL (% edx) (Imm8 (word 11)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x60; 0x4b; 0xbb; 0xf6;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &155497632)) *)
  0x44; 0x8b; 0x56; 0x28;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,40))) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x10;        (* ROL (% ecx) (Imm8 (word 16)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x70; 0xbc; 0xbf; 0xbe;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &1094730640)) *)
  0x44; 0x8b; 0x56; 0x34;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,52))) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x17;        (* ROL (% ebx) (Imm8 (word 23)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0xc6; 0x7e; 0x9b; 0x28;
                           (* LEA (% eax) (%%%% (rax,0,r10,&681279174)) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x04;        (* ROL (% eax) (Imm8 (word 4)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0xfa; 0x27; 0xa1; 0xea;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &358537222)) *)
  0x44; 0x8b; 0x56; 0x0c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,12))) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0b;        (* ROL (% edx) (Imm8 (word 11)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x85; 0x30; 0xef; 0xd4;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &722521979)) *)
  0x44; 0x8b; 0x56; 0x18;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,24))) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x10;        (* ROL (% ecx) (Imm8 (word 16)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x05; 0x1d; 0x88; 0x04;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,&76029189)) *)
  0x44; 0x8b; 0x56; 0x24;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,36))) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x17;        (* ROL (% ebx) (Imm8 (word 23)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x39; 0xd0; 0xd4; 0xd9;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &640364487)) *)
  0x44; 0x8b; 0x56; 0x30;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,48))) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0xc1; 0xc0; 0x04;        (* ROL (% eax) (Imm8 (word 4)) *)
  0x41; 0x89; 0xdb;        (* MOV (% r11d) (% ebx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0xe5; 0x99; 0xdb; 0xe6;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &421815835)) *)
  0x44; 0x8b; 0x56; 0x3c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,60))) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0xc1; 0xc2; 0x0b;        (* ROL (% edx) (Imm8 (word 11)) *)
  0x41; 0x89; 0xc3;        (* MOV (% r11d) (% eax) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0xf8; 0x7c; 0xa2; 0x1f;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,&530742520)) *)
  0x44; 0x8b; 0x56; 0x08;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,8))) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0xc1; 0xc1; 0x10;        (* ROL (% ecx) (Imm8 (word 16)) *)
  0x41; 0x89; 0xd3;        (* MOV (% r11d) (% edx) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x65; 0x56; 0xac; 0xc4;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &995338651)) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0xc1; 0xc3; 0x17;        (* ROL (% ebx) (Imm8 (word 23)) *)
  0x41; 0x89; 0xcb;        (* MOV (% r11d) (% ecx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x42; 0x8d; 0x84; 0x10; 0x44; 0x22; 0x29; 0xf4;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &198630844)) *)
  0x41; 0x09; 0xdb;        (* OR (% r11d) (% ebx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x44; 0x8b; 0x56; 0x1c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,28))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc0; 0x06;        (* ROL (% eax) (Imm8 (word 6)) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x97; 0xff; 0x2a; 0x43;
                           (* LEA (% edx) (%%%% (rdx,0,r10,&1126891415)) *)
  0x41; 0x09; 0xc3;        (* OR (% r11d) (% eax) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x38;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,56))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc2; 0x0a;        (* ROL (% edx) (Imm8 (word 10)) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0xa7; 0x23; 0x94; 0xab;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &1416354905)) *)
  0x41; 0x09; 0xd3;        (* OR (% r11d) (% edx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x14;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,20))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc1; 0x0f;        (* ROL (% ecx) (Imm8 (word 15)) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x39; 0xa0; 0x93; 0xfc;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &57434055)) *)
  0x41; 0x09; 0xcb;        (* OR (% r11d) (% ecx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x30;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,48))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc3; 0x15;        (* ROL (% ebx) (Imm8 (word 21)) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0xc3; 0x59; 0x5b; 0x65;
                           (* LEA (% eax) (%%%% (rax,0,r10,&1700485571)) *)
  0x41; 0x09; 0xdb;        (* OR (% r11d) (% ebx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x44; 0x8b; 0x56; 0x0c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,12))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc0; 0x06;        (* ROL (% eax) (Imm8 (word 6)) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x92; 0xcc; 0x0c; 0x8f;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &1894986606)) *)
  0x41; 0x09; 0xc3;        (* OR (% r11d) (% eax) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x28;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,40))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc2; 0x0a;        (* ROL (% edx) (Imm8 (word 10)) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x7d; 0xf4; 0xef; 0xff;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &1051523)) *)
  0x41; 0x09; 0xd3;        (* OR (% r11d) (% edx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x04;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,4))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc1; 0x0f;        (* ROL (% ecx) (Imm8 (word 15)) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0xd1; 0x5d; 0x84; 0x85;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &2054922799)) *)
  0x41; 0x09; 0xcb;        (* OR (% r11d) (% ecx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x20;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,32))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc3; 0x15;        (* ROL (% ebx) (Imm8 (word 21)) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x4f; 0x7e; 0xa8; 0x6f;
                           (* LEA (% eax) (%%%% (rax,0,r10,&1873313359)) *)
  0x41; 0x09; 0xdb;        (* OR (% r11d) (% ebx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x44; 0x8b; 0x56; 0x3c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,60))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc0; 0x06;        (* ROL (% eax) (Imm8 (word 6)) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0xe0; 0xe6; 0x2c; 0xfe;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &30611744)) *)
  0x41; 0x09; 0xc3;        (* OR (% r11d) (% eax) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x18;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,24))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc2; 0x0a;        (* ROL (% edx) (Imm8 (word 10)) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0x14; 0x43; 0x01; 0xa3;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,-- &1560198380)) *)
  0x41; 0x09; 0xd3;        (* OR (% r11d) (% edx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x34;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,52))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc1; 0x0f;        (* ROL (% ecx) (Imm8 (word 15)) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0xa1; 0x11; 0x08; 0x4e;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,&1309151649)) *)
  0x41; 0x09; 0xcb;        (* OR (% r11d) (% ecx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x10;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,16))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc3; 0x15;        (* ROL (% ebx) (Imm8 (word 21)) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x42; 0x8d; 0x84; 0x10; 0x82; 0x7e; 0x53; 0xf7;
                           (* LEA (% eax) (%%%% (rax,0,r10,-- &145523070)) *)
  0x41; 0x09; 0xdb;        (* OR (% r11d) (% ebx) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x44; 0x01; 0xd8;        (* ADD (% eax) (% r11d) *)
  0x44; 0x8b; 0x56; 0x2c;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,44))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc0; 0x06;        (* ROL (% eax) (Imm8 (word 6)) *)
  0x41; 0x31; 0xcb;        (* XOR (% r11d) (% ecx) *)
  0x01; 0xd8;              (* ADD (% eax) (% ebx) *)
  0x42; 0x8d; 0x94; 0x12; 0x35; 0xf2; 0x3a; 0xbd;
                           (* LEA (% edx) (%%%% (rdx,0,r10,-- &1120210379)) *)
  0x41; 0x09; 0xc3;        (* OR (% r11d) (% eax) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x08;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,8))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc2; 0x0a;        (* ROL (% edx) (Imm8 (word 10)) *)
  0x41; 0x31; 0xdb;        (* XOR (% r11d) (% ebx) *)
  0x01; 0xc2;              (* ADD (% edx) (% eax) *)
  0x42; 0x8d; 0x8c; 0x11; 0xbb; 0xd2; 0xd7; 0x2a;
                           (* LEA (% ecx) (%%%% (rcx,0,r10,&718787259)) *)
  0x41; 0x09; 0xd3;        (* OR (% r11d) (% edx) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x44; 0x01; 0xd9;        (* ADD (% ecx) (% r11d) *)
  0x44; 0x8b; 0x56; 0x24;  (* MOV (% r10d) (Memop Doubleword (%% (rsi,36))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc1; 0x0f;        (* ROL (% ecx) (Imm8 (word 15)) *)
  0x41; 0x31; 0xc3;        (* XOR (% r11d) (% eax) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x42; 0x8d; 0x9c; 0x13; 0x91; 0xd3; 0x86; 0xeb;
                           (* LEA (% ebx) (%%%% (rbx,0,r10,-- &343485551)) *)
  0x41; 0x09; 0xcb;        (* OR (% r11d) (% ecx) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x44; 0x01; 0xdb;        (* ADD (% ebx) (% r11d) *)
  0x44; 0x8b; 0x16;        (* MOV (% r10d) (Memop Doubleword (%% (rsi,0))) *)
  0x41; 0xbb; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% r11d) (Imm32 (word 4294967295)) *)
  0xc1; 0xc3; 0x15;        (* ROL (% ebx) (Imm8 (word 21)) *)
  0x41; 0x31; 0xd3;        (* XOR (% r11d) (% edx) *)
  0x01; 0xcb;              (* ADD (% ebx) (% ecx) *)
  0x44; 0x01; 0xc0;        (* ADD (% eax) (% r8d) *)
  0x44; 0x01; 0xcb;        (* ADD (% ebx) (% r9d) *)
  0x44; 0x01; 0xf1;        (* ADD (% ecx) (% r14d) *)
  0x44; 0x01; 0xfa;        (* ADD (% edx) (% r15d) *)
  0x48; 0x83; 0xc6; 0x40;  (* ADD (% rsi) (Imm8 (word 64)) *)
  0x48; 0x39; 0xfe;        (* CMP (% rsi) (% rdi) *)
  0x0f; 0x82; 0x5e; 0xf7; 0xff; 0xff;
                           (* JB (Imm32 (word 4294965086)) *)
  0x89; 0x45; 0x00;        (* MOV (Memop Doubleword (%% (rbp,0))) (% eax) *)
  0x89; 0x5d; 0x04;        (* MOV (Memop Doubleword (%% (rbp,4))) (% ebx) *)
  0x89; 0x4d; 0x08;        (* MOV (Memop Doubleword (%% (rbp,8))) (% ecx) *)
  0x89; 0x55; 0x0c;        (* MOV (Memop Doubleword (%% (rbp,12))) (% edx) *)
  0x4c; 0x8b; 0x3c; 0x24;  (* MOV (% r15) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x8b; 0x74; 0x24; 0x08;
                           (* MOV (% r14) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x8b; 0x64; 0x24; 0x10;
                           (* MOV (% r12) (Memop Quadword (%% (rsp,16))) *)
  0x48; 0x8b; 0x5c; 0x24; 0x18;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x8b; 0x6c; 0x24; 0x20;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x83; 0xc4; 0x28;  (* ADD (% rsp) (Imm8 (word 40)) *)
  0xc3                     (* RET *)
];;

(* Trimmed variant: strips the leading 4-byte ENDBR64.                       *)

let md5_compress_tmc =
  define_trimmed "md5_compress_tmc" md5_compress_mc;;

(* Core execution rule (trimmed, BUTLAST drops the final RET); used by the   *)
(* core _CORRECT proof, which runs from entry pc+0x8 to exit pc+0x8d6.       *)

let MD5_COMPRESS_EXEC =
  X86_MK_CORE_EXEC_RULE md5_compress_tmc;;

(* Full execution rule (untrimmed, ENDBR64 + RET included); used when        *)
(* wrapping the core theorem into the subroutine forms.                      *)

let MD5_COMPRESS_EXEC_FULL =
  X86_MK_EXEC_RULE md5_compress_mc;;

(* ========================================================================= *)
(* One-round `ensures` (smallest meaningful unit).                           *)
(*                                                                           *)
(* Round 0's instruction range, trimmed pc+0x37 .. pc+0x5a (10 insns):       *)
(*   mov %edx,%r11d ; xor %ecx,%r11d ; lea K0(%rax,%r10),%eax ;              *)
(*   and %ebx,%r11d ; xor %edx,%r11d ; mov 4(%rsi),%r10d(prefetch) ;         *)
(*   add %r11d,%eax ; rol $7,%eax ; mov %ecx,%r11d(rnd1 prep) ;              *)
(*   add %ebx,%eax                                                           *)
(* Validates stepping, the sign-extended LEA K-immediate, word_zx nesting,   *)
(* and the F bridge refold before scaling to 16-round segments.  No memory   *)
(* precondition: M[0] is supplied in R10 (the asm preloads it just before    *)
(* this range); the embedded M[1] prefetch and round-1 F-prep land in        *)
(* R10/R11 (both MAYCHANGE) and are discarded.  Register<->spec map at the   *)
(* boundary, since md5_round 0 m [a;b;c;d] = [d; newB; b; c]:                *)
(* RAX = newB = EL 1, RBX = b = EL 2, RCX = c = EL 3, RDX = d = EL 0         *)
(* (only RAX changes this round).                                            *)
(* ========================================================================= *)

(* Spec-side reduction: md5_round 0 with the i=0 table entries plugged in    *)
(* (K0 = 0xd76aa478, rotate 7, message index 0, group F).                    *)

let MD5_ROUND_0 = prove
 (`!a b c d m:int32 list.
     md5_round 0 m [a;b;c;d] =
     [d;
      word_add b
        (word_rol (word_add (word_add (word_add a (md5_f b c d))
                                      (word 0xd76aa478))
                            (EL 0 m)) 7);
      b; c]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[md5_round] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[md5_k; md5_rot; md5_msgidx] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

(* The round-0 LEA materializes K0 as the sign-extended 64-bit immediate     *)
(* 0xFFFFFFFFD76AA478; truncated back to 32 bits it is exactly K0.           *)

let MD5_LEA_K0 = prove
 (`word_zx (word 18446744073028674680 :int64) :int32 = word 0xd76aa478`,
  CONV_TAC WORD_BLAST);;

let MD5_COMPRESS_ROUND0 = prove
 (`!a b c d m pc.
     ensures x86
       (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
            read RIP s = word (pc + 0x37) /\
            read RAX s = word_zx (a:int32) /\
            read RBX s = word_zx (b:int32) /\
            read RCX s = word_zx (c:int32) /\
            read RDX s = word_zx (d:int32) /\
            read R10 s = word_zx (EL 0 (m:int32 list)))
       (\s. read RIP s = word (pc + 0x5a) /\
            read RAX s = word_zx (EL 1 (md5_round 0 m [a;b;c;d])) /\
            read RBX s = word_zx b /\
            read RCX s = word_zx c /\
            read RDX s = word_zx d)
       (MAYCHANGE [RIP; RAX; R10; R11] ,, MAYCHANGE SOME_FLAGS ,,
        MAYCHANGE [events])`,
  REWRITE_TAC[MD5_ROUND_0; SOME_FLAGS] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_COMPRESS_EXEC (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (* Remaining goal: the RAX word identity.  Drop the (self-contained) flag  *)
  (* hypotheses, collapse the word_zx/word_sx packaging to 32 bits, rewrite  *)
  (* the LEA immediate to K0, refold F via the bridge, then close the        *)
  (* add-ring identity around word_rol with WORD_RULE.                       *)
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_ADD; WORD_VAL] THEN
  SIMP_TAC[WORD_SX_ZX; WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  SIMP_TAC[WORD_ZX_ADD; WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  REWRITE_TAC[WORD_VAL] THEN
  SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  REWRITE_TAC[MD5_LEA_K0; MD5_F_BRIDGE] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC RAND_CONV [WORD_ADD_SYM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* Rounds 0..15 (the F group) with bytes32 LE message loads.                 *)
(*                                                                           *)
(* A single 146-insn straight-line ensures term-explodes during X86_STEPS    *)
(* (the 16th round nests 16 word_rols deep), so the range is split at the    *)
(* 4-round boundaries -- exactly where the register<->spec map returns to    *)
(* the identity ((RAX,RBX,RCX,RDX) = EL 0..3 of md5_rounds(4k)) -- and the   *)
(* four legs are stitched inline with ENSURES_SEQUENCE_TAC (each leg         *)
(* re-simulated; composing standalone segment lemmas instead hits the        *)
(* bytes_loaded leg-alignment trap).                                         *)
(*                                                                           *)
(* SOFTWARE-PIPELINED R10/R11.  The asm prefetches the next rounds message   *)
(* word into R10 mid-round and emits the next rounds F-prep mov %edx,%r11d   *)
(* in the previous rounds tail, so at a 4-round boundary BOTH are live:      *)
(* the intermediate predicates carry R10 = EL (4k) m and R11 = EL 3 of       *)
(* md5_rounds(4k).  The final R0_15 postcondition omits R10/R11 (dont-care   *)
(* at the seam: the G group reloads both at entry).                          *)
(*                                                                           *)
(* Per-round spec machinery, generated as OCaml arrays to avoid 64x          *)
(* copy-paste. md5_round_red.(i) reduces `md5_round i m [a;b;c;d]` to a      *)
(* concrete 4-word list (K/rotate/msgidx plugged in); md5_lea_k.(i)          *)
(* discharges the asm LEA's sign-extended 64-bit K[i] immediate truncated    *)
(* back to 32 bits.  Same conv chain as MD5_ROUND_0/MD5_LEA_K0.              *)
(* ========================================================================= *)

(* All 64 RFC-1321 additive constants (= the spec md5_k table), round order. *)
let md5_k_vals = [|
  0xd76aa478; 0xe8c7b756; 0x242070db; 0xc1bdceee;
  0xf57c0faf; 0x4787c62a; 0xa8304613; 0xfd469501;
  0x698098d8; 0x8b44f7af; 0xffff5bb1; 0x895cd7be;
  0x6b901122; 0xfd987193; 0xa679438e; 0x49b40821;
  0xf61e2562; 0xc040b340; 0x265e5a51; 0xe9b6c7aa;
  0xd62f105d; 0x02441453; 0xd8a1e681; 0xe7d3fbc8;
  0x21e1cde6; 0xc33707d6; 0xf4d50d87; 0x455a14ed;
  0xa9e3e905; 0xfcefa3f8; 0x676f02d9; 0x8d2a4c8a;
  0xfffa3942; 0x8771f681; 0x6d9d6122; 0xfde5380c;
  0xa4beea44; 0x4bdecfa9; 0xf6bb4b60; 0xbebfbc70;
  0x289b7ec6; 0xeaa127fa; 0xd4ef3085; 0x04881d05;
  0xd9d4d039; 0xe6db99e5; 0x1fa27cf8; 0xc4ac5665;
  0xf4292244; 0x432aff97; 0xab9423a7; 0xfc93a039;
  0x655b59c3; 0x8f0ccc92; 0xffeff47d; 0x85845dd1;
  0x6fa87e4f; 0xfe2ce6e0; 0xa3014314; 0x4e0811a1;
  0xf7537e82; 0xbd3af235; 0x2ad7d2bb; 0xeb86d391 |];;

(* K[i] as the 64-bit value the LEA displacement carries: K[i] itself if its *)
(* top bit is clear, else K[i] sign-extended into 64 bits.                   *)
let md5_imm64_of_k k =
  let kk = Num.num_of_int k in
  if k < 0x80000000 then kk
  else kk +/ (Num.num_of_string "18446744069414584320");;

let md5_lea_k = Array.init 64 (fun i ->
  let imm = md5_imm64_of_k md5_k_vals.(i) in
  let tm = mk_eq
    (mk_comb(`word_zx:int64->int32`,
             mk_comb(`word:num->int64`, mk_numeral imm)),
     mk_comb(`word:num->int32`, mk_numeral (Num.num_of_int md5_k_vals.(i)))) in
  prove(tm, CONV_TAC WORD_BLAST));;

(* Concrete-base round reducers: md5_round i m [a;b;c;d] = <4-word list>.    *)
let md5_round_red = Array.init 64 (fun i ->
  let lhs = list_mk_comb
    (`md5_round`, [mk_small_numeral i; `m:int32 list`; `[a;b;c;d]:int32 list`]) in
  let th =
    (REWRITE_CONV[md5_round] THENC
     DEPTH_CONV let_CONV THENC
     REWRITE_CONV[md5_k; md5_rot; md5_msgidx] THENC
     DEPTH_CONV EL_CONV THENC
     NUM_REDUCE_CONV) lhs in
  GENL [`a:int32`; `b:int32`; `c:int32`; `d:int32`; `m:int32 list`] th);;

(* Generic-list round reducers, over a FREE list `l` (EL 0..3 l symbolic):   *)
(* needed for legs whose base state is the opaque md5_rounds(4k) m [a;b;c;d] *)
(* rather than a literal CONS list.                                          *)
let md5_round_red_gen = Array.init 64 (fun i ->
  let lhs = list_mk_comb
    (`md5_round`, [mk_small_numeral i; `m:int32 list`; `l:int32 list`]) in
  let th =
    (REWRITE_CONV[md5_round] THENC
     DEPTH_CONV let_CONV THENC
     REWRITE_CONV[md5_k; md5_rot; md5_msgidx] THENC
     DEPTH_CONV EL_CONV THENC
     NUM_REDUCE_CONV) lhs in
  GENL [`l:int32 list`; `m:int32 list`] th);;

(* Chunk unfolds: md5_rounds(4k+4) m l as four explicit rounds over the      *)
(* (possibly opaque) md5_rounds(4k) m l.                                     *)
let MD5_ROUNDS_4 = prove
 (`md5_rounds 4 m l =
     md5_round 3 m (md5_round 2 m (md5_round 1 m (md5_round 0 m l)))`,
  REWRITE_TAC[ARITH_RULE `4 = (((0+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_ROUNDS_8 = prove
 (`md5_rounds 8 m l =
     md5_round 7 m (md5_round 6 m (md5_round 5 m (md5_round 4 m
       (md5_rounds 4 m l))))`,
  REWRITE_TAC[ARITH_RULE `8 = (((4+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_ROUNDS_12 = prove
 (`md5_rounds 12 m l =
     md5_round 11 m (md5_round 10 m (md5_round 9 m (md5_round 8 m
       (md5_rounds 8 m l))))`,
  REWRITE_TAC[ARITH_RULE `12 = (((8+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_ROUNDS_16 = prove
 (`md5_rounds 16 m l =
     md5_round 15 m (md5_round 14 m (md5_round 13 m (md5_round 12 m
       (md5_rounds 12 m l))))`,
  REWRITE_TAC[ARITH_RULE `16 = (((12+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

(* --- Closer tactics for a refolded k-round segment postcondition. -------- *)

(* Peel one int32-level newB identity                                        *)
(*   word_add (word_rol ARG s) prev = word_add prev (word_rol ARG' s)        *)
(* down to its rotate argument and close the add-ring identity with          *)
(* WORD_RULE (NOT WORD_BLAST -- that times out on word_rol over 32-bit add   *)
(* carry chains).                                                            *)
let MD5_PEEL_TAC : tactic =
  GEN_REWRITE_TAC RAND_CONV [WORD_ADD_SYM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC WORD_RULE;;

(* Regroup (e1 /\ ... /\ ek /\ FRAME) as ((e1 /\ ... /\ ek) /\ FRAME) so the *)
(* register identities and the MAYCHANGE frame dispatch separately.          *)
let MD5_SPLIT_MAYCHANGE_TAC : tactic =
  W(fun (asl,w) ->
      let cjs = conjuncts w in
      let regroup = mk_eq(w, mk_conj(list_mk_conj(butlast cjs), last cjs)) in
      GEN_REWRITE_TAC I [CONJ_ACI_RULE regroup]);;

(* word_zx/word_sx packaging -> pure int32; refold F bitops to md5_f and the *)
(* LEA immediates to word K[i].  Leaves clean int32 add/rol/md5_f trees.     *)
let MD5_REFOLD_TAC : tactic =
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_ADD; WORD_VAL] THEN
  SIMP_TAC[WORD_SX_ZX; WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  SIMP_TAC[WORD_ZX_ADD; WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  REWRITE_TAC[WORD_VAL] THEN
  SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  REWRITE_TAC(MD5_F_BRIDGE :: Array.to_list md5_lea_k);;

(* Close the refolded conjunction of word_zx register identities.  The       *)
(* conjuncts come in register order (RAX,RBX,RCX,RDX) = rounds (0,3,2,1),    *)
(* NOT dependency order, and each round's md5_f references the LOWER rounds' *)
(* newBs.  Sweep the conjuncts up to (#eqs) times; each pass TRYs to prove   *)
(* (and ASSUME the int32 form of) any not-yet-closed identity -- once a      *)
(* lower round's int32 eq is assumed, ASM_REWRITE rewrites the next round's  *)
(* md5_f argument into spec form so MD5_PEEL_TAC closes it.  After the       *)
(* fixpoint a final ASM_REWRITE closes the word_zx conjuncts by reflexivity. *)
let MD5_CLOSE_REGS_TAC : tactic =
  let one_eq eq (asl,w) =
    if exists (fun (_,th) -> concl th = eq) asl then ALL_TAC (asl,w)
    else (SUBGOAL_THEN eq ASSUME_TAC THENL
           [ASM_REWRITE_TAC[] THEN MD5_PEEL_TAC; ALL_TAC]) (asl,w) in
  fun (asl,w) ->
    let cjs = conjuncts w in
    let eqs = map (fun cj -> let l,r = dest_eq cj in mk_eq(rand l, rand r)) cjs in
    let sweep = EVERY (map (fun eq -> TRY(one_eq eq)) eqs) in
    (EVERY (replicate sweep (length eqs)) THEN ASM_REWRITE_TAC[]) (asl,w);;

(* Frame-robust segment closer.  After ENSURES_FINAL_STATE_TAC+ASM_REWRITE   *)
(* the surviving goal is EITHER `(ids) /\ FRAME` (frame survived) OR just    *)
(* `ids` (frame auto-discharged -- happens inside ENSURES_SEQUENCE_TAC legs   *)
(* where SOME_FLAGS is pre-expanded so MAYCHANGE_IDEMPOT closes it).  Detect *)
(* the `,,` frame conjunct and branch.  Also normalize word_add mb (word 0)  *)
(* in BOTH assumptions and goal first, else the offset-0 bytes32 read fails  *)
(* to match its carried assumption.                                          *)
let MD5_CLOSE_SEG_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  W(fun (_,w) ->
    let has_frame = exists
      (fun cj -> match cj with
                 | Comb(Comb(Const(",,",_),_),_) -> true | _ -> false)
      (conjuncts w) in
    if has_frame then
      MD5_SPLIT_MAYCHANGE_TAC THEN CONJ_TAC THENL
       [MD5_REFOLD_TAC THEN MD5_CLOSE_REGS_TAC;
        REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC]
    else
      MD5_REFOLD_TAC THEN MD5_CLOSE_REGS_TAC);;

(* Leg 1 (rounds 0..3): CONCRETE base [a;b;c;d]; concrete reducers.  38      *)
(* instructions (includes the two seam-side loads).                          *)
let MD5_LEG1_TAC : tactic =
  REWRITE_TAC[MD5_ROUNDS_4] THEN
  REWRITE_TAC(Array.to_list md5_round_red) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_COMPRESS_EXEC (1--38) THEN
  ENSURES_FINAL_STATE_TAC THEN
  MD5_CLOSE_SEG_TAC;;

(* Legs 2..4 (rounds 4k..4k+3): OPAQUE base md5_rounds(4k); chunk-unfold +   *)
(* generic reducers + DEPTH EL_CONV (flattens the nested EL over the opaque  *)
(* base).  36 instructions each.                                             *)
let MD5_LEGK_TAC chunk : tactic =
  REWRITE_TAC[chunk] THEN
  REWRITE_TAC(Array.to_list md5_round_red_gen) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_COMPRESS_EXEC (1--36) THEN
  ENSURES_FINAL_STATE_TAC THEN
  MD5_CLOSE_SEG_TAC;;

(* Intermediate predicate Q_k at boundary 4k (k=1,2,3): identity register     *)
(* map at md5_rounds(4k), the live software-pipelined R11 (the asm emits the  *)
(* next round's F-prep `mov %edx,%r11d` in the previous round's tail), the    *)
(* prefetched R10 = EL (4k) m, RSI, and the 16 read-only bytes32 message     *)
(* facts.                                                                    *)
let md5_seg_invariant k =
  let kk = string_of_int (4 * k) in
  parse_term (Printf.sprintf
    "\\s. read RSI s = mb /\\
         read RAX s = word_zx (EL 0 (md5_rounds %s m [a;b;c;d])) /\\
         read RBX s = word_zx (EL 1 (md5_rounds %s m [a;b;c;d])) /\\
         read RCX s = word_zx (EL 2 (md5_rounds %s m [a;b;c;d])) /\\
         read RDX s = word_zx (EL 3 (md5_rounds %s m [a;b;c;d])) /\\
         read R11 s = word_zx (EL 3 (md5_rounds %s m [a;b;c;d])) /\\
         read R10 s = word_zx (EL %s m) /\\
         read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 (m:int32 list) /\\
         read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\\
         read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\\
         read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\\
         read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\\
         read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\\
         read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\\
         read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\\
         read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\\
         read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\\
         read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\\
         read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\\
         read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\\
         read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\\
         read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\\
         read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m"
    kk kk kk kk kk kk);;

(* The full rounds-0..15 `ensures`: four 4-round segments stitched with      *)
(* ENSURES_SEQUENCE_TAC at pc+0xba / pc+0x13a / pc+0x1ba, each leg           *)
(* discharged inline by re-simulation (sidesteps the bytes_loaded            *)
(* leg-alignment trap of composing standalone segment lemmas).  Boundaries   *)
(* are where the register<->spec map returns to the identity.                *)
let MD5_COMPRESS_R0_15 = prove
 (`!a b c d m mb pc.
     ensures x86
       (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
            read RIP s = word (pc + 0x34) /\
            read RSI s = mb /\
            read RAX s = word_zx (a:int32) /\
            read RBX s = word_zx (b:int32) /\
            read RCX s = word_zx (c:int32) /\
            read RDX s = word_zx (d:int32) /\
            read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 (m:int32 list) /\
            read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\
            read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\
            read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\
            read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\
            read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\
            read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\
            read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\
            read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\
            read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\
            read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\
            read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\
            read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\
            read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\
            read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\
            read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m)
       (\s. read RIP s = word (pc + 0x239) /\
            read RSI s = mb /\
            read RAX s = word_zx (EL 0 (md5_rounds 16 m [a;b;c;d])) /\
            read RBX s = word_zx (EL 1 (md5_rounds 16 m [a;b;c;d])) /\
            read RCX s = word_zx (EL 2 (md5_rounds 16 m [a;b;c;d])) /\
            read RDX s = word_zx (EL 3 (md5_rounds 16 m [a;b;c;d])) /\
            read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 m /\
            read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\
            read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\
            read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\
            read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\
            read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\
            read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\
            read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\
            read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\
            read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\
            read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\
            read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\
            read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\
            read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\
            read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\
            read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m)
       (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R10; R11] ,, MAYCHANGE SOME_FLAGS ,,
        MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`a:int32`; `b:int32`; `c:int32`; `d:int32`;
                       `m:int32 list`; `mb:int64`; `pc:num`] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xba` (md5_seg_invariant 1) THEN CONJ_TAC THENL
   [MD5_LEG1_TAC;
    ENSURES_SEQUENCE_TAC `pc + 0x13a` (md5_seg_invariant 2) THEN CONJ_TAC THENL
     [MD5_LEGK_TAC MD5_ROUNDS_8;
      ENSURES_SEQUENCE_TAC `pc + 0x1ba` (md5_seg_invariant 3) THEN CONJ_TAC THENL
       [MD5_LEGK_TAC MD5_ROUNDS_12;
        MD5_LEGK_TAC MD5_ROUNDS_16]]]);;

(* ========================================================================= *)
(* The G group (rounds 16..31), as a clean-seam `ensures`.                   *)
(*                                                                           *)
(* MD5_G_GROUP runs from pc+0x239 (exactly MD5_COMPRESS_R0_15's  *)
(* exit) to pc+0x4a1, advancing the working state from md5_rounds 16 to      *)
(* md5_rounds 32.  Pre and post are the SAME clean seam form as R0_15's      *)
(* post: (RAX,RBX,RCX,RDX) = (EL 0,1,2,3) of md5_rounds{16,32}, RSI = mb,    *)
(* the 16 bytes32 message reads preserved, and NO R10/R11/R12 (the G group   *)
(* reloads all three at entry; the H group reloads them at its entry).  So   *)
(* the body assembles as R0_15 ;; MD5_G_GROUP ;; ... with each seam matching *)
(* exactly.                                                                  *)
(*                                                                           *)
(* THREE deltas from the F group (all read off the instruction bytes):       *)
(*                                                                           *)
(*  1. TWO scratch registers.  G builds its aux value as a SUM of two ANDs   *)
(*     added separately into the accumulator:                                *)
(*       mov d,r11 ; not r11 ; and c,r11      (= ~d AND c)                   *)
(*       mov d,r12 ;           and b,r12      (=  d AND b)                   *)
(*       lea (acc,r10),acc ; add r11,acc ; add r12,acc                       *)
(*     so RAX after the round is ((a + M + K) + (~d&c)) + (d&b).  The two    *)
(*     ANDs straddle the LEA, so they are NOT adjacent -- a forward fold to  *)
(*     md5_g cannot fire.  Instead MD5_REFOLD_G_TAC EXPANDS the spec md5_g   *)
(*     via GSYM MD5_G_BRIDGE_ASM (the asm-operand-order bridge proved in     *)
(*     md5_bridge.ml), giving both sides the opaque atoms                    *)
(*     `word_and (word_not d) c` and `word_and d b`; then the unchanged      *)
(*     MD5_CLOSE_REGS_TAC (peel rol + WORD_RULE) closes the add-ring         *)
(*     (WORD_RULE absorbs the (x+A)+B vs x+(A+B) re-association).            *)
(*     Because R12 is now live across the 4-round boundaries (the round tail *)
(*     does `mov %edx,%r11d; mov %edx,%r12d`, both = EL 3, and the next      *)
(*     round reads R12), md5_g_invariant carries R11 AND R12 (both = EL 3)   *)
(*     plus the prefetched R10; the MAYCHANGE adds R12.                      *)
(*                                                                           *)
(*  2. PERMUTED message index.  msgidx is the md5_msgidx table, not the      *)
(*     round number: round 16 reads M[1], round 20 prefetches M[5], round    *)
(*     24 M[9], round 28 M[13].  The generic reducer already bakes this in,  *)
(*     so only the invariant's R10 conjunct names the permuted index.        *)
(*                                                                           *)
(*  3. Per-round insn counts differ (G leg 1 = 47, legs 2..4 = 44 each), so  *)
(*     the X86_STEPS ranges per leg are 47/44/44/44 (vs F's 38/36/36/36).    *)
(* ========================================================================= *)

(* G refold: like MD5_REFOLD_TAC, but EXPAND the spec md5_g into the asm-    *)
(* order sum (GSYM MD5_G_BRIDGE_ASM) rather than refolding an asm single-    *)
(* bitop.                                                                    *)
let MD5_REFOLD_G_TAC : tactic =
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_ADD; WORD_VAL] THEN
  SIMP_TAC[WORD_SX_ZX; WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  SIMP_TAC[WORD_ZX_ADD; WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  REWRITE_TAC[WORD_VAL] THEN
  SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  REWRITE_TAC(GSYM MD5_G_BRIDGE_ASM :: Array.to_list md5_lea_k);;

(* Frame-robust G segment closer (same `,,` frame detector as                *)
(* MD5_CLOSE_SEG_TAC, but with the G refold).                                *)
let MD5_CLOSE_SEG_G_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  W(fun (_,w) ->
    let has_frame = exists
      (fun cj -> match cj with
                 | Comb(Comb(Const(",,",_),_),_) -> true | _ -> false)
      (conjuncts w) in
    if has_frame then
      MD5_SPLIT_MAYCHANGE_TAC THEN CONJ_TAC THENL
       [MD5_REFOLD_G_TAC THEN MD5_CLOSE_REGS_TAC;
        REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC]
    else
      MD5_REFOLD_G_TAC THEN MD5_CLOSE_REGS_TAC);;

(* Chunk unfolds for the G 4-round boundaries (MD5_ROUNDS_8 pattern).        *)
let MD5_ROUNDS_20 = prove
 (`md5_rounds 20 m l =
     md5_round 19 m (md5_round 18 m (md5_round 17 m (md5_round 16 m
       (md5_rounds 16 m l))))`,
  REWRITE_TAC[ARITH_RULE `20 = (((16+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_ROUNDS_24 = prove
 (`md5_rounds 24 m l =
     md5_round 23 m (md5_round 22 m (md5_round 21 m (md5_round 20 m
       (md5_rounds 20 m l))))`,
  REWRITE_TAC[ARITH_RULE `24 = (((20+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_ROUNDS_28 = prove
 (`md5_rounds 28 m l =
     md5_round 27 m (md5_round 26 m (md5_round 25 m (md5_round 24 m
       (md5_rounds 24 m l))))`,
  REWRITE_TAC[ARITH_RULE `28 = (((24+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_ROUNDS_32 = prove
 (`md5_rounds 32 m l =
     md5_round 31 m (md5_round 30 m (md5_round 29 m (md5_round 28 m
       (md5_rounds 28 m l))))`,
  REWRITE_TAC[ARITH_RULE `32 = (((28+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

(* G leg: chunk-unfold + generic reducers + DEPTH EL_CONV + step + G close.  *)
(* (Generic reducers because every G leg's base is the opaque md5_rounds 4k.)*)
let MD5_LEGK_G_TAC chunk nsteps : tactic =
  REWRITE_TAC[chunk] THEN
  REWRITE_TAC(Array.to_list md5_round_red_gen) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_COMPRESS_EXEC (1--nsteps) THEN
  ENSURES_FINAL_STATE_TAC THEN
  MD5_CLOSE_SEG_G_TAC;;

(* G-internal invariant at round boundary rd = 4k: clean state at            *)
(* md5_rounds rd, the two live scratch regs R11 = R12 = EL 3 (md5_rounds rd),*)
(* and the prefetched R10 = EL idx m with idx the permuted message index     *)
(* md5_msgidx[rd] (20->5, 24->9, 28->13).                                    *)
let md5_g_invariant rd idx =
  let s = string_of_int rd and i = string_of_int idx in
  parse_term (Printf.sprintf
    "\\s. read RSI s = mb /\\
         read RAX s = word_zx (EL 0 (md5_rounds %s m [a;b;c;d])) /\\
         read RBX s = word_zx (EL 1 (md5_rounds %s m [a;b;c;d])) /\\
         read RCX s = word_zx (EL 2 (md5_rounds %s m [a;b;c;d])) /\\
         read RDX s = word_zx (EL 3 (md5_rounds %s m [a;b;c;d])) /\\
         read R11 s = word_zx (EL 3 (md5_rounds %s m [a;b;c;d])) /\\
         read R12 s = word_zx (EL 3 (md5_rounds %s m [a;b;c;d])) /\\
         read R10 s = word_zx (EL %s m) /\\
         read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 (m:int32 list) /\\
         read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\\
         read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\\
         read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\\
         read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\\
         read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\\
         read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\\
         read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\\
         read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\\
         read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\\
         read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\\
         read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\\
         read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\\
         read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\\
         read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\\
         read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m"
    s s s s s s i);;

(* The G-group `ensures`: rounds 16..31, pc+0x239 -> pc+0x4a1, four 4-round  *)
(* legs stitched at pc+0x2da / pc+0x372 / pc+0x40a (each boundary sits       *)
(* between a round's final `add` and the next round's `not %r11d`).          *)
let MD5_G_GROUP = prove
 (`!a b c d m mb pc.
     ensures x86
       (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
            read RIP s = word (pc + 0x239) /\
            read RSI s = mb /\
            read RAX s = word_zx (EL 0 (md5_rounds 16 m [a;b;c;d])) /\
            read RBX s = word_zx (EL 1 (md5_rounds 16 m [a;b;c;d])) /\
            read RCX s = word_zx (EL 2 (md5_rounds 16 m [a;b;c;d])) /\
            read RDX s = word_zx (EL 3 (md5_rounds 16 m [a;b;c;d])) /\
            read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 (m:int32 list) /\
            read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\
            read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\
            read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\
            read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\
            read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\
            read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\
            read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\
            read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\
            read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\
            read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\
            read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\
            read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\
            read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\
            read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\
            read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m)
       (\s. read RIP s = word (pc + 0x4a1) /\
            read RSI s = mb /\
            read RAX s = word_zx (EL 0 (md5_rounds 32 m [a;b;c;d])) /\
            read RBX s = word_zx (EL 1 (md5_rounds 32 m [a;b;c;d])) /\
            read RCX s = word_zx (EL 2 (md5_rounds 32 m [a;b;c;d])) /\
            read RDX s = word_zx (EL 3 (md5_rounds 32 m [a;b;c;d])) /\
            read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 m /\
            read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\
            read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\
            read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\
            read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\
            read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\
            read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\
            read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\
            read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\
            read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\
            read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\
            read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\
            read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\
            read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\
            read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\
            read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m)
       (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R10; R11; R12] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`a:int32`; `b:int32`; `c:int32`; `d:int32`;
                       `m:int32 list`; `mb:int64`; `pc:num`] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x2da` (md5_g_invariant 20 5) THEN CONJ_TAC THENL
   [MD5_LEGK_G_TAC MD5_ROUNDS_20 47;
    ENSURES_SEQUENCE_TAC `pc + 0x372` (md5_g_invariant 24 9) THEN CONJ_TAC THENL
     [MD5_LEGK_G_TAC MD5_ROUNDS_24 44;
      ENSURES_SEQUENCE_TAC `pc + 0x40a` (md5_g_invariant 28 13) THEN CONJ_TAC THENL
       [MD5_LEGK_G_TAC MD5_ROUNDS_28 44;
        MD5_LEGK_G_TAC MD5_ROUNDS_32 44]]]);;

(* ========================================================================= *)
(* The H group (rounds 32..47), as a clean-seam `ensures`.                   *)
(*                                                                           *)
(* MD5_H_GROUP runs from pc+0x4a1 (= MD5_G_GROUP's exit) to pc+0x676,        *)
(* advancing md5_rounds 32 -> md5_rounds 48.  Same clean seam form as G.     *)
(*                                                                           *)
(* H is the SIMPLE case: a single scratch register holding an XOR chain      *)
(*    mov c,r11 ; xor d,r11 ; xor b,r11  =>  (c XOR d) XOR b = md5_h b c d,  *)
(* added once into the accumulator.  So it refolds FORWARD exactly like F    *)
(* (MD5_REFOLD_H_TAC = the F refold with MD5_H_BRIDGE swapped in), and uses  *)
(* only R11 (no R12).                                                        *)
(*                                                                           *)
(* Pipelining: the round tail emits the next round's `mov %ecx,%r11d` (= EL  *)
(* 2 of the post-round state) before the boundary, so the H-internal         *)
(* invariant at boundary 4k carries read R11 = word_zx (EL 2 (md5_rounds     *)
(* 4k)) (cf. the G group's R11 = R12 = EL 3).  R10 prefetch follows          *)
(* md5_msgidx (round 36 -> M[1], 40 -> M[13], 44 -> M[9]).  Step counts      *)
(* 34/32/32/32; boundaries 0x51c / 0x590 / 0x603.                            *)
(* ========================================================================= *)

(* H refold: forward-fold the asm xor-chain to md5_h (the F recipe, with     *)
(* MD5_H_BRIDGE).                                                            *)
let MD5_REFOLD_H_TAC : tactic =
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_ADD; WORD_VAL] THEN
  SIMP_TAC[WORD_SX_ZX; WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  SIMP_TAC[WORD_ZX_ADD; WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  REWRITE_TAC[WORD_VAL] THEN
  SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  REWRITE_TAC(MD5_H_BRIDGE :: Array.to_list md5_lea_k);;

let MD5_CLOSE_SEG_H_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  W(fun (_,w) ->
    let has_frame = exists
      (fun cj -> match cj with
                 | Comb(Comb(Const(",,",_),_),_) -> true | _ -> false)
      (conjuncts w) in
    if has_frame then
      MD5_SPLIT_MAYCHANGE_TAC THEN CONJ_TAC THENL
       [MD5_REFOLD_H_TAC THEN MD5_CLOSE_REGS_TAC;
        REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC]
    else
      MD5_REFOLD_H_TAC THEN MD5_CLOSE_REGS_TAC);;

(* Chunk unfolds for the H 4-round boundaries.                               *)
let MD5_ROUNDS_36 = prove
 (`md5_rounds 36 m l =
     md5_round 35 m (md5_round 34 m (md5_round 33 m (md5_round 32 m
       (md5_rounds 32 m l))))`,
  REWRITE_TAC[ARITH_RULE `36 = (((32+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_ROUNDS_40 = prove
 (`md5_rounds 40 m l =
     md5_round 39 m (md5_round 38 m (md5_round 37 m (md5_round 36 m
       (md5_rounds 36 m l))))`,
  REWRITE_TAC[ARITH_RULE `40 = (((36+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_ROUNDS_44 = prove
 (`md5_rounds 44 m l =
     md5_round 43 m (md5_round 42 m (md5_round 41 m (md5_round 40 m
       (md5_rounds 40 m l))))`,
  REWRITE_TAC[ARITH_RULE `44 = (((40+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_ROUNDS_48 = prove
 (`md5_rounds 48 m l =
     md5_round 47 m (md5_round 46 m (md5_round 45 m (md5_round 44 m
       (md5_rounds 44 m l))))`,
  REWRITE_TAC[ARITH_RULE `48 = (((44+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_LEGK_H_TAC chunk nsteps : tactic =
  REWRITE_TAC[chunk] THEN
  REWRITE_TAC(Array.to_list md5_round_red_gen) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_COMPRESS_EXEC (1--nsteps) THEN
  ENSURES_FINAL_STATE_TAC THEN
  MD5_CLOSE_SEG_H_TAC;;

(* H-internal invariant at boundary 4k: clean state + the single live        *)
(* scratch R11 = EL 2 (md5_rounds 4k) and the prefetched R10 =               *)
(* EL (md5_msgidx[4k]) m.                                                    *)
let md5_h_invariant rd idx =
  let s = string_of_int rd and i = string_of_int idx in
  parse_term (Printf.sprintf
    "\\s. read RSI s = mb /\\
         read RAX s = word_zx (EL 0 (md5_rounds %s m [a;b;c;d])) /\\
         read RBX s = word_zx (EL 1 (md5_rounds %s m [a;b;c;d])) /\\
         read RCX s = word_zx (EL 2 (md5_rounds %s m [a;b;c;d])) /\\
         read RDX s = word_zx (EL 3 (md5_rounds %s m [a;b;c;d])) /\\
         read R11 s = word_zx (EL 2 (md5_rounds %s m [a;b;c;d])) /\\
         read R10 s = word_zx (EL %s m) /\\
         read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 (m:int32 list) /\\
         read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\\
         read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\\
         read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\\
         read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\\
         read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\\
         read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\\
         read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\\
         read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\\
         read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\\
         read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\\
         read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\\
         read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\\
         read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\\
         read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\\
         read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m"
    s s s s s i);;

(* The H-group `ensures`: rounds 32..47, pc+0x4a1 -> pc+0x676, four 4-round  *)
(* legs stitched at pc+0x51c / pc+0x590 / pc+0x603.                          *)
let MD5_H_GROUP = prove
 (`!a b c d m mb pc.
     ensures x86
       (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
            read RIP s = word (pc + 0x4a1) /\
            read RSI s = mb /\
            read RAX s = word_zx (EL 0 (md5_rounds 32 m [a;b;c;d])) /\
            read RBX s = word_zx (EL 1 (md5_rounds 32 m [a;b;c;d])) /\
            read RCX s = word_zx (EL 2 (md5_rounds 32 m [a;b;c;d])) /\
            read RDX s = word_zx (EL 3 (md5_rounds 32 m [a;b;c;d])) /\
            read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 (m:int32 list) /\
            read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\
            read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\
            read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\
            read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\
            read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\
            read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\
            read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\
            read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\
            read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\
            read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\
            read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\
            read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\
            read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\
            read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\
            read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m)
       (\s. read RIP s = word (pc + 0x676) /\
            read RSI s = mb /\
            read RAX s = word_zx (EL 0 (md5_rounds 48 m [a;b;c;d])) /\
            read RBX s = word_zx (EL 1 (md5_rounds 48 m [a;b;c;d])) /\
            read RCX s = word_zx (EL 2 (md5_rounds 48 m [a;b;c;d])) /\
            read RDX s = word_zx (EL 3 (md5_rounds 48 m [a;b;c;d])) /\
            read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 m /\
            read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\
            read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\
            read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\
            read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\
            read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\
            read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\
            read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\
            read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\
            read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\
            read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\
            read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\
            read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\
            read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\
            read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\
            read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m)
       (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R10; R11] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`a:int32`; `b:int32`; `c:int32`; `d:int32`;
                       `m:int32 list`; `mb:int64`; `pc:num`] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x51c` (md5_h_invariant 36 1) THEN CONJ_TAC THENL
   [MD5_LEGK_H_TAC MD5_ROUNDS_36 34;
    ENSURES_SEQUENCE_TAC `pc + 0x590` (md5_h_invariant 40 13) THEN CONJ_TAC THENL
     [MD5_LEGK_H_TAC MD5_ROUNDS_40 32;
      ENSURES_SEQUENCE_TAC `pc + 0x603` (md5_h_invariant 44 9) THEN CONJ_TAC THENL
       [MD5_LEGK_H_TAC MD5_ROUNDS_44 32;
        MD5_LEGK_H_TAC MD5_ROUNDS_48 32]]]);;

(* ========================================================================= *)
(* Te I group (rounds 48..63), as a clean-seam `ensures`.                    *)
(*                                                                           *)
(* MD5_I_GROUP runs from pc+0x676 (= MD5_H_GROUP's exit) to pc+0x8b1,        *)
(* advancing md5_rounds 48 -> md5_rounds 64 (all 64 rounds done).            *)
(*                                                                           *)
(* I aux value: mov $0xffffffff,r11 ; xor d,r11 ; or b,r11 ; xor c,r11  =>   *)
(*   ((0xffffffff XOR d) OR b) XOR c = md5_i b c d   (MD5_I_BRIDGE).         *)
(* Refolds FORWARD like F/H -- but with TWO wrinkles unique to I:            *)
(*                                                                           *)
(*  (a) PIPELINED COMPUTED R11.  Unlike F/G/H (whose boundary R11 is a bare  *)
(*      register copy), the I round tail pre-materializes the NEXT round's   *)
(*      first two ops `mov $0xffffffff,%r11d ; ... ; xor %edx,%r11d` BEFORE  *)
(*      the boundary.  So at an I-internal boundary 4k, R11 holds the        *)
(*      COMPUTED value word_xor (word 0xffffffff)                            *)
(*      (word_zx (EL 3 (md5_rounds 4k))) -- see md5_i_invariant.  (The       *)
(*      I-group ENTRY at 0x676 materializes r11 inline, so the H->I seam is  *)
(*      still clean -- no R11 carried there.)                                *)
(*                                                                           *)
(*  (b) word_zx/word_xor MISMATCH at the closer.  The stepper leaves R11 as  *)
(*      word_zx (word_xor (word 0xffffffff) BIG64) while the invariant       *)
(*      writes word_xor (word 0xffffffff) (word_zx BIG); WORD_ZX_XOR         *)
(*      distributes the LHS word_zx through the xor and WORD_ZX_FFFFFFFF     *)
(*      collapses both the widening and narrowing word_zx of the all-ones    *)
(*      immediate, so both sides become word_xor (word 0xffffffff)           *)
(*      (word_zx _) and the standard rand/rand peel in MD5_CLOSE_REGS_TAC    *)
(*      closes the R11 conjunct too.                                         *)
(*                                                                           *)
(* Step counts 39/36/36/36; boundaries 0x70e / 0x79a / 0x826.  Exit pc+0x8b1 *)
(* is the first add-back insn `add %r8d,%eax`.                               *)
(* ========================================================================= *)

(* word_zx of the all-ones immediate, BOTH directions: the asm's r11 holds   *)
(* ~0 in a 64-bit reg; after WORD_ZX_XOR distributes the (narrowing) word_zx *)
(* through the xor, the LHS carries word_zx (word 0xffffffff :int32) :int64  *)
(* (a WIDENING zx of the int32 all-ones), while the invariant's RHS uses the *)
(* bare int64 all-ones.                                                      *)
let WORD_ZX_FFFFFFFF = prove
 (`(word_zx (word 4294967295 :int64) :int32 = word 4294967295) /\
   (word_zx (word 4294967295 :int32) :int64 = word 4294967295)`,
  CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* I refold: forward-fold the asm chain to md5_i (the F recipe +             *)
(* MD5_I_BRIDGE), plus WORD_ZX_XOR / WORD_ZX_FFFFFFFF up front to normalize  *)
(* the pipelined R11.                                                        *)
let MD5_REFOLD_I_TAC : tactic =
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_ADD; WORD_VAL] THEN
  REWRITE_TAC[WORD_ZX_XOR] THEN
  SIMP_TAC[WORD_SX_ZX; WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  SIMP_TAC[WORD_ZX_ADD; WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  REWRITE_TAC[WORD_VAL] THEN
  SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL;
           DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  REWRITE_TAC[WORD_ZX_FFFFFFFF] THEN
  REWRITE_TAC(MD5_I_BRIDGE :: Array.to_list md5_lea_k);;

let MD5_CLOSE_SEG_I_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  W(fun (_,w) ->
    let has_frame = exists
      (fun cj -> match cj with
                 | Comb(Comb(Const(",,",_),_),_) -> true | _ -> false)
      (conjuncts w) in
    if has_frame then
      MD5_SPLIT_MAYCHANGE_TAC THEN CONJ_TAC THENL
       [MD5_REFOLD_I_TAC THEN MD5_CLOSE_REGS_TAC;
        REWRITE_TAC[SOME_FLAGS] THEN MONOTONE_MAYCHANGE_TAC]
    else
      MD5_REFOLD_I_TAC THEN MD5_CLOSE_REGS_TAC);;

(* Chunk unfolds for the I 4-round boundaries.                               *)
let MD5_ROUNDS_52 = prove
 (`md5_rounds 52 m l =
     md5_round 51 m (md5_round 50 m (md5_round 49 m (md5_round 48 m
       (md5_rounds 48 m l))))`,
  REWRITE_TAC[ARITH_RULE `52 = (((48+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_ROUNDS_56 = prove
 (`md5_rounds 56 m l =
     md5_round 55 m (md5_round 54 m (md5_round 53 m (md5_round 52 m
       (md5_rounds 52 m l))))`,
  REWRITE_TAC[ARITH_RULE `56 = (((52+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_ROUNDS_60 = prove
 (`md5_rounds 60 m l =
     md5_round 59 m (md5_round 58 m (md5_round 57 m (md5_round 56 m
       (md5_rounds 56 m l))))`,
  REWRITE_TAC[ARITH_RULE `60 = (((56+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_ROUNDS_64 = prove
 (`md5_rounds 64 m l =
     md5_round 63 m (md5_round 62 m (md5_round 61 m (md5_round 60 m
       (md5_rounds 60 m l))))`,
  REWRITE_TAC[ARITH_RULE `64 = (((60+1)+1)+1)+1`] THEN
  REWRITE_TAC[md5_rounds] THEN CONV_TAC NUM_REDUCE_CONV);;

let MD5_LEGK_I_TAC chunk nsteps : tactic =
  REWRITE_TAC[chunk] THEN
  REWRITE_TAC(Array.to_list md5_round_red_gen) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_COMPRESS_EXEC (1--nsteps) THEN
  ENSURES_FINAL_STATE_TAC THEN
  MD5_CLOSE_SEG_I_TAC;;

(* I-internal invariant at boundary 4k: clean state + the pipelined COMPUTED *)
(* R11 = word_xor (word 0xffffffff) (word_zx (EL 3 (md5_rounds 4k))) and the *)
(* prefetched R10 = EL (md5_msgidx[4k]) m.                                   *)
let md5_i_invariant rd idx =
  let s = string_of_int rd and i = string_of_int idx in
  parse_term (Printf.sprintf
    "\\s. read RSI s = mb /\\
         read RAX s = word_zx (EL 0 (md5_rounds %s m [a;b;c;d])) /\\
         read RBX s = word_zx (EL 1 (md5_rounds %s m [a;b;c;d])) /\\
         read RCX s = word_zx (EL 2 (md5_rounds %s m [a;b;c;d])) /\\
         read RDX s = word_zx (EL 3 (md5_rounds %s m [a;b;c;d])) /\\
         read R11 s = word_xor (word 4294967295)
                               (word_zx (EL 3 (md5_rounds %s m [a;b;c;d]))) /\\
         read R10 s = word_zx (EL %s m) /\\
         read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 (m:int32 list) /\\
         read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\\
         read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\\
         read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\\
         read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\\
         read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\\
         read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\\
         read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\\
         read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\\
         read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\\
         read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\\
         read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\\
         read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\\
         read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\\
         read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\\
         read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m"
    s s s s s i);;

(* The I-group `ensures`: rounds 48..63, pc+0x676 -> pc+0x8b1, four 4-round  *)
(* legs stitched at pc+0x70e / pc+0x79a / pc+0x826.                          *)
let MD5_I_GROUP = prove
 (`!a b c d m mb pc.
     ensures x86
       (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
            read RIP s = word (pc + 0x676) /\
            read RSI s = mb /\
            read RAX s = word_zx (EL 0 (md5_rounds 48 m [a;b;c;d])) /\
            read RBX s = word_zx (EL 1 (md5_rounds 48 m [a;b;c;d])) /\
            read RCX s = word_zx (EL 2 (md5_rounds 48 m [a;b;c;d])) /\
            read RDX s = word_zx (EL 3 (md5_rounds 48 m [a;b;c;d])) /\
            read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 (m:int32 list) /\
            read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\
            read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\
            read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\
            read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\
            read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\
            read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\
            read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\
            read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\
            read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\
            read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\
            read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\
            read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\
            read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\
            read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\
            read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m)
       (\s. read RIP s = word (pc + 0x8b1) /\
            read RSI s = mb /\
            read RAX s = word_zx (EL 0 (md5_rounds 64 m [a;b;c;d])) /\
            read RBX s = word_zx (EL 1 (md5_rounds 64 m [a;b;c;d])) /\
            read RCX s = word_zx (EL 2 (md5_rounds 64 m [a;b;c;d])) /\
            read RDX s = word_zx (EL 3 (md5_rounds 64 m [a;b;c;d])) /\
            read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 m /\
            read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\
            read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\
            read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\
            read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\
            read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\
            read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\
            read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\
            read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\
            read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\
            read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\
            read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\
            read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\
            read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\
            read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\
            read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m)
       (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R10; R11] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`a:int32`; `b:int32`; `c:int32`; `d:int32`;
                       `m:int32 list`; `mb:int64`; `pc:num`] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x70e` (md5_i_invariant 52 12) THEN CONJ_TAC THENL
   [MD5_LEGK_I_TAC MD5_ROUNDS_52 39;
    ENSURES_SEQUENCE_TAC `pc + 0x79a` (md5_i_invariant 56 8) THEN CONJ_TAC THENL
     [MD5_LEGK_I_TAC MD5_ROUNDS_56 36;
      ENSURES_SEQUENCE_TAC `pc + 0x826` (md5_i_invariant 60 4) THEN CONJ_TAC THENL
       [MD5_LEGK_I_TAC MD5_ROUNDS_60 36;
        MD5_LEGK_I_TAC MD5_ROUNDS_64 36]]]);;

(* ========================================================================= *)
(* The add-back (Davies-Meyer feed-forward).                                 *)
(*                                                                           *)
(* MD5_ADDBACK_SEG runs the four register adds at pc+0x8b1 .. pc+0x8bd:      *)
(*   add %r8d,%eax ; add %r9d,%ebx ; add %r14d,%ecx ; add %r15d,%edx         *)
(* R8/R9/R14/R15 hold the SAVED initial working state a/b/c/d, copied at     *)
(* loop entry (pc+0x28..0x33: mov %eax,%r8d etc.) and untouched by the 64    *)
(* rounds (they appear in no group's MAYCHANGE).  So each add forms the      *)
(* feed-forward word_add (saved) (rounds-result), matching md5_block's       *)
(*   [word_add (EL i s) (EL i (md5_rounds 64 m s))].                         *)
(*                                                                           *)
(* The asm adds in the order (rounds-result) + (saved) -- the operands are   *)
(* commuted vs the spec's (saved) + (rounds-result) -- so the closer         *)
(* collapses the word_zx-of-word_zx packaging (32->32 trivial) then peels    *)
(* the outer word_zx with AP_TERM_TAC and closes the int32 word_add          *)
(* commutation with WORD_RULE.  (WORD_RULE alone fails: the commute is       *)
(* INSIDE the word_zx.)                                                      *)
(*                                                                           *)
(* This segment carries R8/R9/R14/R15 in its precondition; BODY (below)      *)
(* threads them from loop entry through the four round groups -- they are    *)
(* preserved because they are absent from every group's MAYCHANGE frame.     *)
(* ========================================================================= *)

let MD5_ADDBACK_SEG = prove
 (`!a b c d m mb pc.
     ensures x86
       (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
            read RIP s = word (pc + 0x8b1) /\
            read RSI s = mb /\
            read RAX s = word_zx (EL 0 (md5_rounds 64 m [a;b;c;d])) /\
            read RBX s = word_zx (EL 1 (md5_rounds 64 m [a;b;c;d])) /\
            read RCX s = word_zx (EL 2 (md5_rounds 64 m [a;b;c;d])) /\
            read RDX s = word_zx (EL 3 (md5_rounds 64 m [a;b;c;d])) /\
            read R8 s = word_zx (a:int32) /\
            read R9 s = word_zx (b:int32) /\
            read R14 s = word_zx (c:int32) /\
            read R15 s = word_zx (d:int32))
       (\s. read RIP s = word (pc + 0x8bd) /\
            read RSI s = mb /\
            read RAX s = word_zx (word_add a (EL 0 (md5_rounds 64 m [a;b;c;d]))) /\
            read RBX s = word_zx (word_add b (EL 1 (md5_rounds 64 m [a;b;c;d]))) /\
            read RCX s = word_zx (word_add c (EL 2 (md5_rounds 64 m [a;b;c;d]))) /\
            read RDX s = word_zx (word_add d (EL 3 (md5_rounds 64 m [a;b;c;d]))))
       (MAYCHANGE [RIP; RAX; RBX; RCX; RDX] ,, MAYCHANGE SOME_FLAGS ,,
        MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MD5_COMPRESS_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* The full single-block loop BODY.                                          *)
(*                                                                           *)
(* MD5_COMPRESS_BODY chains the four committed GROUP ensures                 *)
(* (R0_15 ;; G ;; H ;; I) and the add-back (MD5_ADDBACK_SEG) into one        *)
(* ensures from pc+0x34 (core entry, first M[0] load) to pc+0x8bd (just      *)
(* past the four feed-forward adds).  Post: (RAX,RBX,RCX,RDX) = word_zx of   *)
(* the Davies-Meyer feed-forward                                             *)
(*   word_add (EL i [a;b;c;d]) (EL i (md5_rounds 64 m [a;b;c;d])),           *)
(* i.e. EL i (md5_block [a;b;c;d] m).                                        *)
(*                                                                           *)
(* WHY THE SEAMS CARRY THE SAVED REGISTERS.                                  *)
(* MD5_ADDBACK_SEG reads R8/R9/R14/R15 (the saved initial working state      *)
(* a..d, copied at loop entry pc+0x28..0x33 and untouched by all 64 rounds). *)
(* So the leg feeding it must assert R8/R9/R14/R15 = word_zx a/b/c/d in its  *)
(* post.  The bare clean-seam invariant (state + RSI + 16 bytes32 reads)     *)
(* does NOT mention those four registers, so BODY threads them explicitly    *)
(* through every seam (md5_body_regseam, below) and lifts the add-back as    *)
(* the final leg.                                                            *)
(*                                                                           *)
(* THE PRESERVED-REGISTER LIFT (MD5_LIFT_GROUP_REGS).                        *)
(* Each seam predicate carries the extra conjuncts R8/R9/R14/R15 = word_zx   *)
(* a/b/c/d that the committed group/add-back lemma does NOT mention.         *)
(* Because those four registers are absent from every group's (and the       *)
(* add-back's) MAYCHANGE frame, the ensures frame `R s s'` guarantees they   *)
(* are unchanged, so ASSUMPTION_STATE_UPDATE_TAC carries each preserved      *)
(* equality from the leg-pre assumption straight into the lifted post.  The  *)
(* lift accepts a group lemma via ENSURES_SUBLEMMA_THM, which leaves a       *)
(* non-trivial (!s. P s ==> P' s) goal (the lifted pre P has the extra reg   *)
(* conjuncts; the lemma's pre P' does not), discharged by                    *)
(* `REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]`.  It also widens   *)
(* the frame to the union frame (incl R12, used by the G group) via          *)
(* SUBSUMED_MAYCHANGE_TAC, and recovers the seam state's bytes_loaded from   *)
(* the pre's via NONSELFMODIFYING_STATE_UPDATE_TAC (the code region is       *)
(* read-only across each group).  SOME_FLAGS must be expanded EVERYWHERE     *)
(* first (goal via REWRITE_TAC and lemma via REWRITE_RULE):                  *)
(* SUBSUMED_MAYCHANGE_TAC and NONSELFMODIFYING_STATE_UPDATE_TAC both choke   *)
(* on `MAYCHANGE SOME_FLAGS`.                                                *)
(*                                                                           *)
(* NB the stores to state[4] (mov %eax,0x0(%rbp) at pc+0x8ca..) are NOT in   *)
(* this body: the asm does the feed-forward (0x8b1), then the loop back-edge *)
(* `add $0x40,%rsi; cmp %rdi,%rsi; jb` (0x8bd..0x8c9), and the stores at     *)
(* 0x8ca run only on the loop-EXIT path.                                     *)
(* ========================================================================= *)

(* Lift a committed group/segment lemma whose seam predicate additionally    *)
(* asserts the preserved registers R8/R9/R14/R15 (= word_zx a/b/c/d), absent *)
(* from the lemma's frame.  See the header above for the mechanism.          *)
let MD5_LIFT_GROUP_REGS grp =
  REWRITE_TAC[SOME_FLAGS] THEN
  MP_TAC(REWRITE_RULE[SOME_FLAGS](SPEC_ALL grp)) THEN
  MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* P ==> P': the lifted pre has the extra preserved-reg conjuncts. *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    SUBSUMED_MAYCHANGE_TAC;
    REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    NONSELFMODIFYING_STATE_UPDATE_TAC
      (MATCH_MP bytes_loaded_update (fst MD5_COMPRESS_EXEC)) THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_REWRITE_TAC[]];;

(* The clean seam at rounds-count rd, now also carrying the preserved        *)
(* R8/R9/R14/R15 = word_zx a/b/c/d (NO bytes_loaded, NO read RIP -- supplied *)
(* by ENSURES_SEQUENCE_TAC).  State + RSI + preserved regs + 16 bytes32      *)
(* reads.                                                                    *)
let md5_body_regseam rd = parse_term (Printf.sprintf
  "\\s. read RSI s = mb /\\
        read RAX s = word_zx (EL 0 (md5_rounds %s m [a;b;c;d])) /\\
        read RBX s = word_zx (EL 1 (md5_rounds %s m [a;b;c;d])) /\\
        read RCX s = word_zx (EL 2 (md5_rounds %s m [a;b;c;d])) /\\
        read RDX s = word_zx (EL 3 (md5_rounds %s m [a;b;c;d])) /\\
        read R8 s = word_zx (a:int32) /\\
        read R9 s = word_zx (b:int32) /\\
        read R14 s = word_zx (c:int32) /\\
        read R15 s = word_zx (d:int32) /\\
        read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 (m:int32 list) /\\
        read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\\
        read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\\
        read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\\
        read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\\
        read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\\
        read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\\
        read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\\
        read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\\
        read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\\
        read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\\
        read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\\
        read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\\
        read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\\
        read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\\
        read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m"
  rd rd rd rd);;

let MD5_COMPRESS_BODY = prove
 (`!a b c d m mb pc.
     ensures x86
       (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
            read RIP s = word (pc + 0x34) /\
            read RSI s = mb /\
            read RAX s = word_zx (a:int32) /\
            read RBX s = word_zx (b:int32) /\
            read RCX s = word_zx (c:int32) /\
            read RDX s = word_zx (d:int32) /\
            read R8 s = word_zx a /\
            read R9 s = word_zx b /\
            read R14 s = word_zx c /\
            read R15 s = word_zx d /\
            read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 (m:int32 list) /\
            read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\
            read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\
            read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\
            read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\
            read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\
            read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\
            read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\
            read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\
            read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\
            read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\
            read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\
            read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\
            read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\
            read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\
            read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m)
       (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
            read RIP s = word (pc + 0x8bd) /\
            read RSI s = mb /\
            read RAX s = word_zx (word_add a (EL 0 (md5_rounds 64 m [a;b;c;d]))) /\
            read RBX s = word_zx (word_add b (EL 1 (md5_rounds 64 m [a;b;c;d]))) /\
            read RCX s = word_zx (word_add c (EL 2 (md5_rounds 64 m [a;b;c;d]))) /\
            read RDX s = word_zx (word_add d (EL 3 (md5_rounds 64 m [a;b;c;d]))))
       (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; R10; R11; R12] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`a:int32`; `b:int32`; `c:int32`; `d:int32`;
                       `m:int32 list`; `mb:int64`; `pc:num`] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x8b1` (md5_body_regseam "64") THEN CONJ_TAC THENL
   [(* rounds 0..63, the four groups composed with R8/R9/R14/R15 threaded *)
    ENSURES_SEQUENCE_TAC `pc + 0x239` (md5_body_regseam "16") THEN CONJ_TAC THENL
     [MD5_LIFT_GROUP_REGS MD5_COMPRESS_R0_15;
      ENSURES_SEQUENCE_TAC `pc + 0x4a1` (md5_body_regseam "32") THEN CONJ_TAC THENL
       [MD5_LIFT_GROUP_REGS MD5_G_GROUP;
        ENSURES_SEQUENCE_TAC `pc + 0x676` (md5_body_regseam "48") THEN CONJ_TAC THENL
         [MD5_LIFT_GROUP_REGS MD5_H_GROUP;
          MD5_LIFT_GROUP_REGS MD5_I_GROUP]]];
    (* the Davies-Meyer add-back *)
    MD5_LIFT_GROUP_REGS MD5_ADDBACK_SEG]);;

(* ========================================================================= *)
(* One loop iteration + spec-level loop algebra.                             *)
(*                                                                           *)
(* MD5_LIFT_BODY is MD5_LIFT_GROUP_REGS WITHOUT the bytes_loaded recovery    *)
(* step (NONSELFMODIFYING_STATE_UPDATE_TAC): unlike the group/segment        *)
(* lemmas, MD5_COMPRESS_BODY's postcondition ALREADY carries                 *)
(* `bytes_loaded s' ...`, so the lifted post needs no separate re-derivation *)
(* (and re-deriving it clashes -- `could not prove that updates will not     *)
(* modify the program code`).  All other deltas vs MD5_LIFT_GROUP_REGS are   *)
(* identical: the extra seam conjunct (here read RDI s = eptr) is carried    *)
(* pre->post for free by ASSUMPTION_STATE_UPDATE_TAC because RDI is absent   *)
(* from BODY's MAYCHANGE frame.                                              *)
(* ========================================================================= *)

let MD5_LIFT_BODY grp =
  REWRITE_TAC[SOME_FLAGS] THEN
  MP_TAC(REWRITE_RULE[SOME_FLAGS](SPEC_ALL grp)) THEN
  MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* P ==> P': the lifted pre adds read RDI s = eptr. *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    SUBSUMED_MAYCHANGE_TAC;
    REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_REWRITE_TAC[]];;

(* Seam at pc+0x34: BODY's precondition body PLUS the loop's fixed end ptr   *)
(* RDI = eptr (= data + 0x40*num_blocks).  read RIP / bytes_loaded supplied  *)
(* by ENSURES_SEQUENCE_TAC.                                                  *)
let md5_iter_seam34 = parse_term
  "\\s. read RSI s = mb /\\
        read RDI s = eptr /\\
        read RAX s = word_zx (a:int32) /\\ read RBX s = word_zx (b:int32) /\\
        read RCX s = word_zx (c:int32) /\\ read RDX s = word_zx (d:int32) /\\
        read R8 s = word_zx a /\\ read R9 s = word_zx b /\\
        read R14 s = word_zx c /\\ read R15 s = word_zx d /\\
        read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 (m:int32 list) /\\
        read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\\
        read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\\
        read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\\
        read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\\
        read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\\
        read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\\
        read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\\
        read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\\
        read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\\
        read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\\
        read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\\
        read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\\
        read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\\
        read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\\
        read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m";;

(* Seam at pc+0x8bd: BODY's feed-forward post PLUS RDI = eptr. *)
let md5_iter_seam8bd = parse_term
  "\\s. read RSI s = mb /\\
        read RDI s = eptr /\\
        read RAX s = word_zx (word_add a (EL 0 (md5_rounds 64 m [a;b;c;d]))) /\\
        read RBX s = word_zx (word_add b (EL 1 (md5_rounds 64 m [a;b;c;d]))) /\\
        read RCX s = word_zx (word_add c (EL 2 (md5_rounds 64 m [a;b;c;d]))) /\\
        read RDX s = word_zx (word_add d (EL 3 (md5_rounds 64 m [a;b;c;d])))";;

(* One loop iteration, pc+0x28 (loop top) -> pc+0x8c4 (the back-edge `jb`).  *)
(* Composes:  leg A = the 4 saves (R8/R9/R14/R15 <- A..D); leg B = the 64-   *)
(* round BODY; leg C = `add $0x40,%rsi; cmp %rdi,%rsi`.  Working state is    *)
(* fed forward to (RAX,RBX,RCX,RDX) = word_zx of EL i (md5_block [a;b;c;d]   *)
(* m), rsi advances by 0x40, and CF records rsi' < eptr (the do-while        *)
(* continue test).                                                           *)
let MD5_LOOP_ITER = prove
 (`!a b c d m mb eptr pc.
     ensures x86
       (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
            read RIP s = word (pc + 0x28) /\
            read RSI s = mb /\ read RDI s = eptr /\
            read RAX s = word_zx (a:int32) /\ read RBX s = word_zx (b:int32) /\
            read RCX s = word_zx (c:int32) /\ read RDX s = word_zx (d:int32) /\
            read (memory :> bytes32 (word_add mb (word 0))) s = EL 0 (m:int32 list) /\
            read (memory :> bytes32 (word_add mb (word 4))) s = EL 1 m /\
            read (memory :> bytes32 (word_add mb (word 8))) s = EL 2 m /\
            read (memory :> bytes32 (word_add mb (word 12))) s = EL 3 m /\
            read (memory :> bytes32 (word_add mb (word 16))) s = EL 4 m /\
            read (memory :> bytes32 (word_add mb (word 20))) s = EL 5 m /\
            read (memory :> bytes32 (word_add mb (word 24))) s = EL 6 m /\
            read (memory :> bytes32 (word_add mb (word 28))) s = EL 7 m /\
            read (memory :> bytes32 (word_add mb (word 32))) s = EL 8 m /\
            read (memory :> bytes32 (word_add mb (word 36))) s = EL 9 m /\
            read (memory :> bytes32 (word_add mb (word 40))) s = EL 10 m /\
            read (memory :> bytes32 (word_add mb (word 44))) s = EL 11 m /\
            read (memory :> bytes32 (word_add mb (word 48))) s = EL 12 m /\
            read (memory :> bytes32 (word_add mb (word 52))) s = EL 13 m /\
            read (memory :> bytes32 (word_add mb (word 56))) s = EL 14 m /\
            read (memory :> bytes32 (word_add mb (word 60))) s = EL 15 m)
       (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
            read RIP s = word (pc + 0x8c4) /\
            read RSI s = word_add mb (word 64) /\
            read RDI s = eptr /\
            read RAX s = word_zx (word_add a (EL 0 (md5_rounds 64 m [a;b;c;d]))) /\
            read RBX s = word_zx (word_add b (EL 1 (md5_rounds 64 m [a;b;c;d]))) /\
            read RCX s = word_zx (word_add c (EL 2 (md5_rounds 64 m [a;b;c;d]))) /\
            read RDX s = word_zx (word_add d (EL 3 (md5_rounds 64 m [a;b;c;d]))) /\
            (read CF s <=> val (word_add mb (word 64)) < val eptr))
       (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RSI; R8; R9; R10; R11; R12; R14; R15] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  MAP_EVERY X_GEN_TAC [`a:int32`; `b:int32`; `c:int32`; `d:int32`;
                       `m:int32 list`; `mb:int64`; `eptr:int64`; `pc:num`] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x34` md5_iter_seam34 THEN CONJ_TAC THENL
   [(* leg A: the 4 register saves R8/R9/R14/R15 <- working A..D. *)
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MD5_COMPRESS_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL; DIMINDEX_32; DIMINDEX_64; LE_REFL; ARITH];
    ENSURES_SEQUENCE_TAC `pc + 0x8bd` md5_iter_seam8bd THEN CONJ_TAC THENL
     [(* leg B: the 64-round body, lifting RDI = eptr through its frame. *)
      MD5_LIFT_BODY MD5_COMPRESS_BODY;
      (* leg C: add $0x40,%rsi ; cmp %rdi,%rsi (sets RSI' and CF). *)
      ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC MD5_COMPRESS_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Spec-level algebra for the multi-block loop invariant.  The running state *)
(* after i blocks is  md5_blocks init (SUB_LIST(0,i) blocks)  (a length-4    *)
(* int32 list); one iteration consumes block (EL i blocks) and advances it.  *)
(* ------------------------------------------------------------------------- *)

let MD5_BLOCKS_SNOC = prove
 (`!l s blk. md5_blocks s (APPEND l [blk]) = md5_block (md5_blocks s l) blk`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; md5_blocks] THEN
  ASM_REWRITE_TAC[md5_blocks]);;

let SUB_LIST_PREFIX_SNOC = prove
 (`!l:(A)list i. i < LENGTH l
        ==> SUB_LIST(0,i+1) l = APPEND (SUB_LIST(0,i) l) [EL i l]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(A)list`; `i:num`; `1`; `0`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_1]);;

let LIST_4_EXPAND = prove
 (`!l:(A)list. LENGTH l = 4 ==> l = [EL 0 l; EL 1 l; EL 2 l; EL 3 l]`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`] THEN
  REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;

(* Advancing the running state by block i (for i < num_blocks), from an      *)
(* arbitrary incoming state `init` (the CORE theorem's incoming state[4]).   *)
let MD5_STATE_ADVANCE = prove
 (`!init blocks i. i < LENGTH blocks
        ==> md5_block (md5_blocks init (SUB_LIST(0,i) blocks)) (EL i blocks) =
            md5_blocks init (SUB_LIST(0,i+1) blocks)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_PREFIX_SNOC; MD5_BLOCKS_SNOC]);;

(* ------------------------------------------------------------------------- *)
(* Address/pointer arithmetic for the multi-block loop.                      *)
(*                                                                           *)
(* The loop is a pointer-counted do-while: rsi walks data..data+64*nb in     *)
(* 64-byte strides and the back-edge `cmp %rdi,%rsi; jb` continues while     *)
(* rsi < eptr (= data + 64*nb).  To turn that unsigned pointer compare into  *)
(* the loop-counter test `i < nb`, the buffer must not wrap the 64-bit       *)
(* address space (the CORE precondition `val datap + 64*val nb < 2 EXP 64`). *)
(* ------------------------------------------------------------------------- *)

(* With the buffer fitting in the address space, pointer order = index order.*)
let MD5_PTR_LT = prove
 (`!(p:int64) i n.
        val p + 64 * n < 2 EXP 64 /\ i <= n
        ==> (val(word_add p (word (64 * i))) < val(word_add p (word (64 * n)))
             <=> i < n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `64 * i < 2 EXP 64 /\ 64 * n < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  SUBGOAL_THEN `(val(p:int64) + 64 * i) MOD 2 EXP 64 = val p + 64 * i /\
                (val(p:int64) + 64 * n) MOD 2 EXP 64 = val p + 64 * n`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* nil/full SUB_LIST folds: running state at i=0 is init; at i=nb all blocks.*)
let SUB_LIST_NIL_FOLD = prove
 (`!(s:int32 list) blocks. md5_blocks s (SUB_LIST(0,0) blocks) = s`,
  REWRITE_TAC[SUB_LIST_CLAUSES; md5_blocks]);;

let SUB_LIST_FULL_FOLD = prove
 (`!blocks:(A)list. SUB_LIST(0,LENGTH blocks) blocks = blocks`,
  REWRITE_TAC[SUB_LIST_LENGTH]);;

(* shl $0x6 = multiply by 64 (the prologue `shl $0x6,%rdx` computing 64*nb). *)
let WORD_SHL_6 = prove
 (`!x:int64. word_shl x 6 = word(64 * val x)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* With a non-empty buffer fitting the address space, the negated byte-count *)
(* (= word_neg(64*nb), set by the prologue cmp) is nonzero, so the prologue  *)
(* `je` num_blocks=0 guard is NOT taken in the nb>0 case.  Stated with the   *)
(* weakened hypothesis 64*nb < 2 EXP 64 (the caller drops the `val datap +`).*)
let WORD_NEG_BYTECOUNT_NZ = prove
 (`!nb:int64.
        ~(val nb = 0) /\ 64 * val nb < 2 EXP 64
        ==> ~(val(word_neg(word(64 * val nb):int64)) = 0)`,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[VAL_WORD_NEG_CASES; DIMINDEX_64] THEN
  ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  COND_CASES_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUB_EQ_0; NOT_LE] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The ENSURES_WHILE_PUP body-step (i -> i+1) for the multi-block loop, in   *)
(* the nb>0 branch.  At the loop top pc+0x28 the working state holds         *)
(* md5_blocks [a;b;c;d] (SUB_LIST(0,i) blocks); one pass of MD5_LOOP_ITER    *)
(* (pc+0x28 -> the back-edge jb pc+0x8c4) consumes block (EL i blocks) and   *)
(* advances it to SUB_LIST(0,i+1).  RSI strides by 0x40 and CF records the   *)
(* unsigned do-while continue test (i+1 < nb, via the non-wrap MD5_PTR_LT).  *)
(* The quantified message memory is unchanged (memory is not in MD5_LOOP_    *)
(* ITER's frame) and supplies block i's 16 reads; RBP=statep is preserved.   *)
(* ------------------------------------------------------------------------- *)
let MD5_LOOP_BODY_STEP = prove
 (`!a b c d blocks statep datap nb pc i.
        val datap + 64 * val(nb:int64) < 2 EXP 64 /\
        LENGTH blocks = val nb /\
        i < val nb
        ==> ensures x86
              (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
                   read RIP s = word (pc + 0x28) /\
                   read RBP s = statep /\
                   read RDI s = word_add datap (word (64 * val nb)) /\
                   read RSI s = word_add datap (word (64 * i)) /\
                   read RAX s = word_zx (EL 0 (md5_blocks [a;b;c;d]
                                  (SUB_LIST(0,i) blocks)):int32) /\
                   read RBX s = word_zx (EL 1 (md5_blocks [a;b;c;d]
                                  (SUB_LIST(0,i) blocks)):int32) /\
                   read RCX s = word_zx (EL 2 (md5_blocks [a;b;c;d]
                                  (SUB_LIST(0,i) blocks)):int32) /\
                   read RDX s = word_zx (EL 3 (md5_blocks [a;b;c;d]
                                  (SUB_LIST(0,i) blocks)):int32) /\
                   (!j k. j < val nb /\ k < 16
                          ==> read (memory :> bytes32
                                     (word_add datap (word (64 * j + 4 * k)))) s
                              = EL k (EL j (blocks:(int32 list)list))))
              (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
                   read RIP s = word (pc + 0x8c4) /\
                   read RBP s = statep /\
                   read RDI s = word_add datap (word (64 * val nb)) /\
                   read RSI s = word_add datap (word (64 * (i + 1))) /\
                   read RAX s = word_zx (EL 0 (md5_blocks [a;b;c;d]
                                  (SUB_LIST(0,i+1) blocks)):int32) /\
                   read RBX s = word_zx (EL 1 (md5_blocks [a;b;c;d]
                                  (SUB_LIST(0,i+1) blocks)):int32) /\
                   read RCX s = word_zx (EL 2 (md5_blocks [a;b;c;d]
                                  (SUB_LIST(0,i+1) blocks)):int32) /\
                   read RDX s = word_zx (EL 3 (md5_blocks [a;b;c;d]
                                  (SUB_LIST(0,i+1) blocks)):int32) /\
                   (!j k. j < val nb /\ k < 16
                          ==> read (memory :> bytes32
                                     (word_add datap (word (64 * j + 4 * k)))) s
                              = EL k (EL j blocks)) /\
                   (read CF s <=> i + 1 < val nb))
              (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RBP; RSI; RDI;
                          R8; R9; R10; R11; R12; R14; R15] ,,
               MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
               MAYCHANGE [memory :> bytes (statep, 16)])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `md5_blocks [a;b;c;d] (SUB_LIST(0,i+1) blocks) =
    md5_block (md5_blocks [a;b;c;d] (SUB_LIST(0,i) blocks)) (EL i blocks)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC MD5_STATE_ADVANCE THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `St = md5_blocks [a;b;c;d] (SUB_LIST(0,i) blocks)` THEN
  SUBGOAL_THEN `LENGTH(St:int32 list) = 4` ASSUME_TAC THENL
   [EXPAND_TAC "St" THEN MATCH_MP_TAC LENGTH_MD5_BLOCKS THEN
    REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(ISPEC `St:int32 list` LIST_4_EXPAND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`EL 0 (St:int32 list)`; `EL 1 (St:int32 list)`;
    `EL 2 (St:int32 list)`; `EL 3 (St:int32 list)`;
    `EL i (blocks:(int32 list)list)`;
    `word_add datap (word (64 * i)):int64`;
    `word_add datap (word (64 * val(nb:int64))):int64`; `pc:num`]
   MD5_LOOP_ITER) THEN
  MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* P ==> P': supply ITER's 16 block-i reads from the quantified msg mem *)
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(end_itlist CONJ
       (map (fun k -> SPECL [`i:num`; mk_small_numeral k] th) (0--15)))) THEN
    ASM_SIMP_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    (* ITER frame subsumed by the body-step frame *)
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC;
    (* ITER post (+ preserved RBP/memory via R') ==> body-step post *)
    REWRITE_TAC[SOME_FLAGS] THEN REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN ASSUMPTION_STATE_UPDATE_TAC THEN
    DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[md5_block] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    SUBGOAL_THEN
     `md5_rounds 64 (EL i blocks) [EL 0 St; EL 1 St; EL 2 St; EL 3 St] =
      md5_rounds 64 (EL i blocks) (St:int32 list)`
     (fun th -> REWRITE_TAC[th]) THENL
     [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word_add datap (word (64 * i))) (word 64):int64 =
      word_add datap (word (64 * (i + 1)))` SUBST_ALL_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONJ_TAC THENL
     [REFL_TAC;
      MP_TAC(ISPECL [`datap:int64`; `i + 1`; `val(nb:int64)`] MD5_PTR_LT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]]]);;

(* ========================================================================= *)
(* The core theorem MD5_COMPRESS_CORRECT.                                    *)
(*                                                                           *)
(* Entry pc+0x8 (after the 5 callee-save pushes, in-frame SP), exit pc+0x8d6 *)
(* (before the pops).  C_ARGUMENTS [statep; datap; num_blocks] (rdi,rsi,rdx).*)
(* Incoming state[4] = the 4 int32 words a,b,c,d at [statep] (no list var    *)
(* needed -- [a;b;c;d] is length-4 by construction).  Message = `blocks`, a  *)
(* list of num_blocks 16-word blocks, read little-endian directly as bytes32 *)
(* (no bswap).  Post: the four 32-bit words at [statep] hold                 *)
(* md5_blocks [a;b;c;d] blocks (run all blocks from the incoming state).     *)
(*                                                                           *)
(* The single non-wrap precondition  val datap + 64*num_blocks < 2 EXP 64    *)
(* covers both the prologue `shl $6 / lea` (= datap + 64*nb without wrap)    *)
(* and the bottom `cmp %rdi,%rsi; jb` continue test, which the proof turns   *)
(* into the loop-counter test i < num_blocks via MD5_PTR_LT.                 *)
(*                                                                           *)
(* Structure: ENSURES_SEQUENCE at pc+0x8ca to a converged seam (RBP=statep,  *)
(* RAX..RDX = the final spec state words) reached on BOTH the num_blocks=0   *)
(* path and the loop-exit path; leg 2 is the four 32-bit stores into         *)
(* state[4].  Leg 1 case-splits on num_blocks=0 (FORCED by                   *)
(* ENSURES_WHILE_PUP_TAC's ~(k=0)); the nb>0 branch runs the pointer-counted *)
(* do-while via ENSURES_WHILE_PUP_TAC + MD5_LOOP_BODY_STEP.                  *)
(* ========================================================================= *)

let MD5_COMPRESS_CORRECT = prove
 (`!a b c d blocks statep datap nb pc.
        nonoverlapping (word pc, LENGTH(BUTLAST md5_compress_tmc))
                       (statep:int64, 16) /\
        nonoverlapping (statep:int64, 16) (datap:int64, 64 * val(nb:int64)) /\
        val datap + 64 * val nb < 2 EXP 64 /\
        LENGTH blocks = val nb
        ==> ensures x86
              (\s. bytes_loaded s (word pc) (BUTLAST md5_compress_tmc) /\
                   read RIP s = word (pc + 0x8) /\
                   C_ARGUMENTS [statep; datap; nb] s /\
                   read (memory :> bytes32 statep) s = (a:int32) /\
                   read (memory :> bytes32 (word_add statep (word 4))) s = (b:int32) /\
                   read (memory :> bytes32 (word_add statep (word 8))) s = (c:int32) /\
                   read (memory :> bytes32 (word_add statep (word 12))) s = (d:int32) /\
                   (!j k. j < val nb /\ k < 16
                          ==> read (memory :> bytes32
                                     (word_add datap (word (64 * j + 4 * k)))) s
                              = EL k (EL j (blocks:(int32 list)list))))
              (\s. read RIP s = word (pc + 0x8d6) /\
                   read (memory :> bytes32 statep) s =
                     EL 0 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 4))) s =
                     EL 1 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 8))) s =
                     EL 2 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 12))) s =
                     EL 3 (md5_blocks [a;b;c;d] blocks))
              (MAYCHANGE [RIP; RAX; RBX; RCX; RDX; RBP; RSI; RDI;
                          R8; R9; R10; R11; R12; R14; R15] ,,
               MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
               MAYCHANGE [memory :> bytes (statep, 16)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; C_ARGUMENTS;
              fst MD5_COMPRESS_EXEC] THEN REPEAT STRIP_TAC THEN
  (* Seam at pc+0x8ca (loop exit / nblk=0 join): RBP=statep + final state. *)
  ENSURES_SEQUENCE_TAC `pc + 0x8ca`
   `\s. read RBP s = statep /\
        read RAX s = word_zx (EL 0 (md5_blocks [a;b;c;d] blocks):int32) /\
        read RBX s = word_zx (EL 1 (md5_blocks [a;b;c;d] blocks):int32) /\
        read RCX s = word_zx (EL 2 (md5_blocks [a;b;c;d] blocks):int32) /\
        read RDX s = word_zx (EL 3 (md5_blocks [a;b;c;d] blocks):int32)` THEN
  CONJ_TAC THENL
   [(* ==================== LEG 1: pc+0x8 -> seam ==================== *)
    ASM_CASES_TAC `val(nb:int64) = 0` THENL
     [(* nb = 0: prologue + cmp + je-taken straight to the seam. *)
      SUBGOAL_THEN `blocks:(int32 list)list = []` SUBST_ALL_TAC THENL
       [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[md5_blocks] THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC MD5_COMPRESS_EXEC (1--9) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `nb:int64 = word 0` SUBST_ALL_TAC THENL
       [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
      (* nb > 0: the pointer-counted do-while. *)
      ENSURES_WHILE_PUP_TAC `val(nb:int64)` `pc + 0x28` `pc + 0x8c4`
       `\i s. (read RBP s = statep /\
               read RDI s = word_add datap (word (64 * val(nb:int64))) /\
               read RSI s = word_add datap (word (64 * i)) /\
               read RAX s = word_zx (EL 0 (md5_blocks [a;b;c;d]
                              (SUB_LIST(0,i) blocks)):int32) /\
               read RBX s = word_zx (EL 1 (md5_blocks [a;b;c;d]
                              (SUB_LIST(0,i) blocks)):int32) /\
               read RCX s = word_zx (EL 2 (md5_blocks [a;b;c;d]
                              (SUB_LIST(0,i) blocks)):int32) /\
               read RDX s = word_zx (EL 3 (md5_blocks [a;b;c;d]
                              (SUB_LIST(0,i) blocks)):int32) /\
               (!j k. j < val nb /\ k < 16
                      ==> read (memory :> bytes32
                                 (word_add datap (word (64 * j + 4 * k)))) s
                          = EL k (EL j (blocks:(int32 list)list)))) /\
              (read CF s <=> i < val(nb:int64))` THEN
      REPEAT CONJ_TAC THENL
       [(* ~(val nb = 0) *)
        ASM_REWRITE_TAC[];
        (* init leg pc+0x8 -> pc+0x28 (p 0) *)
        REWRITE_TAC[SUB_LIST_NIL_FOLD; MULT_CLAUSES; WORD_ADD_0] THEN
        ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC MD5_COMPRESS_EXEC (1--9) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[WORD_SHL_6; MULT_CLAUSES] THEN
        CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `val(word(64 * val(nb:int64)):int64) = 64 * val nb`
          ASSUME_TAC THENL
         [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
          MATCH_MP_TAC LET_TRANS THEN
          EXISTS_TAC `val(datap:int64) + 64 * val(nb:int64)` THEN
          ASM_REWRITE_TAC[LE_ADDR]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
         [SUBGOAL_THEN `~(val(word_neg(word(64 * val(nb:int64)):int64)) = 0)`
            MP_TAC THENL
           [MATCH_MP_TAC WORD_NEG_BYTECOUNT_NZ THEN ASM_REWRITE_TAC[] THEN
            MATCH_MP_TAC LET_TRANS THEN
            EXISTS_TAC `val(datap:int64) + 64 * val(nb:int64)` THEN
            ASM_REWRITE_TAC[LE_ADDR]; ASM_REWRITE_TAC[]];
          REFL_TAC];
        (* body leg i -> i+1 (MD5_LOOP_BODY_STEP, flatten to match grouping) *)
        REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
        MATCH_MP_TAC(REWRITE_RULE[SOME_FLAGS; GSYM CONJ_ASSOC]
                     MD5_LOOP_BODY_STEP) THEN
        ASM_REWRITE_TAC[];
        (* back-edge leg pc+0x8c4 -> pc+0x28 (jb taken, CF set) *)
        REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC MD5_COMPRESS_EXEC (1--1) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
        (* exit leg pc+0x8c4 -> seam pc+0x8ca (jb NOT taken, CF clear) *)
        SUBGOAL_THEN `SUB_LIST(0,val(nb:int64)) (blocks:(int32 list)list) = blocks`
          SUBST1_TAC THENL
         [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUB_LIST_FULL_FOLD];
          ALL_TAC] THEN
        ENSURES_INIT_TAC "s0" THEN
        X86_STEPS_TAC MD5_COMPRESS_EXEC (1--1) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]];
    (* ==================== LEG 2: stores pc+0x8ca -> pc+0x8d6 ========= *)
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MD5_COMPRESS_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL; DIMINDEX_32; DIMINDEX_64;
             LE_REFL; ARITH]]);;

(* ========================================================================= *)
(* The SysV subroutine theorems (full function, incl. prologue and           *)
(* epilogue), wrapping the core via the standard return-stack tactic.        *)
(*                                                                           *)
(* Prologue (entry .. pc+0x8 core start): 5 callee-save pushes               *)
(*   push %rbp; push %rbx; push %r12; push %r14; push %r15   (no `sub rsp`)  *)
(* so the frame is 5*8 = 40 bytes below the caller SP, hence stackoff = 40   *)
(* (= 8*5, so GEN_X86_ADD_RETURN_STACK_TAC's prologue-step count n = 5).     *)
(*                                                                           *)
(* Epilogue (core end pc+0x8d6 .. ret): this routine does NOT use `pop`; it  *)
(* restores the saved registers with explicit loads and then bumps SP once:  *)
(*   mov (%rsp),%r15; mov 0x8(%rsp),%r14; mov 0x10(%rsp),%r12;               *)
(*   mov 0x18(%rsp),%rbx; mov 0x20(%rsp),%rbp; add $0x28,%rsp; ret           *)
(* = 7 instructions (5 movs + add + ret), one MORE than the pop-based form   *)
(* (5 pops + ret = 6) that the (n,n+1) convenience wrapper assumes.  So we   *)
(* call GEN_X86_ADD_RETURN_STACK_TAC directly with explicit (pre,post)=(5,7).*)
(*                                                                           *)
(* The promoted core's `nonoverlapping (word pc, LENGTH(BUTLAST tmc)) ...`   *)
(* antecedent is discharged by NONOVERLAPPING_TAC, which needs the code      *)
(* length as a NUMERAL; we therefore rewrite LENGTH(BUTLAST tmc) -> 2290     *)
(* (fst MD5_COMPRESS_EXEC) in the core before promoting it.      *)
(* ========================================================================= *)

let MD5_COMPRESS_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a b c d blocks statep datap nb pc stackpointer returnaddress.
        nonoverlapping (word pc, LENGTH md5_compress_tmc)
                       (statep:int64, 16) /\
        nonoverlapping (statep:int64, 16) (datap:int64, 64 * val(nb:int64)) /\
        nonoverlapping (word_sub stackpointer (word 40), 48) (statep:int64, 16) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40), 40))
            [(word pc, LENGTH md5_compress_tmc);
             (datap:int64, 64 * val(nb:int64))] /\
        val datap + 64 * val nb < 2 EXP 64 /\
        LENGTH blocks = val nb
        ==> ensures x86
              (\s. bytes_loaded s (word pc) md5_compress_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   C_ARGUMENTS [statep; datap; nb] s /\
                   read (memory :> bytes32 statep) s = (a:int32) /\
                   read (memory :> bytes32 (word_add statep (word 4))) s = (b:int32) /\
                   read (memory :> bytes32 (word_add statep (word 8))) s = (c:int32) /\
                   read (memory :> bytes32 (word_add statep (word 12))) s = (d:int32) /\
                   (!j k. j < val nb /\ k < 16
                          ==> read (memory :> bytes32
                                     (word_add datap (word (64 * j + 4 * k)))) s
                              = EL k (EL j (blocks:(int32 list)list))))
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   read (memory :> bytes32 statep) s =
                     EL 0 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 4))) s =
                     EL 1 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 8))) s =
                     EL 2 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 12))) s =
                     EL 3 (md5_blocks [a;b;c;d] blocks))
              (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes (statep, 16);
                          memory :> bytes (word_sub stackpointer (word 40), 40)])`,
  GEN_X86_ADD_RETURN_STACK_TAC
    (X86_MK_EXEC_RULE md5_compress_tmc)
    (X86_CORE_PROMOTE
       (REWRITE_RULE[fst MD5_COMPRESS_EXEC]
          MD5_COMPRESS_CORRECT))
    `[RBP; RBX; R12; R14; R15]` 40 (5,7));;

(* IBT variant: identical statement against the full (untrimmed) _mc,        *)
(* derived from the NOIBT theorem by ADD_IBT_RULE (re-adds the ENDBR64).     *)
let MD5_COMPRESS_SUBROUTINE_CORRECT = prove
 (`!a b c d blocks statep datap nb pc stackpointer returnaddress.
        nonoverlapping (word pc, LENGTH md5_compress_mc)
                       (statep:int64, 16) /\
        nonoverlapping (statep:int64, 16) (datap:int64, 64 * val(nb:int64)) /\
        nonoverlapping (word_sub stackpointer (word 40), 48) (statep:int64, 16) /\
        ALL (nonoverlapping (word_sub stackpointer (word 40), 40))
            [(word pc, LENGTH md5_compress_mc);
             (datap:int64, 64 * val(nb:int64))] /\
        val datap + 64 * val nb < 2 EXP 64 /\
        LENGTH blocks = val nb
        ==> ensures x86
              (\s. bytes_loaded s (word pc) md5_compress_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   C_ARGUMENTS [statep; datap; nb] s /\
                   read (memory :> bytes32 statep) s = (a:int32) /\
                   read (memory :> bytes32 (word_add statep (word 4))) s = (b:int32) /\
                   read (memory :> bytes32 (word_add statep (word 8))) s = (c:int32) /\
                   read (memory :> bytes32 (word_add statep (word 12))) s = (d:int32) /\
                   (!j k. j < val nb /\ k < 16
                          ==> read (memory :> bytes32
                                     (word_add datap (word (64 * j + 4 * k)))) s
                              = EL k (EL j (blocks:(int32 list)list))))
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   read (memory :> bytes32 statep) s =
                     EL 0 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 4))) s =
                     EL 1 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 8))) s =
                     EL 2 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 12))) s =
                     EL 3 (md5_blocks [a;b;c;d] blocks))
              (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes (statep, 16);
                          memory :> bytes (word_sub stackpointer (word 40), 40)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MD5_COMPRESS_NOIBT_SUBROUTINE_CORRECT));;

(* ========================================================================= *)
(* The Windows-ABI subroutine theorems.                                      *)
(*                                                                           *)
(* The Windows object is the same MD5 body wrapped in a Windows prologue/    *)
(* epilogue.  Layout (objdump of the .obj):                                  *)
(*                                                                           *)
(* Prologue (entry .. core start):                                           *)
(*   push %rdi; push %rsi;                  (save Win-callee-saved rdi/rsi)  *)
(*   mov %rcx,%rdi; mov %rdx,%rsi; mov %r8,%rdx;    (Win->SysV arg shim)     *)
(*   push %rbp; push %rbx; push %r12; push %r14; push %r15                   *)
(*   = 10 instructions (prolog_len = 2 + nargs(3) + n(5) = 10), and the      *)
(*   Windows-specific prefix that the SysV core does NOT share is the first  *)
(*   11 bytes (push rdi/rsi + the 3 arg-shuffle movs), so pcoff = 11.        *)
(*                                                                           *)
(* Epilogue (core end .. ret): like the SysV body this routine restores      *)
(* callee-saves with explicit `mov` + a single `add $0x28,%rsp`, NOT `pop`;  *)
(* then it pops the two Windows-saved regs and returns:                      *)
(*   mov (%rsp),%r15; mov 0x8(%rsp),%r14; mov 0x10(%rsp),%r12;               *)
(*   mov 0x18(%rsp),%rbx; mov 0x20(%rsp),%rbp; add $0x28,%rsp;               *)
(*   pop %rsi; pop %rdi; ret                                                 *)
(* = 9 instructions (5 movs + add + 2 pops + ret).  The stock                *)
(* WINDOWS_X86_WRAP_STACK_TAC (x86.ml) computes epilog_len = 3 + n = 8       *)
(* (pop-based: n callee-pops + pop rsi + pop rdi + ret) and so stops one     *)
(* instruction short of `ret`.  This is the exact Windows analogue of the    *)
(* SysV (5,7) quirk above: the mov-restore form needs one extra `add rsp`,   *)
(* hence epilog_len = 4 + n = 9.  We therefore use a local copy of the       *)
(* wrapper, WINDOWS_X86_WRAP_STACK_TAC_MR ("MR" = mov-restore epilogue),     *)
(* identical to the library tactic except for `epilog_len = 4 + n`.          *)
(*                                                                           *)
(* The wrapper consumes the *un-promoted* BUTLAST-form SysV core (it         *)
(* rebuilds the `bytes_loaded ... (BUTLAST stdmc)` segment itself via        *)
(* X86_TRIM_EXEC_RULE + N_SUBLIST_CONV), so unlike the SysV wrap above we    *)
(* do NOT apply X86_CORE_PROMOTE; we only rewrite LENGTH(BUTLAST tmc) ->     *)
(* 2290 so the wrapper's internal NONOVERLAPPING_TAC sees a numeral.         *)
(* Windows frame is 56 = 40 (SysV 5 pushes) + 16 (push rdi/rsi).             *)
(* ========================================================================= *)

let md5_compress_windows_mc =
  define_from_elf "md5_compress_windows_mc"
    "x86/md5/md5_compress.obj";;

let md5_compress_windows_tmc =
  define_trimmed "md5_compress_windows_tmc"
    md5_compress_windows_mc;;

(* Local copy of WINDOWS_X86_WRAP_STACK_TAC (x86.ml) with epilog_len bumped  *)
(* 3+n -> 4+n for the mov-restore-then-add-rsp epilogue (see comment above). *)
(* Verbatim otherwise; the only edit is the `epilog_len` line, flagged below.*)
let WINDOWS_X86_WRAP_STACK_TAC_MR =
  let monopsrlemma = MESON[]
     `(!x. P x ==> !p s r. Q x p s r)
      ==> (!x. P x) ==> (!x p s r. Q x p s r)`
  and pcofflemma = MESON[]
    `!n:num. (!x. P(x + n) ==> Q x) ==> (!x. P x) ==> (!x. Q x)`
  and pcplusplus_conv =
    GEN_REWRITE_CONV I
     [MESON[ADD_ASSOC] `word((pc + m) + n) = word(pc + m + n)`] THENC
    RAND_CONV(RAND_CONV NUM_ADD_CONV)
  and count_args =
    let argy = `WINDOWS_C_ARGUMENTS` in
    let is_nargle t = is_comb t && rator t = argy in
    fun t -> try
        (length o dest_list o rand o find_term is_nargle) t
      with _ -> failwith "Could not find WINDOWS_C_ARGUMENTS" in
  fun winmc stdmc coreth reglist stdstackoff (asl,w) ->
    let stdregs = dest_list reglist in
    let n =
      let n0 = length stdregs in if 8 * n0 = stdstackoff then n0 else n0 + 1 in
    let regs = [`RSI`; `RDI`] @ stdregs
    and stackoff = stdstackoff + 16 in
    let nargs = count_args w in
    let prolog_len = 2 + nargs + n
    and epilog_len = 4 + n in   (* <-- ONLY EDIT vs x86.ml: was 3 + n        *)
    let pcoff =  match nargs with
      1 -> 5 | 2 -> 8 | 3 -> 11 | 4 -> 14 | 5 -> 19 | 6 -> 24 | _ -> 0 in
    let interstate = "s"^string_of_int(prolog_len+1)
    and subimpth =
      CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE [LENGTH]
        (MATCH_MP bytes_loaded_of_append3
          (TRANS winmc (N_SUBLIST_CONV
             (SPEC_ALL (X86_TRIM_EXEC_RULE stdmc)) pcoff
             (rhs(concl winmc))))))
    and winexecth = X86_MK_EXEC_RULE winmc in
    let is_coreth_safety = is_exists (concl coreth) in
    let check_safety_match_tac:tactic =
      fun (asl,w) ->
        if is_coreth_safety <> (is_exists w) then
          failwith "coreth must be `exists ..` iff the conclusion is"
        else ALL_TAC (asl,w) in

   (check_safety_match_tac THEN
    REWRITE_TAC [WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    PURE_REWRITE_TAC[WINDOWS_ABI_STACK_THM] THEN
    (if is_coreth_safety then
      ASSUME_CALLEE_SAFETY_TAC coreth "" THEN
      META_EXISTS_TAC THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (ONCE_REWRITE_RULE[append_lemma]th)) THEN
      REPEAT(CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[swap_forall])) THEN
             MATCH_MP_TAC monopsrlemma THEN GEN_TAC) THEN
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[swap_forall]))
     else
      MP_TAC coreth THEN
      REPEAT(MATCH_MP_TAC monopsrlemma THEN GEN_TAC)) THEN

    REWRITE_TAC[fst winexecth] THEN
    MATCH_MP_TAC pcofflemma THEN
    EXISTS_TAC (mk_small_numeral pcoff) THEN GEN_TAC THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV pcplusplus_conv)) THEN
    (if vfree_in `RSP` (concl coreth) then
      (if is_coreth_safety then
        CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[swap_forall]))
      else ALL_TAC) THEN
     DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th) THEN
     MATCH_MP_TAC MONO_FORALL THEN GEN_TAC
    else
     DISCH_THEN(fun th ->
       WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th)) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
        REPEAT GEN_TAC THEN
        TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
        MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    (if is_coreth_safety then
      ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
      META_EXISTS_TAC
     else
      ALL_TAC) THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
     DISCH_THEN(fun th ->
      MAP_EVERY (fun c ->
                    ENSURES_PRESERVED_TAC ("init_"^fst(dest_const c)) c)
                regs THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC winexecth (1--prolog_len) THEN
      MP_TAC th) THEN
    X86_BIGSTEP_TAC winexecth interstate THENL
     [(if is_coreth_safety then
        CONJ_TAC THENL [ALL_TAC;
          TRY (CONV_TAC (LAND_CONV CONS_TO_APPEND_CONV) THEN
            BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN
            NO_TAC)]
        else ALL_TAC) THEN
      MATCH_MP_TAC subimpth THEN FIRST_X_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC winexecth ((prolog_len+2)--(prolog_len+epilog_len+1)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) (asl,w);;

let MD5_COMPRESS_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a b c d blocks statep datap nb pc stackpointer returnaddress.
        nonoverlapping (word pc, LENGTH md5_compress_windows_tmc)
                       (statep:int64, 16) /\
        nonoverlapping (statep:int64, 16) (datap:int64, 64 * val(nb:int64)) /\
        nonoverlapping (word_sub stackpointer (word 56), 64) (statep:int64, 16) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56), 56))
            [(word pc, LENGTH md5_compress_windows_tmc);
             (datap:int64, 64 * val(nb:int64))] /\
        val datap + 64 * val nb < 2 EXP 64 /\
        LENGTH blocks = val nb
        ==> ensures x86
              (\s. bytes_loaded s (word pc) md5_compress_windows_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [statep; datap; nb] s /\
                   read (memory :> bytes32 statep) s = (a:int32) /\
                   read (memory :> bytes32 (word_add statep (word 4))) s = (b:int32) /\
                   read (memory :> bytes32 (word_add statep (word 8))) s = (c:int32) /\
                   read (memory :> bytes32 (word_add statep (word 12))) s = (d:int32) /\
                   (!j k. j < val nb /\ k < 16
                          ==> read (memory :> bytes32
                                     (word_add datap (word (64 * j + 4 * k)))) s
                              = EL k (EL j (blocks:(int32 list)list))))
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   read (memory :> bytes32 statep) s =
                     EL 0 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 4))) s =
                     EL 1 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 8))) s =
                     EL 2 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 12))) s =
                     EL 3 (md5_blocks [a;b;c;d] blocks))
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes (statep, 16);
                          memory :> bytes (word_sub stackpointer (word 56), 56)])`,
  WINDOWS_X86_WRAP_STACK_TAC_MR
    md5_compress_windows_tmc md5_compress_tmc
    (REWRITE_RULE[fst MD5_COMPRESS_EXEC]
       MD5_COMPRESS_CORRECT)
    `[RBP; RBX; R12; R14; R15]` 40);;

(* IBT variant: identical statement against the full (untrimmed) Windows     *)
(* _mc, derived from the NOIBT theorem by ADD_IBT_RULE.                      *)
let MD5_COMPRESS_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a b c d blocks statep datap nb pc stackpointer returnaddress.
        nonoverlapping (word pc, LENGTH md5_compress_windows_mc)
                       (statep:int64, 16) /\
        nonoverlapping (statep:int64, 16) (datap:int64, 64 * val(nb:int64)) /\
        nonoverlapping (word_sub stackpointer (word 56), 64) (statep:int64, 16) /\
        ALL (nonoverlapping (word_sub stackpointer (word 56), 56))
            [(word pc, LENGTH md5_compress_windows_mc);
             (datap:int64, 64 * val(nb:int64))] /\
        val datap + 64 * val nb < 2 EXP 64 /\
        LENGTH blocks = val nb
        ==> ensures x86
              (\s. bytes_loaded s (word pc) md5_compress_windows_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [statep; datap; nb] s /\
                   read (memory :> bytes32 statep) s = (a:int32) /\
                   read (memory :> bytes32 (word_add statep (word 4))) s = (b:int32) /\
                   read (memory :> bytes32 (word_add statep (word 8))) s = (c:int32) /\
                   read (memory :> bytes32 (word_add statep (word 12))) s = (d:int32) /\
                   (!j k. j < val nb /\ k < 16
                          ==> read (memory :> bytes32
                                     (word_add datap (word (64 * j + 4 * k)))) s
                              = EL k (EL j (blocks:(int32 list)list))))
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   read (memory :> bytes32 statep) s =
                     EL 0 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 4))) s =
                     EL 1 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 8))) s =
                     EL 2 (md5_blocks [a;b;c;d] blocks) /\
                   read (memory :> bytes32 (word_add statep (word 12))) s =
                     EL 3 (md5_blocks [a;b;c;d] blocks))
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes (statep, 16);
                          memory :> bytes (word_sub stackpointer (word 56), 56)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE MD5_COMPRESS_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;
