(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The x25519 function for curve25519 on the standard basepoint 9.           *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/bignum_inv_p25519.ml";;
needs "common/ecencoding.ml";;

needs "EC/family25519.ml";;
needs "EC/exprojective.ml";;
needs "EC/x25519.ml";;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The code; however, the text segment here contains data at the end         *)
(* so we manually split that off to avoid confusing the decoder.             *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_relocs_from_elf "x86/curve25519/curve25519_x25519base.o";;
 ****)

(* The .text body of curve25519_x25519base is identical between the Linux ABI .o
   and the Windows .obj (the latter merely prepends a small dispatcher that
   shuffles arguments and invokes the Linux ABI entry).  We share the body bytes
   between the two mc declarations to avoid a ~3500-line duplicate.  The
   `prefix` argument is the byte sequence preceding the function body
   (ENDBR64 alone for Linux ABI; ENDBR64 + ABI dispatcher for Windows). *)

let curve25519_x25519base_body : 'a. int list -> (int list -> 'a) ->
                                     (string * int -> 'a) -> 'a list =
  fun prefix b ADDR -> [b(prefix @ [
  0x53;                    (* PUSH (% rbx) *)
  0x55;                    (* PUSH (% rbp) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x41; 0x57;              (* PUSH (% r15) *)
  0x48; 0x81; 0xec; 0xe8; 0x01; 0x00; 0x00;
                           (* SUB (% rsp) (Imm32 (word 488)) *)
  0x48; 0x89; 0xbc; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,448))) (% rdi) *)
  0x48; 0x8b; 0x06;        (* MOV (% rax) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x89; 0x04; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rax) *)
  0x48; 0x8b; 0x46; 0x08;  (* MOV (% rax) (Memop Quadword (%% (rsi,8))) *)
  0x48; 0x89; 0x44; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rax) *)
  0x48; 0x8b; 0x46; 0x10;  (* MOV (% rax) (Memop Quadword (%% (rsi,16))) *)
  0x48; 0x89; 0x44; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rax) *)
  0x48; 0xb8; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x3f;
                           (* MOV (% rax) (Imm64 (word 4611686018427387903)) *)
  0x48; 0x23; 0x46; 0x18;  (* AND (% rax) (Memop Quadword (%% (rsi,24))) *)
  0x48; 0x89; 0x44; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rax) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x83; 0xe0; 0x08;  (* AND (% rax) (Imm8 (word 8)) *)
  0x4c; 0x8d; 0x15]); ADDR ("WHOLE_READONLY_data",(-4)); b[
                           (* LEA (% r10) (Riprel (word_sx (iword (&WHOLE_READONLY_data - (&pc + &88))))) *)
  0x4d; 0x8d; 0x5a; 0x60;  (* LEA (% r11) (%% (r10,96)) *)
  0x49; 0x8b; 0x02;        (* MOV (% rax) (Memop Quadword (%% (r10,0))) *)
  0x49; 0x8b; 0x0b;        (* MOV (% rcx) (Memop Quadword (%% (r11,0))) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rax) *)
  0x49; 0x8b; 0x42; 0x08;  (* MOV (% rax) (Memop Quadword (%% (r10,8))) *)
  0x49; 0x8b; 0x4b; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (r11,8))) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rax) *)
  0x49; 0x8b; 0x42; 0x10;  (* MOV (% rax) (Memop Quadword (%% (r10,16))) *)
  0x49; 0x8b; 0x4b; 0x10;  (* MOV (% rcx) (Memop Quadword (%% (r11,16))) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% rax) *)
  0x49; 0x8b; 0x42; 0x18;  (* MOV (% rax) (Memop Quadword (%% (r10,24))) *)
  0x49; 0x8b; 0x4b; 0x18;  (* MOV (% rcx) (Memop Quadword (%% (r11,24))) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% rax) *)
  0x49; 0x8b; 0x42; 0x20;  (* MOV (% rax) (Memop Quadword (%% (r10,32))) *)
  0x49; 0x8b; 0x4b; 0x20;  (* MOV (% rcx) (Memop Quadword (%% (r11,32))) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rax) *)
  0x49; 0x8b; 0x42; 0x28;  (* MOV (% rax) (Memop Quadword (%% (r10,40))) *)
  0x49; 0x8b; 0x4b; 0x28;  (* MOV (% rcx) (Memop Quadword (%% (r11,40))) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% rax) *)
  0x49; 0x8b; 0x42; 0x30;  (* MOV (% rax) (Memop Quadword (%% (r10,48))) *)
  0x49; 0x8b; 0x4b; 0x30;  (* MOV (% rcx) (Memop Quadword (%% (r11,48))) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% rax) *)
  0x49; 0x8b; 0x42; 0x38;  (* MOV (% rax) (Memop Quadword (%% (r10,56))) *)
  0x49; 0x8b; 0x4b; 0x38;  (* MOV (% rcx) (Memop Quadword (%% (r11,56))) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% rax) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x48; 0x89; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% rax) *)
  0xb8; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 0)) *)
  0x48; 0x89; 0x84; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% rax) *)
  0x49; 0x8b; 0x42; 0x40;  (* MOV (% rax) (Memop Quadword (%% (r10,64))) *)
  0x49; 0x8b; 0x4b; 0x40;  (* MOV (% rcx) (Memop Quadword (%% (r11,64))) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% rax) *)
  0x49; 0x8b; 0x42; 0x48;  (* MOV (% rax) (Memop Quadword (%% (r10,72))) *)
  0x49; 0x8b; 0x4b; 0x48;  (* MOV (% rcx) (Memop Quadword (%% (r11,72))) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% rax) *)
  0x49; 0x8b; 0x42; 0x50;  (* MOV (% rax) (Memop Quadword (%% (r10,80))) *)
  0x49; 0x8b; 0x4b; 0x50;  (* MOV (% rcx) (Memop Quadword (%% (r11,80))) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% rax) *)
  0x49; 0x8b; 0x42; 0x58;  (* MOV (% rax) (Memop Quadword (%% (r10,88))) *)
  0x49; 0x8b; 0x4b; 0x58;  (* MOV (% rcx) (Memop Quadword (%% (r11,88))) *)
  0x48; 0x0f; 0x45; 0xc1;  (* CMOVNE (% rax) (% rcx) *)
  0x48; 0x89; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,248))) (% rax) *)
  0x48; 0xc7; 0x84; 0x24; 0xc8; 0x01; 0x00; 0x00; 0x04; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,456))) (Imm32 (word 4)) *)
  0x49; 0x8d; 0x82; 0xc0; 0x00; 0x00; 0x00;
                           (* LEA (% rax) (%% (r10,192)) *)
  0x48; 0x89; 0x84; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,480))) (% rax) *)
  0x48; 0xc7; 0x84; 0x24; 0xd0; 0x01; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,464))) (Imm32 (word 0)) *)
  0x48; 0x8b; 0x84; 0x24; 0xc8; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,456))) *)
  0x48; 0x89; 0xc1;        (* MOV (% rcx) (% rax) *)
  0x48; 0xc1; 0xe8; 0x06;  (* SHR (% rax) (Imm8 (word 6)) *)
  0x48; 0x8b; 0x04; 0xc4;  (* MOV (% rax) (Memop Quadword (%%% (rsp,3,rax))) *)
  0x48; 0xd3; 0xe8;        (* SHR (% rax) (% cl) *)
  0x48; 0x83; 0xe0; 0x0f;  (* AND (% rax) (Imm8 (word 15)) *)
  0x48; 0x03; 0x84; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* ADD (% rax) (Memop Quadword (%% (rsp,464))) *)
  0x48; 0x89; 0x84; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,472))) (% rax) *)
  0x48; 0x83; 0xbc; 0x24; 0xd8; 0x01; 0x00; 0x00; 0x09;
                           (* CMP (Memop Quadword (%% (rsp,472))) (Imm8 (word 9)) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xff; 0xc0;        (* INC (% rax) *)
  0x48; 0x89; 0x84; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,464))) (% rax) *)
  0x48; 0xc7; 0xc7; 0x10; 0x00; 0x00; 0x00;
                           (* MOV (% rdi) (Imm32 (word 16)) *)
  0x48; 0x2b; 0xbc; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* SUB (% rdi) (Memop Quadword (%% (rsp,472))) *)
  0x48; 0x83; 0xbc; 0x24; 0xd0; 0x01; 0x00; 0x00; 0x00;
                           (* CMP (Memop Quadword (%% (rsp,464))) (Imm8 (word 0)) *)
  0x48; 0x0f; 0x44; 0xbc; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* CMOVE (% rdi) (Memop Quadword (%% (rsp,472))) *)
  0x48; 0x89; 0xbc; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,472))) (% rdi) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xd2;              (* XOR (% edx) (% edx) *)
  0x41; 0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% r8d) (Imm32 (word 1)) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x45; 0x31; 0xdb;        (* XOR (% r11d) (% r11d) *)
  0x45; 0x31; 0xe4;        (* XOR (% r12d) (% r12d) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0x8b; 0xac; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,480))) *)
  0x48; 0x83; 0xbc; 0x24; 0xd8; 0x01; 0x00; 0x00; 0x01;
                           (* CMP (Memop Quadword (%% (rsp,472))) (Imm8 (word 1)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xd8; 0x01; 0x00; 0x00; 0x02;
                           (* CMP (Memop Quadword (%% (rsp,472))) (Imm8 (word 2)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xd8; 0x01; 0x00; 0x00; 0x03;
                           (* CMP (Memop Quadword (%% (rsp,472))) (Imm8 (word 3)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xd8; 0x01; 0x00; 0x00; 0x04;
                           (* CMP (Memop Quadword (%% (rsp,472))) (Imm8 (word 4)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xd8; 0x01; 0x00; 0x00; 0x05;
                           (* CMP (Memop Quadword (%% (rsp,472))) (Imm8 (word 5)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xd8; 0x01; 0x00; 0x00; 0x06;
                           (* CMP (Memop Quadword (%% (rsp,472))) (Imm8 (word 6)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xd8; 0x01; 0x00; 0x00; 0x07;
                           (* CMP (Memop Quadword (%% (rsp,472))) (Imm8 (word 7)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x83; 0xbc; 0x24; 0xd8; 0x01; 0x00; 0x00; 0x08;
                           (* CMP (Memop Quadword (%% (rsp,472))) (Imm8 (word 8)) *)
  0x48; 0x8b; 0x75; 0x00;  (* MOV (% rsi) (Memop Quadword (%% (rbp,0))) *)
  0x48; 0x0f; 0x44; 0xc6;  (* CMOVE (% rax) (% rsi) *)
  0x48; 0x8b; 0x75; 0x08;  (* MOV (% rsi) (Memop Quadword (%% (rbp,8))) *)
  0x48; 0x0f; 0x44; 0xde;  (* CMOVE (% rbx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x10;  (* MOV (% rsi) (Memop Quadword (%% (rbp,16))) *)
  0x48; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x18;  (* MOV (% rsi) (Memop Quadword (%% (rbp,24))) *)
  0x48; 0x0f; 0x44; 0xd6;  (* CMOVE (% rdx) (% rsi) *)
  0x48; 0x8b; 0x75; 0x20;  (* MOV (% rsi) (Memop Quadword (%% (rbp,32))) *)
  0x4c; 0x0f; 0x44; 0xc6;  (* CMOVE (% r8) (% rsi) *)
  0x48; 0x8b; 0x75; 0x28;  (* MOV (% rsi) (Memop Quadword (%% (rbp,40))) *)
  0x4c; 0x0f; 0x44; 0xce;  (* CMOVE (% r9) (% rsi) *)
  0x48; 0x8b; 0x75; 0x30;  (* MOV (% rsi) (Memop Quadword (%% (rbp,48))) *)
  0x4c; 0x0f; 0x44; 0xd6;  (* CMOVE (% r10) (% rsi) *)
  0x48; 0x8b; 0x75; 0x38;  (* MOV (% rsi) (Memop Quadword (%% (rbp,56))) *)
  0x4c; 0x0f; 0x44; 0xde;  (* CMOVE (% r11) (% rsi) *)
  0x48; 0x8b; 0x75; 0x40;  (* MOV (% rsi) (Memop Quadword (%% (rbp,64))) *)
  0x4c; 0x0f; 0x44; 0xe6;  (* CMOVE (% r12) (% rsi) *)
  0x48; 0x8b; 0x75; 0x48;  (* MOV (% rsi) (Memop Quadword (%% (rbp,72))) *)
  0x4c; 0x0f; 0x44; 0xee;  (* CMOVE (% r13) (% rsi) *)
  0x48; 0x8b; 0x75; 0x50;  (* MOV (% rsi) (Memop Quadword (%% (rbp,80))) *)
  0x4c; 0x0f; 0x44; 0xf6;  (* CMOVE (% r14) (% rsi) *)
  0x48; 0x8b; 0x75; 0x58;  (* MOV (% rsi) (Memop Quadword (%% (rbp,88))) *)
  0x4c; 0x0f; 0x44; 0xfe;  (* CMOVE (% r15) (% rsi) *)
  0x48; 0x83; 0xc5; 0x60;  (* ADD (% rbp) (Imm8 (word 96)) *)
  0x48; 0x89; 0xac; 0x24; 0xe0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,480))) (% rbp) *)
  0x48; 0x83; 0xbc; 0x24; 0xd0; 0x01; 0x00; 0x00; 0x00;
                           (* CMP (Memop Quadword (%% (rsp,464))) (Imm8 (word 0)) *)
  0x48; 0x89; 0xc6;        (* MOV (% rsi) (% rax) *)
  0x49; 0x0f; 0x45; 0xf0;  (* CMOVNE (% rsi) (% r8) *)
  0x4c; 0x0f; 0x45; 0xc0;  (* CMOVNE (% r8) (% rax) *)
  0x48; 0x89; 0x74; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rsi) *)
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x48; 0x89; 0xde;        (* MOV (% rsi) (% rbx) *)
  0x49; 0x0f; 0x45; 0xf1;  (* CMOVNE (% rsi) (% r9) *)
  0x4c; 0x0f; 0x45; 0xcb;  (* CMOVNE (% r9) (% rbx) *)
  0x48; 0x89; 0x74; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rsi) *)
  0x4c; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r9) *)
  0x48; 0x89; 0xce;        (* MOV (% rsi) (% rcx) *)
  0x49; 0x0f; 0x45; 0xf2;  (* CMOVNE (% rsi) (% r10) *)
  0x4c; 0x0f; 0x45; 0xd1;  (* CMOVNE (% r10) (% rcx) *)
  0x48; 0x89; 0x74; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rsi) *)
  0x4c; 0x89; 0x54; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r10) *)
  0x48; 0x89; 0xd6;        (* MOV (% rsi) (% rdx) *)
  0x49; 0x0f; 0x45; 0xf3;  (* CMOVNE (% rsi) (% r11) *)
  0x4c; 0x0f; 0x45; 0xda;  (* CMOVNE (% r11) (% rdx) *)
  0x48; 0x89; 0x74; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rsi) *)
  0x4c; 0x89; 0x5c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% r11) *)
  0x48; 0xc7; 0xc0; 0xed; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm32 (word 4294967277)) *)
  0x48; 0xc7; 0xc3; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rbx) (Imm32 (word 4294967295)) *)
  0x48; 0xc7; 0xc1; 0xff; 0xff; 0xff; 0xff;
                           (* MOV (% rcx) (Imm32 (word 4294967295)) *)
  0x48; 0xba; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x7f;
                           (* MOV (% rdx) (Imm64 (word 9223372036854775807)) *)
  0x4c; 0x29; 0xe0;        (* SUB (% rax) (% r12) *)
  0x4c; 0x19; 0xeb;        (* SBB (% rbx) (% r13) *)
  0x4c; 0x19; 0xf1;        (* SBB (% rcx) (% r14) *)
  0x4c; 0x19; 0xfa;        (* SBB (% rdx) (% r15) *)
  0x4c; 0x8b; 0x84; 0x24; 0xd8; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,472))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0xd0; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,464))) *)
  0x4d; 0x85; 0xc0;        (* TEST (% r8) (% r8) *)
  0x4d; 0x0f; 0x44; 0xc8;  (* CMOVE (% r9) (% r8) *)
  0x4d; 0x85; 0xc9;        (* TEST (% r9) (% r9) *)
  0x49; 0x0f; 0x44; 0xc4;  (* CMOVE (% rax) (% r12) *)
  0x49; 0x0f; 0x44; 0xdd;  (* CMOVE (% rbx) (% r13) *)
  0x49; 0x0f; 0x44; 0xce;  (* CMOVE (% rcx) (% r14) *)
  0x49; 0x0f; 0x44; 0xd7;  (* CMOVE (% rdx) (% r15) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x48; 0x89; 0x5c; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rbx) *)
  0x48; 0x89; 0x4c; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rcx) *)
  0x48; 0x89; 0x54; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rdx) *)
  0x4c; 0x8b; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,192))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4d; 0x01; 0xc0;        (* ADD (% r8) (% r8) *)
  0x4c; 0x8b; 0x8c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,200))) *)
  0x4d; 0x11; 0xc9;        (* ADC (% r9) (% r9) *)
  0x4c; 0x8b; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,208))) *)
  0x4d; 0x11; 0xd2;        (* ADC (% r10) (% r10) *)
  0x4c; 0x8b; 0x9c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,216))) *)
  0x4d; 0x11; 0xdb;        (* ADC (% r11) (% r11) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% r11) *)
  0x4c; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,160))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,136))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,176))) *)
  0x4c; 0x1b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x48; 0x8b; 0x84; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,184))) *)
  0x48; 0x1b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% r10) *)
  0x48; 0x89; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% rax) *)
  0x4c; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,160))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x13; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,176))) *)
  0x4c; 0x13; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,184))) *)
  0x4c; 0x13; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,152))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,344))) (% r11) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x60;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,96))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,224))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,232))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,240))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,248))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x68;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,104))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,224))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,232))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,240))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,248))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x70;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,112))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,224))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,232))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,240))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,248))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x78;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,120))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,224))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,232))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,240))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,248))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xba; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 38)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdc;
                           (* MULX4 (% rbx,% rax) (% rdx,% r12) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdd;
                           (* MULX4 (% rbx,% rax) (% rdx,% r13) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xde;
                           (* MULX4 (% rbx,% rax) (% rdx,% r14) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x42; 0xfb; 0xf6; 0xe7;
                           (* MULX4 (% r12,% rax) (% rdx,% r15) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADCX (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,352))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,360))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,368))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,376))) (% r11) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x20;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,32))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,288))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,296))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,304))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,312))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x28;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,40))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,288))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,296))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,304))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,312))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x30;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,48))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,288))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,296))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,304))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,312))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x38;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,56))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,288))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,296))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,304))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,312))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xba; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 38)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdc;
                           (* MULX4 (% rbx,% rax) (% rdx,% r12) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdd;
                           (* MULX4 (% rbx,% rax) (% rdx,% r13) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xde;
                           (* MULX4 (% rbx,% rax) (% rdx,% r14) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x42; 0xfb; 0xf6; 0xe7;
                           (* MULX4 (% r12,% rax) (% rdx,% r15) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADCX (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% r11) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x40;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,64))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,320))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,328))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,336))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,344))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x48;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,72))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,320))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,328))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,336))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,344))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x50;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,80))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,320))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,328))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,336))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,344))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x54; 0x24; 0x58;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,88))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,320))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,328))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,336))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,344))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xba; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 38)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdc;
                           (* MULX4 (% rbx,% rax) (% rdx,% r12) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdd;
                           (* MULX4 (% rbx,% rax) (% rdx,% r13) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xde;
                           (* MULX4 (% rbx,% rax) (% rdx,% r14) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x42; 0xfb; 0xf6; 0xe7;
                           (* MULX4 (% r12,% rax) (% rdx,% r15) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADCX (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,344))) (% r11) *)
  0x4c; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,256))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x84; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,352))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,264))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,360))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,272))) *)
  0x4c; 0x1b; 0x94; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,368))) *)
  0x48; 0x8b; 0x84; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,280))) *)
  0x48; 0x1b; 0x84; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,376))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x84; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,384))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,392))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,400))) (% r10) *)
  0x48; 0x89; 0x84; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,408))) (% rax) *)
  0x4c; 0x8b; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,256))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x84; 0x24; 0x60; 0x01; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,352))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,264))) *)
  0x4c; 0x13; 0x8c; 0x24; 0x68; 0x01; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,360))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,272))) *)
  0x4c; 0x13; 0x94; 0x24; 0x70; 0x01; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,368))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,280))) *)
  0x4c; 0x13; 0x9c; 0x24; 0x78; 0x01; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,376))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,256))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,264))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,272))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,280))) (% r11) *)
  0x4c; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,320))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,288))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,328))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,296))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x94; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,336))) *)
  0x4c; 0x1b; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,304))) *)
  0x48; 0x8b; 0x84; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,344))) *)
  0x48; 0x1b; 0x84; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,312))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x84; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,416))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,424))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,432))) (% r10) *)
  0x48; 0x89; 0x84; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,440))) (% rax) *)
  0x4c; 0x8b; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,320))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,288))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,328))) *)
  0x4c; 0x13; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,296))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,336))) *)
  0x4c; 0x13; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,304))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,344))) *)
  0x4c; 0x13; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,312))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% r11) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,256))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,264))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,272))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,280))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,384))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,392))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,400))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,408))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xba; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 38)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdc;
                           (* MULX4 (% rbx,% rax) (% rdx,% r12) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdd;
                           (* MULX4 (% rbx,% rax) (% rdx,% r13) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xde;
                           (* MULX4 (% rbx,% rax) (% rdx,% r14) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x42; 0xfb; 0xf6; 0xe7;
                           (* MULX4 (% r12,% rax) (% rdx,% r15) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADCX (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xc8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,200))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xd0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,208))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xd8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,216))) (% r11) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x80; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,384))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,424))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x88; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,392))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,424))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x90; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,400))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,424))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x98; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,408))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,424))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xba; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 38)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdc;
                           (* MULX4 (% rbx,% rax) (% rdx,% r12) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdd;
                           (* MULX4 (% rbx,% rax) (% rdx,% r13) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xde;
                           (* MULX4 (% rbx,% rax) (% rdx,% r14) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x42; 0xfb; 0xf6; 0xe7;
                           (* MULX4 (% r12,% rax) (% rdx,% r15) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADCX (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% r11) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,288))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,256))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,264))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,272))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,280))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,296))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,256))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,264))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,272))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,280))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,304))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,256))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,264))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,272))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,280))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,312))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,256))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,264))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,272))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,280))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xba; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 38)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdc;
                           (* MULX4 (% rbx,% rax) (% rdx,% r12) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdd;
                           (* MULX4 (% rbx,% rax) (% rdx,% r13) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xde;
                           (* MULX4 (% rbx,% rax) (% rdx,% r14) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x42; 0xfb; 0xf6; 0xe7;
                           (* MULX4 (% r12,% rax) (% rdx,% r15) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADCX (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% r11) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,288))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,424))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xcc;        (* ADC (% r12) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,296))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,424))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADOX (% r13) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe9;
                           (* ADCX (% r13) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,304))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,424))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADOX (% r14) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf1;
                           (* ADCX (% r14) (% rcx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x94; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,312))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,416))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xa8; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,424))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0xb0; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,432))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0xb8; 0x01; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,440))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADOX (% r15) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf9;
                           (* ADCX (% r15) (% rcx) *)
  0xba; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 38)) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdc;
                           (* MULX4 (% rbx,% rax) (% rdx,% r12) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdd;
                           (* MULX4 (% rbx,% rax) (% rdx,% r13) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xde;
                           (* MULX4 (% rbx,% rax) (% rdx,% r14) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x42; 0xfb; 0xf6; 0xe7;
                           (* MULX4 (% r12,% rax) (% rdx,% r15) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADOX (% r12) (% rcx) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe1;
                           (* ADCX (% r12) (% rcx) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0x0f; 0xaf; 0xd4;  (* IMUL (% rdx) (% r12) *)
  0x49; 0x01; 0xd0;        (* ADD (% r8) (% rdx) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,224))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,232))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,240))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,248))) (% r11) *)
  0x48; 0x83; 0x84; 0x24; 0xc8; 0x01; 0x00; 0x00; 0x04;
                           (* ADD (Memop Quadword (%% (rsp,456))) (Imm8 (word 4)) *)
  0x48; 0x81; 0xbc; 0x24; 0xc8; 0x01; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (Memop Quadword (%% (rsp,456))) (Imm32 (word 256)) *)
  0x0f; 0x82; 0xe4; 0xe9; 0xff; 0xff;
                           (* JB (Imm32 (word 4294961636)) *)
  0x4c; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x03; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* ADD (% r8) (Memop Quadword (%% (rsp,224))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x13; 0x8c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* ADC (% r9) (Memop Quadword (%% (rsp,232))) *)
  0x4c; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x13; 0x94; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* ADC (% r10) (Memop Quadword (%% (rsp,240))) *)
  0x4c; 0x8b; 0x9c; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% r11) (Memop Quadword (%% (rsp,152))) *)
  0x4c; 0x13; 0x9c; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* ADC (% r11) (Memop Quadword (%% (rsp,248))) *)
  0xb8; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 38)) *)
  0x48; 0x0f; 0x43; 0xc1;  (* CMOVAE (% rax) (% rcx) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xc9;        (* ADC (% r9) (% rcx) *)
  0x49; 0x11; 0xca;        (* ADC (% r10) (% rcx) *)
  0x49; 0x11; 0xcb;        (* ADC (% r11) (% rcx) *)
  0x4c; 0x89; 0x84; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,288))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,296))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,304))) (% r10) *)
  0x4c; 0x89; 0x9c; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,312))) (% r11) *)
  0x4c; 0x8b; 0x84; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,128))) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x4c; 0x2b; 0x84; 0x24; 0xe0; 0x00; 0x00; 0x00;
                           (* SUB (% r8) (Memop Quadword (%% (rsp,224))) *)
  0x4c; 0x8b; 0x8c; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% r9) (Memop Quadword (%% (rsp,136))) *)
  0x4c; 0x1b; 0x8c; 0x24; 0xe8; 0x00; 0x00; 0x00;
                           (* SBB (% r9) (Memop Quadword (%% (rsp,232))) *)
  0xb9; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% ecx) (Imm32 (word 38)) *)
  0x4c; 0x8b; 0x94; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* MOV (% r10) (Memop Quadword (%% (rsp,144))) *)
  0x4c; 0x1b; 0x94; 0x24; 0xf0; 0x00; 0x00; 0x00;
                           (* SBB (% r10) (Memop Quadword (%% (rsp,240))) *)
  0x48; 0x8b; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x1b; 0x84; 0x24; 0xf8; 0x00; 0x00; 0x00;
                           (* SBB (% rax) (Memop Quadword (%% (rsp,248))) *)
  0x48; 0x0f; 0x43; 0xcb;  (* CMOVAE (% rcx) (% rbx) *)
  0x49; 0x29; 0xc8;        (* SUB (% r8) (% rcx) *)
  0x49; 0x19; 0xd9;        (* SBB (% r9) (% rbx) *)
  0x49; 0x19; 0xda;        (* SBB (% r10) (% rbx) *)
  0x48; 0x19; 0xd8;        (* SBB (% rax) (% rbx) *)
  0x4c; 0x89; 0x84; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,320))) (% r8) *)
  0x4c; 0x89; 0x8c; 0x24; 0x48; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,328))) (% r9) *)
  0x4c; 0x89; 0x94; 0x24; 0x50; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,336))) (% r10) *)
  0x48; 0x89; 0x84; 0x24; 0x58; 0x01; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,344))) (% rax) *)
  0x48; 0x8d; 0xbc; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* LEA (% rdi) (%% (rsp,256)) *)
  0x48; 0x8d; 0xb4; 0x24; 0x40; 0x01; 0x00; 0x00;
                           (* LEA (% rsi) (%% (rsp,320)) *)
  0x48; 0x89; 0xbc; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,192))) (% rdi) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x8d; 0x48; 0xed;  (* LEA (% rcx) (%% (rax,18446744073709551597)) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x89; 0x0c; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rcx) *)
  0x48; 0x89; 0x44; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rax) *)
  0x48; 0x0f; 0xba; 0xf0; 0x3f;
                           (* BTR (% rax) (Imm8 (word 63)) *)
  0x48; 0x89; 0x44; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rax) *)
  0x48; 0x8b; 0x16;        (* MOV (% rdx) (Memop Quadword (%% (rsi,0))) *)
  0x48; 0x8b; 0x4e; 0x08;  (* MOV (% rcx) (Memop Quadword (%% (rsi,8))) *)
  0x4c; 0x8b; 0x46; 0x10;  (* MOV (% r8) (Memop Quadword (%% (rsi,16))) *)
  0x4c; 0x8b; 0x4e; 0x18;  (* MOV (% r9) (Memop Quadword (%% (rsi,24))) *)
  0xb8; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 1)) *)
  0x45; 0x31; 0xd2;        (* XOR (% r10d) (% r10d) *)
  0x49; 0x0f; 0xba; 0xe9; 0x3f;
                           (* BTS (% r9) (Imm8 (word 63)) *)
  0x4c; 0x11; 0xd0;        (* ADC (% rax) (% r10) *)
  0x48; 0x6b; 0xc0; 0x13;  (* IMUL3 (% rax) (% rax,Imm8 (word 19)) *)
  0x48; 0x01; 0xc2;        (* ADD (% rdx) (% rax) *)
  0x4c; 0x11; 0xd1;        (* ADC (% rcx) (% r10) *)
  0x4d; 0x11; 0xd0;        (* ADC (% r8) (% r10) *)
  0x4d; 0x11; 0xd1;        (* ADC (% r9) (% r10) *)
  0xb8; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 19)) *)
  0x49; 0x0f; 0x42; 0xc2;  (* CMOVB (% rax) (% r10) *)
  0x48; 0x29; 0xc2;        (* SUB (% rdx) (% rax) *)
  0x4c; 0x19; 0xd1;        (* SBB (% rcx) (% r10) *)
  0x4d; 0x19; 0xd0;        (* SBB (% r8) (% r10) *)
  0x4d; 0x19; 0xd1;        (* SBB (% r9) (% r10) *)
  0x49; 0x0f; 0xba; 0xf1; 0x3f;
                           (* BTR (% r9) (Imm8 (word 63)) *)
  0x48; 0x89; 0x54; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rdx) *)
  0x48; 0x89; 0x4c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rcx) *)
  0x4c; 0x89; 0x44; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% r8) *)
  0x4c; 0x89; 0x4c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% r9) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x48; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rax) *)
  0x48; 0x89; 0x44; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rax) *)
  0x48; 0xb8; 0x99; 0x20; 0x02; 0x75; 0x23; 0x9e; 0xf9; 0xa0;
                           (* MOV (% rax) (Imm64 (word 11599476190393540761)) *)
  0x48; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rax) *)
  0x48; 0xb8; 0x95; 0x25; 0x13; 0x1d; 0x3f; 0x8f; 0xc6; 0xa8;
                           (* MOV (% rax) (Imm64 (word 12161565344994108821)) *)
  0x48; 0x89; 0x44; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rax) *)
  0x48; 0xb8; 0x42; 0x52; 0xac; 0x05; 0x38; 0x89; 0x6c; 0x6c;
                           (* MOV (% rax) (Imm64 (word 7812770327287321154)) *)
  0x48; 0x89; 0x44; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rax) *)
  0x48; 0xb8; 0x15; 0x06; 0x77; 0x41; 0xb2; 0x08; 0x65; 0x27;
                           (* MOV (% rax) (Imm64 (word 2838684701822486037)) *)
  0x48; 0x89; 0x44; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rax) *)
  0x48; 0xc7; 0x84; 0x24; 0x90; 0x00; 0x00; 0x00; 0x0a; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,144))) (Imm32 (word 10)) *)
  0x48; 0xc7; 0x84; 0x24; 0x98; 0x00; 0x00; 0x00; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (Imm32 (word 1)) *)
  0xe9; 0x07; 0x04; 0x00; 0x00;
                           (* JMP (Imm32 (word 1031)) *)
  0x4d; 0x89; 0xc1;        (* MOV (% r9) (% r8) *)
  0x49; 0xc1; 0xf9; 0x3f;  (* SAR (% r9) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xc8;        (* XOR (% r8) (% r9) *)
  0x4d; 0x29; 0xc8;        (* SUB (% r8) (% r9) *)
  0x4d; 0x89; 0xd3;        (* MOV (% r11) (% r10) *)
  0x49; 0xc1; 0xfb; 0x3f;  (* SAR (% r11) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xda;        (* XOR (% r10) (% r11) *)
  0x4d; 0x29; 0xda;        (* SUB (% r10) (% r11) *)
  0x4d; 0x89; 0xe5;        (* MOV (% r13) (% r12) *)
  0x49; 0xc1; 0xfd; 0x3f;  (* SAR (% r13) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4d; 0x29; 0xec;        (* SUB (% r12) (% r13) *)
  0x4d; 0x89; 0xf7;        (* MOV (% r15) (% r14) *)
  0x49; 0xc1; 0xff; 0x3f;  (* SAR (% r15) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xfe;        (* XOR (% r14) (% r15) *)
  0x4d; 0x29; 0xfe;        (* SUB (% r14) (% r15) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x4c; 0x21; 0xc8;        (* AND (% rax) (% r9) *)
  0x4c; 0x89; 0xd7;        (* MOV (% rdi) (% r10) *)
  0x4c; 0x21; 0xdf;        (* AND (% rdi) (% r11) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x89; 0xbc; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,128))) (% rdi) *)
  0x4c; 0x89; 0xe0;        (* MOV (% rax) (% r12) *)
  0x4c; 0x21; 0xe8;        (* AND (% rax) (% r13) *)
  0x4c; 0x89; 0xf6;        (* MOV (% rsi) (% r14) *)
  0x4c; 0x21; 0xfe;        (* AND (% rsi) (% r15) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x89; 0xb4; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,136))) (% rsi) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x20;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,32))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x0f; 0xac; 0xdf; 0x3b;
                           (* SHRD (% rdi) (% rbx) (Imm8 (word 59)) *)
  0x48; 0x89; 0x3c; 0x24;  (* MOV (Memop Quadword (%% (rsp,0))) (% rdi) *)
  0x31; 0xff;              (* XOR (% edi) (% edi) *)
  0x48; 0x8b; 0x44; 0x24; 0x08;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,8))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd7;        (* ADC (% rdi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x28;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,40))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd7;        (* ADC (% rdi) (% rdx) *)
  0x48; 0x0f; 0xac; 0xee; 0x3b;
                           (* SHRD (% rsi) (% rbp) (Imm8 (word 59)) *)
  0x48; 0x89; 0x74; 0x24; 0x20;
                           (* MOV (Memop Quadword (%% (rsp,32))) (% rsi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x0f; 0xac; 0xcb; 0x3b;
                           (* SHRD (% rbx) (% rcx) (Imm8 (word 59)) *)
  0x48; 0x89; 0x5c; 0x24; 0x08;
                           (* MOV (Memop Quadword (%% (rsp,8))) (% rbx) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x44; 0x24; 0x10;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,16))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x30;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,48))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc7;        (* ADD (% rdi) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x0f; 0xac; 0xfd; 0x3b;
                           (* SHRD (% rbp) (% rdi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x6c; 0x24; 0x28;
                           (* MOV (Memop Quadword (%% (rsp,40))) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x48; 0x89; 0xc5;        (* MOV (% rbp) (% rax) *)
  0x48; 0xc1; 0xfd; 0x3f;  (* SAR (% rbp) (Imm8 (word 63)) *)
  0x4c; 0x21; 0xc5;        (* AND (% rbp) (% r8) *)
  0x48; 0xf7; 0xdd;        (* NEG (% rbp) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0xc1; 0xfa; 0x3f;  (* SAR (% rdx) (Imm8 (word 63)) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x48; 0x29; 0xd5;        (* SUB (% rbp) (% rdx) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x0f; 0xac; 0xf1; 0x3b;
                           (* SHRD (% rcx) (% rsi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x4c; 0x24; 0x10;
                           (* MOV (Memop Quadword (%% (rsp,16))) (% rcx) *)
  0x48; 0x0f; 0xac; 0xee; 0x3b;
                           (* SHRD (% rsi) (% rbp) (Imm8 (word 59)) *)
  0x48; 0x8b; 0x44; 0x24; 0x18;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,24))) *)
  0x48; 0x89; 0x74; 0x24; 0x18;
                           (* MOV (Memop Quadword (%% (rsp,24))) (% rsi) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x48; 0x89; 0xc6;        (* MOV (% rsi) (% rax) *)
  0x48; 0xc1; 0xfe; 0x3f;  (* SAR (% rsi) (Imm8 (word 63)) *)
  0x4c; 0x21; 0xe6;        (* AND (% rsi) (% r12) *)
  0x48; 0xf7; 0xde;        (* NEG (% rsi) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x38;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,56))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x48; 0x89; 0xc2;        (* MOV (% rdx) (% rax) *)
  0x48; 0xc1; 0xfa; 0x3f;  (* SAR (% rdx) (Imm8 (word 63)) *)
  0x4c; 0x21; 0xf2;        (* AND (% rdx) (% r14) *)
  0x48; 0x29; 0xd6;        (* SUB (% rsi) (% rdx) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x0f; 0xac; 0xdf; 0x3b;
                           (* SHRD (% rdi) (% rbx) (Imm8 (word 59)) *)
  0x48; 0x89; 0x7c; 0x24; 0x30;
                           (* MOV (Memop Quadword (%% (rsp,48))) (% rdi) *)
  0x48; 0x0f; 0xac; 0xf3; 0x3b;
                           (* SHRD (% rbx) (% rsi) (Imm8 (word 59)) *)
  0x48; 0x89; 0x5c; 0x24; 0x38;
                           (* MOV (Memop Quadword (%% (rsp,56))) (% rbx) *)
  0x48; 0x8b; 0x9c; 0x24; 0x80; 0x00; 0x00; 0x00;
                           (* MOV (% rbx) (Memop Quadword (%% (rsp,128))) *)
  0x48; 0x8b; 0xac; 0x24; 0x88; 0x00; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,136))) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x5c; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% rbx) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x89; 0x6c; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% rbp) *)
  0x31; 0xdb;              (* XOR (% ebx) (% ebx) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x4c; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% rcx) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd5;        (* ADC (% rbp) (% rdx) *)
  0x48; 0x89; 0x74; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% rsi) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc3;        (* ADD (% rbx) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x89; 0x5c; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% rbx) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc5;        (* ADD (% rbp) (% rax) *)
  0x48; 0x11; 0xd6;        (* ADC (% rsi) (% rdx) *)
  0x48; 0x89; 0x6c; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% rbp) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x4c; 0x89; 0xcb;        (* MOV (% rbx) (% r9) *)
  0x4c; 0x21; 0xc3;        (* AND (% rbx) (% r8) *)
  0x48; 0xf7; 0xdb;        (* NEG (% rbx) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xd3;        (* ADC (% rbx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x48; 0x29; 0xd3;        (* SUB (% rbx) (% rdx) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x11; 0xda;        (* ADC (% rdx) (% rbx) *)
  0x48; 0x89; 0xd3;        (* MOV (% rbx) (% rdx) *)
  0x48; 0x0f; 0xa4; 0xca; 0x01;
                           (* SHLD (% rdx) (% rcx) (Imm8 (word 1)) *)
  0x48; 0xc1; 0xfb; 0x3f;  (* SAR (% rbx) (Imm8 (word 63)) *)
  0x48; 0x01; 0xda;        (* ADD (% rdx) (% rbx) *)
  0xb8; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 19)) *)
  0x48; 0xf7; 0xea;        (* IMUL2 (% rdx,% rax) (% rdx) *)
  0x4c; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,64))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x4c; 0x89; 0x44; 0x24; 0x40;
                           (* MOV (Memop Quadword (%% (rsp,64))) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,72))) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4c; 0x89; 0x44; 0x24; 0x48;
                           (* MOV (Memop Quadword (%% (rsp,72))) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,80))) *)
  0x49; 0x11; 0xd8;        (* ADC (% r8) (% rbx) *)
  0x4c; 0x89; 0x44; 0x24; 0x50;
                           (* MOV (Memop Quadword (%% (rsp,80))) (% r8) *)
  0x48; 0x11; 0xd9;        (* ADC (% rcx) (% rbx) *)
  0x48; 0xc1; 0xe0; 0x3f;  (* SHL (% rax) (Imm8 (word 63)) *)
  0x48; 0x01; 0xc1;        (* ADD (% rcx) (% rax) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x48; 0x89; 0x4c; 0x24; 0x58;
                           (* MOV (Memop Quadword (%% (rsp,88))) (% rcx) *)
  0x4c; 0x31; 0xe8;        (* XOR (% rax) (% r13) *)
  0x4c; 0x89; 0xe9;        (* MOV (% rcx) (% r13) *)
  0x4c; 0x21; 0xe1;        (* AND (% rcx) (% r12) *)
  0x48; 0xf7; 0xd9;        (* NEG (% rcx) *)
  0x49; 0xf7; 0xe4;        (* MUL2 (% rdx,% rax) (% r12) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xd1;        (* ADC (% rcx) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x4c; 0x31; 0xf8;        (* XOR (% rax) (% r15) *)
  0x4c; 0x89; 0xfa;        (* MOV (% rdx) (% r15) *)
  0x4c; 0x21; 0xf2;        (* AND (% rdx) (% r14) *)
  0x48; 0x29; 0xd1;        (* SUB (% rcx) (% rdx) *)
  0x49; 0xf7; 0xe6;        (* MUL2 (% rdx,% rax) (% r14) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x11; 0xca;        (* ADC (% rdx) (% rcx) *)
  0x48; 0x89; 0xd1;        (* MOV (% rcx) (% rdx) *)
  0x48; 0x0f; 0xa4; 0xf2; 0x01;
                           (* SHLD (% rdx) (% rsi) (Imm8 (word 1)) *)
  0x48; 0xc1; 0xf9; 0x3f;  (* SAR (% rcx) (Imm8 (word 63)) *)
  0xb8; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% eax) (Imm32 (word 19)) *)
  0x48; 0x01; 0xca;        (* ADD (% rdx) (% rcx) *)
  0x48; 0xf7; 0xea;        (* IMUL2 (% rdx,% rax) (% rdx) *)
  0x4c; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,96))) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x4c; 0x89; 0x44; 0x24; 0x60;
                           (* MOV (Memop Quadword (%% (rsp,96))) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,104))) *)
  0x49; 0x11; 0xd0;        (* ADC (% r8) (% rdx) *)
  0x4c; 0x89; 0x44; 0x24; 0x68;
                           (* MOV (Memop Quadword (%% (rsp,104))) (% r8) *)
  0x4c; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% r8) (Memop Quadword (%% (rsp,112))) *)
  0x49; 0x11; 0xc8;        (* ADC (% r8) (% rcx) *)
  0x4c; 0x89; 0x44; 0x24; 0x70;
                           (* MOV (Memop Quadword (%% (rsp,112))) (% r8) *)
  0x48; 0x11; 0xce;        (* ADC (% rsi) (% rcx) *)
  0x48; 0xc1; 0xe0; 0x3f;  (* SHL (% rax) (Imm8 (word 63)) *)
  0x48; 0x01; 0xc6;        (* ADD (% rsi) (% rax) *)
  0x48; 0x89; 0x74; 0x24; 0x78;
                           (* MOV (Memop Quadword (%% (rsp,120))) (% rsi) *)
  0x48; 0x8b; 0xb4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (% rsi) (Memop Quadword (%% (rsp,152))) *)
  0x48; 0x8b; 0x14; 0x24;  (* MOV (% rdx) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x20;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,32))) *)
  0x48; 0x89; 0xd3;        (* MOV (% rbx) (% rdx) *)
  0x48; 0x81; 0xe3; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rbx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0xfe; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446741874686296064)) *)
  0x48; 0x09; 0xc3;        (* OR (% rbx) (% rax) *)
  0x48; 0x81; 0xe1; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rcx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0xc0;
                           (* MOV (% rax) (Imm64 (word 13835058055282163712)) *)
  0x48; 0x09; 0xc1;        (* OR (% rcx) (% rax) *)
  0x48; 0xc7; 0xc0; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm32 (word 4294967294)) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0xba; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 2)) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0xf7; 0xc1; 0x01; 0x00; 0x00; 0x00;
                           (* TEST (% rcx) (Imm32 (word 1)) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0xb8; 0x00; 0x00; 0x10; 0x00;
                           (* MOV (% eax) (Imm32 (word 1048576)) *)
  0x48; 0x8d; 0x14; 0x03;  (* LEA (% rdx) (%%% (rbx,0,rax)) *)
  0x48; 0x8d; 0x3c; 0x01;  (* LEA (% rdi) (%%% (rcx,0,rax)) *)
  0x48; 0xc1; 0xe2; 0x16;  (* SHL (% rdx) (Imm8 (word 22)) *)
  0x48; 0xc1; 0xe7; 0x16;  (* SHL (% rdi) (Imm8 (word 22)) *)
  0x48; 0xc1; 0xfa; 0x2b;  (* SAR (% rdx) (Imm8 (word 43)) *)
  0x48; 0xc1; 0xff; 0x2b;  (* SAR (% rdi) (Imm8 (word 43)) *)
  0x48; 0xb8; 0x00; 0x00; 0x10; 0x00; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 2199024304128)) *)
  0x48; 0x8d; 0x1c; 0x03;  (* LEA (% rbx) (%%% (rbx,0,rax)) *)
  0x48; 0x8d; 0x0c; 0x01;  (* LEA (% rcx) (%%% (rcx,0,rax)) *)
  0x48; 0xc1; 0xfb; 0x2a;  (* SAR (% rbx) (Imm8 (word 42)) *)
  0x48; 0xc1; 0xf9; 0x2a;  (* SAR (% rcx) (Imm8 (word 42)) *)
  0x48; 0x89; 0x94; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,160))) (% rdx) *)
  0x48; 0x89; 0x9c; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,168))) (% rbx) *)
  0x48; 0x89; 0xbc; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,176))) (% rdi) *)
  0x48; 0x89; 0x8c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,184))) (% rcx) *)
  0x4c; 0x8b; 0x24; 0x24;  (* MOV (% r12) (Memop Quadword (%% (rsp,0))) *)
  0x49; 0x0f; 0xaf; 0xfc;  (* IMUL (% rdi) (% r12) *)
  0x4c; 0x0f; 0xaf; 0xe2;  (* IMUL (% r12) (% rdx) *)
  0x4c; 0x8b; 0x6c; 0x24; 0x20;
                           (* MOV (% r13) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x0f; 0xaf; 0xdd;  (* IMUL (% rbx) (% r13) *)
  0x4c; 0x0f; 0xaf; 0xe9;  (* IMUL (% r13) (% rcx) *)
  0x49; 0x01; 0xdc;        (* ADD (% r12) (% rbx) *)
  0x49; 0x01; 0xfd;        (* ADD (% r13) (% rdi) *)
  0x49; 0xc1; 0xfc; 0x14;  (* SAR (% r12) (Imm8 (word 20)) *)
  0x49; 0xc1; 0xfd; 0x14;  (* SAR (% r13) (Imm8 (word 20)) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0x81; 0xe3; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rbx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0xfe; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446741874686296064)) *)
  0x48; 0x09; 0xc3;        (* OR (% rbx) (% rax) *)
  0x4c; 0x89; 0xe9;        (* MOV (% rcx) (% r13) *)
  0x48; 0x81; 0xe1; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rcx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0xc0;
                           (* MOV (% rax) (Imm64 (word 13835058055282163712)) *)
  0x48; 0x09; 0xc1;        (* OR (% rcx) (% rax) *)
  0x48; 0xc7; 0xc0; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm32 (word 4294967294)) *)
  0xba; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 2)) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0xf7; 0xc1; 0x01; 0x00; 0x00; 0x00;
                           (* TEST (% rcx) (Imm32 (word 1)) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0xb8; 0x00; 0x00; 0x10; 0x00;
                           (* MOV (% eax) (Imm32 (word 1048576)) *)
  0x4c; 0x8d; 0x04; 0x03;  (* LEA (% r8) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x14; 0x01;  (* LEA (% r10) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xe0; 0x16;  (* SHL (% r8) (Imm8 (word 22)) *)
  0x49; 0xc1; 0xe2; 0x16;  (* SHL (% r10) (Imm8 (word 22)) *)
  0x49; 0xc1; 0xf8; 0x2b;  (* SAR (% r8) (Imm8 (word 43)) *)
  0x49; 0xc1; 0xfa; 0x2b;  (* SAR (% r10) (Imm8 (word 43)) *)
  0x48; 0xb8; 0x00; 0x00; 0x10; 0x00; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 2199024304128)) *)
  0x4c; 0x8d; 0x3c; 0x03;  (* LEA (% r15) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x1c; 0x01;  (* LEA (% r11) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xff; 0x2a;  (* SAR (% r15) (Imm8 (word 42)) *)
  0x49; 0xc1; 0xfb; 0x2a;  (* SAR (% r11) (Imm8 (word 42)) *)
  0x4c; 0x89; 0xeb;        (* MOV (% rbx) (% r13) *)
  0x4c; 0x89; 0xe1;        (* MOV (% rcx) (% r12) *)
  0x4d; 0x0f; 0xaf; 0xe0;  (* IMUL (% r12) (% r8) *)
  0x49; 0x0f; 0xaf; 0xdf;  (* IMUL (% rbx) (% r15) *)
  0x49; 0x01; 0xdc;        (* ADD (% r12) (% rbx) *)
  0x4d; 0x0f; 0xaf; 0xeb;  (* IMUL (% r13) (% r11) *)
  0x49; 0x0f; 0xaf; 0xca;  (* IMUL (% rcx) (% r10) *)
  0x49; 0x01; 0xcd;        (* ADD (% r13) (% rcx) *)
  0x49; 0xc1; 0xfc; 0x14;  (* SAR (% r12) (Imm8 (word 20)) *)
  0x49; 0xc1; 0xfd; 0x14;  (* SAR (% r13) (Imm8 (word 20)) *)
  0x4c; 0x89; 0xe3;        (* MOV (% rbx) (% r12) *)
  0x48; 0x81; 0xe3; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rbx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0xfe; 0xff; 0xff;
                           (* MOV (% rax) (Imm64 (word 18446741874686296064)) *)
  0x48; 0x09; 0xc3;        (* OR (% rbx) (% rax) *)
  0x4c; 0x89; 0xe9;        (* MOV (% rcx) (% r13) *)
  0x48; 0x81; 0xe1; 0xff; 0xff; 0x0f; 0x00;
                           (* AND (% rcx) (Imm32 (word 1048575)) *)
  0x48; 0xb8; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0x00; 0xc0;
                           (* MOV (% rax) (Imm64 (word 13835058055282163712)) *)
  0x48; 0x09; 0xc1;        (* OR (% rcx) (% rax) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% r8) *)
  0x48; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x0f; 0xaf; 0xd7;  (* IMUL (% rdx) (% r15) *)
  0x4c; 0x0f; 0xaf; 0x84; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* IMUL (% r8) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x0f; 0xaf; 0xbc; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* IMUL (% r15) (Memop Quadword (%% (rsp,184))) *)
  0x4d; 0x01; 0xc7;        (* ADD (% r15) (% r8) *)
  0x4c; 0x8d; 0x0c; 0x10;  (* LEA (% r9) (%%% (rax,0,rdx)) *)
  0x48; 0x8b; 0x84; 0x24; 0xa0; 0x00; 0x00; 0x00;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,160))) *)
  0x49; 0x0f; 0xaf; 0xc2;  (* IMUL (% rax) (% r10) *)
  0x48; 0x8b; 0x94; 0x24; 0xb0; 0x00; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,176))) *)
  0x49; 0x0f; 0xaf; 0xd3;  (* IMUL (% rdx) (% r11) *)
  0x4c; 0x0f; 0xaf; 0x94; 0x24; 0xa8; 0x00; 0x00; 0x00;
                           (* IMUL (% r10) (Memop Quadword (%% (rsp,168))) *)
  0x4c; 0x0f; 0xaf; 0x9c; 0x24; 0xb8; 0x00; 0x00; 0x00;
                           (* IMUL (% r11) (Memop Quadword (%% (rsp,184))) *)
  0x4d; 0x01; 0xd3;        (* ADD (% r11) (% r10) *)
  0x4c; 0x8d; 0x2c; 0x10;  (* LEA (% r13) (%%% (rax,0,rdx)) *)
  0x48; 0xc7; 0xc0; 0xfe; 0xff; 0xff; 0xff;
                           (* MOV (% rax) (Imm32 (word 4294967294)) *)
  0xba; 0x02; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 2)) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x85; 0xf6;        (* TEST (% rsi) (% rsi) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0xf7; 0xc1; 0x01; 0x00; 0x00; 0x00;
                           (* TEST (% rcx) (Imm32 (word 1)) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x4c; 0x0f; 0x48; 0xc5;  (* CMOVS (% r8) (% rbp) *)
  0x48; 0x89; 0xdf;        (* MOV (% rdi) (% rbx) *)
  0x48; 0x85; 0xd1;        (* TEST (% rcx) (% rdx) *)
  0x4c; 0x0f; 0x44; 0xc5;  (* CMOVE (% r8) (% rbp) *)
  0x48; 0x0f; 0x44; 0xfd;  (* CMOVE (% rdi) (% rbp) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0x4c; 0x31; 0xc7;        (* XOR (% rdi) (% r8) *)
  0x4c; 0x31; 0xc6;        (* XOR (% rsi) (% r8) *)
  0x49; 0x0f; 0xba; 0xe0; 0x3f;
                           (* BT (% r8) (Imm8 (word 63)) *)
  0x48; 0x0f; 0x42; 0xd9;  (* CMOVB (% rbx) (% rcx) *)
  0x49; 0x89; 0xc0;        (* MOV (% r8) (% rax) *)
  0x48; 0x29; 0xc6;        (* SUB (% rsi) (% rax) *)
  0x48; 0x8d; 0x0c; 0x39;  (* LEA (% rcx) (%%% (rcx,0,rdi)) *)
  0x48; 0xd1; 0xf9;        (* SAR (% rcx) (Imm8 (word 1)) *)
  0xb8; 0x00; 0x00; 0x10; 0x00;
                           (* MOV (% eax) (Imm32 (word 1048576)) *)
  0x4c; 0x8d; 0x04; 0x03;  (* LEA (% r8) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x24; 0x01;  (* LEA (% r12) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xe0; 0x15;  (* SHL (% r8) (Imm8 (word 21)) *)
  0x49; 0xc1; 0xe4; 0x15;  (* SHL (% r12) (Imm8 (word 21)) *)
  0x49; 0xc1; 0xf8; 0x2b;  (* SAR (% r8) (Imm8 (word 43)) *)
  0x49; 0xc1; 0xfc; 0x2b;  (* SAR (% r12) (Imm8 (word 43)) *)
  0x48; 0xb8; 0x00; 0x00; 0x10; 0x00; 0x00; 0x02; 0x00; 0x00;
                           (* MOV (% rax) (Imm64 (word 2199024304128)) *)
  0x4c; 0x8d; 0x14; 0x03;  (* LEA (% r10) (%%% (rbx,0,rax)) *)
  0x4c; 0x8d; 0x34; 0x01;  (* LEA (% r14) (%%% (rcx,0,rax)) *)
  0x49; 0xc1; 0xfa; 0x2b;  (* SAR (% r10) (Imm8 (word 43)) *)
  0x49; 0xc1; 0xfe; 0x2b;  (* SAR (% r14) (Imm8 (word 43)) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x49; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% r8) *)
  0x4c; 0x89; 0xea;        (* MOV (% rdx) (% r13) *)
  0x49; 0x0f; 0xaf; 0xd2;  (* IMUL (% rdx) (% r10) *)
  0x4d; 0x0f; 0xaf; 0xc7;  (* IMUL (% r8) (% r15) *)
  0x4d; 0x0f; 0xaf; 0xd3;  (* IMUL (% r10) (% r11) *)
  0x4d; 0x01; 0xc2;        (* ADD (% r10) (% r8) *)
  0x4c; 0x8d; 0x04; 0x10;  (* LEA (% r8) (%%% (rax,0,rdx)) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x49; 0x0f; 0xaf; 0xc4;  (* IMUL (% rax) (% r12) *)
  0x4c; 0x89; 0xea;        (* MOV (% rdx) (% r13) *)
  0x49; 0x0f; 0xaf; 0xd6;  (* IMUL (% rdx) (% r14) *)
  0x4d; 0x0f; 0xaf; 0xe7;  (* IMUL (% r12) (% r15) *)
  0x4d; 0x0f; 0xaf; 0xf3;  (* IMUL (% r14) (% r11) *)
  0x4d; 0x01; 0xe6;        (* ADD (% r14) (% r12) *)
  0x4c; 0x8d; 0x24; 0x10;  (* LEA (% r12) (%%% (rax,0,rdx)) *)
  0x48; 0x89; 0xb4; 0x24; 0x98; 0x00; 0x00; 0x00;
                           (* MOV (Memop Quadword (%% (rsp,152))) (% rsi) *)
  0x48; 0xff; 0x8c; 0x24; 0x90; 0x00; 0x00; 0x00;
                           (* DEC (Memop Quadword (%% (rsp,144))) *)
  0x0f; 0x85; 0xc1; 0xee; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294962881)) *)
  0x48; 0x8b; 0x04; 0x24;  (* MOV (% rax) (Memop Quadword (%% (rsp,0))) *)
  0x48; 0x8b; 0x4c; 0x24; 0x20;
                           (* MOV (% rcx) (Memop Quadword (%% (rsp,32))) *)
  0x49; 0x0f; 0xaf; 0xc0;  (* IMUL (% rax) (% r8) *)
  0x49; 0x0f; 0xaf; 0xca;  (* IMUL (% rcx) (% r10) *)
  0x48; 0x01; 0xc8;        (* ADD (% rax) (% rcx) *)
  0x48; 0xc1; 0xf8; 0x3f;  (* SAR (% rax) (Imm8 (word 63)) *)
  0x4d; 0x89; 0xc1;        (* MOV (% r9) (% r8) *)
  0x49; 0xc1; 0xf9; 0x3f;  (* SAR (% r9) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xc8;        (* XOR (% r8) (% r9) *)
  0x4d; 0x29; 0xc8;        (* SUB (% r8) (% r9) *)
  0x49; 0x31; 0xc1;        (* XOR (% r9) (% rax) *)
  0x4d; 0x89; 0xd3;        (* MOV (% r11) (% r10) *)
  0x49; 0xc1; 0xfb; 0x3f;  (* SAR (% r11) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xda;        (* XOR (% r10) (% r11) *)
  0x4d; 0x29; 0xda;        (* SUB (% r10) (% r11) *)
  0x49; 0x31; 0xc3;        (* XOR (% r11) (% rax) *)
  0x4d; 0x89; 0xe5;        (* MOV (% r13) (% r12) *)
  0x49; 0xc1; 0xfd; 0x3f;  (* SAR (% r13) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xec;        (* XOR (% r12) (% r13) *)
  0x4d; 0x29; 0xec;        (* SUB (% r12) (% r13) *)
  0x49; 0x31; 0xc5;        (* XOR (% r13) (% rax) *)
  0x4d; 0x89; 0xf7;        (* MOV (% r15) (% r14) *)
  0x49; 0xc1; 0xff; 0x3f;  (* SAR (% r15) (Imm8 (word 63)) *)
  0x4d; 0x31; 0xfe;        (* XOR (% r14) (% r15) *)
  0x4d; 0x29; 0xfe;        (* SUB (% r14) (% r15) *)
  0x49; 0x31; 0xc7;        (* XOR (% r15) (% rax) *)
  0x4c; 0x89; 0xc0;        (* MOV (% rax) (% r8) *)
  0x4c; 0x21; 0xc8;        (* AND (% rax) (% r9) *)
  0x4d; 0x89; 0xd4;        (* MOV (% r12) (% r10) *)
  0x4d; 0x21; 0xdc;        (* AND (% r12) (% r11) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x45; 0x31; 0xed;        (* XOR (% r13d) (% r13d) *)
  0x48; 0x8b; 0x44; 0x24; 0x40;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,64))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x60;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,96))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x45; 0x31; 0xf6;        (* XOR (% r14d) (% r14d) *)
  0x48; 0x8b; 0x44; 0x24; 0x48;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,72))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x68;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,104))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc5;        (* ADD (% r13) (% rax) *)
  0x49; 0x11; 0xd6;        (* ADC (% r14) (% rdx) *)
  0x45; 0x31; 0xff;        (* XOR (% r15d) (% r15d) *)
  0x48; 0x8b; 0x44; 0x24; 0x50;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,80))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x70;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,112))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc6;        (* ADD (% r14) (% rax) *)
  0x49; 0x11; 0xd7;        (* ADC (% r15) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x58;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,88))) *)
  0x4c; 0x31; 0xc8;        (* XOR (% rax) (% r9) *)
  0x4d; 0x21; 0xc1;        (* AND (% r9) (% r8) *)
  0x49; 0xf7; 0xd9;        (* NEG (% r9) *)
  0x49; 0xf7; 0xe0;        (* MUL2 (% rdx,% rax) (% r8) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x48; 0x8b; 0x44; 0x24; 0x78;
                           (* MOV (% rax) (Memop Quadword (%% (rsp,120))) *)
  0x4c; 0x31; 0xd8;        (* XOR (% rax) (% r11) *)
  0x4c; 0x89; 0xda;        (* MOV (% rdx) (% r11) *)
  0x4c; 0x21; 0xd2;        (* AND (% rdx) (% r10) *)
  0x49; 0x29; 0xd1;        (* SUB (% r9) (% rdx) *)
  0x49; 0xf7; 0xe2;        (* MUL2 (% rdx,% rax) (% r10) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x49; 0x11; 0xd1;        (* ADC (% r9) (% rdx) *)
  0x4c; 0x89; 0xc8;        (* MOV (% rax) (% r9) *)
  0x4c; 0x0f; 0xa4; 0xf8; 0x01;
                           (* SHLD (% rax) (% r15) (Imm8 (word 1)) *)
  0x49; 0xc1; 0xf9; 0x3f;  (* SAR (% r9) (Imm8 (word 63)) *)
  0xbb; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% ebx) (Imm32 (word 19)) *)
  0x4a; 0x8d; 0x44; 0x08; 0x01;
                           (* LEA (% rax) (%%%% (rax,0,r9,&1)) *)
  0x48; 0xf7; 0xeb;        (* IMUL2 (% rdx,% rax) (% rbx) *)
  0x31; 0xed;              (* XOR (% ebp) (% ebp) *)
  0x49; 0x01; 0xc4;        (* ADD (% r12) (% rax) *)
  0x49; 0x11; 0xd5;        (* ADC (% r13) (% rdx) *)
  0x4d; 0x11; 0xce;        (* ADC (% r14) (% r9) *)
  0x4d; 0x11; 0xcf;        (* ADC (% r15) (% r9) *)
  0x48; 0xc1; 0xe0; 0x3f;  (* SHL (% rax) (Imm8 (word 63)) *)
  0x49; 0x01; 0xc7;        (* ADD (% r15) (% rax) *)
  0x48; 0x0f; 0x49; 0xdd;  (* CMOVNS (% rbx) (% rbp) *)
  0x49; 0x29; 0xdc;        (* SUB (% r12) (% rbx) *)
  0x49; 0x19; 0xed;        (* SBB (% r13) (% rbp) *)
  0x49; 0x19; 0xee;        (* SBB (% r14) (% rbp) *)
  0x49; 0x19; 0xef;        (* SBB (% r15) (% rbp) *)
  0x49; 0x0f; 0xba; 0xf7; 0x3f;
                           (* BTR (% r15) (Imm8 (word 63)) *)
  0x48; 0x8b; 0xbc; 0x24; 0xc0; 0x00; 0x00; 0x00;
                           (* MOV (% rdi) (Memop Quadword (%% (rsp,192))) *)
  0x4c; 0x89; 0x27;        (* MOV (Memop Quadword (%% (rdi,0))) (% r12) *)
  0x4c; 0x89; 0x6f; 0x08;  (* MOV (Memop Quadword (%% (rdi,8))) (% r13) *)
  0x4c; 0x89; 0x77; 0x10;  (* MOV (Memop Quadword (%% (rdi,16))) (% r14) *)
  0x4c; 0x89; 0x7f; 0x18;  (* MOV (Memop Quadword (%% (rdi,24))) (% r15) *)
  0x48; 0x8b; 0xac; 0x24; 0xc0; 0x01; 0x00; 0x00;
                           (* MOV (% rbp) (Memop Quadword (%% (rsp,448))) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x94; 0x24; 0x00; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,256))) *)
  0xc4; 0x62; 0xbb; 0xf6; 0x8c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MULX4 (% r9,% r8) (% rdx,Memop Quadword (%% (rsp,288))) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x94; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MULX4 (% r10,% rax) (% rdx,Memop Quadword (%% (rsp,296))) *)
  0x49; 0x01; 0xc1;        (* ADD (% r9) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0x9c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MULX4 (% r11,% rax) (% rdx,Memop Quadword (%% (rsp,304))) *)
  0x49; 0x11; 0xc2;        (* ADC (% r10) (% rax) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xa4; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MULX4 (% r12,% rax) (% rdx,Memop Quadword (%% (rsp,312))) *)
  0x49; 0x11; 0xc3;        (* ADC (% r11) (% rax) *)
  0x49; 0x11; 0xf4;        (* ADC (% r12) (% rsi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x94; 0x24; 0x08; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,264))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,288))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,296))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,304))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xac; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MULX4 (% r13,% rax) (% rdx,Memop Quadword (%% (rsp,312))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xee;
                           (* ADOX (% r13) (% rsi) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xee;
                           (* ADCX (% r13) (% rsi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x94; 0x24; 0x10; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,272))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,288))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,296))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,304))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xb4; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MULX4 (% r14,% rax) (% rdx,Memop Quadword (%% (rsp,312))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADOX (% r14) (% rsi) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf6;
                           (* ADCX (% r14) (% rsi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x48; 0x8b; 0x94; 0x24; 0x18; 0x01; 0x00; 0x00;
                           (* MOV (% rdx) (Memop Quadword (%% (rsp,280))) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x20; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,288))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe3;
                           (* ADOX (% r12) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x28; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,296))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe0;
                           (* ADCX (% r12) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xeb;
                           (* ADOX (% r13) (% rbx) *)
  0xc4; 0xe2; 0xfb; 0xf6; 0x9c; 0x24; 0x30; 0x01; 0x00; 0x00;
                           (* MULX4 (% rbx,% rax) (% rdx,Memop Quadword (%% (rsp,304))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe8;
                           (* ADCX (% r13) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xf3;
                           (* ADOX (% r14) (% rbx) *)
  0xc4; 0x62; 0xfb; 0xf6; 0xbc; 0x24; 0x38; 0x01; 0x00; 0x00;
                           (* MULX4 (% r15,% rax) (% rdx,Memop Quadword (%% (rsp,312))) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xf0;
                           (* ADCX (% r14) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xfe;
                           (* ADOX (% r15) (% rsi) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xfe;
                           (* ADCX (% r15) (% rsi) *)
  0xba; 0x26; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 38)) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdc;
                           (* MULX4 (% rbx,% rax) (% rdx,% r12) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc0;
                           (* ADCX (% r8) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xcb;
                           (* ADOX (% r9) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdd;
                           (* MULX4 (% rbx,% rax) (% rdx,% r13) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xc8;
                           (* ADCX (% r9) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xd3;
                           (* ADOX (% r10) (% rbx) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xde;
                           (* MULX4 (% rbx,% rax) (% rdx,% r14) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd0;
                           (* ADCX (% r10) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xdb;
                           (* ADOX (% r11) (% rbx) *)
  0xc4; 0x42; 0xfb; 0xf6; 0xe7;
                           (* MULX4 (% r12,% rax) (% rdx,% r15) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xd8;
                           (* ADCX (% r11) (% rax) *)
  0xf3; 0x4c; 0x0f; 0x38; 0xf6; 0xe6;
                           (* ADOX (% r12) (% rsi) *)
  0x66; 0x4c; 0x0f; 0x38; 0xf6; 0xe6;
                           (* ADCX (% r12) (% rsi) *)
  0x4d; 0x0f; 0xa4; 0xdc; 0x01;
                           (* SHLD (% r12) (% r11) (Imm8 (word 1)) *)
  0xba; 0x13; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 19)) *)
  0x49; 0xff; 0xc4;        (* INC (% r12) *)
  0x49; 0x0f; 0xba; 0xeb; 0x3f;
                           (* BTS (% r11) (Imm8 (word 63)) *)
  0xc4; 0xc2; 0xfb; 0xf6; 0xdc;
                           (* MULX4 (% rbx,% rax) (% rdx,% r12) *)
  0x49; 0x01; 0xc0;        (* ADD (% r8) (% rax) *)
  0x49; 0x11; 0xd9;        (* ADC (% r9) (% rbx) *)
  0x49; 0x11; 0xf2;        (* ADC (% r10) (% rsi) *)
  0x49; 0x11; 0xf3;        (* ADC (% r11) (% rsi) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xf7; 0xd0;        (* NOT (% rax) *)
  0x48; 0x21; 0xd0;        (* AND (% rax) (% rdx) *)
  0x49; 0x29; 0xc0;        (* SUB (% r8) (% rax) *)
  0x49; 0x19; 0xf1;        (* SBB (% r9) (% rsi) *)
  0x49; 0x19; 0xf2;        (* SBB (% r10) (% rsi) *)
  0x49; 0x19; 0xf3;        (* SBB (% r11) (% rsi) *)
  0x49; 0x0f; 0xba; 0xf3; 0x3f;
                           (* BTR (% r11) (Imm8 (word 63)) *)
  0x4c; 0x89; 0x45; 0x00;  (* MOV (Memop Quadword (%% (rbp,0))) (% r8) *)
  0x4c; 0x89; 0x4d; 0x08;  (* MOV (Memop Quadword (%% (rbp,8))) (% r9) *)
  0x4c; 0x89; 0x55; 0x10;  (* MOV (Memop Quadword (%% (rbp,16))) (% r10) *)
  0x4c; 0x89; 0x5d; 0x18;  (* MOV (Memop Quadword (%% (rbp,24))) (% r11) *)
  0x48; 0x81; 0xc4; 0xe8; 0x01; 0x00; 0x00;
                           (* ADD (% rsp) (Imm32 (word 488)) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x5d;                    (* POP (% rbp) *)
  0x5b;                    (* POP (% rbx) *)
  0xc3                     (* RET *)
]];;

let curve25519_x25519base_mc,
    (curve25519_x25519base_constant_data::_) =
    define_assert_relocs_from_elf "curve25519_x25519base_mc"
    "x86/curve25519/curve25519_x25519base.o"
    (fun b ADDR -> curve25519_x25519base_body
       [0xf3; 0x0f; 0x1e; 0xfa]  (* ENDBR64 *)
       b ADDR);;

let curve25519_x25519base_tmc =
  define_trimmed "curve25519_x25519base_tmc" curve25519_x25519base_mc;;

let CURVE25519_X25519BASE_EXEC =
  X86_MK_EXEC_RULE curve25519_x25519base_tmc;;

(* ------------------------------------------------------------------------- *)
(* Actually proving that the tables are correct.                             *)
(* ------------------------------------------------------------------------- *)

let edwards25519_exprojective = define
 `edwards25519_exprojective P (X,Y,Z,W) <=>
        exprojective (integer_mod_ring p_25519) P (&X,&Y,&Z,&W)`;;

let edwards25519_exprojective2 = define
 `edwards25519_exprojective2 P (X,Y,Z,W) <=>
        X < 2 * p_25519 /\ Y < 2 * p_25519 /\
        Z < 2 * p_25519 /\ W < 2 * p_25519 /\
        edwards25519_exprojective P
         (X MOD p_25519,Y MOD p_25519,Z MOD p_25519, W MOD p_25519)`;;

let edwards25519_epprojective = define
 `edwards25519_epprojective (x,y) (YMX,XPY,KXY) <=>
        x < &p_25519 /\ y < &p_25519 /\
        &YMX = (y - x) rem &p_25519 /\
        &XPY = (x + y) rem &p_25519 /\
        &KXY = (&2 * &d_25519 * x * y) rem &p_25519`;;

let EDWARDS25519_EXPROJECTIVE_IMP_EXPROJECTIVE2 = prove
 (`!P X Y Z W.
        edwards25519_exprojective P (X,Y,Z,W)
        ==> edwards25519_exprojective2 P (X,Y,Z,W)`,
  REWRITE_TAC[edwards25519_exprojective; edwards25519_exprojective2] THEN
  SIMP_TAC[EXPROJECTIVE_ALT; FORALL_PAIR_THM;
           FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_25519] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  SIMP_TAC[INT_REM_LT; INT_POS] THEN INT_ARITH_TAC);;

let EDWARDS25519_EXPROJECTIVE_BOUND = prove
 (`!x y X Y Z W.
        edwards25519_exprojective (x,y) (X,Y,Z,W)
        ==> x < &p_25519 /\ y < &p_25519 /\
            X < p_25519 /\ Y < p_25519 /\ Z < p_25519 /\ W < p_25519`,
  REWRITE_TAC[edwards25519_exprojective; exprojective] THEN
  REWRITE_TAC[p_25519; IN_INTEGER_MOD_RING_CARRIER; INT_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let GE25519_POW_1 = prove
 (`group_pow edwards25519_group E_25519 1 =
    (&15112221349535400772501151409588531511454012693041857206046113283949847762202,
     &46316835694926478169428394003475163141307993866256225615783033603165251855960)`,
  REWRITE_TAC[E_25519] THEN
  MATCH_MP_TAC GROUP_POW_1 THEN
  REWRITE_TAC[GSYM E_25519; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519]);;

let GE25519_GROUPER =
  let pth = prove
   (`group_pow edwards25519_group E_25519 m = x /\
     group_pow edwards25519_group E_25519 n = y
     ==> group_pow edwards25519_group E_25519 (m + n) =
         group_mul edwards25519_group x y`,
    MESON_TAC[GROUP_POW_ADD; GROUP_POW; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519]) in
  fun th1 th2 ->
    CONV_RULE
     (BINOP2_CONV (RAND_CONV NUM_ADD_CONV) ECGROUP_MUL_CONV)
     (MATCH_MP pth (CONJ th1 th2));;

let BYTES_LOADED_DATA = prove
 (`bytes_loaded s tab curve25519_x25519base_constant_data <=>
   read (memory :> bytes(tab,48576)) s =
   num_of_bytelist curve25519_x25519base_constant_data`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV)
     (AP_TERM `LENGTH:byte list->num` curve25519_x25519base_constant_data)]);;

let X25519BASE_TABLE_LEMMA = prove
 (`read (memory :> bytes(wpc,48576)) s =
   num_of_bytelist curve25519_x25519base_constant_data
   ==> edwards25519_exprojective
        (group_pow edwards25519_group E_25519 (2 EXP 254))
        (bignum_from_memory(wpc,4) s,
         bignum_from_memory(word_add wpc (word 0x20),4) s,
         1,
         bignum_from_memory(word_add wpc (word 0x40),4) s) /\
       edwards25519_exprojective
        (group_pow edwards25519_group E_25519 (2 EXP 254 + 8))
        (bignum_from_memory(word_add wpc (word 0x60),4) s,
         bignum_from_memory(word_add wpc (word 0x80),4) s,
         1,
         bignum_from_memory(word_add wpc (word 0xa0),4) s) /\
       !i. i < 63
           ==> !j. j < 8
                   ==> edwards25519_epprojective
                        (group_pow edwards25519_group E_25519
                           (2 EXP (4 * (i + 1)) * (j + 1)))
         (bignum_from_memory(word_add wpc (word(0xc0 + 768 * i + 96 * j)),4) s,
          bignum_from_memory(word_add wpc (word(0xc0 + 768 * i + 96 * j + 32)),4) s,
          bignum_from_memory(word_add wpc (word(0xc0 + 768 * i + 96 * j + 64)),4) s) /\
         ~(bignum_from_memory(word_add wpc (word(0xc0 + 768 * i + 96 * j + 64)),4) s =
           0)`,
  let GE25519_POWERS =
    end_itlist CONJ
     (funpow 63 (fun l -> let x = W GE25519_GROUPER (hd l) in
                        funpow 7 (fun l -> GE25519_GROUPER x (hd l)::l) (x::l))
                [funpow 3 (W GE25519_GROUPER) GE25519_POW_1]) in
  REWRITE_TAC[GSYM BYTES_LOADED_DATA; curve25519_x25519base_constant_data] THEN
  SUBST1_TAC(WORD_RULE `wpc:int64 = word(val wpc + 0)`) THEN
  SPEC_TAC(`val(wpc:int64)`,`pc:num`) THEN GEN_TAC THEN
  CONV_TAC(LAND_CONV DATA64_CONV) THEN
  REWRITE_TAC[GSYM WORD_ADD; ADD_CLAUSES; bytes_loaded_nil] THEN STRIP_TAC THEN
  CONV_TAC(funpow 2 RAND_CONV (BINDER_CONV (RAND_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC(funpow 2 RAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bignum_of_wordlist] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[GE25519_POWERS;
   GE25519_GROUPER (el 4 (CONJUNCTS GE25519_POWERS))
                   (last (CONJUNCTS GE25519_POWERS))] THEN
  REWRITE_TAC[p_25519; edwards25519_exprojective; edwards25519_epprojective;
              exprojective; d_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Common lemmas and tactics for the component proofs.                       *)
(* ------------------------------------------------------------------------- *)

let p25519redlemma = prove
 (`!n. n <= (2 EXP 64 - 1) * (p_25519 - 1)
       ==> let q = n DIV 2 EXP 255 + 1 in
           q < 2 EXP 64 /\
           q * p_25519 <= n + p_25519 /\
           n < q * p_25519 + p_25519`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[p_25519] THEN ARITH_TAC);;

let lvs =
 ["resx",[`RBP`;`0`];
  "scalar",[`RSP`;`0`];
  "tabent",[`RSP`;`32`];
  "ymx_2",[`RSP`;`32`];
  "xpy_2",[`RSP`;`64`];
  "kxy_2",[`RSP`;`96`];
  "acc",[`RSP`;`128`];
  "x_1",[`RSP`;`128`];
  "y_1",[`RSP`;`160`];
  "z_1",[`RSP`;`192`];
  "w_1",[`RSP`;`224`];
  "x_3",[`RSP`;`128`];
  "y_3",[`RSP`;`160`];
  "z_3",[`RSP`;`192`];
  "w_3",[`RSP`;`224`];
  "tmpspace",[`RSP`;`256`];
  "t0",[`RSP`;`256`];
  "t1",[`RSP`;`288`];
  "t2",[`RSP`;`320`];
  "t3",[`RSP`;`352`];
  "t4",[`RSP`;`384`];
  "t5",[`RSP`;`416`]];;

(* ------------------------------------------------------------------------- *)
(* We will use this in macros and subroutines, with specific variables.      *)
(* ------------------------------------------------------------------------- *)

let curve25519_x25519base_tmc' =
  SPECL [`pc:num`; `tables:num`] curve25519_x25519base_tmc;;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_p25519.                                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P25519_TAC =
  X86_MACRO_SIM_ABBREV_TAC curve25519_x25519base_tmc' 91 lvs
   `!(t:x86state) pcin pcout q3 n3 q1 n1 q2 n2.
      !m. read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x2e74) (word_add (read q3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (curve25519_x25519base_tmc pc tables) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RBP s = read RBP t /\
                read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                read(memory :> bytes(word_add (read q3 t) (word n3),8 * 4)) s =
                (m * n) MOD p_25519)
         (MAYCHANGE [RIP; RSI; RAX; RBX; RCX; RDX;
                     R8; R9; R10; R11; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(word_add (read q3 t) (word n3),8 * 4)] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s1" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiplication block, similar to bignum_mul_4_8 ***)

  X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC (2--56) (2--56) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s4; sum_s15; sum_s30; sum_s45]`;
    `h = bignum_of_wordlist[sum_s48; sum_s51; sum_s54; sum_s56]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC (57--71) (57--71) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s60; sum_s63; sum_s66; sum_s69; sum_s71]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (72--75) THEN
  ABBREV_TAC `t = bignum_of_wordlist
   [sum_s60; sum_s63; sum_s66; word_or sum_s69 (word 9223372036854775808)]` THEN
  SUBGOAL_THEN `&ca = &t + &2 pow 255 * (&(ca DIV 2 EXP 255) - &1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `c = t + e * (d - &1):real <=> c + e = t + e * d`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
    `c + d = t + 2 EXP 255 * c DIV 2 EXP 255 <=> c MOD 2 EXP 255 + d = t`] THEN
    MAP_EVERY EXPAND_TAC ["ca"; "t"] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(4,1)] THEN
    REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE
     `2 EXP 256 * n = 2 EXP 255 * 2 * n`] THEN
    REWRITE_TAC[MOD_MULT_MOD; ARITH_RULE
     `2 EXP 255 = 2 EXP 192 * 2 EXP 63`] THEN
    REWRITE_TAC[BIGNUM_OF_WORDLIST_SPLIT_RULE(3,1)] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `bignum_of_wordlist [sum_s60; sum_s63; sum_s66] < 2 EXP 192`
    (fun th -> SIMP_TAC[th; MOD_LT; DIV_LT]) THENL
     [BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE
     `(e * x + a) + e * y:num = a + e * z <=> e * (x + y) = e * z`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[BIGNUM_OF_WORDLIST_SING] THEN
    REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD] THEN
    ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or (word_and x (word_not m)) m`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and (word_and x (word_not m)) m = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    ALL_TAC] THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s71 sum_s69) (63,64)` THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(hw:int64)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    EXPAND_TAC "hw" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[CONG; ADD_SYM; MULT_SYM] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q:int64 = word_add hw (word 1)` THEN
  SUBGOAL_THEN `&(val(q:int64)):real = &(val(hw:int64)) + &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN EXPAND_TAC "q" THEN
    ASM_SIMP_TAC[VAL_WORD_ADD; VAL_WORD_1; DIMINDEX_64; MOD_LT];
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC
   [76;77;78;79;80;84;85;86;87] (76--92) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(hw:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN

  (*** Comparison computation and then the rest is easy ***)

  SUBGOAL_THEN `ca < (val(hw:int64) + 1) * p_25519 <=> ~carry_s80`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REAL_BITVAL_NOT] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN BOUNDER_TAC[];
    REWRITE_TAC[REAL_BITVAL_NOT] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_UNMASK_64]) THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s80:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_4_TAC =
  X86_MACRO_SIM_ABBREV_TAC curve25519_x25519base_tmc' 82 lvs
   `!(t:x86state) pcin pcout q3 n3 q1 n1 q2 n2.
      !m. read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x2e74) (word_add (read q3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (curve25519_x25519base_tmc pc tables) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RBP s = read RBP t /\
                read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                read(memory :> bytes(word_add (read q3 t) (word n3),8 * 4)) s
                < 2 * p_25519 /\
                (read(memory :> bytes(word_add (read q3 t) (word n3),8 * 4)) s ==
                 m * n) (mod p_25519))
           (MAYCHANGE [RIP; RAX; RBX; RCX; RDX;
                       R8; R9; R10; R11; R12; R13; R14; R15] ,,
            MAYCHANGE [memory :> bytes(word_add (read q3 t) (word n3),8 * 4)] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s1" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiplication block, similar to bignum_mul_4_8 ***)

  X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC (2--56) (2--56) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s4; sum_s15; sum_s30; sum_s45]`;
    `h = bignum_of_wordlist[sum_s48; sum_s51; sum_s54; sum_s56]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Instantiate the quotient approximation lemma ***)

  MP_TAC(SPEC `38 * h + l` p25519redlemma) THEN ANTS_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN REWRITE_TAC[p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC] THEN

  (*** Reduction from 8 digits to 5 digits ***)

  X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC (57--71) (57--71) THEN
  ABBREV_TAC
   `ca = bignum_of_wordlist[sum_s60; sum_s63; sum_s66; sum_s69; sum_s71]` THEN
  SUBGOAL_THEN `(38 * h + l) DIV 2 EXP 255 + 1 <= 78`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l = ca` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "ca"] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** Quotient estimate computation ***)

  X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (72--75) THEN
  ABBREV_TAC `hw:int64 = word_subword
    ((word_join:int64->int64->int128) sum_s71 sum_s69) (63,64)` THEN
  SUBGOAL_THEN `ca DIV 2 EXP 255 = val(hw:int64)`
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
   [UNDISCH_TAC `ca DIV 2 EXP 255 + 1 <= 78` THEN REWRITE_TAC[ARITH_RULE
     `n DIV 2 EXP 255 = n DIV 2 EXP 192 DIV 2 EXP 63`] THEN
    EXPAND_TAC "ca" THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
    DISCH_THEN(fun th ->
     MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP 64` THEN
     CONJ_TAC THENL [MP_TAC th THEN ARITH_TAC; REWRITE_TAC[VAL_BOUND_64]]) THEN
    EXPAND_TAC "hw" THEN
    SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[bignum_of_wordlist; MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[CONG; ADD_SYM; MULT_SYM] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC;
    ALL_TAC] THEN

  ABBREV_TAC `qm:int64 = word_mul (word 19:int64) hw` THEN
  SUBGOAL_THEN `&(val(qm:int64)):real = &19 * &(val(hw:int64))`
  ASSUME_TAC THENL
   [EXPAND_TAC "qm" THEN
    REWRITE_TAC[VAL_WORD_MUL; DIMINDEX_64; REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(hw:int64) + 1 <= 78` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The rest of the computation ***)

  X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC (76--79) (76--83) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONG; num_congruent] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\ ca - q * p < p2 /\ x = ca - q * p
    ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(hw:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `x - y:int < z <=> x < y + z`] THEN
    REWRITE_TAC[INT_ARITH `h * p + &2 * p:int = (h + &1) * p + p`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_CLAUSES];
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_CLAUSES; LE_0] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `h * p <= ca <=> (h + 1) * p <= ca + p`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RULE
   `(x:int == y - z) (mod p) <=> (x + z == y) (mod p)`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM num_congruent] THEN
  REWRITE_TAC[REAL_CONGRUENCE; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  EXPAND_TAC "ca" THEN
  REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
  ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  UNDISCH_THEN `ca DIV 2 EXP 255 = val(hw:int64)` (SUBST1_TAC o SYM) THEN
  EXPAND_TAC "ca" THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
  REWRITE_TAC[bignum_of_wordlist; ARITH_RULE
   `(l + 2 EXP 64 * h) DIV 2 EXP 63 = l DIV 2 EXP 63 + 2 * h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_DIV] THEN
  REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add_twice4 (slightly sharper disjunctive hypothesis).        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_TWICE4_TAC =
  X86_MACRO_SIM_ABBREV_TAC curve25519_x25519base_tmc' 19 lvs
   `!(t:x86state) pcin pcout q3 n3 q1 n1 q2 n2.
      !m. read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x2e74) (word_add (read q3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (curve25519_x25519base_tmc pc tables) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDI s = read RDI t /\
                read RSI s = read RSI t /\
                read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                (m < 2 * p_25519 \/ n < 2 * p_25519
                 ==> (read(memory :> bytes(word_add (read q3 t) (word n3),8 * 4)) s ==
                      m + n) (mod p_25519)))
        (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
         MAYCHANGE [memory :> bytes(word_add (read q3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC [3;5;7;9] (1--11) THEN
  SUBGOAL_THEN `carry_s9 <=> 2 EXP 256 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC (12--15) (12--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x = x'
             ==> (x:int == a) (mod p)`) THEN
  EXISTS_TAC
   `if 2 EXP 256 <= m + n then (&m + &n) - &2 * &p_25519:int else &m + &n` THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `2 EXP 256` o MATCH_MP (ARITH_RULE
     `m < p \/ n < p
      ==> !e:num. p < e /\ m < e /\ n < e ==> m + n < e + p`)) THEN
    ANTS_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NOT_LE; SYM(NUM_EXP_CONV `2 EXP 256`)]) THEN
  ABBREV_TAC `bb <=> 2 EXP 256 <= m + n` THEN
  MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of double_twice4.                                               *)
(* ------------------------------------------------------------------------- *)

let LOCAL_DOUBLE_TWICE4_TAC =
  X86_MACRO_SIM_ABBREV_TAC curve25519_x25519base_tmc' 19 lvs
   `!(t:x86state) pcin pcout q3 n3 q1 n1.
      !n. read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x2e74) (word_add (read q3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (curve25519_x25519base_tmc pc tables) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDI s = read RDI t /\
                read RSI s = read RSI t /\
                read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                (n < 2 * p_25519
                 ==> (read(memory :> bytes(word_add (read q3 t) (word n3),8 * 4)) s ==
                      2 * n) (mod p_25519)))
        (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
         MAYCHANGE [memory :> bytes(word_add (read q3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC [3;5;7;9] (1--11) THEN
  SUBGOAL_THEN `carry_s9 <=> 2 EXP 256 <= 2 * n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC (12--15) (12--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x = x'
             ==> (x:int == a) (mod p)`) THEN
  EXISTS_TAC
   `if 2 EXP 256 <= 2 * n then (&2 * &n) - &2 * &p_25519:int else &2 * &n` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    COND_CASES_TAC THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NOT_LE; SYM(NUM_EXP_CONV `2 EXP 256`)]) THEN
  ABBREV_TAC `bb <=> 2 EXP 256 <= 2 * n` THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub_twice4 (slightly sharper hypothesis distinctions).       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_TWICE4_TAC =
  X86_MACRO_SIM_ABBREV_TAC curve25519_x25519base_tmc' 19 lvs
   `!(t:x86state) pcin pcout q3 n3 q1 n1 q2 n2.
      !m. read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) t = n
      ==>
      nonoverlapping (word pc,0x2e74) (word_add (read q3 t) (word n3),8 * 4)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) (curve25519_x25519base_tmc pc tables) /\
                read RIP s = pcin /\
                read RSP s = read RSP t /\
                read RDI s = read RDI t /\
                read RSI s = read RSI t /\
                read(memory :> bytes(word_add (read q1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read q2 t) (word n2),8 * 4)) s = n)
           (\s. read RIP s = pcout /\
                (m < 2 * p_25519 /\ n < 2 * p_25519
                 ==> read(memory :> bytes(word_add (read q3 t) (word n3),8 * 4)) s
                     < 2 * p_25519) /\
                (n < 2 * p_25519
                 ==> (&(bignum_from_memory
                         (word_add (read q3 t) (word n3),4) s):int ==
                      &m - &n) (mod (&p_25519))))
        (MAYCHANGE [RIP; RAX; RBX; RCX; R8; R9; R10] ,,
         MAYCHANGE [memory :> bytes(word_add (read q3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC (1--10) (1--10) THEN
  SUBGOAL_THEN `carry_s10 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC (12--15) (11--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == &m - &n) (mod p) /\
             (m < p2 /\ n < p2 ==> x' < &p2) /\
             (n < p2 ==> &x = x')
             ==> (m < p2 /\ n < p2 ==> x < p2) /\
                 (n:num < p2 ==> (&x:int == &m - &n) (mod p))`) THEN
  EXISTS_TAC `if m < n then &m - &n + &2 * &p_25519:int else &m - &n` THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC INTEGER_RULE;
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
      SUBGOAL_THEN `m < 2 EXP 256` MP_TAC THENL
       [EXPAND_TAC "m" THEN BOUNDER_TAC[];
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN REAL_ARITH_TAC]];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NOT_LT]) THEN
  ABBREV_TAC `bb <=> m:num < n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of modular inverse inlining                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MODINV_TAC =
 X86_SUBROUTINE_SIM_TAC
  (curve25519_x25519base_tmc',
   CURVE25519_X25519BASE_EXEC,
   0x18b1,
   (GEN_REWRITE_CONV RAND_CONV [bignum_inv_p25519_tmc] THENC TRIM_LIST_CONV)
   `TRIM_LIST (17,18) bignum_inv_p25519_tmc`,
   CORE_INV_P25519_CORRECT)
  [`read RDI s`; `read RSI s`;
   `read (memory :> bytes(read RSI s,8 * 4)) s`;
   `pc + 0x18b1`; `stackpointer:int64`];;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let CURVE25519_X25519BASE_CORRECT = time prove
 (`!tables res scalar n pc stackpointer.
    riprel32_within_bounds tables (pc + 84) /\
    ALL (nonoverlapping (stackpointer,488))
        [(word pc,0x2e74); (word tables,48576); (res,32); (scalar,32)] /\
    ALL (nonoverlapping (res,32)) [(word pc,0x2e74); (word tables,48576)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (curve25519_x25519base_tmc pc tables) /\
              read RIP s = word(pc + 0x11) /\
              bytes_loaded s (word tables)
                curve25519_x25519base_constant_data /\
              read RSP s = stackpointer /\
              C_ARGUMENTS [res; scalar] s /\
              bignum_from_memory (scalar,4) s = n)
         (\s. read RIP s = word (pc + 0x2e62) /\
              bignum_from_memory (res,4) s = rfcx25519(n,9))
         (MAYCHANGE [RIP; RDI; RSI; RAX; RBX; RCX; RDX; RBP;
                     R8; R9; R10; R11; R12; R13; R14; R15] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(res,32);
                     memory :> bytes(stackpointer,488)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`tables:num`; `res:int64`; `scalar:int64`; `n_input:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN

  REWRITE_TAC[BYTES_LOADED_APPEND_CLAUSE] THEN
  REWRITE_TAC[fst CURVE25519_X25519BASE_EXEC] THEN
  REWRITE_TAC[BYTES_LOADED_DATA] THEN

  (*** The modified forms of the inputs that get computed early on  ***)
  (*** The nn' is the computed value just modifying the top 2 bits ***)

  ABBREV_TAC `nn = 2 EXP 254 + n_input MOD 2 EXP 254 - n_input MOD 8` THEN
  ABBREV_TAC `nn' = n_input MOD 2 EXP 254` THEN
  ASM_REWRITE_TAC[rfcx25519] THEN CONV_TAC NUM_REDUCE_CONV THEN

  (*** Setup of the main loop ***)

  ENSURES_WHILE_AUP_TAC `1` `64` `pc + 0x197` `pc + 0x17a1`
   `\i s.
      read (memory :> bytes(word tables,48576)) s =
      num_of_bytelist curve25519_x25519base_constant_data /\
      read RSP s = stackpointer /\
      read (memory :> bytes64 (word_add stackpointer (word 448))) s = res /\
      read (memory :> bytes64 (word_add stackpointer (word 480))) s =
      word(tables + 0xc0 + 768 * (i - 1)) /\
      read (memory :> bytes64 (word_add stackpointer (word 456))) s =
      word (4 * i) /\
      val(read (memory :> bytes64 (word_add stackpointer (word 464))) s) <= 1 /\
      (i >= 64
       ==> val(read (memory :> bytes64(word_add stackpointer (word 464))) s)
            < 1) /\
      bignum_from_memory (stackpointer,4) s = nn' /\
      edwards25519_exprojective2
       (group_zpow edwards25519_group E_25519
         (&nn - &2 pow (4 * i) *
                (&(nn' DIV 2 EXP (4 * i)) +
     &(val(read (memory :> bytes64 (word_add stackpointer (word 464))) s)))))
       (bignum_from_memory(word_add stackpointer (word 128),4) s,
        bignum_from_memory(word_add stackpointer (word 160),4) s,
        bignum_from_memory(word_add stackpointer (word 192),4) s,
        bignum_from_memory(word_add stackpointer (word 224),4) s)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial setup and modification of the inputs ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    BIGNUM_LDIGITIZE_TAC "n_" `read (memory :> bytes (scalar,8 * 4)) s0` THEN

    FIRST_ASSUM(MP_TAC o MATCH_MP X25519BASE_TABLE_LEMMA) THEN

    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [WORD_ADD] THEN

    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(K ALL_TAC) THEN
    BIGNUM_LDIGITIZE_TAC "x0_"
      `bignum_from_memory(word tables:int64,4) s0` THEN
    BIGNUM_LDIGITIZE_TAC "y0_"
      `bignum_from_memory(word_add (word tables) (word 32),4) s0` THEN
    BIGNUM_LDIGITIZE_TAC "t0_"
      `bignum_from_memory(word_add (word tables) (word 64),4) s0` THEN
    BIGNUM_LDIGITIZE_TAC "x1_"
      `bignum_from_memory(word_add (word tables) (word 96),4) s0` THEN
    BIGNUM_LDIGITIZE_TAC "y1_"
      `bignum_from_memory(word_add (word tables) (word 128),4) s0` THEN
    BIGNUM_LDIGITIZE_TAC "t1_"
      `bignum_from_memory(word_add (word tables) (word 160),4) s0` THEN

    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (1--14) THEN

    (*** Fold the rip-relative LEA results so `read R10 s = word tables`
         and `read R11 s = word_add (word tables) (word 96)`, using the
         riprel32_within_bounds precondition. ***)

    UNDISCH_TAC `read R10 s14 =
        word(val (word (pc + 84):(64)word) +
             val (word_sx (iword (&tables - (&pc + &84)):int32):(64)word):num)` THEN
    IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `read R11 s14 =
        word_add
        (word (val (word (pc + 84):(64)word) +
               val (word_sx (iword (&tables - (&pc + &84)):int32):(64)word):num))
        (word 96)` THEN
    IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (15--72) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN

    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REPLICATE_TAC 3
     (CONJ_TAC THENL [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV); ALL_TAC]) THEN
    CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["nn'"; "n_input"] THEN MATCH_MP_TAC(ARITH_RULE
       `m + 2 EXP 254 * n DIV 2 EXP 254 = n
        ==> m = n MOD 2 EXP 254`) THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_OF_WORDLIST_DIV_CONV) THEN
      REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 62 - 1`)] THEN
      ONCE_REWRITE_TAC[WORD_AND_SYM] THEN
      REWRITE_TAC[bignum_of_wordlist; VAL_WORD_AND_MASK_WORD] THEN
      ARITH_TAC;
      ALL_TAC] THEN

    MATCH_MP_TAC EDWARDS25519_EXPROJECTIVE_IMP_EXPROJECTIVE2 THEN
    REWRITE_TAC[VAL_WORD_0; INT_ADD_RID; MULT_CLAUSES] THEN
    SUBGOAL_THEN
     `&nn - &2 pow 4 * &(nn' DIV 2 EXP 4):int =
      &(2 EXP 254 + 8 * (n_input DIV 8) MOD 2)`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["nn"; "nn'"] THEN
      REWRITE_TAC[INT_EQ_SUB_RADD; INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
      MATCH_MP_TAC(ARITH_RULE
       `x MOD 2 EXP 4 = a + r ==> x - r = a + 2 EXP 4 * x DIV 2 EXP 4`) THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `MIN 254 4 = 4`] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 4 = 8 * 2`; MOD_MULT_MOD];
      ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_AND_POW2; ARITH_RULE `8 = 2 EXP 3`] THEN
    SUBGOAL_THEN `(n_input DIV 2 EXP 3) MOD 2 = bitval(bit 3 (n_0:int64))`
    SUBST1_TAC THENL
     [EXPAND_TAC "n_input" THEN ONCE_REWRITE_TAC[bignum_of_wordlist] THEN
      REWRITE_TAC[DIV_MOD; ARITH_RULE `2 EXP 3 * 2 = 16`] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 64 * x = 16 * 2 EXP 60 * x`] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[BIT_VAL; BITVAL_ODD; DIV_MOD] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GROUP_NPOW] THEN
    REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ; BITVAL_EQ_0; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; BITVAL_CLAUSES] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
     [bignum_of_wordlist; VAL_WORD_1; VAL_WORD_0;
      ADD_CLAUSES; MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; ARITH_RULE `2 EXP 3 = 8`];

    (*** The main loop invariant for adding the next table entry ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `xn:num`
     `bignum_from_memory (word_add stackpointer (word 128),4)` THEN
    GHOST_INTRO_TAC `yn:num`
     `bignum_from_memory (word_add stackpointer (word 160),4)` THEN
    GHOST_INTRO_TAC `zn:num`
     `bignum_from_memory (word_add stackpointer (word 192),4)` THEN
    GHOST_INTRO_TAC `wn:num`
     `bignum_from_memory(word_add stackpointer (word 224),4)` THEN
    GHOST_INTRO_TAC `nbias:num`
      `\s. val(read (memory :> bytes64
            (word_add stackpointer (word 464))) s)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
    DISCH_THEN(X_CHOOSE_THEN `bias:bool` SUBST_ALL_TAC) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read(memory :> bytes64(word_add stackpointer
       (word(8 * val(word_ushr (word (4 * i):int64) 6))))) s0 =
      word(nn' DIV (2 EXP (64 * (4 * i) DIV 64)) MOD 2 EXP (64 * 1))`
    ASSUME_TAC THENL
     [EXPAND_TAC "nn'" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_MOD] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 64 ==> MIN (4 - (4 * i) DIV 64) 1 = 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL] THEN
      AP_THM_TAC THEN REPLICATE_TAC 6 AP_TERM_TAC THEN
      REWRITE_TAC[VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM BOUNDER_TAC[];
      ALL_TAC] THEN

    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (1--8) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MOD_64_CLAUSES]) THEN
    ABBREV_TAC `bf = (nn' DIV (2 EXP (4 * i))) MOD 16` THEN
    SUBGOAL_THEN
     `word_and
       (word_ushr
        (word ((nn' DIV 2 EXP (64 * (4 * i) DIV 64)) MOD 2 EXP 64))
       ((4 * i) MOD 64))
      (word 15):int64 = word bf`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD;
                  ARITH_RULE `15 = 2 EXP 4 - 1`] THEN
      REWRITE_TAC[VAL_WORD_USHR; DIMINDEX_64; MOD_64_CLAUSES] THEN

      EXPAND_TAC "bf" THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `16 = 2 EXP 4`] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
      REWRITE_TAC[DIV_MOD; MOD_MOD_EXP_MIN; GSYM EXP_ADD; DIV_DIV] THEN
      REWRITE_TAC[ARITH_RULE `64 * i DIV 64 + i MOD 64 = i`] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[ARITH_RULE `64 = 4 * 16`] THEN
      SIMP_TAC[DIV_MULT2; MOD_MULT2; ARITH_EQ] THEN
      UNDISCH_TAC `i < 64` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word bf) (word(bitval bias)):int64 =
      word(bf + bitval bias)`
    SUBST_ALL_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN

    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (9--17) THEN
    ABBREV_TAC `bias' <=> bf + bitval bias >= 9` THEN
    SUBGOAL_THEN
     `word_add (word_neg(word(bitval(val(word(bf + bitval bias):int64) < 9))))
               (word 1):int64 =
      word(bitval bias')`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `bf + bitval bias < 2 EXP 64` MP_TAC THENL
       [EXPAND_TAC "bf" THEN REWRITE_TAC[bitval] THEN ARITH_TAC;
        SIMP_TAC[MOD_LT] THEN DISCH_THEN(K ALL_TAC)] THEN
      EXPAND_TAC "bias'" THEN REWRITE_TAC[GE; GSYM NOT_LT] THEN
      ASM_CASES_TAC `bf + bitval bias < 9` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
      ALL_TAC] THEN
    ABBREV_TAC
     `ix = if bias' then 16 - (bf + bitval bias) else bf + bitval bias` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL; BITVAL_EQ_0; COND_SWAP]) THEN
    SUBGOAL_THEN
     `(if bias'
       then word_sub (word 16) (word (bf + bitval bias))
       else word (bf + bitval bias)):int64 = word ix`
    SUBST_ALL_TAC THENL
     [EXPAND_TAC "ix" THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUB] THEN
      MATCH_MP_TAC(MESON[] `p ==> x = if p then x else y`) THEN
      EXPAND_TAC "bf" THEN REWRITE_TAC[bitval] THEN ARITH_TAC;
      ALL_TAC] THEN

    FIRST_ASSUM(MP_TAC o last o CONJUNCTS o
      MATCH_MP X25519BASE_TABLE_LEMMA) THEN
    DISCH_THEN(MP_TAC o SPEC `i - 1`) THEN ASM_SIMP_TAC[SUB_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 64 ==> i - 1 < 63`] THEN
    REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE
      `tables + off + 768 * (i - 1) + jre =
       (tables + off + 768 * (i - 1)) + jre`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD] THEN
    ABBREV_TAC `tab:int64 = word(tables + 0xc0 + 768 * (i - 1))` THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [WORD_ADD_0] THEN

    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV)) THEN
    ABBREV_TAC `tab_0 = read (memory :> bytes64 tab) s17` THEN
    MAP_EVERY (fun i ->
        ABBREV_TAC(mk_eq(mk_var("tab_"^string_of_int i,`:int64`),
              vsubst [mk_small_numeral(8*i),`n:num`]
                     `read (memory :> bytes64 (word_add tab (word n))) s17`)))
        (1--95) THEN
    STRIP_TAC THEN

    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (18--239) THEN
    REABBREV_TAC `ymx_0 = read RAX s239` THEN
    REABBREV_TAC `ymx_1 = read RBX s239` THEN
    REABBREV_TAC `ymx_2 = read RCX s239` THEN
    REABBREV_TAC `ymx_3 = read RDX s239` THEN
    REABBREV_TAC `xpy_0 = read R8 s239` THEN
    REABBREV_TAC `xpy_1 = read R9 s239` THEN
    REABBREV_TAC `xpy_2 = read R10 s239` THEN
    REABBREV_TAC `xpy_3 = read R11 s239` THEN
    REABBREV_TAC `kxy_0 = read R12 s239` THEN
    REABBREV_TAC `kxy_1 = read R13 s239` THEN
    REABBREV_TAC `kxy_2 = read R14 s239` THEN
    REABBREV_TAC `kxy_3 = read R15 s239` THEN
    SUBGOAL_THEN `ix <= 8` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["ix"; "bias'"] THEN ARITH_TAC; ALL_TAC] THEN

    SUBGOAL_THEN
     `edwards25519_epprojective
        (group_pow edwards25519_group E_25519 (2 EXP (4 * i) * ix))
        (bignum_of_wordlist [ymx_0; ymx_1; ymx_2; ymx_3],
         bignum_of_wordlist [xpy_0; xpy_1; xpy_2; xpy_3],
         bignum_of_wordlist [kxy_0; kxy_1; kxy_2; kxy_3]) /\
      (1 <= ix ==> ~(bignum_of_wordlist [kxy_0; kxy_1; kxy_2; kxy_3] = 0))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ix <= 8` THEN
      REWRITE_TAC[ARITH_RULE `ix <= 8 <=> ix < 9`] THEN
      MAP_EVERY EXPAND_TAC
       ["ymx_0";"ymx_1";"ymx_2";"ymx_3";
        "xpy_0";"xpy_1";"xpy_2";"xpy_3";
        "kxy_0";"kxy_1";"kxy_2";"kxy_3"] THEN
      SPEC_TAC(`ix:num`,`ix:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; group_pow] THEN
      REWRITE_TAC[EDWARDS25519_GROUP; edwards_0; bignum_of_wordlist] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[edwards25519_epprojective; INTEGER_MOD_RING_CLAUSES] THEN
      REWRITE_TAC[p_25519] THEN CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN

    FIRST_X_ASSUM(MP_TAC o check(can
     (term_match []
       `read (memory :> bytes64 (word_add stackpointer (word 480))) s = y`) o
      concl)) THEN
    EXPAND_TAC "tab" THEN
    GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV) [GSYM WORD_ADD] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
     (not o (=) [] o intersect
       (`tab:int64`::map (fun i -> mk_var("tab_"^string_of_int i,`:int64`))
                         (1--95)) o
      frees o concl))) THEN
    DISCH_TAC THEN

    X86_ACCSTEPS_TAC CURVE25519_X25519BASE_EXEC
     (265--268) (240--281) THEN

    SUBGOAL_THEN
     `edwards25519_epprojective
        (group_zpow edwards25519_group E_25519
          (&2 pow (4 * i) *
          ((&bf + &(bitval(bias))) - &16 * &(bitval bias'))))
        (bignum_from_memory (word_add stackpointer (word 32),4) s281,
         bignum_from_memory (word_add stackpointer (word 64),4) s281,
         bignum_from_memory (word_add stackpointer (word 96),4) s281)`
    MP_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[WORD_SUB_0; WORD_EQ_0; VAL_WORD_BITVAL] THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i <= 8 ==> i < 2 EXP 64`] THEN
      REWRITE_TAC[BITVAL_EQ_0; COND_SWAP] THEN REWRITE_TAC[MESON [VAL_EQ_0]
       `val(if p then word 0 else y) = 0 <=> if p then T else val y = 0`] THEN
      REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_EQ_0] THEN
      REWRITE_TAC[TAUT `(if p then T else ~q) <=> q ==> p`] THEN
      UNDISCH_TAC
       `(if bias' then 16 - (bf + bitval bias)
         else bf + bitval bias) = ix` THEN
      ASM_CASES_TAC `bias':bool` THEN
      ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; BITVAL_CLAUSES; MULT_CLAUSES;
                   INT_SUB_RZERO; GROUP_NPOW] THEN
      SUBGOAL_THEN `bf + bitval bias <= 16` MP_TAC THENL
       [EXPAND_TAC "bf" THEN REWRITE_TAC[bitval] THEN ARITH_TAC;
        SIMP_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_SUB] THEN
        DISCH_TAC] THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP (INT_ARITH
       `a - b:int = c ==> b - a = --c`)) THEN
      UNDISCH_TAC
       `edwards25519_epprojective
         (group_pow edwards25519_group E_25519 (2 EXP (4 * i) * ix))
         (bignum_of_wordlist [ymx_0; ymx_1; ymx_2; ymx_3],
          bignum_of_wordlist [xpy_0; xpy_1; xpy_2; xpy_3],
          bignum_of_wordlist [kxy_0; kxy_1; kxy_2; kxy_3])` THEN
      REWRITE_TAC[INT_OF_NUM_EQ] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; INT_NEG_0; INT_MUL_RZERO; GROUP_NPOW] THENL
       [REWRITE_TAC[group_pow; EDWARDS25519_GROUP; edwards_0] THEN
        REWRITE_TAC[edwards25519_epprojective; INTEGER_MOD_RING_CLAUSES] THEN
        REWRITE_TAC[p_25519] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[INT_MUL_RNEG; INT_OF_NUM_CLAUSES; GROUP_ZPOW_POW] THEN
      SPEC_TAC(`group_pow edwards25519_group E_25519 (2 EXP (4 * i) * ix)`,
               `tp:int#int`) THEN
      REWRITE_TAC[FORALL_PAIR_THM; EDWARDS25519_GROUP; edwards_neg] THEN
      REWRITE_TAC[edwards25519_epprojective; INTEGER_MOD_RING_CLAUSES] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_MUL_LNEG; INT_MUL_RNEG] THEN
      MAP_EVERY X_GEN_TAC [`tx:int`; `ty:int`] THEN
      REWRITE_TAC[INT_ARITH `--x + y:int = y - x /\ y - -- x = x + y`] THEN
      SIMP_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM o last o CONJUNCTS) THEN
      REWRITE_TAC[INT_LT_REM_EQ; p_25519] THEN CONV_TAC INT_REDUCE_CONV THEN
      REWRITE_TAC[GSYM p_25519] THEN UNDISCH_TAC
       `1 <= ix ==> ~(bignum_of_wordlist[kxy_0; kxy_1; kxy_2; kxy_3] = 0)` THEN
      ASM_SIMP_TAC[LE_1; INT_REM_LNEG; GSYM INT_OF_NUM_EQ; INT_ABS_NUM] THEN
      DISCH_TAC THEN MATCH_MP_TAC INT_CONG_IMP_EQ THEN
      EXISTS_TAC `(&2:int) pow 256` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
         `y rem p = x
          ==> &0 <= p /\ p < e /\ &0 <= y rem p /\
              y rem p < p /\ &0 <= z /\ z < e
              ==> abs(z - (p - x)) < e`)) THEN
        REWRITE_TAC[INT_LT_REM_EQ; p_25519; INT_REM_POS_EQ] THEN
        CONV_TAC INT_REDUCE_CONV THEN BOUNDER_TAC[];
        REWRITE_TAC[REAL_INT_CONGRUENCE]] THEN
      REWRITE_TAC[INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[int_sub_th; int_of_num_th; int_pow_th] THEN
      REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

    DISCARD_MATCHING_ASSUMPTIONS [`edwards25519_epprojective a b`] THEN
    MAP_EVERY ABBREV_TAC
     [`ymx = bignum_from_memory (word_add stackpointer (word 32),4) s281`;
      `xpy = bignum_from_memory (word_add stackpointer (word 64),4) s281`;
      `kxy = bignum_from_memory (word_add stackpointer (word 96),4) s281`]
    THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

    LOCAL_DOUBLE_TWICE4_TAC 0 ["t0"; "z_1"] THEN
    LOCAL_SUB_TWICE4_TAC 0 ["t1"; "y_1"; "x_1"] THEN
    LOCAL_ADD_TWICE4_TAC 0 ["t2"; "y_1"; "x_1"] THEN
    LOCAL_MUL_4_TAC 0 ["t3"; "w_1"; "kxy_2"] THEN
    LOCAL_MUL_4_TAC 0 ["t1"; "t1"; "ymx_2"] THEN
    LOCAL_MUL_4_TAC 0 ["t2"; "t2"; "xpy_2"] THEN
    LOCAL_SUB_TWICE4_TAC 0 ["t4"; "t0"; "t3"] THEN
    LOCAL_ADD_TWICE4_TAC 0 ["t0"; "t0"; "t3"] THEN
    LOCAL_SUB_TWICE4_TAC 0 ["t5"; "t2"; "t1"] THEN
    LOCAL_ADD_TWICE4_TAC 0 ["t1"; "t2"; "t1"] THEN
    LOCAL_MUL_4_TAC 0 ["z_3"; "t4"; "t0"] THEN
    LOCAL_MUL_4_TAC 0 ["x_3"; "t5"; "t4"] THEN
    LOCAL_MUL_4_TAC 0 ["y_3"; "t0"; "t1"] THEN
    LOCAL_MUL_4_TAC 0 ["w_3"; "t5"; "t1"] THEN

    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC [296] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_BOUND] THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN UNDISCH_TAC `1 <= i` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `n < 1 <=> n = 0`; BITVAL_EQ_0] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 64 ==> (i + 1 >= 64 <=> i = 63)`] THEN
      DISCH_THEN SUBST_ALL_TAC THEN EXPAND_TAC "bias'" THEN
      MATCH_MP_TAC(ARITH_RULE `x < 8 /\ y <= 1 ==> ~(x + y >= 9)`) THEN
      REWRITE_TAC[BITVAL_BOUND] THEN EXPAND_TAC "bf" THEN
      MATCH_MP_TAC(MESON[LET_TRANS; MOD_LE] `x < b ==> x MOD n < b`) THEN
      SUBST1_TAC(SYM(ASSUME `n_input MOD 2 EXP 254 = nn'`)) THEN ARITH_TAC;
      ALL_TAC] THEN

    DISCARD_STATE_TAC "s296" THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`aligned a b`; `nonoverlapping_modulo a b c`] THEN

    SUBGOAL_THEN
     `(&nn:int) -
      &2 pow (4 * (i + 1)) *
      (&(nn' DIV 2 EXP (4 * (i + 1))) + &(bitval bias')) =
      (&nn - &2 pow (4 * i) * (&(nn' DIV 2 EXP (4 * i)) + &(bitval bias))) +
      (&2 pow (4 * i) * ((&bf + &(bitval bias)) - &16 * &(bitval bias')))`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      REWRITE_TAC[EXP_ADD; INT_POW_ADD] THEN
      REWRITE_TAC[INT_ARITH `n - x:int = (n - y) + p * (a - b) <=>
                             p * b + y = p * a + x`] THEN
      EXPAND_TAC "bf" THEN REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM DIV_DIV] THEN
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; GSYM MULT_ASSOC] THEN
      AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN

    FIRST_X_ASSUM(MP_TAC o check(can
       (term_match [] `edwards25519_epprojective p q`) o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [edwards25519_exprojective2]) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    SIMP_TAC[GROUP_ZPOW_ADD; GROUP_ZPOW;
             GENERATOR_IN_GROUP_CARRIER_EDWARDS25519] THEN
    MP_TAC(MATCH_MP GROUP_ZPOW GENERATOR_IN_GROUP_CARRIER_EDWARDS25519) THEN
    DISCH_THEN(fun th ->
     MAP_EVERY (MP_TAC o C SPEC th)
     [`&nn - &2 pow (4 * i) * (&(nn' DIV 2 EXP (4 * i)) + &(bitval bias)):int`;
      `&2 pow (4 * i) * ((&bf + &(bitval bias)) - &16 * &(bitval bias')):int`]
     ) THEN
    SPEC_TAC(`group_zpow edwards25519_group E_25519
               (&2 pow (4 * i) * ((&bf + &(bitval bias)) - &16 * &(bitval
              bias')))`,`P2:int#int`) THEN
    SPEC_TAC(`group_zpow edwards25519_group E_25519
               (&nn - &2 pow (4 * i) *
               (&(nn' DIV 2 EXP (4 * i)) + &(bitval bias)))`,`P1:int#int`) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
     (not o (=) [] o intersect [`n_input:num`; `i:num`; `bf:num`; `ix:num`]) o
      frees o concl)) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check ((=) [] o frees o concl))) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN

    MAP_EVERY X_GEN_TAC [`x1:int`; `y1:int`; `x2:int`; `y2:int`] THEN
    REWRITE_TAC[edwards25519_epprojective] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
      MATCH_MP EDWARDS25519_EXPROJECTIVE_BOUND) THEN

    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    REPEAT(ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC]) THEN
    DISCH_THEN(K ALL_TAC) THEN
    ASM_REWRITE_TAC[edwards25519_exprojective2] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN

    RULE_ASSUM_TAC(REWRITE_RULE
     [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN

    MP_TAC(ISPECL
     [`integer_mod_ring p_25519`; `&e_25519:int`; `&d_25519:int`;
      `x1:int`; `y1:int`;
      `&xn rem &p_25519`; `&yn rem &p_25519`;
      `&zn rem &p_25519`; `&wn rem &p_25519`;
      `x2:int`; `y2:int`;
      `x2:int`; `y2:int`; `&1:int`; `(x2 * y2) rem &p_25519`]
     EDWARDS_EXPROJADD4) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[EDWARDS_NONSINGULAR_25519] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN])) THEN
      SIMP_TAC[EDWARDS25519_GROUP] THEN
      REWRITE_TAC[edwards_curve] THEN STRIP_TAC THEN STRIP_TAC THEN
      REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [edwards25519_exprojective]) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[exprojective] THEN
      REWRITE_TAC[INTEGER_MOD_RING_CHAR; IN_INTEGER_MOD_RING_CARRIER;
                  INTEGER_MOD_RING_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519; e_25519; d_25519] THEN
      REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
      CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[GSYM p_25519] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC(MESON[RING_DIV_1]
       `x IN ring_carrier f /\ y = ring_1 f ==> ring_div f x y = x`) THEN
      ASM_REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; p_25519] THEN
      REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
      REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
      CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN

    REWRITE_TAC[edwards25519_exprojective; EDWARDS25519_GROUP] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[edwards_exprojadd4; edwards_exprojadd; edwards25519;
                INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN `&e_25519 = (-- &1) rem &p_25519` SUBST_ALL_TAC THENL
     [REWRITE_TAC[e_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[PAIR_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC;

    (*** The trivial loop-back subgoal ***)

    REPEAT STRIP_TAC THEN
    X86_SIM_TAC CURVE25519_X25519BASE_EXEC (1--2) THEN
    ASM_SIMP_TAC[VAL_WORD_LT; ARITH_RULE `4 * i < 256 <=> i < 64`];

    ALL_TAC] THEN

  (*** Clean up ready for the final translation part ***)

  REWRITE_TAC[GE; LE_REFL; ARITH_RULE `a < 1 <=> a = 0`] THEN
  GHOST_INTRO_TAC `zerobias:num`
   `\s. val(read(memory :> bytes64(word_add stackpointer (word 464))) s)` THEN
  ASM_CASES_TAC `zerobias = 0` THEN ASM_REWRITE_TAC[ENSURES_TRIVIAL] THEN
  EXPAND_TAC "nn'" THEN
  REWRITE_TAC[ARITH_RULE `(n MOD 2 EXP 254) DIV 2 EXP (4 * 64) = 0`] THEN
  REWRITE_TAC[INT_ADD_RID; INT_MUL_RZERO; INT_SUB_RZERO; GROUP_NPOW] THEN
  GHOST_INTRO_TAC `X:num`
   `bignum_from_memory (word_add stackpointer (word 128),4)` THEN
  GHOST_INTRO_TAC `Y:num`
   `bignum_from_memory (word_add stackpointer (word 160),4)` THEN
  GHOST_INTRO_TAC `Z:num`
   `bignum_from_memory (word_add stackpointer (word 192),4)` THEN
  GHOST_INTRO_TAC `W:num`
   `bignum_from_memory (word_add stackpointer (word 224),4)` THEN
  CONV_TAC NUM_REDUCE_CONV THEN

  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_ADD_TWICE4_TAC 2 ["t1"; "x_3"; "w_3"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t2"; "x_3"; "w_3"] THEN

  (*** The inlining of modular inverse ***)

  X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (5--6) THEN
  LOCAL_MODINV_TAC 7 THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP(MESON[PRIME_COPRIME_EQ; PRIME_P25519]
   `(bnx = if p_25519 divides n then 0 else inverse_mod p_25519 n)
    ==> coprime(p_25519,n) ==> bnx = inverse_mod p_25519 n`)) THEN
  ABBREV_TAC
   `t0 =
    read(memory :> bytes(word_add stackpointer (word 256),8 * 4)) s7` THEN

  (*** Final multiplication ***)

  LOCAL_MUL_P25519_TAC 1 ["resx"; "t1"; "t0"] THEN

  (*** Basic mathematics mapping things to curve25519 ***)

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOD_UNIQUE; PUREX25519_BOUND] THEN
  REWRITE_TAC[num_congruent; GSYM INT_REM_EQ] THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_25519`; `nn:num`; `9`; `C_25519`]
    PUREX25519) THEN
  REWRITE_TAC[CURVE25519X_CURVE25519_GROUP] THEN ANTS_TAC THENL
   [REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_CURVE25519] THEN
    REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    REWRITE_TAC[INTEGER_MOD_RING_CHAR; C_25519; montgomery_xmap] THEN
    REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; p_25519] THEN
    CONV_TAC INT_REDUCE_CONV;
    REWRITE_TAC[INTEGER_MOD_RING_OF_NUM] THEN
    DISCH_THEN(SUBST1_TAC o SYM)] THEN

  SUBGOAL_THEN
   `group_pow curve25519_group C_25519 nn =
    curve25519_of_edwards25519
     (group_pow edwards25519_group E_25519 nn)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EDWARDS25519_OF_CURVE25519_C25519] THEN
    MP_TAC GROUP_ISOMORPHISMS_EDWARDS25519_CURVE25519 THEN
    REWRITE_TAC[group_isomorphisms] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_POW) STRIP_ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [group_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[GENERATOR_IN_GROUP_CARRIER_CURVE25519];
    ALL_TAC] THEN

  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [edwards25519_exprojective2]) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[edwards25519_exprojective] THEN

  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NO_TAC; DISCH_TAC]) THEN

  DISCH_TAC THEN REWRITE_TAC[exprojective] THEN
  MP_TAC(SPEC `nn:num`
   (MATCH_MP GROUP_POW GENERATOR_IN_GROUP_CARRIER_EDWARDS25519)) THEN
  SPEC_TAC(`group_pow edwards25519_group E_25519 nn`,`P:int#int`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`xint:int`; `yint:int`] THEN
  SIMP_TAC[EXPROJECTIVE_ALT; FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[curve25519_of_edwards25519; montgomery_of_edwards] THEN
  REWRITE_TAC[EDWARDS25519_GROUP] THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
  REWRITE_TAC[edwards_curve; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[p_25519] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM p_25519; GSYM CONJ_ASSOC] THEN
  GEN_REWRITE_TAC I [TAUT
   `p /\ p' /\ q /\ q' ==> r <=> p ==> q ==> p' /\ q' ==> r`] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`yint:int`; `xint:int`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; GSYM INT_FORALL_POS] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
  REWRITE_TAC[PAIR_EQ; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  REWRITE_TAC[LE_0; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM p_25519] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM CONG] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
   `(e * x + y == 1 + d * x * y) (mod p)
    ==> ((x == 0) (mod p) ==> (y == 1) (mod p)) /\
        ((y == 1) (mod p) ==> (d * x == e * x) (mod p))`)) THEN

  (*** Naive case-splits for degenerate cases, which in fact never happen ***)

  ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_THEN `x = 0` SUBST1_TAC THEN
    REWRITE_TAC[EXP_ZERO; ARITH_EQ; CONG_REFL] THEN
    MP_TAC(SPECL [`p_25519`; `1`; `y:num`] CONG_SQUARE_1_PRIME_POWER) THEN
    REWRITE_TAC[PRIME_P25519] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_25519; ARITH_EQ]; REWRITE_TAC[EXP_1]] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ASM_SIMP_TAC[CONG; MOD_LT] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[montgomery_xmap] THEN
    REWRITE_TAC[GSYM p_25519; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[MULT_CLAUSES; MOD_0] THEN
    (ASM_CASES_TAC `X MOD p_25519 = 0` THEN ASM_REWRITE_TAC[]) THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM DIVIDES_MOD] THEN
    DISCH_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[GSYM CONG] THEN DISCH_THEN(MP_TAC o MATCH_MP(NUMBER_RULE
     `(W * Z == X * Y) (mod p)
      ==> p divides X /\ coprime(p,Z) ==> (X + W == 0) (mod p)`)) THEN
    ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `(y == x + w) (mod p) ==> (x + w == 0) (mod p) ==> p divides y * y'`) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[montgomery_xmap]] THEN

  ASM_CASES_TAC `y = 1` THENL
   [UNDISCH_THEN `y = 1` SUBST1_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[EXP_ONE; CONG_REFL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `(d * x:num == e * x) (mod p)
      ==> coprime(p,x) ==> (d == e) (mod p)`)) THEN
    SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519; PRIME_DIVEXP_EQ] THEN
    ASM_SIMP_TAC[DIVIDES_MOD; MOD_LT] THEN
    REWRITE_TAC[CONG; d_25519; e_25519; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN(K ALL_TAC) THEN STRIP_TAC] THEN

  SUBGOAL_THEN
   `!f x y z:int.
        field f /\
        x IN ring_carrier f /\ y IN ring_carrier f /\ z IN ring_carrier f /\
        ring_mul f y z = x /\ ~(y = ring_0 f)
              ==> z = ring_div f x y`
  MATCH_MP_TAC THENL [POP_ASSUM_LIST(K ALL_TAC) THEN FIELD_TAC; ALL_TAC] THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  REWRITE_TAC[p_25519] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM p_25519; INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ_0; INT_REM_EQ] THEN
  REWRITE_TAC[INTEGER_RULE `p divides x - y <=> (y:int == x) (mod p)`] THEN
  REWRITE_TAC[GSYM INT_REM_EQ; p_25519] THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[GSYM p_25519] THEN
  ASM_SIMP_TAC[MOD_LT; INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INT_REM_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONG; GSYM DIVIDES_MOD]) THEN

  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  MATCH_MP_TAC(TAUT `p /\ (p /\ q ==> r) ==> (p ==> q) ==> r`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519] THEN REWRITE_TAC[num_divides] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INT_CONG_DIVIDES) THEN
    REWRITE_TAC[GSYM INT_CONG; GSYM num_congruent] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
     `(W * Z == X * Y) (mod p) ==> (X == W) (mod p) /\ coprime(p,X)
      ==> (Z:num == Y) (mod p)`)) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
       `(x * Z:num == X) (mod p)
        ==> coprime(p,x) /\ coprime(p,Z) ==> coprime(p,X)`)) THEN
      ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519] THEN
      ASM_SIMP_TAC[DIVIDES_MOD; MOD_LT];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
       `(y * Z == Y) (mod p)
        ==> coprime(p,Z) /\ (Z == Y) (mod p) ==> (y == 1) (mod p)`)) THEN
      ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519] THEN
      ASM_SIMP_TAC[CONG; MOD_LT] THEN REWRITE_TAC[p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[INVERSE_MOD_RMUL]
     `coprime(p,x) /\ y = inverse_mod p x ==> (x * y == 1) (mod p)`))] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_congruent])) THEN
  UNDISCH_TAC `(&t2:int == &X - &W) (mod &p_25519)` THEN
  UNDISCH_TAC `~(p_25519 divides Z)` THEN
  ASM_SIMP_TAC[GSYM PRIME_COPRIME_EQ; PRIME_P25519] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; num_congruent; num_coprime] THEN
  CONV_TAC INTEGER_RULE);;

let CURVE25519_X25519BASE_NOIBT_SUBROUTINE_CORRECT = time prove
 (`!tables res scalar n pc stackpointer returnaddress.
    riprel32_within_bounds tables (pc + 84) /\
    ALL (nonoverlapping (word_sub stackpointer (word 536),536))
        [(word pc,0x2e74); (word tables,48576); (scalar,32)] /\
    ALL (nonoverlapping (res,32))
        [(word pc,0x2e74); (word tables,48576);
         (word_sub stackpointer (word 536),544)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
                (curve25519_x25519base_tmc pc tables) /\
              read RIP s = word pc /\
              bytes_loaded s (word tables)
                curve25519_x25519base_constant_data /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [res; scalar] s /\
              bignum_from_memory (scalar,4) s = n)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              bignum_from_memory (res,4) s = rfcx25519(n,9))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(res,32);
                     memory :> bytes(word_sub stackpointer (word 536),536)])`,
  REWRITE_TAC[BYTES_LOADED_DATA; fst CURVE25519_X25519BASE_EXEC] THEN
  X86_ADD_RETURN_STACK_TAC CURVE25519_X25519BASE_EXEC
   (REWRITE_RULE[BYTES_LOADED_DATA; fst CURVE25519_X25519BASE_EXEC]
    CURVE25519_X25519BASE_CORRECT)
    `[RBX; RBP; R12; R13; R14; R15]` 536);;

(* Bridge equation relating the IBT mc to the trimmed mc: mc pc tables =
   APPEND [endbr64] (tmc (pc+4) tables). Used for ADD_IBT_RULE-style
   transformations on parametrized mcs. *)
let CURVE25519_X25519BASE_MC_BRIDGE = prove
 (`!pc tables. curve25519_x25519base_mc pc tables =
     APPEND [word 0xf3:byte; word 0x0f; word 0x1e; word 0xfa]
            (curve25519_x25519base_tmc (pc + 4) tables)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[curve25519_x25519base_mc; curve25519_x25519base_tmc; APPEND] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[INT_ARITH `&pc + &88 = (&pc + &4) + &84:int`]);;

let CURVE25519_X25519BASE_SUBROUTINE_CORRECT = time prove
 (`!tables res scalar n pc stackpointer returnaddress.
    riprel32_within_bounds tables (pc + 88) /\
    ALL (nonoverlapping (word_sub stackpointer (word 536),536))
        [(word pc,0x2e78); (word tables,48576); (scalar,32)] /\
    ALL (nonoverlapping (res,32))
        [(word pc,0x2e78); (word tables,48576);
         (word_sub stackpointer (word 536),544)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
                (curve25519_x25519base_mc pc tables) /\
              read RIP s = word pc /\
              bytes_loaded s (word tables)
                curve25519_x25519base_constant_data /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [res; scalar] s /\
              bignum_from_memory (scalar,4) s = n)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              bignum_from_memory (res,4) s = rfcx25519(n,9))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(res,32);
                     memory :> bytes(word_sub stackpointer (word 536),536)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE ~bridge:(Some CURVE25519_X25519BASE_MC_BRIDGE)
                                CURVE25519_X25519BASE_NOIBT_SUBROUTINE_CORRECT));;

let CURVE25519_X25519BASE_BYTE_NOIBT_SUBROUTINE_CORRECT = prove
 (`!tables res scalar n pc stackpointer returnaddress.
    riprel32_within_bounds tables (pc + 84) /\
    ALL (nonoverlapping (word_sub stackpointer (word 536),536))
        [(word pc,0x2e74); (word tables,48576); (scalar,32)] /\
    ALL (nonoverlapping (res,32))
        [(word pc,0x2e74); (word tables,48576);
         (word_sub stackpointer (word 536),544)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
                (curve25519_x25519base_tmc pc tables) /\
              read RIP s = word pc /\
              bytes_loaded s (word tables)
                curve25519_x25519base_constant_data /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [res; scalar] s /\
              read (memory :> bytes(scalar,32)) s = n)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              read (memory :> bytes(res,32)) s = rfcx25519(n,9))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(res,32);
                     memory :> bytes(word_sub stackpointer (word 536),536)])`,
  REWRITE_TAC[GSYM(CONV_RULE NUM_REDUCE_CONV
   (SPEC `4` BIGNUM_FROM_MEMORY_BYTES))] THEN
  MATCH_ACCEPT_TAC CURVE25519_X25519BASE_NOIBT_SUBROUTINE_CORRECT);;

let CURVE25519_X25519BASE_BYTE_SUBROUTINE_CORRECT = prove
 (`!tables res scalar n pc stackpointer returnaddress.
    riprel32_within_bounds tables (pc + 88) /\
    ALL (nonoverlapping (word_sub stackpointer (word 536),536))
        [(word pc,0x2e78); (word tables,48576); (scalar,32)] /\
    ALL (nonoverlapping (res,32))
        [(word pc,0x2e78); (word tables,48576);
         (word_sub stackpointer (word 536),544)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
                (curve25519_x25519base_mc pc tables) /\
              read RIP s = word pc /\
              bytes_loaded s (word tables)
                curve25519_x25519base_constant_data /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [res; scalar] s /\
              read (memory :> bytes(scalar,32)) s = n)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              read (memory :> bytes(res,32)) s = rfcx25519(n,9))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(res,32);
                     memory :> bytes(word_sub stackpointer (word 536),536)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE ~bridge:(Some CURVE25519_X25519BASE_MC_BRIDGE)
                                CURVE25519_X25519BASE_BYTE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

(* The Windows .obj's .text contains a relocation against .rodata, so it is
   loaded with define_assert_relocs_from_elf rather than define_coda_from_elf.
   The .rodata content is identical to the Linux ABI build, so the WHOLE_READONLY_data
   constant is reused. *)

(* The Windows entry prepends a ~16-byte ABI dispatcher to the Linux ABI body. *)
let curve25519_x25519base_windows_mc,_ =
  define_assert_relocs_from_elf
    "curve25519_x25519base_windows_mc"
    "x86/curve25519/curve25519_x25519base.obj"
    (fun b ADDR -> curve25519_x25519base_body
       [0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
        0x57;                    (* PUSH (% rdi) *)
        0x56;                    (* PUSH (% rsi) *)
        0x48; 0x89; 0xcf;        (* MOV (% rdi) (% rcx) *)
        0x48; 0x89; 0xd6;        (* MOV (% rsi) (% rdx) *)
        0xe8; 0x03; 0x00; 0x00; 0x00;
                                 (* CALL (Imm32 (word 3)) *)
        0x5e;                    (* POP (% rsi) *)
        0x5f;                    (* POP (% rdi) *)
        0xc3]                    (* RET *)
       b ADDR);;

let curve25519_x25519base_windows_tmc =
  define_trimmed "curve25519_x25519base_windows_tmc"
                 curve25519_x25519base_windows_mc;;

(* Bridge equation analogous to CURVE25519_X25519BASE_MC_BRIDGE for the
   Windows mc/tmc pair. Used to apply ADD_IBT_RULE on rodata-aware
   parametrized mcs. *)
let CURVE25519_X25519BASE_WINDOWS_MC_BRIDGE = prove
 (`!pc tables. curve25519_x25519base_windows_mc pc tables =
     APPEND [word 0xf3:byte; word 0x0f; word 0x1e; word 0xfa]
            (curve25519_x25519base_windows_tmc (pc + 4) tables)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[curve25519_x25519base_windows_mc;
              curve25519_x25519base_windows_tmc; APPEND] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[INT_ARITH `&pc + &104 = (&pc + &4) + &100:int`]);;

(* The Windows trimmed mc has length 0x2e84: a 16-byte ABI-translation wrapper
   (PUSH RDI/RSI; MOV RDI<-RCX; MOV RSI<-RDX; CALL +3; POP RSI/RDI; RET) at
   offsets 0..15, then the Linux ABI trimmed body of length 0x2e74 starting at
   pc+0x10. The LEA targeting `tables` is at the same instruction as in the
   Linux ABI body, so the riprel32_within_bounds bound is `tables (pc + 100)`
   for the trimmed mc (since `(pc + 0x10) + 84 = pc + 100`) and `tables (pc + 104)`
   for the IBT mc. *)

let CURVE25519_X25519BASE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!tables res scalar n pc stackpointer returnaddress.
    riprel32_within_bounds tables (pc + 100) /\
    ALL (nonoverlapping (word_sub stackpointer (word 560),560))
        [(word pc,0x2e84); (word tables,48576); (scalar,32)] /\
    ALL (nonoverlapping (res,32))
        [(word pc,0x2e84); (word tables,48576);
         (word_sub stackpointer (word 560),568)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
                (curve25519_x25519base_windows_tmc pc tables) /\
              read RIP s = word pc /\
              bytes_loaded s (word tables)
                curve25519_x25519base_constant_data /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [res; scalar] s /\
              bignum_from_memory (scalar,4) s = n)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              bignum_from_memory (res,4) s = rfcx25519(n,9))
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(res,32);
                     memory :> bytes(word_sub stackpointer (word 560),560)])`,
  let WINDOWS_CURVE25519_X25519BASE_EXEC =
    X86_MK_EXEC_RULE curve25519_x25519base_windows_tmc
  (* Re-derive the Linux ABI subroutine theorem from the explicit-MAYCHANGE form
     of CURVE25519_X25519BASE_CORRECT (no ZMM, no ABI macro). This makes the
     Linux ABI subth's MAYCHANGE small enough that ENSURES_FINAL_STATE_TAC's
     MONOTONE_MAYCHANGE step subsumes the goal's WINDOWS ABI MAYCHANGE
     directly. *)
  and subth =
    REWRITE_RULE[BYTES_LOADED_DATA; BIGNUM_FROM_MEMORY_BYTES; ARITH]
    (X86_SIMD_SHARPEN_RULE CURVE25519_X25519BASE_NOIBT_SUBROUTINE_CORRECT
     (REWRITE_TAC[BYTES_LOADED_DATA; fst CURVE25519_X25519BASE_EXEC] THEN
      X86_ADD_RETURN_STACK_TAC CURVE25519_X25519BASE_EXEC
       (REWRITE_RULE[BYTES_LOADED_DATA; fst CURVE25519_X25519BASE_EXEC]
        CURVE25519_X25519BASE_CORRECT)
       `[RBX; RBP; R12; R13; R14; R15]` 536)) in
  REWRITE_TAC[BYTES_LOADED_DATA] THEN
  REPLICATE_TAC 5 GEN_TAC THEN WORD_FORALL_OFFSET_TAC 560 THEN
  REWRITE_TAC[ALL; WINDOWS_C_ARGUMENTS; SOME_FLAGS;
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC WINDOWS_CURVE25519_X25519BASE_EXEC (1--5) THEN
  X86_SUBROUTINE_SIM_TAC
    (curve25519_x25519base_windows_tmc,
     WINDOWS_CURVE25519_X25519BASE_EXEC,
     0x10,curve25519_x25519base_tmc,subth)
        [`tables:num`; `read RDI s`; `read RSI s`;
         `read (memory :> bytes (read RSI s,8 * 4)) s`;
         `pc + 0x10`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
        6 THENL [
    UNDISCH_TAC `read (memory :> bytes (scalar:int64,8 * 4)) s5 = n` THEN
    REWRITE_TAC[ARITH_RULE `8 * 4 = 32`];
    ALL_TAC] THEN
  X86_STEPS_TAC WINDOWS_CURVE25519_X25519BASE_EXEC (7--9) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 4 = 32`]);;

let CURVE25519_X25519BASE_WINDOWS_SUBROUTINE_CORRECT = time prove
 (`!tables res scalar n pc stackpointer returnaddress.
    riprel32_within_bounds tables (pc + 104) /\
    ALL (nonoverlapping (word_sub stackpointer (word 560),560))
        [(word pc,0x2e88); (word tables,48576); (scalar,32)] /\
    ALL (nonoverlapping (res,32))
        [(word pc,0x2e88); (word tables,48576);
         (word_sub stackpointer (word 560),568)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
                (curve25519_x25519base_windows_mc pc tables) /\
              read RIP s = word pc /\
              bytes_loaded s (word tables)
                curve25519_x25519base_constant_data /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [res; scalar] s /\
              bignum_from_memory (scalar,4) s = n)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              bignum_from_memory (res,4) s = rfcx25519(n,9))
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(res,32);
                     memory :> bytes(word_sub stackpointer (word 560),560)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
                     ~bridge:(Some CURVE25519_X25519BASE_WINDOWS_MC_BRIDGE)
                     CURVE25519_X25519BASE_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

let CURVE25519_X25519BASE_BYTE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!tables res scalar n pc stackpointer returnaddress.
    riprel32_within_bounds tables (pc + 100) /\
    ALL (nonoverlapping (word_sub stackpointer (word 560),560))
        [(word pc,0x2e84); (word tables,48576); (scalar,32)] /\
    ALL (nonoverlapping (res,32))
        [(word pc,0x2e84); (word tables,48576);
         (word_sub stackpointer (word 560),568)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
                (curve25519_x25519base_windows_tmc pc tables) /\
              read RIP s = word pc /\
              bytes_loaded s (word tables)
                curve25519_x25519base_constant_data /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [res; scalar] s /\
              read (memory :> bytes(scalar,32)) s = n)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              read (memory :> bytes(res,32)) s = rfcx25519(n,9))
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(res,32);
                     memory :> bytes(word_sub stackpointer (word 560),560)])`,
  REWRITE_TAC[GSYM(CONV_RULE NUM_REDUCE_CONV
   (SPEC `4` BIGNUM_FROM_MEMORY_BYTES))] THEN
  MATCH_ACCEPT_TAC CURVE25519_X25519BASE_NOIBT_WINDOWS_SUBROUTINE_CORRECT);;

let CURVE25519_X25519BASE_BYTE_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!tables res scalar n pc stackpointer returnaddress.
    riprel32_within_bounds tables (pc + 104) /\
    ALL (nonoverlapping (word_sub stackpointer (word 560),560))
        [(word pc,0x2e88); (word tables,48576); (scalar,32)] /\
    ALL (nonoverlapping (res,32))
        [(word pc,0x2e88); (word tables,48576);
         (word_sub stackpointer (word 560),568)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc)
                (curve25519_x25519base_windows_mc pc tables) /\
              read RIP s = word pc /\
              bytes_loaded s (word tables)
                curve25519_x25519base_constant_data /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              WINDOWS_C_ARGUMENTS [res; scalar] s /\
              read (memory :> bytes(scalar,32)) s = n)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              read (memory :> bytes(res,32)) s = rfcx25519(n,9))
         (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(res,32);
                     memory :> bytes(word_sub stackpointer (word 560),560)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
                     ~bridge:(Some CURVE25519_X25519BASE_WINDOWS_MC_BRIDGE)
                     CURVE25519_X25519BASE_BYTE_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(* The Linux ABI mc trims its 17-byte IBT prologue, so the inner BIGNUM_INV_P25519
   call lands at pc + 0x18b1 (vs. pc + 0x18b4 in pre-rodata where the IBT-mc
   path was used). The H_INV_SAFE callee safety hypothesis (post
   ASSUME_CALLEE_SAFETY_TAILED_TAC) is universally quantified over
   `e z x pc stackpointer e_tail` in that order, so the ilist matches. *)
let LOCAL_MODINV_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
       (curve25519_x25519base_tmc',
        CURVE25519_X25519BASE_EXEC,
        0x18b1,
        (GEN_REWRITE_CONV RAND_CONV [bignum_inv_p25519_tmc] THENC TRIM_LIST_CONV)
        `TRIM_LIST (17,18) bignum_inv_p25519_tmc`,
        safety_th)
        [`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
        `pc + 0x18b1`; `stackpointer:int64`] n
    THENL [
      EXISTS_E2_TAC(ref
        [`scalar:int64`;`point:int64`;`res:int64`;`pc:num`;
         `stackpointer:int64`;`tables:num`;
         (* inside the loop... *)
         `i:num`;
         `f_ev_loop:int64->int64->int64->num->int64->num->num->(uarch_event)list`]);

      LABEL_TAC assump_name safety_th
    ]
  );;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word tables:int64`,`48576`]
    ~keep_maychanges:true
    (assoc "curve25519_x25519base" subroutine_signatures)
    CURVE25519_X25519BASE_CORRECT
    CURVE25519_X25519BASE_EXEC;;

let CURVE25519_X25519BASE_SAFE = time prove
 (`exists f_events.
       forall e tables res scalar pc stackpointer.
           riprel32_within_bounds tables (pc + 84) /\
           ALL (nonoverlapping (stackpointer,488))
           [word pc,0x2e74; word tables,48576; res,32; scalar,32] /\
           nonoverlapping (res,32) (word pc,0x2e74)
           ==> ensures x86
               (\s.
                    bytes_loaded s (word pc)
                      (curve25519_x25519base_tmc pc tables) /\
                    read RIP s = word (pc + 17) /\
                    bytes_loaded s (word tables)
                      curve25519_x25519base_constant_data /\
                    read RSP s = stackpointer /\
                    C_ARGUMENTS [res; scalar] s /\
                    read events s = e)
               (\s.
                    read RIP s = word (pc + 11874) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events scalar res tables pc stackpointer /\
                         memaccess_inbounds e2
                         [scalar,32; res,32; stackpointer,488;
                          word tables,48576]
                         [res,32; stackpointer,488]))
               (MAYCHANGE
                [RIP; RDI; RSI; RAX; RBX; RCX; RDX; RBP; R8; R9; R10; R11;
                 R12; R13; R14; R15] ,,
                MAYCHANGE SOME_FLAGS ,,
                MAYCHANGE [events] ,,
                MAYCHANGE
                [memory :> bytes (res,32); memory :> bytes (stackpointer,488)])`,
  (* Prepare the safety theorem of subroutine to be used; this keeps
     introduction of metavariables in the right order. *)
  ASSUME_CALLEE_SAFETY_TAILED_TAC CORE_INV_P25519_SAFE
      "H_INV_SAFE" THEN

  CONCRETIZE_F_EVENTS_TAC
    `\(scalar:int64) (res:int64) (tables:num) (pc:num) (stackpointer:int64).
      APPEND
        (f_ev_epil scalar res tables pc stackpointer)
        (APPEND
          (ENUMERATEL 63 (\i.
            f_ev_loop scalar res tables pc stackpointer i))
          (f_ev_prol scalar res tables pc stackpointer))
    :(uarch_event)list` THEN

  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN

  REWRITE_TAC[BYTES_LOADED_DATA] THEN

  (*** Setup of the main loop ***)

  (* Loop entry pc + 0x197 (=407), loop exit pc + 0x17a1 (=6049) per the
     CORRECT proof. UP2 takes the loop-end address + 2 insns, since it
     unrolls the 0..63 body once before terminating. The pre-rodata mc had
     the same loop-body layout but at +3 byte offset because of the
     embedded 4-byte LEA displacement vs the rodata-resolved version. *)
  ENSURES_EVENTS_WHILE_UP2_TAC `63` `pc + 0x197` `pc + 0x17b3`(*+2 insns *)
   `\i s.
      read (memory :> bytes(word tables,48576)) s =
          num_of_bytelist curve25519_x25519base_constant_data /\
      read RSP s = stackpointer /\
      read (memory :> bytes64 (word_add stackpointer (word 448))) s = res /\
      read (memory :> bytes64 (word_add stackpointer (word 480))) s =
          word(tables + 0xc0 + 768 * i) /\
      read (memory :> bytes64 (word_add stackpointer (word 456))) s =
          word (4 * (i+1))` THEN
  REPEAT CONJ_TAC THENL [
    ARITH_TAC;

    (*** Initial setup and modification of the inputs ***)

    ENSURES_INIT_TAC "s0" THEN

    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (1--14) THEN

    (*** Fold the rip-relative LEA results so `read R10 s = word tables`
         and `read R11 s = word_add (word tables) (word 96)`. ***)

    UNDISCH_TAC `read R10 s14 =
        word(val (word (pc + 84):(64)word) +
             val (word_sx (iword (&tables - (&pc + &84)):int32):(64)word):num)` THEN
    IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `read R11 s14 =
        word_add
        (word (val (word (pc + 84):(64)word) +
               val (word_sx (iword (&tables - (&pc + &84)):int32):(64)word):num))
        (word 96)` THEN
    IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (15--72) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONJ_TAC THENL [WORD_ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The main loop invariant for adding the next table entry ***)

    REPEAT STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (1--239) THEN
    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (240--
      (239+(19(*DOUBLE_TWICE4*) + 19(*SUB_TWICE4*) + 19(*ADD_TWICE4*) +
            82(*MUL_4*) + 82(*MUL_4*) + 82(*MUL_4*) + 19(*SUB_TWICE4*) +
            19(*ADD_TWICE4*) + 19(*SUB_TWICE4*) + 19(*ADD_TWICE4*) +
            82(*MUL_4*) + 82(*MUL_4*) + 82(*MUL_4*) + 82(*MUL_4*)))) THEN
    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (947--947) THEN
    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (948--989) THEN
    X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (990--991) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[VAL_WORD_ADD] THEN
      MAP_EVERY VAL_INT64_TAC [`4*(i+1)`;`4`] THEN
      ASM_REWRITE_TAC[DIMINDEX_64] THEN
      ONCE_REWRITE_TAC[GSYM COND_RAND] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN
      SIMPLE_ARITH_TAC;

      ALL_TAC
    ] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE;ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE;ALL_TAC] THEN

    (* Found this pattern from safety_print_log := true *)
    SUBGOAL_THEN
      `word (8 * val (word_ushr (word (4 * (i + 1)):int64) 6))
      :int64 = word (8 * (4 * (i + 1)) DIV 2 EXP 6)`
    SUBST_ALL_TAC THENL [
      AP_TERM_TAC THEN REWRITE_TAC[VAL_WORD_USHR] THEN
      IMP_REWRITE_TAC[VAL_WORD;MOD_LT;DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      ALL_TAC
    ] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC] THEN

  (*** Clean up ready for the final translation part ***)

  ENSURES_INIT_TAC "s0" THEN
  STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (1--
      (19(*ADD_TWICE4*) + 19(*SUB_TWICE4*))) THEN
  X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (39--40) THEN
  LOCAL_MODINV_SAFETY_TAC "H_INV_SAFE" 41 THEN
  X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (42--(41+91)) THEN

  X86_STEPS_TAC CURVE25519_X25519BASE_EXEC (133--133) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  SUBST_ALL_TAC (ARITH_RULE`2 EXP 6 = 64`) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let CURVE25519_X25519BASE_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e tables res scalar pc stackpointer returnaddress.
        riprel32_within_bounds tables (pc + 84) /\
        ALL (nonoverlapping (word_sub stackpointer (word 536),536))
        [word pc,0x2e74; word tables,48576; scalar,32] /\
        nonoverlapping (res,32) (word pc,0x2e74) /\
        nonoverlapping (res,32) (word_sub stackpointer (word 536),544)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc)
                   (curve25519_x25519base_tmc pc tables) /\
                 read RIP s = word pc /\
                 bytes_loaded s (word tables)
                   curve25519_x25519base_constant_data /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [res; scalar] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events scalar res tables pc
                      (word_sub stackpointer (word 536))
                      returnaddress /\
                      memaccess_inbounds e2
                      [scalar,32; res,32;
                       word_sub stackpointer (word 536),544;
                       word tables,48576]
                      [res,32; word_sub stackpointer (word 536),536]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bytes (res,32);
              memory :> bytes (word_sub stackpointer (word 536),536)])`,
  REWRITE_TAC[BYTES_LOADED_DATA; fst CURVE25519_X25519BASE_EXEC] THEN
  X86_ADD_RETURN_STACK_TAC CURVE25519_X25519BASE_EXEC
   (REWRITE_RULE[BYTES_LOADED_DATA; fst CURVE25519_X25519BASE_EXEC]
    CURVE25519_X25519BASE_SAFE)
    `[RBX; RBP; R12; R13; R14; R15]` 536
  THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let CURVE25519_X25519BASE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e tables res scalar pc stackpointer returnaddress.
        riprel32_within_bounds tables (pc + 88) /\
        ALL (nonoverlapping (word_sub stackpointer (word 536),536))
        [word pc,0x2e78; word tables,48576; scalar,32] /\
        nonoverlapping (res,32) (word pc,0x2e78) /\
        nonoverlapping (res,32) (word_sub stackpointer (word 536),544)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc)
                   (curve25519_x25519base_mc pc tables) /\
                 read RIP s = word pc /\
                 bytes_loaded s (word tables)
                   curve25519_x25519base_constant_data /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [res; scalar] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events scalar res tables pc
                          (word_sub stackpointer (word 536))
                          returnaddress /\
                      memaccess_inbounds e2
                          [scalar,32; res,32;
                           word_sub stackpointer (word 536),544;
                           word tables,48576]
                          [res,32; word_sub stackpointer (word 536),536]))
            (MAYCHANGE [RSP] ,,
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bytes (res,32);
              memory :> bytes (word_sub stackpointer (word 536),536)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
                     ~bridge:(Some CURVE25519_X25519BASE_MC_BRIDGE)
                     CURVE25519_X25519BASE_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let CURVE25519_X25519BASE_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e tables res scalar pc stackpointer returnaddress.
        riprel32_within_bounds tables (pc + 100) /\
        ALL (nonoverlapping (word_sub stackpointer (word 560),560))
        [word pc,0x2e84; word tables,48576; scalar,32] /\
        nonoverlapping (res,32) (word pc,0x2e84) /\
        nonoverlapping (res,32) (word_sub stackpointer (word 560),568)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc)
                   (curve25519_x25519base_windows_tmc pc tables) /\
                 read RIP s = word pc /\
                 bytes_loaded s (word tables)
                   curve25519_x25519base_constant_data /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [res; scalar] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events scalar res tables pc
                      (word_sub stackpointer (word 560))
                      returnaddress /\
                      memaccess_inbounds e2
                      [scalar,32; res,32;
                       word_sub stackpointer (word 560),568;
                       word tables,48576]
                      [res,32; word_sub stackpointer (word 560),560]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bytes (res,32);
              memory :> bytes (word_sub stackpointer (word 560),560)])`,
  let WINDOWS_CURVE25519_X25519BASE_EXEC =
    X86_MK_EXEC_RULE curve25519_x25519base_windows_tmc
  (* Re-derive the Linux ABI SUBROUTINE_SAFE theorem with explicit MAYCHANGE
     small enough that ENSURES_FINAL_STATE_TAC's MONOTONE_MAYCHANGE step
     subsumes the Windows ABI MAYCHANGE directly. *)
  and subth =
    REWRITE_RULE[BYTES_LOADED_DATA; fst CURVE25519_X25519BASE_EXEC]
    (X86_SIMD_SHARPEN_RULE CURVE25519_X25519BASE_NOIBT_SUBROUTINE_SAFE
     (REWRITE_TAC[BYTES_LOADED_DATA; fst CURVE25519_X25519BASE_EXEC] THEN
      X86_ADD_RETURN_STACK_TAC CURVE25519_X25519BASE_EXEC
       (REWRITE_RULE[BYTES_LOADED_DATA; fst CURVE25519_X25519BASE_EXEC]
        CURVE25519_X25519BASE_SAFE)
       `[RBX; RBP; R12; R13; R14; R15]` 536 THEN
      DISCHARGE_SAFETY_PROPERTY_TAC)) in
  ASSUME_CALLEE_SAFETY_TAILED_TAC subth "H_CALLEE" THEN
  META_EXISTS_TAC THEN GEN_TAC THEN

  REWRITE_TAC[BYTES_LOADED_DATA] THEN
  REPLICATE_TAC 4 GEN_TAC THEN WORD_FORALL_OFFSET_TAC 560 THEN
  REWRITE_TAC[ALL; WINDOWS_C_ARGUMENTS; SOME_FLAGS;
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC WINDOWS_CURVE25519_X25519BASE_EXEC (1--5) THEN
  REMOVE_THEN "H_CALLEE" (fun subth ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (curve25519_x25519base_windows_tmc,
      WINDOWS_CURVE25519_X25519BASE_EXEC,
      0x10,curve25519_x25519base_tmc,subth)
          (* H_CALLEE quantifier order (from ASSUME_CALLEE_SAFETY_TAILED_TAC):
             [e; tables; res; scalar; pc; stackpointer; returnaddress; e_tail].
             SPECL the leading 7; e_tail is left as a metavariable bound by
             META_EXISTS_TAC inside X86_SUBROUTINE_SIM_TAC. *)
          [`e:(uarch_event)list`; `tables:num`;
           `read RDI s`; `read RSI s`;
          `pc + 0x10`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
          6) THENL [
    EXISTS_E2_TAC(ref
      [`tables:num`;`pc:num`;`stackpointer:int64`]);

    ALL_TAC
  ] THEN
  X86_STEPS_TAC WINDOWS_CURVE25519_X25519BASE_EXEC (7--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let CURVE25519_X25519BASE_WINDOWS_SUBROUTINE_SAFE = time prove
 (`exists f_events.
    forall e tables res scalar pc stackpointer returnaddress.
        riprel32_within_bounds tables (pc + 104) /\
        ALL (nonoverlapping (word_sub stackpointer (word 560),560))
        [word pc,0x2e88; word tables,48576; scalar,32] /\
        nonoverlapping (res,32) (word pc,0x2e88) /\
        nonoverlapping (res,32) (word_sub stackpointer (word 560),568)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc)
                   (curve25519_x25519base_windows_mc pc tables) /\
                 read RIP s = word pc /\
                 bytes_loaded s (word tables)
                   curve25519_x25519base_constant_data /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [res; scalar] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events scalar res tables pc
                        (word_sub stackpointer (word 560))
                        returnaddress /\
                      memaccess_inbounds e2
                        [scalar,32; res,32;
                         word_sub stackpointer (word 560),568;
                         word tables,48576]
                        [res,32; word_sub stackpointer (word 560),560]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bytes (res,32);
              memory :> bytes (word_sub stackpointer (word 560),560)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
                     ~bridge:(Some CURVE25519_X25519BASE_WINDOWS_MC_BRIDGE)
                     CURVE25519_X25519BASE_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
