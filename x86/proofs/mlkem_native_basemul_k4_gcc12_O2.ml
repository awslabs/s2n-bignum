(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of vectors of polynomials in NTT form for k = 4.           *)
(* This is the code for mlkem1024_polyvec_basemul_acc_montgomery_cached from *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mlkem_native/README.md).                                             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;

(**** print_literal_from_elf
        "x86/mlkem_native/mlkem_native_basemul_k4_gcc12_O2.o";;
 ****)

let mlkem_native_basemul_k4_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_basemul_k4_gcc12_O2_mc"
  "x86/mlkem_native/mlkem_native_basemul_k4_gcc12_O2.o"
[
  0x41; 0x57;              (* PUSH (% r15) *)
  0x49; 0x89; 0xf9;        (* MOV (% r9) (% rdi) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0x48; 0x8d; 0x7a; 0x02;  (* LEA (% rdi) (%% (rdx,2)) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x49; 0x89; 0xf0;        (* MOV (% r8) (% rsi) *)
  0x49; 0x8d; 0x51; 0x02;  (* LEA (% rdx) (%% (r9,2)) *)
  0x4c; 0x8d; 0xb1; 0x00; 0x01; 0x00; 0x00;
                           (* LEA (% r14) (%% (rcx,256)) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x66; 0x0f; 0x1f; 0x44; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x49; 0x89; 0xc2;        (* MOV (% r10) (% rax) *)
  0x45; 0x31; 0xc9;        (* XOR (% r9d) (% r9d) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x49; 0x8d; 0x58; 0x02;  (* LEA (% rbx) (%% (r8,2)) *)
  0x4c; 0x8d; 0x5f; 0xfe;  (* LEA (% r11) (%% (rdi,18446744073709551614)) *)
  0x46; 0x0f; 0xbf; 0x3c; 0x0b;
                           (* MOVSX (% r15d) (Memop Word (%%% (rbx,0,r9))) *)
  0x41; 0x0f; 0xbf; 0x2a;  (* MOVSX (% ebp) (Memop Word (%% (r10,0))) *)
  0x49; 0x81; 0xc2; 0x00; 0x01; 0x00; 0x00;
                           (* ADD (% r10) (Imm32 (word 256)) *)
  0x47; 0x0f; 0xbf; 0x2c; 0x08;
                           (* MOVSX (% r13d) (Memop Word (%%% (r8,0,r9))) *)
  0x44; 0x89; 0x7c; 0x24; 0xfc;
                           (* MOV (Memop Doubleword (%%
                                  (rsp,18446744073709551612))) (% r15d) *)
  0x44; 0x8b; 0x64; 0x24; 0xfc;
                           (* MOV (% r12d) (Memop Doubleword (%%
                                  (rsp,18446744073709551612))) *)
  0x47; 0x0f; 0xbf; 0x3c; 0x0b;
                           (* MOVSX (% r15d) (Memop Word (%%% (r11,0,r9))) *)
  0x41; 0x0f; 0xaf; 0xec;  (* IMUL (% ebp) (% r12d) *)
  0x41; 0x89; 0xec;        (* MOV (% r12d) (% ebp) *)
  0x44; 0x89; 0xed;        (* MOV (% ebp) (% r13d) *)
  0x41; 0x0f; 0xaf; 0xef;  (* IMUL (% ebp) (% r15d) *)
  0x41; 0x01; 0xec;        (* ADD (% r12d) (% ebp) *)
  0x42; 0x0f; 0xbf; 0x2c; 0x0f;
                           (* MOVSX (% ebp) (Memop Word (%%% (rdi,0,r9))) *)
  0x49; 0x81; 0xc1; 0x00; 0x02; 0x00; 0x00;
                           (* ADD (% r9) (Imm32 (word 512)) *)
  0x44; 0x01; 0xe1;        (* ADD (% ecx) (% r12d) *)
  0x44; 0x8b; 0x64; 0x24; 0xfc;
                           (* MOV (% r12d) (Memop Doubleword (%%
                                  (rsp,18446744073709551612))) *)
  0x41; 0x0f; 0xaf; 0xed;  (* IMUL (% ebp) (% r13d) *)
  0x45; 0x0f; 0xaf; 0xe7;  (* IMUL (% r12d) (% r15d) *)
  0x44; 0x01; 0xe5;        (* ADD (% ebp) (% r12d) *)
  0x01; 0xee;              (* ADD (% esi) (% ebp) *)
  0x49; 0x81; 0xf9; 0x00; 0x08; 0x00; 0x00;
                           (* CMP (% r9) (Imm32 (word 2048)) *)
  0x75; 0xa1;              (* JNE (Imm8 (word 161)) *)
  0x48; 0x83; 0xc0; 0x02;  (* ADD (% rax) (Imm8 (word 2)) *)
  0x49; 0x83; 0xc0; 0x04;  (* ADD (% r8) (Imm8 (word 4)) *)
  0x48; 0x83; 0xc7; 0x04;  (* ADD (% rdi) (Imm8 (word 4)) *)
  0x48; 0x83; 0xc2; 0x04;  (* ADD (% rdx) (Imm8 (word 4)) *)
  0x66; 0x44; 0x69; 0xc9; 0x01; 0xf3;
                           (* IMUL3 (% r9w) (% cx,Imm16 (word 62209)) *)
  0x45; 0x0f; 0xbf; 0xc9;  (* MOVSX (% r9d) (% r9w) *)
  0x45; 0x69; 0xc9; 0xff; 0xf2; 0xff; 0xff;
                           (* IMUL3 (% r9d) (% r9d,Imm32 (word 4294963967)) *)
  0x44; 0x01; 0xc9;        (* ADD (% ecx) (% r9d) *)
  0xc1; 0xf9; 0x10;        (* SAR (% ecx) (Imm8 (word 16)) *)
  0x66; 0x89; 0x4a; 0xfa;  (* MOV (Memop Word (%% (rdx,18446744073709551610)))
                                  (% cx) *)
  0x66; 0x69; 0xce; 0x01; 0xf3;
                           (* IMUL3 (% cx) (% si,Imm16 (word 62209)) *)
  0x0f; 0xbf; 0xc9;        (* MOVSX (% ecx) (% cx) *)
  0x69; 0xc9; 0xff; 0xf2; 0xff; 0xff;
                           (* IMUL3 (% ecx) (% ecx,Imm32 (word 4294963967)) *)
  0x01; 0xf1;              (* ADD (% ecx) (% esi) *)
  0xc1; 0xf9; 0x10;        (* SAR (% ecx) (Imm8 (word 16)) *)
  0x66; 0x89; 0x4a; 0xfc;  (* MOV (Memop Word (%% (rdx,18446744073709551612)))
                                  (% cx) *)
  0x49; 0x39; 0xc6;        (* CMP (% r14) (% rax) *)
  0x0f; 0x85; 0x44; 0xff; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294967108)) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0xc3                     (* RET *)
];;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_basemul_k4_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* Definitions used to state specification, as for mlkem_basemul_k4.         *)
(* ------------------------------------------------------------------------- *)

let pmull = define
  `pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;

let pmull_acc4 = define
  `pmull_acc4 (x00: int) (x01 : int) (y00 : int) (y01 : int)
              (x10: int) (x11 : int) (y10 : int) (y11 : int)
              (x20: int) (x21 : int) (y20 : int) (y21 : int)
              (x30: int) (x31 : int) (y30 : int) (y31 : int) =
              pmull x30 x31 y30 y31 + pmull x20 x21 y20 y21 +
              pmull x10 x11 y10 y11 + pmull x00 x01 y00 y01`;;

let pmul_acc4 = define
  `pmul_acc4 (x00: int) (x01 : int) (y00 : int) (y01 : int)
             (x10: int) (x11 : int) (y10 : int) (y11 : int)
             (x20: int) (x21 : int) (y20 : int) (y21 : int)
             (x30: int) (x31 : int) (y30 : int) (y31 : int) =
             (&(inverse_mod 3329 65536) *
    pmull_acc4 x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21
               x30 x31 y30 y31) rem &3329`;;

let basemul4_even = define
 `basemul4_even x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t = \i.
    pmul_acc4 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i)) (y0t i)
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i)) (y1t i)
              (x2 (2 * i)) (x2 (2 * i + 1))
              (y2 (2 * i)) (y2t i)
              (x3 (2 * i)) (x3 (2 * i + 1))
              (y3 (2 * i)) (y3t i)`;;

let basemul4_odd = define
 `basemul4_odd x0 y0 x1 y1 x2 y2 x3 y3 = \i.
  pmul_acc4 (x0 (2 * i)) (x0 (2 * i + 1))
            (y0 (2 * i + 1)) (y0 (2 * i))
            (x1 (2 * i)) (x1 (2 * i + 1))
            (y1 (2 * i + 1)) (y1 (2 * i))
            (x2 (2 * i)) (x2 (2 * i + 1))
            (y2 (2 * i + 1)) (y2 (2 * i))
            (x3 (2 * i)) (x3 (2 * i + 1))
            (y3 (2 * i + 1)) (y3 (2 * i))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** Instantiate the input facts at the addresses that the loads use. The
 *** inner loop over the four polynomials indexes them with R9 = 0, 512,
 *** 1024 and 1536, and the simulator folds this into the offset in two
 *** ways.
 ***)

let BASEMUL_READ_TAC =
  MAP_EVERY READ_INSTANCE_TAC
   [`read (memory :> bytes16 (word_add srcA (word (4 * i)))) s0 =
     x0(2 * i)`;
    `read (memory :> bytes16
           (word_add (word_add srcA (word (4 * i))) (word 2))) s0 =
     x0(2 * i + 1)`;
    `read (memory :> bytes16 (word_add srcB (word (4 * i)))) s0 =
     y0(2 * i)`;
    `read (memory :> bytes16
           (word_add (word_add srcB (word (4 * i))) (word 2))) s0 =
     y0(2 * i + 1)`;
    `read (memory :> bytes16 (word_add srcBt (word (2 * i)))) s0 =
     y0t i`;
    `read (memory :> bytes16 (word_add srcA (word (4 * i + 512)))) s0 =
     x1(2 * i)`;
    `read (memory :> bytes16
           (word_add (word_add srcA (word (4 * i))) (word 514))) s0 =
     x1(2 * i + 1)`;
    `read (memory :> bytes16 (word_add srcB (word (4 * i + 512)))) s0 =
     y1(2 * i)`;
    `read (memory :> bytes16
           (word_add (word_add srcB (word (4 * i))) (word 514))) s0 =
     y1(2 * i + 1)`;
    `read (memory :> bytes16
           (word_add (word_add srcBt (word (2 * i))) (word 256))) s0 =
     y1t i`;
    `read (memory :> bytes16 (word_add srcA (word (4 * i + 1024)))) s0 =
     x2(2 * i)`;
    `read (memory :> bytes16
           (word_add (word_add srcA (word (4 * i))) (word 1026))) s0 =
     x2(2 * i + 1)`;
    `read (memory :> bytes16 (word_add srcB (word (4 * i + 1024)))) s0 =
     y2(2 * i)`;
    `read (memory :> bytes16
           (word_add (word_add srcB (word (4 * i))) (word 1026))) s0 =
     y2(2 * i + 1)`;
    `read (memory :> bytes16
           (word_add (word_add srcBt (word (2 * i))) (word 512))) s0 =
     y2t i`;
    `read (memory :> bytes16 (word_add srcA (word (4 * i + 1536)))) s0 =
     x3(2 * i)`;
    `read (memory :> bytes16
           (word_add (word_add srcA (word (4 * i))) (word 1538))) s0 =
     x3(2 * i + 1)`;
    `read (memory :> bytes16 (word_add srcB (word (4 * i + 1536)))) s0 =
     y3(2 * i)`;
    `read (memory :> bytes16
           (word_add (word_add srcB (word (4 * i))) (word 1538))) s0 =
     y3(2 * i + 1)`;
    `read (memory :> bytes16
           (word_add (word_add srcBt (word (2 * i))) (word 768))) s0 =
     y3t i`];;

let BASEMUL_CONG_TAC =
  ASSUM_LIST(fun ths -> W(fun (asl,w) ->
    let tm = rand(rand(lhand(rator w))) in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE ths tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2)))) in
    MP_TAC(CONJUNCT1 th3))) THEN
  REWRITE_TAC[basemul4_even; basemul4_odd;
              pmul_acc4; pmull_acc4; pmull; o_THM] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING;;

(*** The function saves RBX, RBP and R12-R15 and uses them as temporaries.
 *** Since the saves are interleaved with other setup, the core proof starts
 *** after them, with the registers that setup has assigned. The core also
 *** spills a 32-bit value to the red zone just below the stack pointer, and
 *** its "stackpointer" parameter is the address of that 4-byte slot.
 ***)

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t pc
    stackpointer.
     ALL (nonoverlapping (dst, 512))
         [(word pc, 0xef); (srcA, 2048); (srcB, 2048); (srcBt, 1024);
          (stackpointer, 4)] /\
     ALL (nonoverlapping (stackpointer, 4))
         [(word pc, 0xef); (srcA, 2048); (srcB, 2048); (srcBt, 1024)]
     ==>
     ensures x86
       (\s. bytes_loaded s (word pc) mlkem_native_basemul_k4_gcc12_O2_mc /\
            read RIP s = word (pc + 0x28) /\
            read RAX s = srcBt /\ read R8 s = srcA /\
            read RDI s = word_add srcB (word 2) /\
            read RDX s = word_add dst (word 2) /\
            read R14 s = word_add srcBt (word 256) /\
            read RSP s = word_add stackpointer (word 4) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (2 * i)))) s = y0 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (2 * i)))) s = y0t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1536 + 2 * i)))) s = x3 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1536 + 2 * i)))) s = y3 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (768 + 2 * i)))) s = y3t i))
       (\s. read RIP s = word (pc + 0xe4) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                      abs(ival(x1 i)) <= &2 pow 12 /\
                      abs(ival(x2 i)) <= &2 pow 12 /\
                      abs(ival(x3 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul4_even
                            (ival o x0) (ival o y0) (ival o y0t)
                            (ival o x1) (ival o y1) (ival o y1t)
                            (ival o x2) (ival o y2) (ival o y2t)
                            (ival o x3) (ival o y3) (ival o y3t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul4_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2) (ival o x3) (ival o y3)
                            i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [RBX; RBP; R12; R13; R15] ,,
        MAYCHANGE [memory :> bytes(dst, 512);
                   memory :> bytes(stackpointer, 4)])`,
  MAP_EVERY X_GEN_TAC
   [`srcA:int64`; `srcB:int64`; `srcBt:int64`; `dst:int64`;
    `x0:num->int16`; `y0:num->int16`; `y0t:num->int16`;
    `x1:num->int16`; `y1:num->int16`; `y1t:num->int16`;
    `x2:num->int16`; `y2:num->int16`; `y2t:num->int16`;
    `x3:num->int16`; `y3:num->int16`; `y3t:num->int16`; `pc:num`;
    `stackpointer:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The outer loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + 0x28` `pc + 0xdb`
   `\i s. read RAX s = word_add srcBt (word(2 * i)) /\
          read R8 s = word_add srcA (word(4 * i)) /\
          read RDI s = word_add (word_add srcB (word(4 * i))) (word 2) /\
          read RDX s = word_add (word_add dst (word(4 * i))) (word 2) /\
          read R14 s = word_add srcBt (word 256) /\
          read RSP s = word_add stackpointer (word 4) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (2 * i)))) s = x0 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB (word (2 * i)))) s = y0 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (2 * i)))) s = y0t i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (512 + 2 * i)))) s = y2t i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (1536 + 2 * i)))) s = x3 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB (word (1536 + 2 * i)))) s = y3 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (768 + 2 * i)))) s = y3t i) /\
          ((!i. i < 256
                ==> abs(ival(x0 i)) <= &2 pow 12 /\
                    abs(ival(x1 i)) <= &2 pow 12 /\
                    abs(ival(x2 i)) <= &2 pow 12 /\
                    abs(ival(x3 i)) <= &2 pow 12)
           ==> (!j. j < i
                    ==> (ival(read(memory :> bytes16
                           (word_add dst (word (4 * j)))) s) ==
                         basemul4_even
                          (ival o x0) (ival o y0) (ival o y0t)
                          (ival o x1) (ival o y1) (ival o y1t)
                          (ival o x2) (ival o y2) (ival o y2t)
                          (ival o x3) (ival o y3) (ival o y3t)
                          j) (mod &3329) /\
                        (ival(read(memory :> bytes16
                           (word_add dst (word (4 * j + 2)))) s) ==
                         basemul4_odd
                          (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                          (ival o x2) (ival o y2) (ival o x3) (ival o y3)
                          j) (mod &3329)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The initialization is already done ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT];

    (*** The loop body, with the inner loop over the four polynomials
     *** unrolled, computing two output coefficients
     ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    BASEMUL_READ_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_EXEC (1--110) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC] THEN
    ASM_REWRITE_TAC[] THEN MLKEM_NATIVE_WORD_SIMP_TAC THEN
    REWRITE_TAC[MONTRED_X86_FOLD] THEN
    SUBGOAL_THEN
     `abs(ival(x0(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x2(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x3(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x0(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x2(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x3(2 * i + 1):int16)) <= &2 pow 12`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> 2 * i < 256 /\ 2 * i + 1 < 256`];
      ALL_TAC] THEN
    CONJ_TAC THEN BASEMUL_CONG_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add srcBt (word 256))
                     (word_add srcBt (word (2 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add x y) (word_add x z):int64 = word_sub y z`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> 2 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 128` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t pc
    stackpointer returnaddress.
     ALL (nonoverlapping (dst, 512))
         [(word pc, 0xef); (srcA, 2048); (srcB, 2048); (srcBt, 1024)] /\
     ALL (nonoverlapping (word_sub stackpointer (word 52), 60))
         [(word pc, 0xef); (srcA, 2048); (srcB, 2048); (srcBt, 1024);
          (dst, 512)]
     ==>
     ensures x86
       (\s. bytes_loaded s (word pc) mlkem_native_basemul_k4_gcc12_O2_mc /\
            read RIP s = word pc /\
            read RSP s = stackpointer /\
            read (memory :> bytes64 stackpointer) s = returnaddress /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (2 * i)))) s = y0 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (2 * i)))) s = y0t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1536 + 2 * i)))) s = x3 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1536 + 2 * i)))) s = y3 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (768 + 2 * i)))) s = y3t i))
       (\s. read RIP s = returnaddress /\
            read RSP s = word_add stackpointer (word 8) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                      abs(ival(x1 i)) <= &2 pow 12 /\
                      abs(ival(x2 i)) <= &2 pow 12 /\
                      abs(ival(x3 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul4_even
                            (ival o x0) (ival o y0) (ival o y0t)
                            (ival o x1) (ival o y1) (ival o y1t)
                            (ival o x2) (ival o y2) (ival o y2t)
                            (ival o x3) (ival o y3) (ival o y3t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul4_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2) (ival o x3) (ival o y3)
                            i) (mod &3329))))
       (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(dst, 512);
                   memory :> bytes(word_sub stackpointer (word 52), 52)])`,
  GEN_X86_ADD_RETURN_STACK_TAC MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_EXEC
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_CORRECT
    `[R15; R14; R13; R12; RBP; RBX]` 52 (13,7));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** The specification is that of mk_safety_spec for the C signature of
 *** mlkem_basemul_k4 and the theorem above, with the registers assigned
 *** before the core added to the precondition.
 ***)

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SAFE = time prove
 (`exists f_events.
       forall e srcA srcB srcBt dst pc stackpointer.
           ALL (nonoverlapping (dst,512))
           [word pc,0xef; srcA,2048; srcB,2048; srcBt,1024;
            stackpointer,4] /\
           ALL (nonoverlapping (stackpointer,4))
           [word pc,0xef; srcA,2048; srcB,2048; srcBt,1024]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_basemul_k4_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x28) /\
                    read RAX s = srcBt /\ read R8 s = srcA /\
                    read RDI s = word_add srcB (word 2) /\
                    read RDX s = word_add dst (word 2) /\
                    read R14 s = word_add srcBt (word 256) /\
                    read RSP s = word_add stackpointer (word 4) /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0xe4) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events srcA srcB srcBt dst pc stackpointer /\
                         memaccess_inbounds e2
                          [srcA,2048; srcB,2048; srcBt,1024; dst,512;
                           stackpointer,4]
                          [dst,512; stackpointer,4]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [RBX; RBP; R12; R13; R15] ,,
                MAYCHANGE [memory :> bytes (dst,512);
                           memory :> bytes (stackpointer,4)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(srcA:int64) (srcB:int64) (srcBt:int64) (dst:int64) (pc:num)
      (stackpointer:int64).
      APPEND
        (f_ev_epil srcA srcB srcBt dst pc stackpointer)
        (APPEND
          (ENUMERATEL 128
            (\i. f_ev_loop srcA srcB srcBt dst pc stackpointer i))
          (f_ev_prol srcA srcB srcBt dst pc stackpointer))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + 0x28` `pc + 0xe4`
    `\i s. read RAX s = word_add srcBt (word(2 * i)) /\
           read R8 s = word_add srcA (word(4 * i)) /\
           read RDI s = word_add (word_add srcB (word(4 * i))) (word 2) /\
           read RDX s = word_add (word_add dst (word(4 * i))) (word 2) /\
           read R14 s = word_add srcBt (word 256) /\
           read RSP s = word_add stackpointer (word 4)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN VAL_INT64_TAC `i:num` THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_EXEC (1--112) THEN
  SUBGOAL_THEN
   `~(val (word_add srcBt (word 256):int64) =
      val (word_add (word_add srcBt (word (2 * i))) (word 2):int64)) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> 2 * i + 2 < 2 EXP 64`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 128` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e srcA srcB srcBt dst pc stackpointer returnaddress.
           ALL (nonoverlapping (dst,512))
           [word pc,0xef; srcA,2048; srcB,2048; srcBt,1024] /\
           ALL (nonoverlapping (word_sub stackpointer (word 52),60))
           [word pc,0xef; srcA,2048; srcB,2048; srcBt,1024; dst,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_basemul_k4_gcc12_O2_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events srcA srcB srcBt dst pc
                                (word_sub stackpointer (word 52))
                                returnaddress /\
                         memaccess_inbounds e2
                          [srcA,2048; srcB,2048; srcBt,1024; dst,512;
                           word_sub stackpointer (word 52),60]
                          [dst,512; word_sub stackpointer (word 52),52]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst, 512);
                           memory :> bytes(word_sub stackpointer (word 52),
                                           52)])`,
  GEN_X86_ADD_RETURN_STACK_TAC MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_EXEC
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SAFE
    `[R15; R14; R13; R12; RBP; RBX]` 52 (13,7) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image, at address 0x20a0 (see                  *)
(* mlkem_native_libmlkem_gcc12_O2.ml).                                       *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_basemul_k4_gcc12_O2_mc
    0x20a0 [];;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t pc
    stackpointer returnaddress.
     aligned 16 (word pc:int64) /\
     ALL (nonoverlapping (dst, 512))
         [(word pc, 0x82a0); (srcA, 2048); (srcB, 2048); (srcBt, 1024)] /\
     ALL (nonoverlapping (word_sub stackpointer (word 52), 60))
         [(word pc, 0x82a0); (srcA, 2048); (srcB, 2048); (srcBt, 1024);
          (dst, 512)]
     ==>
     ensures x86
       (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
            read RIP s = word (pc + 0x20a0) /\
            read RSP s = stackpointer /\
            read (memory :> bytes64 stackpointer) s = returnaddress /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (2 * i)))) s = y0 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (2 * i)))) s = y0t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1536 + 2 * i)))) s = x3 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1536 + 2 * i)))) s = y3 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (768 + 2 * i)))) s = y3t i))
       (\s. read RIP s = returnaddress /\
            read RSP s = word_add stackpointer (word 8) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                      abs(ival(x1 i)) <= &2 pow 12 /\
                      abs(ival(x2 i)) <= &2 pow 12 /\
                      abs(ival(x3 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul4_even
                            (ival o x0) (ival o y0) (ival o y0t)
                            (ival o x1) (ival o y1) (ival o y1t)
                            (ival o x2) (ival o y2) (ival o y2t)
                            (ival o x3) (ival o y3) (ival o y3t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul4_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2) (ival o x3) (ival o y3)
                            i) (mod &3329))))
       (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(dst, 512);
                   memory :> bytes(word_sub stackpointer (word 52), 52)])`,
  MLKEM_NATIVE_IMAGE_TAC
   (INST [`pc + 0x20a0`,`pc:num`]
     (SPEC_ALL MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SUBROUTINE_CORRECT))
   [MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IN_IMAGE]);;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e srcA srcB srcBt dst pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (dst,512))
               [word pc,0x82a0; srcA,2048; srcB,2048; srcBt,1024] /\
           ALL (nonoverlapping (word_sub stackpointer (word 52),60))
               [word pc,0x82a0; srcA,2048; srcB,2048; srcBt,1024; dst,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x20a0) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events srcA srcB srcBt dst pc
                                (word_sub stackpointer (word 52))
                                returnaddress /\
                         memaccess_inbounds e2
                          [srcA,2048; srcB,2048; srcBt,1024; dst,512;
                           word_sub stackpointer (word 52),60]
                          [dst,512; word_sub stackpointer (word 52),52]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst, 512);
                           memory :> bytes(word_sub stackpointer (word 52),
                                           52)])`,
  MLKEM_NATIVE_IMAGE_SAFE_TAC MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SUBROUTINE_SAFE
   [`pc + 0x20a0`,`pc:num`]
   [MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IN_IMAGE]);;
