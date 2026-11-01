(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of vectors of polynomials in NTT form for k = 3.           *)
(* This is the code for mlkem768_polyvec_basemul_acc_montgomery_cached from  *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mlkem_native/README.md).                                             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;

(**** print_literal_from_elf
        "x86/mlkem_native/mlkem_native_basemul_k3_gcc12_O2.o";;
 ****)

let mlkem_native_basemul_k3_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_basemul_k3_gcc12_O2_mc"
  "x86/mlkem_native/mlkem_native_basemul_k3_gcc12_O2.o"
[
  0x41; 0x57;              (* PUSH (% r15) *)
  0x4c; 0x8d; 0x42; 0x02;  (* LEA (% r8) (%% (rdx,2)) *)
  0x48; 0x89; 0xc8;        (* MOV (% rax) (% rcx) *)
  0x49; 0x89; 0xf1;        (* MOV (% r9) (% rsi) *)
  0x41; 0x56;              (* PUSH (% r14) *)
  0x48; 0x8d; 0x57; 0x02;  (* LEA (% rdx) (%% (rdi,2)) *)
  0x4c; 0x8d; 0xb1; 0x00; 0x01; 0x00; 0x00;
                           (* LEA (% r14) (%% (rcx,256)) *)
  0x41; 0x55;              (* PUSH (% r13) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x90;                    (* NOP *)
  0x49; 0x89; 0xc3;        (* MOV (% r11) (% rax) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x31; 0xff;              (* XOR (% edi) (% edi) *)
  0x31; 0xf6;              (* XOR (% esi) (% esi) *)
  0x4d; 0x8d; 0x61; 0x02;  (* LEA (% r12) (%% (r9,2)) *)
  0x49; 0x8d; 0x68; 0xfe;  (* LEA (% rbp) (%% (r8,18446744073709551614)) *)
  0x41; 0x0f; 0xbf; 0x1c; 0x0c;
                           (* MOVSX (% ebx) (Memop Word (%%% (r12,0,rcx))) *)
  0x45; 0x0f; 0xbf; 0x13;  (* MOVSX (% r10d) (Memop Word (%% (r11,0))) *)
  0x49; 0x81; 0xc3; 0x00; 0x01; 0x00; 0x00;
                           (* ADD (% r11) (Imm32 (word 256)) *)
  0x45; 0x0f; 0xbf; 0x2c; 0x09;
                           (* MOVSX (% r13d) (Memop Word (%%% (r9,0,rcx))) *)
  0x44; 0x0f; 0xbf; 0x7c; 0x0d; 0x00;
                           (* MOVSX (% r15d) (Memop Word (%%% (rbp,0,rcx))) *)
  0x44; 0x0f; 0xaf; 0xd3;  (* IMUL (% r10d) (% ebx) *)
  0x89; 0x5c; 0x24; 0xfc;  (* MOV (Memop Doubleword (%%
                                  (rsp,18446744073709551612))) (% ebx) *)
  0x44; 0x89; 0xd3;        (* MOV (% ebx) (% r10d) *)
  0x45; 0x89; 0xea;        (* MOV (% r10d) (% r13d) *)
  0x45; 0x0f; 0xaf; 0xd7;  (* IMUL (% r10d) (% r15d) *)
  0x44; 0x01; 0xd3;        (* ADD (% ebx) (% r10d) *)
  0x45; 0x0f; 0xbf; 0x14; 0x08;
                           (* MOVSX (% r10d) (Memop Word (%%% (r8,0,rcx))) *)
  0x48; 0x81; 0xc1; 0x00; 0x02; 0x00; 0x00;
                           (* ADD (% rcx) (Imm32 (word 512)) *)
  0x01; 0xde;              (* ADD (% esi) (% ebx) *)
  0x8b; 0x5c; 0x24; 0xfc;  (* MOV (% ebx) (Memop Doubleword (%%
                                  (rsp,18446744073709551612))) *)
  0x45; 0x0f; 0xaf; 0xd5;  (* IMUL (% r10d) (% r13d) *)
  0x41; 0x0f; 0xaf; 0xdf;  (* IMUL (% ebx) (% r15d) *)
  0x44; 0x01; 0xd3;        (* ADD (% ebx) (% r10d) *)
  0x01; 0xdf;              (* ADD (% edi) (% ebx) *)
  0x48; 0x81; 0xf9; 0x00; 0x06; 0x00; 0x00;
                           (* CMP (% rcx) (Imm32 (word 1536)) *)
  0x75; 0xa8;              (* JNE (Imm8 (word 168)) *)
  0x48; 0x83; 0xc0; 0x02;  (* ADD (% rax) (Imm8 (word 2)) *)
  0x49; 0x83; 0xc1; 0x04;  (* ADD (% r9) (Imm8 (word 4)) *)
  0x49; 0x83; 0xc0; 0x04;  (* ADD (% r8) (Imm8 (word 4)) *)
  0x48; 0x83; 0xc2; 0x04;  (* ADD (% rdx) (Imm8 (word 4)) *)
  0x66; 0x69; 0xce; 0x01; 0xf3;
                           (* IMUL3 (% cx) (% si,Imm16 (word 62209)) *)
  0x0f; 0xbf; 0xc9;        (* MOVSX (% ecx) (% cx) *)
  0x69; 0xc9; 0xff; 0xf2; 0xff; 0xff;
                           (* IMUL3 (% ecx) (% ecx,Imm32 (word 4294963967)) *)
  0x01; 0xf1;              (* ADD (% ecx) (% esi) *)
  0xc1; 0xf9; 0x10;        (* SAR (% ecx) (Imm8 (word 16)) *)
  0x66; 0x89; 0x4a; 0xfa;  (* MOV (Memop Word (%% (rdx,18446744073709551610)))
                                  (% cx) *)
  0x66; 0x69; 0xcf; 0x01; 0xf3;
                           (* IMUL3 (% cx) (% di,Imm16 (word 62209)) *)
  0x0f; 0xbf; 0xc9;        (* MOVSX (% ecx) (% cx) *)
  0x69; 0xc9; 0xff; 0xf2; 0xff; 0xff;
                           (* IMUL3 (% ecx) (% ecx,Imm32 (word 4294963967)) *)
  0x01; 0xf9;              (* ADD (% ecx) (% edi) *)
  0xc1; 0xf9; 0x10;        (* SAR (% ecx) (Imm8 (word 16)) *)
  0x66; 0x89; 0x4a; 0xfc;  (* MOV (Memop Word (%% (rdx,18446744073709551612)))
                                  (% cx) *)
  0x49; 0x39; 0xc6;        (* CMP (% r14) (% rax) *)
  0x0f; 0x85; 0x50; 0xff; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294967120)) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0x41; 0x5e;              (* POP (% r14) *)
  0x41; 0x5f;              (* POP (% r15) *)
  0xc3                     (* RET *)
];;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_basemul_k3_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* Definitions used to state specification, as for mlkem_basemul_k3.         *)
(* ------------------------------------------------------------------------- *)

let pmull = define
  `pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;

let pmull_acc3 = define
  `pmull_acc3 (x00: int) (x01 : int) (y00 : int) (y01 : int)
              (x10: int) (x11 : int) (y10 : int) (y11 : int)
              (x20: int) (x21 : int) (y20 : int) (y21 : int) =
              pmull x20 x21 y20 y21 + pmull x10 x11 y10 y11 +
              pmull x00 x01 y00 y01`;;

let pmul_acc3 = define
  `pmul_acc3 (x00: int) (x01 : int) (y00 : int) (y01 : int)
             (x10: int) (x11 : int) (y10 : int) (y11 : int)
             (x20: int) (x21 : int) (y20 : int) (y21 : int) =
             (&(inverse_mod 3329 65536) *
    pmull_acc3 x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21) rem &3329`;;

let basemul3_even = define
 `basemul3_even x0 y0 y0t x1 y1 y1t x2 y2 y2t = \i.
    pmul_acc3 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i)) (y0t i)
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i)) (y1t i)
              (x2 (2 * i)) (x2 (2 * i + 1))
              (y2 (2 * i)) (y2t i)`;;

let basemul3_odd = define
 `basemul3_odd x0 y0 x1 y1 x2 y2 = \i.
   pmul_acc3 (x0 (2 * i)) (x0 (2 * i + 1))
             (y0 (2 * i + 1)) (y0 (2 * i))
             (x1 (2 * i)) (x1 (2 * i + 1))
             (y1 (2 * i + 1)) (y1 (2 * i))
             (x2 (2 * i)) (x2 (2 * i + 1))
             (y2 (2 * i + 1)) (y2 (2 * i))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** Instantiate the input facts at the addresses that the loads use. The
 *** inner loop over the three polynomials indexes them with RCX = 0, 512
 *** and 1024, and the simulator folds this into the offset in two ways.
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
     y2t i`];;

let BASEMUL_CONG_TAC =
  ASSUM_LIST(fun ths -> W(fun (asl,w) ->
    let tm = rand(rand(lhand(rator w))) in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE ths tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2)))) in
    MP_TAC(CONJUNCT1 th3))) THEN
  REWRITE_TAC[basemul3_even; basemul3_odd;
              pmul_acc3; pmull_acc3; pmull; o_THM] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING;;

(*** The function saves RBX, RBP and R12-R15 and uses them as temporaries.
 *** Since the saves are interleaved with other setup, the core proof starts
 *** after them, with the registers that setup has assigned. The core also
 *** spills a 32-bit value to the red zone just below the stack pointer, and
 *** its "stackpointer" parameter is the address of that 4-byte slot.
 ***)

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t pc stackpointer.
     ALL (nonoverlapping (dst, 512))
         [(word pc, 0xdb); (srcA, 1536); (srcB, 1536); (srcBt, 768);
          (stackpointer, 4)] /\
     ALL (nonoverlapping (stackpointer, 4))
         [(word pc, 0xdb); (srcA, 1536); (srcB, 1536); (srcBt, 768)]
     ==>
     ensures x86
       (\s. bytes_loaded s (word pc) mlkem_native_basemul_k3_gcc12_O2_mc /\
            read RIP s = word (pc + 0x20) /\
            read RAX s = srcBt /\ read R9 s = srcA /\
            read R8 s = word_add srcB (word 2) /\
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
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i))
       (\s. read RIP s = word (pc + 0xd0) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                      abs(ival(x1 i)) <= &2 pow 12 /\
                      abs(ival(x2 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul3_even
                            (ival o x0) (ival o y0) (ival o y0t)
                            (ival o x1) (ival o y1) (ival o y1t)
                            (ival o x2) (ival o y2) (ival o y2t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul3_odd
                            (ival o x0) (ival o y0) (ival o x1)
                            (ival o y1) (ival o x2) (ival o y2)
                            i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [RBX; RBP; R12; R13; R15] ,,
        MAYCHANGE [memory :> bytes(dst, 512);
                   memory :> bytes(stackpointer, 4)])`,
  MAP_EVERY X_GEN_TAC
   [`srcA:int64`; `srcB:int64`; `srcBt:int64`; `dst:int64`;
    `x0:num->int16`; `y0:num->int16`; `y0t:num->int16`;
    `x1:num->int16`; `y1:num->int16`; `y1t:num->int16`;
    `x2:num->int16`; `y2:num->int16`; `y2t:num->int16`; `pc:num`;
    `stackpointer:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The outer loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + 0x20` `pc + 0xc7`
   `\i s. read RAX s = word_add srcBt (word(2 * i)) /\
          read R9 s = word_add srcA (word(4 * i)) /\
          read R8 s = word_add (word_add srcB (word(4 * i))) (word 2) /\
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
          ((!i. i < 256
                ==> abs(ival(x0 i)) <= &2 pow 12 /\
                    abs(ival(x1 i)) <= &2 pow 12 /\
                    abs(ival(x2 i)) <= &2 pow 12)
           ==> (!j. j < i
                    ==> (ival(read(memory :> bytes16
                           (word_add dst (word (4 * j)))) s) ==
                         basemul3_even
                          (ival o x0) (ival o y0) (ival o y0t)
                          (ival o x1) (ival o y1) (ival o y1t)
                          (ival o x2) (ival o y2) (ival o y2t)
                          j) (mod &3329) /\
                        (ival(read(memory :> bytes16
                           (word_add dst (word (4 * j + 2)))) s) ==
                         basemul3_odd
                          (ival o x0) (ival o y0) (ival o x1)
                          (ival o y1) (ival o x2) (ival o y2)
                          j) (mod &3329)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The initialization is already done ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT];

    (*** The loop body, with the inner loop over the three polynomials
     *** unrolled, computing two output coefficients
     ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    BASEMUL_READ_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--85) THEN
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
      abs(ival(x0(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x2(2 * i + 1):int16)) <= &2 pow 12`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> 2 * i < 256 /\ 2 * i + 1 < 256`];
      ALL_TAC] THEN
    CONJ_TAC THEN BASEMUL_CONG_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--2) THEN
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
    X86_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t pc
    stackpointer returnaddress.
     ALL (nonoverlapping (dst, 512))
         [(word pc, 0xdb); (srcA, 1536); (srcB, 1536); (srcBt, 768)] /\
     ALL (nonoverlapping (word_sub stackpointer (word 52), 60))
         [(word pc, 0xdb); (srcA, 1536); (srcB, 1536); (srcBt, 768);
          (dst, 512)]
     ==>
     ensures x86
       (\s. bytes_loaded s (word pc) mlkem_native_basemul_k3_gcc12_O2_mc /\
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
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i))
       (\s. read RIP s = returnaddress /\
            read RSP s = word_add stackpointer (word 8) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                      abs(ival(x1 i)) <= &2 pow 12 /\
                      abs(ival(x2 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul3_even
                            (ival o x0) (ival o y0) (ival o y0t)
                            (ival o x1) (ival o y1) (ival o y1t)
                            (ival o x2) (ival o y2) (ival o y2t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul3_odd
                            (ival o x0) (ival o y0) (ival o x1)
                            (ival o y1) (ival o x2) (ival o y2)
                            i) (mod &3329))))
       (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(dst, 512);
                   memory :> bytes(word_sub stackpointer (word 52), 52)])`,
  GEN_X86_ADD_RETURN_STACK_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_CORRECT
    `[R15; R14; R13; R12; RBP; RBX]` 52 (12,7));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** The specification is that of mk_safety_spec for the C signature of
 *** mlkem_basemul_k3 and the theorem above, with the registers assigned
 *** before the core added to the precondition.
 ***)

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SAFE = time prove
 (`exists f_events.
       forall e srcA srcB srcBt dst pc stackpointer.
           ALL (nonoverlapping (dst,512))
           [word pc,0xdb; srcA,1536; srcB,1536; srcBt,768; stackpointer,4] /\
           ALL (nonoverlapping (stackpointer,4))
           [word pc,0xdb; srcA,1536; srcB,1536; srcBt,768]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_basemul_k3_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x20) /\
                    read RAX s = srcBt /\ read R9 s = srcA /\
                    read R8 s = word_add srcB (word 2) /\
                    read RDX s = word_add dst (word 2) /\
                    read R14 s = word_add srcBt (word 256) /\
                    read RSP s = word_add stackpointer (word 4) /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0xd0) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events srcA srcB srcBt dst pc stackpointer /\
                         memaccess_inbounds e2
                          [srcA,1536; srcB,1536; srcBt,768; dst,512;
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
              fst MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + 0x20` `pc + 0xd0`
    `\i s. read RAX s = word_add srcBt (word(2 * i)) /\
           read R9 s = word_add srcA (word(4 * i)) /\
           read R8 s = word_add (word_add srcB (word(4 * i))) (word 2) /\
           read RDX s = word_add (word_add dst (word(4 * i))) (word 2) /\
           read R14 s = word_add srcBt (word 256) /\
           read RSP s = word_add stackpointer (word 4)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN VAL_INT64_TAC `i:num` THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--87) THEN
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

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e srcA srcB srcBt dst pc stackpointer returnaddress.
           ALL (nonoverlapping (dst,512))
           [word pc,0xdb; srcA,1536; srcB,1536; srcBt,768] /\
           ALL (nonoverlapping (word_sub stackpointer (word 52),60))
           [word pc,0xdb; srcA,1536; srcB,1536; srcBt,768; dst,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_basemul_k3_gcc12_O2_mc /\
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
                          [srcA,1536; srcB,1536; srcBt,768; dst,512;
                           word_sub stackpointer (word 52),60]
                          [dst,512; word_sub stackpointer (word 52),52]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst, 512);
                           memory :> bytes(word_sub stackpointer (word 52),
                                           52)])`,
  GEN_X86_ADD_RETURN_STACK_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SAFE
    `[R15; R14; R13; R12; RBP; RBX]` 52 (12,7) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
