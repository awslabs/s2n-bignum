(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of vectors of polynomials in NTT form for k = 2.           *)
(* This is the code for mlkem512_polyvec_basemul_acc_montgomery_cached from  *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mlkem_native/README.md).                                             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;

(**** print_literal_from_elf
        "x86/mlkem_native/mlkem_native_basemul_k2_gcc12_O2.o";;
 ****)

let mlkem_native_basemul_k2_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_basemul_k2_gcc12_O2_mc"
  "x86/mlkem_native/mlkem_native_basemul_k2_gcc12_O2.o"
[
  0x41; 0x55;              (* PUSH (% r13) *)
  0x49; 0x89; 0xd0;        (* MOV (% r8) (% rdx) *)
  0x49; 0x89; 0xc9;        (* MOV (% r9) (% rcx) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x41; 0x54;              (* PUSH (% r12) *)
  0x55;                    (* PUSH (% rbp) *)
  0x53;                    (* PUSH (% rbx) *)
  0x66; 0x90;              (* NOP *)
  0x45; 0x0f; 0xbf; 0x1c; 0x80;
                           (* MOVSX (% r11d) (Memop Word (%%% (r8,2,rax))) *)
  0x44; 0x0f; 0xbf; 0x64; 0x86; 0x02;
                           (* MOVSX (% r12d) (Memop Word (%%%% (rsi,2,rax,&2)))
                                    *)
  0x44; 0x0f; 0xbf; 0x2c; 0x86;
                           (* MOVSX (% r13d) (Memop Word (%%% (rsi,2,rax))) *)
  0x41; 0x0f; 0xbf; 0x0c; 0x41;
                           (* MOVSX (% ecx) (Memop Word (%%% (r9,1,rax))) *)
  0x44; 0x89; 0xda;        (* MOV (% edx) (% r11d) *)
  0x45; 0x0f; 0xaf; 0xdc;  (* IMUL (% r11d) (% r12d) *)
  0x44; 0x0f; 0xbf; 0x94; 0x86; 0x02; 0x02; 0x00; 0x00;
                           (* MOVSX (% r10d) (Memop Word (%%%%
                                    (rsi,2,rax,&514))) *)
  0x0f; 0xbf; 0xac; 0x86; 0x00; 0x02; 0x00; 0x00;
                           (* MOVSX (% ebp) (Memop Word (%%%%
                                    (rsi,2,rax,&512))) *)
  0x41; 0x0f; 0xbf; 0x9c; 0x80; 0x00; 0x02; 0x00; 0x00;
                           (* MOVSX (% ebx) (Memop Word (%%%% (r8,2,rax,&512)))
                                    *)
  0x41; 0x0f; 0xaf; 0xd5;  (* IMUL (% edx) (% r13d) *)
  0x41; 0x0f; 0xaf; 0xcc;  (* IMUL (% ecx) (% r12d) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0x0f; 0xbf; 0x94; 0x41; 0x00; 0x01; 0x00; 0x00;
                           (* MOVSX (% edx) (Memop Word (%%%% (r9,1,rax,&256)))
                                    *)
  0x41; 0x0f; 0xaf; 0xd2;  (* IMUL (% edx) (% r10d) *)
  0x44; 0x0f; 0xaf; 0xd3;  (* IMUL (% r10d) (% ebx) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x89; 0xea;              (* MOV (% edx) (% ebp) *)
  0x0f; 0xaf; 0xd3;        (* IMUL (% edx) (% ebx) *)
  0x01; 0xd1;              (* ADD (% ecx) (% edx) *)
  0x41; 0x0f; 0xbf; 0x54; 0x80; 0x02;
                           (* MOVSX (% edx) (Memop Word (%%%% (r8,2,rax,&2)))
                                    *)
  0x41; 0x0f; 0xaf; 0xd5;  (* IMUL (% edx) (% r13d) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x45; 0x0f; 0xbf; 0x9c; 0x80; 0x02; 0x02; 0x00; 0x00;
                           (* MOVSX (% r11d) (Memop Word (%%%%
                                    (r8,2,rax,&514))) *)
  0x44; 0x0f; 0xaf; 0xdd;  (* IMUL (% r11d) (% ebp) *)
  0x44; 0x01; 0xda;        (* ADD (% edx) (% r11d) *)
  0x44; 0x01; 0xd2;        (* ADD (% edx) (% r10d) *)
  0x66; 0x44; 0x69; 0xd1; 0x01; 0xf3;
                           (* IMUL3 (% r10w) (% cx,Imm16 (word 62209)) *)
  0x45; 0x0f; 0xbf; 0xd2;  (* MOVSX (% r10d) (% r10w) *)
  0x45; 0x69; 0xd2; 0xff; 0xf2; 0xff; 0xff;
                           (* IMUL3 (% r10d) (% r10d,Imm32 (word 4294963967))
                                    *)
  0x44; 0x01; 0xd1;        (* ADD (% ecx) (% r10d) *)
  0xc1; 0xf9; 0x10;        (* SAR (% ecx) (Imm8 (word 16)) *)
  0x66; 0x89; 0x0c; 0x87;  (* MOV (Memop Word (%%% (rdi,2,rax))) (% cx) *)
  0x66; 0x69; 0xca; 0x01; 0xf3;
                           (* IMUL3 (% cx) (% dx,Imm16 (word 62209)) *)
  0x0f; 0xbf; 0xc9;        (* MOVSX (% ecx) (% cx) *)
  0x69; 0xc9; 0xff; 0xf2; 0xff; 0xff;
                           (* IMUL3 (% ecx) (% ecx,Imm32 (word 4294963967)) *)
  0x01; 0xca;              (* ADD (% edx) (% ecx) *)
  0xc1; 0xfa; 0x10;        (* SAR (% edx) (Imm8 (word 16)) *)
  0x66; 0x89; 0x54; 0x87; 0x02;
                           (* MOV (Memop Word (%%%% (rdi,2,rax,&2))) (% dx) *)
  0x48; 0x83; 0xc0; 0x01;  (* ADD (% rax) (Imm8 (word 1)) *)
  0x48; 0x3d; 0x80; 0x00; 0x00; 0x00;
                           (* CMP (% rax) (Imm32 (word 128)) *)
  0x0f; 0x85; 0x43; 0xff; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294967107)) *)
  0x5b;                    (* POP (% rbx) *)
  0x5d;                    (* POP (% rbp) *)
  0x41; 0x5c;              (* POP (% r12) *)
  0x41; 0x5d;              (* POP (% r13) *)
  0xc3                     (* RET *)
];;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_basemul_k2_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* Definitions used to state specification, as for mlkem_basemul_k2.         *)
(* ------------------------------------------------------------------------- *)

let pmull = define
  `pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;
let pmull_acc2 = define
    `pmull_acc2 (x00: int) (x01 : int) (y00 : int) (y01 : int)
          (x10: int) (x11 : int) (y10 : int) (y11 : int) =
      pmull x10 x11 y10 y11 + pmull x00 x01 y00 y01`;;
let pmul_acc2 = define
    `pmul_acc2 (x00: int) (x01 : int) (y00 : int) (y01 : int)
          (x10: int) (x11 : int) (y10 : int) (y11 : int) =
     (&(inverse_mod 3329 65536) *
      pmull_acc2 x00 x01 y00 y01 x10 x11 y10 y11) rem &3329`;;
let basemul2_even = define
   `basemul2_even x0 y0 y0t x1 y1 y1t = \i.
      pmul_acc2 (x0 (2 * i)) (x0 (2 * i + 1))
                (y0 (2 * i)) (y0t i)
                (x1 (2 * i)) (x1 (2 * i + 1))
                (y1 (2 * i)) (y1t i)`;;
let basemul2_odd = define
 `basemul2_odd x0 y0 x1 y1 = \i.
    pmul_acc2 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i + 1)) (y0 (2 * i))
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i + 1)) (y1 (2 * i))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** Instantiate the input facts at the addresses that the indexed loads ***)
(*** compute from the loop counter i in RAX                              ***)

let BASEMUL_READ_TAC =
  MAP_EVERY READ_INSTANCE_TAC
   [`read (memory :> bytes16 (word_add srcA (word (4 * i)))) s0 = x0(2 * i)`;
    `read (memory :> bytes16 (word_add srcA (word (4 * i + 2)))) s0 =
     x0(2 * i + 1)`;
    `read (memory :> bytes16 (word_add srcA (word (4 * i + 512)))) s0 =
     x1(2 * i)`;
    `read (memory :> bytes16 (word_add srcA (word (4 * i + 514)))) s0 =
     x1(2 * i + 1)`;
    `read (memory :> bytes16 (word_add srcB (word (4 * i)))) s0 = y0(2 * i)`;
    `read (memory :> bytes16 (word_add srcB (word (4 * i + 2)))) s0 =
     y0(2 * i + 1)`;
    `read (memory :> bytes16 (word_add srcB (word (4 * i + 512)))) s0 =
     y1(2 * i)`;
    `read (memory :> bytes16 (word_add srcB (word (4 * i + 514)))) s0 =
     y1(2 * i + 1)`;
    `read (memory :> bytes16 (word_add srcBt (word (2 * i)))) s0 = y0t i`;
    `read (memory :> bytes16 (word_add srcBt (word (2 * i + 256)))) s0 =
     y1t i`];;
let MONTRED_SCALAR_CONG_TAC =
  ASSUM_LIST(fun ths -> W(fun (asl,w) ->
    let tm = rand(rand(lhand(rator w))) in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE ths tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2)))) in
    MP_TAC(CONJUNCT1 th3))) THEN
  REWRITE_TAC[basemul2_even; basemul2_odd;
              pmul_acc2; pmull_acc2; pmull; o_THM] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING;;

(*** The function saves RBX, RBP, R12 and R13 and uses them as temporaries.
 *** Since the saves are interleaved with other setup, the core proof starts
 *** after them, with the registers that setup has assigned.
 ***)

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc.
     ALL (nonoverlapping (dst, 512))
         [(word pc, 0xd4); (srcA, 1024); (srcB, 1024); (srcBt, 512)]
     ==>
     ensures x86
       (\s. bytes_loaded s (word pc) mlkem_native_basemul_k2_gcc12_O2_mc /\
            read RIP s = word (pc + 0x10) /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            read R8 s = srcB /\ read R9 s = srcBt /\ read RAX s = word 0 /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB  (word (2 * i)))) s = y0 i) /\
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
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i))
       (\s. read RIP s = word (pc + 0xcd) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                      abs(ival(x1 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                         (ival o x1) (ival o y1) (ival o y1t)
                                         i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul2_odd (ival o x0) (ival o y0) (ival o x1)
                           (ival o y1) i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [RBX; RBP; R12; R13] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`,
  MAP_EVERY X_GEN_TAC
   [`srcA:int64`; `srcB:int64`; `srcBt:int64`; `dst:int64`;
    `x0:num->int16`; `y0:num->int16`; `y0t:num->int16`;
    `x1:num->int16`; `y1:num->int16`; `y1t:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + 0x10` `pc + 0xc1`
   `\i s. read RAX s = word i /\ read RDI s = dst /\ read RSI s = srcA /\
          read R8 s = srcB /\ read R9 s = srcBt /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (2 * i)))) s = x0 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB  (word (2 * i)))) s = y0 i) /\
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
          ((!i. i < 256
                ==> abs(ival(x0 i)) <= &2 pow 12 /\
                    abs(ival(x1 i)) <= &2 pow 12)
           ==> (!j. j < i
                    ==> (ival(read(memory :> bytes16
                           (word_add dst (word (4 * j)))) s) ==
                         basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                       (ival o x1) (ival o y1) (ival o y1t)
                                       j) (mod &3329) /\
                        (ival(read(memory :> bytes16
                           (word_add dst (word (4 * j + 2)))) s) ==
                         basemul2_odd (ival o x0) (ival o y0) (ival o x1)
                         (ival o y1) j) (mod &3329)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The initialization is already done ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[CONJUNCT1 LT];

    (*** The loop body, computing two output coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    VAL_INT64_TAC `i:num` THEN BASEMUL_READ_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--39) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MLKEM_NATIVE_WORD_SIMP_TAC THEN
    REWRITE_TAC[MONTRED_X86_FOLD] THEN
    SUBGOAL_THEN
     `abs(ival(x0(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x0(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i + 1):int16)) <= &2 pow 12`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> 2 * i < 256 /\ 2 * i + 1 < 256`];
      ALL_TAC] THEN
    CONJ_TAC THEN MONTRED_SCALAR_CONG_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN `~(val(word_sub (word i) (word 128):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 128` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc stackpointer returnaddress.
     ALL (nonoverlapping (dst, 512))
         [(word pc, 0xd4); (srcA, 1024); (srcB, 1024); (srcBt, 512)] /\
     ALL (nonoverlapping (word_sub stackpointer (word 32), 40))
         [(word pc, 0xd4); (srcA, 1024); (srcB, 1024); (srcBt, 512);
          (dst, 512)]
     ==>
     ensures x86
       (\s. bytes_loaded s (word pc) mlkem_native_basemul_k2_gcc12_O2_mc /\
            read RIP s = word pc /\
            read RSP s = stackpointer /\
            read (memory :> bytes64 stackpointer) s = returnaddress /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB  (word (2 * i)))) s = y0 i) /\
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
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i))
       (\s. read RIP s = returnaddress /\
            read RSP s = word_add stackpointer (word 8) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                      abs(ival(x1 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                         (ival o x1) (ival o y1) (ival o y1t)
                                         i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul2_odd (ival o x0) (ival o y0) (ival o x1)
                           (ival o y1) i) (mod &3329))))
       (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [memory :> bytes(dst, 512);
                   memory :> bytes(word_sub stackpointer (word 32), 32)])`,
  GEN_X86_ADD_RETURN_STACK_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_CORRECT `[R13; R12; RBP; RBX]` 32 (8,5));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** The specification is that of mk_safety_spec for the C signature of
 *** mlkem_basemul_k2 and the theorem above, with the registers assigned
 *** before the core added to the precondition.
 ***)

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SAFE = time prove
 (`exists f_events.
       forall e srcA srcB srcBt dst pc.
           ALL (nonoverlapping (dst,512))
           [word pc,0xd4; srcA,1024; srcB,1024; srcBt,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_basemul_k2_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x10) /\
                    C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                    read R8 s = srcB /\ read R9 s = srcBt /\
                    read RAX s = word 0 /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0xcd) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events srcA srcB srcBt dst pc /\
                         memaccess_inbounds e2
                          [srcA,1024; srcB,1024; srcBt,512; dst,512]
                          [dst,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [RBX; RBP; R12; R13] ,,
                MAYCHANGE [memory :> bytes (dst,512)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(srcA:int64) (srcB:int64) (srcBt:int64) (dst:int64) (pc:num).
      APPEND
        (f_ev_epil srcA srcB srcBt dst pc)
        (APPEND
          (ENUMERATEL 128 (\i. f_ev_loop srcA srcB srcBt dst pc i))
          (f_ev_prol srcA srcB srcBt dst pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + 0x10` `pc + 0xcd`
    `\i s. read RAX s = word i /\ read RDI s = dst /\ read RSI s = srcA /\
           read R8 s = srcB /\ read R9 s = srcBt` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN VAL_INT64_TAC `i:num` THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--41) THEN
  MP_TAC(SPECL [`i:num`; `128`; `18446744073709551489`]
    VAL_WORD_ADD_LOOP_TEST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN SUBST_ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e srcA srcB srcBt dst pc stackpointer returnaddress.
           ALL (nonoverlapping (dst,512))
           [word pc,0xd4; srcA,1024; srcB,1024; srcBt,512] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
           [word pc,0xd4; srcA,1024; srcB,1024; srcBt,512; dst,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_basemul_k2_gcc12_O2_mc /\
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
                                (word_sub stackpointer (word 32))
                                returnaddress /\
                         memaccess_inbounds e2
                          [srcA,1024; srcB,1024; srcBt,512; dst,512;
                           word_sub stackpointer (word 32),40]
                          [dst,512; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst, 512);
                           memory :> bytes(word_sub stackpointer (word 32),
                                           32)])`,
  GEN_X86_ADD_RETURN_STACK_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SAFE `[R13; R12; RBP; RBX]` 32 (8,5) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
