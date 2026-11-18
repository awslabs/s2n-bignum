(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of 2-element polynomial vectors in NTT domain.             *)
(* This is the code for mlkem512_polyvec_basemul_acc_montgomery_cached from  *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mlkem_native/README.md).                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/base.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/layout.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;

(* Names for the labels of this transcription, whose code is at pc.          *)

install_layout (layout_copies
 ["basemul_k2","mlkem512_polyvec_basemul_acc_montgomery_cached"]);;

(**** print_literal_from_elf
        "arm/mlkem_native/gcc12_O2/basemul_k2.o";;
 ****)

let mlkem_native_basemul_k2_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_basemul_k2_gcc12_O2_mc"
  "arm/mlkem_native/gcc12_O2/basemul_k2.o"
[
  0xaa0103e4;       (* arm_MOV X4 X1 *)
  0xaa0003e7;       (* arm_MOV X7 X0 *)
  0xaa0203e5;       (* arm_MOV X5 X2 *)
  0xaa0303e6;       (* arm_MOV X6 X3 *)
  0x9108002d;       (* arm_ADD X13 X1 (rvalue (word 512)) *)
  0x12819fcc;       (* arm_MOVN W12 (word 3326) 0 *)
  0x1281a00b;       (* arm_MOVN W11 (word 3328) 0 *)
  0xd503201f;       (* arm_NOP *)
  0x79c00490;       (* arm_LDRSH W16 X4 (Immediate_Offset (word 2)) *)
  0x91001084;       (* arm_ADD X4 X4 (rvalue (word 4)) *)
  0x79c000a0;       (* arm_LDRSH W0 X5 (Immediate_Offset (word 0)) *)
  0x910008c6;       (* arm_ADD X6 X6 (rvalue (word 2)) *)
  0x79c400a1;       (* arm_LDRSH W1 X5 (Immediate_Offset (word 512)) *)
  0x910010e7;       (* arm_ADD X7 X7 (rvalue (word 4)) *)
  0x78dfc08a;       (* arm_LDRSH W10 X4 (Immediate_Offset (word
                       18446744073709551612)) *)
  0x910010a5;       (* arm_ADD X5 X5 (rvalue (word 4)) *)
  0x79c3fc8f;       (* arm_LDRSH W15 X4 (Immediate_Offset (word 510)) *)
  0x79c3f88e;       (* arm_LDRSH W14 X4 (Immediate_Offset (word 508)) *)
  0x78dfe0c3;       (* arm_LDRSH W3 X6 (Immediate_Offset (word
                       18446744073709551614)) *)
  0x79c1fcc9;       (* arm_LDRSH W9 X6 (Immediate_Offset (word 254)) *)
  0x1b007d52;       (* arm_MUL W18 W10 W0 *)
  0x79c3fca2;       (* arm_LDRSH W2 X5 (Immediate_Offset (word 510)) *)
  0x1b007e00;       (* arm_MUL W0 W16 W0 *)
  0x78dfe0a8;       (* arm_LDRSH W8 X5 (Immediate_Offset (word
                       18446744073709551614)) *)
  0x1b017dd1;       (* arm_MUL W17 W14 W1 *)
  0x1b017de1;       (* arm_MUL W1 W15 W1 *)
  0x1b104863;       (* arm_MADD W3 W3 W16 W18 *)
  0x1b0e0442;       (* arm_MADD W2 W2 W14 W1 *)
  0x1b0a0100;       (* arm_MADD W0 W8 W10 W0 *)
  0x1b0f4529;       (* arm_MADD W9 W9 W15 W17 *)
  0x0b000042;       (* arm_ADD W2 W2 W0 *)
  0x0b090063;       (* arm_ADD W3 W3 W9 *)
  0x1b0c7c40;       (* arm_MUL W0 W2 W12 *)
  0x1b0c7c61;       (* arm_MUL W1 W3 W12 *)
  0x13003c00;       (* arm_SBFM W0 W0 0 15 *)
  0x13003c21;       (* arm_SBFM W1 W1 0 15 *)
  0x1b0b0800;       (* arm_MADD W0 W0 W11 W2 *)
  0x1b0b0c21;       (* arm_MADD W1 W1 W11 W3 *)
  0x13107c00;       (* arm_ASR W0 W0 16 *)
  0x781fe0e0;       (* arm_STRH W0 X7 (Immediate_Offset (word
                       18446744073709551614)) *)
  0x13107c21;       (* arm_ASR W1 W1 16 *)
  0x781fc0e1;       (* arm_STRH W1 X7 (Immediate_Offset (word
                       18446744073709551612)) *)
  0xeb0d009f;       (* arm_CMP X4 X13 *)
  0x54fffba1;       (* arm_BNE (word 2097012) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_basemul_k2_gcc12_O2_mc;;

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

let BASEMUL_ADDR_NORM_RULES =
  map ARITH_RULE
   [`2 * 2 * i = 4 * i`; `2 * (2 * i + 1) = 4 * i + 2`;
    `512 + 2 * 2 * i = 4 * i + 512`; `512 + 2 * (2 * i + 1) = 4 * i + 514`;
    `256 + 2 * i = 2 * i + 256`];;

(*** Instantiate a quantified input fact at a particular index ***)

let SPECIALIZE_LOAD_TAC (f,idx) =
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in f (concl th) then
      MP_TAC(SPEC idx th) else failwith "SPECIALIZE_LOAD_TAC") THEN
  ANTS_TAC THENL
   [ASM_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE BASEMUL_ADDR_NORM_RULES)];;

(*** Prove the congruence for a Montgomery-reduced sum of products ***)

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

(*** Unlike mlkem_basemul_k2, this uses X18 as a temporary register ***)

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_CORRECT_STMT =
  `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc.
     ALL (nonoverlapping (dst, 512))
         [(word pc, basemul_k2_size); (srcA, 1024); (srcB, 1024); (srcBt, 512)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_basemul_k2_gcc12_O2_mc /\
            read PC s = word pc /\
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
       (\s. read PC s = word (pc + basemul_k2_ret) /\
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
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_CORRECT =
  assume_spec MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_CORRECT_STMT;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_CORRECT_STMT =
  `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc returnaddress.
     ALL (nonoverlapping (dst, 512))
         [(word pc, basemul_k2_size); (srcA, 1024); (srcB, 1024); (srcBt, 512)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_basemul_k2_gcc12_O2_mc /\
            read PC s = word pc /\
            read X30 s = returnaddress /\
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
       (\s. read PC s = returnaddress /\
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
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_basemul_k2 ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_basemul_k2" subroutine_signatures)
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_CORRECT
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e srcA srcB srcBt dst pc returnaddress.
           ALL (nonoverlapping (dst,512))
           [word pc,180; srcA,1024; srcB,1024; srcBt,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_basemul_k2_gcc12_O2_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events srcA srcB srcBt dst pc returnaddress /\
                        memaccess_inbounds e2
                         [srcA,1024; srcB,1024; srcBt,512; dst,512]
                         [dst,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image (see libmlkem.ml).                       *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_basemul_k2_gcc12_O2_mc
    (layout "mlkem512_polyvec_basemul_acc_montgomery_cached") [];;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc, libmlkem_size); (srcA, 1024); (srcB, 1024); (srcBt, 512)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_gcc12_O2_mc /\
            read PC s =
              word (pc + mlkem512_polyvec_basemul_acc_montgomery_cached) /\
            read X30 s = returnaddress /\
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
       (\s. read PC s = returnaddress /\
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
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e srcA srcB srcBt dst pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (dst,512))
           [word pc,libmlkem_size; srcA,1024; srcB,1024; srcBt,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s =
                      word (pc
                             + mlkem512_polyvec_basemul_acc_montgomery_cached)
                              /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events srcA srcB srcBt dst pc returnaddress /\
                        memaccess_inbounds e2
                         [srcA,1024; srcB,1024; srcBt,512; dst,512]
                         [dst,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
