(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of 4-element polynomial vectors in NTT domain.             *)
(* This is the code for mlkem1024_polyvec_basemul_acc_montgomery_cached from *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mlkem_native/README.md).                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/base.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/layout.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;

(* Names for the labels of this transcription, whose code is at pc.          *)

install_layout (layout_copies
 ["basemul_k4","mlkem1024_polyvec_basemul_acc_montgomery_cached"]);;

(**** print_literal_from_elf
        "arm/mlkem_native/gcc12_O2/basemul_k4.o";;
 ****)

let mlkem_native_basemul_k4_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_basemul_k4_gcc12_O2_mc"
  "arm/mlkem_native/gcc12_O2/basemul_k4.o"
[
  0x91000807;       (* arm_ADD X7 X0 (rvalue (word 2)) *)
  0xaa0103e6;       (* arm_MOV X6 X1 *)
  0x91000845;       (* arm_ADD X5 X2 (rvalue (word 2)) *)
  0x9104006c;       (* arm_ADD X12 X3 (rvalue (word 256)) *)
  0x12819fc9;       (* arm_MOVN W9 (word 3326) 0 *)
  0x1281a008;       (* arm_MOVN W8 (word 3328) 0 *)
  0xaa0303e1;       (* arm_MOV X1 X3 *)
  0x910008cb;       (* arm_ADD X11 X6 (rvalue (word 2)) *)
  0xd10008aa;       (* arm_SUB X10 X5 (rvalue (word 2)) *)
  0xd2800000;       (* arm_MOV X0 (rvalue (word 0)) *)
  0x52800004;       (* arm_MOV W4 (rvalue (word 0)) *)
  0x52800002;       (* arm_MOV W2 (rvalue (word 0)) *)
  0x78e06971;       (* arm_LDRSH W17 X11 (Register_Offset X0) *)
  0x91040021;       (* arm_ADD X1 X1 (rvalue (word 256)) *)
  0x78e068d0;       (* arm_LDRSH W16 X6 (Register_Offset X0) *)
  0x78e0694d;       (* arm_LDRSH W13 X10 (Register_Offset X0) *)
  0x78e068ae;       (* arm_LDRSH W14 X5 (Register_Offset X0) *)
  0x91080000;       (* arm_ADD X0 X0 (rvalue (word 512)) *)
  0x78d0002f;       (* arm_LDRSH W15 X1 (Immediate_Offset (word
                       18446744073709551360)) *)
  0x1b0d7e12;       (* arm_MUL W18 W16 W13 *)
  0x1b0d7e2d;       (* arm_MUL W13 W17 W13 *)
  0x1b1149ef;       (* arm_MADD W15 W15 W17 W18 *)
  0x1b1035cd;       (* arm_MADD W13 W14 W16 W13 *)
  0x0b0f0042;       (* arm_ADD W2 W2 W15 *)
  0x0b0d0084;       (* arm_ADD W4 W4 W13 *)
  0xf120001f;       (* arm_CMP X0 (rvalue (word 2048)) *)
  0x54fffe41;       (* arm_BNE (word 2097096) *)
  0x1b097c41;       (* arm_MUL W1 W2 W9 *)
  0x91000863;       (* arm_ADD X3 X3 (rvalue (word 2)) *)
  0x1b097c80;       (* arm_MUL W0 W4 W9 *)
  0x910010c6;       (* arm_ADD X6 X6 (rvalue (word 4)) *)
  0x910010a5;       (* arm_ADD X5 X5 (rvalue (word 4)) *)
  0x13003c21;       (* arm_SBFM W1 W1 0 15 *)
  0x13003c00;       (* arm_SBFM W0 W0 0 15 *)
  0x1b080821;       (* arm_MADD W1 W1 W8 W2 *)
  0x1b081000;       (* arm_MADD W0 W0 W8 W4 *)
  0x13107c21;       (* arm_ASR W1 W1 16 *)
  0x781fe0e1;       (* arm_STRH W1 X7 (Immediate_Offset (word
                       18446744073709551614)) *)
  0x13107c00;       (* arm_ASR W0 W0 16 *)
  0x780044e0;       (* arm_STRH W0 X7 (Postimmediate_Offset (word 4)) *)
  0xeb03019f;       (* arm_CMP X12 X3 *)
  0x54fffba1;       (* arm_BNE (word 2097012) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_basemul_k4_gcc12_O2_mc;;

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

(*** Instantiate a quantified input fact at a particular index, and put   ***)
(*** the address in the form that the simulation will produce            ***)

let BASEMUL_SPECIALIZE_LOAD_TAC (f,idx,tgt) =
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in f (concl th) then
      MP_TAC(SPEC idx th) else failwith "BASEMUL_SPECIALIZE_LOAD_TAC") THEN
  ANTS_TAC THENL
   [W(fun (asl,w) -> MP_TAC(ARITH_RULE (mk_imp(`i < 128`,w)))) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
      let wt = find_term (fun t -> is_comb t && rator t = `word:num->int64`)
                         (lhand(concl th)) in
      ASSUME_TAC(REWRITE_RULE[ARITH_RULE(mk_eq(rand wt,tgt))] th))];;

(*** Prove the congruence for a Montgomery-reduced sum of products ***)

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

(*** Unlike mlkem_basemul_k4, this uses X18 as a temporary register ***)

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_CORRECT_STMT =
  `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t pc.
     ALL (nonoverlapping (dst, 512))
         [(word pc, basemul_k4_size); (srcA, 2048); (srcB, 2048);
          (srcBt, 1024)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_basemul_k4_gcc12_O2_mc /\
            read PC s = word pc /\
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
       (\s. read PC s = word (pc + basemul_k4_ret) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12 /\
                       abs(ival(x3 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul4_even
                            (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                            (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                            (ival o y2t) (ival o x3) (ival o y3) (ival o y3t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul4_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2) (ival o x3) (ival o y3)
                            i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_CORRECT =
  assume_spec MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_CORRECT_STMT;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SUBROUTINE_CORRECT_STMT =
  `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t
    pc returnaddress.
     ALL (nonoverlapping (dst, 512))
         [(word pc, basemul_k4_size); (srcA, 2048); (srcB, 2048);
          (srcBt, 1024)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_basemul_k4_gcc12_O2_mc /\
            read PC s = word pc /\
            read X30 s = returnaddress /\
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
       (\s. read PC s = returnaddress /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12 /\
                       abs(ival(x3 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul4_even
                            (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                            (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                            (ival o y2t) (ival o x3) (ival o y3) (ival o y3t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul4_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2) (ival o x3) (ival o y3)
                            i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_basemul_k4 ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_basemul_k4" subroutine_signatures)
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SUBROUTINE_CORRECT
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_EXEC;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e srcA srcB srcBt dst pc returnaddress.
           ALL (nonoverlapping (dst,512))
           [word pc,172; srcA,2048; srcB,2048; srcBt,1024]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_basemul_k4_gcc12_O2_mc /\
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
                         [srcA,2048; srcB,2048; srcBt,1024; dst,512]
                         [dst,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image (see libmlkem.ml).                       *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_basemul_k4_gcc12_O2_mc
    (layout "mlkem1024_polyvec_basemul_acc_montgomery_cached") [];;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t
    pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc, libmlkem_size); (srcA, 2048); (srcB, 2048); (srcBt, 1024)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_gcc12_O2_mc /\
            read PC s =
              word (pc + mlkem1024_polyvec_basemul_acc_montgomery_cached) /\
            read X30 s = returnaddress /\
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
       (\s. read PC s = returnaddress /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12 /\
                       abs(ival(x3 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul4_even
                            (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                            (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                            (ival o y2t) (ival o x3) (ival o y3) (ival o y3t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul4_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2) (ival o x3) (ival o y3)
                            i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e srcA srcB srcBt dst pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (dst,512))
           [word pc,libmlkem_size; srcA,2048; srcB,2048; srcBt,1024]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s =
                      word (pc
                             + mlkem1024_polyvec_basemul_acc_montgomery_cached)
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
                         [srcA,2048; srcB,2048; srcBt,1024; dst,512]
                         [dst,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
