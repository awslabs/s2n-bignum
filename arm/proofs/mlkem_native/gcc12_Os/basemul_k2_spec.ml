(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of 2-element polynomial vectors in NTT domain.             *)
(* This is the code for mlkem512_polyvec_basemul_acc_montgomery_cached from *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -Os      *)
(* (see mlkem_native/README.md). It is the scalar loop over the 128 pairs of *)
(* coefficients that -O2 produces, with other registers and another order of *)
(* instructions. It uses X0 to X15 only, so it does not change X18. It is    *)
(* verified in the whole image (see libmlkem.ml), with the same statements   *)
(* as the -O2 code.                                                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem512_polyvec_basemul_acc_montgomery_cached:
       +0x0: add     x11, x1, #0x200
       +0x4: mov     w9, #0xfffff301
       +0x8: mov     w8, #0xfffff2ff
       +0xc: ldrsh   w10, [x1]
      +0x10: add     x1, x1, #0x4
      +0x14: ldrsh   w4, [x2]
      +0x18: add     x3, x3, #0x2
      +0x1c: ldursh  w12, [x1, #-2]
      +0x20: add     x2, x2, #0x4
      +0x24: ldursh  w6, [x3, #-2]
      +0x28: add     x0, x0, #0x4
      +0x2c: ldrsh   w13, [x1, #508]
      +0x30: ldrsh   w14, [x2, #508]
      +0x34: mul     w5, w4, w10
      +0x38: ldrsh   w7, [x1, #510]
      +0x3c: mul     w4, w4, w12
      +0x40: madd    w6, w6, w12, w5
      +0x44: ldrsh   w5, [x3, #254]
      +0x48: mul     w15, w13, w14
      +0x4c: madd    w5, w5, w7, w15
      +0x50: mul     w7, w7, w14
      +0x54: add     w6, w6, w5
      +0x58: ldrsh   w5, [x2, #510]
      +0x5c: madd    w5, w5, w13, w7
      +0x60: ldursh  w7, [x2, #-2]
      +0x64: madd    w4, w7, w10, w4
      +0x68: add     w5, w5, w4
      +0x6c: mul     w4, w6, w9
      +0x70: sxth    w4, w4
      +0x74: madd    w4, w4, w8, w6
      +0x78: asr     w4, w4, #16
      +0x7c: sturh   w4, [x0, #-4]
      +0x80: mul     w4, w5, w9
      +0x84: sxth    w4, w4
      +0x88: madd    w4, w4, w8, w5
      +0x8c: asr     w4, w4, #16
      +0x90: sturh   w4, [x0, #-2]
      +0x94: cmp     x11, x1
      +0x98: b.ne    <mlkem512_polyvec_basemul_acc_montgomery_cached+0xc>
      +0x9c: ret
 ***)

let MLKEM_NATIVE_BASEMUL_K2_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem512_polyvec_basemul_acc_montgomery_cached"];;

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

(*** The statements allow a change of X18 as those of the -O2 code do, ***)
(*** though this code does not use X18.                                ***)

let MLKEM_NATIVE_BASEMUL_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc, libmlkem_size); (srcA, 1024); (srcB, 1024); (srcBt, 512)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_gcc12_Os_mc /\
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

let MLKEM_NATIVE_BASEMUL_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_BASEMUL_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_basemul_k2 ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_basemul_k2" subroutine_signatures)
    MLKEM_NATIVE_BASEMUL_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_BASEMUL_K2_GCC12_OS_EXEC;;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e srcA srcB srcBt dst pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (dst,512))
           [word pc,libmlkem_size; srcA,1024; srcB,1024; srcBt,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_Os_mc /\
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

let MLKEM_NATIVE_BASEMUL_K2_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_BASEMUL_K2_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
