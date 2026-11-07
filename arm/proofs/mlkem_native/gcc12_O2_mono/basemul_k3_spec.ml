(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of 3-element polynomial vectors in NTT domain. This is     *)
(* the code for mlk_polyvec_basemul_acc_montgomery_cached_c768 from          *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 as   *)
(* one translation unit (see mlkem_native/README.md). It computes the same   *)
(* as mlkem768_polyvec_basemul_acc_montgomery_cached of the separate -O2     *)
(* build, but the compiler has allocated registers differently. It is        *)
(* verified in the whole image (see libmlkem.ml), with the proof for the     *)
(* separate -O2 build adapted to the image.                                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlk_polyvec_basemul_acc_montgomery_cached_c768:
       +0x0: mov     x10, x1
       +0x4: mov     x11, x2
       +0x8: mov     x14, x3
       +0xc: add     x13, x1, #0x2
      +0x10: mov     x15, x0
      +0x14: add     x12, x2, #0x2
      +0x18: add     x18, x3, #0x100
      +0x1c: mov     w17, #0xfffff301
      +0x20: mov     w16, #0xfffff2ff
      +0x24: nop
      +0x28: mov     x4, x14
      +0x2c: mov     x0, #0x0
      +0x30: mov     w6, #0x0
      +0x34: mov     w5, #0x0
      +0x38: ldrsh   w8, [x13, x0]     <+ |
      +0x3c: add     x4, x4, #0x100     | |
      +0x40: ldrsh   w7, [x10, x0]      | |
      +0x44: ldrsh   w1, [x11, x0]      | |
      +0x48: ldrsh   w2, [x12, x0]      | |
      +0x4c: add     x0, x0, #0x200     | |
      +0x50: ldursh  w3, [x4, #-256]    | |
      +0x54: mul     w9, w7, w1         | |
      +0x58: mul     w1, w8, w1         | |
      +0x5c: madd    w3, w3, w8, w9     | |
      +0x60: madd    w1, w2, w7, w1     | |
      +0x64: add     w5, w5, w3         | |
      +0x68: add     w6, w6, w1         | |
      +0x6c: cmp     x0, #0x600         | |
      +0x70: b.ne    <mlk_polyvec_basemul_acc_montgomery_cached_c768+0x38>             -+ |
      +0x74: mul     w1, w5, w17
      +0x78: add     x14, x14, #0x2
      +0x7c: mul     w0, w6, w17
      +0x80: add     x13, x13, #0x4
      +0x84: add     x10, x10, #0x4
      +0x88: add     x11, x11, #0x4
      +0x8c: sxth    w1, w1
      +0x90: add     x12, x12, #0x4
      +0x94: sxth    w0, w0
      +0x98: add     x15, x15, #0x4
      +0x9c: madd    w1, w1, w16, w5
      +0xa0: madd    w0, w0, w16, w6
      +0xa4: asr     w1, w1, #16
      +0xa8: sturh   w1, [x15, #-4]
      +0xac: asr     w0, w0, #16
      +0xb0: sturh   w0, [x15, #-2]
      +0xb4: cmp     x18, x14
      +0xb8: b.ne    <mlk_polyvec_basemul_acc_montgomery_cached_c768+0x28>
      +0xbc: ret
 ***)

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_polyvec_basemul_acc_montgomery_cached_c768"];;

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
  REWRITE_TAC[basemul3_even; basemul3_odd;
              pmul_acc3; pmull_acc3; pmull; o_THM] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING;;

(*** Unlike mlkem_basemul_k3, this uses X18 as a temporary register ***)

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_CORRECT_STMT =
  `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t pc.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc,libmlkem_size); (srcA, 1536); (srcB, 1536); (srcBt, 768)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_gcc12_O2_mono_mc /\
            read PC s = word (pc + mlk_polyvec_basemul_acc_montgomery_cached_c768) /\
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
       (\s. read PC s = word (pc + mlk_polyvec_basemul_acc_montgomery_cached_c768_ret) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul3_even
                            (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                            (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                            (ival o y2t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul3_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2)
                            i) (mod &3329))))
       (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                   X12; X13; X14; X15; X16; X17; X18] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_CORRECT =
  assume_spec MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_CORRECT_STMT;;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc,libmlkem_size); (srcA, 1536); (srcB, 1536); (srcBt, 768)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_gcc12_O2_mono_mc /\
            read PC s = word (pc + mlk_polyvec_basemul_acc_montgomery_cached_c768) /\
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
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i))
       (\s. read PC s = returnaddress /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul3_even
                            (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                            (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                            (ival o y2t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul3_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2)
                            i) (mod &3329))))
       (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                   X12; X13; X14; X15; X16; X17; X18] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_basemul_k3 ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_basemul_k3" subroutine_signatures)
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_EXEC;;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e srcA srcB srcBt dst pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (dst,512))
           [word pc,libmlkem_size; srcA,1536; srcB,1536; srcBt,768]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlk_polyvec_basemul_acc_montgomery_cached_c768) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events srcA srcB srcBt dst pc returnaddress /\
                        memaccess_inbounds e2
                         [srcA,1536; srcB,1536; srcBt,768; dst,512]
                         [dst,512])
               (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                           X11; X12; X13; X14; X15; X16; X17; X18] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image (see libmlkem.ml).                       *)
(* ------------------------------------------------------------------------- *)

