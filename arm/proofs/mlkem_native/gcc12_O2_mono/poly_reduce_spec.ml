(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing nonnegative remainders.    *)
(* This is the code for mlk_poly_reduce_c from mlkem-native's portable C     *)
(* implementation compiled by gcc 12 with -O2 as one translation unit (see   *)
(* mlkem_native/README.md), which is the same as mlkem_poly_reduce of the    *)
(* separate -O2 and the -O3 builds, except for a NOP before the loop. It is  *)
(* verified in the whole image (see libmlkem.ml), with the loop invariants   *)
(* of the proof for the -O3 image.                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlk_poly_reduce_c:
       +0x0: add     x5, x0, #0x200
       +0x4: mov     w7, #0x4ebf
       +0x8: mov     w6, #0x2000000
       +0xc: mov     w4, #0xfffff2ff
      +0x10: nop
      +0x14: ldrsh   w2, [x0]
      +0x18: madd    w1, w2, w7, w6
      +0x1c: asr     w1, w1, #26
      +0x20: madd    w1, w1, w4, w2
      +0x24: sxth    w1, w1
      +0x28: mov     w2, w1
      +0x2c: neg     w2, w2, lsr #16
      +0x30: add     w3, w1, #0xd01
      +0x34: eor     w3, w1, w3
      +0x38: and     w2, w3, w2, asr #16
      +0x3c: eor     w1, w1, w2
      +0x40: strh    w1, [x0], #2
      +0x44: cmp     x5, x0
      +0x48: b.ne    <mlk_poly_reduce_c+0x14>
      +0x4c: ret
 ***)

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_poly_reduce_c"];;

(* ------------------------------------------------------------------------- *)
(* The value computed for each coefficient.                                  *)
(* ------------------------------------------------------------------------- *)

(*** The conditional addition of 3329, mlk_scalar_signed_to_unsigned_q,
 *** as compiled, applied to the 32-bit result w of the Barrett reduction
 ***)

let CONDADD_GCC12_O2_MONO_STMT =
  `!w:int32.
     word_zx
      (word_xor (word_sxfrom 15 (word_subword w (0,16):int32))
       (word_and
         (word_xor (word_sxfrom 15 (word_subword w (0,16):int32))
                   (word_add (word_sxfrom 15 (word_subword w (0,16):int32))
                             (word 3329)))
         (word_ishr (word_sub (word 0)
                       (word_ushr (word_sxfrom 15
                                    (word_subword w (0,16):int32)) 16))
                    16))):int16 =
     word_add (word_zx w) (word_and (word_ishr (word_zx w) 15) (word 3329))`;;

let CONDADD_GCC12_O2_MONO = assume_spec CONDADD_GCC12_O2_MONO_STMT;;

let REDUCE_ELEMENT_STMT =
  `!x:int16.
     let w:int32 =
       word_add (word_sx x)
        (word_mul (word_ishr (word_add (word 33554432)
                               (word_mul (word_sx x) (word 20159))) 26)
                  (word 4294963967)) in
     ival(word_zx
      (word_xor (word_sxfrom 15 (word_subword w (0,16):int32))
       (word_and
         (word_xor (word_sxfrom 15 (word_subword w (0,16):int32))
                   (word_add (word_sxfrom 15 (word_subword w (0,16):int32))
                             (word 3329)))
         (word_ishr (word_sub (word 0)
                       (word_ushr (word_sxfrom 15
                                    (word_subword w (0,16):int32)) 16))
                    16))):int16) =
     ival x rem &3329`;;

let REDUCE_ELEMENT = assume_spec REDUCE_ELEMENT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        nonoverlapping (word pc,libmlkem_size) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_poly_reduce_c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_reduce ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_EXEC;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (word pc,libmlkem_size) (a,512)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlk_poly_reduce_c) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc returnaddress /\
                        memaccess_inbounds e2 [a,512] [a,512])
               (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for the      *)
(* modulus check of the encapsulation key, whose result the encapsulation    *)
(* branches on. The loop is that of the correctness proof, but with the loop *)
(* test at the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires.    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a x pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (word pc,libmlkem_size) (a,512)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlk_poly_reduce_c) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    (!i. i < 256
                         ==> read(memory :> bytes16
                                   (word_add a (word(2 * i)))) s = x i) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> ival(read(memory :> bytes16
                                    (word_add a (word(2 * i)))) s) =
                             ival(x i) rem &3329) /\
                    (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc returnaddress /\
                        memaccess_inbounds e2 [a,512] [a,512]))
               (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_STMT;;
