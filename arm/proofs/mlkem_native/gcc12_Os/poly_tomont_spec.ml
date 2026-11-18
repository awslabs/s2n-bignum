(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of polynomial coefficients to Montgomery form. This is the     *)
(* code for mlkem_poly_tomont from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -Os (see mlkem_native/README.md). The compiler    *)
(* has not vectorized the loop: it multiplies and reduces one 16-bit         *)
(* coefficient per iteration, with the scalar Montgomery reduction           *)
(* (montred_scalar), and the code has no read-only data. It is verified in   *)
(* the whole image (see libmlkem.ml).                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_tomont:
       +0x0: mov     x2, #0x0
       +0x4: mov     w6, #0x549
       +0x8: mov     w5, #0xfffff301
       +0xc: mov     w4, #0xfffff2ff
      +0x10: ldrsh   w3, [x0, x2, lsl #1]
      +0x14: mul     w3, w3, w6
      +0x18: mul     w1, w3, w5
      +0x1c: sxth    w1, w1
      +0x20: madd    w1, w1, w4, w3
      +0x24: asr     w1, w1, #16
      +0x28: strh    w1, [x0, x2, lsl #1]
      +0x2c: add     x2, x2, #0x1
      +0x30: cmp     x2, #0x100
      +0x34: b.ne    <mlkem_poly_tomont+0x10>
      +0x38: ret
 ***)

let MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_tomont"];;

(* ------------------------------------------------------------------------- *)
(* The value computed in each lane.                                          *)
(* ------------------------------------------------------------------------- *)

let TOMONT_LANE_STMT =
  `!x:int16.
     (ival(montred_scalar(word_mul (word_sx x) (word 1353))) ==
      (&2 pow 16 * ival x) rem &3329) (mod &3329) /\
     abs(ival(montred_scalar(word_mul (word_sx x) (word 1353)))) <= &3328`;;

let TOMONT_LANE = assume_spec TOMONT_LANE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_Os_mc /\
           read PC s = word (pc + mlkem_poly_tomont) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word (2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 256
               ==> let z_i = read(memory :> bytes16
                                (word_add a (word (2 * i)))) s in
                   (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The signature is the same as for mlkem_tomont ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_tomont" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_EXEC;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (a,512) (word pc,libmlkem_size)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     mlkem_native_libmlkem_gcc12_Os_mc /\
                    read PC s = word (pc + mlkem_poly_tomont) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a pc returnaddress /\
                        memaccess_inbounds e2 [a,512] [a,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
