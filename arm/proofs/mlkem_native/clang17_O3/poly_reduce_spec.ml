(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing nonnegative remainders.    *)
(* This is the code for mlkem_poly_reduce from mlkem-native's portable C     *)
(* implementation compiled by clang 17 with -O3 (see                         *)
(* mlkem_native/README.md), which is the same as with -O2. It is verified in *)
(* the whole image (see libmlkem.ml).                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_reduce:
       +0x0: mov     x8, xzr
       +0x4: mov     w9, #0x4ebf
       +0x8: mov     w10, #0x2000000
       +0xc: mov     w11, #0xfffff2ff
      +0x10: ldrsh   w12, [x0, x8]
      +0x14: madd    w13, w12, w9, w10
      +0x18: asr     w13, w13, #26
      +0x1c: madd    w12, w13, w11, w12
      +0x20: sxth    w13, w12
      +0x24: add     w14, w12, #0xd01
      +0x28: neg     w13, w13, lsr #16
      +0x2c: lsr     w13, w13, #16
      +0x30: bic     w12, w12, w13
      +0x34: and     w13, w14, w13
      +0x38: orr     w12, w13, w12
      +0x3c: strh    w12, [x0, x8]
      +0x40: add     x8, x8, #0x2
      +0x44: cmp     x8, #0x200
      +0x48: b.ne    <mlkem_poly_reduce+0x10>
      +0x4c: ret
 ***)

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_reduce"];;

(* ------------------------------------------------------------------------- *)
(* The value computed for each coefficient.                                  *)
(* ------------------------------------------------------------------------- *)

(*** The conditional addition of 3329, mlk_scalar_signed_to_unsigned_q,
 *** as compiled, applied to the 32-bit result w of the Barrett reduction
 ***)

let CONDADD_CLANG17_O3_STMT =
  `!w:int32.
     word_zx
      (word_or
        (word_and (word_add w (word 3329))
          (word_ushr (word_sub (word 0)
                        (word_ushr (word_sxfrom 15
                                     (word_subword w (0,16):int32)) 16))
                     16))
        (word_and w
          (word_not
            (word_ushr (word_sub (word 0)
                          (word_ushr (word_sxfrom 15
                                       (word_subword w (0,16):int32)) 16))
                       16)))):int16 =
     word_add (word_zx w) (word_and (word_ishr (word_zx w) 15) (word 3329))`;;

let CONDADD_CLANG17_O3 = assume_spec CONDADD_CLANG17_O3_STMT;;

let REDUCE_ELEMENT_STMT =
  `!x:int16.
     let w:int32 =
       word_add (word_sx x)
        (word_mul (word_ishr (word_add (word 33554432)
                               (word_mul (word_sx x) (word 20159))) 26)
                  (word 4294963967)) in
     ival(word_zx
      (word_or
        (word_and (word_add w (word 3329))
          (word_ushr (word_sub (word 0)
                        (word_ushr (word_sxfrom 15
                                     (word_subword w (0,16):int32)) 16))
                     16))
        (word_and w
          (word_not
            (word_ushr (word_sub (word 0)
                          (word_ushr (word_sxfrom 15
                                       (word_subword w (0,16):int32)) 16))
                       16)))):int16) =
     ival x rem &3329`;;

let REDUCE_ELEMENT = assume_spec REDUCE_ELEMENT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        nonoverlapping (word pc,libmlkem_size) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_reduce) /\
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
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_reduce ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (word pc,libmlkem_size) (a,512)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_reduce) /\
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

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for the      *)
(* modulus check of the encapsulation key, whose result the encapsulation    *)
(* branches on. The loop is that of the correctness proof, but with the loop *)
(* test at the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires.    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a x pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (word pc,libmlkem_size) (a,512)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_reduce) /\
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
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT;;
