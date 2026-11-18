(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of polynomial coefficients producing nonnegative remainders.    *)
(* This is the code for mlkem_poly_reduce from mlkem-native's portable C     *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/base.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/layout.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;

(* Names for the labels of this transcription, whose code is at pc.          *)

install_layout (layout_copies
 ["poly_reduce","mlkem_poly_reduce"]);;

(**** print_literal_from_elf
        "arm/mlkem_native/gcc12_O2/poly_reduce.o";;
 ****)

let mlkem_native_poly_reduce_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_poly_reduce_gcc12_O2_mc"
  "arm/mlkem_native/gcc12_O2/poly_reduce.o"
[
  0x91080005;       (* arm_ADD X5 X0 (rvalue (word 512)) *)
  0x5289d7e7;       (* arm_MOV W7 (rvalue (word 20159)) *)
  0x52a04006;       (* arm_MOVZ W6 (word 512) 16 *)
  0x1281a004;       (* arm_MOVN W4 (word 3328) 0 *)
  0x79c00002;       (* arm_LDRSH W2 X0 (Immediate_Offset (word 0)) *)
  0x1b071841;       (* arm_MADD W1 W2 W7 W6 *)
  0x131a7c21;       (* arm_ASR W1 W1 26 *)
  0x1b040821;       (* arm_MADD W1 W1 W4 W2 *)
  0x13003c21;       (* arm_SBFM W1 W1 0 15 *)
  0x2a0103e2;       (* arm_MOV W2 W1 *)
  0x4b4243e2;       (* arm_NEG W2 (Shiftedreg W2 LSR 16) *)
  0x11340423;       (* arm_ADD W3 W1 (rvalue (word 3329)) *)
  0x4a030023;       (* arm_EOR W3 W1 W3 *)
  0x0a824062;       (* arm_AND W2 W3 (Shiftedreg W2 ASR 16) *)
  0x4a020021;       (* arm_EOR W1 W1 W2 *)
  0x78002401;       (* arm_STRH W1 X0 (Postimmediate_Offset (word 2)) *)
  0xeb0000bf;       (* arm_CMP X5 X0 *)
  0x54fffe61;       (* arm_BNE (word 2097100) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_poly_reduce_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* The value computed for each coefficient.                                  *)
(* ------------------------------------------------------------------------- *)

(*** The conditional addition of 3329, mlk_scalar_signed_to_unsigned_q,
 *** as compiled, applied to the 32-bit result w of the Barrett reduction
 ***)

let CONDADD_GCC12_O2_STMT =
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

let CONDADD_GCC12_O2 = assume_spec CONDADD_GCC12_O2_STMT;;

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

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT_STMT =
  `!a x pc.
        nonoverlapping (word pc,poly_reduce_size) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_poly_reduce_gcc12_O2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = word(pc + poly_reduce_ret) /\
                  !i. i < 256
                      ==> ival(read(memory :> bytes16
                                 (word_add a (word(2 * i)))) s) =
                          ival(x i) rem &3329)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_CORRECT_STMT =
  `!a x pc returnaddress.
        nonoverlapping (word pc,poly_reduce_size) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_poly_reduce_gcc12_O2_mc /\
                  read PC s = word pc /\
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

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_reduce ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc returnaddress.
           nonoverlapping (word pc,76) (a,512)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_poly_reduce_gcc12_O2_mc /\
                    read PC s = word pc /\
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

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image (see libmlkem.ml).                       *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_poly_reduce_gcc12_O2_mc
    (layout "mlkem_poly_reduce") [];;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        nonoverlapping (word pc,libmlkem_size) (a,512)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
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

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (word pc,libmlkem_size) (a,512)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
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

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for the      *)
(* modulus check of the encapsulation key, whose result the encapsulation    *)
(* branches on. The loop is that of the correctness proof, but with the loop *)
(* test at the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires,    *)
(* and the version in the image follows.                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a x pc returnaddress.
           nonoverlapping (word pc,poly_reduce_size) (a,512)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_poly_reduce_gcc12_O2_mc /\
                    read PC s = word pc /\
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

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_FULL_STMT;;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a x pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (word pc,libmlkem_size) (a,512)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
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

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
