(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of polynomials, coefficientwise with wraparound. This is the     *)
(* code for mlkem_poly_add from mlkem-native's portable C implementation     *)
(* compiled by gcc 12 with -Os (see mlkem_native/README.md). The compiler    *)
(* has not vectorized the loop: it adds one 16-bit coefficient per           *)
(* iteration. It is verified in the whole image (see libmlkem.ml).           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_add:
       +0x0: mov     x2, #0x0
       +0x4: ldrh    w3, [x0, x2]
       +0x8: ldrh    w4, [x1, x2]
       +0xc: add     w3, w3, w4
      +0x10: strh    w3, [x0, x2]
      +0x14: add     x2, x2, #0x2
      +0x18: cmp     x2, #0x200
      +0x1c: b.ne    <mlkem_poly_add+0x4>
      +0x20: ret
 ***)

let MLKEM_NATIVE_POLY_ADD_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_add"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r b x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (b,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem_poly_add) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add r (word(2 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes16(word_add b (word(2 * i))))
                             s = y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word_add (x i) (y i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_add_signature =
  ([("r", "int16_t[static 256]", "false");
    ("b", "int16_t[static 256]", "true")],
   "void",
   [("r", "256", 2); ("b", "256", 2)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_add_signature
    MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_ADD_GCC12_OS_EXEC;;

let MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r b pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; b,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                    read PC s = word (pc + mlkem_poly_add) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; b] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events b r pc returnaddress /\
                         memaccess_inbounds e2 [r,512; b,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
