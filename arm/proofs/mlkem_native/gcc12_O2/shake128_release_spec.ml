(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Release of a SHAKE128 context. This is the code for                       *)
(* mlkem_shake128_release from mlkem-native's portable C implementation      *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which zeroes    *)
(* the context of 224 bytes, the 200 bytes of the state padded to a multiple *)
(* of 32. It is verified in the whole image (see                             *)
(* libmlkem.ml).                                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128_release:
       +0x0: movi    v0.4s, #0x0
       +0x4: stp     q0, q0, [x0]
       +0x8: stp     q0, q0, [x0, #32]
       +0xc: stp     q0, q0, [x0, #64]
      +0x10: stp     q0, q0, [x0, #96]
      +0x14: stp     q0, q0, [x0, #128]
      +0x18: stp     q0, q0, [x0, #160]
      +0x1c: stp     q0, q0, [x0, #192]
      +0x20: ret
 ***)

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem_shake128_release"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!st pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        nonoverlapping (st,224) (word pc,libmlkem_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem_shake128_release) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st] s)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(st,224)) s = 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(st,224)])`;;

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e st pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           nonoverlapping (st,224) (word pc,libmlkem_size)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem_shake128_release) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [st] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events st pc returnaddress /\
                         memaccess_inbounds e2 [st,224] [st,224]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(st,224)])`;;

let MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
