(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Initialization of a context of four SHAKE128 states. This is the code for *)
(* mlkem_shake128x4_init from mlkem-native's portable C implementation       *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md), which does    *)
(* nothing, since the states are set by mlkem_shake128x4_absorb_once. It is  *)
(* verified in the whole image (see libmlkem.ml).                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128x4_init:
      +0x0: ret
 ***)

let MLKEM_NATIVE_SHAKE128X4_INIT_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_shake128x4_init"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_INIT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!st pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_shake128x4_init) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st] s)
             (\s. read PC s = returnaddress)
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`;;

let MLKEM_NATIVE_SHAKE128X4_INIT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128X4_INIT_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_SHAKE128X4_INIT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e st pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_shake128x4_init) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [st] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events pc returnaddress /\
                         memaccess_inbounds e2 [] []))
               MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`;;

let MLKEM_NATIVE_SHAKE128X4_INIT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128X4_INIT_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
