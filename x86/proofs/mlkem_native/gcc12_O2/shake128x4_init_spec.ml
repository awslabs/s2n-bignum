(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Initialization of a context of four SHAKE128 states. This is the code for *)
(* mlkem_shake128x4_init from mlkem-native's portable C implementation       *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which does      *)
(* nothing, since the states are set by mlkem_shake128x4_absorb_once. It is  *)
(* verified in the whole image (see libmlkem.ml).                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128x4_init:
       +0x0: ret
 ***)

let MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_shake128x4_init"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!st pc stackpointer returnaddress.
        aligned 16 (word pc:int64)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_shake128x4_init) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st] s)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e st pc stackpointer returnaddress.
           aligned 16 (word pc:int64)
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_shake128x4_init) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [st] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events pc stackpointer returnaddress /\
                         memaccess_inbounds e2 [stackpointer,8] []))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
