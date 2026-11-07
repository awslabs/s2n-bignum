(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Initialization of a context of four SHAKE256 states. This is the code for *)
(* mldsa_shake256x4_init from mldsa-native's portable C implementation       *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which does      *)
(* nothing, since the states are set by mldsa_shake256x4_absorb_once. It is  *)
(* verified in the whole image (see libmldsa.ml).                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake256x4_init:
       +0x0: ret
 ***)

let MLDSA_NATIVE_SHAKE256X4_INIT_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake256x4_init"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake256x4_init) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st] s)
             (\s. read PC s = returnaddress)
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`;;

let MLDSA_NATIVE_SHAKE256X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SHAKE256X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
