(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Initialization of a context of four SHAKE128 states. This is the code for *)
(* mlkem_shake128x4_init from mlkem-native's portable C implementation       *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which does      *)
(* nothing, since the states are set by mlkem_shake128x4_absorb_once. It is  *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x2a00.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2a00: ret
 ***)

let MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2a00,0x2a04];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!st pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2a00) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st] s)
             (\s. read PC s = returnaddress)
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`,
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e st pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x2a00) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [st] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events pc returnaddress /\
                         memaccess_inbounds e2 [] []))
               MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`,
  PROVE_SAFETY_SPEC_TAC MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O2_EXEC);;
