(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Initialization of a SHAKE128 context: the statement. This is the code for *)
(* mldsa_shake128_init (mld_shake128_init in fips202.c) from mldsa-native's  *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md), which sets the Keccak state, the first 200 bytes *)
(* of the context, and the position, the 32-bit word after it, to zero. It   *)
(* is also shown to be constant time and memory safe.                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_keccak.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake128_init:
       +0x0: movi    v0.4s, #0x0
       +0x4: str     xzr, [x0, #192]
       +0x8: str     wzr, [x0, #200]
       +0xc: stp     q0, q0, [x0]
      +0x10: stp     q0, q0, [x0, #32]
      +0x14: stp     q0, q0, [x0, #64]
      +0x18: stp     q0, q0, [x0, #96]
      +0x1c: stp     q0, q0, [x0, #128]
      +0x20: stp     q0, q0, [x0, #160]
      +0x24: ret
 ***)

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake128_init"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ctx pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (ctx,204) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake128_init) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ctx] s)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes ctx) s = (word 0:1600 word) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(ctx,204)])`;;

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the address of the context only, with all        *)
(* accesses within the context.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e ctx pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (ctx,204) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake128_init) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ctx] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes ctx) s = (word 0:1600 word) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word 0 /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events ctx pc returnaddress /\
                     memaccess_inbounds e2 [ctx,204] [ctx,204]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(ctx,204)])`;;

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e ctx pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (ctx,204) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake128_init) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ctx] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events ctx pc returnaddress /\
                     memaccess_inbounds e2 [ctx,204] [ctx,204]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(ctx,204)])`;;

let MLDSA_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SHAKE128_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
