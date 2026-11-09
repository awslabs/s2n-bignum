(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Copying the challenge seed c~ of 32 bytes to the start of a signature:    *)
(* the statement. This is the code for mldsa44_pack_sig_c (mld_pack_sig_c    *)
(* in packing.c) from mldsa-native's portable C implementation compiled by   *)
(* gcc 12 with -O2 (see mldsa_native/README.md), in which the call of        *)
(* memcpy is inlined. It is verified in the whole image (see libmldsa.ml),   *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_pack_sig_c:
       +0x0: ldp     q0, q1, [x1]
       +0x4: stp     q0, q1, [x0]
       +0x8: ret
 ***)

let MLDSA_NATIVE_PACK_SIG_C_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_pack_sig_c"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 32 bytes b at c, which may not overlap the first 32      *)
(* bytes of the signature at sig, are copied there.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_C_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sig c b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (sig,32)) [(word pc,libmldsa_size); (c,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_pack_sig_c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sig; c] s /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add c (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  !j. j < 32
                      ==> read(memory :> bytes8(word_add sig (word j))) s =
                          b j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(sig,32)])`;;

let MLDSA_NATIVE_PACK_SIG_C_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PACK_SIG_C_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_C_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e sig c b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (sig,32)) [(word pc,libmldsa_size); (c,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_pack_sig_c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sig; c] s /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add c (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add sig (word j))) s =
                           b j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sig c pc returnaddress /\
                     memaccess_inbounds e2 [c,32; sig,32] [sig,32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(sig,32)])`;;

let MLDSA_NATIVE_PACK_SIG_C_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PACK_SIG_C_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_C_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e sig c pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (sig,32)) [(word pc,libmldsa_size); (c,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_pack_sig_c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sig; c] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sig c pc returnaddress /\
                     memaccess_inbounds e2 [c,32; sig,32] [sig,32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(sig,32)])`;;

let MLDSA_NATIVE_PACK_SIG_C_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PACK_SIG_C_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
