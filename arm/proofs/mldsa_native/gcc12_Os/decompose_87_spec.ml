(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of one coefficient into high and low parts: the statement.  *)
(* This is the code for mld_decompose87 (mld_decompose in rounding.h for     *)
(* gamma2 = (q - 1) / 32, for ML-DSA-87), from mldsa-native's portable C     *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
(* where it is a function of its own, called by mldsa87_poly_decompose and   *)
(* mldsa87_poly_use_hint (gcc 12 with -O2 inlines it). Its arguments are the *)
(* addresses a0p of the low part and a1p of the high part, and the           *)
(* coefficient a in the low 32 bits of the third register. It is verified in *)
(* the whole image (see libmldsa.ml) against mld_decompose_lo_32 and         *)
(* mld_decompose_hi_32 of common/mldsa_native_rounding.ml, and shown to be   *)
(* constant time and memory safe. It changes only the registers X1 to X3 and *)
(* no flags, which its callers rely on: they keep the state of their loops   *)
(* in X6 and higher registers, which the ABI would allow a callee to change. *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mld_decompose87:
       +0x0: add     w3, w2, #0x7f
       +0x4: asr     w3, w3, #7
       +0x8: add     w3, w3, w3, lsl #10
       +0xc: add     w3, w3, #0x200, lsl #12
      +0x10: ubfx    x3, x3, #22, #4
      +0x14: str     w3, [x1]
      +0x18: mov     w1, #0x3ff000
      +0x1c: sub     w3, w3, w3, lsl #10
      +0x20: add     w2, w2, w3, lsl #9
      +0x24: sub     w1, w1, w2
      +0x28: sxtw    x1, w1
      +0x2c: asr     x1, x1, #31
      +0x30: mov     w3, #0xff801fff
      +0x34: add     w3, w2, w3
      +0x38: eor     w3, w3, w2
      +0x3c: and     w1, w3, w1
      +0x40: eor     w1, w1, w2
      +0x44: str     w1, [x0]
      +0x48: ret
 ***)

let MLDSA_NATIVE_DECOMPOSE_87_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mld_decompose87"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The coefficient is the low 32 bits of a; the high part is    *)
(* written to the 4 bytes at a1p and the low part to the 4 bytes at a0p,     *)
(* which may not overlap each other.                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_DECOMPOSE_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a0p a1p a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a0p,4); (a1p,4); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_decompose87) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a0p; a1p; a] s)
             (\s. read PC s = returnaddress /\
                  read(memory :> bytes32 a1p) s =
                    mld_decompose_hi_32 (word_zx a) /\
                  read(memory :> bytes32 a0p) s =
                    mld_decompose_lo_32 (word_zx a))
             (MAYCHANGE [PC; X1; X2; X3] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a0p,4); memory :> bytes(a1p,4)])`;;

let MLDSA_NATIVE_DECOMPOSE_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_DECOMPOSE_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with the writes within the   *)
(* two outputs and no reads of memory.                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_DECOMPOSE_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a0p a1p a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a0p,4); (a1p,4); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_decompose87) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a0p; a1p; a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read(memory :> bytes32 a1p) s =
                    mld_decompose_hi_32 (word_zx a) /\
                  read(memory :> bytes32 a0p) s =
                    mld_decompose_lo_32 (word_zx a) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a0p a1p pc returnaddress /\
                     memaccess_inbounds e2 [] [a1p,4; a0p,4]))
             (MAYCHANGE [PC; X1; X2; X3] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a0p,4); memory :> bytes(a1p,4)])`;;

let MLDSA_NATIVE_DECOMPOSE_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_DECOMPOSE_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_DECOMPOSE_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a0p a1p a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a0p,4); (a1p,4); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_decompose87) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a0p; a1p; a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a0p a1p pc returnaddress /\
                     memaccess_inbounds e2 [] [a1p,4; a0p,4]))
             (MAYCHANGE [PC; X1; X2; X3] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a0p,4); memory :> bytes(a1p,4)])`;;

let MLDSA_NATIVE_DECOMPOSE_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_DECOMPOSE_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
