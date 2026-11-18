(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time comparison of two byte arrays. This is the code for         *)
(* mlk_ct_memcmp_1 from mlkem-native's portable C implementation compiled by *)
(* gcc 12 with -Os (see mlkem_native/README.md), which XORs the bytes of the *)
(* two arrays pairwise and collects the results into two bytes: the OR of    *)
(* all of them, which is zero if and only if the arrays are equal, and their *)
(* XOR. It turns them into a result that is 0 for equal arrays and 255       *)
(* otherwise, without a branch on the data. With -Os the API functions call  *)
(* it instead of comparing inline. The image has three identical copies      *)
(* mlk_ct_memcmp_1 to mlk_ct_memcmp_3, one for each translation unit of the  *)
(* library. It is verified in the whole image (see libmlkem.ml).             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlk_ct_memcmp_1:
       +0x0: mov     w6, #0x0
       +0x4: mov     w5, #0x0
       +0x8: mov     w3, #0x0
       +0xc: mov     w7, w6
      +0x10: cmp     x2, w6, uxtw
      +0x14: b.hi    <mlk_ct_memcmp_1+0x2c>
      +0x18: neg     w1, w3
      +0x1c: eor     w1, w5, w1, asr #16
      +0x20: and     w1, w1, #0xff
      +0x24: eor     w0, w5, w1
      +0x28: ret
      +0x2c: ldrb    w4, [x0, x7]
      +0x30: add     w6, w6, #0x1
      +0x34: ldrb    w7, [x1, x7]
      +0x38: eor     w4, w4, w7
      +0x3c: and     w4, w4, #0xff
      +0x40: orr     w3, w4, w3
      +0x44: eor     w5, w4, w5
      +0x48: b       <mlk_ct_memcmp_1+0xc>
 ***)

let MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlk_ct_memcmp_1"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The first len bytes at a and b are the numbers n and   *)
(* m. The result is 0 if n = m and 255 otherwise, and the register X2 still  *)
(* holds len, which the callers use to pass the size of the buffers to       *)
(* mlk_zeroize_N. The loop counter is a 32-bit register, so len must be      *)
(* below 2^32. The function reads memory only, so no non-overlap condition   *)
(* is needed. It does not use the stack.                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a b len n m pc returnaddress.
        0 < len /\ len < 2 EXP 32 /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlk_ct_memcmp_1) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; b; word len] s /\
                  read (memory :> bytes(a,len)) s = n /\
                  read (memory :> bytes(b,len)) s = m)
             (\s. read PC s = returnaddress /\
                  C_RETURN s = (if n = m then word 0 else word 255) /\
                  read X2 s = word len)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* addresses, the length and the image, not on the contents of the arrays.   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a b len pc returnaddress.
           0 < len /\ len < 2 EXP 32 /\
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_Os_mc /\
                    read PC s = word (pc + mlk_ct_memcmp_1) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; b; word len] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    read X2 s = word len /\
                    (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a b len pc returnaddress /\
                        memaccess_inbounds e2 [a,len; b,len] []))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for the      *)
(* callers that use the result.                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a b len n m pc returnaddress.
           0 < len /\ len < 2 EXP 32 /\
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_Os_mc /\
                    read PC s = word (pc + mlk_ct_memcmp_1) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; b; word len] s /\
                    read (memory :> bytes(a,len)) s = n /\
                    read (memory :> bytes(b,len)) s = m /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = (if n = m then word 0 else word 255) /\
                    read X2 s = word len /\
                    (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a b len pc returnaddress /\
                        memaccess_inbounds e2 [a,len; b,len] []))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;
