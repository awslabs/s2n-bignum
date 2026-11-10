(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Zeroing a context of four SHAKE256 states. This is the code for           *)
(* mldsa_shake256x4_release from mldsa-native's portable C implementation    *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which zeroes    *)
(* the 800 bytes of the context. Unlike the AArch64 code, which calls memset *)
(* from the C library, it has the memset inlined, with REP STOSQ, so the     *)
(* direction flag must be clear, as the ABI requires on entry. It is         *)
(* verified in the whole image (see libmldsa.ml). It is also shown to be     *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake256x4_release:
       +0x0  mov     QWORD PTR [rdi], 0x0
       +0x7  mov     rdx, rdi
       +0xa  lea     rdi, [rdi+0x8]
       +0xe  xor     eax, eax
      +0x10  mov     QWORD PTR [rdi+0x310], 0x0
      +0x1b  mov     rcx, rdx
      +0x1e  and     rdi, 0xfffffffffffffff8
      +0x22  sub     rcx, rdi
      +0x25  add     ecx, 0x320
      +0x2b  shr     ecx, 0x3
      +0x2e  rep stos QWORD PTR es:[rdi], rax
     ret:
      +0x31  ret
 ***)

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake256x4_release"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (st,800))
            [(word pc,libmldsa_size); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256x4_release) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st] s /\
                  (read DF s <=> false))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(st,800)) s = 0)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(st,800)])`;;

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the address of the context only, with all        *)
(* accesses within the context and the slot of the return address, and the   *)
(* writes within the context.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e st pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (st,800))
            [(word pc,libmldsa_size); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256x4_release) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st] s /\
                  (read DF s <=> false) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(st,800)) s = 0 /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events st pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [st,800; stackpointer,8] [st,800]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(st,800)])`;;

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e st pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (st,800))
            [(word pc,libmldsa_size); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256x4_release) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [st] s /\
                  (read DF s <=> false) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events st pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [st,800; stackpointer,8] [st,800]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(st,800)])`;;

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
