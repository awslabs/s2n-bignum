(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extraction of bytes from a Keccak state. This is the code for             *)
(* mldsa_keccakf1600_extract_bytes from mldsa-native's portable C            *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which copies len bytes of the 200-byte state starting at byte off. It is  *)
(* verified in the whole image (see libmldsa.ml). It is also shown to be     *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_keccakf1600_extract_bytes:
       +0x0  mov     edx, edx
       +0x2  test    ecx, ecx
       +0x4  je      join1
       +0x6  mov     ecx, ecx
       +0x8  xor     eax, eax
       +0xa  add     rdi, rdx
       +0xd  nop     DWORD PTR [rax]
     loop1:
      +0x10  movzx   edx, BYTE PTR [rdi+rax*1]
      +0x14  mov     BYTE PTR [rsi+rax*1], dl
      +0x17  add     rax, 0x1
     loop1_test:
      +0x1b  cmp     rcx, rax
     loop1_back:
      +0x1e  jne     loop1
     join1: loop1_exit: ret:
      +0x20  ret
 ***)

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_keccakf1600_extract_bytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a d off len (S:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (d,len))
            [(word pc,libmldsa_size); (a,200); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600_extract_bytes) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read (memory :> wbytes a) s = S)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(d,len)) s =
                  (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d,len)])`;;

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* state, the output and the slot of the return address, and the writes      *)
(* within the output.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a d off len (S:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (d,len))
            [(word pc,libmldsa_size); (a,200); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600_extract_bytes) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read (memory :> wbytes a) s = S /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(d,len)) s =
                  (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a d off len pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,200; d,len; stackpointer,8] [d,len]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d,len)])`;;

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a d off len pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (d,len))
            [(word pc,libmldsa_size); (a,200); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600_extract_bytes) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a d off len pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,200; d,len; stackpointer,8] [d,len]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d,len)])`;;

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
