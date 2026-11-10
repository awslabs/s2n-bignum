(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* XOR of bytes into a Keccak state. This is the code for                    *)
(* mldsa_keccakf1600_xor_bytes from mldsa-native's portable C implementation *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which XORs len  *)
(* bytes of data into the 200-byte state starting at byte off. It is         *)
(* verified in the whole image (see libmldsa.ml). It is also shown to be     *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_keccakf1600_xor_bytes:
       +0x0  mov     edx, edx
       +0x2  test    ecx, ecx
       +0x4  je      join1
       +0x6  mov     ecx, ecx
       +0x8  add     rdi, rdx
       +0xb  lea     rdx, [rsi+rcx*1]
       +0xf  nop
     loop1:
      +0x10  movzx   eax, BYTE PTR [rsi]
      +0x13  add     rsi, 0x1
      +0x17  xor     BYTE PTR [rdi], al
      +0x19  add     rdi, 0x1
     loop1_test:
      +0x1d  cmp     rsi, rdx
     loop1_back:
      +0x20  jne     loop1
     join1: loop1_exit: ret:
      +0x22  ret
 ***)

let MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_keccakf1600_xor_bytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a d off len (S:1600 word) m pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (a,200))
            [(word pc,libmldsa_size); (d,len); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600_xor_bytes) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read (memory :> wbytes a) s = S /\
                  read (memory :> bytes(d,len)) s = m)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes a) s =
                  word_xor S (word(2 EXP (8 * off) * m)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,200)])`;;

let MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* state, the data and the slot of the return address, and the writes within *)
(* the state.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a d off len (S:1600 word) m pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (a,200))
            [(word pc,libmldsa_size); (d,len); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600_xor_bytes) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read (memory :> wbytes a) s = S /\
                  read (memory :> bytes(d,len)) s = m /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes a) s =
                  word_xor S (word(2 EXP (8 * off) * m)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a d off len pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,200; d,len; stackpointer,8] [a,200]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,200)])`;;

let MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a d off len pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (a,200))
            [(word pc,libmldsa_size); (d,len); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_keccakf1600_xor_bytes) /\
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
                       [a,200; d,len; stackpointer,8] [a,200]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,200)])`;;

let MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
