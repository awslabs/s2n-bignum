(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 6 bits per coefficient: the statement. This  *)
(* is the code for mldsa_polyw1_pack_88 (mld_polyw1_pack_88 in poly.c, for   *)
(* ML-DSA-44) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which writes 3 bytes for each 4 *)
(* coefficients, as the C code does first the low part of each byte and then *)
(* the whole byte. It is verified in the whole image (see libmldsa.ml)       *)
(* against mld_polyw1_pack_88 of common/mldsa_native_packing.ml, byte by     *)
(* byte. It is also shown to be constant time and memory safe.               *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyw1_pack_88:
       +0x0  lea     rcx, [rdi+0xc0]
       +0x7  nop     WORD PTR [rax+rax*1+0x0]
     loop1:
      +0x10  mov     eax, DWORD PTR [rsi]
      +0x12  add     rdi, 0x3
      +0x16  add     rsi, 0x10
      +0x1a  mov     BYTE PTR [rdi-0x3], al
      +0x1d  mov     edx, DWORD PTR [rsi-0xc]
      +0x20  shl     edx, 0x6
      +0x23  or      eax, edx
      +0x25  mov     BYTE PTR [rdi-0x3], al
      +0x28  mov     eax, DWORD PTR [rsi-0xc]
      +0x2b  sar     eax, 0x2
      +0x2e  mov     BYTE PTR [rdi-0x2], al
      +0x31  mov     edx, DWORD PTR [rsi-0x8]
      +0x34  shl     edx, 0x4
      +0x37  or      eax, edx
      +0x39  mov     BYTE PTR [rdi-0x2], al
      +0x3c  mov     eax, DWORD PTR [rsi-0x8]
      +0x3f  sar     eax, 0x4
      +0x42  mov     BYTE PTR [rdi-0x1], al
      +0x45  mov     edx, DWORD PTR [rsi-0x4]
      +0x48  shl     edx, 0x2
      +0x4b  or      eax, edx
      +0x4d  mov     BYTE PTR [rdi-0x1], al
     loop1_test:
      +0x50  cmp     rdi, rcx
     loop1_back:
      +0x53  jne     loop1
     loop1_exit: ret:
      +0x55  ret
 ***)

let MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyw1_pack_88"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,192))
            [(word pc,libmldsa_size); (a,1024); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyw1_pack_88) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 192
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyw1_pack_88 x j)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,192)])`;;

let MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,192))
            [(word pc,libmldsa_size); (a,1024); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyw1_pack_88) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 192
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyw1_pack_88 x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; r,192; stackpointer,8] [r,192]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,192)])`;;

let MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,192))
            [(word pc,libmldsa_size); (a,1024); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyw1_pack_88) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; r,192; stackpointer,8] [r,192]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,192)])`;;

let MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
