(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 3 bits per coefficient, of 2 - a: the        *)
(* statement. This is the code for mldsa87_polyeta_pack (mld_polyeta_pack in *)
(* poly_kl.c with MLDSA_ETA = 2, for ML-DSA-87) from mldsa-native's portable *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mldsa_native/README.md), which writes 3 bytes for each 8 coefficients. It *)
(* is verified in the whole image (see libmldsa.ml) against                  *)
(* mld_polyeta_pack_2 of common/mldsa_native_packing.ml, byte by byte. It is *)
(* also shown to be constant time and memory safe.                           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyeta_pack:
       +0x0  push    r12
       +0x2  mov     rax, rsi
       +0x5  mov     r8, rdi
       +0x8  lea     r9, [rsi+0x400]
       +0xf  push    rbp
      +0x10  mov     edx, 0x2
      +0x15  push    rbx
      +0x16  cs nop  WORD PTR [rax+rax*1+0x0]
     loop1:
      +0x20  mov     r11d, edx
      +0x23  sub     r11b, BYTE PTR [rax+0x8]
      +0x27  mov     r12d, edx
      +0x2a  sub     r12b, BYTE PTR [rax+0x4]
      +0x2e  mov     edi, r11d
      +0x31  shl     r12d, 0x3
      +0x35  mov     ebp, edx
      +0x37  mov     esi, edx
      +0x39  shl     edi, 0x6
      +0x3c  sub     bpl, BYTE PTR [rax+0xc]
      +0x40  sub     sil, BYTE PTR [rax+0x10]
      +0x44  mov     r10d, edx
      +0x47  or      edi, r12d
      +0x4a  mov     r12d, edx
      +0x4d  sub     r12b, BYTE PTR [rax]
      +0x50  sub     r10b, BYTE PTR [rax+0x14]
      +0x54  or      edi, r12d
      +0x57  mov     ebx, edx
      +0x59  mov     ecx, edx
      +0x5b  sub     bl, BYTE PTR [rax+0x18]
      +0x5e  sub     cl, BYTE PTR [rax+0x1c]
      +0x61  shl     esi, 0x4
      +0x64  mov     BYTE PTR [r8], dil
      +0x67  lea     edi, [rbp+rbp*1+0x0]
      +0x6b  or      esi, edi
      +0x6d  shr     r11b, 0x2
      +0x71  mov     edi, r10d
      +0x74  add     rax, 0x20
      +0x78  shl     ebx, 0x2
      +0x7b  shl     ecx, 0x5
      +0x7e  or      esi, r11d
      +0x81  add     r8, 0x3
      +0x85  shl     edi, 0x7
      +0x88  or      ecx, ebx
      +0x8a  shr     r10b, 1
      +0x8d  or      esi, edi
      +0x8f  or      ecx, r10d
      +0x92  mov     BYTE PTR [r8-0x2], sil
      +0x96  mov     BYTE PTR [r8-0x1], cl
     loop1_test:
      +0x9a  cmp     r9, rax
     loop1_back:
      +0x9d  jne     loop1
     loop1_exit:
      +0x9f  pop     rbx
      +0xa0  pop     rbp
      +0xa1  pop     r12
     ret:
      +0xa3  ret
 ***)

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_polyeta_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The function saves R12, RBP and RBX, which it uses, in the   *)
(* 24 bytes below the return address.                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,96))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 24),24); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_polyeta_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 96
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyeta_pack_2 x j)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,96);
                memory :> bytes(word_sub stackpointer (word 24),24)])`;;

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs, the stack frame and the slot of the return address,   *)
(* and the writes within the outputs and the stack frame.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,96))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 24),24); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_polyeta_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyeta_pack_2 x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 24))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; r,96; word_sub stackpointer (word 24),24;
                        stackpointer,8]
                       [r,96; word_sub stackpointer (word 24),24]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,96);
                memory :> bytes(word_sub stackpointer (word 24),24)])`;;

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,96))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 24),24); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_polyeta_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 24))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; r,96; word_sub stackpointer (word 24),24;
                        stackpointer,8]
                       [r,96; word_sub stackpointer (word 24),24]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,96);
                memory :> bytes(word_sub stackpointer (word 24),24)])`;;

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYETA_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
