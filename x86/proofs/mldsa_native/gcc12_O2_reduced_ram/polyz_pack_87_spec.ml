(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 20 bits per coefficient, of 2^19 - a: the    *)
(* statement. This is the code for mldsa87_polyz_pack (mld_polyz_pack in     *)
(* poly_kl.c with MLDSA_GAMMA1 = 2^19, for ML-DSA-87) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -O2 and                 *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which writes 5 bytes  *)
(* for each 2 coefficients, 4 of them as one 32-bit word. It is verified in  *)
(* the whole image (see libmldsa.ml) against mld_polyz_pack_19 of            *)
(* common/mldsa_native_packing.ml, byte by byte. It is also shown to be      *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyz_pack:
       +0x0  push    rbx
       +0x1  mov     rax, rdi
       +0x4  mov     r8d, 0x80000
       +0xa  mov     rdi, rsi
       +0xd  lea     r9, [rax+0x280]
      +0x14  mov     rsi, rax
      +0x17  nop     WORD PTR [rax+rax*1+0x0]
     loop1:
      +0x20  mov     ecx, r8d
      +0x23  mov     edx, r8d
      +0x26  sub     ecx, DWORD PTR [rdi]
      +0x28  sub     edx, DWORD PTR [rdi+0x4]
      +0x2b  mov     eax, ecx
      +0x2d  mov     r10d, edx
      +0x30  movzx   ebx, ch
      +0x33  movzx   ecx, cl
      +0x36  shr     eax, 0x10
      +0x39  shl     r10d, 0x4
      +0x3d  add     rsi, 0x5
      +0x41  add     rdi, 0x8
      +0x45  or      r10d, eax
      +0x48  mov     eax, edx
      +0x4a  shr     edx, 0xc
      +0x4d  shl     eax, 0x4
      +0x50  movzx   r10d, r10b
      +0x54  mov     BYTE PTR [rsi-0x1], dl
      +0x57  and     eax, 0xff00
      +0x5c  or      eax, r10d
      +0x5f  shl     eax, 0x8
      +0x62  or      eax, ebx
      +0x64  shl     eax, 0x8
      +0x67  or      eax, ecx
      +0x69  mov     DWORD PTR [rsi-0x5], eax
     loop1_test:
      +0x6c  cmp     r9, rsi
     loop1_back:
      +0x6f  jne     loop1
     loop1_exit:
      +0x71  pxor    xmm0, xmm0
      +0x75  lea     rax, [rsp-0x10]
      +0x7a  movaps  XMMWORD PTR [rsp-0x10], xmm0
      +0x7f  pop     rbx
     ret:
      +0x80  ret
 ***)

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa87_polyz_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The function saves RBX, which it uses, in the 8 bytes below  *)
(* the return address, and clears the 16 bytes below them, the temporary     *)
(* array that mld_polyz_pack zeroizes, with an aligned SSE store (so the     *)
(* frame is 24 bytes). The store faults unless RSP + 8 is a multiple of 16   *)
(* on entry, as the ABI requires, which the statements assume.               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 (word_add stackpointer (word 8)) /\
        ALL (nonoverlapping (r,640))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 24),24); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_polyz_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 640
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyz_pack_19 x j)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,640);
                memory :> bytes(word_sub stackpointer (word 24),24)])`;;

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs, the stack frame and the slot of the return address,   *)
(* and the writes within the outputs and the stack frame.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 (word_add stackpointer (word 8)) /\
        ALL (nonoverlapping (r,640))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 24),24); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_polyz_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 640
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyz_pack_19 x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 24))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; r,640; word_sub stackpointer (word 24),24;
                        stackpointer,8]
                       [r,640; word_sub stackpointer (word 24),24]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,640);
                memory :> bytes(word_sub stackpointer (word 24),24)])`;;

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 (word_add stackpointer (word 8)) /\
        ALL (nonoverlapping (r,640))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 24),24); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),24))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa87_polyz_pack) /\
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
                       [a,1024; r,640; word_sub stackpointer (word 24),24;
                        stackpointer,8]
                       [r,640; word_sub stackpointer (word 24),24]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,640);
                memory :> bytes(word_sub stackpointer (word 24),24)])`;;

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
