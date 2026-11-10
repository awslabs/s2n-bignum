(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 6 bits per coefficient: the statement.     *)
(* This is the code for mldsa_polyw1_unpack_88 (mld_polyw1_unpack_88 in      *)
(* poly.c, for ML-DSA-44) from mldsa-native's portable C implementation      *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which reads 3   *)
(* bytes for each 4 coefficients. It is verified in the whole image (see     *)
(* libmldsa.ml) against mld_polyw1_unpack_88 of                              *)
(* common/mldsa_native_packing.ml. It is also shown to be constant time and  *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyw1_unpack_88:
       +0x0  mov     rcx, rdi
       +0x3  mov     rdx, rsi
       +0x6  lea     rdi, [rsi+0xc0]
       +0xd  nop     DWORD PTR [rax]
     loop1:
      +0x10  movzx   eax, BYTE PTR [rdx]
      +0x13  add     rdx, 0x3
      +0x17  add     rcx, 0x10
      +0x1b  and     eax, 0x3f
      +0x1e  mov     DWORD PTR [rcx-0x10], eax
      +0x21  movzx   eax, BYTE PTR [rdx-0x3]
      +0x25  movzx   esi, BYTE PTR [rdx-0x2]
      +0x29  shr     al, 0x6
      +0x2c  shl     esi, 0x2
      +0x2f  movzx   eax, al
      +0x32  or      eax, esi
      +0x34  and     eax, 0x3f
      +0x37  mov     DWORD PTR [rcx-0xc], eax
      +0x3a  movzx   eax, BYTE PTR [rdx-0x2]
      +0x3e  movzx   esi, BYTE PTR [rdx-0x1]
      +0x42  shr     al, 0x4
      +0x45  movzx   eax, al
      +0x48  shl     esi, 0x4
      +0x4b  or      eax, esi
      +0x4d  and     eax, 0x3f
      +0x50  mov     DWORD PTR [rcx-0x8], eax
      +0x53  movzx   eax, BYTE PTR [rdx-0x1]
      +0x57  shr     al, 0x2
      +0x5a  movzx   eax, al
      +0x5d  mov     DWORD PTR [rcx-0x4], eax
     loop1_test:
      +0x60  cmp     rdx, rdi
     loop1_back:
      +0x63  jne     loop1
     loop1_exit: ret:
      +0x65  ret
 ***)

let MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyw1_unpack_88"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,192); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyw1_unpack_88) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 192
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyw1_unpack_88 b i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,192); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyw1_unpack_88) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 192
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyw1_unpack_88 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,192; r,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,192); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyw1_unpack_88) /\
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
                       [a,192; r,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
