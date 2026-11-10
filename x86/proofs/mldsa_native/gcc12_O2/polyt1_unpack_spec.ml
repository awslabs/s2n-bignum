(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 10 bits per coefficient: the statement.    *)
(* This is the code for mldsa_polyt1_unpack (mld_polyt1_unpack in poly.c)    *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which reads 5 bytes for each 4              *)
(* coefficients. It is verified in the whole image (see libmldsa.ml) against *)
(* mld_polyt1_unpack of common/mldsa_native_packing.ml. It is also shown to  *)
(* be constant time and memory safe.                                         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyt1_unpack:
       +0x0  mov     rax, rsi
       +0x3  mov     rcx, rdi
       +0x6  lea     rsi, [rsi+0x140]
       +0xd  nop     DWORD PTR [rax]
     loop1:
      +0x10  movzx   edx, BYTE PTR [rax+0x1]
      +0x14  movzx   edi, BYTE PTR [rax]
      +0x17  add     rax, 0x5
      +0x1b  add     rcx, 0x10
      +0x1f  shl     edx, 0x8
      +0x22  or      edx, edi
      +0x24  and     edx, 0x3ff
      +0x2a  mov     DWORD PTR [rcx-0x10], edx
      +0x2d  movzx   edx, BYTE PTR [rax-0x4]
      +0x31  movzx   edi, BYTE PTR [rax-0x3]
      +0x35  shr     dl, 0x2
      +0x38  shl     edi, 0x6
      +0x3b  movzx   edx, dl
      +0x3e  or      edx, edi
      +0x40  and     edx, 0x3ff
      +0x46  mov     DWORD PTR [rcx-0xc], edx
      +0x49  movzx   edx, BYTE PTR [rax-0x3]
      +0x4d  movzx   edi, BYTE PTR [rax-0x2]
      +0x51  shr     dl, 0x4
      +0x54  shl     edi, 0x4
      +0x57  movzx   edx, dl
      +0x5a  or      edx, edi
      +0x5c  and     edx, 0x3ff
      +0x62  mov     DWORD PTR [rcx-0x8], edx
      +0x65  movzx   edx, BYTE PTR [rax-0x2]
      +0x69  movzx   edi, BYTE PTR [rax-0x1]
      +0x6d  shr     dl, 0x6
      +0x70  movzx   edx, dl
      +0x73  shl     edi, 0x2
      +0x76  or      edx, edi
      +0x78  mov     DWORD PTR [rcx-0x4], edx
     loop1_test:
      +0x7b  cmp     rsi, rax
     loop1_back:
      +0x7e  jne     loop1
     loop1_exit: ret:
      +0x80  ret
 ***)

let MLDSA_NATIVE_POLYT1_UNPACK_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyt1_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT1_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,320); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyt1_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 320
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyt1_unpack b i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYT1_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYT1_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT1_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,320); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyt1_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 320
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyt1_unpack b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,320; r,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYT1_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYT1_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT1_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,320); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyt1_unpack) /\
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
                       [a,320; r,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYT1_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYT1_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
