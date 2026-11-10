(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 4 bits per coefficient: the statement.     *)
(* This is the code for mldsa_polyw1_unpack_32 (mld_polyw1_unpack_32 in      *)
(* poly.c, for ML-DSA-65 and ML-DSA-87) from mldsa-native's portable C       *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which reads a byte for each 2 coefficients. It is verified in the whole   *)
(* image (see libmldsa.ml) against mld_polyw1_unpack_32 of                   *)
(* common/mldsa_native_packing.ml. It is also shown to be constant time and  *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyw1_unpack_32:
       +0x0  xor     eax, eax
       +0x2  nop     WORD PTR [rax+rax*1+0x0]
     loop1:
       +0x8  movzx   edx, BYTE PTR [rsi+rax*1]
       +0xc  and     edx, 0xf
       +0xf  mov     DWORD PTR [rdi+rax*8], edx
      +0x12  movzx   edx, BYTE PTR [rsi+rax*1]
      +0x16  shr     dl, 0x4
      +0x19  movzx   edx, dl
      +0x1c  mov     DWORD PTR [rdi+rax*8+0x4], edx
      +0x20  add     rax, 0x1
     loop1_test:
      +0x24  cmp     rax, 0x80
     loop1_back:
      +0x2a  jne     loop1
     loop1_exit: ret:
      +0x2c  ret
 ***)

let MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyw1_unpack_32"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,128); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyw1_unpack_32) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 128
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyw1_unpack_32 b i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,128); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyw1_unpack_32) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 128
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyw1_unpack_32 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,128; r,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,128); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyw1_unpack_32) /\
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
                       [a,128; r,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
