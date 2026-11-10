(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 10 bits per coefficient: the statement. This *)
(* is the code for mldsa_polyt1_pack (mld_polyt1_pack in poly.c) from        *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which writes 5 bytes for each 4 coefficients. It *)
(* is verified in the whole image (see libmldsa.ml) against mld_polyt1_pack  *)
(* of common/mldsa_native_packing.ml, byte by byte. It is also shown to be   *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyt1_pack:
       +0x0  lea     rcx, [rsi+0x400]
       +0x7  nop     WORD PTR [rax+rax*1+0x0]
     loop1:
      +0x10  mov     eax, DWORD PTR [rsi]
      +0x12  add     rsi, 0x10
      +0x16  add     rdi, 0x5
      +0x1a  mov     BYTE PTR [rdi-0x5], al
      +0x1d  mov     eax, DWORD PTR [rsi-0xc]
      +0x20  shl     eax, 0x2
      +0x23  or      al, BYTE PTR [rsi-0xf]
      +0x26  mov     BYTE PTR [rdi-0x4], al
      +0x29  mov     eax, DWORD PTR [rsi-0xc]
      +0x2c  mov     edx, DWORD PTR [rsi-0x8]
      +0x2f  sar     eax, 0x6
      +0x32  shl     edx, 0x4
      +0x35  or      eax, edx
      +0x37  mov     BYTE PTR [rdi-0x3], al
      +0x3a  mov     eax, DWORD PTR [rsi-0x8]
      +0x3d  mov     edx, DWORD PTR [rsi-0x4]
      +0x40  sar     eax, 0x4
      +0x43  shl     edx, 0x6
      +0x46  or      eax, edx
      +0x48  mov     BYTE PTR [rdi-0x2], al
      +0x4b  mov     eax, DWORD PTR [rsi-0x4]
      +0x4e  sar     eax, 0x2
      +0x51  mov     BYTE PTR [rdi-0x1], al
     loop1_test:
      +0x54  cmp     rsi, rcx
     loop1_back:
      +0x57  jne     loop1
     loop1_exit: ret:
      +0x59  ret
 ***)

let MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyt1_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,320))
            [(word pc,libmldsa_size); (a,1024); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyt1_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 320
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyt1_pack x j)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,320)])`;;

let MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,320))
            [(word pc,libmldsa_size); (a,1024); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyt1_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 320
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyt1_pack x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; r,320; stackpointer,8] [r,320]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,320)])`;;

let MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,320))
            [(word pc,libmldsa_size); (a,1024); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyt1_pack) /\
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
                       [a,1024; r,320; stackpointer,8] [r,320]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,320)])`;;

let MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
