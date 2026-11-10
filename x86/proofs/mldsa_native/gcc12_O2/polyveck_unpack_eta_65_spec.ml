(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a vector of 6 polynomials with coefficients in [-4,4]: the   *)
(* statement. This is the code for mldsa65_polyveck_unpack_eta               *)
(* (mld_polyveck_unpack_eta in polyvec.c) from mldsa-native's portable C     *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which calls mldsa65_polyeta_unpack for each polynomial in a loop. It is   *)
(* verified in the whole image (see libmldsa.ml) against mld_polyvec_unpack  *)
(* 128 mld_polyeta_unpack_4 of common/mldsa_native_polyvec.ml, using the     *)
(* theorems for mldsa65_polyeta_unpack, and shown to be constant time and    *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyeta_unpack_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyveck_unpack_eta:
       +0x0  push    r12
       +0x2  lea     r12, [rdi+0x1800]
       +0x9  push    rbp
       +0xa  mov     rbp, rsi
       +0xd  push    rbx
       +0xe  mov     rbx, rdi
      +0x11  nop     DWORD PTR [rax+0x0]
     loop1:
      +0x18  mov     rsi, rbp
      +0x1b  mov     rdi, rbx
      +0x1e  add     rbx, 0x400
      +0x25  sub     rbp, 0xffffffffffffff80
      +0x29  call    mldsa65_polyeta_unpack
     loop1_test: after_mldsa65_polyeta_unpack:
      +0x2e  cmp     rbx, r12
     loop1_back:
      +0x31  jne     loop1
     loop1_exit:
      +0x33  pop     rbx
      +0x34  pop     rbp
      +0x35  pop     r12
     ret:
      +0x37  ret
 ***)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyveck_unpack_eta"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 6 packed polynomials of 128 bytes each at r, given byte  *)
(* by byte by b, are unpacked to the vector mld_polyvec_unpack 128           *)
(* mld_polyeta_unpack_4 b at p, 6 polynomials of 256 coefficients of 32 bits *)
(* each (see common/mldsa_native_polyvec.ml). The function saves R12, RBP    *)
(* and RBX below the return address, and each call of mldsa65_polyeta_unpack *)
(* puts its return address below them (32 bytes in all).                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!p r b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (p,6144))
            [(word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(p,6144); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size); (r,768)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_polyveck_unpack_eta) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p; r] s /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add p (word(4 * i))))
                             s =
                           mld_polyvec_unpack 128 mld_polyeta_unpack_4 b i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(p,6144);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVECK_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* packed polynomials, the vector, the stack frame and the slot of the       *)
(* return address, and the writes within the vector and the stack frame.     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e p r b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (p,6144))
            [(word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(p,6144); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size); (r,768)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_polyveck_unpack_eta) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p; r] s /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add p (word(4 * i))))
                             s =
                           mld_polyvec_unpack 128 mld_polyeta_unpack_4 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events p r pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [r,768; p,6144; word_sub stackpointer (word 32),32;
                       stackpointer,8]
                      [p,6144; word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(p,6144);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVECK_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e p r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (p,6144))
            [(word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(p,6144); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size); (r,768)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_polyveck_unpack_eta) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p; r] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events p r pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [r,768; p,6144; word_sub stackpointer (word 32),32;
                       stackpointer,8]
                      [p,6144; word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(p,6144);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVECK_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
