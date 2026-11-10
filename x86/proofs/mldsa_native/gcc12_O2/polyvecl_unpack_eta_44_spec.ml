(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a vector of 4 polynomials with coefficients in [-2,2]: the   *)
(* statement. This is the code for mldsa44_polyvecl_unpack_eta               *)
(* (mld_polyvecl_unpack_eta in polyvec.c) from mldsa-native's portable C     *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which calls mldsa44_polyeta_unpack for each polynomial in a loop. It is   *)
(* verified in the whole image (see libmldsa.ml) against mld_polyvec_unpack  *)
(* 96 mld_polyeta_unpack_2 of common/mldsa_native_polyvec.ml, using the      *)
(* theorems for mldsa44_polyeta_unpack, and shown to be constant time and    *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyeta_unpack_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyvecl_unpack_eta:
       +0x0  push    r12
       +0x2  lea     r12, [rsi+0x180]
       +0x9  push    rbp
       +0xa  mov     rbp, rdi
       +0xd  push    rbx
       +0xe  mov     rbx, rsi
     loop1:
      +0x11  mov     rsi, rbx
      +0x14  mov     rdi, rbp
      +0x17  add     rbx, 0x60
      +0x1b  add     rbp, 0x400
      +0x22  call    mldsa44_polyeta_unpack
     loop1_test: after_mldsa44_polyeta_unpack:
      +0x27  cmp     rbx, r12
     loop1_back:
      +0x2a  jne     loop1
     loop1_exit:
      +0x2c  pop     rbx
      +0x2d  pop     rbp
      +0x2e  pop     r12
     ret:
      +0x30  ret
 ***)

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyvecl_unpack_eta"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 4 packed polynomials of 96 bytes each at r, given byte   *)
(* by byte by b, are unpacked to the vector mld_polyvec_unpack 96            *)
(* mld_polyeta_unpack_2 b at p, 4 polynomials of 256 coefficients of 32 bits *)
(* each (see common/mldsa_native_polyvec.ml). The function saves R12, RBP    *)
(* and RBX below the return address, and each call of mldsa44_polyeta_unpack *)
(* puts its return address below them, below which mldsa44_polyeta_unpack    *)
(* has its stack frame of 32 bytes (64 bytes in all).                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!p r b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (p,4096))
            [(word_sub stackpointer (word 64),64); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(p,4096); (word_sub stackpointer (word 64),64)]
         [(word pc,libmldsa_size); (r,384)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyvecl_unpack_eta) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p; r] s /\
                  (!j. j < 384
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add p (word(4 * i))))
                             s =
                           mld_polyvec_unpack 96 mld_polyeta_unpack_2 b i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(p,4096);
                memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* packed polynomials, the vector, the stack frame and the slot of the       *)
(* return address, and the writes within the vector and the stack frame.     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e p r b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (p,4096))
            [(word_sub stackpointer (word 64),64); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(p,4096); (word_sub stackpointer (word 64),64)]
         [(word pc,libmldsa_size); (r,384)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyvecl_unpack_eta) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p; r] s /\
                  (!j. j < 384
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add p (word(4 * i))))
                             s =
                           mld_polyvec_unpack 96 mld_polyeta_unpack_2 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events p r pc (word_sub stackpointer (word 64))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [r,384; p,4096; word_sub stackpointer (word 64),64;
                       stackpointer,8]
                      [p,4096; word_sub stackpointer (word 64),64]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(p,4096);
                memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e p r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (p,4096))
            [(word_sub stackpointer (word 64),64); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(p,4096); (word_sub stackpointer (word 64),64)]
         [(word pc,libmldsa_size); (r,384)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyvecl_unpack_eta) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [p; r] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events p r pc (word_sub stackpointer (word 64))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [r,384; p,4096; word_sub stackpointer (word 64),64;
                       stackpointer,8]
                      [p,4096; word_sub stackpointer (word 64),64]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(p,4096);
                memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
