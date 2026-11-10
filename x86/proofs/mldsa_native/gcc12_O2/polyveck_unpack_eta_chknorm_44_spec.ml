(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking and norm check of a vector of 4 polynomials with coefficients   *)
(* in [-2,2]: the statement. This is the code for                            *)
(* mldsa44_polyveck_unpack_eta_chknorm (mld_polyveck_unpack_eta_chknorm in   *)
(* polyvec.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which, for each polynomial in a *)
(* loop, unpacks it to the scratch polynomial with mldsa44_polyeta_unpack    *)
(* and ORs the result of mldsa_poly_chknorm for it. It is verified in the    *)
(* whole image (see libmldsa.ml) against mld_polyvec_chknorm and             *)
(* mld_polyvec_unpack of common/mldsa_native_polyvec.ml, using the theorems  *)
(* for mldsa44_polyeta_unpack and mldsa_poly_chknorm, and shown to be        *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyeta_unpack_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_chknorm_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyveck_unpack_eta_chknorm:
       +0x0  push    r14
       +0x2  lea     r14, [rdi+0x180]
       +0x9  push    r13
       +0xb  mov     r13d, esi
       +0xe  push    r12
      +0x10  xor     r12d, r12d
      +0x13  push    rbp
      +0x14  mov     rbp, rdx
      +0x17  push    rbx
      +0x18  mov     rbx, rdi
     loop1:
      +0x1b  mov     rsi, rbx
      +0x1e  mov     rdi, rbp
      +0x21  add     rbx, 0x60
      +0x25  call    mldsa44_polyeta_unpack
     after_mldsa44_polyeta_unpack:
      +0x2a  mov     esi, r13d
      +0x2d  mov     rdi, rbp
      +0x30  call    mldsa_poly_chknorm
     after_mldsa_poly_chknorm:
      +0x35  or      r12d, eax
     loop1_test:
      +0x38  cmp     rbx, r14
     loop1_back:
      +0x3b  jne     loop1
     loop1_exit:
      +0x3d  pop     rbx
      +0x3e  mov     eax, r12d
      +0x41  pop     rbp
      +0x42  pop     r12
      +0x44  pop     r13
      +0x46  pop     r14
     ret:
      +0x48  ret
 ***)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyveck_unpack_eta_chknorm"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. For the 4 packed polynomials of 96 bytes each at r, given    *)
(* byte by byte by b, and the bound in the low 32 bits of bnd, the result is *)
(* the norm check mld_polyvec_chknorm 4 of their unpacked forms              *)
(* mld_polyvec_unpack 96 mld_polyeta_unpack_2 b (see                         *)
(* common/mldsa_native_polyvec.ml). The scratch polynomial at scratch is     *)
(* overwritten. The function saves R14, R13, R12, RBP and RBX below the      *)
(* return address, and each call puts its return address below them, below   *)
(* which mldsa44_polyeta_unpack has its stack frame of 32 bytes (80 bytes in *)
(* all).                                                                     *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r b bnd scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (scratch,1024))
            [(word_sub stackpointer (word 80),80); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(scratch,1024); (word_sub stackpointer (word 80),80)]
         [(word pc,libmldsa_size); (r,384)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                    word (pc + mldsa44_polyveck_unpack_eta_chknorm) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; bnd; scratch] s /\
                  (!j. j < 384
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                    word_zx(mld_polyvec_chknorm 4
                             (mld_polyvec_unpack 96 mld_polyeta_unpack_2 b)
                             (word_zx bnd)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let
 MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the bound only, with all       *)
(* accesses within the packed polynomials, the scratch polynomial, the stack *)
(* frame and the slot of the return address, and the writes within the       *)
(* scratch polynomial and the stack frame.                                   *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r b bnd scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (scratch,1024))
            [(word_sub stackpointer (word 80),80); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(scratch,1024); (word_sub stackpointer (word 80),80)]
         [(word pc,libmldsa_size); (r,384)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                    word (pc + mldsa44_polyveck_unpack_eta_chknorm) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; bnd; scratch] s /\
                  (!j. j < 384
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                    word_zx(mld_polyvec_chknorm 4
                             (mld_polyvec_unpack 96 mld_polyeta_unpack_2 b)
                             (word_zx bnd)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r bnd scratch pc
                            (word_sub stackpointer (word 80)) returnaddress /\
                     memaccess_inbounds e2
                      [r,384; scratch,1024; word_sub stackpointer (word 80),80;
                       stackpointer,8]
                      [scratch,1024; word_sub stackpointer (word 80),80]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
 MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r bnd scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (scratch,1024))
            [(word_sub stackpointer (word 80),80); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(scratch,1024); (word_sub stackpointer (word 80),80)]
         [(word pc,libmldsa_size); (r,384)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                    word (pc + mldsa44_polyveck_unpack_eta_chknorm) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; bnd; scratch] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r bnd scratch pc
                            (word_sub stackpointer (word 80)) returnaddress /\
                     memaccess_inbounds e2
                      [r,384; scratch,1024; word_sub stackpointer (word 80),80;
                       stackpointer,8]
                      [scratch,1024; word_sub stackpointer (word 80),80]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
 MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
