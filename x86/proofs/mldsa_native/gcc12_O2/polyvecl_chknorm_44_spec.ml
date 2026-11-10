(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Norm check of a vector of 4 polynomials: the statement. This is the code  *)
(* for mldsa44_polyvecl_chknorm (mld_polyvecl_chknorm in polyvec.c) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which ORs the results of mldsa_poly_chknorm for  *)
(* the polynomials in a loop. It is verified in the whole image (see         *)
(* libmldsa.ml) against mld_polyvec_chknorm of                               *)
(* common/mldsa_native_polyvec.ml, using the theorems for                    *)
(* mldsa_poly_chknorm, and shown to be constant time and memory safe.        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_chknorm_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyvecl_chknorm:
       +0x0  push    r13
       +0x2  lea     r13, [rdi+0x1000]
       +0x9  push    r12
       +0xb  mov     r12d, esi
       +0xe  push    rbp
       +0xf  xor     ebp, ebp
      +0x11  push    rbx
      +0x12  mov     rbx, rdi
      +0x15  sub     rsp, 0x8
     loop1:
      +0x19  mov     rdi, rbx
      +0x1c  mov     esi, r12d
      +0x1f  add     rbx, 0x400
      +0x26  call    mldsa_poly_chknorm
     after_mldsa_poly_chknorm:
      +0x2b  or      ebp, eax
     loop1_test:
      +0x2d  cmp     rbx, r13
     loop1_back:
      +0x30  jne     loop1
     loop1_exit:
      +0x32  add     rsp, 0x8
      +0x36  mov     eax, ebp
      +0x38  pop     rbx
      +0x39  pop     rbp
      +0x3a  pop     r12
      +0x3c  pop     r13
     ret:
      +0x3e  ret
 ***)

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyvecl_chknorm"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. For the vector x at v, 4 polynomials of 256 coefficients of  *)
(* 32 bits each (see common/mldsa_native_polyvec.ml), and the bound in the   *)
(* low 32 bits of bnd, the result is mld_polyvec_chknorm 4 x bnd: all ones   *)
(* if some coefficient is not below the bound in absolute value, zero        *)
(* otherwise. The function saves R13, R12, RBP and RBX below the return      *)
(* address and keeps 8 more bytes there, and each call of mldsa_poly_chknorm *)
(* puts its return address below them (48 bytes in all).                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!v x bnd pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(v,4096); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyvecl_chknorm) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; bnd] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                    word_zx(mld_polyvec_chknorm 4 x (word_zx bnd)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the bound only, with all       *)
(* accesses within the vector, the stack frame and the slot of the return    *)
(* address, and the writes within the stack frame.                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e v x bnd pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(v,4096); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyvecl_chknorm) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; bnd] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                    word_zx(mld_polyvec_chknorm 4 x (word_zx bnd)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v bnd pc (word_sub stackpointer (word 48))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,4096; word_sub stackpointer (word 48),48;
                       stackpointer,8]
                      [word_sub stackpointer (word 48),48]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e v bnd pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_sub stackpointer (word 48),48))
            [(v,4096); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyvecl_chknorm) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; bnd] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v bnd pc (word_sub stackpointer (word 48))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,4096; word_sub stackpointer (word 48),48;
                       stackpointer,8]
                      [word_sub stackpointer (word 48),48]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
