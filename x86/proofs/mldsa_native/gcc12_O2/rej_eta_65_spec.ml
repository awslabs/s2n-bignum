(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Rejection sampling of coefficients in [-4,4] from nibbles: the statement. *)
(* This is the code for mld_rej_eta_c65 (mld_rej_eta_c in poly_kl.c with     *)
(* MLDSA_ETA = 4, for ML-DSA-65) from mldsa-native's portable C              *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* the function mld_rej_eta_c65.constprop.0 of the binary, which the         *)
(* compiler has specialized to the target 256 of all its calls and, as       *)
(* buflen > 0 in all of them, does not test buflen before reading the first  *)
(* byte. It is verified in the whole image (see libmldsa.ml) against         *)
(* mld_rej_eta_list and mld_rej_eta_ctr of common/mldsa_native_sampling.ml.  *)
(* It is also shown to be constant time and memory safe, with the events     *)
(* depending on the buffer only through the acceptance of the nibbles that   *)
(* the C code declassifies.                                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mld_rej_eta_c65:
       +0x0  cmp     esi, 0xff
       +0x6  ja      join3
       +0xc  push    rbx
       +0xd  mov     r10d, 0x1
      +0x13  mov     r8, rdi
      +0x16  mov     r9d, ecx
      +0x19  mov     r11d, 0x4
      +0x1f  sub     r10d, edx
      +0x22  nop     WORD PTR [rax+rax*1+0x0]
     loop1:
      +0x28  movzx   eax, BYTE PTR [rdx]
      +0x2b  mov     ecx, eax
      +0x2d  shr     al, 0x4
      +0x30  and     ecx, 0xf
      +0x33  cmp     cl, 0x8
      +0x36  ja      join1
      +0x38  movzx   ecx, cl
      +0x3b  mov     ebx, r11d
      +0x3e  mov     edi, esi
      +0x40  add     esi, 0x1
      +0x43  sub     ebx, ecx
      +0x45  mov     DWORD PTR [r8+rdi*4], ebx
     join1:
      +0x49  cmp     esi, 0xff
      +0x4f  setbe   cl
      +0x52  cmp     al, 0x8
      +0x54  ja      join2
      +0x56  test    cl, cl
      +0x58  je      join2
      +0x5a  lea     edi, [rsi+0x1]
      +0x5d  movzx   eax, al
      +0x60  mov     ecx, r11d
      +0x63  mov     esi, esi
      +0x65  sub     ecx, eax
      +0x67  cmp     edi, 0xff
      +0x6d  mov     DWORD PTR [r8+rsi*4], ecx
      +0x71  setbe   cl
      +0x74  mov     esi, edi
     join2:
      +0x76  lea     eax, [r10+rdx*1]
      +0x7a  cmp     eax, r9d
      +0x7d  setb    al
      +0x80  add     rdx, 0x1
     loop1_test:
      +0x84  test    al, cl
     loop1_back:
      +0x86  jne     loop1
     loop1_exit:
      +0x88  mov     eax, esi
      +0x8a  pop     rbx
     ret1:
      +0x8b  ret
      +0x8c  nop     DWORD PTR [rax+0x0]
     join3:
      +0x90  mov     eax, esi
     ret2:
      +0x92  ret
 ***)

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mld_rej_eta_c65"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. From offset <= 256 coefficients of the polynomial at a, the  *)
(* function reads the buffer of buflen bytes at buf, 0 < buflen <= 272, and  *)
(* stores the accepted values of its nibbles that fit below 256, from        *)
(* coefficient offset on, returning the new number of coefficients. Unless   *)
(* offset = 256, it saves RBX on the stack below the return address; the     *)
(* registers it may change are those that it does change. (Its caller in the *)
(* image, mldsa65_poly_uniform_eta_4x, keeps values across the calls only in *)
(* callee-saved registers and on the stack.)                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a offset buf buflen b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\ 0 < buflen /\ buflen <= 272 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,buflen);
             (word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,libmldsa_size); (buf,buflen)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_rej_eta_c65) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf; word buflen] s /\
                  (!j. j < buflen
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word(mld_rej_eta_ctr 4 256 offset b buflen) /\
                  (!i. offset <= i /\ i < mld_rej_eta_ctr 4 256 offset b buflen
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                           EL (i - offset) (mld_rej_eta_list 4 b (2 * buflen))))
             (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset));
                         memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, offset, buflen and the list of    *)
(* whether each nibble that the C code examines is accepted (the values      *)
(* t_valid that it declassifies), mld_rej_eta_declass, with all accesses     *)
(* within the buffer, the stack frame and the slot of the return address and *)
(* the writes within the coefficients from offset on and the stack frame.    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a offset buf buflen b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\ 0 < buflen /\ buflen <= 272 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,buflen);
             (word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,libmldsa_size); (buf,buflen)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_rej_eta_c65) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf; word buflen] s /\
                  (!j. j < buflen
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word(mld_rej_eta_ctr 4 256 offset b buflen) /\
                  (!i. offset <= i /\ i < mld_rej_eta_ctr 4 256 offset b buflen
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                           EL (i - offset)
                              (mld_rej_eta_list 4 b (2 * buflen))) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a offset buf buflen
                            (mld_rej_eta_declass 4 256 offset b buflen)
                            pc (word_sub stackpointer (word 8))
                            returnaddress /\
                     memaccess_inbounds e2
                      [buf,buflen; word_sub stackpointer (word 8),8;
                       stackpointer,8]
                      [word_add a (word(4 * offset)),4 * (256 - offset);
                       word_sub stackpointer (word 8),8]))
             (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset));
                         memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* buffer only through the declassified validity of its nibbles, as above.   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a offset buf buflen b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\ 0 < buflen /\ buflen <= 272 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,buflen);
             (word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,libmldsa_size); (buf,buflen)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_rej_eta_c65) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf; word buflen] s /\
                  (!j. j < buflen
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a offset buf buflen
                            (mld_rej_eta_declass 4 256 offset b buflen)
                            pc (word_sub stackpointer (word 8))
                            returnaddress /\
                     memaccess_inbounds e2
                      [buf,buflen; word_sub stackpointer (word 8),8;
                       stackpointer,8]
                      [word_add a (word(4 * offset)),4 * (256 - offset);
                       word_sub stackpointer (word 8),8]))
             (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset));
                         memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_REJ_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
