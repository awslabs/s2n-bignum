(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Rejection sampling of coefficients in [-2,2] from nibbles: the statement. *)
(* This is the code for mld_rej_eta_c44 (mld_rej_eta_c in poly_kl.c with     *)
(* MLDSA_ETA = 2, for ML-DSA-44) from mldsa-native's portable C              *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* the function mld_rej_eta_c44.constprop.0 of the binary, which the         *)
(* compiler has specialized to the target 256 and the buffer length 136 of   *)
(* all its calls. It is verified in the whole image (see libmldsa.ml)        *)
(* against mld_rej_eta_list and mld_rej_eta_ctr of                           *)
(* common/mldsa_native_sampling.ml. It is also shown to be constant time and *)
(* memory safe, with the events depending on the buffer only through the     *)
(* acceptance of the nibbles that the C code declassifies.                   *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mld_rej_eta_c44:
       +0x0  mov     r8, rdi
       +0x3  cmp     esi, 0xff
       +0x9  ja      join3
       +0xf  mov     r9d, 0x1
      +0x15  mov     r10d, 0x2
      +0x1b  sub     r9d, edx
      +0x1e  xchg    ax, ax
     loop1:
      +0x20  movzx   eax, BYTE PTR [rdx]
      +0x23  mov     ecx, eax
      +0x25  shr     al, 0x4
      +0x28  and     ecx, 0xf
      +0x2b  movzx   eax, al
      +0x2e  cmp     cl, 0xf
      +0x31  je      join1
      +0x33  movzx   ecx, cl
      +0x36  imul    edi, ecx, 0xcd
      +0x3c  shr     edi, 0xa
      +0x3f  lea     r11d, [rdi+rdi*4]
      +0x43  mov     edi, esi
      +0x45  add     esi, 0x1
      +0x48  sub     ecx, r11d
      +0x4b  mov     r11d, r10d
      +0x4e  sub     r11d, ecx
      +0x51  mov     DWORD PTR [r8+rdi*4], r11d
     join1:
      +0x55  cmp     esi, 0xff
      +0x5b  setbe   cl
      +0x5e  cmp     eax, 0xe
      +0x61  ja      join2
      +0x63  test    cl, cl
      +0x65  je      join2
      +0x67  imul    ecx, eax, 0xcd
      +0x6d  lea     edi, [rsi+0x1]
      +0x70  mov     esi, esi
      +0x72  shr     ecx, 0xa
      +0x75  lea     ecx, [rcx+rcx*4]
      +0x78  sub     eax, ecx
      +0x7a  mov     ecx, r10d
      +0x7d  sub     ecx, eax
      +0x7f  cmp     edi, 0xff
      +0x85  mov     DWORD PTR [r8+rsi*4], ecx
      +0x89  setbe   cl
      +0x8c  mov     esi, edi
     join2:
      +0x8e  lea     eax, [r9+rdx*1]
      +0x92  cmp     eax, 0x87
      +0x97  setbe   al
      +0x9a  add     rdx, 0x1
     loop1_test:
      +0x9e  test    al, cl
     loop1_back:
      +0xa0  jne     loop1
     join3: loop1_exit:
      +0xa6  mov     eax, esi
     ret:
      +0xa8  ret
 ***)

let MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mld_rej_eta_c44"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. From offset <= 256 coefficients of the polynomial at a, the  *)
(* function reads the buffer of 136 bytes at buf and stores the accepted     *)
(* values of its nibbles that fit below 256, from coefficient offset on,     *)
(* returning the new number of coefficients. It uses no stack, and the       *)
(* registers it may change are those that it does change. (Its caller in the *)
(* image, mldsa44_poly_uniform_eta_4x, keeps values across the calls only in *)
(* callee-saved registers and on the stack.)                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a offset buf b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,136); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_rej_eta_c44) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf] s /\
                  (!j. j < 136
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word(mld_rej_eta_ctr 2 256 offset b 136) /\
                  (!i. offset <= i /\ i < mld_rej_eta_ctr 2 256 offset b 136
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                           EL (i - offset) (mld_rej_eta_list 2 b (2 * 136))))
             (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, offset and the list of whether    *)
(* each nibble that the C code examines is accepted (the values t_valid that *)
(* it declassifies), mld_rej_eta_declass, with all accesses within the       *)
(* buffer and the slot of the return address and the writes within the       *)
(* coefficients from offset on.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a offset buf b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,136); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_rej_eta_c44) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf] s /\
                  (!j. j < 136
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word(mld_rej_eta_ctr 2 256 offset b 136) /\
                  (!i. offset <= i /\ i < mld_rej_eta_ctr 2 256 offset b 136
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                           EL (i - offset)
                              (mld_rej_eta_list 2 b (2 * 136))) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a offset buf
                            (mld_rej_eta_declass 2 256 offset b 136)
                            pc stackpointer returnaddress /\
                     memaccess_inbounds e2 [buf,136; stackpointer,8]
                      [word_add a (word(4 * offset)),4 * (256 - offset)]))
             (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* buffer only through the declassified validity of its nibbles, as above.   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a offset buf b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,136); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_rej_eta_c44) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf] s /\
                  (!j. j < 136
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a offset buf
                            (mld_rej_eta_declass 2 256 offset b 136)
                            pc stackpointer returnaddress /\
                     memaccess_inbounds e2 [buf,136; stackpointer,8]
                      [word_add a (word(4 * offset)),4 * (256 - offset)]))
             (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
