(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Rejection sampling of coefficients mod q from groups of 3 bytes: the      *)
(* statement. This is the code for mld_rej_uniform_c (poly.c) from           *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), the function mld_rej_uniform_c.constprop.0 of    *)
(* the binary, which the compiler has specialized to the target 256 of all   *)
(* its calls and, as buflen >= 3 in all of them, does not test buflen before *)
(* reading the first group. It is verified in the whole image (see           *)
(* libmldsa.ml) against mld_rej_uniform_list and mld_rej_uniform_ctr of      *)
(* common/mldsa_native_sampling.ml. It is also shown to be constant time and *)
(* memory safe, with the events depending on the buffer, which the callers   *)
(* fill with the SHAKE128 output of the public seed rho of the matrix.       *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mld_rej_uniform_c:
       +0x0  mov     r8, rdi
       +0x3  mov     r9d, ecx
       +0x6  cmp     esi, 0xff
       +0xc  ja      join4
       +0xe  mov     r10d, 0x3
      +0x14  sub     r10d, edx
      +0x17  jmp     join3
      +0x19  nop     DWORD PTR [rax+0x0]
     join1:
      +0x20  mov     esi, ecx
     join2:
      +0x22  add     rdx, 0x3
      +0x26  lea     eax, [r10+rdx*1]
      +0x2a  cmp     r9d, eax
      +0x2d  jb      join4
     join3:
      +0x2f  movzx   eax, BYTE PTR [rdx+0x1]
      +0x33  movzx   ecx, BYTE PTR [rdx+0x2]
      +0x37  movzx   edi, BYTE PTR [rdx]
      +0x3a  shl     eax, 0x8
      +0x3d  shl     ecx, 0x10
      +0x40  or      eax, ecx
      +0x42  or      eax, edi
      +0x44  and     eax, 0x7fffff
      +0x49  cmp     eax, 0x7fe000
      +0x4e  ja      join2
      +0x50  mov     edi, esi
      +0x52  lea     ecx, [rsi+0x1]
      +0x55  mov     DWORD PTR [r8+rdi*4], eax
      +0x59  cmp     esi, 0xff
      +0x5f  jne     join1
      +0x61  mov     eax, ecx
     ret1:
      +0x63  ret
      +0x64  nop     DWORD PTR [rax+0x0]
     join4:
      +0x68  mov     ecx, esi
      +0x6a  mov     eax, ecx
     ret2:
      +0x6c  ret
 ***)

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mld_rej_uniform_c"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. From offset <= 256 coefficients of the polynomial at a, the  *)
(* function reads the buffer of buflen bytes at buf, 3 <= buflen <= 840, and *)
(* stores the accepted values of its groups of 3 bytes that fit below 256,   *)
(* from coefficient offset on, returning the new number of coefficients. It  *)
(* uses no stack, and the registers it may change are those that it does     *)
(* change. (Its callers in the image, mldsa_poly_uniform and                 *)
(* mldsa_poly_uniform_4x, keep values across the calls only in callee-saved  *)
(* registers and on the stack.)                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a offset buf buflen b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\ 3 <= buflen /\ buflen <= 840 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,buflen); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_rej_uniform_c) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf; word buflen] s /\
                  (!j. j < buflen
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word(mld_rej_uniform_ctr 256 offset b buflen) /\
                  (!i. offset <= i /\
                       i < mld_rej_uniform_ctr 256 offset b buflen
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                           EL (i - offset)
                              (mld_rej_uniform_list b (buflen DIV 3))))
             (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, offset, buflen and the contents b *)
(* of the buffer, which is public, with all accesses within the buffer and   *)
(* the slot of the return address and the writes within the coefficients     *)
(* from offset on.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a offset buf buflen b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\ 3 <= buflen /\ buflen <= 840 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,buflen); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_rej_uniform_c) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; word offset; buf; word buflen] s /\
                  (!j. j < buflen
                       ==> read(memory :> bytes8(word_add buf (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word(mld_rej_uniform_ctr 256 offset b buflen) /\
                  (!i. offset <= i /\
                       i < mld_rej_uniform_ctr 256 offset b buflen
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                           EL (i - offset)
                              (mld_rej_uniform_list b (buflen DIV 3))) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a offset buf buflen b pc stackpointer
                                   returnaddress /\
                     memaccess_inbounds e2 [buf,buflen; stackpointer,8]
                      [word_add a (word(4 * offset)),4 * (256 - offset)]))
             (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* buffer as above.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a offset buf buflen b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        offset <= 256 /\ 3 <= buflen /\ buflen <= 840 /\
        ALL (nonoverlapping (word_add a (word(4 * offset)),4 * (256 - offset)))
            [(word pc,libmldsa_size); (buf,buflen); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_rej_uniform_c) /\
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
                     e2 = f_events a offset buf buflen b pc stackpointer
                                   returnaddress /\
                     memaccess_inbounds e2 [buf,buflen; stackpointer,8]
                      [word_add a (word(4 * offset)),4 * (256 - offset)]))
             (MAYCHANGE [RIP; RSP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word(4 * offset)),
                                         4 * (256 - offset))])`;;

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
