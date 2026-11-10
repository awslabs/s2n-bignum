(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing the hints of a signature: the statement. This is the code for     *)
(* mldsa65_pack_sig_h (mld_pack_sig_h in packing.c) from mldsa-native's      *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md): it zeroes the 61 bytes of the hints (at offset   *)
(* 3248 of the signature) with four (overlapping) 128-bit stores, the memset *)
(* of the C code that gcc inlines, then for each of the 6 polynomials it     *)
(* unpacks w1 into the scratch polynomial with mldsa_polyw1_unpack_32 and    *)
(* records the coefficients with a hint, from w0 and w1, returning -1 if     *)
(* there are more than 55 hints and 0 otherwise. It is verified in the whole *)
(* image (see libmldsa.ml) against mld_pack_hints and mld_pack_hints_ret of  *)
(* common/mldsa_native_hints.ml, using the theorems for                      *)
(* mldsa_polyw1_unpack_32, and shown to be constant time and memory safe     *)
(* with events depending on w0 and w1, which the caller declassifies.        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_hints.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyw1_unpack_32_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_pack_sig_h:
       +0x0  push    r15
       +0x2  lea     rax, [rdx+0x300]
       +0x9  pxor    xmm0, xmm0
       +0xd  lea     r15, [rdi+0xcb0]
      +0x14  push    r14
      +0x16  mov     r14, rsi
      +0x19  push    r13
      +0x1b  mov     r13, rcx
      +0x1e  push    r12
      +0x20  mov     r12, rdx
      +0x23  push    rbp
      +0x24  lea     rbp, [rdi+0xce7]
      +0x2b  push    rbx
      +0x2c  xor     ebx, ebx
      +0x2e  sub     rsp, 0x18
      +0x32  movups  XMMWORD PTR [rdi+0xcb0], xmm0
      +0x39  mov     QWORD PTR [rsp+0x8], rax
      +0x3e  movups  XMMWORD PTR [r15+0x20], xmm0
      +0x43  movups  XMMWORD PTR [r15+0x10], xmm0
      +0x48  movups  XMMWORD PTR [r15+0x2d], xmm0
     join1:
      +0x4d  mov     rsi, r12
      +0x50  mov     rdi, r13
      +0x53  call    mldsa_polyw1_unpack_32
     after_mldsa_polyw1_unpack_32:
      +0x58  xor     eax, eax
      +0x5a  jmp     join4
      +0x5c  nop     DWORD PTR [rax+0x0]
     join2:
      +0x60  mov     ecx, ebx
      +0x62  add     ebx, 0x1
      +0x65  mov     BYTE PTR [r15+rcx*1], al
     join3:
      +0x69  add     rax, 0x1
      +0x6d  cmp     rax, 0x100
      +0x73  je      +0xb1
     join4:
      +0x75  mov     ecx, DWORD PTR [r14+rax*4]
      +0x79  mov     edi, DWORD PTR [r13+rax*4+0x0]
      +0x7e  lea     esi, [rcx+0x3ff00]
      +0x84  cmp     esi, 0x7fe00
      +0x8a  ja      join5
      +0x8c  cmp     ecx, 0xfffc0100
      +0x92  jne     join3
      +0x94  test    edi, edi
      +0x96  je      join3
     join5:
      +0x98  cmp     ebx, 0x37
      +0x9b  jne     join2
      +0x9d  mov     eax, 0xffffffff
     join6:
      +0xa2  add     rsp, 0x18
      +0xa6  pop     rbx
      +0xa7  pop     rbp
      +0xa8  pop     r12
      +0xaa  pop     r13
      +0xac  pop     r14
      +0xae  pop     r15
     ret:
      +0xb0  ret
      +0xb1  mov     rax, QWORD PTR [rsp+0x8]
      +0xb6  sub     r12, 0xffffffffffffff80
      +0xba  mov     BYTE PTR [rbp+0x0], bl
      +0xbd  add     rbp, 0x1
      +0xc1  add     r14, 0x400
      +0xc8  cmp     r12, rax
      +0xcb  jne     join1
      +0xcd  xor     eax, eax
      +0xcf  jmp     join6
 ***)

let MLDSA_NATIVE_PACK_SIG_H_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_pack_sig_h"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector x of w0 at w0 and the 768 bytes b of w1 at w1p    *)
(* may overlap each other but not the 61 bytes of the hints in the signature *)
(* at sig, the scratch polynomial or the stack frame, where the function     *)
(* saves the six callee-saved registers it uses below the return address and *)
(* keeps the end of w1, with the slot of the return address of the calls     *)
(* below them. The return value is that of mld_pack_hints_ret, and if it is  *)
(* 0, the hints are those of mld_pack_hints.                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sig w0 w1p scratch x b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(word_add sig (word 3248),61); (scratch,1024);
          (word_sub stackpointer (word 80),80)] /\
        ALLPAIRS nonoverlapping
         [(word_add sig (word 3248),61); (scratch,1024);
          (word_sub stackpointer (word 80),80)]
         [(word pc,libmldsa_size); (w0,6144); (w1p,768)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(word_add sig (word 3248),61); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_pack_sig_h) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; w0; w1p; scratch] s /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add w0 (word(4 * i))))
                             s = x i) /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add w1p (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                    word_zx(mld_pack_hints_ret 55 6
                             (mld_polyvec_make_hint_32 x b)) /\
                  (mld_pack_hints_ret 55 6 (mld_polyvec_make_hint_32 x b) =
                   word 0
                   ==> !t. t < 61
                           ==> read(memory :> bytes8
                                 (word_add sig (word(3248 + t)))) s =
                               mld_pack_hints 55 6
                                 (mld_polyvec_make_hint_32 x b) t))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_add sig (word 3248),61);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_PACK_SIG_H_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PACK_SIG_H_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of w0 and w1 (x and b) and the addresses, with all  *)
(* accesses within the inputs, the scratch polynomial, the stack frame and   *)
(* the slot of the return address, and the writes within the outputs (the    *)
(* hints are only written).                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e sig w0 w1p scratch x b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(word_add sig (word 3248),61); (scratch,1024);
          (word_sub stackpointer (word 80),80)] /\
        ALLPAIRS nonoverlapping
         [(word_add sig (word 3248),61); (scratch,1024);
          (word_sub stackpointer (word 80),80)]
         [(word pc,libmldsa_size); (w0,6144); (w1p,768)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(word_add sig (word 3248),61); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_pack_sig_h) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; w0; w1p; scratch] s /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add w0 (word(4 * i))))
                             s = x i) /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add w1p (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                    word_zx(mld_pack_hints_ret 55 6
                             (mld_polyvec_make_hint_32 x b)) /\
                  (mld_pack_hints_ret 55 6 (mld_polyvec_make_hint_32 x b) =
                   word 0
                   ==> !t. t < 61
                           ==> read(memory :> bytes8
                                 (word_add sig (word(3248 + t)))) s =
                               mld_pack_hints 55 6
                                 (mld_polyvec_make_hint_32 x b) t) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events x b sig w0 w1p scratch pc
                                 (word_sub stackpointer (word 80))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [w0,6144; w1p,768; scratch,1024;
                       word_sub stackpointer (word 80),80; stackpointer,8]
                      [word_add sig (word 3248),61; scratch,1024;
                       word_sub stackpointer (word 80),80]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_add sig (word 3248),61);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_PACK_SIG_H_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on w0    *)
(* and w1 as above.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e sig w0 w1p scratch x b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(word_add sig (word 3248),61); (scratch,1024);
          (word_sub stackpointer (word 80),80)] /\
        ALLPAIRS nonoverlapping
         [(word_add sig (word 3248),61); (scratch,1024);
          (word_sub stackpointer (word 80),80)]
         [(word pc,libmldsa_size); (w0,6144); (w1p,768)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(word_add sig (word 3248),61); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_pack_sig_h) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; w0; w1p; scratch] s /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add w0 (word(4 * i))))
                             s = x i) /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add w1p (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events x b sig w0 w1p scratch pc
                                 (word_sub stackpointer (word 80))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [w0,6144; w1p,768; scratch,1024;
                       word_sub stackpointer (word 80),80; stackpointer,8]
                      [word_add sig (word 3248),61; scratch,1024;
                       word_sub stackpointer (word 80),80]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_add sig (word 3248),61);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_PACK_SIG_H_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
