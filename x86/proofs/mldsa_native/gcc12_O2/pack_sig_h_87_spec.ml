(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing the hints of a signature: the statement. This is the code for     *)
(* mldsa87_pack_sig_h (mld_pack_sig_h in packing.c) from mldsa-native's      *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md): it zeroes the 83 bytes of the hints (at offset   *)
(* 4544 of the signature) with two quadword stores and a REP STOSQ, the      *)
(* memset of the C code that gcc inlines, which needs the direction flag     *)
(* clear, as the ABI guarantees on entry, then for each of the 8 polynomials *)
(* it unpacks w1 into the scratch polynomial with mldsa_polyw1_unpack_32 and *)
(* records the coefficients with a hint, from w0 and w1, returning -1 if     *)
(* there are more than 75 hints and 0 otherwise. It is verified in the whole *)
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

    mldsa87_pack_sig_h:
       +0x0  push    r15
       +0x2  lea     r15, [rdi+0x11c0]
       +0x9  xor     eax, eax
       +0xb  push    r14
       +0xd  mov     r14, rsi
      +0x10  push    r13
      +0x12  mov     r13, rcx
      +0x15  mov     rcx, r15
      +0x18  push    r12
      +0x1a  mov     r12, rdx
      +0x1d  push    rbp
      +0x1e  mov     rbp, rdi
      +0x21  lea     rdi, [rdi+0x11c8]
      +0x28  push    rbx
      +0x29  add     rbp, 0x120b
      +0x30  xor     ebx, ebx
      +0x32  sub     rsp, 0x18
      +0x36  mov     QWORD PTR [rdi-0x8], 0x0
      +0x3e  mov     QWORD PTR [rdi+0x43], 0x0
      +0x46  and     rdi, 0xfffffffffffffff8
      +0x4a  sub     rcx, rdi
      +0x4d  add     ecx, 0x53
      +0x50  shr     ecx, 0x3
      +0x53  rep stos QWORD PTR es:[rdi], rax
      +0x56  lea     rax, [rdx+0x400]
      +0x5d  mov     QWORD PTR [rsp+0x8], rax
     join1:
      +0x62  mov     rsi, r12
      +0x65  mov     rdi, r13
      +0x68  call    mldsa_polyw1_unpack_32
     after_mldsa_polyw1_unpack_32:
      +0x6d  xor     eax, eax
      +0x6f  jmp     join4
      +0x71  nop     DWORD PTR [rax+0x0]
     join2:
      +0x78  mov     ecx, ebx
      +0x7a  add     ebx, 0x1
      +0x7d  mov     BYTE PTR [r15+rcx*1], al
     join3:
      +0x81  add     rax, 0x1
      +0x85  cmp     rax, 0x100
      +0x8b  je      +0xc9
     join4:
      +0x8d  mov     ecx, DWORD PTR [r14+rax*4]
      +0x91  mov     edi, DWORD PTR [r13+rax*4+0x0]
      +0x96  lea     esi, [rcx+0x3ff00]
      +0x9c  cmp     esi, 0x7fe00
      +0xa2  ja      join5
      +0xa4  cmp     ecx, 0xfffc0100
      +0xaa  jne     join3
      +0xac  test    edi, edi
      +0xae  je      join3
     join5:
      +0xb0  cmp     ebx, 0x4b
      +0xb3  jne     join2
      +0xb5  mov     eax, 0xffffffff
     join6:
      +0xba  add     rsp, 0x18
      +0xbe  pop     rbx
      +0xbf  pop     rbp
      +0xc0  pop     r12
      +0xc2  pop     r13
      +0xc4  pop     r14
      +0xc6  pop     r15
     ret:
      +0xc8  ret
      +0xc9  mov     rax, QWORD PTR [rsp+0x8]
      +0xce  sub     r12, 0xffffffffffffff80
      +0xd2  mov     BYTE PTR [rbp+0x0], bl
      +0xd5  add     rbp, 0x1
      +0xd9  add     r14, 0x400
      +0xe0  cmp     r12, rax
      +0xe3  jne     join1
      +0xe9  xor     eax, eax
      +0xeb  jmp     join6
 ***)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_pack_sig_h"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector x of w0 at w0 and the 1024 bytes b of w1 at w1p   *)
(* may overlap each other but not the 83 bytes of the hints in the signature *)
(* at sig, the scratch polynomial or the stack frame, where the function     *)
(* saves the six callee-saved registers it uses below the return address and *)
(* keeps the end of w1, with the slot of the return address of the calls     *)
(* below them. The return value is that of mld_pack_hints_ret, and if it is  *)
(* 0, the hints are those of mld_pack_hints.                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sig w0 w1p scratch x b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(word_add sig (word 4544),83); (scratch,1024);
          (word_sub stackpointer (word 80),80)] /\
        ALLPAIRS nonoverlapping
         [(word_add sig (word 4544),83); (scratch,1024);
          (word_sub stackpointer (word 80),80)]
         [(word pc,libmldsa_size); (w0,8192); (w1p,1024)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(word_add sig (word 4544),83); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_pack_sig_h) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; w0; w1p; scratch] s /\
                  (read DF s <=> false) /\
                  (!i. i < 2048
                       ==> read(memory :> bytes32(word_add w0 (word(4 * i))))
                             s = x i) /\
                  (!j. j < 1024
                       ==> read(memory :> bytes8(word_add w1p (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                    word_zx(mld_pack_hints_ret 75 8
                             (mld_polyvec_make_hint_32 x b)) /\
                  (mld_pack_hints_ret 75 8 (mld_polyvec_make_hint_32 x b) =
                   word 0
                   ==> !t. t < 83
                           ==> read(memory :> bytes8
                                 (word_add sig (word(4544 + t)))) s =
                               mld_pack_hints 75 8
                                 (mld_polyvec_make_hint_32 x b) t))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_add sig (word 4544),83);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of w0 and w1 (x and b) and the addresses, with all  *)
(* accesses within the inputs, the scratch polynomial, the stack frame and   *)
(* the slot of the return address, and the writes within the outputs (the    *)
(* hints are only written).                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e sig w0 w1p scratch x b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(word_add sig (word 4544),83); (scratch,1024);
          (word_sub stackpointer (word 80),80)] /\
        ALLPAIRS nonoverlapping
         [(word_add sig (word 4544),83); (scratch,1024);
          (word_sub stackpointer (word 80),80)]
         [(word pc,libmldsa_size); (w0,8192); (w1p,1024)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(word_add sig (word 4544),83); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_pack_sig_h) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; w0; w1p; scratch] s /\
                  (read DF s <=> false) /\
                  (!i. i < 2048
                       ==> read(memory :> bytes32(word_add w0 (word(4 * i))))
                             s = x i) /\
                  (!j. j < 1024
                       ==> read(memory :> bytes8(word_add w1p (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s =
                    word_zx(mld_pack_hints_ret 75 8
                             (mld_polyvec_make_hint_32 x b)) /\
                  (mld_pack_hints_ret 75 8 (mld_polyvec_make_hint_32 x b) =
                   word 0
                   ==> !t. t < 83
                           ==> read(memory :> bytes8
                                 (word_add sig (word(4544 + t)))) s =
                               mld_pack_hints 75 8
                                 (mld_polyvec_make_hint_32 x b) t) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events x b sig w0 w1p scratch pc
                                 (word_sub stackpointer (word 80))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [w0,8192; w1p,1024; scratch,1024;
                       word_sub stackpointer (word 80),80; stackpointer,8]
                      [word_add sig (word 4544),83; scratch,1024;
                       word_sub stackpointer (word 80),80]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_add sig (word 4544),83);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on w0    *)
(* and w1 as above.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e sig w0 w1p scratch x b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(word_add sig (word 4544),83); (scratch,1024);
          (word_sub stackpointer (word 80),80)] /\
        ALLPAIRS nonoverlapping
         [(word_add sig (word 4544),83); (scratch,1024);
          (word_sub stackpointer (word 80),80)]
         [(word pc,libmldsa_size); (w0,8192); (w1p,1024)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(word_add sig (word 4544),83); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_pack_sig_h) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sig; w0; w1p; scratch] s /\
                  (read DF s <=> false) /\
                  (!i. i < 2048
                       ==> read(memory :> bytes32(word_add w0 (word(4 * i))))
                             s = x i) /\
                  (!j. j < 1024
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
                      [w0,8192; w1p,1024; scratch,1024;
                       word_sub stackpointer (word 80),80; stackpointer,8]
                      [word_add sig (word 4544),83; scratch,1024;
                       word_sub stackpointer (word 80),80]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(word_add sig (word 4544),83);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
