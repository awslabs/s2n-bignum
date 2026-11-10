(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking the hints of a polynomial of a signature: the statement. This   *)
(* is the code for mldsa65_sig_unpack_hints (mld_sig_unpack_hints in         *)
(* packing.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md): for polynomial i of the 6, it   *)
(* checks the counts of the hints in the 61 bytes of the hints (at offset    *)
(* 3248 of the signature), zeroes the polynomial with the inlined memset of  *)
(* the C code (two quadword stores and a REP STOSQ, which need the direction *)
(* flag clear, as the ABI guarantees on entry), sets the coefficients at the *)
(* indices of its hints to 1, checking that they are increasing, and for the *)
(* last polynomial checks that the unused index bytes are zero, returning -1 *)
(* if a check fails and 0 otherwise. It is verified in the whole image (see  *)
(* libmldsa.ml) against mld_unpack_hints and mld_unpack_hints_ret of         *)
(* common/mldsa_native_hints.ml, and shown to be constant time and memory    *)
(* safe with events depending on the bytes of the hints and on i, which are  *)
(* public.                                                                   *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_hints.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_sig_unpack_hints:
       +0x0  push    rbp
       +0x1  mov     r11, rsi
       +0x4  mov     r8, rdi
       +0x7  mov     ebp, edx
       +0x9  push    rbx
       +0xa  lea     rbx, [rsi+0xcb0]
      +0x11  xor     esi, esi
      +0x13  test    edx, edx
      +0x15  je      join1
      +0x17  lea     eax, [rdx+0x36]
      +0x1a  movzx   esi, BYTE PTR [r11+rax*1+0xcb0]
     join1:
      +0x23  lea     eax, [rbp+0x37]
      +0x26  movzx   r9d, BYTE PTR [r11+rax*1+0xcb0]
      +0x2f  mov     r10, r9
      +0x32  cmp     r9d, esi
      +0x35  jb      join2
      +0x37  cmp     r9d, 0x37
      +0x3b  ja      join2
      +0x3d  lea     rdi, [r8+0x8]
      +0x41  mov     rcx, r8
      +0x44  xor     eax, eax
      +0x46  mov     QWORD PTR [r8], 0x0
      +0x4d  mov     QWORD PTR [r8+0x3f8], 0x0
      +0x58  and     rdi, 0xfffffffffffffff8
      +0x5c  sub     rcx, rdi
      +0x5f  add     ecx, 0x400
      +0x65  shr     ecx, 0x3
      +0x68  rep stos QWORD PTR es:[rdi], rax
      +0x6b  cmp     esi, r9d
      +0x6e  jae     join3
      +0x70  lea     edx, [rsi+0xcb0]
      +0x76  mov     eax, esi
      +0x78  add     rdx, r11
      +0x7b  nop     DWORD PTR [rax+rax*1+0x0]
     loop1:
      +0x80  movzx   ecx, BYTE PTR [rdx]
      +0x83  add     rdx, 0x1
      +0x87  mov     DWORD PTR [r8+rcx*4], 0x1
      +0x8f  mov     ecx, eax
      +0x91  add     eax, 0x1
     loop1_test1:
      +0x94  cmp     eax, r9d
      +0x97  jae     join3
     loop1_next1:
      +0x99  cmp     esi, eax
      +0x9b  jae     loop1
      +0x9d  movzx   edi, BYTE PTR [rdx]
     loop1_test2:
      +0xa0  cmp     BYTE PTR [rbx+rcx*1], dil
      +0xa4  jb      loop1
     join2: loop1_exit1:
      +0xa6  mov     eax, 0xffffffff
      +0xab  pop     rbx
      +0xac  pop     rbp
     ret1:
      +0xad  ret
      +0xae  xchg    ax, ax
     join3: loop1_exit2:
      +0xb0  cmp     ebp, 0x5
      +0xb3  je      join5
     join4: loop2_exit1:
      +0xb5  xor     eax, eax
      +0xb7  pop     rbx
      +0xb8  pop     rbp
     ret2:
      +0xb9  ret
      +0xba  nop     WORD PTR [rax+rax*1+0x0]
     join5:
      +0xc0  cmp     r9d, 0x37
      +0xc4  je      join4
      +0xc6  cmp     BYTE PTR [r11+r10*1+0xcb0], 0x0
      +0xcf  jne     join2
      +0xd1  nop     DWORD PTR [rax+0x0]
     loop2:
      +0xd8  add     r10, 0x1
     loop2_test1:
      +0xdc  cmp     r10d, 0x37
      +0xe0  je      join4
     loop2_test2: loop2_next1:
      +0xe2  cmp     BYTE PTR [r11+r10*1+0xcb0], 0x0
     loop2_back:
      +0xeb  je      loop2
     loop2_exit2:
      +0xed  jmp     join2
 ***)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_sig_unpack_hints"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial h is distinct from the code, the hints and    *)
(* the stack frame, where the function saves RBP and RBX below the return    *)
(* address. The return value is that of mld_unpack_hints_ret, and if it is   *)
(* 0, the coefficients are those of mld_unpack_hints.                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!h sig b i pc stackpointer returnaddress.
        i < 6 /\
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (h,1024))
            [(word pc,libmldsa_size); (word_add sig (word 3248),61);
             (word_sub stackpointer (word 16),16); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,libmldsa_size); (word_add sig (word 3248),61)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_sig_unpack_hints) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [h; sig; word i] s /\
                  (read DF s <=> false) /\
                  (!j. j < 61
                       ==> read(memory :> bytes8
                             (word_add sig (word(3248 + j)))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word_zx(mld_unpack_hints_ret 55 6 b i) /\
                  (mld_unpack_hints_ret 55 6 b i = word 0
                   ==> !p. p < 256
                           ==> read(memory :> bytes32
                                 (word_add h (word(4 * p)))) s =
                               mld_unpack_hints 55 b i p))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(h,1024);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_SIG_UNPACK_HINTS_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    MLDSA_NATIVE_SIG_UNPACK_HINTS_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the bytes of the hints, i and the addresses,     *)
(* with all accesses within the hints, h, the stack frame and the slot of    *)
(* the return address, and the writes within h and the stack frame.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e h sig b i pc stackpointer returnaddress.
        i < 6 /\
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (h,1024))
            [(word pc,libmldsa_size); (word_add sig (word 3248),61);
             (word_sub stackpointer (word 16),16); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,libmldsa_size); (word_add sig (word 3248),61)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_sig_unpack_hints) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [h; sig; word i] s /\
                  (read DF s <=> false) /\
                  (!j. j < 61
                       ==> read(memory :> bytes8
                             (word_add sig (word(3248 + j)))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word_zx(mld_unpack_hints_ret 55 6 b i) /\
                  (mld_unpack_hints_ret 55 6 b i = word 0
                   ==> !p. p < 256
                           ==> read(memory :> bytes32
                                 (word_add h (word(4 * p)))) s =
                               mld_unpack_hints 55 b i p) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events b i h sig pc
                            (word_sub stackpointer (word 16)) returnaddress /\
                     memaccess_inbounds e2
                      [word_add sig (word 3248),61; h,1024;
                       word_sub stackpointer (word 16),16; stackpointer,8]
                      [h,1024; word_sub stackpointer (word 16),16]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(h,1024);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_SIG_UNPACK_HINTS_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
    MLDSA_NATIVE_SIG_UNPACK_HINTS_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* hints and i as above.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e h sig b i pc stackpointer returnaddress.
        i < 6 /\
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (h,1024))
            [(word pc,libmldsa_size); (word_add sig (word 3248),61);
             (word_sub stackpointer (word 16),16); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),16))
            [(word pc,libmldsa_size); (word_add sig (word 3248),61)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_sig_unpack_hints) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [h; sig; word i] s /\
                  (read DF s <=> false) /\
                  (!j. j < 61
                       ==> read(memory :> bytes8
                             (word_add sig (word(3248 + j)))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events b i h sig pc
                            (word_sub stackpointer (word 16)) returnaddress /\
                     memaccess_inbounds e2
                      [word_add sig (word 3248),61; h,1024;
                       word_sub stackpointer (word 16),16; stackpointer,8]
                      [h,1024; word_sub stackpointer (word 16),16]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(h,1024);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_SIG_UNPACK_HINTS_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
    MLDSA_NATIVE_SIG_UNPACK_HINTS_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
