(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a message (pure ML-DSA): the statement. This is  *)
(* the code for mldsa87_verify (mld_sign_verify in sign.c, an external API   *)
(* function) from mldsa-native's portable C implementation compiled by clang *)
(* 23 with -O3 and MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which *)
(* returns -9 if ctxlen > 255 and otherwise builds the prefix 0 || ctxlen || *)
(* ctx of pure ML-DSA in a buffer on the stack (it inlines                   *)
(* mld_prepare_domain_separation_prefix, calling memcpy through the PLT for  *)
(* the context if ctxlen is not 0), and verifies with that prefix with       *)
(* mldsa87_verify_internal. It zeroes the prefix with memset, which it calls *)
(* through the PLT, in both cases. It realigns its stack frame to 32 bytes   *)
(* (utils/mldsa_native_realign.ml). It is verified in the whole image (see   *)
(* libmldsa.ml), using the theorem for the callee and the contracts          *)
(* memset_full_contract and memcpy_full_contract of                          *)
(* utils/mldsa_native_libc.ml for the C library functions, and shown to be   *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stubs for memcpy, memset:

    mldsa87_verify:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  push    r13
       +0xa  push    r12
       +0xc  push    rbx
       +0xd  and     rsp, 0xffffffffffffffe0
      +0x11  sub     rsp, 0x1a0
      +0x18  mov     ebx, 0xfffffff7
      +0x1d  cmp     r8, 0xff
      +0x24  ja      join2                     ---+
      +0x26  mov     BYTE PTR [rsp+0x20], 0x0     |
      +0x2b  mov     BYTE PTR [rsp+0x21], r8b     |
      +0x30  test    r8, r8                       |
      +0x33  je      join1                     -+ |
      +0x35  lea     rax, [rsp+0x22]            | |
      +0x3a  mov     rbx, rdi                   | |
      +0x3d  mov     rdi, rax                   | |
      +0x40  mov     r14, rsi                   | |
      +0x43  mov     rsi, rcx                   | |
      +0x46  mov     r15, rdx                   | |
      +0x49  mov     rdx, r8                    | |
      +0x4c  mov     r12, r9                    | |
      +0x4f  mov     r13, r8                    | |
      +0x52  call    memcpy                     | |
    after_memcpy:                               | |
      +0x57  mov     rdi, rbx                   | |
      +0x5a  mov     rsi, r14                   | |
      +0x5d  mov     rdx, r15                   | |
      +0x60  mov     r8, r13                    | |
      +0x63  mov     r9, r12                    | |
    join1:                                      | |
      +0x66  add     r8, 0x2                   <+ |
      +0x6a  mov     DWORD PTR [rsp], 0x0         |
      +0x71  lea     rcx, [rsp+0x20]              |
      +0x76  call    mldsa87_verify_internal      |
    after_mldsa87_verify_internal:                |
      +0x7b  mov     ebx, eax                     |
    join2:                                        |
      +0x7d  lea     r14, [rsp+0x20]           <--+
      +0x82  mov     edx, 0x14c
      +0x87  mov     rdi, r14
      +0x8a  xor     esi, esi
      +0x8c  call    memset
    after_memset:
      +0x91  mov     eax, ebx
      +0x93  lea     rsp, [rbp-0x28]
      +0x97  pop     rbx
      +0x98  pop     r12
      +0x9a  pop     r13
      +0x9c  pop     r14
      +0x9e  pop     r15
      +0xa0  pop     rbp
      +0xa1  xor     ecx, ecx
      +0xa3  xor     edi, edi
      +0xa5  xor     edx, edx
      +0xa7  xor     esi, esi
      +0xa9  xor     r8d, r8d
      +0xac  xor     r9d, r9d
    ret:
      +0xaf  ret

    plt_memcpy:
       +0x0  jmp     QWORD PTR [rip+0x26fd2]
                     // got_memcpy
       +0x6  push    0x0
       +0xb  jmp     <.plt>

    plt_memset:
       +0x0  jmp     QWORD PTR [rip+0x26fc2]
                     // got_memset
       +0x6  push    0x2
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_VERIFY_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_verify";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (4627 bytes), the message M of mlen bytes at m, the *)
(* context C of ctxlen bytes at ctx and the public key pkb at pk (2592       *)
(* bytes): the result is -9 if ctxlen > 255, and otherwise 0 if the          *)
(* signature is accepted for the message with the prefix of pure ML-DSA, and *)
(* -6 if not. The function saves RBP, the frame pointer, and five more       *)
(* registers below the return address, lowers RSP by up to 31 bytes to align *)
(* it to 32 bytes, reserves 416 bytes for the prefix and ext, the seventh    *)
(* argument of mldsa87_verify_internal, below which that function uses 14565 *)
(* bytes with its return address: 15068 bytes of stack below the return      *)
(* address in all. The GOT entries of memcpy and memset and the region       *)
(* (ea,el) that they may read are apart from the stack.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigb pkb M C pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 60 64
                (num_of_bytelist(list_of_seq sigb 64))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 15068),15068))
              [(sig,4627); (m,mlen); (ctx,ctxlen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_verify) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb
                       (mld_verify_mu 2592 pkb (2 + ctxlen)
                         (num_of_bytelist
                           (mld_domain_separation_prefix 0
                             (bytelist_of_num ctxlen C) []))
                         mlen M)
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 15068),15068)])`;;

let MLDSA_NATIVE_VERIFY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the signature, the   *)
(* message, the context and the public key, all public, the addresses of     *)
(* memset and memcpy and the stack, with all accesses within the arguments,  *)
(* the stack, the return address, the GOT entries, the region (ea,el) that   *)
(* the C library functions may read and the constants of the callees, and    *)
(* the writes within the stack.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 60 64
                (num_of_bytelist(list_of_seq sigb 64))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 15068),15068))
              [(sig,4627); (m,mlen); (ctx,ctxlen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_verify) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb
                       (mld_verify_mu 2592 pkb (2 + ctxlen)
                         (num_of_bytelist
                           (mld_domain_separation_prefix 0
                             (bytelist_of_num ctxlen C) []))
                         mlen M)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            mf mc pc (word_sub stackpointer (word 15068))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; ctx,ctxlen; pk,2592;
                         word_sub stackpointer (word 15068),15068;
                         stackpointer,8; word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc +
                            mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy_consts),
                          32;
                          word(pc + mldsa87_verify_internal_consts),784]
                        [word_sub stackpointer (word 15068),15068]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 15068),15068)])`;;

let MLDSA_NATIVE_VERIFY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 60 64
                (num_of_bytelist(list_of_seq sigb 64))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 15068),15068))
              [(sig,4627); (m,mlen); (ctx,ctxlen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_verify) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            mf mc pc (word_sub stackpointer (word 15068))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; ctx,ctxlen; pk,2592;
                         word_sub stackpointer (word 15068),15068;
                         stackpointer,8; word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc +
                            mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy_consts),
                          32;
                          word(pc + mldsa87_verify_internal_consts),784]
                        [word_sub stackpointer (word 15068),15068]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 15068),15068)])`;;

let MLDSA_NATIVE_VERIFY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
