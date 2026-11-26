(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message (pure ML-DSA, randomized): the statement. This is the   *)
(* code for mldsa87_signature (mld_sign_signature in sign.c, an external API *)
(* function) from mldsa-native's portable C implementation compiled by clang *)
(* 23 with -O3 and MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which *)
(* aligns its frame to 32 bytes, returns early with -9 (MLD_ERR_INVALID_ARG) *)
(* if ctxlen > 255, builds the prefix 0 || ctxlen || ctx of pure ML-DSA in a *)
(* buffer on the stack (it inlines mld_prepare_domain_separation_prefix,     *)
(* calling memcpy through the PLT for the context if ctxlen is not 0), gets  *)
(* the 32 bytes of rnd with randombytes, which it calls through the PLT,     *)
(* returning -3 (MLD_ERR_RNG_FAIL) if that fails, and signs the message with *)
(* that prefix with mldsa87_signature_internal. It zeroes the signature on   *)
(* any failure, with memset, which it calls through the PLT, and rnd with    *)
(* SSE stores and the prefix with memset in all cases, so that the direction *)
(* flag must be clear, as the ABI requires on entry. It is verified in the   *)
(* whole image (see libmldsa.ml), using the theorem for the callee and the   *)
(* contracts memset_full_contract, memcpy_full_contract and                  *)
(* randombytes_safety_contract of utils/mldsa_native_libc.ml for the C       *)
(* library functions, and shown to be constant time and memory safe.         *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stubs for memcpy, randombytes, memset:

    mldsa87_signature:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  push    r13
       +0xa  push    r12
       +0xc  push    rbx
       +0xd  and     rsp, 0xffffffffffffffe0
      +0x11  sub     rsp, 0x1c0
      +0x18  mov     rbx, rdi
      +0x1b  mov     r15d, 0xfffffff7
      +0x21  cmp     r8, 0xff
      +0x28  ja      join2                         -----+
      +0x2a  mov     r12, r8                            |
      +0x2d  mov     QWORD PTR [rsp+0x18], rsi          |
      +0x32  mov     r14, rdx                           |
      +0x35  mov     r13, r9                            |
      +0x38  mov     BYTE PTR [rsp+0x40], 0x0           |
      +0x3d  mov     BYTE PTR [rsp+0x41], r12b          |
      +0x42  test    r8, r8                             |
      +0x45  je      join1                         -+   |
      +0x47  lea     rdi, [rsp+0x42]                |   |
      +0x4c  mov     rsi, rcx                       |   |
      +0x4f  mov     rdx, r12                       |   |
      +0x52  call    memcpy                         |   |
    join1: after_memcpy:                            |   |
      +0x57  lea     rdi, [rsp+0x20]               <+   |
      +0x5c  mov     esi, 0x20                          |
      +0x61  call    randombytes                        |
    after_randombytes:                                  |
      +0x66  mov     r15d, 0xfffffffd                   |
      +0x6c  test    eax, eax                           |
      +0x6e  mov     rsi, QWORD PTR [rsp+0x18]          |
      +0x73  jne     join2                         -+   |
      +0x75  add     r12, 0x2                       |   |
      +0x79  lea     rcx, [rsp+0x40]                |   |
      +0x7e  lea     r9, [rsp+0x20]                 |   |
      +0x83  mov     rdi, rbx                       |   |
      +0x86  mov     rdx, r14                       |   |
      +0x89  mov     r8, r12                        |   |
      +0x8c  push    0x0                            |   |
      +0x8e  push    r13                            |   |
      +0x90  call    mldsa87_signature_internal     |   |
    after_mldsa87_signature_internal:               |   |
      +0x95  add     rsp, 0x10                      |   |
      +0x99  mov     r15d, eax                      |   |
      +0x9c  test    eax, eax                       |   |
      +0x9e  je      +0xf5                         ---+ |
    join2:                                          | | |
      +0xa0  mov     edx, 0x1213                   <+---+
      +0xa5  mov     rdi, rbx                         |
      +0xa8  xor     esi, esi                         |
      +0xaa  call    memset                           |
    join3: after_memset_1:                            |
      +0xaf  xorps   xmm0, xmm0                    <+ |
      +0xb2  movaps  XMMWORD PTR [rsp+0x30], xmm0   | |
      +0xb7  movaps  XMMWORD PTR [rsp+0x20], xmm0   | |
      +0xbc  lea     rax, [rsp+0x20]                | |
      +0xc1  lea     rbx, [rsp+0x40]                | |
      +0xc6  mov     edx, 0x14c                     | |
      +0xcb  mov     rdi, rbx                       | |
      +0xce  xor     esi, esi                       | |
      +0xd0  call    memset                         | |
    after_memset_2:                                 | |
      +0xd5  mov     eax, r15d                      | |
      +0xd8  lea     rsp, [rbp-0x28]                | |
      +0xdc  pop     rbx                            | |
      +0xdd  pop     r12                            | |
      +0xdf  pop     r13                            | |
      +0xe1  pop     r14                            | |
      +0xe3  pop     r15                            | |
      +0xe5  pop     rbp                            | |
      +0xe6  xor     ecx, ecx                       | |
      +0xe8  xor     edi, edi                       | |
      +0xea  xor     edx, edx                       | |
      +0xec  xor     esi, esi                       | |
      +0xee  xor     r8d, r8d                       | |
      +0xf1  xor     r9d, r9d                       | |
    ret:                                            | |
      +0xf4  ret                                    | |
      +0xf5  xor     r15d, r15d                    <--+
      +0xf8  jmp     join3                         -+

    plt_memcpy:
       +0x0  jmp     QWORD PTR [rip+0x26fd2]
                     // got_memcpy
       +0x6  push    0x0
       +0xb  jmp     <.plt>

    plt_randombytes:
       +0x0  jmp     QWORD PTR [rip+0x26fca]
                     // got_randombytes
       +0x6  push    0x1
       +0xb  jmp     <.plt>

    plt_memset:
       +0x0  jmp     QWORD PTR [rip+0x26fc2]
                     // got_memset
       +0x6  push    0x2
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_signature";
    layout_range "plt_memcpy";
    layout_range "plt_randombytes";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (4896 bytes), the message M of mlen bytes at m and   *)
(* the context C of ctxlen bytes at ctx, with MU the mu of signing (H(tr ||  *)
(* prefix || M, 64)). The result is -9 if ctxlen > 255, and otherwise, for   *)
(* some RND (the random bytes), either -3 or the result of signing with RND; *)
(* the signature is mld_sign_sig_87 skb MU RND if the result is 0, and zero  *)
(* otherwise. The theorem assumes that the samplings terminate for every     *)
(* RND. The function saves RBP, the frame pointer, and five more registers   *)
(* below the return address, lowers RSP by up to 31 bytes to align it to 32  *)
(* bytes, reserves 448 bytes for the prefix, rnd and two saved values, and   *)
(* then the two arguments of mldsa87_signature_internal on the stack, whose  *)
(* call uses 16462 bytes below them, with its return address: 17013 bytes of *)
(* stack below the return address in all. The GOT entries of the C library   *)
(* functions and the region (ea,el) that they may read are apart from the    *)
(* signature and the stack.                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig m mlen ctx ctxlen sk skb M C MU pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          MU = mld_sign_mu (\j. skb(64 + j)) (2 + ctxlen)
                (num_of_bytelist
                  (mld_domain_separation_prefix 0
                    (bytelist_of_num ctxlen C) []))
                mlen M /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
               !RND. RND < 2 EXP 256
                     ==> mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 17013),17013)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 17013),17013)]
           [(m,mlen); (ctx,ctxlen); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_signature) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; sk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                    mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (255 < ctxlen ==> C_RETURN s = word 4294967287) /\
                      (ctxlen <= 255
                       ==> C_RETURN s = word 4294967293 \/
                           C_RETURN s =
                            (if mld_sign_ok_87 skb MU RND then word 0
                             else word 4294967292)) /\
                      (!t. t < 4627
                           ==> read(memory :> bytes8
                                     (word_add sig (word t))) s =
                               if C_RETURN s = word 0
                               then mld_sign_sig_87 skb MU RND t
                               else word 0))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 17013),17013)])`;;

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, rho, the result and, *)
(* for the RND of the signature, what the C code declassifies in signing     *)
(* (mld_sign_declass_87), with all accesses within the arguments, the stack, *)
(* the return address, the GOT entries, the region (ea,el) that the C        *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the signature and the stack.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen sk skb M C MU pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          MU = mld_sign_mu (\j. skb(64 + j)) (2 + ctxlen)
                (num_of_bytelist
                  (mld_domain_separation_prefix 0
                    (bytelist_of_num ctxlen C) []))
                mlen M /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
               !RND. RND < 2 EXP 256
                     ==> mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 17013),17013)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 17013),17013)]
           [(m,mlen); (ctx,ctxlen); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_signature) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; sk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                    mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (255 < ctxlen ==> C_RETURN s = word 4294967287) /\
                      (ctxlen <= 255
                       ==> C_RETURN s = word 4294967293 \/
                           C_RETURN s =
                            (if mld_sign_ok_87 skb MU RND then word 0
                             else word 4294967292)) /\
                      (!t. t < 4627
                           ==> read(memory :> bytes8
                                     (word_add sig (word t))) s =
                               if C_RETURN s = word 0
                               then mld_sign_sig_87 skb MU RND t
                               else word 0) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events sig m mlen ctx ctxlen sk
                             (mld_sk_rho skb) (C_RETURN s)
                             (mld_sign_declass_87 skb MU RND) mf mc mr pc
                             (word_sub stackpointer (word 17013))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,4627; m,mlen; ctx,ctxlen; sk,4896;
                          word_sub stackpointer (word 17013),17013;
                          stackpointer,8; word(pc + got_memset),8;
                          word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa87_signature_internal_consts),784;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                         [sig,4627;
                          word_sub stackpointer (word 17013),17013]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 17013),17013)])`;;

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone. The events are given for an RND of *)
(* the signature: they depend on what signing declassifies, which only RND   *)
(* determines.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen sk skb M C MU pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          MU = mld_sign_mu (\j. skb(64 + j)) (2 + ctxlen)
                (num_of_bytelist
                  (mld_domain_separation_prefix 0
                    (bytelist_of_num ctxlen C) []))
                mlen M /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
               !RND. RND < 2 EXP 256
                     ==> mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 17013),17013)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 17013),17013)]
           [(m,mlen); (ctx,ctxlen); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_signature) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; sk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                    mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (!t. t < 4627
                           ==> read(memory :> bytes8
                                     (word_add sig (word t))) s =
                               if C_RETURN s = word 0
                               then mld_sign_sig_87 skb MU RND t
                               else word 0) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events sig m mlen ctx ctxlen sk
                             (mld_sk_rho skb) (C_RETURN s)
                             (mld_sign_declass_87 skb MU RND) mf mc mr pc
                             (word_sub stackpointer (word 17013))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,4627; m,mlen; ctx,ctxlen; sk,4896;
                          word_sub stackpointer (word 17013),17013;
                          stackpointer,8; word(pc + got_memset),8;
                          word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa87_signature_internal_consts),784;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448]
                         [sig,4627;
                          word_sub stackpointer (word 17013),17013]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 17013),17013)])`;;

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
