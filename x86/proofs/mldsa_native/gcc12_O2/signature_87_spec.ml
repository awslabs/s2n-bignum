(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message (pure ML-DSA, randomized): the statement. This is the   *)
(* code for mldsa87_signature (mld_sign_signature in sign.c, an external API *)
(* function) from mldsa-native's portable C implementation compiled by gcc   *)
(* 12 with -O2 (see mldsa_native/README.md), which aligns its frame to 32    *)
(* bytes, builds the prefix 0 || ctxlen || ctx of pure ML-DSA in a buffer on *)
(* the stack with mldsa87_prepare_domain_separation_prefix, returning -9     *)
(* (MLD_ERR_INVALID_ARG) if ctxlen > 255, gets the 32 bytes of rnd with      *)
(* randombytes, which it calls through the PLT, returning -3                 *)
(* (MLD_ERR_RNG_FAIL) if that fails, and signs the message with that prefix  *)
(* with mldsa87_signature_internal. It zeroes the signature on any failure,  *)
(* with a memset that gcc inlines as quadword stores and REP STOSQ, and its  *)
(* buffers with SSE stores and REP STOSQ, so that the direction flag must be *)
(* clear, as the ABI requires on entry. It is verified in the whole image    *)
(* (see libmldsa.ml), using the theorems for the callees and the contracts   *)
(* memset_full_contract, memcpy_full_contract and                            *)
(* randombytes_safety_contract of utils/mldsa_native_libc.ml for the C       *)
(* library functions, and shown to be constant time and memory safe.         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/prepare_domain_separation_prefix_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/signature_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for randombytes:

    mldsa87_signature:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  mov     r15, r9
      +0x16  xor     r9d, r9d
      +0x19  push    r14
      +0x1b  mov     r14, rdx
      +0x1e  xor     edx, edx
      +0x20  push    r13
      +0x22  push    r12
      +0x24  lea     r12, [rbp-0x190]
      +0x2b  push    r10
      +0x2d  push    rbx
      +0x2e  mov     rbx, rdi
      +0x31  mov     rdi, r12
      +0x34  sub     rsp, 0x1a0
      +0x3b  mov     QWORD PTR [rbp-0x1b8], rsi
      +0x42  xor     esi, esi
      +0x44  call    mldsa87_prepare_domain_separation_prefix
     after_mldsa87_prepare_domain_separation_prefix:
      +0x49  test    rax, rax
      +0x4c  mov     QWORD PTR [rbp-0x1c0], rax
      +0x53  jne     join3
      +0x55  mov     edx, 0xfffffff7
      +0x5a  lea     r13, [rbp-0x1b0]
     join1:
      +0x61  lea     rdi, [rbx+0x8]
      +0x65  mov     rcx, rbx
      +0x68  xor     eax, eax
      +0x6a  mov     QWORD PTR [rbx], 0x0
      +0x71  mov     QWORD PTR [rbx+0x120b], 0x0
      +0x7c  and     rdi, 0xfffffffffffffff8
      +0x80  sub     rcx, rdi
      +0x83  add     ecx, 0x1213
      +0x89  shr     ecx, 0x3
      +0x8c  rep stos QWORD PTR es:[rdi], rax
     join2:
      +0x8f  pxor    xmm0, xmm0
      +0x93  movaps  XMMWORD PTR [rbp-0x1b0], xmm0
      +0x9a  movaps  XMMWORD PTR [rbp-0x1a0], xmm0
      +0xa1  xor     eax, eax
      +0xa3  mov     rdi, r12
      +0xa6  mov     ecx, 0x29
      +0xab  rep stos QWORD PTR es:[rdi], rax
      +0xae  mov     DWORD PTR [rdi], 0x0
      +0xb4  lea     rsp, [rbp-0x30]
      +0xb8  mov     eax, edx
      +0xba  pop     rbx
      +0xbb  pop     r10
      +0xbd  pop     r12
      +0xbf  pop     r13
      +0xc1  pop     r14
      +0xc3  pop     r15
      +0xc5  pop     rbp
      +0xc6  lea     rsp, [r10-0x8]
     ret:
      +0xca  ret
      +0xcb  nop     DWORD PTR [rax+rax*1+0x0]
     join3:
      +0xd0  lea     r13, [rbp-0x1b0]
      +0xd7  mov     esi, 0x20
      +0xdc  mov     rdi, r13
      +0xdf  call    randombytes
     after_randombytes:
      +0xe4  mov     edx, 0xfffffffd
      +0xe9  test    eax, eax
      +0xeb  jne     join1
      +0xf1  push    0x0
      +0xf3  mov     r8, QWORD PTR [rbp-0x1c0]
      +0xfa  mov     rcx, r12
      +0xfd  mov     rdx, r14
     +0x100  push    r15
     +0x102  mov     rsi, QWORD PTR [rbp-0x1b8]
     +0x109  mov     r9, r13
     +0x10c  mov     rdi, rbx
     +0x10f  call    mldsa87_signature_internal
     after_mldsa87_signature_internal:
     +0x114  mov     edx, eax
     +0x116  pop     rax
     +0x117  pop     rcx
     +0x118  test    edx, edx
     +0x11a  je      join2
     +0x120  jmp     join1

    plt_randombytes:
       +0x0  jmp     QWORD PTR [rip+0xefca]
                     // got_randombytes
       +0x6  push    0x1
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_signature"; layout_range "plt_randombytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (4896 bytes), the message M of mlen bytes at m and   *)
(* the context C of ctxlen bytes at ctx, with MU the mu of signing (H(tr ||  *)
(* prefix || M, 64)). The result is -9 if ctxlen > 255, and otherwise, for   *)
(* some RND (the random bytes), either -3 or the result of signing with RND; *)
(* the signature is mld_sign_sig_87 skb MU RND if the result is 0, and zero  *)
(* otherwise. The theorem assumes that the samplings terminate for every     *)
(* RND. The function keeps the stack pointer of the entry in R10, lowers RSP *)
(* by up to 31 bytes to align it to 32 bytes, copies the return address      *)
(* there and saves RBP, the frame pointer, and six more registers, and       *)
(* reserves the stack for the prefix, rnd, two saved values and the two      *)
(* arguments of mldsa87_signature_internal on the stack, whose call uses     *)
(* 112229 bytes below them, with its return address: 112756 bytes of stack   *)
(* below the return address in all. The GOT entries of the C library         *)
(* functions and the region (ea,el) that they may read are apart from the    *)
(* signature and the stack.                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
           [(sig,4627); (word_sub stackpointer (word 112756),112756)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112756),112756)]
           [(m,mlen); (ctx,ctxlen); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 112756),
                                  112756)])`;;

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, rho, the result and, *)
(* for the RND of the signature, what the C code declassifies in signing     *)
(* (mld_sign_declass_87), with all accesses within the arguments, the stack, *)
(* the return address, the GOT entries, the region (ea,el) that the C        *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the signature and the stack.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
           [(sig,4627); (word_sub stackpointer (word 112756),112756)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112756),112756)]
           [(m,mlen); (ctx,ctxlen); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                             (word_sub stackpointer (word 112756))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,4627; m,mlen; ctx,ctxlen; sk,4896;
                          word_sub stackpointer (word 112756),112756;
                          stackpointer,8; word(pc + got_memset),8;
                          word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_reduce_consts),16;
                          word(pc +
                        mldsa87_prepare_domain_separation_prefix_switch1_table),
                          52;
                          word(pc + rodata_oid_map_0_3),192]
                         [sig,4627;
                          word_sub stackpointer (word 112756),112756]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112756),
                                  112756)])`;;

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone. The events are given for an RND of *)
(* the signature: they depend on what signing declassifies, which only RND   *)
(* determines.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
           [(sig,4627); (word_sub stackpointer (word 112756),112756)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112756),112756)]
           [(m,mlen); (ctx,ctxlen); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                             (word_sub stackpointer (word 112756))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,4627; m,mlen; ctx,ctxlen; sk,4896;
                          word_sub stackpointer (word 112756),112756;
                          stackpointer,8; word(pc + got_memset),8;
                          word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_reduce_consts),16;
                          word(pc +
                        mldsa87_prepare_domain_separation_prefix_switch1_table),
                          52;
                          word(pc + rodata_oid_map_0_3),192]
                         [sig,4627;
                          word_sub stackpointer (word 112756),112756]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112756),
                                  112756)])`;;

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
