(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with external mu (randomized): the statement. This is the code    *)
(* for mldsa87_signature_extmu (mld_sign_signature_extmu in sign.c, an       *)
(* external API function) from mldsa-native's portable C implementation      *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which aligns    *)
(* its frame to 32 bytes, gets the 32 bytes of rnd with randombytes, which   *)
(* it calls through the PLT, into a buffer on the stack, returns -3          *)
(* (MLD_ERR_RNG_FAIL) if that fails, and otherwise signs with the given mu   *)
(* with mldsa87_signature_internal (with ext = 1, the message being mu), and *)
(* then zeroes rnd with SSE stores. It is verified in the whole image (see   *)
(* libmldsa.ml), using the theorem for the callee and the contracts          *)
(* memset_full_contract and randombytes_safety_contract of                   *)
(* utils/mldsa_native_libc.ml for the C library functions, and shown to be   *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/signature_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for randombytes:

    mldsa87_signature_extmu:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r14
      +0x13  mov     r14, rdx
      +0x16  push    r13
      +0x18  mov     r13, rsi
      +0x1b  mov     esi, 0x20
      +0x20  push    r12
      +0x22  mov     r12, rdi
      +0x25  push    r10
      +0x27  push    rbx
      +0x28  lea     rbx, [rbp-0x50]
      +0x2c  mov     rdi, rbx
      +0x2f  sub     rsp, 0x28
      +0x33  call    randombytes
     after_randombytes:
      +0x38  test    eax, eax
      +0x3a  jne     join2
      +0x3c  push    0x1
      +0x3e  xor     ecx, ecx
      +0x40  mov     edx, 0x40
      +0x45  mov     r9, rbx
      +0x48  push    r14
      +0x4a  xor     r8d, r8d
      +0x4d  mov     rsi, r13
      +0x50  mov     rdi, r12
      +0x53  call    mldsa87_signature_internal
     after_mldsa87_signature_internal:
      +0x58  pop     rdx
      +0x59  pop     rcx
     join1:
      +0x5a  pxor    xmm0, xmm0
      +0x5e  movaps  XMMWORD PTR [rbp-0x50], xmm0
      +0x62  movaps  XMMWORD PTR [rbp-0x40], xmm0
      +0x66  lea     rsp, [rbp-0x28]
      +0x6a  pop     rbx
      +0x6b  pop     r10
      +0x6d  pop     r12
      +0x6f  pop     r13
      +0x71  pop     r14
      +0x73  pop     rbp
      +0x74  lea     rsp, [r10-0x8]
     ret:
      +0x78  ret
      +0x79  nop     DWORD PTR [rax+0x0]
     join2:
      +0x80  mov     eax, 0xfffffffd
      +0x85  jmp     join1

    plt_randombytes:
       +0x0  jmp     QWORD PTR [rip+0xefca]
                     // got_randombytes
       +0x6  push    0x1
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_signature_extmu"; layout_range "plt_randombytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (4896 bytes) and mu, MU, the 64 bytes at mu: for     *)
(* some RND (the random bytes), the result is -3, or that of signing with    *)
(* RND, with the signature mld_sign_sig_87 skb MU RND (zero if signing       *)
(* fails). The theorem assumes that the samplings terminate for every RND.   *)
(* The function keeps the stack pointer of the entry in R10, lowers RSP by   *)
(* up to 31 bytes to align it to 32 bytes, copies the return address there   *)
(* and saves RBP, the frame pointer, and five more registers, and reserves   *)
(* the stack for rnd and the two arguments of mldsa87_signature_internal on  *)
(* the stack, whose call uses 112229 bytes below them, with its return       *)
(* address: 112372 bytes of stack below the return address in all. The GOT   *)
(* entries of the C library functions and the region (ea,el) that they may   *)
(* read are apart from the signature and the stack.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mr ea el ev.
     memset_full_contract mf ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig mu sk skb MU pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          (!RND. RND < 2 EXP 256
                 ==> mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112372),112372)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112372),112372)]
           [(mu,64); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (word(pc + got_randombytes),8);
            (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_signature_extmu) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; mu; sk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                    mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(mu,64)) s = MU /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (C_RETURN s = word 4294967293 \/
                       C_RETURN s =
                       (if mld_sign_ok_87 skb MU RND then word 0
                        else word 4294967292) /\
                       (!t. t < 4627
                            ==> read(memory :> bytes8
                                      (word_add sig (word t))) s =
                                mld_sign_sig_87 skb MU RND t)))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112372),
                                  112372)])`;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result and, for the RND  *)
(* of the signature, what the C code declassifies in signing                 *)
(* (mld_sign_declass_87), with all accesses within the arguments, the stack, *)
(* the return address, the GOT entries, the region (ea,el) that the C        *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the signature and the stack.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mr ea el ev.
     memset_full_contract mf ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig mu sk skb MU pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          (!RND. RND < 2 EXP 256
                 ==> mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112372),112372)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112372),112372)]
           [(mu,64); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (word(pc + got_randombytes),8);
            (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_signature_extmu) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; mu; sk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                    mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(mu,64)) s = MU /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (C_RETURN s = word 4294967293 \/
                       C_RETURN s =
                       (if mld_sign_ok_87 skb MU RND then word 0
                        else word 4294967292) /\
                       (!t. t < 4627
                            ==> read(memory :> bytes8
                                      (word_add sig (word t))) s =
                                mld_sign_sig_87 skb MU RND t)) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events sig mu sk (mld_sk_rho skb) (C_RETURN s)
                             (mld_sign_declass_87 skb MU RND) mf mr pc
                             (word_sub stackpointer (word 112372))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,4627; mu,64; sk,4896;
                          word_sub stackpointer (word 112372),112372;
                          stackpointer,8; word(pc + got_memset),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_reduce_consts),16]
                         [sig,4627;
                          word_sub stackpointer (word 112372),112372]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112372),
                                  112372)])`;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone. The events are given for an RND of *)
(* the signature if the result is 0: they depend on what signing             *)
(* declassifies, which only RND determines.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mr ea el ev.
     memset_full_contract mf ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig mu sk skb MU pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          (!RND. RND < 2 EXP 256
                 ==> mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112372),112372)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112372),112372)]
           [(mu,64); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (word(pc + got_randombytes),8);
            (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa87_signature_extmu) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; mu; sk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                    mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(mu,64)) s = MU /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (C_RETURN s = word 0
                       ==> !t. t < 4627
                               ==> read(memory :> bytes8
                                         (word_add sig (word t))) s =
                                   mld_sign_sig_87 skb MU RND t) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events sig mu sk (mld_sk_rho skb) (C_RETURN s)
                             (mld_sign_declass_87 skb MU RND) mf mr pc
                             (word_sub stackpointer (word 112372))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,4627; mu,64; sk,4896;
                          word_sub stackpointer (word 112372),112372;
                          stackpointer,8; word(pc + got_memset),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_reduce_consts),16]
                         [sig,4627;
                          word_sub stackpointer (word 112372),112372]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112372),
                                  112372)])`;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
