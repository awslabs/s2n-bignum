(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message (pure ML-DSA, randomized): the statement. This is the   *)
(* code for mldsa65_signature (mld_sign_signature in sign.c, an external API *)
(* function) from mldsa-native's portable C implementation compiled by clang *)
(* 23 with -O3 as one translation unit with MLD_CONFIG_REDUCE_RAM (see       *)
(* mldsa_native/README.md), which builds the prefix 0 || ctxlen || ctx of    *)
(* pure ML-DSA in a buffer on the stack, with two byte stores and memcpy,    *)
(* returning -9 (MLD_ERR_INVALID_ARG) if ctxlen > 255, gets the 32 bytes of  *)
(* rnd with randombytes, returning -3 if that fails, and signs the message   *)
(* with that prefix with mldsa65_signature_internal, zeroing the signature   *)
(* on any failure and its buffers with stores of zero vectors. It is         *)
(* verified in the whole image (see libmldsa.ml), using the theorems for the *)
(* callees and the contracts memset_full_contract, memcpy_full_contract,     *)
(* randombytes_safety_contract of the C library functions, and shown to be   *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/prepare_domain_separation_prefix_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stubs:

    mldsa65_signature:
       +0x0: stp     x29, x30, [sp, #-64]!
       +0x4: stp     x28, x23, [sp, #16]
       +0x8: stp     x22, x21, [sp, #32]
       +0xc: stp     x20, x19, [sp, #48]
      +0x10: mov     x29, sp
      +0x14: sub     x9, sp, #0x180
      +0x18: and     sp, x9, #0xffffffffffffffe0
      +0x1c: adrp    x8, <page>
      +0x20: mov     x19, x0
      +0x24: cmp     x4, #0xff
      +0x28: ldr     x8, [x8, #4088]
      +0x2c: ldr     x8, [x8]
      +0x30: str     x8, [sp, #376]
      +0x34: b.ls    <mldsa65_signature+0x40>
      +0x38: mov     w20, #0xfffffff7
      +0x3c: b       <mldsa65_signature+0xb4>
      +0x40: mov     x20, x4
      +0x44: mov     x23, x1
      +0x48: mov     x22, x2
      +0x4c: mov     x21, x5
      +0x50: strb    wzr, [sp, #32]
      +0x54: strb    w20, [sp, #33]
      +0x58: cbz     x4, <mldsa65_signature+0x70>
      +0x5c: add     x8, sp, #0x20
      +0x60: mov     x1, x3
      +0x64: mov     x2, x20
      +0x68: orr     x0, x8, #0x2
      +0x6c: bl      <memcpy>
      +0x70: mov     x0, sp
      +0x74: mov     w1, #0x20
      +0x78: bl      <randombytes>
      +0x7c: cbz     w0, <mldsa65_signature+0x88>
      +0x80: mov     w20, #0xfffffffd
      +0x84: b       <mldsa65_signature+0xb4>
      +0x88: add     x3, sp, #0x20
      +0x8c: add     x4, x20, #0x2
      +0x90: mov     x5, sp
      +0x94: mov     x0, x19
      +0x98: mov     x1, x23
      +0x9c: mov     x2, x22
      +0xa0: mov     x6, x21
      +0xa4: mov     w7, wzr
      +0xa8: bl      <mldsa65_signature_internal>
      +0xac: mov     w20, w0
      +0xb0: cbz     w0, <mldsa65_signature+0xc4>
      +0xb4: mov     x0, x19
      +0xb8: mov     w1, wzr
      +0xbc: mov     w2, #0xced
      +0xc0: bl      <memset>
      +0xc4: movi    v0.2d, #0x0
      +0xc8: add     x8, sp, #0x20
      +0xcc: mov     x9, sp
      +0xd0: add     x10, x8, #0x13c
      +0xd4: stp     q0, q0, [sp]
      +0xd8: str     q0, [x10]
      +0xdc: stp     q0, q0, [sp, #32]
      +0xe0: stp     q0, q0, [sp, #64]
      +0xe4: stp     q0, q0, [sp, #96]
      +0xe8: stp     q0, q0, [sp, #128]
      +0xec: stp     q0, q0, [sp, #160]
      +0xf0: stp     q0, q0, [sp, #192]
      +0xf4: stp     q0, q0, [sp, #224]
      +0xf8: stp     q0, q0, [sp, #256]
      +0xfc: stp     q0, q0, [sp, #288]
     +0x100: stp     q0, q0, [sp, #320]
     +0x104: adrp    x8, <page>
     +0x108: ldr     x8, [x8, #4088]
     +0x10c: ldr     x9, [sp, #376]
     +0x110: ldr     x8, [x8]
     +0x114: cmp     x8, x9
     +0x118: b.ne    <mldsa65_signature+0x160>
     +0x11c: mov     w0, w20
     +0x120: mov     sp, x29
     +0x124: ldp     x20, x19, [sp, #48]
     +0x128: ldp     x22, x21, [sp, #32]
     +0x12c: ldp     x28, x23, [sp, #16]
     +0x130: ldp     x29, x30, [sp], #64
     +0x134: mov     x1, #0x0
     +0x138: mov     x2, #0x0
     +0x13c: mov     x3, #0x0
     +0x140: mov     x4, #0x0
     +0x144: mov     x5, #0x0
     +0x148: mov     x6, #0x0
     +0x14c: mov     x7, #0x0
     +0x150: mov     x8, #0x0
     +0x154: mov     x9, #0x0
     +0x158: mov     x10, #0x0
     +0x15c: ret     
     +0x160: bl      <__stack_chk_fail>

    memcpy@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4048]
       +0x8: add     x16, x16, #0xfd0
       +0xc: br      x17

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17

    randombytes@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4056]
       +0x8: add     x16, x16, #0xfd8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIGNATURE_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_signature";
    layout_range "plt_memcpy";
    layout_range "plt_memset";
    layout_range "plt_randombytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (4032 bytes), the message M of mlen bytes at m and   *)
(* the context C of ctxlen bytes at ctx, with MU the mu of signing (H(tr ||  *)
(* prefix || M, 64)). The result is -9 if ctxlen > 255, and otherwise, for   *)
(* some RND (the random bytes), either -3 or the result of signing with RND; *)
(* the signature is mld_sign_sig_65 skb MU RND if the result is 0, and zero  *)
(* otherwise. The theorem assumes that the samplings terminate for every     *)
(* RND. The stack is the 15104 bytes below the stack pointer: the frame of   *)
(* the function, of up to 464 bytes, and the stacks of its callees.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig m mlen ctx ctxlen sk skb M C MU guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          MU = mld_sign_mu (\j. skb(64 + j)) (2 + ctxlen)
                (num_of_bytelist
                  (mld_domain_separation_prefix 0
                    (bytelist_of_num ctxlen C) []))
                mlen M /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
               !RND. RND < 2 EXP 256
                     ==> mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 15104),15104)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 15104),15104)]
           [(m,mlen); (ctx,ctxlen); (sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_signature) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (255 < ctxlen ==> C_RETURN s = word 4294967287) /\
                      (ctxlen <= 255
                       ==> C_RETURN s = word 4294967293 \/
                           C_RETURN s =
                            (if mld_sign_ok_65 skb MU RND then word 0
                             else word 4294967292)) /\
                      (!t. t < 3309
                           ==> read(memory :> bytes8(word_add sig (word t))) s =
                               if C_RETURN s = word 0
                               then mld_sign_sig_65 skb MU RND t
                               else word 0))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 15104),15104)])`;;

let MLDSA_NATIVE_SIGNATURE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, rho, the result and, *)
(* for the RND of the signature, what the C code declassifies in signing     *)
(* (mld_sign_declass_65), with all accesses within the arguments, the stack, *)
(* the GOT entries and the stack guard, the region (ea,el) that the C        *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the outputs and the stack.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen sk skb M C MU guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          MU = mld_sign_mu (\j. skb(64 + j)) (2 + ctxlen)
                (num_of_bytelist
                  (mld_domain_separation_prefix 0
                    (bytelist_of_num ctxlen C) []))
                mlen M /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
               !RND. RND < 2 EXP 256
                     ==> mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 15104),15104)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 15104),15104)]
           [(m,mlen); (ctx,ctxlen); (sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_signature) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (255 < ctxlen ==> C_RETURN s = word 4294967287) /\
                      (ctxlen <= 255
                       ==> C_RETURN s = word 4294967293 \/
                           C_RETURN s =
                            (if mld_sign_ok_65 skb MU RND then word 0
                             else word 4294967292)) /\
                      (!t. t < 3309
                           ==> read(memory :> bytes8(word_add sig (word t))) s =
                               if C_RETURN s = word 0
                               then mld_sign_sig_65 skb MU RND t
                               else word 0) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events sig m mlen ctx ctxlen sk
                             (mld_sk_rho skb) (C_RETURN s)
                             (mld_sign_declass_65 skb MU RND) guard mf mc mr
                             pc (word_sub stackpointer (word 15104))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,3309; m,mlen; ctx,ctxlen; sk,4032;
                          word_sub stackpointer (word 15104),15104;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa65_signature_internal_consts),336]
                         [sig,3309; word_sub stackpointer (word 15104),15104]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 15104),15104)])`;;

let MLDSA_NATIVE_SIGNATURE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone. The events are given for an RND of *)
(* the signature: they depend on what signing declassifies, which only RND   *)
(* determines.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen sk skb M C MU guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          MU = mld_sign_mu (\j. skb(64 + j)) (2 + ctxlen)
                (num_of_bytelist
                  (mld_domain_separation_prefix 0
                    (bytelist_of_num ctxlen C) []))
                mlen M /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
               !RND. RND < 2 EXP 256
                     ==> mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 15104),15104)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 15104),15104)]
           [(m,mlen); (ctx,ctxlen); (sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_signature) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (!t. t < 3309
                           ==> read(memory :> bytes8(word_add sig (word t))) s =
                               if C_RETURN s = word 0
                               then mld_sign_sig_65 skb MU RND t
                               else word 0) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events sig m mlen ctx ctxlen sk
                             (mld_sk_rho skb) (C_RETURN s)
                             (mld_sign_declass_65 skb MU RND) guard mf mc mr
                             pc (word_sub stackpointer (word 15104))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,3309; m,mlen; ctx,ctxlen; sk,4032;
                          word_sub stackpointer (word 15104),15104;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa65_signature_internal_consts),336]
                         [sig,3309; word_sub stackpointer (word 15104),15104]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 15104),15104)])`;;

let MLDSA_NATIVE_SIGNATURE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
