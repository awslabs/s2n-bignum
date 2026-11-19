(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message (pure ML-DSA, randomized): the statement. This is the   *)
(* code for mldsa44_signature (mld_sign_signature in sign.c, an external API *)
(* function) from mldsa-native's portable C implementation compiled by gcc   *)
(* 12 with -Os (see mldsa_native/README.md), which builds the prefix 0 ||    *)
(* ctxlen || ctx of pure ML-DSA with                                         *)
(* mldsa44_prepare_domain_separation_prefix, returning -9                    *)
(* (MLD_ERR_INVALID_ARG) if ctxlen > 255, gets the 32 bytes of rnd with      *)
(* randombytes, returning -3 if that fails, and signs the message with that  *)
(* prefix with mldsa44_signature_internal, zeroing the signature on any      *)
(* failure and its buffers with mld_zeroize (a call of memset). It is        *)
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
needs "arm/proofs/mldsa_native/gcc12_Os/prepare_domain_separation_prefix_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/signature_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stubs:

    mldsa44_signature:
       +0x0: stp     x19, x20, [sp, #-480]!
       +0x4: stp     x21, x22, [sp, #16]
       +0x8: mov     x21, x0
       +0xc: add     x20, sp, #0x5f
      +0x10: adrp    x0, <page>
      +0x14: ldr     x0, [x0, #4088]
      +0x18: stp     x23, x24, [sp, #32]
      +0x1c: and     x20, x20, #0xffffffffffffffe0
      +0x20: stp     x25, x30, [sp, #48]
      +0x24: mov     x23, x1
      +0x28: mov     x24, x2
      +0x2c: ldr     x1, [x0]
      +0x30: str     x1, [sp, #472]
      +0x34: mov     x1, #0x0
      +0x38: mov     x25, x5
      +0x3c: mov     x0, x20
      +0x40: mov     w5, #0x0
      +0x44: mov     x2, #0x0
      +0x48: add     x22, x20, #0x160
      +0x4c: bl      <mldsa44_prepare_domain_separation_prefix>
      +0x50: cbz     x0, <mldsa44_signature+0xd8>
      +0x54: mov     x19, x0
      +0x58: mov     x1, #0x20
      +0x5c: mov     x0, x22
      +0x60: bl      <randombytes>
      +0x64: cbnz    w0, <mldsa44_signature+0xe0>
      +0x68: mov     x4, x19
      +0x6c: mov     x6, x25
      +0x70: mov     x5, x22
      +0x74: mov     x3, x20
      +0x78: mov     x2, x24
      +0x7c: mov     x1, x23
      +0x80: mov     x0, x21
      +0x84: mov     w7, #0x0
      +0x88: bl      <mldsa44_signature_internal>
      +0x8c: mov     w19, w0
      +0x90: cbz     w0, <mldsa44_signature+0xa0>
      +0x94: mov     x0, x21
      +0x98: mov     x1, #0x974
      +0x9c: bl      <mld_zeroize_2>
      +0xa0: mov     x0, x22
      +0xa4: mov     x1, #0x20
      +0xa8: bl      <mld_zeroize_2>
      +0xac: mov     x0, x20
      +0xb0: mov     x1, #0x14c
      +0xb4: bl      <mld_zeroize_2>
      +0xb8: adrp    x0, <page>
      +0xbc: ldr     x0, [x0, #4088]
      +0xc0: ldr     x2, [sp, #472]
      +0xc4: ldr     x1, [x0]
      +0xc8: subs    x2, x2, x1
      +0xcc: mov     x1, #0x0
      +0xd0: b.eq    <mldsa44_signature+0xe8>
      +0xd4: bl      <stack_chk_fail>
      +0xd8: mov     w19, #0xfffffff7
      +0xdc: b       <mldsa44_signature+0x94>
      +0xe0: mov     w19, #0xfffffffd
      +0xe4: b       <mldsa44_signature+0x94>
      +0xe8: ldp     x21, x22, [sp, #16]
      +0xec: mov     w0, w19
      +0xf0: ldp     x23, x24, [sp, #32]
      +0xf4: ldp     x25, x30, [sp, #48]
      +0xf8: ldp     x19, x20, [sp], #480
      +0xfc: ret
    plt_randombytes:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4056]
       +0x8: add     x16, x16, #0xfd8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIGNATURE_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_signature"; layout_range "plt_randombytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (2560 bytes), the message M of mlen bytes at m and   *)
(* the context C of ctxlen bytes at ctx, with MU the mu of signing (H(tr ||  *)
(* prefix || M, 64)). The result is -9 if ctxlen > 255, and otherwise, for   *)
(* some RND (the random bytes), either -3 or the result of signing with RND; *)
(* the signature is mld_sign_sig_44 skb MU RND if the result is 0, and zero  *)
(* otherwise. The theorem assumes that the samplings terminate for every     *)
(* RND. The stack is the 480 bytes of the function and those of the callees  *)
(* below them.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig m mlen ctx ctxlen sk skb M C MU guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          MU = mld_sign_mu (\j. skb(64 + j)) (2 + ctxlen)
                (num_of_bytelist
                  (mld_domain_separation_prefix 0
                    (bytelist_of_num ctxlen C) []))
                mlen M /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
               !RND. RND < 2 EXP 256
                     ==> mld_sign_terminates_44 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49840),49840)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49840),49840)]
           [(m,mlen); (ctx,ctxlen); (sk,2560); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_signature) /\
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
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (255 < ctxlen ==> C_RETURN s = word 4294967287) /\
                      (ctxlen <= 255
                       ==> C_RETURN s = word 4294967293 \/
                           C_RETURN s =
                            (if mld_sign_ok_44 skb MU RND then word 0
                             else word 4294967292)) /\
                      (!t. t < 2420
                           ==> read(memory :> bytes8(word_add sig (word t))) s =
                               if C_RETURN s = word 0
                               then mld_sign_sig_44 skb MU RND t
                               else word 0))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49840),49840)])`;;

let MLDSA_NATIVE_SIGNATURE_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, rho, the result and, *)
(* for the RND of the signature, what the C code declassifies in signing     *)
(* (mld_sign_declass_44), with all accesses within the arguments, the        *)
(* stack, the GOT entries and the stack guard, the region (ea,el) that the C *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the outputs and the stack.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen sk skb M C MU guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          MU = mld_sign_mu (\j. skb(64 + j)) (2 + ctxlen)
                (num_of_bytelist
                  (mld_domain_separation_prefix 0
                    (bytelist_of_num ctxlen C) []))
                mlen M /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
               !RND. RND < 2 EXP 256
                     ==> mld_sign_terminates_44 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49840),49840)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49840),49840)]
           [(m,mlen); (ctx,ctxlen); (sk,2560); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_signature) /\
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
                    (!j. j < 2560
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
                            (if mld_sign_ok_44 skb MU RND then word 0
                             else word 4294967292)) /\
                      (!t. t < 2420
                           ==> read(memory :> bytes8(word_add sig (word t))) s =
                               if C_RETURN s = word 0
                               then mld_sign_sig_44 skb MU RND t
                               else word 0) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events sig m mlen ctx ctxlen sk
                             (mld_sk_rho skb) (C_RETURN s)
                             (mld_sign_declass_44 skb MU RND) guard mf mc mr
                             pc (word_sub stackpointer (word 49840))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,2420; m,mlen; ctx,ctxlen; sk,2560;
                          word_sub stackpointer (word 49840),49840;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el; word 0,0;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_invntt_tomont_consts),48;
                          word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                          word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const2),16;
                          word(pc +
                           mldsa44_prepare_domain_separation_prefix_jump_table),
                          12;
                          word(pc +
                           mldsa44_prepare_domain_separation_prefix_oid_map),
                          192]
                         [sig,2420; word_sub stackpointer (word 49840),49840]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49840),49840)])`;;

let MLDSA_NATIVE_SIGNATURE_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone. The events are given for an RND of *)
(* the signature: they depend on what signing declassifies, which only RND   *)
(* determines.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen sk skb M C MU guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          MU = mld_sign_mu (\j. skb(64 + j)) (2 + ctxlen)
                (num_of_bytelist
                  (mld_domain_separation_prefix 0
                    (bytelist_of_num ctxlen C) []))
                mlen M /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
               !RND. RND < 2 EXP 256
                     ==> mld_sign_terminates_44 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49840),49840)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49840),49840)]
           [(m,mlen); (ctx,ctxlen); (sk,2560); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_signature) /\
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
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (!t. t < 2420
                           ==> read(memory :> bytes8(word_add sig (word t))) s =
                               if C_RETURN s = word 0
                               then mld_sign_sig_44 skb MU RND t
                               else word 0) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events sig m mlen ctx ctxlen sk
                             (mld_sk_rho skb) (C_RETURN s)
                             (mld_sign_declass_44 skb MU RND) guard mf mc mr
                             pc (word_sub stackpointer (word 49840))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,2420; m,mlen; ctx,ctxlen; sk,2560;
                          word_sub stackpointer (word 49840),49840;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el; word 0,0;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_invntt_tomont_consts),48;
                          word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                          word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const2),16;
                          word(pc +
                           mldsa44_prepare_domain_separation_prefix_jump_table),
                          12;
                          word(pc +
                           mldsa44_prepare_domain_separation_prefix_oid_map),
                          192]
                         [sig,2420; word_sub stackpointer (word 49840),49840]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49840),49840)])`;;

let MLDSA_NATIVE_SIGNATURE_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
