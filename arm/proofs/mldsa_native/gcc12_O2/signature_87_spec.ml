(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message (pure ML-DSA, randomized): the statement. This is the   *)
(* code for mldsa87_signature (mld_sign_signature in sign.c, an external API *)
(* function) from mldsa-native's portable C implementation compiled by gcc   *)
(* 12 with -O2 (see mldsa_native/README.md), which builds the prefix 0 ||    *)
(* ctxlen || ctx of pure ML-DSA with                                         *)
(* mldsa87_prepare_domain_separation_prefix, returning -9                    *)
(* (MLD_ERR_INVALID_ARG) if ctxlen > 255, gets the 32 bytes of rnd with      *)
(* randombytes, returning -3 if that fails, and signs the message with that  *)
(* prefix with mldsa87_signature_internal, zeroing the signature on any      *)
(* failure and its buffers with memset and stores. It is verified in the     *)
(* whole image (see libmldsa.ml), using the theorems for the callees and the *)
(* contracts memset_full_contract, memcpy_full_contract,                     *)
(* randombytes_safety_contract of the C library functions, and shown to be   *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/prepare_domain_separation_prefix_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_internal_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stubs:

    mldsa87_signature:
       +0x0: stp     x19, x20, [sp, #-496]!
       +0x4: mov     x20, x0
       +0x8: adrp    x7, <page>
       +0xc: ldr     x7, [x7, #4088]
      +0x10: add     x19, sp, #0x6f
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: and     x19, x19, #0xffffffffffffffe0
      +0x1c: mov     x0, x19
      +0x20: stp     x23, x24, [sp, #32]
      +0x24: mov     x23, x1
      +0x28: mov     x24, x2
      +0x2c: stp     x25, x26, [sp, #48]
      +0x30: mov     x2, #0x0
      +0x34: mov     x25, x5
      +0x38: str     x30, [sp, #64]
      +0x3c: mov     w5, #0x0
      +0x40: ldr     x1, [x7]
      +0x44: str     x1, [sp, #488]
      +0x48: mov     x1, #0x0
      +0x4c: bl      <mldsa87_prepare_domain_separation_prefix>
      +0x50: cbnz    x0, <+0xbc>
      +0x54: add     x22, x19, #0x160
      +0x58: mov     w26, #0xfffffff7
      +0x5c: mov     x0, x20
      +0x60: mov     x2, #0x1213
      +0x64: mov     w1, #0x0
      +0x68: bl      <memset@plt>
      +0x6c: stp     xzr, xzr, [x19, #352]
      +0x70: stp     xzr, xzr, [x22, #16]
      +0x74: mov     x2, #0x14c
      +0x78: mov     x0, x19
      +0x7c: mov     w1, #0x0
      +0x80: bl      <memset@plt>
      +0x84: adrp    x0, <page>
      +0x88: ldr     x0, [x0, #4088]
      +0x8c: ldr     x2, [sp, #488]
      +0x90: ldr     x1, [x0]
      +0x94: subs    x2, x2, x1
      +0x98: mov     x1, #0x0
      +0x9c: b.ne    <+0x108>
      +0xa0: ldp     x21, x22, [sp, #16]
      +0xa4: mov     w0, w26
      +0xa8: ldp     x23, x24, [sp, #32]
      +0xac: ldp     x25, x26, [sp, #48]
      +0xb0: ldr     x30, [sp, #64]
      +0xb4: ldp     x19, x20, [sp], #496
      +0xb8: ret
      +0xbc: add     x22, x19, #0x160
      +0xc0: mov     x21, x0
      +0xc4: mov     x1, #0x20
      +0xc8: mov     x0, x22
      +0xcc: mov     w26, #0xfffffffd
      +0xd0: bl      <randombytes@plt>
      +0xd4: cbnz    w0, <+0x5c>
      +0xd8: mov     x6, x25
      +0xdc: mov     x4, x21
      +0xe0: mov     x2, x24
      +0xe4: mov     x1, x23
      +0xe8: mov     x5, x22
      +0xec: mov     x3, x19
      +0xf0: mov     x0, x20
      +0xf4: mov     w7, #0x0
      +0xf8: bl      <mldsa87_signature_internal>
      +0xfc: mov     w26, w0
     +0x100: cbz     w0, <+0x6c>
     +0x104: b       <+0x5c>
     +0x108: bl      <__stack_chk_fail@plt>

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

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_signature";
    layout_range "plt_memset";
    layout_range "plt_randombytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (4896 bytes), the message M of mlen bytes at m and   *)
(* the context C of ctxlen bytes at ctx, with MU the mu of signing (H(tr ||  *)
(* prefix || M, 64)). The result is -9 if ctxlen > 255, and otherwise, for   *)
(* some RND (the random bytes), either -3 or the result of signing with RND; *)
(* the signature is mld_sign_sig_87 skb MU RND if the result is 0, and zero  *)
(* otherwise. The theorem assumes that the samplings terminate for every     *)
(* RND. The stack is the 496 bytes of the function and those of the callees  *)
(* below them.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
           ==> mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
               !RND. RND < 2 EXP 256
                     ==> mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112768),112768)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112768),112768)]
           [(m,mlen); (ctx,ctxlen); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_signature) /\
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
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (255 < ctxlen ==> C_RETURN s = word 4294967287) /\
                      (ctxlen <= 255
                       ==> C_RETURN s = word 4294967293 \/
                           C_RETURN s =
                            (if mld_sign_ok_87 skb MU RND then word 0
                             else word 4294967292)) /\
                      (!t. t < 4627
                           ==> read(memory :> bytes8(word_add sig (word t))) s =
                               if C_RETURN s = word 0
                               then mld_sign_sig_87 skb MU RND t
                               else word 0))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112768),
                                  112768)])`;;

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, rho, the result and, *)
(* for the RND of the signature, what the C code declassifies in signing     *)
(* (mld_sign_declass_87), with all accesses within the arguments, the stack, *)
(* the GOT entries and the stack guard, the region (ea,el) that the C        *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the outputs and the stack.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
           ==> mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
               !RND. RND < 2 EXP 256
                     ==> mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112768),112768)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112768),112768)]
           [(m,mlen); (ctx,ctxlen); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_signature) /\
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
                    (!j. j < 4896
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
                            (if mld_sign_ok_87 skb MU RND then word 0
                             else word 4294967292)) /\
                      (!t. t < 4627
                           ==> read(memory :> bytes8(word_add sig (word t))) s =
                               if C_RETURN s = word 0
                               then mld_sign_sig_87 skb MU RND t
                               else word 0) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events sig m mlen ctx ctxlen sk
                             (mld_sk_rho skb) (C_RETURN s)
                             (mld_sign_declass_87 skb MU RND) guard mf mc mr
                             pc (word_sub stackpointer (word 112768))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,4627; m,mlen; ctx,ctxlen; sk,4896;
                          word_sub stackpointer (word 112768),112768;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_invntt_tomont_consts),48;
                          word(pc + mldsa_poly_reduce_consts),16;
                          word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                          word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                          word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                          word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16;
                          word(pc +
                           mldsa87_prepare_domain_separation_prefix_jump_table),
                          12;
                          word(pc +
                           mldsa87_prepare_domain_separation_prefix_oid_map),
                          192]
                         [sig,4627;
                          word_sub stackpointer (word 112768),112768]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112768),
                                  112768)])`;;

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
           ==> mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
               !RND. RND < 2 EXP 256
                     ==> mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112768),112768)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112768),112768)]
           [(m,mlen); (ctx,ctxlen); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_signature) /\
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
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (!t. t < 4627
                           ==> read(memory :> bytes8(word_add sig (word t))) s =
                               if C_RETURN s = word 0
                               then mld_sign_sig_87 skb MU RND t
                               else word 0) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events sig m mlen ctx ctxlen sk
                             (mld_sk_rho skb) (C_RETURN s)
                             (mld_sign_declass_87 skb MU RND) guard mf mc mr
                             pc (word_sub stackpointer (word 112768))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,4627; m,mlen; ctx,ctxlen; sk,4896;
                          word_sub stackpointer (word 112768),112768;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_invntt_tomont_consts),48;
                          word(pc + mldsa_poly_reduce_consts),16;
                          word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                          word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                          word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                          word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16;
                          word(pc +
                           mldsa87_prepare_domain_separation_prefix_jump_table),
                          12;
                          word(pc +
                           mldsa87_prepare_domain_separation_prefix_oid_map),
                          192]
                         [sig,4627;
                          word_sub stackpointer (word 112768),112768]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112768),
                                  112768)])`;;

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
