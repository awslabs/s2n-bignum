(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with external mu (randomized): the statement. This is the code    *)
(* for mldsa65_signature_extmu (mld_sign_signature_extmu in sign.c, an       *)
(* external API function) from mldsa-native's portable C implementation      *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which gets the  *)
(* 32 bytes of rnd with randombytes, returning -3 if that fails, and         *)
(* otherwise signs with the given mu with mldsa65_signature_internal, and    *)
(* then zeroes rnd. It is verified in the whole image (see libmldsa.ml),     *)
(* using the theorems for the callees and the contracts                      *)
(* memset_full_contract, memcpy_full_contract, randombytes_safety_contract   *)
(* of the C library functions, and shown to be constant time and memory      *)
(* safe.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stubs:

    mldsa65_signature_extmu:
       +0x0: stp     x19, x20, [sp, #-112]!
       +0x4: mov     x20, x0
       +0x8: adrp    x3, <page>
       +0xc: ldr     x3, [x3, #4088]
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: add     x19, sp, #0x4f
      +0x18: str     x30, [sp, #32]
      +0x1c: and     x19, x19, #0xffffffffffffffe0
      +0x20: mov     x21, x1
      +0x24: mov     x22, x2
      +0x28: ldr     x1, [x3]
      +0x2c: str     x1, [sp, #104]
      +0x30: mov     x1, #0x0
      +0x34: mov     x0, x19
      +0x38: mov     x1, #0x20
      +0x3c: bl      <randombytes@plt>
      +0x40: cbnz    w0, <+0x9c>
      +0x44: mov     x6, x22
      +0x48: mov     x1, x21
      +0x4c: mov     x0, x20
      +0x50: mov     x5, x19
      +0x54: mov     w7, #0x1
      +0x58: mov     x4, #0x0
      +0x5c: mov     x3, #0x0
      +0x60: mov     x2, #0x40
      +0x64: bl      <mldsa65_signature_internal>
      +0x68: stp     xzr, xzr, [x19]
      +0x6c: stp     xzr, xzr, [x19, #16]
      +0x70: adrp    x1, <page>
      +0x74: ldr     x1, [x1, #4088]
      +0x78: ldr     x3, [sp, #104]
      +0x7c: ldr     x2, [x1]
      +0x80: subs    x3, x3, x2
      +0x84: mov     x2, #0x0
      +0x88: b.ne    <+0xa4>
      +0x8c: ldp     x21, x22, [sp, #16]
      +0x90: ldr     x30, [sp, #32]
      +0x94: ldp     x19, x20, [sp], #112
      +0x98: ret
      +0x9c: mov     w0, #0xfffffffd
      +0xa0: b       <+0x68>
      +0xa4: bl      <__stack_chk_fail@plt>

    randombytes@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4056]
       +0x8: add     x16, x16, #0xfd8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_signature_extmu"; layout_range "plt_randombytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (4032 bytes) and mu, MU, the 64 bytes at mu: for     *)
(* some RND (the random bytes), the result is -3, or that of signing with    *)
(* RND with the signature mld_sign_sig_65 skb MU RND. The theorem assumes    *)
(* that the samplings terminate for every RND. The stack is the 112 bytes of *)
(* the function and those of the callees below them.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig mu sk skb MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          (!RND. RND < 2 EXP 256
                 ==> mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73200),73200)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73200),73200)]
           [(mu,64); (sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_signature_extmu) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; mu; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(mu,64)) s = MU /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (C_RETURN s = word 4294967293 \/
                       C_RETURN s =
                       (if mld_sign_ok_65 skb MU RND then word 0
                        else word 4294967292) /\
                       (!t. t < 3309
                            ==> read(memory :> bytes8
                                      (word_add sig (word t))) s =
                                mld_sign_sig_65 skb MU RND t)))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73200),73200)])`;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result and, for the RND  *)
(* of the signature, what the C code declassifies in signing                 *)
(* (mld_sign_declass_65), with all accesses within the arguments, the stack, *)
(* the GOT entries and the stack guard, the region (ea,el) that the C        *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the outputs and the stack.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig mu sk skb MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          (!RND. RND < 2 EXP 256
                 ==> mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73200),73200)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73200),73200)]
           [(mu,64); (sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_signature_extmu) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; mu; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(mu,64)) s = MU /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (C_RETURN s = word 4294967293 \/
                       C_RETURN s =
                       (if mld_sign_ok_65 skb MU RND then word 0
                        else word 4294967292) /\
                       (!t. t < 3309
                            ==> read(memory :> bytes8
                                      (word_add sig (word t))) s =
                                mld_sign_sig_65 skb MU RND t)) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events sig mu sk (mld_sk_rho skb) (C_RETURN s)
                             (mld_sign_declass_65 skb MU RND) guard mf mc mr
                             pc (word_sub stackpointer (word 73200))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,3309; mu,64; sk,4032;
                          word_sub stackpointer (word 73200),73200;
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
                           mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                          word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                         [sig,3309; word_sub stackpointer (word 73200),73200]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73200),73200)])`;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone. The events are given for an RND of *)
(* the signature if the result is 0: they depend on what signing             *)
(* declassifies, which only RND determines.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig mu sk skb MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          (!RND. RND < 2 EXP 256
                 ==> mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73200),73200)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73200),73200)]
           [(mu,64); (sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_signature_extmu) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; mu; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(mu,64)) s = MU /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    ?RND.
                      RND < 2 EXP 256 /\
                      (C_RETURN s = word 0
                       ==> !t. t < 3309
                               ==> read(memory :> bytes8
                                         (word_add sig (word t))) s =
                                   mld_sign_sig_65 skb MU RND t) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events sig mu sk (mld_sk_rho skb) (C_RETURN s)
                             (mld_sign_declass_65 skb MU RND) guard mf mc mr
                             pc (word_sub stackpointer (word 73200))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,3309; mu,64; sk,4032;
                          word_sub stackpointer (word 73200),73200;
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
                           mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                          word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                         [sig,3309; word_sub stackpointer (word 73200),73200]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73200),73200)])`;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
