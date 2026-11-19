(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with external mu (randomized): the statement. This is the code    *)
(* for mldsa87_signature_extmu (mld_sign_signature_extmu in sign.c, an       *)
(* external API function) from mldsa-native's portable C implementation      *)
(* compiled by gcc 12 with -Os (see mldsa_native/README.md), which gets the  *)
(* 32 bytes of rnd with randombytes, returning -3 if that fails, and         *)
(* otherwise signs with the given mu with mldsa87_signature_internal, and    *)
(* then zeroes rnd with mld_zeroize (a call of memset), also if randombytes  *)
(* fails. It is verified in the whole image (see libmldsa.ml), using the     *)
(* theorems for the callees and the contracts memset_full_contract,          *)
(* memcpy_full_contract, randombytes_safety_contract of the C library        *)
(* functions, and shown to be constant time and memory safe.                 *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/signature_internal_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stubs:

    mldsa87_signature_extmu:
       +0x0: stp     x19, x20, [sp, #-112]!
       +0x4: mov     x20, x0
       +0x8: adrp    x0, <page>
       +0xc: ldr     x0, [x0, #4088]
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: add     x19, sp, #0x4f
      +0x18: str     x30, [sp, #32]
      +0x1c: mov     x21, x1
      +0x20: and     x19, x19, #0xffffffffffffffe0
      +0x24: mov     x22, x2
      +0x28: ldr     x1, [x0]
      +0x2c: str     x1, [sp, #104]
      +0x30: mov     x1, #0x0
      +0x34: mov     x0, x19
      +0x38: mov     x1, #0x20
      +0x3c: bl      <randombytes>
      +0x40: cbnz    w0, <mldsa87_signature_extmu+0x98>
      +0x44: mov     x0, x20
      +0x48: mov     x6, x22
      +0x4c: mov     x5, x19
      +0x50: mov     x1, x21
      +0x54: mov     w7, #0x1
      +0x58: mov     x4, #0x0
      +0x5c: mov     x3, #0x0
      +0x60: mov     x2, #0x40
      +0x64: bl      <mldsa87_signature_internal>
      +0x68: mov     w20, w0
      +0x6c: mov     x0, x19
      +0x70: mov     x1, #0x20
      +0x74: bl      <mld_zeroize_6>
      +0x78: adrp    x0, <page>
      +0x7c: ldr     x0, [x0, #4088]
      +0x80: ldr     x2, [sp, #104]
      +0x84: ldr     x1, [x0]
      +0x88: subs    x2, x2, x1
      +0x8c: mov     x1, #0x0
      +0x90: b.eq    <mldsa87_signature_extmu+0xa0>
      +0x94: bl      <stack_chk_fail>
      +0x98: mov     w20, #0xfffffffd
      +0x9c: b       <mldsa87_signature_extmu+0x6c>
      +0xa0: ldp     x21, x22, [sp, #16]
      +0xa4: mov     w0, w20
      +0xa8: ldr     x30, [sp, #32]
      +0xac: ldp     x19, x20, [sp], #112
      +0xb0: ret
    plt_randombytes:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4056]
       +0x8: add     x16, x16, #0xfd8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa87_signature_extmu"; layout_range "plt_randombytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (4896 bytes) and mu, MU, the 64 bytes at mu: for     *)
(* some RND (the random bytes), the result is -3, or that of signing with    *)
(* RND with the signature mld_sign_sig_87 skb MU RND. The theorem assumes    *)
(* that the samplings terminate for every RND. The stack is the 112 bytes of *)
(* the function and those of the callees below them.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig mu sk skb MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          (!RND. RND < 2 EXP 256
                 ==> mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112208),112208)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112208),112208)]
           [(mu,64); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_signature_extmu) /\
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
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
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
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112208),
                                  112208)])`;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result and, for the RND  *)
(* of the signature, what the C code declassifies in signing                 *)
(* (mld_sign_declass_87), with all accesses within the arguments, the        *)
(* stack, the GOT entries and the stack guard, the region (ea,el) that the C *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the outputs and the stack.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig mu sk skb MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          (!RND. RND < 2 EXP 256
                 ==> mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112208),112208)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112208),112208)]
           [(mu,64); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_signature_extmu) /\
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
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
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
                             (mld_sign_declass_87 skb MU RND) guard mf mc mr
                             pc (word_sub stackpointer (word 112208))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,4627; mu,64; sk,4896;
                          word_sub stackpointer (word 112208),112208;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el; word 0,0;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_invntt_tomont_consts),48;
                          word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                          word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                         [sig,4627;
                          word_sub stackpointer (word 112208),112208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112208),
                                  112208)])`;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone. The events are given for an RND of *)
(* the signature if the result is 0: they depend on what signing             *)
(* declassifies, which only RND determines.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig mu sk skb MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          (!RND. RND < 2 EXP 256
                 ==> mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112208),112208)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112208),112208)]
           [(mu,64); (sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_signature_extmu) /\
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
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
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
                             (mld_sign_declass_87 skb MU RND) guard mf mc mr
                             pc (word_sub stackpointer (word 112208))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,4627; mu,64; sk,4896;
                          word_sub stackpointer (word 112208),112208;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el; word 0,0;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_invntt_tomont_consts),48;
                          word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                          word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                         [sig,4627;
                          word_sub stackpointer (word 112208),112208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112208),
                                  112208)])`;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
