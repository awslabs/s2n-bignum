(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with external mu (randomized): the statement. This is the code    *)
(* for mldsa65_signature_extmu (mld_sign_signature_extmu in sign.c, an       *)
(* external API function) from mldsa-native's portable C implementation      *)
(* compiled by clang 23 with -O3 as one translation unit with                *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which gets the 32     *)
(* bytes of rnd with randombytes, returning -3 if that fails, and otherwise  *)
(* signs with the given mu with mldsa65_signature_internal, and then zeroes  *)
(* rnd. It is verified in the whole image (see libmldsa.ml), using the       *)
(* theorems for the callees and the contracts memset_full_contract,          *)
(* memcpy_full_contract, randombytes_safety_contract of the C library        *)
(* functions, and shown to be constant time and memory safe.                 *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stubs:

    mldsa65_signature_extmu:
       +0x0: stp     x29, x30, [sp, #-48]!
       +0x4: str     x21, [sp, #16]
       +0x8: stp     x20, x19, [sp, #32]
       +0xc: mov     x29, sp
      +0x10: sub     x9, sp, #0x30
      +0x14: and     sp, x9, #0xffffffffffffffe0
      +0x18: adrp    x8, <page>
      +0x1c: mov     x20, x1
      +0x20: mov     x21, x0
      +0x24: ldr     x8, [x8, #4088]
      +0x28: mov     x0, sp
      +0x2c: mov     w1, #0x20
      +0x30: mov     x19, x2
      +0x34: ldr     x8, [x8]
      +0x38: str     x8, [sp, #40]
      +0x3c: bl      <randombytes>
      +0x40: cbz     w0, <mldsa65_signature_extmu+0x4c>
      +0x44: mov     w0, #0xfffffffd
      +0x48: b       <mldsa65_signature_extmu+0x70>
      +0x4c: mov     x5, sp
      +0x50: mov     x0, x21
      +0x54: mov     x1, x20
      +0x58: mov     w2, #0x40
      +0x5c: mov     x3, xzr
      +0x60: mov     x4, xzr
      +0x64: mov     x6, x19
      +0x68: mov     w7, #0x1
      +0x6c: bl      <mldsa65_signature_internal>
      +0x70: movi    v0.2d, #0x0
      +0x74: mov     x8, sp
      +0x78: stp     q0, q0, [sp]
      +0x7c: adrp    x8, <page>
      +0x80: ldr     x8, [x8, #4088]
      +0x84: ldr     x9, [sp, #40]
      +0x88: ldr     x8, [x8]
      +0x8c: cmp     x8, x9
      +0x90: b.ne    <mldsa65_signature_extmu+0xcc>
      +0x94: mov     sp, x29
      +0x98: ldp     x20, x19, [sp, #32]
      +0x9c: ldr     x21, [sp, #16]
      +0xa0: ldp     x29, x30, [sp], #48
      +0xa4: mov     x1, #0x0
      +0xa8: mov     x2, #0x0
      +0xac: mov     x3, #0x0
      +0xb0: mov     x4, #0x0
      +0xb4: mov     x5, #0x0
      +0xb8: mov     x6, #0x0
      +0xbc: mov     x7, #0x0
      +0xc0: mov     x8, #0x0
      +0xc4: mov     x9, #0x0
      +0xc8: ret     
      +0xcc: bl      <__stack_chk_fail>

    randombytes@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4056]
       +0x8: add     x16, x16, #0xfd8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_signature_extmu";
    layout_range "plt_randombytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (4032 bytes) and mu, MU, the 64 bytes at mu: for     *)
(* some RND (the random bytes), the result is -3, or that of signing with    *)
(* RND with the signature mld_sign_sig_65 skb MU RND. The theorem assumes    *)
(* that the samplings terminate for every RND. The stack is the 14752 bytes  *)
(* below the stack pointer: the frame of the function, of up to 112 bytes,   *)
(* and the stacks of its callees.                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !sig mu sk skb MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          (!RND. RND < 2 EXP 256
                 ==> mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 14752),14752)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 14752),14752)]
           [(mu,64); (sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 14752),14752)])`;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_EXTMU_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result and, for the RND  *)
(* of the signature, what the C code declassifies in signing                 *)
(* (mld_sign_declass_65), with all accesses within the arguments, the stack, *)
(* the GOT entries and the stack guard, the region (ea,el) that the C        *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the outputs and the stack.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig mu sk skb MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          (!RND. RND < 2 EXP 256
                 ==> mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 14752),14752)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 14752),14752)]
           [(mu,64); (sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
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
                             pc (word_sub stackpointer (word 14752))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,3309; mu,64; sk,4032;
                          word_sub stackpointer (word 14752),14752;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa65_signature_internal_consts),336]
                         [sig,3309; word_sub stackpointer (word 14752),14752]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 14752),14752)])`;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_EXTMU_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone. The events are given for an RND of *)
(* the signature if the result is 0: they depend on what signing             *)
(* declassifies, which only RND determines.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e sig mu sk skb MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          (!RND. RND < 2 EXP 256
                 ==> mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 14752),14752)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 14752),14752)]
           [(mu,64); (sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
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
                             pc (word_sub stackpointer (word 14752))
                             returnaddress /\
                        memaccess_inbounds e2
                         [sig,3309; mu,64; sk,4032;
                          word_sub stackpointer (word 14752),14752;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8; word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa65_signature_internal_consts),336]
                         [sig,3309; word_sub stackpointer (word 14752),14752]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 14752),14752)])`;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_EXTMU_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
