(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation with random bytes: the statement. This is the code for     *)
(* mldsa87_keypair (mld_sign_keypair in sign.c, an external API function)    *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which gets 32 random bytes with randombytes *)
(* into a buffer on the stack, returns -3 (MLD_ERR_RNG_FAIL) if that fails,  *)
(* and otherwise generates the keys from them with mldsa87_keypair_internal, *)
(* and then zeroes the buffer. It is verified in the whole image (see        *)
(* libmldsa.ml), using the theorems for the callees and the contracts        *)
(* memset_full_contract, randombytes_safety_contract of the C library        *)
(* functions, and shown to be constant time and memory safe.                 *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keypair_internal_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stubs:

    mldsa87_keypair:
       +0x0: stp     x19, x20, [sp, #-96]!
       +0x4: mov     x20, x0
       +0x8: adrp    x2, <page>
       +0xc: ldr     x2, [x2, #4088]
      +0x10: stp     x21, x30, [sp, #16]
      +0x14: add     x19, sp, #0x3f
      +0x18: and     x19, x19, #0xffffffffffffffe0
      +0x1c: mov     x21, x1
      +0x20: ldr     x1, [x2]
      +0x24: str     x1, [sp, #88]
      +0x28: mov     x1, #0x0
      +0x2c: mov     x0, x19
      +0x30: mov     x1, #0x20
      +0x34: bl      <randombytes@plt>
      +0x38: cbnz    w0, <+0x7c>
      +0x3c: mov     x1, x21
      +0x40: mov     x0, x20
      +0x44: mov     x2, x19
      +0x48: bl      <mldsa87_keypair_internal>
      +0x4c: stp     xzr, xzr, [x19]
      +0x50: stp     xzr, xzr, [x19, #16]
      +0x54: adrp    x1, <page>
      +0x58: ldr     x1, [x1, #4088]
      +0x5c: ldr     x3, [sp, #88]
      +0x60: ldr     x2, [x1]
      +0x64: subs    x3, x3, x2
      +0x68: mov     x2, #0x0
      +0x6c: b.ne    <+0x84>
      +0x70: ldp     x21, x30, [sp, #16]
      +0x74: ldp     x19, x20, [sp], #96
      +0x78: ret
      +0x7c: mov     w0, #0xfffffffd
      +0x80: b       <+0x4c>
      +0x84: bl      <__stack_chk_fail@plt>

    randombytes@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4056]
       +0x8: add     x16, x16, #0xfd8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_keypair"; layout_range "plt_randombytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. Either   *)
(* randombytes succeeds and the function returns 0 with the keys             *)
(* mld_keypair_pk_87 SEED and mld_keypair_sk_87 SEED for some seed SEED (the *)
(* random bytes), or it fails and the function returns -3. The theorem       *)
(* assumes that the samplings terminate for every seed. The stack is the 96  *)
(* bytes of the function and those of the callees below them.                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mr ea el ev.
     memset_full_contract mf ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !pk sk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          (!SEED. SEED < 2 EXP 256
                  ==> mld_matrix_terminates 8 7
                       (mld_keypair_rho 8 7 SEED) /\
                      mld_keypair_terminates_87 SEED) /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896); (word_sub stackpointer (word 72240),72240)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896); (word_sub stackpointer (word 72240),72240)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_keypair) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev)
               (\s. read PC s = returnaddress /\
                    ?SEED.
                      SEED < 2 EXP 256 /\
                      (C_RETURN s = word 0 \/
                       C_RETURN s = word 4294967293) /\
                      (C_RETURN s = word 0
                       ==> (!j. j < 2592
                                ==> read(memory :> bytes8
                                          (word_add pk (word j))) s =
                                    mld_keypair_pk_87 SEED j) /\
                           (!j. j < 4896
                                ==> read(memory :> bytes8
                                          (word_add sk (word j))) s =
                                    mld_keypair_sk_87 SEED j)))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72240),72240)])`;;

let MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the result and, for a seed SEED   *)
(* of the keys, rho and what the C code declassifies in the sampling         *)
(* (mld_keypair_declass_87), with all accesses within the arguments, the     *)
(* stack, the GOT entries and the stack guard, the region (ea,el) that the C *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the outputs and the stack.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mr ea el ev.
     memset_full_contract mf ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e pk sk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          (!SEED. SEED < 2 EXP 256
                  ==> mld_matrix_terminates 8 7
                       (mld_keypair_rho 8 7 SEED) /\
                      mld_keypair_terminates_87 SEED) /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896); (word_sub stackpointer (word 72240),72240)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896); (word_sub stackpointer (word 72240),72240)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_keypair) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    ?SEED.
                      SEED < 2 EXP 256 /\
                      (C_RETURN s = word 0 \/
                       C_RETURN s = word 4294967293) /\
                      (C_RETURN s = word 0
                       ==> (!j. j < 2592
                                ==> read(memory :> bytes8
                                          (word_add pk (word j))) s =
                                    mld_keypair_pk_87 SEED j) /\
                           (!j. j < 4896
                                ==> read(memory :> bytes8
                                          (word_add sk (word j))) s =
                                    mld_keypair_sk_87 SEED j)) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events pk sk (C_RETURN s)
                             (mld_keypair_rho 8 7 SEED)
                             (mld_keypair_declass_87 SEED) guard mf mr pc
                             (word_sub stackpointer (word 72240))
                             returnaddress /\
                        memaccess_inbounds e2
                         [pk,2592; sk,4896;
                          word_sub stackpointer (word 72240),72240;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_invntt_tomont_consts),48;
                          word(pc + mldsa_poly_reduce_consts),16;
                          word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                          word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                         [pk,2592; sk,4896;
                          word_sub stackpointer (word 72240),72240]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72240),72240)])`;;

let MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone. The events are given for a seed    *)
(* SEED of the secret key if the result is 0: they depend on the values that *)
(* the sampling declassifies, which only the seed determines.                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mr ea el ev.
     memset_full_contract mf ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e pk sk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          (!SEED. SEED < 2 EXP 256
                  ==> mld_matrix_terminates 8 7
                       (mld_keypair_rho 8 7 SEED) /\
                      mld_keypair_terminates_87 SEED) /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896); (word_sub stackpointer (word 72240),72240)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896); (word_sub stackpointer (word 72240),72240)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8);
            (word(pc + got_randombytes),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_keypair) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    ?SEED.
                      SEED < 2 EXP 256 /\
                      (C_RETURN s = word 0
                       ==> !j. j < 4896
                               ==> read(memory :> bytes8
                                         (word_add sk (word j))) s =
                                   mld_keypair_sk_87 SEED j) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events pk sk (C_RETURN s)
                             (mld_keypair_rho 8 7 SEED)
                             (mld_keypair_declass_87 SEED) guard mf mr pc
                             (word_sub stackpointer (word 72240))
                             returnaddress /\
                        memaccess_inbounds e2
                         [pk,2592; sk,4896;
                          word_sub stackpointer (word 72240),72240;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa_poly_invntt_tomont_consts),48;
                          word(pc + mldsa_poly_reduce_consts),16;
                          word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                          word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                         [pk,2592; sk,4896;
                          word_sub stackpointer (word 72240),72240]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72240),72240)])`;;

let MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
