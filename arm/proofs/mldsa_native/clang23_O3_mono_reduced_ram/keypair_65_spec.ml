(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation with random bytes: the statement. This is the code for     *)
(* mldsa65_keypair (mld_sign_keypair in sign.c, an external API function)    *)
(* from mldsa-native's portable C implementation compiled by clang 23 with   *)
(* -O3 as one translation unit with MLD_CONFIG_REDUCE_RAM (see               *)
(* mldsa_native/README.md), which gets 32 random bytes with randombytes into *)
(* a buffer on the stack, returns -3 (MLD_ERR_RNG_FAIL) if that fails, and   *)
(* otherwise generates the keys from them with mldsa65_keypair_internal, and *)
(* then zeroes the buffer. It is verified in the whole image (see            *)
(* libmldsa.ml), using the theorems for the callees and the contracts        *)
(* memset_full_contract, memcpy_full_contract (which the callees use) and    *)
(* randombytes_safety_contract of the C library functions, and shown to be   *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keypair_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stubs:

    mldsa65_keypair:
       +0x0: stp     x29, x30, [sp, #-32]!
       +0x4: stp     x20, x19, [sp, #16]
       +0x8: mov     x29, sp
       +0xc: sub     x9, sp, #0x40
      +0x10: and     sp, x9, #0xffffffffffffffe0
      +0x14: adrp    x8, <page>
      +0x18: mov     x19, x1
      +0x1c: mov     x20, x0
      +0x20: ldr     x8, [x8, #4088]
      +0x24: mov     x0, sp
      +0x28: mov     w1, #0x20
      +0x2c: ldr     x8, [x8]
      +0x30: str     x8, [sp, #56]
      +0x34: bl      <randombytes>
      +0x38: cbz     w0, <mldsa65_keypair+0x44>
      +0x3c: mov     w0, #0xfffffffd
      +0x40: b       <mldsa65_keypair+0x58>
      +0x44: mov     x2, sp
      +0x48: mov     x0, x20
      +0x4c: mov     x1, x19
      +0x50: bl      <mldsa65_keypair_internal>
      +0x54: mov     w0, wzr
      +0x58: movi    v0.2d, #0x0
      +0x5c: mov     x8, sp
      +0x60: stp     q0, q0, [sp]
      +0x64: adrp    x8, <page>
      +0x68: ldr     x8, [x8, #4088]
      +0x6c: ldr     x9, [sp, #56]
      +0x70: ldr     x8, [x8]
      +0x74: cmp     x8, x9
      +0x78: b.ne    <mldsa65_keypair+0x9c>
      +0x7c: mov     sp, x29
      +0x80: ldp     x20, x19, [sp, #16]
      +0x84: ldp     x29, x30, [sp], #32
      +0x88: mov     x1, #0x0
      +0x8c: mov     x2, #0x0
      +0x90: mov     x8, #0x0
      +0x94: mov     x9, #0x0
      +0x98: ret     
      +0x9c: bl      <__stack_chk_fail>

    randombytes@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4056]
       +0x8: add     x16, x16, #0xfd8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_KEYPAIR_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_keypair";
    layout_range "plt_randombytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. Either   *)
(* randombytes succeeds and the function returns 0 with the keys             *)
(* mld_keypair_pk_65 SEED and mld_keypair_sk_65 SEED for some seed SEED (the *)
(* random bytes), or it fails and the function returns -3. The theorem       *)
(* assumes that the samplings terminate for every seed. The stack is the     *)
(* 11424 bytes below the stack pointer: the frame of the function, of up to  *)
(* 112 bytes, and the stacks of its callees.                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> !pk sk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          (!SEED. SEED < 2 EXP 256
                  ==> mld_matrix_terminates 6 5
                       (mld_keypair_rho 6 5 SEED) /\
                      mld_keypair_terminates_65 SEED) /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032); (word_sub stackpointer (word 11424),11424)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032); (word_sub stackpointer (word 11424),11424)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (word(pc + got_randombytes),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_keypair) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev)
               (\s. read PC s = returnaddress /\
                    ?SEED.
                      SEED < 2 EXP 256 /\
                      (C_RETURN s = word 0 \/
                       C_RETURN s = word 4294967293) /\
                      (C_RETURN s = word 0
                       ==> (!j. j < 1952
                                ==> read(memory :> bytes8
                                          (word_add pk (word j))) s =
                                    mld_keypair_pk_65 SEED j) /\
                           (!j. j < 4032
                                ==> read(memory :> bytes8
                                          (word_add sk (word j))) s =
                                    mld_keypair_sk_65 SEED j)))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 11424),11424)])`;;

let MLDSA_NATIVE_KEYPAIR_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KEYPAIR_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the result and, for a seed SEED   *)
(* of the keys, rho and what the C code declassifies in the sampling         *)
(* (mld_keypair_declass_65), with all accesses within the arguments, the     *)
(* stack, the GOT entries and the stack guard, the region (ea,el) that the C *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the outputs and the stack.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e pk sk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          (!SEED. SEED < 2 EXP 256
                  ==> mld_matrix_terminates 6 5
                       (mld_keypair_rho 6 5 SEED) /\
                      mld_keypair_terminates_65 SEED) /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032); (word_sub stackpointer (word 11424),11424)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032); (word_sub stackpointer (word 11424),11424)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (word(pc + got_randombytes),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_keypair) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
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
                       ==> (!j. j < 1952
                                ==> read(memory :> bytes8
                                          (word_add pk (word j))) s =
                                    mld_keypair_pk_65 SEED j) /\
                           (!j. j < 4032
                                ==> read(memory :> bytes8
                                          (word_add sk (word j))) s =
                                    mld_keypair_sk_65 SEED j)) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events pk sk (C_RETURN s)
                             (mld_keypair_rho 6 5 SEED)
                             (mld_keypair_declass_65 SEED) guard mf mc mr pc
                             (word_sub stackpointer (word 11424))
                             returnaddress /\
                        memaccess_inbounds e2
                         [pk,1952; sk,4032;
                          word_sub stackpointer (word 11424),11424;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8;
                          word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mld_compute_pack_t0_t165_consts),272]
                         [pk,1952; sk,4032;
                          word_sub stackpointer (word 11424),11424]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 11424),11424)])`;;

let MLDSA_NATIVE_KEYPAIR_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KEYPAIR_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone. The events are given for a seed    *)
(* SEED of the secret key if the result is 0: they depend on the values that *)
(* the sampling declassifies, which only the seed determines.                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc mr ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev /\
     randombytes_safety_contract mr ea el ev
     ==> exists f_events.
          forall e pk sk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          (!SEED. SEED < 2 EXP 256
                  ==> mld_matrix_terminates 6 5
                       (mld_keypair_rho 6 5 SEED) /\
                      mld_keypair_terminates_65 SEED) /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032); (word_sub stackpointer (word 11424),11424)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032); (word_sub stackpointer (word 11424),11424)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (word(pc + got_randombytes),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_keypair) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes64(word(pc + got_randombytes))) s =
                      mr /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    ?SEED.
                      SEED < 2 EXP 256 /\
                      (C_RETURN s = word 0
                       ==> !j. j < 4032
                               ==> read(memory :> bytes8
                                         (word_add sk (word j))) s =
                                   mld_keypair_sk_65 SEED j) /\
                      (exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events pk sk (C_RETURN s)
                             (mld_keypair_rho 6 5 SEED)
                             (mld_keypair_declass_65 SEED) guard mf mc mr pc
                             (word_sub stackpointer (word 11424))
                             returnaddress /\
                        memaccess_inbounds e2
                         [pk,1952; sk,4032;
                          word_sub stackpointer (word 11424),11424;
                          word(pc + got_stack_chk_guard),8; guard,8;
                          word(pc + got_memset),8;
                          word(pc + got_memcpy),8;
                          word(pc + got_randombytes),8; ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mld_compute_pack_t0_t165_consts),272]
                         [pk,1952; sk,4032;
                          word_sub stackpointer (word 11424),11424]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 11424),11424)])`;;

let MLDSA_NATIVE_KEYPAIR_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KEYPAIR_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
