(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a pre-hash (HashML-DSA): the statement. This is the code for      *)
(* mldsa65_signature_pre_hash_internal (mld_sign_signature_pre_hash_internal *)
(* in sign.c, an external API function) from mldsa-native's portable C       *)
(* implementation compiled by clang 23 with -O3 as one translation unit with *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which returns -9 if   *)
(* hashalg is MLD_PREHASH_NONE (0) or if                                     *)
(* mldsa65_prepare_domain_separation_prefix rejects the context or the pre-  *)
(* hash, and otherwise signs the prefix 1 || ctxlen || ctx || OID || ph as   *)
(* the message with mldsa65_signature_internal, zeroing the signature on any *)
(* failure and the prefix with memset. It is verified in the whole image     *)
(* (see libmldsa.ml), using the theorems for the callees and the contracts   *)
(* memset_full_contract, memcpy_full_contract of the C library functions,    *)
(* and shown to be constant time and memory safe.                            *)
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

    mldsa65_signature_pre_hash_internal:
       +0x0: stp     x29, x30, [sp, #-48]!
       +0x4: stp     x28, x21, [sp, #16]
       +0x8: stp     x20, x19, [sp, #32]
       +0xc: mov     x29, sp
      +0x10: sub     x9, sp, #0x170
      +0x14: and     sp, x9, #0xffffffffffffffe0
      +0x18: adrp    x8, <page>
      +0x1c: mov     x20, x0
      +0x20: ldr     x8, [x8, #4088]
      +0x24: ldr     x8, [x8]
      +0x28: str     x8, [sp, #360]
      +0x2c: cbz     w7, <mldsa65_signature_pre_hash_internal+0x78>
      +0x30: mov     x21, x5
      +0x34: mov     x0, sp
      +0x38: mov     w5, w7
      +0x3c: mov     x19, x6
      +0x40: bl      <mldsa65_prepare_domain_separation_prefix>
      +0x44: cbz     x0, <mldsa65_signature_pre_hash_internal+0x78>
      +0x48: mov     x2, x0
      +0x4c: mov     x1, sp
      +0x50: mov     x0, x20
      +0x54: mov     x3, xzr
      +0x58: mov     x4, xzr
      +0x5c: mov     x5, x21
      +0x60: mov     x6, x19
      +0x64: mov     w7, wzr
      +0x68: bl      <mldsa65_signature_internal>
      +0x6c: mov     w19, w0
      +0x70: cbnz    w0, <mldsa65_signature_pre_hash_internal+0x7c>
      +0x74: b       <mldsa65_signature_pre_hash_internal+0x8c>
      +0x78: mov     w19, #0xfffffff7
      +0x7c: mov     x0, x20
      +0x80: mov     w1, wzr
      +0x84: mov     w2, #0xced
      +0x88: bl      <memset>
      +0x8c: movi    v0.2d, #0x0
      +0x90: mov     x8, sp
      +0x94: add     x9, x8, #0x13c
      +0x98: str     q0, [x9]
      +0x9c: stp     q0, q0, [sp]
      +0xa0: stp     q0, q0, [sp, #32]
      +0xa4: stp     q0, q0, [sp, #64]
      +0xa8: stp     q0, q0, [sp, #96]
      +0xac: stp     q0, q0, [sp, #128]
      +0xb0: stp     q0, q0, [sp, #160]
      +0xb4: stp     q0, q0, [sp, #192]
      +0xb8: stp     q0, q0, [sp, #224]
      +0xbc: stp     q0, q0, [sp, #256]
      +0xc0: stp     q0, q0, [sp, #288]
      +0xc4: adrp    x8, <page>
      +0xc8: ldr     x8, [x8, #4088]
      +0xcc: ldr     x9, [sp, #360]
      +0xd0: ldr     x8, [x8]
      +0xd4: cmp     x8, x9
      +0xd8: b.ne    <mldsa65_signature_pre_hash_internal+0x118>
      +0xdc: mov     w0, w19
      +0xe0: mov     sp, x29
      +0xe4: ldp     x20, x19, [sp, #32]
      +0xe8: ldp     x28, x21, [sp, #16]
      +0xec: ldp     x29, x30, [sp], #48
      +0xf0: mov     x1, #0x0
      +0xf4: mov     x2, #0x0
      +0xf8: mov     x3, #0x0
      +0xfc: mov     x4, #0x0
     +0x100: mov     x5, #0x0
     +0x104: mov     x6, #0x0
     +0x108: mov     x7, #0x0
     +0x10c: mov     x8, #0x0
     +0x110: mov     x9, #0x0
     +0x114: ret     
     +0x118: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_signature_pre_hash_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (4032 bytes), the pre-hash PH of phlen bytes at ph,  *)
(* the context C of ctxlen bytes at ctx and the 32 bytes RND at rnd, with HA *)
(* the 32-bit hashalg, PRE the prefix, PLEN its length (0 if it is invalid)  *)
(* and MU the mu of signing PRE: the result is -9 for an invalid hashalg or  *)
(* prefix, with the signature zero, and otherwise that of signing, with the  *)
(* signature mld_sign_sig_65 skb MU RND. The stack is the 15072 bytes below  *)
(* the stack pointer: the frame of the function, of up to 432 bytes, and the *)
(* stacks of its callees. The 12 pointers to the entries of oid_map that     *)
(* mldsa65_prepare_domain_separation_prefix reads, outside the image at pc + *)
(* mldsa65_prepare_domain_separation_prefix_oid_ptrs, are assumed to hold    *)
(* their relocated addresses, and are apart from the stack and the outputs.  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig ph phlen ctx ctxlen rnd sk hashalg skb PH C RND HA
                 PLEN PRE MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0 PLEN PRE /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
               mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 15072),15072)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 15072),15072)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + mldsa65_prepare_domain_separation_prefix_oid_ptrs),96);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s =
                    word(pc + mldsa65_signature_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; rnd;
                                 sk; hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc +
                               mldsa65_prepare_domain_separation_prefix_oid_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map +
                                  16 * k)) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if HA = 0 \/ PLEN = 0 then word 4294967287
                     else if mld_sign_ok_65 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 3309
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if HA = 0 \/ PLEN = 0 then word 0
                             else mld_sign_sig_65 skb MU RND t))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 15072),15072)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, hashalg, rho and     *)
(* what the C code declassifies in signing (mld_sign_declass_65), with all   *)
(* accesses within the arguments, the stack, the GOT entries and the stack   *)
(* guard, the region (ea,el) that the C library functions may read and the   *)
(* constants of the callees, and the writes within the outputs and the       *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig ph phlen ctx ctxlen rnd sk hashalg skb PH C RND HA
                 PLEN PRE MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0 PLEN PRE /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
               mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 15072),15072)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 15072),15072)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + mldsa65_prepare_domain_separation_prefix_oid_ptrs),96);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s =
                    word(pc + mldsa65_signature_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; rnd;
                                 sk; hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc +
                               mldsa65_prepare_domain_separation_prefix_oid_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map +
                                  16 * k)) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if HA = 0 \/ PLEN = 0 then word 4294967287
                     else if mld_sign_ok_65 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 3309
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if HA = 0 \/ PLEN = 0 then word 0
                             else mld_sign_sig_65 skb MU RND t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig ph phlen ctx ctxlen rnd sk hashalg
                            (mld_sk_rho skb) (mld_sign_declass_65 skb MU RND)
                            guard mf mc pc
                            (word_sub stackpointer (word 15072))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; ph,phlen; ctx,ctxlen; rnd,32; sk,4032;
                         word_sub stackpointer (word 15072),15072;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa65_signature_internal_consts),336;
                         word(pc +
                          mldsa65_prepare_domain_separation_prefix_jump_table),
                         13; word(pc +
                          mldsa65_prepare_domain_separation_prefix_oid_ptrs),
                         96;
                         word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [sig,3309; word_sub stackpointer (word 15072),15072]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 15072),15072)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig ph phlen ctx ctxlen rnd sk hashalg skb PH C RND HA
                 PLEN PRE MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0 PLEN PRE /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
               mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 15072),15072)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 15072),15072)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (word(pc + mldsa65_prepare_domain_separation_prefix_oid_ptrs),96);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s =
                    word(pc + mldsa65_signature_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; rnd;
                                 sk; hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc +
                               mldsa65_prepare_domain_separation_prefix_oid_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map +
                                  16 * k)) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig ph phlen ctx ctxlen rnd sk hashalg
                            (mld_sk_rho skb) (mld_sign_declass_65 skb MU RND)
                            guard mf mc pc
                            (word_sub stackpointer (word 15072))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; ph,phlen; ctx,ctxlen; rnd,32; sk,4032;
                         word_sub stackpointer (word 15072),15072;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa65_signature_internal_consts),336;
                         word(pc +
                          mldsa65_prepare_domain_separation_prefix_jump_table),
                         13; word(pc +
                          mldsa65_prepare_domain_separation_prefix_oid_ptrs),
                         96;
                         word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [sig,3309; word_sub stackpointer (word 15072),15072]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 15072),15072)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
