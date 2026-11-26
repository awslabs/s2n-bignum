(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a pre-hash: the statement. This is the code for  *)
(* mldsa44_verify_pre_hash_internal (mld_sign_verify_pre_hash_internal in    *)
(* sign.c, an external API function) from mldsa-native's portable C          *)
(* implementation compiled by clang 23 with -O3 as one translation unit with *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which returns -9 if   *)
(* hashalg is MLD_PREHASH_NONE (0) or if                                     *)
(* mldsa44_prepare_domain_separation_prefix rejects the context or the pre-  *)
(* hash, and otherwise verifies the prefix 1 || ctxlen || ctx || OID || ph   *)
(* as the message with mldsa44_verify_internal, and zeroes the buffer with   *)
(* stores of zero vectors. It is verified in the whole image (see            *)
(* libmldsa.ml), using the theorems for the callees and the contracts        *)
(* memset_ret_full_contract, memcpy_full_contract of the C library           *)
(* functions, and shown to be constant time and memory safe.                 *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/prepare_domain_separation_prefix_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stubs:

    mldsa44_verify_pre_hash_internal:
       +0x0: stp     x29, x30, [sp, #-48]!
       +0x4: str     x28, [sp, #16]
       +0x8: stp     x20, x19, [sp, #32]
       +0xc: mov     x29, sp
      +0x10: sub     x9, sp, #0x170
      +0x14: and     sp, x9, #0xffffffffffffffe0
      +0x18: adrp    x8, <page>
      +0x1c: ldr     x8, [x8, #4088]
      +0x20: ldr     x8, [x8]
      +0x24: str     x8, [sp, #360]
      +0x28: cbz     w6, <mldsa44_verify_pre_hash_internal+0x68>
      +0x2c: mov     x20, x0
      +0x30: mov     x19, x5
      +0x34: mov     x0, sp
      +0x38: mov     w5, w6
      +0x3c: bl      <mldsa44_prepare_domain_separation_prefix>
      +0x40: cbz     x0, <mldsa44_verify_pre_hash_internal+0x68>
      +0x44: mov     x2, x0
      +0x48: mov     x1, sp
      +0x4c: mov     x0, x20
      +0x50: mov     x3, xzr
      +0x54: mov     x4, xzr
      +0x58: mov     x5, x19
      +0x5c: mov     w6, wzr
      +0x60: bl      <mldsa44_verify_internal>
      +0x64: b       <mldsa44_verify_pre_hash_internal+0x6c>
      +0x68: mov     w0, #0xfffffff7
      +0x6c: movi    v0.2d, #0x0
      +0x70: mov     x8, sp
      +0x74: add     x9, x8, #0x13c
      +0x78: str     q0, [x9]
      +0x7c: stp     q0, q0, [sp]
      +0x80: stp     q0, q0, [sp, #32]
      +0x84: stp     q0, q0, [sp, #64]
      +0x88: stp     q0, q0, [sp, #96]
      +0x8c: stp     q0, q0, [sp, #128]
      +0x90: stp     q0, q0, [sp, #160]
      +0x94: stp     q0, q0, [sp, #192]
      +0x98: stp     q0, q0, [sp, #224]
      +0x9c: stp     q0, q0, [sp, #256]
      +0xa0: stp     q0, q0, [sp, #288]
      +0xa4: adrp    x8, <page>
      +0xa8: ldr     x8, [x8, #4088]
      +0xac: ldr     x9, [sp, #360]
      +0xb0: ldr     x8, [x8]
      +0xb4: cmp     x8, x9
      +0xb8: b.ne    <mldsa44_verify_pre_hash_internal+0xf0>
      +0xbc: mov     sp, x29
      +0xc0: ldp     x20, x19, [sp, #32]
      +0xc4: ldr     x28, [sp, #16]
      +0xc8: ldp     x29, x30, [sp], #48
      +0xcc: mov     x1, #0x0
      +0xd0: mov     x2, #0x0
      +0xd4: mov     x3, #0x0
      +0xd8: mov     x4, #0x0
      +0xdc: mov     x5, #0x0
      +0xe0: mov     x6, #0x0
      +0xe4: mov     x8, #0x0
      +0xe8: mov     x9, #0x0
      +0xec: ret     
      +0xf0: bl      <__stack_chk_fail>
 ***)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_verify_pre_hash_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (2420 bytes), the pre-hash PH of phlen bytes at ph, *)
(* the context C of ctxlen bytes at ctx and the public key pkb at pk (1312   *)
(* bytes), with HA the 32-bit hashalg, PRE the prefix and PLEN its length (0 *)
(* if it is invalid): the result is -9 for an invalid hashalg or prefix, and *)
(* otherwise 0 if the signature is accepted for PRE as the message and -6 if *)
(* not. The stack is the 11904 bytes below the stack pointer: the frame of   *)
(* the function, of up to 432 bytes, and the stacks of its callees. The 12   *)
(* pointers to the entries of oid_map that                                   *)
(* mldsa44_prepare_domain_separation_prefix reads, outside the image at pc + *)
(* mldsa44_prepare_domain_separation_prefix_oid_ptrs, are assumed to hold    *)
(* their relocated addresses, and are apart from the stack.                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig ph phlen ctx ctxlen pk hashalg sigb pkb PH C HA PLEN
                 PRE guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(list_of_seq sigb 32))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 11904),11904))
              [(sig,2420); (ph,phlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (word(pc + mldsa44_prepare_domain_separation_prefix_oid_ptrs),96);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_verify_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; pk;
                                 hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc +
                               mldsa44_prepare_domain_separation_prefix_oid_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map +
                                  16 * k)) /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if HA = 0 \/ PLEN = 0 then word 4294967287
                     else if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                       (mld_verify_mu 1312 pkb 0 0 PLEN PRE)
                     then word 0 else word 4294967290))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11904),11904)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, hashalg, the         *)
(* signature, the pre-hash, the context and the public key, all public, with *)
(* all accesses within the arguments, the stack, the GOT entries and the     *)
(* stack guard, the region (ea,el) that the C library functions may read and *)
(* the constants of the callees, and the writes within the outputs and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig ph phlen ctx ctxlen pk hashalg sigb pkb PH C HA PLEN
                 PRE guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(list_of_seq sigb 32))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 11904),11904))
              [(sig,2420); (ph,phlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (word(pc + mldsa44_prepare_domain_separation_prefix_oid_ptrs),96);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_verify_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; pk;
                                 hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc +
                               mldsa44_prepare_domain_separation_prefix_oid_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map +
                                  16 * k)) /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if HA = 0 \/ PLEN = 0 then word 4294967287
                     else if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                       (mld_verify_mu 1312 pkb 0 0 PLEN PRE)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig ph phlen ctx ctxlen pk hashalg sigb
                            pkb PH C guard mf mc pc
                            (word_sub stackpointer (word 11904))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; ph,phlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 11904),11904;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa44_verify_internal_const1),16;
                         word(pc + mldsa44_verify_internal_const2),16;
                         word(pc + mldsa44_verify_internal_const3),8;
                         word(pc +
                          mldsa44_prepare_domain_separation_prefix_jump_table),
                         13; word(pc +
                          mldsa44_prepare_domain_separation_prefix_oid_ptrs),
                         96;
                         word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [word_sub stackpointer (word 11904),11904]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11904),11904)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig ph phlen ctx ctxlen pk hashalg sigb pkb PH C HA PLEN
                 PRE guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(list_of_seq sigb 32))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 11904),11904))
              [(sig,2420); (ph,phlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (word(pc + mldsa44_prepare_domain_separation_prefix_oid_ptrs),96);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_verify_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; pk;
                                 hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc +
                               mldsa44_prepare_domain_separation_prefix_oid_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map +
                                  16 * k)) /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig ph phlen ctx ctxlen pk hashalg sigb
                            pkb PH C guard mf mc pc
                            (word_sub stackpointer (word 11904))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; ph,phlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 11904),11904;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa44_verify_internal_const1),16;
                         word(pc + mldsa44_verify_internal_const2),16;
                         word(pc + mldsa44_verify_internal_const3),8;
                         word(pc +
                          mldsa44_prepare_domain_separation_prefix_jump_table),
                         13; word(pc +
                          mldsa44_prepare_domain_separation_prefix_oid_ptrs),
                         96;
                         word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [word_sub stackpointer (word 11904),11904]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11904),11904)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
