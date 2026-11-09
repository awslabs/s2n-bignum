(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a pre-hash: the statement. This is the code for  *)
(* mldsa87_verify_pre_hash_internal (mld_sign_verify_pre_hash_internal in    *)
(* sign.c, an external API function) from mldsa-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which returns -9 if hashalg is MLD_PREHASH_NONE (0) or if                 *)
(* mldsa87_prepare_domain_separation_prefix rejects the context or the       *)
(* pre-hash, and otherwise verifies the prefix 1 || ctxlen || ctx || OID ||  *)
(* ph as the message with mldsa87_verify_internal, and zeroes the prefix     *)
(* with memset. It is verified in the whole image (see libmldsa.ml), using   *)
(* the theorems for the callees and the contracts memset_ret_full_contract,  *)
(* memcpy_full_contract of the C library functions, and shown to be constant *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/prepare_domain_separation_prefix_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/verify_internal_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stubs:

    mldsa87_verify_pre_hash_internal:
       +0x0: stp     x19, x20, [sp, #-400]!
       +0x4: adrp    x7, <page>
       +0x8: ldr     x7, [x7, #4088]
       +0xc: str     x30, [sp, #24]
      +0x10: add     x19, sp, #0x3f
      +0x14: ldr     x8, [x7]
      +0x18: str     x8, [sp, #392]
      +0x1c: mov     x8, #0x0
      +0x20: and     x19, x19, #0xffffffffffffffe0
      +0x24: cbz     w6, <+0xac>
      +0x28: mov     x20, x0
      +0x2c: mov     x0, x19
      +0x30: str     x21, [sp, #16]
      +0x34: mov     x21, x5
      +0x38: mov     w5, w6
      +0x3c: bl      <mldsa87_prepare_domain_separation_prefix>
      +0x40: mov     x2, x0
      +0x44: cbz     x0, <+0xa8>
      +0x48: mov     x5, x21
      +0x4c: mov     x0, x20
      +0x50: mov     x1, x19
      +0x54: mov     w6, #0x0
      +0x58: mov     x4, #0x0
      +0x5c: mov     x3, #0x0
      +0x60: bl      <mldsa87_verify_internal>
      +0x64: mov     w20, w0
      +0x68: ldr     x21, [sp, #16]
      +0x6c: mov     x0, x19
      +0x70: mov     x2, #0x14c
      +0x74: mov     w1, #0x0
      +0x78: bl      <memset@plt>
      +0x7c: adrp    x0, <page>
      +0x80: ldr     x0, [x0, #4088]
      +0x84: ldr     x2, [sp, #392]
      +0x88: ldr     x1, [x0]
      +0x8c: subs    x2, x2, x1
      +0x90: mov     x1, #0x0
      +0x94: b.ne    <+0xb4>
      +0x98: ldr     x30, [sp, #24]
      +0x9c: mov     w0, w20
      +0xa0: ldp     x19, x20, [sp], #400
      +0xa4: ret
      +0xa8: ldr     x21, [sp, #16]
      +0xac: mov     w20, #0xfffffff7
      +0xb0: b       <+0x6c>
      +0xb4: str     x21, [sp, #16]
      +0xb8: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_verify_pre_hash_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (4627 bytes), the pre-hash PH of phlen bytes at ph, *)
(* the context C of ctxlen bytes at ctx and the public key pkb at pk (2592   *)
(* bytes), with HA the 32-bit hashalg, PRE the prefix and PLEN its length (0 *)
(* if it is invalid): the result is -9 for an invalid hashalg or prefix, and *)
(* otherwise 0 if the signature is accepted for PRE as the message and -6 if *)
(* not. The stack is the 400 bytes of the function and those of the callees  *)
(* below them.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig ph phlen ctx ctxlen pk hashalg sigb pkb PH C HA PLEN
                 PRE guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 60 64
                (num_of_bytelist(list_of_seq sigb 64))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74624),74624))
              [(sig,4627); (ph,phlen); (ctx,ctxlen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_verify_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; pk;
                                 hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if HA = 0 \/ PLEN = 0 then word 4294967287
                     else if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb
                       (mld_verify_mu 2592 pkb 0 0 PLEN PRE)
                     then word 0 else word 4294967290))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74624),74624)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, hashalg, the         *)
(* signature, the pre-hash, the context and the public key, all public, with *)
(* all accesses within the arguments, the stack, the GOT entries and the     *)
(* stack guard, the region (ea,el) that the C library functions may read and *)
(* the constants of the callees, and the writes within the outputs and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig ph phlen ctx ctxlen pk hashalg sigb pkb PH C HA PLEN
                 PRE guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 60 64
                (num_of_bytelist(list_of_seq sigb 64))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74624),74624))
              [(sig,4627); (ph,phlen); (ctx,ctxlen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_verify_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; pk;
                                 hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if HA = 0 \/ PLEN = 0 then word 4294967287
                     else if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb
                       (mld_verify_mu 2592 pkb 0 0 PLEN PRE)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig ph phlen ctx ctxlen pk hashalg sigb
                            pkb PH C guard mf mc pc
                            (word_sub stackpointer (word 74624))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; ph,phlen; ctx,ctxlen; pk,2592;
                         word_sub stackpointer (word 74624),74624;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
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
                        [word_sub stackpointer (word 74624),74624]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74624),74624)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig ph phlen ctx ctxlen pk hashalg sigb pkb PH C HA PLEN
                 PRE guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 60 64
                (num_of_bytelist(list_of_seq sigb 64))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74624),74624))
              [(sig,4627); (ph,phlen); (ctx,ctxlen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_verify_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; pk;
                                 hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig ph phlen ctx ctxlen pk hashalg sigb
                            pkb PH C guard mf mc pc
                            (word_sub stackpointer (word 74624))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; ph,phlen; ctx,ctxlen; pk,2592;
                         word_sub stackpointer (word 74624),74624;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
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
                        [word_sub stackpointer (word 74624),74624]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74624),74624)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
