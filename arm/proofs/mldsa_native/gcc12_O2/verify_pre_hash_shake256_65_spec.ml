(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature with a SHAKE256 pre-hash: the statement. This is    *)
(* the code for mldsa65_verify_pre_hash_shake256                             *)
(* (mld_sign_verify_pre_hash_shake256 in sign.c, an external API function)   *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which hashes the message to 64 bytes with   *)
(* mldsa_shake256 and verifies that pre-hash with                            *)
(* mldsa65_verify_pre_hash_internal and hashalg MLD_PREHASH_SHAKE_256 (12),  *)
(* and then zeroes the pre-hash. It is verified in the whole image (see      *)
(* libmldsa.ml), using the theorems for the callees and the contracts        *)
(* memset_ret_full_contract, memcpy_full_contract of the C library           *)
(* functions, and shown to be constant time and memory safe.                 *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/verify_pre_hash_internal_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_verify_pre_hash_shake256:
       +0x0: stp     x19, x20, [sp, #-144]!
       +0x4: mov     x7, x2
       +0x8: mov     x2, x1
       +0xc: adrp    x6, <page>
      +0x10: ldr     x6, [x6, #4088]
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: add     x19, sp, #0x4f
      +0x1c: stp     x23, x30, [sp, #32]
      +0x20: and     x19, x19, #0xffffffffffffffe0
      +0x24: mov     x20, x0
      +0x28: ldr     x1, [x6]
      +0x2c: str     x1, [sp, #136]
      +0x30: mov     x1, #0x0
      +0x34: mov     x21, x3
      +0x38: mov     x22, x4
      +0x3c: mov     x3, x7
      +0x40: mov     x23, x5
      +0x44: mov     x0, x19
      +0x48: mov     x1, #0x40
      +0x4c: bl      <mldsa_shake256>
      +0x50: mov     x5, x23
      +0x54: mov     x4, x22
      +0x58: mov     x3, x21
      +0x5c: mov     x0, x20
      +0x60: mov     x1, x19
      +0x64: mov     w6, #0xc
      +0x68: mov     x2, #0x40
      +0x6c: bl      <mldsa65_verify_pre_hash_internal>
      +0x70: movi    v0.4s, #0x0
      +0x74: stp     q0, q0, [x19]
      +0x78: stp     q0, q0, [x19, #32]
      +0x7c: adrp    x1, <page>
      +0x80: ldr     x1, [x1, #4088]
      +0x84: ldr     x3, [sp, #136]
      +0x88: ldr     x2, [x1]
      +0x8c: subs    x3, x3, x2
      +0x90: mov     x2, #0x0
      +0x94: b.ne    <+0xa8>
      +0x98: ldp     x21, x22, [sp, #16]
      +0x9c: ldp     x23, x30, [sp, #32]
      +0xa0: ldp     x19, x20, [sp], #144
      +0xa4: ret
      +0xa8: bl      <__stack_chk_fail@plt>
 ***)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_verify_pre_hash_shake256"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (3309 bytes), the message M of mlen bytes at m, the *)
(* context C of ctxlen bytes at ctx and the public key pkb at pk (1952       *)
(* bytes), with PH the SHAKE256 pre-hash of M and PRE the prefix of          *)
(* HashML-DSA (of length ctxlen + 77): the result is -9 if ctxlen > 255, and *)
(* otherwise 0 if the signature is accepted for PRE as the message and -6 if *)
(* not. The stack is the 144 bytes of the function and those of the callees  *)
(* below them.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigb pkb M C PH PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 49 48
                (num_of_bytelist(list_of_seq sigb 48))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45824),45824))
              [(sig,3309); (m,mlen); (ctx,ctxlen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_verify_pre_hash_shake256) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_verify_internal_ok 6 5 48
                           mld_polyz_unpack_19 640 524092
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49
                           sigb pkb
                       (mld_verify_mu 1952 pkb 0 0 (ctxlen + 77) PRE)
                     then word 0 else word 4294967290))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45824),45824)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the signature, the   *)
(* message, the context and the public key, all public, with all accesses    *)
(* within the arguments, the stack, the GOT entries and the stack guard, the *)
(* region (ea,el) that the C library functions may read and the constants of *)
(* the callees, and the writes within the outputs and the stack.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C PH PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 49 48
                (num_of_bytelist(list_of_seq sigb 48))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45824),45824))
              [(sig,3309); (m,mlen); (ctx,ctxlen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_verify_pre_hash_shake256) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_verify_internal_ok 6 5 48
                           mld_polyz_unpack_19 640 524092
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49
                           sigb pkb
                       (mld_verify_mu 1952 pkb 0 0 (ctxlen + 77) PRE)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            guard mf mc pc
                            (word_sub stackpointer (word 45824))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; ctx,ctxlen; pk,1952;
                         word_sub stackpointer (word 45824),45824;
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
                          mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                          mldsa65_polyvecl_pointwise_acc_montgomery_const2),16;
                         word(pc +
                          mldsa65_prepare_domain_separation_prefix_jump_table),
                         12;
                         word(pc +
                          mldsa65_prepare_domain_separation_prefix_oid_map),
                         192]
                        [word_sub stackpointer (word 45824),45824]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45824),45824)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C PH PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 49 48
                (num_of_bytelist(list_of_seq sigb 48))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45824),45824))
              [(sig,3309); (m,mlen); (ctx,ctxlen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_verify_pre_hash_shake256) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            guard mf mc pc
                            (word_sub stackpointer (word 45824))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; ctx,ctxlen; pk,1952;
                         word_sub stackpointer (word 45824),45824;
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
                          mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                          mldsa65_polyvecl_pointwise_acc_montgomery_const2),16;
                         word(pc +
                          mldsa65_prepare_domain_separation_prefix_jump_table),
                         12;
                         word(pc +
                          mldsa65_prepare_domain_separation_prefix_oid_map),
                         192]
                        [word_sub stackpointer (word 45824),45824]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45824),45824)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
