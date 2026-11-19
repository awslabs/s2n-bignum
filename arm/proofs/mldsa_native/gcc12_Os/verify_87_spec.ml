(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a message (pure ML-DSA): the statement. This is  *)
(* the code for mldsa87_verify (mld_sign_verify in sign.c, an external API   *)
(* function) from mldsa-native's portable C implementation compiled by gcc   *)
(* 12 with -Os (see mldsa_native/README.md), which builds the prefix 0 ||    *)
(* ctxlen || ctx of pure ML-DSA with                                         *)
(* mldsa87_prepare_domain_separation_prefix, returning -9 if ctxlen > 255,   *)
(* and otherwise verifies with mldsa87_verify_internal, and zeroes the       *)
(* prefix with mld_zeroize_6, a call of memset. It is verified in the whole  *)
(* image (see libmldsa.ml), using the theorems for the callees and the       *)
(* contracts memset_ret_full_contract, memcpy_full_contract of the C library *)
(* functions, and shown to be constant time and memory safe.                 *)
(* ========================================================================= *)


needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/prepare_domain_separation_prefix_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/verify_internal_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_6_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa87_verify:
       +0x0: stp     x19, x20, [sp, #-416]!
       +0x4: mov     x20, x5
       +0x8: adrp    x5, <page>
       +0xc: ldr     x5, [x5, #4088]
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: add     x19, sp, #0x4f
      +0x18: stp     x23, x30, [sp, #32]
      +0x1c: mov     x21, x0
      +0x20: and     x19, x19, #0xffffffffffffffe0
      +0x24: ldr     x0, [x5]
      +0x28: str     x0, [sp, #408]
      +0x2c: mov     x0, #0x0
      +0x30: mov     x22, x1
      +0x34: mov     x23, x2
      +0x38: mov     x0, x19
      +0x3c: mov     w5, #0x0
      +0x40: mov     x2, #0x0
      +0x44: mov     x1, #0x0
      +0x48: bl      <mldsa87_prepare_domain_separation_prefix>
      +0x4c: cbz     x0, <mldsa87_verify+0xa0>
      +0x50: mov     x4, x0
      +0x54: mov     x5, x20
      +0x58: mov     x3, x19
      +0x5c: mov     x2, x23
      +0x60: mov     x1, x22
      +0x64: mov     x0, x21
      +0x68: mov     w6, #0x0
      +0x6c: bl      <mldsa87_verify_internal>
      +0x70: mov     w20, w0
      +0x74: mov     x0, x19
      +0x78: mov     x1, #0x14c
      +0x7c: bl      <mld_zeroize_6>
      +0x80: adrp    x0, <page>
      +0x84: ldr     x0, [x0, #4088]
      +0x88: ldr     x2, [sp, #408]
      +0x8c: ldr     x1, [x0]
      +0x90: subs    x2, x2, x1
      +0x94: mov     x1, #0x0
      +0x98: b.eq    <mldsa87_verify+0xa8>
      +0x9c: bl      <stack_chk_fail>
      +0xa0: mov     w20, #0xfffffff7
      +0xa4: b       <mldsa87_verify+0x74>
      +0xa8: ldp     x21, x22, [sp, #16]
      +0xac: mov     w0, w20
      +0xb0: ldp     x23, x30, [sp, #32]
      +0xb4: ldp     x19, x20, [sp], #416
      +0xb8: ret
 ***)

let MLDSA_NATIVE_VERIFY_87_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa87_verify"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (4627 bytes), the message M of mlen bytes at m, the *)
(* context C of ctxlen bytes at ctx and the public key pkb at pk (2592       *)
(* bytes): the result is -9 if ctxlen > 255, and otherwise 0 if the          *)
(* signature is accepted for the message with the prefix of pure ML-DSA, and *)
(* -6 if not. The stack is the 416 bytes of the function and those of the    *)
(* callees below them.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigb pkb M C guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 60 64
                (num_of_bytelist(list_of_seq sigb 64))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74480),74480))
              [(sig,4627); (m,mlen); (ctx,ctxlen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_verify) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb
                       (mld_verify_mu 2592 pkb (2 + ctxlen)
                         (num_of_bytelist
                           (mld_domain_separation_prefix 0
                             (bytelist_of_num ctxlen C) []))
                         mlen M)
                     then word 0 else word 4294967290))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74480),74480)])`;;

let MLDSA_NATIVE_VERIFY_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the signature, the   *)
(* message, the context and the public key, all public, with all accesses    *)
(* within the arguments, the stack, the GOT entries and the stack guard, the *)
(* region (ea,el) that the C library functions may read and the constants of *)
(* the callees, and the writes within the outputs and the stack.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 60 64
                (num_of_bytelist(list_of_seq sigb 64))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74480),74480))
              [(sig,4627); (m,mlen); (ctx,ctxlen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_verify) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb
                       (mld_verify_mu 2592 pkb (2 + ctxlen)
                         (num_of_bytelist
                           (mld_domain_separation_prefix 0
                             (bytelist_of_num ctxlen C) []))
                         mlen M)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            guard mf mc pc
                            (word_sub stackpointer (word 74480))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; ctx,ctxlen; pk,2592;
                         word_sub stackpointer (word 74480),74480;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa87_prepare_domain_separation_prefix_jump_table), 12;
                         word(pc + mldsa87_prepare_domain_separation_prefix_oid_map), 192]
                        [word_sub stackpointer (word 74480),74480]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74480),74480)])`;;

let MLDSA_NATIVE_VERIFY_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 8 7
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 60 64
                (num_of_bytelist(list_of_seq sigb 64))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74480),74480))
              [(sig,4627); (m,mlen); (ctx,ctxlen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_verify) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            guard mf mc pc
                            (word_sub stackpointer (word 74480))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; ctx,ctxlen; pk,2592;
                         word_sub stackpointer (word 74480),74480;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa87_prepare_domain_separation_prefix_jump_table), 12;
                         word(pc + mldsa87_prepare_domain_separation_prefix_oid_map), 192]
                        [word_sub stackpointer (word 74480),74480]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74480),74480)])`;;

let MLDSA_NATIVE_VERIFY_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
