(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message with a SHAKE256 pre-hash (HashML-DSA): the statement.   *)
(* This is the code for mldsa44_signature_pre_hash_shake256                  *)
(* (mld_sign_signature_pre_hash_shake256 in sign.c, an external API          *)
(* function) from mldsa-native's portable C implementation compiled by gcc   *)
(* 12 with -O2 (see mldsa_native/README.md), which hashes the message to 64  *)
(* bytes with mldsa_shake256 and signs that pre-hash with                    *)
(* mldsa44_signature_pre_hash_internal and hashalg MLD_PREHASH_SHAKE_256     *)
(* (12), and then zeroes the pre-hash. It is verified in the whole image     *)
(* (see libmldsa.ml), using the theorems for the callees and the contracts   *)
(* memset_full_contract, memcpy_full_contract of the C library functions,    *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/signature_pre_hash_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_signature_pre_hash_shake256:
       +0x0: stp     x19, x20, [sp, #-160]!
       +0x4: mov     x8, x2
       +0x8: mov     x2, x1
       +0xc: adrp    x7, <page>
      +0x10: ldr     x7, [x7, #4088]
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: add     x19, sp, #0x5f
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: and     x19, x19, #0xffffffffffffffe0
      +0x24: mov     x20, x0
      +0x28: str     x30, [sp, #48]
      +0x2c: mov     x21, x3
      +0x30: mov     x22, x4
      +0x34: mov     x3, x8
      +0x38: ldr     x1, [x7]
      +0x3c: str     x1, [sp, #152]
      +0x40: mov     x1, #0x0
      +0x44: mov     x23, x5
      +0x48: mov     x24, x6
      +0x4c: mov     x0, x19
      +0x50: mov     x1, #0x40
      +0x54: bl      <mldsa_shake256>
      +0x58: mov     x6, x24
      +0x5c: mov     x5, x23
      +0x60: mov     x4, x22
      +0x64: mov     x3, x21
      +0x68: mov     x0, x20
      +0x6c: mov     x1, x19
      +0x70: mov     w7, #0xc
      +0x74: mov     x2, #0x40
      +0x78: bl      <mldsa44_signature_pre_hash_internal>
      +0x7c: movi    v0.4s, #0x0
      +0x80: stp     q0, q0, [x19]
      +0x84: stp     q0, q0, [x19, #32]
      +0x88: adrp    x1, <page>
      +0x8c: ldr     x1, [x1, #4088]
      +0x90: ldr     x3, [sp, #152]
      +0x94: ldr     x2, [x1]
      +0x98: subs    x3, x3, x2
      +0x9c: mov     x2, #0x0
      +0xa0: b.ne    <+0xb8>
      +0xa4: ldp     x21, x22, [sp, #16]
      +0xa8: ldp     x23, x24, [sp, #32]
      +0xac: ldr     x30, [sp, #48]
      +0xb0: ldp     x19, x20, [sp], #160
      +0xb4: ret
      +0xb8: bl      <__stack_chk_fail@plt>
 ***)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_signature_pre_hash_shake256"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (2560 bytes), the message M of mlen bytes at m, the  *)
(* context C of ctxlen bytes at ctx and the 32 bytes RND at rnd, with PH the *)
(* SHAKE256 pre-hash of M, PRE the prefix of HashML-DSA (of length ctxlen +  *)
(* 77 if ctxlen <= 255) and MU the mu of signing PRE: the result is -9 if    *)
(* ctxlen > 255, with the signature zero, and otherwise that of signing,     *)
(* with the signature mld_sign_sig_44 skb MU RND. The stack is the 160 bytes *)
(* of the function and those of the callees below them.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen rnd sk skb M C RND PH PRE MU
                 guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0
                (mld_domain_separation_prefix_length 12 ctxlen 64) PRE /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
               mld_sign_terminates_44 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 50112),50112)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 50112),50112)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa44_signature_pre_hash_shake256) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; rnd;
                                 sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_sign_ok_44 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 2420
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if 255 < ctxlen then word 0
                             else mld_sign_sig_44 skb MU RND t))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 50112),50112)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, rho and what the C   *)
(* code declassifies in signing (mld_sign_declass_44), with all accesses     *)
(* within the arguments, the stack, the GOT entries and the stack guard, the *)
(* region (ea,el) that the C library functions may read and the constants of *)
(* the callees, and the writes within the outputs and the stack.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen rnd sk skb M C RND PH PRE MU
                 guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0
                (mld_domain_separation_prefix_length 12 ctxlen 64) PRE /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
               mld_sign_terminates_44 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 50112),50112)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 50112),50112)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa44_signature_pre_hash_shake256) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; rnd;
                                 sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_sign_ok_44 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 2420
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if 255 < ctxlen then word 0
                             else mld_sign_sig_44 skb MU RND t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen rnd sk
                            (mld_sk_rho skb) (mld_sign_declass_44 skb MU RND)
                            guard mf mc pc
                            (word_sub stackpointer (word 50112))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; ctx,ctxlen; rnd,32; sk,2560;
                         word_sub stackpointer (word 50112),50112;
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
                          mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                          mldsa44_polyvecl_pointwise_acc_montgomery_const2),16;
                         word(pc +
                          mldsa44_prepare_domain_separation_prefix_jump_table),
                         12;
                         word(pc +
                          mldsa44_prepare_domain_separation_prefix_oid_map),
                         192]
                        [sig,2420; word_sub stackpointer (word 50112),50112]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 50112),50112)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen rnd sk skb M C RND PH PRE MU
                 guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0
                (mld_domain_separation_prefix_length 12 ctxlen 64) PRE /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
               mld_sign_terminates_44 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 50112),50112)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 50112),50112)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc + mldsa44_signature_pre_hash_shake256) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; rnd;
                                 sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen rnd sk
                            (mld_sk_rho skb) (mld_sign_declass_44 skb MU RND)
                            guard mf mc pc
                            (word_sub stackpointer (word 50112))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; ctx,ctxlen; rnd,32; sk,2560;
                         word_sub stackpointer (word 50112),50112;
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
                          mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                          mldsa44_polyvecl_pointwise_acc_montgomery_const2),16;
                         word(pc +
                          mldsa44_prepare_domain_separation_prefix_jump_table),
                         12;
                         word(pc +
                          mldsa44_prepare_domain_separation_prefix_oid_map),
                         192]
                        [sig,2420; word_sub stackpointer (word 50112),50112]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 50112),50112)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
