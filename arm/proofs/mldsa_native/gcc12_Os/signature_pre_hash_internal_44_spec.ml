(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a pre-hash (HashML-DSA): the statement. This is the code for      *)
(* mldsa44_signature_pre_hash_internal (mld_sign_signature_pre_hash_internal *)
(* in sign.c, an external API function) from mldsa-native's portable C       *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
(* which returns -9 if hashalg is MLD_PREHASH_NONE (0) or if                 *)
(* mldsa44_prepare_domain_separation_prefix rejects the context or the       *)
(* pre-hash, and otherwise signs the prefix 1 || ctxlen || ctx || OID || ph  *)
(* as the message with mldsa44_signature_internal, zeroing the signature on  *)
(* any failure and the prefix with mld_zeroize (a call of memset). It is     *)
(* verified in the whole image (see libmldsa.ml), using the theorems for the *)
(* callees and the contracts memset_full_contract, memcpy_full_contract of   *)
(* the C library functions, and shown to be constant time and memory safe.   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/prepare_domain_separation_prefix_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/signature_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stubs:

    mldsa44_signature_pre_hash_internal:
       +0x0: stp     x19, x20, [sp, #-416]!
       +0x4: stp     x21, x22, [sp, #16]
       +0x8: mov     x21, x0
       +0xc: mov     x22, x6
      +0x10: adrp    x0, <page>
      +0x14: ldr     x0, [x0, #4088]
      +0x18: str     x30, [sp, #32]
      +0x1c: add     x20, sp, #0x4f
      +0x20: ldr     x6, [x0]
      +0x24: str     x6, [sp, #408]
      +0x28: mov     x6, #0x0
      +0x2c: and     x20, x20, #0xffffffffffffffe0
      +0x30: cbnz    w7, <mldsa44_signature_pre_hash_internal+0x48>
      +0x34: mov     w19, #0xfffffff7
      +0x38: mov     x0, x21
      +0x3c: mov     x1, #0x974
      +0x40: bl      <mld_zeroize_2>
      +0x44: b       <mldsa44_signature_pre_hash_internal+0x88>
      +0x48: mov     x19, x5
      +0x4c: mov     x0, x20
      +0x50: mov     w5, w7
      +0x54: bl      <mldsa44_prepare_domain_separation_prefix>
      +0x58: mov     x2, x0
      +0x5c: cbz     x0, <mldsa44_signature_pre_hash_internal+0x34>
      +0x60: mov     x5, x19
      +0x64: mov     x6, x22
      +0x68: mov     x1, x20
      +0x6c: mov     x0, x21
      +0x70: mov     w7, #0x0
      +0x74: mov     x4, #0x0
      +0x78: mov     x3, #0x0
      +0x7c: bl      <mldsa44_signature_internal>
      +0x80: mov     w19, w0
      +0x84: cbnz    w0, <mldsa44_signature_pre_hash_internal+0x38>
      +0x88: mov     x0, x20
      +0x8c: mov     x1, #0x14c
      +0x90: bl      <mld_zeroize_2>
      +0x94: adrp    x0, <page>
      +0x98: ldr     x0, [x0, #4088]
      +0x9c: ldr     x2, [sp, #408]
      +0xa0: ldr     x1, [x0]
      +0xa4: subs    x2, x2, x1
      +0xa8: mov     x1, #0x0
      +0xac: b.eq    <mldsa44_signature_pre_hash_internal+0xb4>
      +0xb0: bl      <stack_chk_fail>
      +0xb4: ldp     x21, x22, [sp, #16]
      +0xb8: mov     w0, w19
      +0xbc: ldr     x30, [sp, #32]
      +0xc0: ldp     x19, x20, [sp], #416
      +0xc4: ret
 ***)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_signature_pre_hash_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (2560 bytes), the pre-hash PH of phlen bytes at ph,  *)
(* the context C of ctxlen bytes at ctx and the 32 bytes RND at rnd, with HA *)
(* the 32-bit hashalg, PRE the prefix, PLEN its length (0 if it is invalid)  *)
(* and MU the mu of signing PRE: the result is -9 for an invalid hashalg or  *)
(* prefix, with the signature zero, and otherwise that of signing, with the  *)
(* signature mld_sign_sig_44 skb MU RND. The stack is the 416 bytes of the   *)
(* function and those of the callees below them.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig ph phlen ctx ctxlen rnd sk hashalg skb PH C RND HA
                 PLEN PRE MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0 PLEN PRE /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
               mld_sign_terminates_44 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49776),49776)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49776),49776)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s =
                    word(pc + mldsa44_signature_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; rnd;
                                 sk; hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if HA = 0 \/ PLEN = 0 then word 4294967287
                     else if mld_sign_ok_44 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 2420
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if HA = 0 \/ PLEN = 0 then word 0
                             else mld_sign_sig_44 skb MU RND t))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49776),49776)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, hashalg, rho and     *)
(* what the C code declassifies in signing (mld_sign_declass_44), with       *)
(* all accesses within the arguments, the stack, the GOT entries and the     *)
(* stack guard, the region (ea,el) that the C library functions may read and *)
(* the constants of the callees, and the writes within the outputs and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig ph phlen ctx ctxlen rnd sk hashalg skb PH C RND HA
                 PLEN PRE MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0 PLEN PRE /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
               mld_sign_terminates_44 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49776),49776)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49776),49776)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s =
                    word(pc + mldsa44_signature_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; rnd;
                                 sk; hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if HA = 0 \/ PLEN = 0 then word 4294967287
                     else if mld_sign_ok_44 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 2420
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if HA = 0 \/ PLEN = 0 then word 0
                             else mld_sign_sig_44 skb MU RND t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig ph phlen ctx ctxlen rnd sk hashalg
                            (mld_sk_rho skb) (mld_sign_declass_44 skb MU RND)
                            guard mf mc pc
                            (word_sub stackpointer (word 49776))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; ph,phlen; ctx,ctxlen; rnd,32; sk,2560;
                         word_sub stackpointer (word 49776),49776;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el; word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
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
                        [sig,2420; word_sub stackpointer (word 49776),49776]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49776),49776)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig ph phlen ctx ctxlen rnd sk hashalg skb PH C RND HA
                 PLEN PRE MU guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0 PLEN PRE /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
               mld_sign_terminates_44 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49776),49776)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49776),49776)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s =
                    word(pc + mldsa44_signature_pre_hash_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; rnd;
                                 sk; hashalg] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig ph phlen ctx ctxlen rnd sk hashalg
                            (mld_sk_rho skb) (mld_sign_declass_44 skb MU RND)
                            guard mf mc pc
                            (word_sub stackpointer (word 49776))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; ph,phlen; ctx,ctxlen; rnd,32; sk,2560;
                         word_sub stackpointer (word 49776),49776;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el; word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
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
                        [sig,2420; word_sub stackpointer (word 49776),49776]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49776),49776)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
