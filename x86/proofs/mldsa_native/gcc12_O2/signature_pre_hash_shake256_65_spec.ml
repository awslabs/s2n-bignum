(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message with a SHAKE256 pre-hash (HashML-DSA): the statement.   *)
(* This is the code for mldsa65_signature_pre_hash_shake256                  *)
(* (mld_sign_signature_pre_hash_shake256 in sign.c, an external API          *)
(* function) from mldsa-native's portable C implementation compiled by gcc   *)
(* 12 with -O2 (see mldsa_native/README.md), which aligns its frame to 32    *)
(* bytes, hashes the message with mldsa_shake256 into a 64-byte buffer on    *)
(* the stack, signs that pre-hash with mldsa65_signature_pre_hash_internal   *)
(* with hashalg = MLD_PREHASH_SHAKE_256 (12), and zeroes the buffer with SSE *)
(* stores. It is verified in the whole image (see libmldsa.ml), using the    *)
(* theorems for the callees and the contracts memset_full_contract and       *)
(* memcpy_full_contract of utils/mldsa_native_libc.ml for the C library      *)
(* functions that they call, and shown to be constant time and memory safe.  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/signature_pre_hash_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_signature_pre_hash_shake256:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r15
      +0x13  mov     r15, r9
      +0x16  push    r14
      +0x18  mov     r14, r8
      +0x1b  push    r13
      +0x1d  mov     r13, rcx
      +0x20  mov     rcx, rdx
      +0x23  mov     rdx, rsi
      +0x26  push    r12
      +0x28  mov     esi, 0x40
      +0x2d  push    r10
      +0x2f  push    rbx
      +0x30  lea     rbx, [rbp-0x70]
      +0x34  sub     rsp, 0x60
      +0x38  mov     r12, QWORD PTR [r10]
      +0x3b  mov     QWORD PTR [rbp-0x78], rdi
      +0x3f  mov     rdi, rbx
      +0x42  call    mldsa_shake256
     after_mldsa_shake256:
      +0x47  push    0xc
      +0x49  mov     rdi, QWORD PTR [rbp-0x78]
      +0x4d  mov     r9, r15
      +0x50  push    r12
      +0x52  mov     r8, r14
      +0x55  mov     rcx, r13
      +0x58  mov     edx, 0x40
      +0x5d  mov     rsi, rbx
      +0x60  call    mldsa65_signature_pre_hash_internal
     after_mldsa65_signature_pre_hash_internal:
      +0x65  pxor    xmm0, xmm0
      +0x69  movaps  XMMWORD PTR [rbp-0x70], xmm0
      +0x6d  movaps  XMMWORD PTR [rbp-0x60], xmm0
      +0x71  movaps  XMMWORD PTR [rbp-0x50], xmm0
      +0x75  movaps  XMMWORD PTR [rbp-0x40], xmm0
      +0x79  pop     rdx
      +0x7a  pop     rcx
      +0x7b  lea     rsp, [rbp-0x30]
      +0x7f  pop     rbx
      +0x80  pop     r10
      +0x82  pop     r12
      +0x84  pop     r13
      +0x86  pop     r14
      +0x88  pop     r15
      +0x8a  pop     rbp
      +0x8b  lea     rsp, [r10-0x8]
     ret:
      +0x8f  ret
 ***)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_signature_pre_hash_shake256"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* message M of mlen bytes at m, the context C of ctxlen bytes at ctx, the   *)
(* 32 bytes RND at rnd and the secret key skb at sk (4032 bytes), the        *)
(* seventh argument, on the stack above the return address, with PH the      *)
(* pre-hash, PRE the prefix 1 || ctxlen || ctx || OID || PH and MU the mu of *)
(* signing it: the result is -9 if ctxlen > 255, with the signature zeroed,  *)
(* and otherwise that of signing, with the signature mld_sign_sig_65 skb MU  *)
(* RND (zero if signing fails). The function keeps the stack pointer of the  *)
(* entry in R10, lowers RSP by up to 31 bytes to align it to 32 bytes,       *)
(* copies the return address there and saves RBP, the frame pointer, and six *)
(* more registers, and reserves the stack for the pre-hash, the saved sig    *)
(* and the two arguments of mldsa65_signature_pre_hash_internal on the       *)
(* stack, whose call uses 73540 bytes below them, with its return address:   *)
(* 73747 bytes of stack below the return address in all. The GOT entries of  *)
(* memset and memcpy and the region (ea,el) that they may read are apart     *)
(* from the signature and the stack.                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen rnd sk skb M C RND PH PRE MU
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0
                (mld_domain_separation_prefix_length 12 ctxlen 64) PRE /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
               mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73747),73747)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73747),73747)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,3309) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s =
                    word(pc + mldsa65_signature_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_sign_ok_65 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 3309
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if 255 < ctxlen then word 0
                             else mld_sign_sig_65 skb MU RND t))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73747),73747)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, rho and what the C   *)
(* code declassifies in signing (mld_sign_declass_65), with all accesses     *)
(* within the arguments, the stack, the return address and the argument      *)
(* above it, the GOT entries, the region (ea,el) that the C library          *)
(* functions may read and the constants of the callees, and the writes       *)
(* within the signature and the stack.                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen rnd sk skb M C RND PH PRE MU
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0
                (mld_domain_separation_prefix_length 12 ctxlen 64) PRE /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
               mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73747),73747)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73747),73747)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,3309) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s =
                    word(pc + mldsa65_signature_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_sign_ok_65 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 3309
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if 255 < ctxlen then word 0
                             else mld_sign_sig_65 skb MU RND t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen rnd sk
                            (mld_sk_rho skb) (mld_sign_declass_65 skb MU RND)
                            mf mc pc (word_sub stackpointer (word 73747))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; ctx,ctxlen; rnd,32; sk,4032;
                         word_sub stackpointer (word 73747),73747;
                         stackpointer,8; word_add stackpointer (word 8),8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                           mldsa65_polyvec_matrix_expand_eager_consts),4;
                         word(pc +
                       mldsa65_prepare_domain_separation_prefix_switch1_table),
                         52;
                         word(pc + rodata_oid_map_0_2),192]
                        [sig,3309; word_sub stackpointer (word 73747),73747]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73747),73747)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen rnd sk skb M C RND PH PRE MU
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0
                (mld_domain_separation_prefix_length 12 ctxlen 64) PRE /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
               mld_sign_terminates_65 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73747),73747)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73747),73747)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,3309) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s =
                    word(pc + mldsa65_signature_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen rnd sk
                            (mld_sk_rho skb) (mld_sign_declass_65 skb MU RND)
                            mf mc pc (word_sub stackpointer (word 73747))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; ctx,ctxlen; rnd,32; sk,4032;
                         word_sub stackpointer (word 73747),73747;
                         stackpointer,8; word_add stackpointer (word 8),8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                           mldsa65_polyvec_matrix_expand_eager_consts),4;
                         word(pc +
                       mldsa65_prepare_domain_separation_prefix_switch1_table),
                         52;
                         word(pc + rodata_oid_map_0_2),192]
                        [sig,3309; word_sub stackpointer (word 73747),73747]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73747),73747)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
