(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a pre-hash (HashML-DSA): the statement. This is the code for      *)
(* mldsa87_signature_pre_hash_internal (mld_sign_signature_pre_hash_internal *)
(* in sign.c, an external API function) from mldsa-native's portable C       *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which aligns its frame to 32 bytes, returns -9 (MLD_ERR_INVALID_ARG) if   *)
(* hashalg is MLD_PREHASH_NONE (0) or if                                     *)
(* mldsa87_prepare_domain_separation_prefix rejects the context or the       *)
(* pre-hash, and otherwise signs the prefix 1 || ctxlen || ctx || OID || ph, *)
(* which it builds in a buffer on the stack, as the message with             *)
(* mldsa87_signature_internal. It zeroes the signature on any failure, with  *)
(* a memset that gcc inlines as quadword stores and REP STOSQ, and the       *)
(* prefix with REP STOSQ, so that the direction flag must be clear, as the   *)
(* ABI requires on entry. It is verified in the whole image (see             *)
(* libmldsa.ml), using the theorems for the callees and the contracts        *)
(* memset_full_contract and memcpy_full_contract of                          *)
(* utils/mldsa_native_libc.ml for the C library functions that they call,    *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/prepare_domain_separation_prefix_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/signature_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_signature_pre_hash_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r14
      +0x13  push    r13
      +0x15  mov     r13, r9
      +0x18  push    r12
      +0x1a  lea     r12, [rbp-0x190]
      +0x21  push    r10
      +0x23  push    rbx
      +0x24  mov     rbx, rdi
      +0x27  sub     rsp, 0x168
      +0x2e  mov     r9d, DWORD PTR [r10+0x8]
      +0x32  mov     r14, QWORD PTR [r10]
      +0x35  test    r9d, r9d
      +0x38  jne     join4
     join1:
      +0x3a  mov     edx, 0xfffffff7
     join2:
      +0x3f  lea     rdi, [rbx+0x8]
      +0x43  mov     rcx, rbx
      +0x46  xor     eax, eax
      +0x48  mov     QWORD PTR [rbx], 0x0
      +0x4f  mov     QWORD PTR [rbx+0x120b], 0x0
      +0x5a  and     rdi, 0xfffffffffffffff8
      +0x5e  sub     rcx, rdi
      +0x61  add     ecx, 0x1213
      +0x67  shr     ecx, 0x3
      +0x6a  rep stos QWORD PTR es:[rdi], rax
     join3:
      +0x6d  xor     eax, eax
      +0x6f  mov     rdi, r12
      +0x72  mov     ecx, 0x29
      +0x77  rep stos QWORD PTR es:[rdi], rax
      +0x7a  mov     DWORD PTR [rdi], 0x0
      +0x80  lea     rsp, [rbp-0x28]
      +0x84  mov     eax, edx
      +0x86  pop     rbx
      +0x87  pop     r10
      +0x89  pop     r12
      +0x8b  pop     r13
      +0x8d  pop     r14
      +0x8f  pop     rbp
      +0x90  lea     rsp, [r10-0x8]
     ret:
      +0x94  ret
      +0x95  nop     DWORD PTR [rax]
     join4:
      +0x98  mov     rdi, r12
      +0x9b  call    mldsa87_prepare_domain_separation_prefix
     after_mldsa87_prepare_domain_separation_prefix:
      +0xa0  test    rax, rax
      +0xa3  je      join1
      +0xa5  push    0x0
      +0xa7  xor     ecx, ecx
      +0xa9  mov     rdx, rax
      +0xac  mov     r9, r13
      +0xaf  push    r14
      +0xb1  xor     r8d, r8d
      +0xb4  mov     rsi, r12
      +0xb7  mov     rdi, rbx
      +0xba  call    mldsa87_signature_internal
     after_mldsa87_signature_internal:
      +0xbf  mov     edx, eax
      +0xc1  pop     rax
      +0xc2  pop     rcx
      +0xc3  test    edx, edx
      +0xc5  je      join3
      +0xc7  jmp     join2
 ***)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_signature_pre_hash_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* pre-hash PH of phlen bytes at ph, the context C of ctxlen bytes at ctx,   *)
(* the 32 bytes RND at rnd, the secret key skb at sk (4896 bytes) and        *)
(* hashalg, of which the code reads the low 32 bits HA, with sk and hashalg, *)
(* the seventh and eighth arguments, on the stack above the return address   *)
(* as 64-bit words: the result is -9 if HA is 0 or if the prefix is rejected *)
(* (its length PLEN is 0), with the signature zeroed, and otherwise that of  *)
(* signing the prefix PRE as the message, with MU the mu of signing, and the *)
(* signature mld_sign_sig_87 skb MU RND (zero if signing fails). The         *)
(* function keeps the stack pointer of the entry in R10, lowers RSP by up to *)
(* 31 bytes to align it to 32 bytes, copies the return address there and     *)
(* saves RBP, the frame pointer, and five more registers, and reserves the   *)
(* stack for the prefix and the two arguments of mldsa87_signature_internal  *)
(* on the stack, whose call uses 112229 bytes below them, with its return    *)
(* address: 112692 bytes of stack below the return address in all. The GOT   *)
(* entries of memset and memcpy and the region (ea,el) that they may read    *)
(* are apart from the signature and the stack.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig ph phlen ctx ctxlen rnd sk hashalg skb PH C RND HA
                 PLEN PRE MU pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0 PLEN PRE /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
               mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112692),112692)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112692),112692)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s =
                    word(pc + mldsa87_signature_pre_hash_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen;
                                 rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    read (memory :> bytes64(word_add stackpointer (word 16)))
                         s = hashalg /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if HA = 0 \/ PLEN = 0 then word 4294967287
                     else if mld_sign_ok_87 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 4627
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if HA = 0 \/ PLEN = 0 then word 0
                             else mld_sign_sig_87 skb MU RND t))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112692),
                                  112692)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, hashalg, rho and     *)
(* what the C code declassifies in signing (mld_sign_declass_87), with all   *)
(* accesses within the arguments, the stack, the return address and the      *)
(* arguments above it, the GOT entries, the region (ea,el) that the C        *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the signature and the stack.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig ph phlen ctx ctxlen rnd sk hashalg skb PH C RND HA
                 PLEN PRE MU pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0 PLEN PRE /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
               mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112692),112692)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112692),112692)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s =
                    word(pc + mldsa87_signature_pre_hash_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen;
                                 rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    read (memory :> bytes64(word_add stackpointer (word 16)))
                         s = hashalg /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if HA = 0 \/ PLEN = 0 then word 4294967287
                     else if mld_sign_ok_87 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 4627
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if HA = 0 \/ PLEN = 0 then word 0
                             else mld_sign_sig_87 skb MU RND t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig ph phlen ctx ctxlen rnd sk hashalg
                            (mld_sk_rho skb) (mld_sign_declass_87 skb MU RND)
                            mf mc pc (word_sub stackpointer (word 112692))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; ph,phlen; ctx,ctxlen; rnd,32; sk,4896;
                         word_sub stackpointer (word 112692),112692;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                       mldsa87_prepare_domain_separation_prefix_switch1_table),
                         52;
                         word(pc + rodata_oid_map_0_3),192]
                        [sig,4627; word_sub stackpointer (word 112692),112692]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112692),
                                  112692)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig ph phlen ctx ctxlen rnd sk hashalg skb PH C RND HA
                 PLEN PRE MU pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          phlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          HA = val(word_zx hashalg:int32) /\
          PLEN = mld_domain_separation_prefix_length HA ctxlen phlen /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix HA
                   (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH)) /\
          MU = mld_sign_mu (\j. skb(64 + j)) 0 0 PLEN PRE /\
          (~(HA = 0) /\ ~(PLEN = 0)
           ==> mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
               mld_sign_terminates_87 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112692),112692)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112692),112692)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)] /\
          nonoverlapping (sig,4627) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s =
                    word(pc + mldsa87_signature_pre_hash_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen;
                                 rnd] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8)))
                         s = sk /\
                    read (memory :> bytes64(word_add stackpointer (word 16)))
                         s = hashalg /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig ph phlen ctx ctxlen rnd sk hashalg
                            (mld_sk_rho skb) (mld_sign_declass_87 skb MU RND)
                            mf mc pc (word_sub stackpointer (word 112692))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; ph,phlen; ctx,ctxlen; rnd,32; sk,4896;
                         word_sub stackpointer (word 112692),112692;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                       mldsa87_prepare_domain_separation_prefix_switch1_table),
                         52;
                         word(pc + rodata_oid_map_0_3),192]
                        [sig,4627; word_sub stackpointer (word 112692),112692]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112692),
                                  112692)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
