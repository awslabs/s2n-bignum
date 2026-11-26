(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a pre-hash (HashML-DSA): the statement. This is the code for      *)
(* mldsa44_signature_pre_hash_internal (mld_sign_signature_pre_hash_internal *)
(* in sign.c, an external API function) from mldsa-native's portable C       *)
(* implementation compiled by clang 23 with -O3 and MLD_CONFIG_REDUCE_RAM    *)
(* (see mldsa_native/README.md), which aligns its frame to 32 bytes, returns *)
(* -9 (MLD_ERR_INVALID_ARG) if hashalg is MLD_PREHASH_NONE (0) or if         *)
(* mldsa44_prepare_domain_separation_prefix rejects the context or the pre-  *)
(* hash, and otherwise signs the prefix 1 || ctxlen || ctx || OID || ph,     *)
(* which it builds in a buffer on the stack, as the message with             *)
(* mldsa44_signature_internal. It zeroes the signature on any failure, with  *)
(* memset, which it calls through the PLT, and the prefix with memset in all *)
(* cases, so that the direction flag must be clear, as the ABI requires on   *)
(* entry. It is verified in the whole image (see libmldsa.ml), using the     *)
(* theorems for the callees and the contracts memset_full_contract,          *)
(* memcpy_full_contract and randombytes_safety_contract of                   *)
(* utils/mldsa_native_libc.ml for the C library functions that they and it   *)
(* call, and shown to be constant time and memory safe.                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/prepare_domain_separation_prefix_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa44_signature_pre_hash_internal:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  push    r12
       +0xa  push    rbx
       +0xb  and     rsp, 0xffffffffffffffe0
       +0xf  sub     rsp, 0x160
      +0x16  mov     r12, r9
      +0x19  mov     rbx, rdi
      +0x1c  mov     r9d, DWORD PTR [rbp+0x18]
      +0x20  mov     r14d, 0xfffffff7
      +0x26  test    r9d, r9d
      +0x29  je      join1                                     -----+
      +0x2b  mov     rdi, rsp                                       |
      +0x2e  call    mldsa44_prepare_domain_separation_prefix       |
    after_mldsa44_prepare_domain_separation_prefix:                 |
      +0x33  test    rax, rax                                       |
      +0x36  je      join1                                     ---+ |
      +0x38  xor     r15d, r15d                                   | |
      +0x3b  mov     rsi, rsp                                     | |
      +0x3e  mov     rdi, rbx                                     | |
      +0x41  mov     rdx, rax                                     | |
      +0x44  xor     ecx, ecx                                     | |
      +0x46  xor     r8d, r8d                                     | |
      +0x49  mov     r9, r12                                      | |
      +0x4c  push    0x0                                          | |
      +0x4e  push    QWORD PTR [rbp+0x10]                         | |
      +0x51  call    mldsa44_signature_internal                   | |
    after_mldsa44_signature_internal:                             | |
      +0x56  add     rsp, 0x10                                    | |
      +0x5a  mov     r14d, eax                                    | |
      +0x5d  test    eax, eax                                     | |
      +0x5f  je      join2                                     -+ | |
    join1:                                                      | | |
      +0x61  mov     edx, 0x974                                <--+-+
      +0x66  mov     rdi, rbx                                   |
      +0x69  xor     esi, esi                                   |
      +0x6b  call    memset                                     |
    after_memset_1:                                             |
      +0x70  mov     r15d, r14d                                 |
    join2:                                                      |
      +0x73  mov     rbx, rsp                                  <+
      +0x76  mov     edx, 0x14c
      +0x7b  mov     rdi, rbx
      +0x7e  xor     esi, esi
      +0x80  call    memset
    after_memset_2:
      +0x85  mov     eax, r15d
      +0x88  lea     rsp, [rbp-0x20]
      +0x8c  pop     rbx
      +0x8d  pop     r12
      +0x8f  pop     r14
      +0x91  pop     r15
      +0x93  pop     rbp
      +0x94  xor     ecx, ecx
      +0x96  xor     edi, edi
      +0x98  xor     edx, edx
      +0x9a  xor     esi, esi
      +0x9c  xor     r8d, r8d
      +0x9f  xor     r9d, r9d
    ret:
      +0xa2  ret

    plt_memset:
       +0x0  jmp     QWORD PTR [rip+0x26fc2]
                     // got_memset
       +0x6  push    0x2
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_signature_pre_hash_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The pre- *)
(* hash PH of phlen bytes at ph, the context C of ctxlen bytes at ctx, the   *)
(* 32 bytes RND at rnd, the secret key skb at sk (2560 bytes) and hashalg,   *)
(* of which the code reads the low 32 bits HA, with sk and hashalg, the      *)
(* seventh and eighth arguments, on the stack above the return address as    *)
(* 64-bit words: the result is -9 if HA is 0 or if the prefix is rejected    *)
(* (its length PLEN is 0), with the signature zeroed, and otherwise that of  *)
(* signing the prefix PRE as the message, with MU the mu of signing, and the *)
(* signature mld_sign_sig_44 skb MU RND (zero if signing fails). The         *)
(* function saves RBP, the frame pointer, and four more registers below the  *)
(* return address, lowers RSP by up to 31 bytes to align it to 32 bytes,     *)
(* reserves 352 bytes for the prefix, and then the two arguments of          *)
(* mldsa44_signature_internal on the stack, whose call uses 12078 bytes      *)
(* below them, with its return address: 12525 bytes of stack below the       *)
(* return address in all. The GOT entries of the C library functions and the *)
(* region (ea,el) that they may read are apart from the signature and the    *)
(* stack. The table of 12 pointers to the records of the OIDs at pc +        *)
(* oid_map_ptrs, which the dynamic loader fills in and which is outside the  *)
(* image, is assumed to hold the addresses of the records of                 *)
(* rodata_mld_get_hash_oid87_oid_map, and is apart from the stack and the    *)
(* outputs.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
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
           ==> mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
               mld_sign_terminates_44 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 12525),12525)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 12525),12525)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (word(pc + oid_map_ptrs),96); (ea,el)] /\
          nonoverlapping (sig,2420) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s =
                    word(pc + mldsa44_signature_pre_hash_internal) /\
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
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc + oid_map_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if HA = 0 \/ PLEN = 0 then word 4294967287
                     else if mld_sign_ok_44 skb MU RND then word 0
                     else word 4294967292) /\
                    (!t. t < 2420
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             if HA = 0 \/ PLEN = 0 then word 0
                             else mld_sign_sig_44 skb MU RND t))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 12525),12525)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, hashalg, rho and     *)
(* what the C code declassifies in signing (mld_sign_declass_44), with all   *)
(* accesses within the arguments, the stack, the return address and the      *)
(* arguments above it, the GOT entries, the region (ea,el) that the C        *)
(* library functions may read and the constants of the callees, and the      *)
(* writes within the signature and the stack.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
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
           ==> mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
               mld_sign_terminates_44 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 12525),12525)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 12525),12525)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (word(pc + oid_map_ptrs),96); (ea,el)] /\
          nonoverlapping (sig,2420) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s =
                    word(pc + mldsa44_signature_pre_hash_internal) /\
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
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc + oid_map_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
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
                            mf mc pc (word_sub stackpointer (word 12525))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; ph,phlen; ctx,ctxlen; rnd,32; sk,2560;
                         word_sub stackpointer (word 12525),12525;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa44_poly_challenge_consts),64;
                          word(pc + mldsa44_signature_internal_consts),32;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448;
                          word(pc + oid_map_ptrs),96;
                          word(pc +
                            mldsa44_prepare_domain_separation_prefix_switch1_table),
                          52;
                          word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [sig,2420; word_sub stackpointer (word 12525),12525]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 12525),12525)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
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
           ==> mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
               mld_sign_terminates_44 skb MU RND) /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 12525),12525)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 12525),12525)]
           [(ph,phlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (word(pc + oid_map_ptrs),96); (ea,el)] /\
          nonoverlapping (sig,2420) (stackpointer,8)
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s =
                    word(pc + mldsa44_signature_pre_hash_internal) /\
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
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc + oid_map_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig ph phlen ctx ctxlen rnd sk hashalg
                            (mld_sk_rho skb) (mld_sign_declass_44 skb MU RND)
                            mf mc pc (word_sub stackpointer (word 12525))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; ph,phlen; ctx,ctxlen; rnd,32; sk,2560;
                         word_sub stackpointer (word 12525),12525;
                         stackpointer,8; word_add stackpointer (word 8),16;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa44_poly_challenge_consts),64;
                          word(pc + mldsa44_signature_internal_consts),32;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448;
                          word(pc + oid_map_ptrs),96;
                          word(pc +
                            mldsa44_prepare_domain_separation_prefix_switch1_table),
                          52;
                          word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [sig,2420; word_sub stackpointer (word 12525),12525]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 12525),12525)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
