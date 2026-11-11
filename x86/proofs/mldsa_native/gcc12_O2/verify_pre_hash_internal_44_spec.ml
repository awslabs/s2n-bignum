(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a pre-hash: the statement. This is the code for  *)
(* mldsa44_verify_pre_hash_internal (mld_sign_verify_pre_hash_internal in    *)
(* sign.c, an external API function) from mldsa-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which returns -9 if hashalg is MLD_PREHASH_NONE (0) or if                 *)
(* mldsa44_prepare_domain_separation_prefix rejects the context or the       *)
(* pre-hash, and otherwise verifies the prefix 1 || ctxlen || ctx || OID ||  *)
(* ph as the message with mldsa44_verify_internal, and zeroes the prefix     *)
(* with a memset that gcc inlines as REP STOSQ, so that the direction flag   *)
(* must be clear, as the ABI requires on entry. It realigns its stack frame  *)
(* to 32 bytes (utils/mldsa_native_realign.ml). It is verified in the whole  *)
(* image (see libmldsa.ml), using the theorems for the callees and the       *)
(* contracts memset_full_contract and memcpy_full_contract of                *)
(* utils/mldsa_native_libc.ml for the C library functions that they call,    *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/prepare_domain_separation_prefix_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_verify_pre_hash_internal:
       +0x0  lea     r10, [rsp+0x8]
       +0x5  and     rsp, 0xffffffffffffffe0
       +0x9  push    QWORD PTR [r10-0x8]
       +0xd  push    rbp
       +0xe  mov     rbp, rsp
      +0x11  push    r13
      +0x13  mov     r13, r9
      +0x16  push    r12
      +0x18  push    r10
      +0x1a  push    rbx
      +0x1b  sub     rsp, 0x170
      +0x22  mov     r9d, DWORD PTR [r10]
      +0x25  test    r9d, r9d
      +0x28  je      join2
      +0x2a  lea     rbx, [rbp-0x190]
      +0x31  mov     r12, rdi
      +0x34  mov     rdi, rbx
      +0x37  call    mldsa44_prepare_domain_separation_prefix
     after_mldsa44_prepare_domain_separation_prefix:
      +0x3c  mov     rdx, rax
      +0x3f  test    rax, rax
      +0x42  je      join3
      +0x44  sub     rsp, 0x8
      +0x48  xor     ecx, ecx
      +0x4a  mov     r9, r13
      +0x4d  xor     r8d, r8d
      +0x50  push    0x0
      +0x52  mov     rsi, rbx
      +0x55  mov     rdi, r12
      +0x58  call    mldsa44_verify_internal
     after_mldsa44_verify_internal:
      +0x5d  mov     edx, eax
      +0x5f  pop     rax
      +0x60  pop     rcx
     join1:
      +0x61  xor     eax, eax
      +0x63  mov     rdi, rbx
      +0x66  mov     ecx, 0x29
      +0x6b  rep stos QWORD PTR es:[rdi], rax
      +0x6e  mov     DWORD PTR [rdi], 0x0
      +0x74  lea     rsp, [rbp-0x20]
      +0x78  mov     eax, edx
      +0x7a  pop     rbx
      +0x7b  pop     r10
      +0x7d  pop     r12
      +0x7f  pop     r13
      +0x81  pop     rbp
      +0x82  lea     rsp, [r10-0x8]
     ret:
      +0x86  ret
      +0x87  nop     WORD PTR [rax+rax*1+0x0]
     join2:
      +0x90  lea     rbx, [rbp-0x190]
     join3:
      +0x97  mov     edx, 0xfffffff7
      +0x9c  jmp     join1
 ***)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_verify_pre_hash_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (2420 bytes), the pre-hash PH of phlen bytes at ph, *)
(* the context C of ctxlen bytes at ctx, the public key pkb at pk (1312      *)
(* bytes) and hashalg, the seventh argument, on the stack above the return   *)
(* address as a 64-bit word whose low 32 bits HA the code reads: the result  *)
(* is -9 if HA is 0 or if the prefix is rejected (its length PLEN is 0), and *)
(* otherwise 0 if the signature is accepted for the prefix PRE as the        *)
(* message, and -6 if not. The function keeps the stack pointer of the entry *)
(* in R10, lowers RSP by up to 31 bytes to align it to 32 bytes, copies the  *)
(* return address there and saves RBP, the frame pointer, and four more      *)
(* registers, reserves the stack for the prefix, below which the callees use *)
(* theirs: 30468 bytes of stack below the return address in all. The GOT     *)
(* entries of memset and memcpy and the region (ea,el) that they may read    *)
(* are apart from the stack.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig ph phlen ctx ctxlen pk hashalg sigb pkb PH C HA PLEN
                 PRE pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
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
          ALL (nonoverlapping (word_sub stackpointer (word 30468),30468))
              [(sig,2420); (ph,phlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_verify_pre_hash_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    hashalg /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if HA = 0 \/ PLEN = 0 then word 4294967287
                     else if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                       (mld_verify_mu 1312 pkb 0 0 PLEN PRE)
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 30468),30468)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, hashalg, the         *)
(* signature, the pre-hash, the context and the public key, all public, the  *)
(* addresses of memset and memcpy and the stack, with all accesses within    *)
(* the arguments, the stack, the return address and hashalg above it, the    *)
(* GOT entries, the region (ea,el) that the C library functions may read and *)
(* the constants of the callees, and the writes within the stack.            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig ph phlen ctx ctxlen pk hashalg sigb pkb PH C HA PLEN
                 PRE pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
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
          ALL (nonoverlapping (word_sub stackpointer (word 30468),30468))
              [(sig,2420); (ph,phlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_verify_pre_hash_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    hashalg /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
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
                            pkb PH C mf mc pc
                            (word_sub stackpointer (word 30468))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; ph,phlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 30468),30468;
                         stackpointer,8; word_add stackpointer (word 8),8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                        mldsa44_prepare_domain_separation_prefix_switch1_table),
                         52;
                         word(pc + rodata_oid_map_0_1),192]
                        [word_sub stackpointer (word 30468),30468]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 30468),30468)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig ph phlen ctx ctxlen pk hashalg sigb pkb PH C HA PLEN
                 PRE pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
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
          ALL (nonoverlapping (word_sub stackpointer (word 30468),30468))
              [(sig,2420); (ph,phlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_verify_pre_hash_internal) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; ph; word phlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word_add stackpointer (word 8))) s =
                    hashalg /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(ph,phlen)) s = PH /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig ph phlen ctx ctxlen pk hashalg sigb
                            pkb PH C mf mc pc
                            (word_sub stackpointer (word 30468))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; ph,phlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 30468),30468;
                         stackpointer,8; word_add stackpointer (word 8),8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                        mldsa44_prepare_domain_separation_prefix_switch1_table),
                         52;
                         word(pc + rodata_oid_map_0_1),192]
                        [word_sub stackpointer (word 30468),30468]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 30468),30468)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
