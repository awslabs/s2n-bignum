(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a pre-hash: the statement. This is the code for  *)
(* mldsa44_verify_pre_hash_internal (mld_sign_verify_pre_hash_internal in    *)
(* sign.c, an external API function) from mldsa-native's portable C          *)
(* implementation compiled by clang 23 with -O3 and MLD_CONFIG_REDUCE_RAM    *)
(* (see mldsa_native/README.md), which returns -9 if hashalg is              *)
(* MLD_PREHASH_NONE (0) or if mldsa44_prepare_domain_separation_prefix       *)
(* rejects the context or the pre-hash, and otherwise verifies the prefix 1  *)
(* || ctxlen || ctx || OID || ph as the message with                         *)
(* mldsa44_verify_internal, and zeroes the prefix with memset, which it      *)
(* calls through the PLT, in both cases. It realigns its stack frame to 32   *)
(* bytes (utils/mldsa_native_realign.ml). It is verified in the whole image  *)
(* (see libmldsa.ml), using the theorems for the callees and the contracts   *)
(* memset_full_contract and memcpy_full_contract of                          *)
(* utils/mldsa_native_libc.ml for the C library functions that they and it   *)
(* call, and shown to be constant time and memory safe.                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/prepare_domain_separation_prefix_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa44_verify_pre_hash_internal:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  push    rbx
       +0x9  and     rsp, 0xffffffffffffffe0
       +0xd  sub     rsp, 0x180
      +0x14  mov     r14, r9
      +0x17  mov     r9d, DWORD PTR [rbp+0x10]
      +0x1b  mov     ebx, 0xfffffff7
      +0x20  test    r9d, r9d
      +0x23  je      join1                                     ---+
      +0x25  mov     r15, rdi                                     |
      +0x28  lea     rdi, [rsp+0x20]                              |
      +0x2d  call    mldsa44_prepare_domain_separation_prefix     |
    after_mldsa44_prepare_domain_separation_prefix:               |
      +0x32  test    rax, rax                                     |
      +0x35  je      join1                                     -+ |
      +0x37  mov     DWORD PTR [rsp], 0x0                       | |
      +0x3e  lea     rsi, [rsp+0x20]                            | |
      +0x43  mov     rdi, r15                                   | |
      +0x46  mov     rdx, rax                                   | |
      +0x49  xor     ecx, ecx                                   | |
      +0x4b  xor     r8d, r8d                                   | |
      +0x4e  mov     r9, r14                                    | |
      +0x51  call    mldsa44_verify_internal                    | |
    after_mldsa44_verify_internal:                              | |
      +0x56  mov     ebx, eax                                   | |
    join1:                                                      | |
      +0x58  lea     r14, [rsp+0x20]                           <+-+
      +0x5d  mov     edx, 0x14c
      +0x62  mov     rdi, r14
      +0x65  xor     esi, esi
      +0x67  call    memset
    after_memset:
      +0x6c  mov     eax, ebx
      +0x6e  lea     rsp, [rbp-0x18]
      +0x72  pop     rbx
      +0x73  pop     r14
      +0x75  pop     r15
      +0x77  pop     rbp
      +0x78  xor     ecx, ecx
      +0x7a  xor     edi, edi
      +0x7c  xor     edx, edx
      +0x7e  xor     esi, esi
      +0x80  xor     r8d, r8d
      +0x83  xor     r9d, r9d
    ret:
      +0x86  ret

    plt_memset:
       +0x0  jmp     QWORD PTR [rip+0x26fc2]
                     // got_memset
       +0x6  push    0x2
       +0xb  jmp     <.plt>
 ***)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_verify_pre_hash_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (2420 bytes), the pre-hash PH of phlen bytes at ph, *)
(* the context C of ctxlen bytes at ctx, the public key pkb at pk (1312      *)
(* bytes) and hashalg, the seventh argument, on the stack above the return   *)
(* address as a 64-bit word whose low 32 bits HA the code reads: the result  *)
(* is -9 if HA is 0 or if the prefix is rejected (its length PLEN is 0), and *)
(* otherwise 0 if the signature is accepted for the prefix PRE as the        *)
(* message, and -6 if not. The function saves RBP, the frame pointer, and    *)
(* three more registers below the return address, lowers RSP by up to 31     *)
(* bytes to align it to 32 bytes, reserves 384 bytes for the prefix and ext, *)
(* the seventh argument of mldsa44_verify_internal, below which that         *)
(* function uses 10949 bytes with its return address: 11404 bytes of stack   *)
(* below the return address in all. The GOT entries of memcpy and memset and *)
(* the region (ea,el) that they may read are apart from the stack. The table *)
(* of 12 pointers to the records of the OIDs at pc + oid_map_ptrs, which the *)
(* dynamic loader fills in and which is outside the image, is assumed to     *)
(* hold the addresses of the records of rodata_mld_get_hash_oid87_oid_map,   *)
(* and is apart from the stack and the outputs.                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 11404),11404))
              [(sig,2420); (ph,phlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (word(pc + oid_map_ptrs),96); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
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
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc + oid_map_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
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
                 [memory :> bytes(word_sub stackpointer (word 11404),11404)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, hashalg, the         *)
(* signature, the pre-hash, the context and the public key, all public, the  *)
(* addresses of memset and memcpy and the stack, with all accesses within    *)
(* the arguments, the stack, the return address and hashalg above it, the    *)
(* GOT entries, the region (ea,el) that the C library functions may read and *)
(* the constants of the callees, and the writes within the stack.            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 11404),11404))
              [(sig,2420); (ph,phlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (word(pc + oid_map_ptrs),96); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
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
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc + oid_map_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
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
                            (word_sub stackpointer (word 11404))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; ph,phlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 11404),11404;
                         stackpointer,8; word_add stackpointer (word 8),8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa44_poly_challenge_consts),64;
                          word(pc + mldsa44_verify_internal_const1),16;
                          word(pc + mldsa44_verify_internal_const2),16;
                          word(pc + mldsa44_verify_internal_const3),8;
                          word(pc + mldsa44_verify_internal_const4),8;
                          word(pc + mld_compute_pack_t0_t144_const1),16;
                          word(pc + mld_compute_pack_t0_t144_const2),16;
                          word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448;
                          word(pc + oid_map_ptrs),96;
                          word(pc +
                            mldsa44_prepare_domain_separation_prefix_switch1_table),
                          52;
                          word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [word_sub stackpointer (word 11404),11404]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11404),11404)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 11404),11404))
              [(sig,2420); (ph,phlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (word(pc + oid_map_ptrs),96); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
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
                    (!k. k < 12
                         ==> read (memory :> bytes64(word(pc + oid_map_ptrs + 8 * k))) s =
                             word(pc + rodata_mld_get_hash_oid87_oid_map + 16 * k)) /\
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
                            (word_sub stackpointer (word 11404))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; ph,phlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 11404),11404;
                         stackpointer,8; word_add stackpointer (word 8),8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                          word(pc + rodata_mld_KeccakF_RoundConstants),192;
                          word(pc + rodata_mld_zetas),1024;
                          word(pc + mldsa44_poly_challenge_consts),64;
                          word(pc + mldsa44_verify_internal_const1),16;
                          word(pc + mldsa44_verify_internal_const2),16;
                          word(pc + mldsa44_verify_internal_const3),8;
                          word(pc + mldsa44_verify_internal_const4),8;
                          word(pc + mld_compute_pack_t0_t144_const1),16;
                          word(pc + mld_compute_pack_t0_t144_const2),16;
                          word(pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy_consts),32;
                          word(pc + mldsa_poly_ntt_consts),256;
                          word(pc + mldsa_poly_invntt_tomont_consts),448;
                          word(pc + oid_map_ptrs),96;
                          word(pc +
                            mldsa44_prepare_domain_separation_prefix_switch1_table),
                          52;
                          word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [word_sub stackpointer (word 11404),11404]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11404),11404)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
