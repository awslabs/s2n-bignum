(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature with a SHAKE256 pre-hash: the statement. This is    *)
(* the code for mldsa44_verify_pre_hash_shake256                             *)
(* (mld_sign_verify_pre_hash_shake256 in sign.c, an external API function)   *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which hashes the message to 64 bytes with   *)
(* mldsa_shake256 and verifies that pre-hash with                            *)
(* mldsa44_verify_pre_hash_internal and hashalg MLD_PREHASH_SHAKE_256 (12),  *)
(* which it pushes on the stack, and then zeroes the pre-hash. It realigns   *)
(* its stack frame to 32 bytes (utils/mldsa_native_realign.ml). It is        *)
(* verified in the whole image (see libmldsa.ml), using the theorems for the *)
(* callees and the contracts memset_full_contract and memcpy_full_contract   *)
(* of utils/mldsa_native_libc.ml for the C library functions that they call, *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/verify_pre_hash_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_verify_pre_hash_shake256:
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
      +0x2d  mov     r12, rdi
      +0x30  push    r10
      +0x32  push    rbx
      +0x33  lea     rbx, [rbp-0x70]
      +0x37  mov     rdi, rbx
      +0x3a  sub     rsp, 0x40
      +0x3e  call    mldsa_shake256
     after_mldsa_shake256:
      +0x43  sub     rsp, 0x8
      +0x47  mov     r9, r15
      +0x4a  mov     r8, r14
      +0x4d  push    0xc
      +0x4f  mov     rcx, r13
      +0x52  mov     edx, 0x40
      +0x57  mov     rsi, rbx
      +0x5a  mov     rdi, r12
      +0x5d  call    mldsa44_verify_pre_hash_internal
     after_mldsa44_verify_pre_hash_internal:
      +0x62  pxor    xmm0, xmm0
      +0x66  movaps  XMMWORD PTR [rbp-0x70], xmm0
      +0x6a  movaps  XMMWORD PTR [rbp-0x60], xmm0
      +0x6e  movaps  XMMWORD PTR [rbp-0x50], xmm0
      +0x72  movaps  XMMWORD PTR [rbp-0x40], xmm0
      +0x76  pop     rdx
      +0x77  pop     rcx
      +0x78  lea     rsp, [rbp-0x30]
      +0x7c  pop     rbx
      +0x7d  pop     r10
      +0x7f  pop     r12
      +0x81  pop     r13
      +0x83  pop     r14
      +0x85  pop     r15
      +0x87  pop     rbp
      +0x88  lea     rsp, [r10-0x8]
     ret:
      +0x8c  ret
 ***)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_verify_pre_hash_shake256"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (2420 bytes), the message M of mlen bytes at m, the *)
(* context C of ctxlen bytes at ctx and the public key pkb at pk (1312       *)
(* bytes), with PH the 64 bytes of the SHAKE256 pre-hash of M and PRE the    *)
(* prefix 1 || ctxlen || ctx || OID || PH: the result is -9 if ctxlen > 255, *)
(* and otherwise 0 if the signature is accepted for PRE as the message, and  *)
(* -6 if not. The function keeps the stack pointer of the entry in R10,      *)
(* lowers RSP by up to 31 bytes to align it to 32 bytes, copies the return   *)
(* address there and saves RBP, the frame pointer, and six more registers,   *)
(* reserves the stack for the pre-hash, below which the callees use theirs:  *)
(* 30651 bytes of stack below the return address in all. The GOT entries of  *)
(* memset and memcpy and the region (ea,el) that they may read are apart     *)
(* from the stack.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigb pkb M C PH PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(list_of_seq sigb 32))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 30651),30651))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_verify_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                       (mld_verify_mu 1312 pkb 0 0 (ctxlen + 77) PRE)
                     then word 0 else word 4294967290))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 30651),30651)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the signature, the   *)
(* message, the context and the public key, all public, the addresses of     *)
(* memset and memcpy and the stack, with all accesses within the arguments,  *)
(* the stack, the return address, the GOT entries, the region (ea,el) that   *)
(* the C library functions may read and the constants of the callees, and    *)
(* the writes within the stack.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C PH PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(list_of_seq sigb 32))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 30651),30651))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_verify_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                       (mld_verify_mu 1312 pkb 0 0 (ctxlen + 77) PRE)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            mf mc pc (word_sub stackpointer (word 30651))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 30651),30651;
                         stackpointer,8; word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                        mldsa44_prepare_domain_separation_prefix_switch1_table),
                         52;
                         word(pc + rodata_oid_map_0_1),192]
                        [word_sub stackpointer (word 30651),30651]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 30651),30651)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C PH PRE pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          PH = num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64) /\
          PRE = num_of_bytelist
                 (mld_domain_separation_prefix 12
                   (bytelist_of_num ctxlen C) (bytelist_of_num 64 PH)) /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(list_of_seq sigb 32))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 30651),30651))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_memset),8);
               (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_verify_pre_hash_shake256) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(ctx,ctxlen)) s = C /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            mf mc pc (word_sub stackpointer (word 30651))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 30651),30651;
                         stackpointer,8; word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                        mldsa44_prepare_domain_separation_prefix_switch1_table),
                         52;
                         word(pc + rodata_oid_map_0_1),192]
                        [word_sub stackpointer (word 30651),30651]))
               (MAYCHANGE [RSP] ,,
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 30651),30651)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
