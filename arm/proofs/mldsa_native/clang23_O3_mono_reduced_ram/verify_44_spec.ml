(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a message (pure ML-DSA): the statement. This is  *)
(* the code for mldsa44_verify (mld_sign_verify in sign.c, an external API   *)
(* function) from mldsa-native's portable C implementation compiled by clang *)
(* 23 with -O3 as one translation unit with MLD_CONFIG_REDUCE_RAM (see       *)
(* mldsa_native/README.md), which builds the prefix 0 || ctxlen || ctx of    *)
(* pure ML-DSA in a buffer on the stack, with two byte stores and memcpy,    *)
(* returning -9 if ctxlen > 255, and otherwise verifies with                 *)
(* mldsa44_verify_internal, and zeroes the buffer with stores of zero        *)
(* vectors. It is verified in the whole image (see libmldsa.ml), using the   *)
(* theorems for the callees and the contracts memset_ret_full_contract,      *)
(* memcpy_full_contract of the C library functions, and shown to be constant *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/prepare_domain_separation_prefix_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stubs:

    mldsa44_verify:
       +0x0: stp     x29, x30, [sp, #-64]!
       +0x4: stp     x28, x23, [sp, #16]
       +0x8: stp     x22, x21, [sp, #32]
       +0xc: stp     x20, x19, [sp, #48]
      +0x10: mov     x29, sp
      +0x14: sub     x9, sp, #0x160
      +0x18: and     sp, x9, #0xffffffffffffffe0
      +0x1c: adrp    x8, <page>
      +0x20: cmp     x4, #0xff
      +0x24: ldr     x8, [x8, #4088]
      +0x28: ldr     x8, [x8]
      +0x2c: str     x8, [sp, #344]
      +0x30: b.ls    <mldsa44_verify+0x3c>
      +0x34: mov     w0, #0xfffffff7
      +0x38: b       <mldsa44_verify+0x94>
      +0x3c: strb    wzr, [sp]
      +0x40: strb    w4, [sp, #1]
      +0x44: cbz     x4, <mldsa44_verify+0x84>
      +0x48: mov     x8, sp
      +0x4c: mov     x19, x0
      +0x50: mov     x20, x1
      +0x54: orr     x0, x8, #0x2
      +0x58: mov     x1, x3
      +0x5c: mov     x21, x2
      +0x60: mov     x2, x4
      +0x64: mov     x22, x5
      +0x68: mov     x23, x4
      +0x6c: bl      <memcpy>
      +0x70: mov     x0, x19
      +0x74: mov     x1, x20
      +0x78: mov     x4, x23
      +0x7c: mov     x2, x21
      +0x80: mov     x5, x22
      +0x84: mov     x3, sp
      +0x88: add     x4, x4, #0x2
      +0x8c: mov     w6, wzr
      +0x90: bl      <mldsa44_verify_internal>
      +0x94: movi    v0.2d, #0x0
      +0x98: mov     x8, sp
      +0x9c: add     x9, x8, #0x13c
      +0xa0: str     q0, [x9]
      +0xa4: stp     q0, q0, [sp]
      +0xa8: stp     q0, q0, [sp, #32]
      +0xac: stp     q0, q0, [sp, #64]
      +0xb0: stp     q0, q0, [sp, #96]
      +0xb4: stp     q0, q0, [sp, #128]
      +0xb8: stp     q0, q0, [sp, #160]
      +0xbc: stp     q0, q0, [sp, #192]
      +0xc0: stp     q0, q0, [sp, #224]
      +0xc4: stp     q0, q0, [sp, #256]
      +0xc8: stp     q0, q0, [sp, #288]
      +0xcc: adrp    x8, <page>
      +0xd0: ldr     x8, [x8, #4088]
      +0xd4: ldr     x9, [sp, #344]
      +0xd8: ldr     x8, [x8]
      +0xdc: cmp     x8, x9
      +0xe0: b.ne    <mldsa44_verify+0x11c>
      +0xe4: mov     sp, x29
      +0xe8: ldp     x20, x19, [sp, #48]
      +0xec: ldp     x22, x21, [sp, #32]
      +0xf0: ldp     x28, x23, [sp, #16]
      +0xf4: ldp     x29, x30, [sp], #64
      +0xf8: mov     x1, #0x0
      +0xfc: mov     x2, #0x0
     +0x100: mov     x3, #0x0
     +0x104: mov     x4, #0x0
     +0x108: mov     x5, #0x0
     +0x10c: mov     x6, #0x0
     +0x110: mov     x8, #0x0
     +0x114: mov     x9, #0x0
     +0x118: ret     
     +0x11c: bl      <__stack_chk_fail>

    memcpy@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4048]
       +0x8: add     x16, x16, #0xfd0
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_VERIFY_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_verify";
    layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (2420 bytes), the message M of mlen bytes at m, the *)
(* context C of ctxlen bytes at ctx and the public key pkb at pk (1312       *)
(* bytes): the result is -9 if ctxlen > 255, and otherwise 0 if the          *)
(* signature is accepted for the message with the prefix of pure ML-DSA, and *)
(* -6 if not. The stack is the 11904 bytes below the stack pointer: the      *)
(* frame of the function, of up to 432 bytes, and the stacks of its callees. *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigb pkb M C guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(list_of_seq sigb 32))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 11904),11904))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_verify) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
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
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                       (mld_verify_mu 1312 pkb (2 + ctxlen)
                         (num_of_bytelist
                           (mld_domain_separation_prefix 0
                             (bytelist_of_num ctxlen C) []))
                         mlen M)
                     then word 0 else word 4294967290))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11904),11904)])`;;

let MLDSA_NATIVE_VERIFY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the signature, the   *)
(* message, the context and the public key, all public, with all accesses    *)
(* within the arguments, the stack, the GOT entries and the stack guard, the *)
(* region (ea,el) that the C library functions may read and the constants of *)
(* the callees, and the writes within the outputs and the stack.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(list_of_seq sigb 32))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 11904),11904))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_verify) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
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
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if 255 < ctxlen then word 4294967287
                     else if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                       (mld_verify_mu 1312 pkb (2 + ctxlen)
                         (num_of_bytelist
                           (mld_domain_separation_prefix 0
                             (bytelist_of_num ctxlen C) []))
                         mlen M)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            guard mf mc pc
                            (word_sub stackpointer (word 11904))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 11904),11904;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa44_verify_internal_const1),16;
                         word(pc + mldsa44_verify_internal_const2),16;
                         word(pc + mldsa44_verify_internal_const3),8]
                        [word_sub stackpointer (word 11904),11904]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11904),11904)])`;;

let MLDSA_NATIVE_VERIFY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mlen < 2 EXP 64 /\ ctxlen < 2 EXP 64 /\
          (ctxlen <= 255
           ==> mld_matrix_terminates 4 4
                (num_of_bytelist(list_of_seq pkb 32)) /\
               mld_poly_challenge_terminates 39 32
                (num_of_bytelist(list_of_seq sigb 32))) /\
          ALL (nonoverlapping (word_sub stackpointer (word 11904),11904))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_verify) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; ctx; word ctxlen; pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
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
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            guard mf mc pc
                            (word_sub stackpointer (word 11904))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 11904),11904;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa44_verify_internal_const1),16;
                         word(pc + mldsa44_verify_internal_const2),16;
                         word(pc + mldsa44_verify_internal_const3),8]
                        [word_sub stackpointer (word 11904),11904]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11904),11904)])`;;

let MLDSA_NATIVE_VERIFY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
