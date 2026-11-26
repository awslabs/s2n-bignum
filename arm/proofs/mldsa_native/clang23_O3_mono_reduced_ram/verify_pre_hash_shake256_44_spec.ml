(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature with a SHAKE256 pre-hash: the statement. This is    *)
(* the code for mldsa44_verify_pre_hash_shake256                             *)
(* (mld_sign_verify_pre_hash_shake256 in sign.c, an external API function)   *)
(* from mldsa-native's portable C implementation compiled by clang 23 with   *)
(* -O3 as one translation unit with MLD_CONFIG_REDUCE_RAM (see               *)
(* mldsa_native/README.md). It has inlined mldsa_shake256, which absorbs the *)
(* message into a zero Keccak state (a loop over the blocks of 136 bytes     *)
(* with a call of mldsa_keccakf1600_permute, then the XOR of the rest),      *)
(* pads, calls mldsa_keccakf1600_permute and copies the first 64 bytes of    *)
(* the state as the pre-hash. It builds the prefix 1 || ctxlen || ctx || OID *)
(* || PH of HashML-DSA with hashalg MLD_PREHASH_SHAKE_256 (12) in a buffer   *)
(* on the stack, with memcpy for the context and stores for the OID,         *)
(* verifies it with mldsa44_verify_internal, and zeroes the pre-hash and the *)
(* buffer with stores of zero vectors. It is verified in the whole image     *)
(* (see libmldsa.ml), using the theorems for the callees and the contracts   *)
(* memset_ret_full_contract, memcpy_full_contract of the C library           *)
(* functions, and shown to be constant time and memory safe.                 *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_pre_hash_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_verify_pre_hash_shake256:
       +0x0: stp     x29, x30, [sp, #-80]!
       +0x4: str     x28, [sp, #16]
       +0x8: stp     x24, x23, [sp, #32]
       +0xc: stp     x22, x21, [sp, #48]
      +0x10: stp     x20, x19, [sp, #64]
      +0x14: mov     x29, sp
      +0x18: sub     x9, sp, #0x1b0
      +0x1c: and     sp, x9, #0xffffffffffffffe0
      +0x20: adrp    x8, <page>
      +0x24: movi    v0.2d, #0x0
      +0x28: mov     x19, x5
      +0x2c: ldr     x8, [x8, #4088]
      +0x30: mov     x20, x4
      +0x34: mov     x22, x3
      +0x38: mov     x23, x2
      +0x3c: mov     x24, x1
      +0x40: mov     x21, x0
      +0x44: ldr     x8, [x8]
      +0x48: cmp     x2, #0x88
      +0x4c: str     x8, [sp, #424]
      +0x50: stur    q0, [sp, #252]
      +0x54: stp     q0, q0, [sp, #64]
      +0x58: stp     q0, q0, [sp, #96]
      +0x5c: stp     q0, q0, [sp, #128]
      +0x60: stp     q0, q0, [sp, #160]
      +0x64: stp     q0, q0, [sp, #192]
      +0x68: stp     q0, q0, [sp, #224]
      +0x6c: b.cc    <mldsa44_verify_pre_hash_shake256+0x138>
      +0x70: ldp     d0, d3, [sp, #64]
      +0x74: add     x0, sp, #0x40
      +0x78: ldp     d1, d2, [x24]
      +0x7c: sub     x23, x23, #0x88
      +0x80: ldp     d6, d7, [sp, #96]
      +0x84: ldp     d16, d17, [sp, #112]
      +0x88: eor     v0.8b, v0.8b, v1.8b
      +0x8c: eor     v1.8b, v3.8b, v2.8b
      +0x90: ldp     d4, d2, [x24, #16]
      +0x94: ldp     d5, d3, [sp, #80]
      +0x98: stp     d0, d1, [sp, #64]
      +0x9c: eor     v4.8b, v5.8b, v4.8b
      +0xa0: eor     v2.8b, v3.8b, v2.8b
      +0xa4: ldp     d5, d3, [x24, #32]
      +0xa8: stp     d4, d2, [sp, #80]
      +0xac: ldp     d1, d2, [x24, #80]
      +0xb0: eor     v5.8b, v6.8b, v5.8b
      +0xb4: eor     v3.8b, v7.8b, v3.8b
      +0xb8: ldp     d6, d7, [x24, #48]
      +0xbc: stp     d5, d3, [sp, #96]
      +0xc0: ldp     d3, d5, [x24, #96]
      +0xc4: eor     v6.8b, v16.8b, v6.8b
      +0xc8: eor     v7.8b, v17.8b, v7.8b
      +0xcc: ldp     d16, d0, [x24, #64]
      +0xd0: ldp     d18, d17, [sp, #128]
      +0xd4: stp     d6, d7, [sp, #112]
      +0xd8: eor     v0.8b, v17.8b, v0.8b
      +0xdc: ldp     d4, d17, [sp, #144]
      +0xe0: eor     v16.8b, v18.8b, v16.8b
      +0xe4: eor     v1.8b, v4.8b, v1.8b
      +0xe8: ldp     d4, d6, [sp, #160]
      +0xec: eor     v2.8b, v17.8b, v2.8b
      +0xf0: stp     d16, d0, [sp, #128]
      +0xf4: eor     v3.8b, v4.8b, v3.8b
      +0xf8: ldp     d4, d0, [x24, #112]
      +0xfc: eor     v5.8b, v6.8b, v5.8b
     +0x100: ldp     d7, d6, [sp, #176]
     +0x104: stp     d1, d2, [sp, #144]
     +0x108: ldr     d1, [x24, #128]
     +0x10c: ldr     d2, [sp, #192]
     +0x110: add     x24, x24, #0x88
     +0x114: eor     v4.8b, v7.8b, v4.8b
     +0x118: eor     v0.8b, v6.8b, v0.8b
     +0x11c: eor     v1.8b, v2.8b, v1.8b
     +0x120: stp     d3, d5, [sp, #160]
     +0x124: stp     d4, d0, [sp, #176]
     +0x128: str     d1, [sp, #192]
     +0x12c: bl      <mldsa_keccakf1600_permute>
     +0x130: cmp     x23, #0x87
     +0x134: b.hi    <mldsa44_verify_pre_hash_shake256+0x70>
     +0x138: cbz     x23, <mldsa44_verify_pre_hash_shake256+0x188>
     +0x13c: cmp     x23, #0x8
     +0x140: b.cc    <mldsa44_verify_pre_hash_shake256+0x15c>
     +0x144: add     x8, sp, #0x40
     +0x148: add     x10, x24, x23
     +0x14c: add     x9, x8, x23
     +0x150: cmp     x24, x9
     +0x154: ccmp    x8, x10, #0x2, cc
     +0x158: b.cs    <mldsa44_verify_pre_hash_shake256+0x318>
     +0x15c: mov     x8, xzr
     +0x160: add     x10, sp, #0x40
     +0x164: sub     x9, x23, x8
     +0x168: add     x10, x10, x8
     +0x16c: add     x8, x24, x8
     +0x170: ldrb    w11, [x8], #1
     +0x174: ldrb    w12, [x10]
     +0x178: subs    x9, x9, #0x1
     +0x17c: eor     w11, w12, w11
     +0x180: strb    w11, [x10], #1
     +0x184: b.ne    <mldsa44_verify_pre_hash_shake256+0x170>
     +0x188: str     w23, [sp, #264]
     +0x18c: add     x24, sp, #0x40
     +0x190: mov     w9, #0x88
     +0x194: ldrb    w8, [x24, x23]
     +0x198: add     x0, sp, #0x40
     +0x19c: eor     w8, w8, #0x1f
     +0x1a0: strb    w8, [x24, x23]
     +0x1a4: ldrb    w8, [sp, #199]
     +0x1a8: str     w9, [sp, #264]
     +0x1ac: eor     w8, w8, #0x80
     +0x1b0: strb    w8, [sp, #199]
     +0x1b4: bl      <mldsa_keccakf1600_permute>
     +0x1b8: ldp     q0, q1, [sp, #64]
     +0x1bc: movi    v3.2d, #0x0
     +0x1c0: cmp     x20, #0xff
     +0x1c4: stp     q0, q1, [sp]
     +0x1c8: ldp     q2, q0, [sp, #96]
     +0x1cc: str     q3, [sp, #256]
     +0x1d0: stp     q3, q3, [sp, #64]
     +0x1d4: stp     q2, q0, [sp, #32]
     +0x1d8: stp     q3, q3, [sp, #96]
     +0x1dc: stp     q3, q3, [sp, #128]
     +0x1e0: stp     q3, q3, [sp, #160]
     +0x1e4: stp     q3, q3, [sp, #192]
     +0x1e8: stp     q3, q3, [sp, #224]
     +0x1ec: b.ls    <mldsa44_verify_pre_hash_shake256+0x1f8>
     +0x1f0: mov     w0, #0xfffffff7
     +0x1f4: b       <mldsa44_verify_pre_hash_shake256+0x27c>
     +0x1f8: mov     w8, #0x1
     +0x1fc: strb    w20, [sp, #65]
     +0x200: strb    w8, [sp, #64]
     +0x204: cbz     x20, <mldsa44_verify_pre_hash_shake256+0x21c>
     +0x208: add     x8, sp, #0x40
     +0x20c: mov     x1, x22
     +0x210: mov     x2, x20
     +0x214: orr     x0, x8, #0x2
     +0x218: bl      <memcpy>
     +0x21c: ldp     q0, q1, [sp]
     +0x220: add     x8, sp, #0x40
     +0x224: add     x8, x8, x20
     +0x228: adrp    x9, <page>
     +0x22c: add     x9, x9, #0xbdc
     +0x230: ldr     x9, [x9]
     +0x234: mov     w10, #0x403
     +0x238: add     x1, sp, #0x40
     +0x23c: stur    q0, [x8, #13]
     +0x240: movk    w10, #0xc02, lsl #16
     +0x244: add     x2, x20, #0x4d
     +0x248: stur    q1, [x8, #29]
     +0x24c: ldp     q0, q1, [sp, #32]
     +0x250: mov     x0, x21
     +0x254: mov     x3, xzr
     +0x258: mov     x4, xzr
     +0x25c: mov     x5, x19
     +0x260: mov     w6, wzr
     +0x264: stur    x9, [x8, #2]
     +0x268: stur    w10, [x8, #9]
     +0x26c: stur    q0, [x8, #45]
     +0x270: stur    q1, [x8, #61]
     +0x274: bl      <mldsa44_verify_internal>
     +0x278: movi    v3.2d, #0x0
     +0x27c: add     x8, x24, #0x13c
     +0x280: stp     q3, q3, [sp, #64]
     +0x284: str     q3, [x8]
     +0x288: mov     x8, sp
     +0x28c: stp     q3, q3, [sp, #96]
     +0x290: stp     q3, q3, [sp, #128]
     +0x294: stp     q3, q3, [sp, #160]
     +0x298: stp     q3, q3, [sp, #192]
     +0x29c: stp     q3, q3, [sp, #224]
     +0x2a0: stp     q3, q3, [sp, #256]
     +0x2a4: stp     q3, q3, [sp, #288]
     +0x2a8: stp     q3, q3, [sp, #320]
     +0x2ac: stp     q3, q3, [sp, #352]
     +0x2b0: stp     q3, q3, [sp]
     +0x2b4: stp     q3, q3, [sp, #32]
     +0x2b8: adrp    x8, <page>
     +0x2bc: ldr     x8, [x8, #4088]
     +0x2c0: ldr     x9, [sp, #424]
     +0x2c4: ldr     x8, [x8]
     +0x2c8: cmp     x8, x9
     +0x2cc: b.ne    <mldsa44_verify_pre_hash_shake256+0x3ac>
     +0x2d0: mov     sp, x29
     +0x2d4: ldp     x20, x19, [sp, #64]
     +0x2d8: ldr     x28, [sp, #16]
     +0x2dc: ldp     x22, x21, [sp, #48]
     +0x2e0: ldp     x24, x23, [sp, #32]
     +0x2e4: ldp     x29, x30, [sp], #80
     +0x2e8: mov     x1, #0x0
     +0x2ec: mov     x2, #0x0
     +0x2f0: mov     x3, #0x0
     +0x2f4: mov     x4, #0x0
     +0x2f8: mov     x5, #0x0
     +0x2fc: mov     x6, #0x0
     +0x300: mov     x8, #0x0
     +0x304: mov     x9, #0x0
     +0x308: mov     x10, #0x0
     +0x30c: mov     x11, #0x0
     +0x310: mov     x12, #0x0
     +0x314: ret     
     +0x318: cmp     x23, #0x20
     +0x31c: b.cs    <mldsa44_verify_pre_hash_shake256+0x328>
     +0x320: mov     x8, xzr
     +0x324: b       <mldsa44_verify_pre_hash_shake256+0x370>
     +0x328: add     x10, sp, #0x40
     +0x32c: and     x9, x23, #0x18
     +0x330: and     x8, x23, #0xe0
     +0x334: add     x10, x10, #0x10
     +0x338: add     x11, x24, #0x10
     +0x33c: and     x12, x23, #0xe0
     +0x340: ldp     q0, q3, [x10, #-16]
     +0x344: subs    x12, x12, #0x20
     +0x348: ldp     q1, q2, [x11, #-16]
     +0x34c: add     x11, x11, #0x20
     +0x350: eor     v0.16b, v0.16b, v1.16b
     +0x354: eor     v1.16b, v3.16b, v2.16b
     +0x358: stp     q0, q1, [x10, #-16]
     +0x35c: add     x10, x10, #0x20
     +0x360: b.ne    <mldsa44_verify_pre_hash_shake256+0x340>
     +0x364: cmp     x23, x8
     +0x368: b.eq    <mldsa44_verify_pre_hash_shake256+0x188>
     +0x36c: cbz     x9, <mldsa44_verify_pre_hash_shake256+0x160>
     +0x370: mov     x11, x8
     +0x374: and     x8, x23, #0xf8
     +0x378: add     x10, sp, #0x40
     +0x37c: sub     x9, x11, x8
     +0x380: add     x10, x10, x11
     +0x384: add     x11, x24, x11
     +0x388: ldr     d0, [x11], #8
     +0x38c: ldr     d1, [x10]
     +0x390: adds    x9, x9, #0x8
     +0x394: eor     v0.8b, v1.8b, v0.8b
     +0x398: str     d0, [x10], #8
     +0x39c: b.ne    <mldsa44_verify_pre_hash_shake256+0x388>
     +0x3a0: cmp     x23, x8
     +0x3a4: b.eq    <mldsa44_verify_pre_hash_shake256+0x188>
     +0x3a8: b       <mldsa44_verify_pre_hash_shake256+0x160>
     +0x3ac: bl      <__stack_chk_fail>

    memcpy@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4048]
       +0x8: add     x16, x16, #0xfd0
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_verify_pre_hash_shake256";
    layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* signature sigb at sig (2420 bytes), the message M of mlen bytes at m, the *)
(* context C of ctxlen bytes at ctx and the public key pkb at pk (1312       *)
(* bytes), with PH the SHAKE256 pre-hash of M and PRE the prefix of HashML-  *)
(* DSA (of length ctxlen + 77): the result is -9 if ctxlen > 255, and        *)
(* otherwise 0 if the signature is accepted for PRE as the message and -6 if *)
(* not. The stack is the 12000 bytes below the stack pointer: the frame of   *)
(* the function, of up to 528 bytes, and the stacks of its callees.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen pk sigb pkb M C PH PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
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
          ALL (nonoverlapping (word_sub stackpointer (word 12000),12000))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_verify_pre_hash_shake256) /\
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
                       (mld_verify_mu 1312 pkb 0 0 (ctxlen + 77) PRE)
                     then word 0 else word 4294967290))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 12000),12000)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the signature, the   *)
(* message, the context and the public key, all public, with all accesses    *)
(* within the arguments, the stack, the GOT entries and the stack guard, the *)
(* region (ea,el) that the C library functions may read and the constants of *)
(* the callees, and the writes within the outputs and the stack.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C PH PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
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
          ALL (nonoverlapping (word_sub stackpointer (word 12000),12000))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_verify_pre_hash_shake256) /\
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
                       (mld_verify_mu 1312 pkb 0 0 (ctxlen + 77) PRE)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen ctx ctxlen pk sigb pkb M C
                            guard mf mc pc
                            (word_sub stackpointer (word 12000))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 12000),12000;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa44_verify_internal_const1),16;
                         word(pc + mldsa44_verify_internal_const2),16;
                         word(pc + mldsa44_verify_internal_const3),8;
                         word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [word_sub stackpointer (word 12000),12000]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 12000),12000)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_ret_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen pk sigb pkb M C PH PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
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
          ALL (nonoverlapping (word_sub stackpointer (word 12000),12000))
              [(sig,2420); (m,mlen); (ctx,ctxlen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
               (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_verify_pre_hash_shake256) /\
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
                            (word_sub stackpointer (word 12000))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; ctx,ctxlen; pk,1312;
                         word_sub stackpointer (word 12000),12000;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa44_verify_internal_const1),16;
                         word(pc + mldsa44_verify_internal_const2),16;
                         word(pc + mldsa44_verify_internal_const3),8;
                         word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [word_sub stackpointer (word 12000),12000]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 12000),12000)])`;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
