(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message with a SHAKE256 pre-hash (HashML-DSA): the statement.   *)
(* This is the code for mldsa44_signature_pre_hash_shake256                  *)
(* (mld_sign_signature_pre_hash_shake256 in sign.c, an external API          *)
(* function) from mldsa-native's portable C implementation compiled by clang *)
(* 23 with -O3 as one translation unit with MLD_CONFIG_REDUCE_RAM (see       *)
(* mldsa_native/README.md). It has inlined mldsa_shake256, which absorbs the *)
(* message into a zero Keccak state (a loop over the blocks of 136 bytes     *)
(* with a call of mldsa_keccakf1600_permute, then the XOR of the rest),      *)
(* pads, calls mldsa_keccakf1600_permute and copies the first 64 bytes of    *)
(* the state as the pre-hash. It builds the prefix 1 || ctxlen || ctx || OID *)
(* || PH of HashML-DSA with hashalg MLD_PREHASH_SHAKE_256 (12) in a buffer   *)
(* on the stack, with memcpy for the context and stores for the OID, signs   *)
(* it with mldsa44_signature_internal, and zeroes the pre-hash and the       *)
(* buffer with stores of zero vectors (and the signature with memset if      *)
(* signing fails). It is verified in the whole image (see libmldsa.ml),      *)
(* using the theorems for the callees and the contracts                      *)
(* memset_full_contract, memcpy_full_contract of the C library functions,    *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_pre_hash_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_signature_pre_hash_shake256:
       +0x0: stp     x29, x30, [sp, #-80]!
       +0x4: stp     x28, x25, [sp, #16]
       +0x8: stp     x24, x23, [sp, #32]
       +0xc: stp     x22, x21, [sp, #48]
      +0x10: stp     x20, x19, [sp, #64]
      +0x14: mov     x29, sp
      +0x18: sub     x9, sp, #0x1b0
      +0x1c: and     sp, x9, #0xffffffffffffffe0
      +0x20: adrp    x8, <page>
      +0x24: movi    v0.2d, #0x0
      +0x28: mov     x20, x6
      +0x2c: ldr     x8, [x8, #4088]
      +0x30: mov     x21, x5
      +0x34: mov     x22, x4
      +0x38: mov     x23, x3
      +0x3c: mov     x24, x2
      +0x40: mov     x25, x1
      +0x44: ldr     x8, [x8]
      +0x48: mov     x19, x0
      +0x4c: cmp     x2, #0x88
      +0x50: str     x8, [sp, #424]
      +0x54: stur    q0, [sp, #252]
      +0x58: stp     q0, q0, [sp, #64]
      +0x5c: stp     q0, q0, [sp, #96]
      +0x60: stp     q0, q0, [sp, #128]
      +0x64: stp     q0, q0, [sp, #160]
      +0x68: stp     q0, q0, [sp, #192]
      +0x6c: stp     q0, q0, [sp, #224]
      +0x70: b.cc    <mldsa44_signature_pre_hash_shake256+0x13c>
      +0x74: ldp     d0, d3, [sp, #64]
      +0x78: add     x0, sp, #0x40
      +0x7c: ldp     d1, d2, [x25]
      +0x80: sub     x24, x24, #0x88
      +0x84: ldp     d6, d7, [sp, #96]
      +0x88: ldp     d16, d17, [sp, #112]
      +0x8c: eor     v0.8b, v0.8b, v1.8b
      +0x90: eor     v1.8b, v3.8b, v2.8b
      +0x94: ldp     d4, d2, [x25, #16]
      +0x98: ldp     d5, d3, [sp, #80]
      +0x9c: stp     d0, d1, [sp, #64]
      +0xa0: eor     v4.8b, v5.8b, v4.8b
      +0xa4: eor     v2.8b, v3.8b, v2.8b
      +0xa8: ldp     d5, d3, [x25, #32]
      +0xac: stp     d4, d2, [sp, #80]
      +0xb0: ldp     d1, d2, [x25, #80]
      +0xb4: eor     v5.8b, v6.8b, v5.8b
      +0xb8: eor     v3.8b, v7.8b, v3.8b
      +0xbc: ldp     d6, d7, [x25, #48]
      +0xc0: stp     d5, d3, [sp, #96]
      +0xc4: ldp     d3, d5, [x25, #96]
      +0xc8: eor     v6.8b, v16.8b, v6.8b
      +0xcc: eor     v7.8b, v17.8b, v7.8b
      +0xd0: ldp     d16, d0, [x25, #64]
      +0xd4: ldp     d18, d17, [sp, #128]
      +0xd8: stp     d6, d7, [sp, #112]
      +0xdc: eor     v0.8b, v17.8b, v0.8b
      +0xe0: ldp     d4, d17, [sp, #144]
      +0xe4: eor     v16.8b, v18.8b, v16.8b
      +0xe8: eor     v1.8b, v4.8b, v1.8b
      +0xec: ldp     d4, d6, [sp, #160]
      +0xf0: eor     v2.8b, v17.8b, v2.8b
      +0xf4: stp     d16, d0, [sp, #128]
      +0xf8: eor     v3.8b, v4.8b, v3.8b
      +0xfc: ldp     d4, d0, [x25, #112]
     +0x100: eor     v5.8b, v6.8b, v5.8b
     +0x104: ldp     d7, d6, [sp, #176]
     +0x108: stp     d1, d2, [sp, #144]
     +0x10c: ldr     d1, [x25, #128]
     +0x110: ldr     d2, [sp, #192]
     +0x114: add     x25, x25, #0x88
     +0x118: eor     v4.8b, v7.8b, v4.8b
     +0x11c: eor     v0.8b, v6.8b, v0.8b
     +0x120: eor     v1.8b, v2.8b, v1.8b
     +0x124: stp     d3, d5, [sp, #160]
     +0x128: stp     d4, d0, [sp, #176]
     +0x12c: str     d1, [sp, #192]
     +0x130: bl      <mldsa_keccakf1600_permute>
     +0x134: cmp     x24, #0x87
     +0x138: b.hi    <mldsa44_signature_pre_hash_shake256+0x74>
     +0x13c: cbz     x24, <mldsa44_signature_pre_hash_shake256+0x18c>
     +0x140: cmp     x24, #0x8
     +0x144: b.cc    <mldsa44_signature_pre_hash_shake256+0x160>
     +0x148: add     x8, sp, #0x40
     +0x14c: add     x10, x25, x24
     +0x150: add     x9, x8, x24
     +0x154: cmp     x25, x9
     +0x158: ccmp    x8, x10, #0x2, cc
     +0x15c: b.cs    <mldsa44_signature_pre_hash_shake256+0x344>
     +0x160: mov     x8, xzr
     +0x164: add     x10, sp, #0x40
     +0x168: sub     x9, x24, x8
     +0x16c: add     x10, x10, x8
     +0x170: add     x8, x25, x8
     +0x174: ldrb    w11, [x8], #1
     +0x178: ldrb    w12, [x10]
     +0x17c: subs    x9, x9, #0x1
     +0x180: eor     w11, w12, w11
     +0x184: strb    w11, [x10], #1
     +0x188: b.ne    <mldsa44_signature_pre_hash_shake256+0x174>
     +0x18c: str     w24, [sp, #264]
     +0x190: add     x25, sp, #0x40
     +0x194: mov     w9, #0x88
     +0x198: ldrb    w8, [x25, x24]
     +0x19c: add     x0, sp, #0x40
     +0x1a0: eor     w8, w8, #0x1f
     +0x1a4: strb    w8, [x25, x24]
     +0x1a8: ldrb    w8, [sp, #199]
     +0x1ac: str     w9, [sp, #264]
     +0x1b0: eor     w8, w8, #0x80
     +0x1b4: strb    w8, [sp, #199]
     +0x1b8: bl      <mldsa_keccakf1600_permute>
     +0x1bc: ldp     q0, q1, [sp, #64]
     +0x1c0: movi    v3.2d, #0x0
     +0x1c4: cmp     x22, #0xff
     +0x1c8: stp     q0, q1, [sp]
     +0x1cc: ldp     q2, q0, [sp, #96]
     +0x1d0: str     q3, [sp, #256]
     +0x1d4: stp     q3, q3, [sp, #64]
     +0x1d8: stp     q2, q0, [sp, #32]
     +0x1dc: stp     q3, q3, [sp, #96]
     +0x1e0: stp     q3, q3, [sp, #128]
     +0x1e4: stp     q3, q3, [sp, #160]
     +0x1e8: stp     q3, q3, [sp, #192]
     +0x1ec: stp     q3, q3, [sp, #224]
     +0x1f0: b.ls    <mldsa44_signature_pre_hash_shake256+0x1fc>
     +0x1f4: mov     w20, #0xfffffff7
     +0x1f8: b       <mldsa44_signature_pre_hash_shake256+0x288>
     +0x1fc: mov     w8, #0x1
     +0x200: strb    w22, [sp, #65]
     +0x204: strb    w8, [sp, #64]
     +0x208: cbz     x22, <mldsa44_signature_pre_hash_shake256+0x220>
     +0x20c: add     x8, sp, #0x40
     +0x210: mov     x1, x23
     +0x214: mov     x2, x22
     +0x218: orr     x0, x8, #0x2
     +0x21c: bl      <memcpy>
     +0x220: ldp     q0, q1, [sp]
     +0x224: add     x8, sp, #0x40
     +0x228: add     x8, x8, x22
     +0x22c: adrp    x9, <page>
     +0x230: add     x9, x9, #0xbdc
     +0x234: ldr     x9, [x9]
     +0x238: mov     w10, #0x403
     +0x23c: add     x1, sp, #0x40
     +0x240: stur    q0, [x8, #13]
     +0x244: movk    w10, #0xc02, lsl #16
     +0x248: add     x2, x22, #0x4d
     +0x24c: stur    q1, [x8, #29]
     +0x250: ldp     q0, q1, [sp, #32]
     +0x254: mov     x0, x19
     +0x258: mov     x3, xzr
     +0x25c: mov     x4, xzr
     +0x260: mov     x5, x21
     +0x264: mov     x6, x20
     +0x268: mov     w7, wzr
     +0x26c: stur    x9, [x8, #2]
     +0x270: stur    w10, [x8, #9]
     +0x274: stur    q0, [x8, #45]
     +0x278: stur    q1, [x8, #61]
     +0x27c: bl      <mldsa44_signature_internal>
     +0x280: mov     w20, w0
     +0x284: cbz     w0, <mldsa44_signature_pre_hash_shake256+0x298>
     +0x288: mov     x0, x19
     +0x28c: mov     w1, wzr
     +0x290: mov     w2, #0x974
     +0x294: bl      <memset>
     +0x298: movi    v0.2d, #0x0
     +0x29c: add     x8, sp, #0x40
     +0x2a0: add     x9, x8, #0x13c
     +0x2a4: str     q0, [x9]
     +0x2a8: stp     q0, q0, [sp, #64]
     +0x2ac: stp     q0, q0, [sp, #96]
     +0x2b0: stp     q0, q0, [sp, #128]
     +0x2b4: stp     q0, q0, [sp, #160]
     +0x2b8: stp     q0, q0, [sp, #192]
     +0x2bc: stp     q0, q0, [sp, #224]
     +0x2c0: stp     q0, q0, [sp, #256]
     +0x2c4: stp     q0, q0, [sp, #288]
     +0x2c8: stp     q0, q0, [sp, #320]
     +0x2cc: stp     q0, q0, [sp, #352]
     +0x2d0: stp     q0, q0, [sp]
     +0x2d4: mov     x8, sp
     +0x2d8: stp     q0, q0, [sp, #32]
     +0x2dc: adrp    x8, <page>
     +0x2e0: ldr     x8, [x8, #4088]
     +0x2e4: ldr     x9, [sp, #424]
     +0x2e8: ldr     x8, [x8]
     +0x2ec: cmp     x8, x9
     +0x2f0: b.ne    <mldsa44_signature_pre_hash_shake256+0x3d8>
     +0x2f4: mov     w0, w20
     +0x2f8: mov     sp, x29
     +0x2fc: ldp     x20, x19, [sp, #64]
     +0x300: ldp     x22, x21, [sp, #48]
     +0x304: ldp     x24, x23, [sp, #32]
     +0x308: ldp     x28, x25, [sp, #16]
     +0x30c: ldp     x29, x30, [sp], #80
     +0x310: mov     x1, #0x0
     +0x314: mov     x2, #0x0
     +0x318: mov     x3, #0x0
     +0x31c: mov     x4, #0x0
     +0x320: mov     x5, #0x0
     +0x324: mov     x6, #0x0
     +0x328: mov     x7, #0x0
     +0x32c: mov     x8, #0x0
     +0x330: mov     x9, #0x0
     +0x334: mov     x10, #0x0
     +0x338: mov     x11, #0x0
     +0x33c: mov     x12, #0x0
     +0x340: ret     
     +0x344: cmp     x24, #0x20
     +0x348: b.cs    <mldsa44_signature_pre_hash_shake256+0x354>
     +0x34c: mov     x8, xzr
     +0x350: b       <mldsa44_signature_pre_hash_shake256+0x39c>
     +0x354: add     x10, sp, #0x40
     +0x358: and     x9, x24, #0x18
     +0x35c: and     x8, x24, #0xe0
     +0x360: add     x10, x10, #0x10
     +0x364: add     x11, x25, #0x10
     +0x368: and     x12, x24, #0xe0
     +0x36c: ldp     q0, q3, [x10, #-16]
     +0x370: subs    x12, x12, #0x20
     +0x374: ldp     q1, q2, [x11, #-16]
     +0x378: add     x11, x11, #0x20
     +0x37c: eor     v0.16b, v0.16b, v1.16b
     +0x380: eor     v1.16b, v3.16b, v2.16b
     +0x384: stp     q0, q1, [x10, #-16]
     +0x388: add     x10, x10, #0x20
     +0x38c: b.ne    <mldsa44_signature_pre_hash_shake256+0x36c>
     +0x390: cmp     x24, x8
     +0x394: b.eq    <mldsa44_signature_pre_hash_shake256+0x18c>
     +0x398: cbz     x9, <mldsa44_signature_pre_hash_shake256+0x164>
     +0x39c: mov     x11, x8
     +0x3a0: and     x8, x24, #0xf8
     +0x3a4: add     x10, sp, #0x40
     +0x3a8: sub     x9, x11, x8
     +0x3ac: add     x10, x10, x11
     +0x3b0: add     x11, x25, x11
     +0x3b4: ldr     d0, [x11], #8
     +0x3b8: ldr     d1, [x10]
     +0x3bc: adds    x9, x9, #0x8
     +0x3c0: eor     v0.8b, v1.8b, v0.8b
     +0x3c4: str     d0, [x10], #8
     +0x3c8: b.ne    <mldsa44_signature_pre_hash_shake256+0x3b4>
     +0x3cc: cmp     x24, x8
     +0x3d0: b.eq    <mldsa44_signature_pre_hash_shake256+0x18c>
     +0x3d4: b       <mldsa44_signature_pre_hash_shake256+0x164>
     +0x3d8: bl      <__stack_chk_fail>

    memcpy@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4048]
       +0x8: add     x16, x16, #0xfd0
       +0xc: br      x17

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_signature_pre_hash_shake256";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for the C library functions. The      *)
(* secret key skb at sk (2560 bytes), the message M of mlen bytes at m, the  *)
(* context C of ctxlen bytes at ctx and the 32 bytes RND at rnd, with PH the *)
(* SHAKE256 pre-hash of M, PRE the prefix of HashML-DSA (of length ctxlen +  *)
(* 77 if ctxlen <= 255) and MU the mu of signing PRE: the result is -9 if    *)
(* ctxlen > 255, with the signature zero, and otherwise that of signing,     *)
(* with the signature mld_sign_sig_44 skb MU RND. The stack is the 13408     *)
(* bytes below the stack pointer: the frame of the function, of up to 528    *)
(* bytes, and the stacks of its callees.                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen ctx ctxlen rnd sk skb M C RND PH PRE MU
                 guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
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
           [(sig,2420); (word_sub stackpointer (word 13408),13408)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 13408),13408)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 13408),13408)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, rho and what the C   *)
(* code declassifies in signing (mld_sign_declass_44), with all accesses     *)
(* within the arguments, the stack, the GOT entries and the stack guard, the *)
(* region (ea,el) that the C library functions may read and the constants of *)
(* the callees, and the writes within the outputs and the stack.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen rnd sk skb M C RND PH PRE MU
                 guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
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
           [(sig,2420); (word_sub stackpointer (word 13408),13408)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 13408),13408)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
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
                            (word_sub stackpointer (word 13408))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; ctx,ctxlen; rnd,32; sk,2560;
                         word_sub stackpointer (word 13408),13408;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa44_signature_internal_consts),128;
                         word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [sig,2420; word_sub stackpointer (word 13408),13408]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 13408),13408)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen ctx ctxlen rnd sk skb M C RND PH PRE MU
                 guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          33792 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
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
           [(sig,2420); (word_sub stackpointer (word 13408),13408)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 13408),13408)]
           [(m,mlen); (ctx,ctxlen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
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
                            (word_sub stackpointer (word 13408))
                            returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; ctx,ctxlen; rnd,32; sk,2560;
                         word_sub stackpointer (word 13408),13408;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa44_signature_internal_consts),128;
                         word(pc + rodata_mld_get_hash_oid87_oid_map),192]
                        [sig,2420; word_sub stackpointer (word 13408),13408]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 13408),13408)])`;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
