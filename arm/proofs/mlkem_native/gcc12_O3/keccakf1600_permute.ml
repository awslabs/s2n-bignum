(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation.                                                 *)
(* This is the code for mlkem_keccakf1600_permute from mlkem-native's        *)
(* portable C implementation compiled by gcc 12 with -O3 (see                *)
(* mlkem_native/README.md), which is the same as with -O2 except for the     *)
(* address of its table of round constants. Unlike the hand-written kernels, *)
(* it reads that table from the read-only data rather than taking it as an   *)
(* argument, and it does two rounds in each iteration of its loop. It is     *)
(* verified in the whole image (see libmlkem.ml), with the same theorems as  *)
(* for -O2, including those for the state as a 1600-bit word, with           *)
(* keccak_f1600 of common/fips202.ml.                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;
needs "arm/proofs/utils/keccak_spec.ml";;

(*** The code in the image:

    mlkem_keccakf1600_permute:
       +0x0: stp     x19, x20, [sp, #-192]!
       +0x4: adrp    x1, <page>
       +0x8: add     x1, x1, #0xab0  // rodata_mlk_KeccakF_RoundConstants
       +0xc: ldp     x9, x4, [x0, #56]
      +0x10: str     x1, [sp, #96]
      +0x14: add     x1, x1, #0xc0
      +0x18: str     x1, [sp, #176]
      +0x1c: ldr     x1, [x0]
      +0x20: str     x1, [sp, #104]
      +0x24: ldr     x1, [x0, #16]
      +0x28: str     x4, [sp, #112]
      +0x2c: ldr     x4, [x0, #112]
      +0x30: stp     x21, x22, [sp, #16]
      +0x34: mov     x18, x9
      +0x38: ldr     x2, [x0, #8]
      +0x3c: stp     x23, x24, [sp, #32]
      +0x40: ldr     x3, [x0, #40]
      +0x44: stp     x25, x26, [sp, #48]
      +0x48: ldp     x26, x23, [x0, #24]
      +0x4c: stp     x27, x28, [sp, #64]
      +0x50: ldp     x7, x21, [x0, #72]
      +0x54: str     x4, [sp, #120]
      +0x58: ldp     x20, x16, [x0, #88]
      +0x5c: str     x1, [sp, #136]
      +0x60: ldr     x1, [x0, #48]
      +0x64: mov     x28, x23
      +0x68: ldr     x11, [x0, #104]
      +0x6c: str     x30, [sp, #80]
      +0x70: ldp     x22, x12, [x0, #120]
      +0x74: mov     x14, x20
      +0x78: ldp     x4, x25, [x0, #184]
      +0x7c: mov     x23, x21
      +0x80: ldp     x6, x5, [x0, #136]
      +0x84: mov     x20, x2
      +0x88: ldp     x13, x10, [x0, #152]
      +0x8c: mov     x30, x22
      +0x90: ldp     x19, x15, [x0, #168]
      +0x94: mov     x9, x25
      +0x98: mov     x27, x11
      +0x9c: mov     x22, x7
      +0xa0: mov     x17, x12
      +0xa4: mov     x25, x3
      +0xa8: str     x26, [sp, #128]
      +0xac: str     x0, [sp, #184]
      +0xb0: ldp     x11, x24, [sp, #128]
      +0xb4: eor     x12, x16, x6
      +0xb8: ldp     x0, x21, [sp, #104]
      +0xbc: eor     x2, x23, x30
      +0xc0: eor     x26, x14, x17
      +0xc4: eor     x7, x24, x18
      +0xc8: eor     x7, x7, x12
      +0xcc: ldr     x12, [sp, #120]
      +0xd0: eor     x3, x0, x25
      +0xd4: eor     x8, x11, x21
      +0xd8: eor     x11, x27, x5
      +0xdc: eor     x0, x20, x1
      +0xe0: eor     x3, x3, x2
      +0xe4: eor     x8, x8, x11
      +0xe8: eor     x7, x7, x15
      +0xec: eor     x3, x3, x10
      +0xf0: eor     x8, x8, x4
      +0xf4: eor     x26, x26, x0
      +0xf8: eor     x2, x28, x22
      +0xfc: eor     x0, x12, x13
     +0x100: eor     x26, x26, x19
     +0x104: eor     x2, x2, x0
     +0x108: eor     x0, x3, x7, ror #63
     +0x10c: eor     x3, x8, x3, ror #63
     +0x110: eor     x8, x26, x8, ror #63
     +0x114: eor     x2, x2, x9
     +0x118: eor     x1, x0, x1
     +0x11c: eor     x21, x0, x20
     +0x120: eor     x17, x0, x17
     +0x124: eor     x20, x8, x18
     +0x128: eor     x14, x0, x14
     +0x12c: eor     x0, x0, x19
     +0x130: eor     x26, x2, x26, ror #63
     +0x134: ldp     x18, x19, [sp, #112]
     +0x138: eor     x2, x7, x2, ror #63
     +0x13c: ldr     x7, [sp, #96]
     +0x140: eor     x12, x8, x6
     +0x144: ldr     x6, [sp, #128]
     +0x148: eor     x16, x8, x16
     +0x14c: eor     x15, x8, x15
     +0x150: eor     x9, x3, x9
     +0x154: eor     x8, x8, x24
     +0x158: eor     x5, x2, x5
     +0x15c: ldr     x7, [x7]
     +0x160: ror     x9, x9, #50
     +0x164: eor     x11, x3, x13
     +0x168: ror     x5, x5, #43
     +0x16c: eor     x13, x2, x27
     +0x170: eor     x4, x2, x4
     +0x174: eor     x6, x2, x6
     +0x178: eor     x2, x2, x18
     +0x17c: ror     x18, x1, #20
     +0x180: ror     x1, x8, #2
     +0x184: ldr     x8, [sp, #104]
     +0x188: str     x18, [sp, #104]
     +0x18c: eor     x22, x3, x22
     +0x190: ror     x16, x16, #21
     +0x194: stp     x7, x1, [sp, #136]
     +0x198: eor     x7, x3, x28
     +0x19c: eor     x3, x3, x19
     +0x1a0: bic     x19, x9, x5
     +0x1a4: eor     x24, x26, x23
     +0x1a8: eor     x1, x26, x30
     +0x1ac: bic     x30, x16, x18
     +0x1b0: bic     x18, x5, x16
     +0x1b4: eor     x16, x19, x16
     +0x1b8: ldr     x19, [sp, #104]
     +0x1bc: ror     x17, x17, #19
     +0x1c0: eor     x23, x26, x25
     +0x1c4: ror     x24, x24, #61
     +0x1c8: ldr     x25, [sp, #136]
     +0x1cc: eor     x10, x26, x10
     +0x1d0: eor     x8, x26, x8
     +0x1d4: eor     x19, x18, x19
     +0x1d8: ror     x22, x22, #44
     +0x1dc: bic     x18, x17, x24
     +0x1e0: ror     x6, x6, #36
     +0x1e4: ror     x15, x15, #3
     +0x1e8: ror     x20, x20, #58
     +0x1ec: ror     x13, x13, #39
     +0x1f0: ror     x11, x11, #56
     +0x1f4: bic     x27, x24, x22
     +0x1f8: ror     x10, x10, #46
     +0x1fc: eor     x18, x18, x22
     +0x200: bic     x22, x22, x6
     +0x204: str     x16, [sp, #112]
     +0x208: bic     x16, x8, x9
     +0x20c: eor     x27, x27, x6
     +0x210: bic     x26, x13, x20
     +0x214: eor     x16, x16, x5
     +0x218: ror     x21, x21, #63
     +0x21c: bic     x5, x15, x17
     +0x220: eor     x28, x8, x25
     +0x224: bic     x6, x6, x15
     +0x228: eor     x22, x22, x15
     +0x22c: bic     x15, x10, x11
     +0x230: ror     x14, x14, #54
     +0x234: eor     x28, x30, x28
     +0x238: ror     x23, x23, #28
     +0x23c: eor     x30, x26, x21
     +0x240: eor     x15, x15, x13
     +0x244: eor     x26, x5, x24
     +0x248: eor     x5, x6, x17
     +0x24c: bic     x6, x11, x13
     +0x250: bic     x13, x20, x21
     +0x254: bic     x21, x21, x10
     +0x258: ror     x4, x4, #8
     +0x25c: bic     x25, x14, x23
     +0x260: ror     x7, x7, #37
     +0x264: eor     x11, x21, x11
     +0x268: ror     x12, x12, #49
     +0x26c: eor     x25, x25, x7
     +0x270: stp     x5, x11, [sp, #120]
     +0x274: bic     x11, x23, x7
     +0x278: bic     x7, x7, x4
     +0x27c: eor     x10, x13, x10
     +0x280: bic     x5, x4, x12
     +0x284: bic     x13, x12, x14
     +0x288: eor     x7, x7, x12
     +0x28c: ror     x3, x3, #25
     +0x290: ldr     x12, [sp, #104]
     +0x294: ror     x1, x1, #23
     +0x298: ldr     x21, [sp, #144]
     +0x29c: ror     x0, x0, #62
     +0x2a0: str     x10, [sp, #136]
     +0x2a4: ror     x2, x2, #9
     +0x2a8: bic     x24, x1, x3
     +0x2ac: eor     x5, x5, x14
     +0x2b0: bic     x8, x12, x8
     +0x2b4: bic     x14, x0, x1
     +0x2b8: ldr     x12, [sp, #112]
     +0x2bc: eor     x24, x24, x2
     +0x2c0: bic     x17, x2, x21
     +0x2c4: eor     x14, x14, x3
     +0x2c8: bic     x10, x3, x2
     +0x2cc: eor     x13, x13, x23
     +0x2d0: ldp     x3, x2, [sp, #128]
     +0x2d4: eor     x23, x15, x5
     +0x2d8: eor     x12, x12, x26
     +0x2dc: eor     x8, x8, x9
     +0x2e0: eor     x9, x12, x23
     +0x2e4: eor     x6, x6, x20
     +0x2e8: ldr     x23, [sp, #120]
     +0x2ec: eor     x20, x28, x27
     +0x2f0: eor     x17, x17, x0
     +0x2f4: eor     x11, x11, x4
     +0x2f8: eor     x4, x30, x25
     +0x2fc: eor     x9, x9, x14
     +0x300: eor     x12, x16, x23
     +0x304: eor     x20, x20, x4
     +0x308: eor     x23, x22, x2
     +0x30c: eor     x10, x10, x21
     +0x310: eor     x4, x6, x13
     +0x314: eor     x2, x11, x17
     +0x318: bic     x0, x21, x0
     +0x31c: eor     x3, x3, x7
     +0x320: eor     x21, x19, x18
     +0x324: eor     x0, x0, x1
     +0x328: eor     x4, x21, x4
     +0x32c: eor     x1, x20, x10
     +0x330: eor     x3, x12, x3
     +0x334: eor     x2, x23, x2
     +0x338: eor     x12, x1, x9, ror #63
     +0x33c: eor     x4, x4, x24
     +0x340: eor     x3, x3, x0
     +0x344: eor     x2, x2, x8
     +0x348: eor     x21, x19, x12
     +0x34c: eor     x18, x18, x12
     +0x350: eor     x13, x13, x12
     +0x354: eor     x6, x6, x12
     +0x358: eor     x24, x24, x12
     +0x35c: eor     x1, x3, x1, ror #63
     +0x360: ldr     x12, [sp, #112]
     +0x364: eor     x3, x4, x3, ror #63
     +0x368: eor     x4, x2, x4, ror #63
     +0x36c: eor     x2, x9, x2, ror #63
     +0x370: ldr     x9, [sp, #96]
     +0x374: eor     x19, x26, x3
     +0x378: eor     x15, x15, x3
     +0x37c: eor     x14, x14, x3
     +0x380: eor     x5, x5, x3
     +0x384: eor     x3, x12, x3
     +0x388: ldr     x12, [sp, #136]
     +0x38c: eor     x23, x16, x2
     +0x390: ldr     x20, [x9, #8]
     +0x394: eor     x22, x22, x1
     +0x398: ldr     x16, [sp, #128]
     +0x39c: eor     x17, x17, x1
     +0x3a0: eor     x11, x11, x1
     +0x3a4: eor     x8, x8, x1
     +0x3a8: str     x20, [sp, #104]
     +0x3ac: eor     x20, x12, x1
     +0x3b0: eor     x1, x25, x4
     +0x3b4: eor     x7, x7, x2
     +0x3b8: ldr     x25, [sp, #120]
     +0x3bc: eor     x0, x0, x2
     +0x3c0: eor     x16, x16, x2
     +0x3c4: ror     x26, x20, #25
     +0x3c8: eor     x2, x25, x2
     +0x3cc: ror     x20, x1, #23
     +0x3d0: ldr     x25, [sp, #104]
     +0x3d4: ror     x1, x2, #9
     +0x3d8: ror     x18, x18, #20
     +0x3dc: ror     x17, x17, #50
     +0x3e0: ror     x7, x7, #43
     +0x3e4: eor     x9, x30, x4
     +0x3e8: ror     x15, x15, #21
     +0x3ec: eor     x12, x27, x4
     +0x3f0: eor     x10, x10, x4
     +0x3f4: eor     x4, x28, x4
     +0x3f8: stp     x1, x20, [sp, #144]
     +0x3fc: bic     x30, x15, x18
     +0x400: ldr     x1, [sp, #96]
     +0x404: eor     x20, x4, x25
     +0x408: bic     x25, x17, x7
     +0x40c: str     x25, [sp, #112]
     +0x410: ror     x14, x14, #3
     +0x414: bic     x28, x7, x15
     +0x418: ror     x23, x23, #36
     +0x41c: bic     x27, x18, x4
     +0x420: eor     x30, x30, x20
     +0x424: ror     x22, x22, #44
     +0x428: ror     x9, x9, #61
     +0x42c: bic     x4, x4, x17
     +0x430: ror     x13, x13, #19
     +0x434: eor     x20, x28, x18
     +0x438: add     x1, x1, #0x10
     +0x43c: eor     x28, x27, x17
     +0x440: stp     x1, x30, [sp, #96]
     +0x444: bic     x30, x23, x14
     +0x448: ldr     x17, [sp, #112]
     +0x44c: str     x30, [sp, #120]
     +0x450: ror     x11, x11, #56
     +0x454: bic     x2, x22, x23
     +0x458: ror     x16, x16, #39
     +0x45c: eor     x4, x4, x7
     +0x460: bic     x1, x13, x9
     +0x464: ror     x19, x19, #58
     +0x468: ror     x10, x10, #46
     +0x46c: ror     x0, x0, #8
     +0x470: bic     x25, x9, x22
     +0x474: ror     x5, x5, #49
     +0x478: eor     x1, x1, x22
     +0x47c: eor     x22, x2, x14
     +0x480: ldr     x2, [sp, #120]
     +0x484: str     x4, [sp, #128]
     +0x488: bic     x4, x11, x16
     +0x48c: bic     x18, x14, x13
     +0x490: eor     x15, x17, x15
     +0x494: eor     x14, x4, x19
     +0x498: bic     x17, x10, x11
     +0x49c: bic     x4, x0, x5
     +0x4a0: stp     x17, x4, [sp, #160]
     +0x4a4: eor     x13, x2, x13
     +0x4a8: ror     x21, x21, #63
     +0x4ac: ldr     x2, [sp, #160]
     +0x4b0: bic     x27, x16, x19
     +0x4b4: ldr     x4, [sp, #144]
     +0x4b8: eor     x16, x2, x16
     +0x4bc: ldr     x2, [sp, #168]
     +0x4c0: bic     x7, x19, x21
     +0x4c4: ror     x8, x8, #37
     +0x4c8: ror     x12, x12, #28
     +0x4cc: eor     x18, x18, x9
     +0x4d0: ror     x6, x6, #54
     +0x4d4: eor     x9, x7, x10
     +0x4d8: stp     x13, x9, [sp, #112]
     +0x4dc: bic     x13, x12, x8
     +0x4e0: ldr     x7, [sp, #152]
     +0x4e4: bic     x17, x5, x6
     +0x4e8: bic     x30, x6, x12
     +0x4ec: eor     x25, x25, x23
     +0x4f0: eor     x6, x2, x6
     +0x4f4: eor     x23, x27, x21
     +0x4f8: ldr     x2, [sp, #176]
     +0x4fc: eor     x13, x13, x0
     +0x500: str     x15, [sp, #136]
     +0x504: bic     x15, x21, x10
     +0x508: bic     x21, x8, x0
     +0x50c: ror     x24, x24, #62
     +0x510: ldr     x0, [sp, #96]
     +0x514: ror     x3, x3, #2
     +0x518: eor     x27, x15, x11
     +0x51c: mov     x11, x4
     +0x520: bic     x10, x26, x4
     +0x524: bic     x19, x7, x26
     +0x528: bic     x15, x24, x7
     +0x52c: bic     x4, x3, x24
     +0x530: bic     x9, x11, x3
     +0x534: eor     x30, x30, x8
     +0x538: eor     x17, x17, x12
     +0x53c: eor     x5, x21, x5
     +0x540: eor     x15, x15, x26
     +0x544: eor     x10, x10, x3
     +0x548: eor     x19, x19, x11
     +0x54c: eor     x4, x4, x7
     +0x550: eor     x9, x9, x24
     +0x554: cmp     x2, x0
     +0x558: b.ne    <mlkem_keccakf1600_permute+0xb0>
     +0x55c: ldr     x0, [sp, #184]
     +0x560: mov     x7, x25
     +0x564: ldr     x2, [sp, #104]
     +0x568: stp     x7, x1, [x0, #40]
     +0x56c: ldr     x1, [sp, #112]
     +0x570: stp     x2, x20, [x0]
     +0x574: ldr     x26, [sp, #128]
     +0x578: str     x1, [x0, #64]
     +0x57c: ldr     x1, [sp, #120]
     +0x580: stp     x26, x28, [x0, #24]
     +0x584: ldr     x2, [sp, #136]
     +0x588: str     x2, [x0, #16]
     +0x58c: str     x18, [x0, #56]
     +0x590: stp     x22, x23, [x0, #72]
     +0x594: stp     x14, x16, [x0, #88]
     +0x598: str     x27, [x0, #104]
     +0x59c: str     x1, [x0, #112]
     +0x5a0: stp     x30, x17, [x0, #120]
     +0x5a4: stp     x6, x5, [x0, #136]
     +0x5a8: stp     x13, x10, [x0, #152]
     +0x5ac: stp     x19, x15, [x0, #168]
     +0x5b0: stp     x4, x9, [x0, #184]
     +0x5b4: ldp     x21, x22, [sp, #16]
     +0x5b8: ldp     x23, x24, [sp, #32]
     +0x5bc: ldp     x25, x26, [sp, #48]
     +0x5c0: ldp     x27, x28, [sp, #64]
     +0x5c4: ldr     x30, [sp, #80]
     +0x5c8: ldp     x19, x20, [sp], #192
     +0x5cc: ret
 ***)

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_keccakf1600_permute"];;

(* ------------------------------------------------------------------------- *)
(* Reading the round constants from the table in the image.                  *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES64_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int64 list) n j s:armstate.
        read (memory :> bytes(a,8 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes64(word_add a (word(8 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int64 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read c s`) (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `64 * j = 8 * (8 * j)`;
              ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(*** The 192 bytes of the table, as they are in the image ***)

let KECCAK_RC_IN_IMAGE =
  let d = layout "rodata_mlk_KeccakF_RoundConstants" in
  let l = mk_list(fst(chop_list 192 (snd(chop_list d
            (dest_list(rhs(concl mlkem_native_libmlkem_gcc12_O3_mc)))))),
                  `:byte`) in
  let lth = MLKEM_NATIVE_IMAGE_DATA_RULE (REFL l) d
  and lenth = LENGTH_CONV(mk_comb(`LENGTH:byte list->num`,l))
  and nth = prove
   (mk_eq(mk_comb(`num_of_bytelist`,l),`num_of_wordlist round_constants`),
    REWRITE_TAC[round_constants; num_of_bytelist; num_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV) in
  prove
   (`!s pc.
        aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc
        ==> read (memory :> bytes(word(pc + rodata_mlk_KeccakF_RoundConstants),
                                  192)) s =
            num_of_wordlist round_constants`,
    REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP lth) THEN
    REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; lenth; nth]);;

let LENGTH_ROUND_CONSTANTS = prove
 (`LENGTH round_constants = 24`,
  REWRITE_TAC[round_constants; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the loop body, which does two rounds. As each lane of the     *)
(* first round is computed, it is replaced by a variable E_j abbreviating    *)
(* the corresponding lane in the specification, so that the second round     *)
(* and the final checks are about one round only. The lanes are recognized   *)
(* by evaluating both sides at random values, before proving the equations   *)
(* with KECCAK_BITBLAST_TAC.                                                 *)
(* ------------------------------------------------------------------------- *)

(*** Introduce ghost variables for the state reads in a list ***)

let GHOST_STATELIST_TAC =
  W(fun (asl,w) ->
        let regreads = dest_list(find_term is_list w) in
        let ghostvars = make_args "Ai_" [] (map type_of regreads) in
        EVERY(map2 GHOST_INTRO_TAC ghostvars (map rator regreads)));;

(*** Evaluation of 64-bit word expressions, with random values for atoms ***)

let eval64 =
  let atom_vals = Hashtbl.create 100 and memo = Hashtbl.create 10000 in
  let rand64 () =
    Int64.logor (Int64.shift_left (Int64.of_int (Random.bits ())) 34)
     (Int64.logor (Int64.shift_left (Int64.of_int (Random.bits ())) 4)
                  (Int64.of_int (Random.bits () land 15))) in
  let atom_val t =
    try Hashtbl.find atom_vals t with Not_found ->
      let v = rand64 () in Hashtbl.add atom_vals t v; v in
  let ror64 x n =
    if n = 0 then x else
    Int64.logor (Int64.shift_right_logical x n)
                (Int64.shift_left x (64 - n)) in
  let int64_of_num n =
    let v = ref 0L in
    String.iter (fun c -> v := Int64.add (Int64.mul !v 10L)
                                (Int64.of_int (Char.code c - 48)))
                (string_of_num n);
    !v in
  let rec eval t =
    try Hashtbl.find memo t with Not_found ->
    let v = match t with
      Comb(Comb(Const("word_xor",_),x),y) -> Int64.logxor (eval x) (eval y)
    | Comb(Comb(Const("word_and",_),x),y) -> Int64.logand (eval x) (eval y)
    | Comb(Comb(Const("word_or",_),x),y) -> Int64.logor (eval x) (eval y)
    | Comb(Const("word_not",_),x) -> Int64.lognot (eval x)
    | Comb(Comb(Const("word_ror",_),x),n) ->
        ror64 (eval x) (dest_small_numeral n)
    | Comb(Comb(Const("word_rol",_),x),n) ->
        ror64 (eval x) ((64 - dest_small_numeral n) mod 64)
    | Comb(Comb(Const("word_subword",_),
                Comb(Comb(Const("word_join",_),x),y)),p)
        when dest_small_numeral(rand p) = 64 ->
        let pos = dest_small_numeral(lhand p) in
        if pos = 0 then eval y else
        Int64.logor (Int64.shift_right_logical (eval y) pos)
                    (Int64.shift_left (eval x) (64 - pos))
    | Comb(Const("word",_),n) when is_numeral n ->
        int64_of_num(dest_numeral n)
    | _ -> atom_val t in
    Hashtbl.add memo t v; v in
  eval;;

(*** Expansion of one round of the specification as an explicit list ***)

let keccak_spec_round_conv =
  REWRITE_CONV[keccak_round] THENC TOP_DEPTH_CONV let_CONV THENC
  ONCE_DEPTH_CONV EL_CONV;;

(*** The abbreviations E_j for the lanes after the first round ***)

let KECCAK_INTRO_ABBREVS_TAC =
  W(fun (asl,w) ->
    let ais = map (fun j -> mk_var("Ai_"^string_of_int j,`:int64`)) (0--24) in
    let tm = mk_comb(mk_comb(`keccak_round`,`EL (2 * i) round_constants`),
                     mk_list(ais,`:int64`)) in
    let specs = dest_list(rhs(concl(keccak_spec_round_conv tm))) in
    let evs = map (fun j -> mk_var("E_"^string_of_int j,`:int64`)) (0--24) in
    MAP_EVERY (fun (e,t) -> ABBREV_TAC(mk_eq(e,t))) (zip evs specs));;

let keccak_abbrevs asl =
  mapfilter (fun (_,th) ->
    let c = concl th in
    let v = rhs c in
    if is_var v && String.length (fst(dest_var v)) > 2 &&
       String.sub (fst(dest_var v)) 0 2 = "E_"
    then (v,lhs c) else failwith "") asl;;

(*** After a step, replace any value that is a lane of the first round ***)

let KECCAK_ABBREV_STEP_TAC =
  let int64_ty = `:int64` in
  W(fun (asl,w) ->
    let s = rand w in
    let evals = map (fun (e,sp) -> (eval64 sp,(e,sp))) (keccak_abbrevs asl) in
    let cands = mapfilter (fun (_,th) ->
       let c = concl th in
       if is_eq c && is_comb(lhs c) && rand(lhs c) = s &&
          type_of(rhs c) = int64_ty && not(is_var(rhs c))
       then let (e,sp) = assoc (eval64(rhs c)) evals in (c,e,sp)
       else failwith "") asl in
    MAP_EVERY (fun (c,e,sp) ->
       let eqth = TRANS (prove(mk_eq(rhs c,sp),KECCAK_BITBLAST_TAC))
                        (ASSUME(mk_eq(sp,e))) in
       FIRST_X_ASSUM(fun th -> if concl th = c then ASSUME_TAC(TRANS th eqth)
                               else failwith "")) cands);;

(*** The final check of the lanes, now in terms of the E_j ***)

let KECCAK_SECOND_ROUND_TAC =
  CONV_TAC(RAND_CONV(REWRITE_CONV
   [ARITH_RULE `2 * (i + 1) = (2 * i + 1) + 1`; keccak])) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && is_list(lhs(concl th))
    then CONV_TAC(RAND_CONV(REWRITE_CONV[GSYM th]))
    else failwith "") THEN
  CONV_TAC(RAND_CONV(RAND_CONV keccak_spec_round_conv)) THEN
  W(fun (asl,w) ->
    REWRITE_TAC(map (fun (e,sp) -> ASSUME(mk_eq(sp,e)))
                    (keccak_abbrevs asl))) THEN
  CONV_TAC(RAND_CONV keccak_spec_round_conv) THEN
  REWRITE_TAC[CONS_11] THEN REPEAT CONJ_TAC THEN KECCAK_BITBLAST_TAC;;


(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for the      *)
(* whole subroutine since the register saves are mixed up with the main      *)
(* code by the compiler, as in the proof of sha3_keccak_f1600_alt2. The      *)
(* loop has its test and branch at the end of the body, as                   *)
(* ENSURES_EVENTS_WHILE_UP2_TAC requires; the events of the last iteration   *)
(* include the branch out of the loop. It is first proved with the address   *)
(* rc of the table as a variable, equal to the address in the image, so that *)
(* the loop is about word rc as in the proof for -O2: the address that the   *)
(* ADRP and ADD compute is replaced by word rc. The other theorems follow    *)
(* from it.                                                                  *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The lanes in row-major order at the head and the end of the loop ***)

let keccak_lanes_str =
 "[read (memory :> bytes64(word_add stackpointer (word 104))) s;
   read X20 s;
   read (memory :> bytes64(word_add stackpointer (word 136))) s;
   read (memory :> bytes64(word_add stackpointer (word 128))) s;
   read X28 s; read X25 s; read X1 s; read X18 s;
   read (memory :> bytes64(word_add stackpointer (word 112))) s;
   read X22 s; read X23 s; read X14 s; read X16 s; read X27 s;
   read (memory :> bytes64(word_add stackpointer (word 120))) s;
   read X30 s; read X17 s; read X6 s; read X5 s; read X13 s;
   read X10 s; read X19 s; read X15 s; read X4 s; read X9 s]";;

let keccak_inv_cs = parse_term ("\\i s.
   read SP s = stackpointer /\\
   read (memory :> bytes64(word_add stackpointer (word 80))) s =
   returnaddress /\\
   read (memory :> bytes64 stackpointer) s = x19_init /\\
   read (memory :> bytes64(word_add stackpointer (word 8))) s = x20_init /\\
   read (memory :> bytes64(word_add stackpointer (word 16))) s = x21_init /\\
   read (memory :> bytes64(word_add stackpointer (word 24))) s = x22_init /\\
   read (memory :> bytes64(word_add stackpointer (word 32))) s = x23_init /\\
   read (memory :> bytes64(word_add stackpointer (word 40))) s = x24_init /\\
   read (memory :> bytes64(word_add stackpointer (word 48))) s = x25_init /\\
   read (memory :> bytes64(word_add stackpointer (word 56))) s = x26_init /\\
   read (memory :> bytes64(word_add stackpointer (word 64))) s = x27_init /\\
   read (memory :> bytes64(word_add stackpointer (word 72))) s = x28_init /\\
   read (memory :> bytes64(word_add stackpointer (word 96))) s =
   word_add (word rc) (word(16 * i)) /\\
   read (memory :> bytes64(word_add stackpointer (word 176))) s =
   word_add (word rc) (word 192) /\\
   read (memory :> bytes64(word_add stackpointer (word 184))) s = a /\\
   read (memory :> bytes(word rc,192)) s = num_of_wordlist round_constants /\\
   " ^ keccak_lanes_str ^ " = keccak (2 * i) A");;

let PERMUTE_CS_INTRO_TAC =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (rc:num) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     APPEND (f_ev_epil a rc pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL 12
          (\i. f_ev_loop a rc pc stackpointer returnaddress i))
        (f_ev_prol a rc pc stackpointer returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[fst MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_EXEC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping (stackpointer:int64,192) (word rc,192)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28`;;

(*** The prologue, given rcth: rc = pc + rodata_mlk_KeccakF_RoundConstants ***)

let PERMUTE_CS_INIT_TAC rcth =
  let wth = SYM(GEN_REWRITE_RULE RAND_CONV [WORD_ADD]
                 (AP_TERM `word:num->int64` rcth)) in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM rcth] o
              MATCH_MP KECCAK_RC_IN_IMAGE) THEN
  BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (a,8 * 25)) s0` THEN
  FIRST_ASSUM(MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[wth]) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_EXEC (4--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[keccak; MULT_CLAUSES; WORD_ADD_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PERMUTE_CS_BODY1_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  GHOST_STATELIST_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MP_TAC(ISPECL [`word rc:int64`; `round_constants`; `24`; `2 * i + 1`;
                 `s0:armstate`] READ_MEMORY_BYTES64_NUM_OF_WORDLIST) THEN
  MP_TAC(ISPECL [`word rc:int64`; `round_constants`; `24`; `2 * i`;
                 `s0:armstate`] READ_MEMORY_BYTES64_NUM_OF_WORDLIST) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[LENGTH_ROUND_CONSTANTS] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 12 ==> 2 * i < 24 /\ 2 * i + 1 < 24`] THEN
  REWRITE_TAC[ARITH_RULE
   `8 * (2 * i) = 16 * i /\ 8 * (2 * i + 1) = 16 * i + 8`] THEN
  REPEAT DISCH_TAC THEN
  KECCAK_INTRO_ABBREVS_TAC THEN
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_EXEC [n] THEN
    KECCAK_ABBREV_STEP_TAC) (1--299);;

let PERMUTE_CS_TEST = prove
 (`!rc i. i < 12
          ==> (val(word_sub (word_add (word rc) (word 192))
                            (word_add (word_add (word rc) (word (16 * i)))
                                      (word 16)):int64) = 0 <=>
               ~(i + 1 < 12))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE
   `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
    word_sub x (word_add y z)`] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `i < 12 ==> 16 * i + 16 < 18446744073709551616`] THEN
  ASM_ARITH_TAC);;

let PERMUTE_CS_BODY2_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s299" THEN
  REWRITE_TAC[MP (SPECL [`rc:num`; `i:num`] PERMUTE_CS_TEST)
                 (ASSUME `i < 12`)] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [KECCAK_SECOND_ROUND_TAC; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PERMUTE_CS_TAIL_TAC =
  REWRITE_TAC[] THEN GHOST_STATELIST_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_EXEC (1--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL_RC =
  prove
 (`exists f_events.
       forall e a rc A pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           rc = pc + rodata_mlk_KeccakF_RoundConstants /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 192),192))
           [word pc,libmlkem_size; a,200] /\
           nonoverlapping (a,200) (word pc,libmlkem_size)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_keccakf1600_permute) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    wordlist_from_memory(a,25) s = A /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    wordlist_from_memory(a,25) s = keccak 24 A /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a rc pc (word_sub stackpointer (word 192))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 192),192;
                          word rc,192]
                         [a,200; word_sub stackpointer (word 192),192]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 192),192)])`,
  PERMUTE_CS_INTRO_TAC THEN
  FIRST_X_ASSUM(fun rcth ->
    if concl rcth = `rc = pc + rodata_mlk_KeccakF_RoundConstants`
    then
      ENSURES_EVENTS_WHILE_UP2_TAC `12` `pc + mlkem_keccakf1600_permute_loop1`
       `pc + mlkem_keccakf1600_permute_loop1_exit`
       keccak_inv_cs THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC;
        PERMUTE_CS_INIT_TAC rcth;
        PERMUTE_CS_BODY1_TAC THEN PERMUTE_CS_BODY2_TAC;
        PERMUTE_CS_TAIL_TAC]
    else NO_TAC));;

(* ------------------------------------------------------------------------- *)
(* The theorems for the code in the image: the combined one, with the table  *)
(* at its address in the image, and from it those of correctness and of      *)
(* constant time and memory safety, which have the same specifications as    *)
(* for -O2.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
       forall e a A pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 192),192))
           [word pc,libmlkem_size; a,200] /\
           nonoverlapping (a,200) (word pc,libmlkem_size)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_keccakf1600_permute) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    wordlist_from_memory(a,25) s = A /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    wordlist_from_memory(a,25) s = keccak 24 A /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a pc (word_sub stackpointer (word 192))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 192),192;
                          word (pc + rodata_mlk_KeccakF_RoundConstants),192]
                         [a,200; word_sub stackpointer (word 192),192]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 192),192)])`,
  X_CHOOSE_TAC
   `f:int64->num->num->int64->int64->(uarch_event)list`
   MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL_RC THEN
  EXISTS_TAC
   `\(a:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      (f:int64->num->num->int64->int64->(uarch_event)list)
      a (pc + rodata_mlk_KeccakF_RoundConstants) pc stackpointer
      returnaddress` THEN
  REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`;
    `pc + rodata_mlk_KeccakF_RoundConstants`; `A:int64 list`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[]);;

(*** Weakening the pre- and postconditions of an ensures ***)

let ENSURES_PREPOST_WEAKEN = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a A pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 192),192))
            [(word pc,libmlkem_size); (a,200)] /\
        nonoverlapping (a,200) (word pc,libmlkem_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_keccakf1600_permute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  wordlist_from_memory(a,25) s = A)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 192),192)])`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `f:int64->num->int64->int64->(uarch_event)list`
   MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `A:int64 list`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 192),192))
           [word pc,libmlkem_size; a,200] /\
           nonoverlapping (a,200) (word pc,libmlkem_size)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_keccakf1600_permute) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a pc (word_sub stackpointer (word 192))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 192),192;
                          word (pc + rodata_mlk_KeccakF_RoundConstants),192]
                         [a,200; word_sub stackpointer (word 192),192]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 192),192)])`,
  MP_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `A:int64 list`
   `wordlist_from_memory(a,25):armstate->int64 list` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `A:int64 list`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The same for the state as a 1600-bit word, read by wbytes, with the       *)
(* permutation keccak_f1600 of common/fips202.ml (see                        *)
(* utils/keccak_fips202.ml), and tactics for callers, which carry the state  *)
(* between calls as 200 bytes.                                               *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/keccak_fips202.ml";;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_F1600 =
  prove
 (`!a (S:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 192),192))
            [(word pc,libmlkem_size); (a,200)] /\
        nonoverlapping (a,200) (word pc,libmlkem_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_keccakf1600_permute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> wbytes a) s = S)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s = keccak_f1600 S)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 192),192)])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `wordlist_of_num 25 (val(S:1600 word)):int64 list`;
                `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_KECCAK] THEN SIMP_TAC[];
    MESON_TAC[KECCAK_F1600_MEMORY]]);;

(*** The state at a as a 1600-bit word, from it as 200 bytes ***)

let KECCAK_STATE_AT_TAC a =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),_)),
           Comb(Const("val",_),_))
        when aa = mk_pair(a,`200`) ->
          ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] th)
    | _ -> NO_TAC);;

(*** Apply ttac to the 1600-bit word for the state at a ***)

let KECCAK_STATE_THEN a (ttac:term->tactic) =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("wbytes",_),aa))),_)),v)
        when aa = a -> ttac v
    | _ -> NO_TAC);;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL_F1600 =
  prove
 (`exists f_events.
       forall e a (S:1600 word) pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 192),192))
           [word pc,libmlkem_size; a,200] /\
           nonoverlapping (a,200) (word pc,libmlkem_size)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_keccakf1600_permute) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read (memory :> wbytes a) s = S /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    read (memory :> wbytes a) s = keccak_f1600 S /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a pc (word_sub stackpointer (word 192))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 192),192;
                          word (pc + rodata_mlk_KeccakF_RoundConstants),192]
                         [a,200; word_sub stackpointer (word 192),192]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 192),192)])`,
  MP_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`;
    `wordlist_of_num 25 (val(S:1600 word)):int64 list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_KECCAK] THEN SIMP_TAC[];
    MESON_TAC[KECCAK_F1600_MEMORY]]);;
