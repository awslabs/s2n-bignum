(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation.                                                 *)
(* This is the code for mldsa_keccakf1600_permute from mldsa-native's        *)
(* portable C implementation compiled by gcc 12 with -Os (see                *)
(* mldsa_native/README.md). Unlike the hand-written kernels, it reads its    *)
(* table of round constants from the read-only data rather than taking it    *)
(* as an argument. Its loop does two rounds in each of 12 iterations, with   *)
(* the 25 lanes of the state in registers and on the stack and the round     *)
(* counter on the stack. It uses a stack frame of 224 bytes. It is verified  *)
(* in the whole image (see libmldsa.ml), with the same theorems as for       *)
(* -O2, including those for the state as a 1600-bit word, with keccak_f1600  *)
(* of common/fips202/fips202.ml.                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_keccak.ml";;
needs "arm/proofs/utils/keccak_spec.ml";;
needs "arm/proofs/utils/keccak_f1600.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_keccakf1600_permute:
       +0x0: stp     x19, x20, [sp, #-224]!
       +0x4: adrp    x2, <page>
       +0x8: ldp     x17, x1, [x0]
       +0xc: str     x30, [sp, #80]
      +0x10: str     x1, [sp, #104]
      +0x14: ldp     x1, x30, [x0, #16]
      +0x18: str     x1, [sp, #112]
      +0x1c: ldr     x1, [x0, #32]
      +0x20: str     x1, [sp, #120]
      +0x24: ldr     x1, [x0, #40]
      +0x28: str     x1, [sp, #128]
      +0x2c: ldr     x1, [x0, #64]
      +0x30: stp     x21, x22, [sp, #16]
      +0x34: stp     x23, x24, [sp, #32]
      +0x38: add     x24, x2, #0xdb8  // rodata_mld_KeccakF_RoundConstants
      +0x3c: stp     x25, x26, [sp, #48]
      +0x40: stp     x27, x28, [sp, #64]
      +0x44: str     x1, [sp, #136]
      +0x48: ldr     x1, [x0, #120]
      +0x4c: ldp     x16, x15, [x0, #48]
      +0x50: ldp     x14, x4, [x0, #72]
      +0x54: ldp     x21, x9, [x0, #88]
      +0x58: ldp     x3, x10, [x0, #104]
      +0x5c: str     x1, [sp, #144]
      +0x60: ldp     x18, x8, [x0, #128]
      +0x64: str     wzr, [sp, #156]
      +0x68: ldp     x13, x7, [x0, #144]
      +0x6c: ldp     x6, x22, [x0, #160]
      +0x70: ldp     x12, x5, [x0, #176]
      +0x74: ldr     x1, [x0, #192]
      +0x78: eor     x11, x21, x18
      +0x7c: ldr     x2, [sp, #144]
      +0x80: eor     x20, x10, x7
      +0x84: add     x24, x24, #0x10
      +0x88: eor     x19, x4, x2
      +0x8c: ldr     x2, [sp, #128]
      +0x90: eor     x2, x17, x2
      +0x94: eor     x19, x19, x2
      +0x98: ldr     x2, [sp, #104]
      +0x9c: eor     x19, x19, x6
      +0xa0: eor     x2, x2, x16
      +0xa4: eor     x11, x11, x2
      +0xa8: ldr     x2, [sp, #112]
      +0xac: eor     x11, x11, x22
      +0xb0: eor     x26, x2, x15
      +0xb4: eor     x2, x9, x8
      +0xb8: eor     x26, x26, x2
      +0xbc: ldr     x2, [sp, #136]
      +0xc0: eor     x26, x26, x12
      +0xc4: eor     x25, x30, x2
      +0xc8: eor     x2, x3, x13
      +0xcc: eor     x25, x25, x2
      +0xd0: ldr     x2, [sp, #120]
      +0xd4: eor     x25, x25, x5
      +0xd8: eor     x2, x2, x14
      +0xdc: eor     x2, x2, x20
      +0xe0: eor     x20, x19, x26, ror #63
      +0xe4: eor     x2, x2, x1
      +0xe8: eor     x19, x25, x19, ror #63
      +0xec: eor     x23, x2, x11, ror #63
      +0xf0: eor     x16, x20, x16
      +0xf4: eor     x11, x11, x25, ror #63
      +0xf8: eor     x2, x26, x2, ror #63
      +0xfc: ldur    x25, [x24, #-16]
     +0x100: eor     x9, x11, x9
     +0x104: eor     x17, x23, x17
     +0x108: mvn     x26, x16, ror #20
     +0x10c: eor     x13, x2, x13
     +0x110: eor     x25, x17, x25
     +0x114: and     x26, x26, x9, ror #21
     +0x118: eor     x14, x19, x14
     +0x11c: eor     x26, x26, x25
     +0x120: mvn     x25, x9, ror #21
     +0x124: eor     x1, x19, x1
     +0x128: ror     x28, x13, #43
     +0x12c: and     x13, x25, x13, ror #43
     +0x130: ror     x14, x14, #44
     +0x134: eor     x13, x13, x16, ror #20
     +0x138: eor     x4, x23, x4
     +0x13c: str     x13, [sp, #160]
     +0x140: mvn     x13, x28
     +0x144: eor     x30, x2, x30
     +0x148: ror     x27, x1, #50
     +0x14c: and     x1, x13, x1, ror #50
     +0x150: mvn     x13, x14
     +0x154: eor     x18, x20, x18
     +0x158: eor     x1, x1, x9, ror #21
     +0x15c: eor     x12, x11, x12
     +0x160: ror     x9, x4, #61
     +0x164: and     x4, x13, x4, ror #61
     +0x168: eor     x15, x11, x15
     +0x16c: eor     x4, x4, x30, ror #36
     +0x170: stp     x1, x4, [sp, #168]
     +0x174: bic     x1, x17, x27
     +0x178: mvn     x4, x18, ror #19
     +0x17c: eor     x28, x1, x28
     +0x180: and     x4, x4, x12, ror #3
     +0x184: ror     x1, x30, #36
     +0x188: eor     x4, x4, x9
     +0x18c: bic     x1, x14, x1
     +0x190: str     x4, [sp, #184]
     +0x194: mvn     x4, x12, ror #3
     +0x198: eor     x12, x1, x12, ror #3
     +0x19c: and     x30, x4, x30, ror #36
     +0x1a0: ldr     x1, [sp, #104]
     +0x1a4: eor     x4, x30, x18, ror #19
     +0x1a8: eor     x3, x2, x3
     +0x1ac: mvn     x17, x17
     +0x1b0: and     x16, x17, x16, ror #20
     +0x1b4: ror     x15, x15, #58
     +0x1b8: str     x4, [sp, #192]
     +0x1bc: eor     x4, x20, x1
     +0x1c0: eor     x7, x19, x7
     +0x1c4: eor     x6, x23, x6
     +0x1c8: eor     x27, x16, x27
     +0x1cc: mvn     x17, x15
     +0x1d0: mvn     x13, x9
     +0x1d4: ror     x16, x3, #39
     +0x1d8: and     x13, x13, x18, ror #19
     +0x1dc: and     x3, x17, x3, ror #39
     +0x1e0: mvn     x17, x16
     +0x1e4: ror     x1, x4, #63
     +0x1e8: eor     x13, x13, x14
     +0x1ec: ror     x9, x6, #46
     +0x1f0: bic     x1, x15, x1
     +0x1f4: ror     x14, x7, #56
     +0x1f8: and     x7, x17, x7, ror #56
     +0x1fc: eor     x1, x1, x9
     +0x200: eor     x7, x7, x15
     +0x204: str     x7, [sp, #200]
     +0x208: mvn     x7, x14
     +0x20c: str     x1, [sp, #208]
     +0x210: ldr     x1, [sp, #120]
     +0x214: and     x6, x7, x6, ror #46
     +0x218: mvn     x7, x9
     +0x21c: eor     x3, x3, x4, ror #63
     +0x220: and     x4, x7, x4, ror #63
     +0x224: eor     x21, x20, x21
     +0x228: eor     x4, x4, x14
     +0x22c: eor     x14, x19, x1
     +0x230: ldr     x1, [sp, #128]
     +0x234: eor     x6, x6, x16
     +0x238: eor     x8, x11, x8
     +0x23c: ror     x15, x21, #54
     +0x240: eor     x1, x23, x1
     +0x244: eor     x5, x2, x5
     +0x248: ror     x9, x8, #49
     +0x24c: mvn     x16, x1, ror #28
     +0x250: ror     x7, x14, #37
     +0x254: and     x21, x16, x21, ror #54
     +0x258: mvn     x7, x7
     +0x25c: eor     x16, x21, x14, ror #37
     +0x260: str     x16, [sp, #216]
     +0x264: mvn     x16, x15
     +0x268: eor     x10, x19, x10
     +0x26c: and     x8, x16, x8, ror #49
     +0x270: mvn     x16, x9
     +0x274: eor     x8, x8, x1, ror #28
     +0x278: and     x16, x16, x5, ror #8
     +0x27c: and     x1, x7, x1, ror #28
     +0x280: eor     x18, x16, x15
     +0x284: mvn     x15, x5, ror #8
     +0x288: eor     x5, x1, x5, ror #8
     +0x28c: ldr     x1, [sp, #112]
     +0x290: eor     x20, x20, x22
     +0x294: and     x14, x15, x14, ror #37
     +0x298: mvn     x15, x10, ror #25
     +0x29c: eor     x11, x11, x1
     +0x2a0: eor     x14, x14, x9
     +0x2a4: ldr     x1, [sp, #136]
     +0x2a8: eor     x2, x2, x1
     +0x2ac: ldr     x1, [sp, #144]
     +0x2b0: mvn     x9, x2, ror #9
     +0x2b4: and     x9, x9, x10, ror #25
     +0x2b8: eor     x7, x23, x1
     +0x2bc: ror     x1, x20, #62
     +0x2c0: eor     x9, x9, x11, ror #2
     +0x2c4: and     x15, x15, x7, ror #23
     +0x2c8: eor     x25, x15, x2, ror #9
     +0x2cc: mvn     x15, x7, ror #23
     +0x2d0: and     x20, x15, x20, ror #62
     +0x2d4: mvn     x15, x1
     +0x2d8: and     x15, x15, x11, ror #2
     +0x2dc: mvn     x11, x11, ror #2
     +0x2e0: and     x2, x11, x2, ror #9
     +0x2e4: eor     x7, x15, x7, ror #23
     +0x2e8: eor     x2, x2, x1
     +0x2ec: eor     x10, x20, x10, ror #25
     +0x2f0: ldp     x1, x15, [sp, #176]
     +0x2f4: eor     x17, x5, x2
     +0x2f8: ldur    x23, [x24, #-8]
     +0x2fc: eor     x19, x26, x1
     +0x300: ldr     x1, [sp, #216]
     +0x304: eor     x1, x3, x1
     +0x308: eor     x19, x19, x1
     +0x30c: ldr     x1, [sp, #160]
     +0x310: eor     x19, x19, x9
     +0x314: eor     x11, x1, x13
     +0x318: ldr     x1, [sp, #200]
     +0x31c: eor     x1, x1, x8
     +0x320: eor     x11, x11, x1
     +0x324: ldr     x1, [sp, #168]
     +0x328: eor     x11, x11, x25
     +0x32c: eor     x16, x1, x15
     +0x330: eor     x1, x6, x18
     +0x334: eor     x16, x16, x1
     +0x338: ldr     x1, [sp, #192]
     +0x33c: eor     x16, x16, x10
     +0x340: eor     x15, x28, x1
     +0x344: eor     x1, x4, x14
     +0x348: eor     x15, x15, x1
     +0x34c: eor     x22, x19, x16, ror #63
     +0x350: ldr     x1, [sp, #208]
     +0x354: eor     x15, x15, x7
     +0x358: eor     x13, x13, x22
     +0x35c: eor     x19, x15, x19, ror #63
     +0x360: eor     x1, x12, x1
     +0x364: eor     x2, x2, x19
     +0x368: eor     x1, x1, x17
     +0x36c: mvn     x17, x13, ror #20
     +0x370: eor     x1, x1, x27
     +0x374: eor     x12, x12, x19
     +0x378: eor     x20, x1, x11, ror #63
     +0x37c: eor     x11, x11, x15, ror #63
     +0x380: eor     x6, x6, x11
     +0x384: eor     x1, x16, x1, ror #63
     +0x388: eor     x15, x26, x20
     +0x38c: eor     x14, x14, x1
     +0x390: eor     x23, x15, x23
     +0x394: and     x17, x17, x6, ror #21
     +0x398: eor     x17, x17, x23
     +0x39c: mvn     x23, x6, ror #21
     +0x3a0: ror     x21, x14, #43
     +0x3a4: and     x14, x23, x14, ror #43
     +0x3a8: ror     x16, x2, #50
     +0x3ac: eor     x14, x14, x13, ror #20
     +0x3b0: str     x14, [sp, #104]
     +0x3b4: mvn     x14, x21
     +0x3b8: bic     x30, x15, x16
     +0x3bc: and     x2, x14, x2, ror #50
     +0x3c0: mvn     x15, x15
     +0x3c4: and     x13, x15, x13, ror #20
     +0x3c8: eor     x2, x2, x6, ror #21
     +0x3cc: eor     x3, x3, x20
     +0x3d0: ror     x12, x12, #44
     +0x3d4: str     x2, [sp, #112]
     +0x3d8: eor     x2, x13, x16
     +0x3dc: mvn     x13, x12
     +0x3e0: str     x2, [sp, #120]
     +0x3e4: eor     x2, x28, x1
     +0x3e8: eor     x10, x10, x11
     +0x3ec: eor     x8, x8, x22
     +0x3f0: ror     x6, x3, #61
     +0x3f4: and     x3, x13, x3, ror #61
     +0x3f8: ror     x14, x2, #36
     +0x3fc: eor     x3, x3, x2, ror #36
     +0x400: str     x3, [sp, #128]
     +0x404: mvn     x3, x10, ror #3
     +0x408: eor     x4, x4, x1
     +0x40c: and     x2, x3, x2, ror #36
     +0x410: mvn     x16, x6
     +0x414: eor     x2, x2, x8, ror #19
     +0x418: str     x2, [sp, #136]
     +0x41c: ldr     x2, [sp, #160]
     +0x420: and     x16, x16, x8, ror #19
     +0x424: eor     x5, x5, x19
     +0x428: bic     x14, x12, x14
     +0x42c: eor     x3, x2, x22
     +0x430: eor     x16, x16, x12
     +0x434: ldr     x2, [sp, #184]
     +0x438: ror     x12, x4, #39
     +0x43c: eor     x9, x9, x20
     +0x440: mvn     x15, x8, ror #19
     +0x444: eor     x2, x2, x11
     +0x448: ror     x8, x5, #56
     +0x44c: and     x15, x15, x10, ror #3
     +0x450: eor     x14, x14, x10, ror #3
     +0x454: ror     x2, x2, #58
     +0x458: mvn     x13, x2
     +0x45c: ror     x10, x3, #63
     +0x460: and     x4, x13, x4, ror #39
     +0x464: mvn     x13, x12
     +0x468: and     x5, x13, x5, ror #56
     +0x46c: bic     x10, x2, x10
     +0x470: eor     x30, x30, x21
     +0x474: eor     x15, x15, x6
     +0x478: eor     x21, x5, x2
     +0x47c: ror     x6, x9, #46
     +0x480: ldr     x2, [sp, #176]
     +0x484: mvn     x5, x8
     +0x488: and     x9, x5, x9, ror #46
     +0x48c: eor     x10, x10, x6
     +0x490: mvn     x5, x6
     +0x494: eor     x2, x2, x20
     +0x498: ldr     x6, [sp, #200]
     +0x49c: eor     x4, x4, x3, ror #63
     +0x4a0: and     x3, x5, x3, ror #63
     +0x4a4: eor     x13, x27, x19
     +0x4a8: eor     x3, x3, x8
     +0x4ac: eor     x8, x6, x22
     +0x4b0: mvn     x23, x2, ror #28
     +0x4b4: eor     x18, x18, x11
     +0x4b8: eor     x9, x9, x12
     +0x4bc: ror     x12, x8, #54
     +0x4c0: and     x8, x23, x8, ror #54
     +0x4c4: eor     x7, x7, x1
     +0x4c8: eor     x8, x8, x13, ror #37
     +0x4cc: ror     x6, x18, #49
     +0x4d0: str     x8, [sp, #144]
     +0x4d4: ror     x5, x13, #37
     +0x4d8: mvn     x8, x12
     +0x4dc: mvn     x5, x5
     +0x4e0: and     x18, x8, x18, ror #49
     +0x4e4: mvn     x8, x6
     +0x4e8: and     x8, x8, x7, ror #8
     +0x4ec: eor     x18, x18, x2, ror #28
     +0x4f0: and     x2, x5, x2, ror #28
     +0x4f4: eor     x8, x8, x12
     +0x4f8: mvn     x12, x7, ror #8
     +0x4fc: eor     x7, x2, x7, ror #8
     +0x500: ldr     x2, [sp, #168]
     +0x504: eor     x5, x25, x22
     +0x508: and     x13, x12, x13, ror #37
     +0x50c: eor     x11, x2, x11
     +0x510: eor     x13, x13, x6
     +0x514: ldr     x2, [sp, #192]
     +0x518: eor     x1, x2, x1
     +0x51c: ldr     x2, [sp, #208]
     +0x520: mvn     x6, x1, ror #9
     +0x524: eor     x19, x2, x19
     +0x528: ldr     x2, [sp, #216]
     +0x52c: and     x6, x6, x19, ror #25
     +0x530: mvn     x22, x19, ror #25
     +0x534: eor     x6, x6, x11, ror #2
     +0x538: eor     x20, x2, x20
     +0x53c: ror     x2, x5, #62
     +0x540: mvn     x12, x20, ror #23
     +0x544: and     x22, x22, x20, ror #23
     +0x548: and     x5, x12, x5, ror #62
     +0x54c: eor     x22, x22, x1, ror #9
     +0x550: eor     x12, x5, x19, ror #25
     +0x554: mvn     x5, x2
     +0x558: and     x5, x5, x11, ror #2
     +0x55c: mvn     x11, x11, ror #2
     +0x560: and     x1, x11, x1, ror #9
     +0x564: eor     x5, x5, x20, ror #23
     +0x568: eor     x1, x1, x2
     +0x56c: ldr     w2, [sp, #156]
     +0x570: add     w2, w2, #0x2
     +0x574: str     w2, [sp, #156]
     +0x578: cmp     w2, #0x18
     +0x57c: b.ne    <mldsa_keccakf1600_permute+0x78>
     +0x580: ldr     x2, [sp, #104]
     +0x584: stp     x17, x2, [x0]
     +0x588: ldr     x2, [sp, #112]
     +0x58c: str     x2, [x0, #16]
     +0x590: ldr     x2, [sp, #120]
     +0x594: str     x2, [x0, #32]
     +0x598: ldr     x2, [sp, #128]
     +0x59c: str     x2, [x0, #40]
     +0x5a0: ldr     x2, [sp, #136]
     +0x5a4: str     x2, [x0, #64]
     +0x5a8: ldr     x2, [sp, #144]
     +0x5ac: str     x30, [x0, #24]
     +0x5b0: stp     x16, x15, [x0, #48]
     +0x5b4: stp     x14, x4, [x0, #72]
     +0x5b8: stp     x21, x9, [x0, #88]
     +0x5bc: stp     x3, x10, [x0, #104]
     +0x5c0: str     x2, [x0, #120]
     +0x5c4: stp     x18, x8, [x0, #128]
     +0x5c8: stp     x13, x7, [x0, #144]
     +0x5cc: stp     x6, x22, [x0, #160]
     +0x5d0: stp     x12, x5, [x0, #176]
     +0x5d4: str     x1, [x0, #192]
     +0x5d8: ldp     x21, x22, [sp, #16]
     +0x5dc: ldp     x23, x24, [sp, #32]
     +0x5e0: ldp     x25, x26, [sp, #48]
     +0x5e4: ldp     x27, x28, [sp, #64]
     +0x5e8: ldr     x30, [sp, #80]
     +0x5ec: ldp     x19, x20, [sp], #224
     +0x5f0: ret
 ***)



let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_keccakf1600_permute"];;

(* ------------------------------------------------------------------------- *)
(* Reading the round constants from the table in the image.                  *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES64_NUM_OF_WORDLIST_STMT =
  `!a:int64 (l:int64 list) n j s:armstate.
        read (memory :> bytes(a,8 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes64(word_add a (word(8 * j)))) s = EL j l`;;

let READ_MEMORY_BYTES64_NUM_OF_WORDLIST =
  assume_spec READ_MEMORY_BYTES64_NUM_OF_WORDLIST_STMT;;

(*** The 192 bytes of the table, as they are in the image ***)

let KECCAK_RC_IN_IMAGE =
  let d = layout "rodata_mld_KeccakF_RoundConstants" in
  let l = mk_list(fst(chop_list 192 (snd(chop_list d
            (dest_list(rhs(concl mldsa_native_libmldsa_gcc12_Os_mc)))))),
                  `:byte`) in
  let lth = MLDSA_NATIVE_IMAGE_DATA_RULE (REFL l) d
  and lenth = LENGTH_CONV(mk_comb(`LENGTH:byte list->num`,l))
  and nth = prove
   (mk_eq(mk_comb(`num_of_bytelist`,l),`num_of_wordlist round_constants`),
    REWRITE_TAC[round_constants; num_of_bytelist; num_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV) in
  prove
   (`!s pc.
        aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_Os_mc
        ==> read (memory :> bytes(word(pc + rodata_mld_KeccakF_RoundConstants),
                                  192)) s =
            num_of_wordlist round_constants`,
    REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP lth) THEN
    REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; lenth; nth]);;

let LENGTH_ROUND_CONSTANTS_STMT =
  `LENGTH round_constants = 24`;;

let LENGTH_ROUND_CONSTANTS = assume_spec LENGTH_ROUND_CONSTANTS_STMT;;

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
 "[read X17 s;
   read (memory :> bytes64(word_add stackpointer (word 104))) s;
   read (memory :> bytes64(word_add stackpointer (word 112))) s;
   read X30 s;
   read (memory :> bytes64(word_add stackpointer (word 120))) s;
   read (memory :> bytes64(word_add stackpointer (word 128))) s;
   read X16 s; read X15 s;
   read (memory :> bytes64(word_add stackpointer (word 136))) s;
   read X14 s; read X4 s; read X21 s; read X9 s; read X3 s; read X10 s;
   read (memory :> bytes64(word_add stackpointer (word 144))) s;
   read X18 s; read X8 s; read X13 s; read X7 s; read X6 s; read X22 s;
   read X12 s; read X5 s; read X1 s]";;

let keccak_inv_cs = parse_term ("\\i s.
   read SP s = stackpointer /\\
   read X0 s = a /\\
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
   read X24 s = word_add (word rc) (word(16 * i)) /\\
   read (memory :> bytes32(word_add stackpointer (word 156))) s =
   word(2 * i) /\\
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
  REWRITE_TAC[fst MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_EXEC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping (stackpointer:int64,224) (word rc,192)`
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

(*** The prologue, given rcth: rc = pc + rodata_mld_KeccakF_RoundConstants ***)

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
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_EXEC (1--15) THEN
  MLKEM_NATIVE_ADRP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[wth]) THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_EXEC (16--30) THEN
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
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_EXEC [n] THEN
    KECCAK_ABBREV_STEP_TAC) (1--322);;

(*** The counter on the stack after an iteration, and the loop test ***)

let PERMUTE_CS_COUNTER_STMT =
  `!i. i < 12
       ==> word_zx(word_zx(word_add (word_zx(word_zx(word(2 * i):int32):int64):int32)
                                    (word 2)):int64):int32 =
           word(2 * (i + 1))`;;

let PERMUTE_CS_COUNTER = assume_spec PERMUTE_CS_COUNTER_STMT;;

let PERMUTE_CS_TEST_STMT =
  `!i. i < 12
       ==> (val(word_sub (word(2 * (i + 1)):int32) (word 24)) = 0 <=>
            ~(i + 1 < 12))`;;

let PERMUTE_CS_TEST = assume_spec PERMUTE_CS_TEST_STMT;;

let PERMUTE_CS_BODY2_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s322" THEN
  REWRITE_TAC[MP (SPEC `i:num` PERMUTE_CS_COUNTER) (ASSUME `i < 12`)] THEN
  REWRITE_TAC[MP (SPEC `i:num` PERMUTE_CS_TEST) (ASSUME `i < 12`)] THEN
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
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_EXEC (1--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_RC_STMT =
  `exists f_events.
       forall e a rc A pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           rc = pc + rodata_mld_KeccakF_RoundConstants /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 224),224))
           [word pc,libmldsa_size; a,200] /\
           nonoverlapping (a,200) (word pc,libmldsa_size)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa_keccakf1600_permute) /\
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
                         f_events a rc pc (word_sub stackpointer (word 224))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 224),224;
                          word rc,192]
                         [a,200; word_sub stackpointer (word 224),224]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 224),224)])`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_RC =
  assume_spec MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_RC_STMT;;

(* ------------------------------------------------------------------------- *)
(* The theorems for the code in the image: the combined one, with the table  *)
(* at its address in the image, and from it those of correctness and of      *)
(* constant time and memory safety, which have the same specifications as    *)
(* for -O2.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a A pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 224),224))
           [word pc,libmldsa_size; a,200] /\
           nonoverlapping (a,200) (word pc,libmldsa_size)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa_keccakf1600_permute) /\
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
                         f_events a pc (word_sub stackpointer (word 224))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 224),224;
                          word (pc + rodata_mld_KeccakF_RoundConstants),192]
                         [a,200; word_sub stackpointer (word 224),224]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 224),224)])`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(*** Weakening the pre- and postconditions of an ensures ***)

let ENSURES_PREPOST_WEAKEN = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a A pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 224),224))
            [(word pc,libmldsa_size); (a,200)] /\
        nonoverlapping (a,200) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_keccakf1600_permute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  wordlist_from_memory(a,25) s = A)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 224),224)])`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 224),224))
           [word pc,libmldsa_size; a,200] /\
           nonoverlapping (a,200) (word pc,libmldsa_size)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa_keccakf1600_permute) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a pc (word_sub stackpointer (word 224))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 224),224;
                          word (pc + rodata_mld_KeccakF_RoundConstants),192]
                         [a,200; word_sub stackpointer (word 224),224]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 224),224)])`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same for the state as a 1600-bit word, read by wbytes, with the       *)
(* permutation keccak_f1600 of common/fips202/fips202.ml (see                *)
(* utils/keccak_f1600.ml), and tactics for callers, which carry the state  *)
(* between calls as 200 bytes.                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_F1600_STMT =
  `!a (S:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 224),224))
            [(word pc,libmldsa_size); (a,200)] /\
        nonoverlapping (a,200) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_keccakf1600_permute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> wbytes a) s = S)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s = keccak_f1600 S)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 224),224)])`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_F1600 =
  assume_spec MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_F1600_STMT;;

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

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_F1600_STMT =
  `exists f_events.
       forall e a (S:1600 word) pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 224),224))
           [word pc,libmldsa_size; a,200] /\
           nonoverlapping (a,200) (word pc,libmldsa_size)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa_keccakf1600_permute) /\
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
                         f_events a pc (word_sub stackpointer (word 224))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 224),224;
                          word (pc + rodata_mld_KeccakF_RoundConstants),192]
                         [a,200; word_sub stackpointer (word 224),224]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 224),224)])`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_F1600 =
  assume_spec MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_F1600_STMT;;
