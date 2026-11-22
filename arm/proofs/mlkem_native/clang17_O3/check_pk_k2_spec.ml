(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The modulus check of an ML-KEM-512 encapsulation key. This is the code    *)
(* for mlkem512_check_pk from mlkem-native's portable C implementation       *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md). It decodes    *)
(* the vector of the key from its first 768 bytes into a buffer on the       *)
(* stack, reduces it, encodes it again into another buffer, compares the     *)
(* result in constant time with the key, and zeroes the buffers with memset. *)
(* The comparison is unrolled and vectorized, without a loop: it reads the   *)
(* key and the encoding 32 bytes at a time, XORs them, and combines the      *)
(* results with two accumulators. The function saves its registers,          *)
(* including d8-d15, realigns the stack pointer to 32 bytes, and keeps the   *)
(* buffers above the 32 bytes of the callees; the statements use the stack   *)
(* frame below the incoming stack pointer. It is verified in the whole image *)
(* (see libmlkem.ml), using the theorems for mlkem512_polyvec_frombytes,     *)
(* mlkem512_polyvec_reduce and mlkem512_polyvec_tobytes in the image and     *)
(* assuming the contracts for memset in utils/mlkem_native_libc.ml.          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_frombytes_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_reduce_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_tobytes_k2_spec.ml";;

(*** The code in the image, and the PLT stub for memset:

    mlkem512_check_pk:
       +0x0: stp     d15, d14, [sp, #-128]!
       +0x4: stp     d13, d12, [sp, #16]
       +0x8: stp     d11, d10, [sp, #32]
       +0xc: stp     d9, d8, [sp, #48]
      +0x10: stp     x29, x30, [sp, #64]
      +0x14: str     x28, [sp, #80]
      +0x18: stp     x22, x21, [sp, #96]
      +0x1c: stp     x20, x19, [sp, #112]
      +0x20: add     x29, sp, #0x40
      +0x24: sub     x9, sp, #0x720
      +0x28: and     sp, x9, #0xffffffffffffffe0
      +0x2c: adrp    x8, <page>
      +0x30: mov     x20, x0
      +0x34: add     x0, sp, #0x300
      +0x38: mov     x1, x20
      +0x3c: add     x21, sp, #0x300
      +0x40: ldr     x8, [x8, #4088]
      +0x44: ldr     x8, [x8]
      +0x48: str     x8, [sp, #1816]
      +0x4c: bl      <mlkem512_polyvec_frombytes>
      +0x50: add     x0, sp, #0x300
      +0x54: bl      <mlkem512_polyvec_reduce>
      +0x58: mov     x0, sp
      +0x5c: add     x1, sp, #0x300
      +0x60: mov     x22, sp
      +0x64: bl      <mlkem512_polyvec_tobytes>
      +0x68: ldp     q0, q1, [x20]
      +0x6c: mov     w19, wzr
      +0x70: mov     x0, sp
      +0x74: mov     w1, w19
      +0x78: mov     w2, #0x300
      +0x7c: ldp     q2, q3, [sp]
      +0x80: eor     v2.16b, v2.16b, v0.16b
      +0x84: ldp     q4, q5, [x20, #32]
      +0x88: eor     v0.16b, v3.16b, v1.16b
      +0x8c: ldp     q6, q7, [sp, #32]
      +0x90: eor     v4.16b, v6.16b, v4.16b
      +0x94: ldp     q16, q17, [x20, #64]
      +0x98: eor     v1.16b, v7.16b, v5.16b
      +0x9c: orr     v7.16b, v4.16b, v2.16b
      +0xa0: eor     v4.16b, v4.16b, v2.16b
      +0xa4: ldp     q18, q3, [sp, #64]
      +0xa8: eor     v16.16b, v18.16b, v16.16b
      +0xac: eor     v4.16b, v16.16b, v4.16b
      +0xb0: ldp     q6, q5, [x20, #96]
      +0xb4: eor     v2.16b, v3.16b, v17.16b
      +0xb8: ldp     q19, q20, [sp, #96]
      +0xbc: eor     v6.16b, v19.16b, v6.16b
      +0xc0: orr     v16.16b, v6.16b, v16.16b
      +0xc4: ldp     q18, q17, [x20, #128]
      +0xc8: eor     v3.16b, v20.16b, v5.16b
      +0xcc: orr     v7.16b, v16.16b, v7.16b
      +0xd0: eor     v6.16b, v6.16b, v4.16b
      +0xd4: ldp     q21, q19, [sp, #128]
      +0xd8: eor     v18.16b, v21.16b, v18.16b
      +0xdc: eor     v6.16b, v18.16b, v6.16b
      +0xe0: ldp     q5, q20, [x20, #160]
      +0xe4: eor     v4.16b, v19.16b, v17.16b
      +0xe8: ldp     q16, q22, [sp, #160]
      +0xec: eor     v16.16b, v16.16b, v5.16b
      +0xf0: orr     v18.16b, v16.16b, v18.16b
      +0xf4: ldp     q21, q17, [x20, #192]
      +0xf8: eor     v5.16b, v22.16b, v20.16b
      +0xfc: eor     v16.16b, v16.16b, v6.16b
     +0x100: ldp     q19, q23, [sp, #192]
     +0x104: eor     v19.16b, v19.16b, v21.16b
     +0x108: orr     v18.16b, v19.16b, v18.16b
     +0x10c: ldp     q20, q22, [x20, #224]
     +0x110: eor     v6.16b, v23.16b, v17.16b
     +0x114: orr     v25.16b, v18.16b, v7.16b
     +0x118: eor     v16.16b, v19.16b, v16.16b
     +0x11c: ldp     q24, q21, [sp, #224]
     +0x120: eor     v20.16b, v24.16b, v20.16b
     +0x124: ldp     q17, q23, [x20, #256]
     +0x128: eor     v7.16b, v21.16b, v22.16b
     +0x12c: eor     v22.16b, v20.16b, v16.16b
     +0x130: ldp     q18, q19, [sp, #256]
     +0x134: eor     v17.16b, v18.16b, v17.16b
     +0x138: orr     v20.16b, v17.16b, v20.16b
     +0x13c: ldp     q24, q21, [x20, #288]
     +0x140: eor     v16.16b, v19.16b, v23.16b
     +0x144: eor     v22.16b, v17.16b, v22.16b
     +0x148: ldp     q26, q18, [sp, #288]
     +0x14c: eor     v24.16b, v26.16b, v24.16b
     +0x150: orr     v20.16b, v24.16b, v20.16b
     +0x154: ldp     q19, q23, [x20, #320]
     +0x158: eor     v17.16b, v18.16b, v21.16b
     +0x15c: eor     v22.16b, v24.16b, v22.16b
     +0x160: ldp     q27, q26, [sp, #320]
     +0x164: eor     v19.16b, v27.16b, v19.16b
     +0x168: orr     v20.16b, v19.16b, v20.16b
     +0x16c: ldp     q21, q28, [x20, #352]
     +0x170: eor     v18.16b, v26.16b, v23.16b
     +0x174: orr     v25.16b, v20.16b, v25.16b
     +0x178: eor     v22.16b, v19.16b, v22.16b
     +0x17c: ldp     q24, q27, [sp, #352]
     +0x180: eor     v21.16b, v24.16b, v21.16b
     +0x184: eor     v22.16b, v21.16b, v22.16b
     +0x188: ldp     q23, q26, [x20, #384]
     +0x18c: eor     v19.16b, v27.16b, v28.16b
     +0x190: ldp     q20, q29, [sp, #384]
     +0x194: eor     v23.16b, v20.16b, v23.16b
     +0x198: eor     v22.16b, v23.16b, v22.16b
     +0x19c: ldp     q24, q27, [x20, #416]
     +0x1a0: eor     v20.16b, v29.16b, v26.16b
     +0x1a4: orr     v29.16b, v23.16b, v21.16b
     +0x1a8: ldp     q28, q30, [sp, #416]
     +0x1ac: eor     v24.16b, v28.16b, v24.16b
     +0x1b0: orr     v29.16b, v24.16b, v29.16b
     +0x1b4: ldp     q26, q31, [x20, #448]
     +0x1b8: eor     v21.16b, v30.16b, v27.16b
     +0x1bc: eor     v24.16b, v24.16b, v22.16b
     +0x1c0: ldp     q23, q28, [sp, #448]
     +0x1c4: eor     v23.16b, v23.16b, v26.16b
     +0x1c8: orr     v29.16b, v23.16b, v29.16b
     +0x1cc: ldp     q27, q30, [x20, #480]
     +0x1d0: eor     v22.16b, v28.16b, v31.16b
     +0x1d4: eor     v24.16b, v23.16b, v24.16b
     +0x1d8: ldp     q8, q26, [sp, #480]
     +0x1dc: eor     v27.16b, v8.16b, v27.16b
     +0x1e0: orr     v29.16b, v27.16b, v29.16b
     +0x1e4: ldp     q28, q31, [x20, #512]
     +0x1e8: eor     v23.16b, v26.16b, v30.16b
     +0x1ec: orr     v10.16b, v29.16b, v25.16b
     +0x1f0: eor     v27.16b, v27.16b, v24.16b
     +0x1f4: ldp     q9, q8, [sp, #512]
     +0x1f8: eor     v28.16b, v9.16b, v28.16b
     +0x1fc: eor     v27.16b, v28.16b, v27.16b
     +0x200: ldp     q26, q30, [x20, #544]
     +0x204: eor     v24.16b, v8.16b, v31.16b
     +0x208: ldp     q25, q29, [sp, #544]
     +0x20c: eor     v26.16b, v25.16b, v26.16b
     +0x210: orr     v28.16b, v26.16b, v28.16b
     +0x214: ldp     q9, q31, [x20, #576]
     +0x218: eor     v25.16b, v29.16b, v30.16b
     +0x21c: eor     v27.16b, v26.16b, v27.16b
     +0x220: ldp     q8, q11, [sp, #576]
     +0x224: eor     v8.16b, v8.16b, v9.16b
     +0x228: orr     v28.16b, v8.16b, v28.16b
     +0x22c: ldp     q29, q30, [x20, #608]
     +0x230: eor     v26.16b, v11.16b, v31.16b
     +0x234: eor     v8.16b, v8.16b, v27.16b
     +0x238: ldp     q12, q9, [sp, #608]
     +0x23c: eor     v29.16b, v12.16b, v29.16b
     +0x240: ldp     q31, q11, [x20, #640]
     +0x244: eor     v27.16b, v9.16b, v30.16b
     +0x248: orr     v9.16b, v29.16b, v28.16b
     +0x24c: eor     v29.16b, v29.16b, v8.16b
     +0x250: ldp     q13, q12, [sp, #640]
     +0x254: eor     v31.16b, v13.16b, v31.16b
     +0x258: orr     v9.16b, v31.16b, v9.16b
     +0x25c: ldp     q30, q14, [x20, #672]
     +0x260: eor     v28.16b, v12.16b, v11.16b
     +0x264: eor     v31.16b, v31.16b, v29.16b
     +0x268: ldp     q8, q13, [sp, #672]
     +0x26c: eor     v30.16b, v8.16b, v30.16b
     +0x270: orr     v9.16b, v30.16b, v9.16b
     +0x274: ldp     q11, q12, [x20, #704]
     +0x278: eor     v29.16b, v13.16b, v14.16b
     +0x27c: orr     v9.16b, v9.16b, v10.16b
     +0x280: eor     v30.16b, v30.16b, v31.16b
     +0x284: ldp     q15, q8, [sp, #704]
     +0x288: eor     v11.16b, v15.16b, v11.16b
     +0x28c: eor     v30.16b, v11.16b, v30.16b
     +0x290: ldp     q13, q14, [x20, #736]
     +0x294: eor     v8.16b, v8.16b, v12.16b
     +0x298: ldp     q10, q15, [sp, #736]
     +0x29c: eor     v10.16b, v10.16b, v13.16b
     +0x2a0: orr     v13.16b, v10.16b, v11.16b
     +0x2a4: orr     v13.16b, v0.16b, v13.16b
     +0x2a8: orr     v13.16b, v13.16b, v1.16b
     +0x2ac: orr     v13.16b, v13.16b, v2.16b
     +0x2b0: orr     v13.16b, v13.16b, v3.16b
     +0x2b4: eor     v0.16b, v0.16b, v1.16b
     +0x2b8: orr     v13.16b, v13.16b, v4.16b
     +0x2bc: eor     v0.16b, v0.16b, v2.16b
     +0x2c0: orr     v9.16b, v13.16b, v9.16b
     +0x2c4: orr     v13.16b, v5.16b, v6.16b
     +0x2c8: eor     v0.16b, v0.16b, v3.16b
     +0x2cc: orr     v13.16b, v13.16b, v7.16b
     +0x2d0: eor     v0.16b, v0.16b, v4.16b
     +0x2d4: orr     v13.16b, v13.16b, v16.16b
     +0x2d8: eor     v0.16b, v0.16b, v5.16b
     +0x2dc: orr     v13.16b, v13.16b, v17.16b
     +0x2e0: eor     v0.16b, v0.16b, v6.16b
     +0x2e4: orr     v13.16b, v13.16b, v18.16b
     +0x2e8: eor     v0.16b, v0.16b, v7.16b
     +0x2ec: orr     v13.16b, v13.16b, v19.16b
     +0x2f0: eor     v0.16b, v0.16b, v16.16b
     +0x2f4: orr     v13.16b, v13.16b, v20.16b
     +0x2f8: eor     v0.16b, v0.16b, v17.16b
     +0x2fc: orr     v9.16b, v9.16b, v13.16b
     +0x300: orr     v13.16b, v21.16b, v22.16b
     +0x304: eor     v0.16b, v0.16b, v18.16b
     +0x308: orr     v13.16b, v13.16b, v23.16b
     +0x30c: eor     v0.16b, v0.16b, v19.16b
     +0x310: orr     v13.16b, v13.16b, v24.16b
     +0x314: eor     v0.16b, v0.16b, v20.16b
     +0x318: orr     v13.16b, v13.16b, v25.16b
     +0x31c: eor     v0.16b, v0.16b, v21.16b
     +0x320: orr     v13.16b, v13.16b, v26.16b
     +0x324: eor     v0.16b, v0.16b, v22.16b
     +0x328: orr     v13.16b, v13.16b, v27.16b
     +0x32c: eor     v0.16b, v0.16b, v23.16b
     +0x330: orr     v13.16b, v13.16b, v28.16b
     +0x334: eor     v0.16b, v0.16b, v24.16b
     +0x338: eor     v12.16b, v15.16b, v14.16b
     +0x33c: orr     v13.16b, v13.16b, v29.16b
     +0x340: eor     v0.16b, v0.16b, v25.16b
     +0x344: orr     v9.16b, v9.16b, v13.16b
     +0x348: orr     v13.16b, v8.16b, v12.16b
     +0x34c: eor     v0.16b, v0.16b, v26.16b
     +0x350: orr     v9.16b, v9.16b, v13.16b
     +0x354: eor     v0.16b, v0.16b, v27.16b
     +0x358: ext     v13.16b, v9.16b, v9.16b, #8
     +0x35c: eor     v0.16b, v0.16b, v28.16b
     +0x360: eor     v0.16b, v0.16b, v29.16b
     +0x364: eor     v0.16b, v0.16b, v8.16b
     +0x368: eor     v30.16b, v10.16b, v30.16b
     +0x36c: eor     v0.16b, v0.16b, v12.16b
     +0x370: orr     v31.8b, v9.8b, v13.8b
     +0x374: eor     v0.16b, v0.16b, v30.16b
     +0x378: fmov    x8, d31
     +0x37c: ext     v1.16b, v0.16b, v0.16b, #8
     +0x380: orr     x8, x8, x8, lsr #32
     +0x384: lsr     x9, x8, #16
     +0x388: eor     v0.8b, v0.8b, v1.8b
     +0x38c: orr     w8, w8, w9
     +0x390: fmov    x9, d0
     +0x394: orr     w8, w8, w8, lsr #8
     +0x398: sub     w8, w19, w8, uxtb
     +0x39c: eor     x9, x9, x9, lsr #32
     +0x3a0: eor     x9, x9, x9, lsr #16
     +0x3a4: lsr     x10, x9, #8
     +0x3a8: eor     w9, w9, w10
     +0x3ac: eor     w8, w9, w8, lsr #16
     +0x3b0: and     w8, w8, #0xff
     +0x3b4: cmp     w8, w9, uxtb
     +0x3b8: mov     w8, #0xfffffffc
     +0x3bc: csel    w20, w19, w8, eq
     +0x3c0: bl      <memset@plt>
     +0x3c4: add     x0, sp, #0x300
     +0x3c8: mov     w1, w19
     +0x3cc: mov     w2, #0x400
     +0x3d0: bl      <memset@plt>
     +0x3d4: adrp    x8, <page>
     +0x3d8: ldr     x8, [x8, #4088]
     +0x3dc: ldr     x9, [sp, #1816]
     +0x3e0: ldr     x8, [x8]
     +0x3e4: cmp     x8, x9
     +0x3e8: b.ne    <mlkem512_check_pk+0x418>
     +0x3ec: mov     w0, w20
     +0x3f0: sub     sp, x29, #0x40
     +0x3f4: ldp     x20, x19, [sp, #112]
     +0x3f8: ldp     x22, x21, [sp, #96]
     +0x3fc: ldp     x29, x30, [sp, #64]
     +0x400: ldp     d9, d8, [sp, #48]
     +0x404: ldp     d11, d10, [sp, #32]
     +0x408: ldp     d13, d12, [sp, #16]
     +0x40c: ldr     x28, [sp, #80]
     +0x410: ldp     d15, d14, [sp], #128
     +0x414: ret
     +0x418: bl      <__stack_chk_fail@plt>

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem512_check_pk"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* The reduced vector, as a list of 16-bit coefficients for the encoding,    *)
(* and the equivalence of its encoding with the key with the 12-bit fields   *)
(* of the key being below 3329.                                              *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_BYTES16_LIST_STMT =
  `!a n (f:num->int16) s:armstate.
        (!i. i < n
             ==> read (memory :> bytes16(word_add a (word(2 * i)))) s = f i)
        ==> read (memory :> bytes(a,2 * n)) s =
            num_of_wordlist(list_of_seq f n)`;;

let CHECKPK_BYTES16_LIST = assume_spec CHECKPK_BYTES16_LIST_STMT;;

let CHECKPK_IVAL_WORD_STMT =
  `!f. f < 32768 ==> ival(word f:int16) = &f`;;

let CHECKPK_IVAL_WORD = assume_spec CHECKPK_IVAL_WORD_STMT;;

let CHECKPK_REDUCED_STMT =
  `!(x:int16) f.
        f < 2 EXP 12 /\ ival x = ival(word f:int16) rem &3329
        ==> x = word(f MOD 3329)`;;

let CHECKPK_REDUCED = assume_spec CHECKPK_REDUCED_STMT;;

let CHECKPK_LIST_PROPS_STMT =
  `!(g:num->num) l.
        LENGTH(list_of_seq (\i. word(g i MOD 3329):int16) l) = l /\
        ALL (\x. val x < 4096) (list_of_seq (\i. word(g i MOD 3329):int16) l)`;;

let CHECKPK_LIST_PROPS = assume_spec CHECKPK_LIST_PROPS_STMT;;

let CHECKPK_REENCODE_STMT =
  `!l n. n < 2 EXP (12 * l)
         ==> (n = num_of_wordlist(MAP (word_zx:int16->12 word)
                    (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                            2 EXP 12) MOD 3329):int16) l)) <=>
              !i. i < l ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329)`;;

let CHECKPK_REENCODE = assume_spec CHECKPK_REENCODE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The comparison, 16 bytes at a time: the bytes of the key and of the       *)
(* encoding are XORed together, and the results ORed into one accumulator    *)
(* (and XORed into another), which is zero if and only if all the chunks     *)
(* agree. The chunks are the 128-bit words at the addresses of the loads.    *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_BYTES128_STMT =
  `!a l k n s:armstate.
        read (memory :> bytes(a,l)) s = n /\ 16 * k + 16 <= l
        ==> read (memory :> bytes128(word_add a (word(16 * k)))) s =
            word((n DIV 2 EXP (128 * k)) MOD 2 EXP 128)`;;

let CHECKPK_BYTES128 = assume_spec CHECKPK_BYTES128_STMT;;

let CHECKPK_MOD_STEP_STMT =
  `!n m k. n MOD 2 EXP (128 * (k + 1)) = m MOD 2 EXP (128 * (k + 1)) <=>
           n MOD 2 EXP (128 * k) = m MOD 2 EXP (128 * k) /\
           (n DIV 2 EXP (128 * k)) MOD 2 EXP 128 =
           (m DIV 2 EXP (128 * k)) MOD 2 EXP 128`;;

let CHECKPK_MOD_STEP = assume_spec CHECKPK_MOD_STEP_STMT;;

let CHECKPK_MOD_ALL_STMT =
 `!n m k. n MOD 2 EXP (128 * k) = m MOD 2 EXP (128 * k) <=>
          !j. j < k ==> (n DIV 2 EXP (128 * j)) MOD 2 EXP 128 =
                        (m DIV 2 EXP (128 * j)) MOD 2 EXP 128`;;

let CHECKPK_MOD_ALL = assume_spec CHECKPK_MOD_ALL_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* address depends on whether the stack pointer is a multiple of 32 or just  *)
(* of 16. The proof uses a variable boff for the offset of the first one.    *)
(* ------------------------------------------------------------------------- *)

let CHECKPK_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let CHECKPK_ALIGNED_16_32 = assume_spec CHECKPK_ALIGNED_16_32_STMT;;

let CHECKPK2_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 48)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 32 else 48)) /\
            aligned 16 (word_add sp (word(if aligned 32 sp then 32 else 48)))`;;

let CHECKPK2_BUFFER_ADDRESS = assume_spec CHECKPK2_BUFFER_ADDRESS_STMT;;

let CHECKPK_BUFFER_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) &&
       can (term_match [] `word_and (word_add stackpointer (word n))
                                    (word m):int64`) (lhs(concl th))
    then SUBST_ALL_TAC th else NO_TAC);;

let CHECKPK_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

(*** The registers d8-d15 are restored from the 64 bits saved ***)

let CHECKPK2_DREG_STMT =
  `!x:int64. word_zx(word_zx x:int128):int64 = x`;;

let CHECKPK2_DREG = assume_spec CHECKPK2_DREG_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset as in                 *)
(* mlkem_native_libc.ml. The first 768 bytes of the key at pk are a number   *)
(* n, and the result is 0 if all the 512 12-bit fields of n are below 3329,  *)
(* which is the modulus check of FIPS 203, and -4 otherwise. The code has no *)
(* loop: the 24 pairs of 128-bit chunks of the key and of the encoding are   *)
(* loaded, XORed and ORed into an accumulator in one run. The accumulator is *)
(* abbreviated by a variable q9 once it is complete, and the fact that it is *)
(* zero if and only if the chunks agree is derived from the loads, and       *)
(* similarly for the XOR accumulator q0. The stack is the 1952 bytes of the  *)
(* function, with the buffers aligned within them, and the 32 used by the    *)
(* callees below them, plus up to 16 bytes of padding.                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

(*** The setup, with the offset of the buffers as boff ***)

let CHECKPK2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `n:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`;
    `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 2000 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 2000):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP CHECKPK2_BUFFER_ADDRESS
          (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
  SUBGOAL_THEN
   `32 <= (if aligned 32 (stackpointer:int64) then 32 else 48) /\
    (if aligned 32 (stackpointer:int64) then 32 else 48) <= 48`
  MP_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`if aligned 32 (stackpointer:int64) then 32 else 48`,
           `boff:num`) THEN
  GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word boff) (word 32):int64 = word(boff - 32)`
  ASSUME_TAC THENL [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word boff) (word 16):int64 = word(boff - 16)`
  ASSUME_TAC THENL [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

(*** The registers d8-d15 are preserved ***)

let CHECKPK2_PRESERVE_TAC =
  MAP_EVERY (fun (n,d) -> ENSURES_PRESERVED_DREG_TAC n d)
   [("d8_init",`D8`); ("d9_init",`D9`); ("d10_init",`D10`);
    ("d11_init",`D11`); ("d12_init",`D12`); ("d13_init",`D13`);
    ("d14_init",`D14`); ("d15_init",`D15`)];;

(*** The regions of the callees, in the form word_add stackpointer
     (word _) ***)

let CHECKPK_FIX_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term (concl th)
    then REWRITE_RULE
          [ASSUME `word_sub (word boff) (word 32):int64 = word(boff - 32)`;
           ASSUME `word_sub (word boff) (word 16):int64 = word(boff - 16)`] th
    else th);;

(*** A call of a callee, whose buffer address is word_add (word_add sp
     b) c ***)

let CHECKPK_CALL_TAC tac args n =
  tac args n THENL [CONV_TAC WORD_RULE; ALL_TAC];;

(*** The reduced vector as a list of coefficients, and its encoding as
     a number ***)

let CHECKPK_L =
 `list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329):int16)
              512`;;

let CHECKPK_M =
 `num_of_wordlist(MAP (word_zx:int16->12 word)
   (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329))
                512))`;;

(*** The buffer of the reduced vector as a list of 16-bit words ***)

let CHECKPK_LIST_TAC s =
  SUBGOAL_THEN (vsubst [s,`s:armstate`]
   `read (memory :> bytes(word_add (word_add stackpointer (word boff))
                          (word 768),1024)) s =
    num_of_wordlist(list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                           2 EXP 12) MOD 3329):int16) 512)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1024 = 2 * 512`] THEN
    MATCH_MP_TAC CHECKPK_BYTES16_LIST THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CHECKPK_REDUCED THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN
     `word_add (word_add (word_add stackpointer (word boff)) (word 768))
               (word (2 * i)):int64 =
      word_add (word_add stackpointer (word boff)) (word (768 + 2 * i))`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The bound on the number of a buffer, for the final comparison of
     the numbers ***)

let CHECKPK2_BOUND a s =
  REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
   (ISPECL [a; `768`; mk_comb(`read memory:armstate->int64->byte`,s)]
           READ_BYTES_BOUND);;

let CHECKPK2_CHUNK_TAC norm a v k =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`768`) && vv = v ->
          let kt = mk_small_numeral k in
          let bth = EQT_ELIM(NUM_REDUCE_CONV (subst [kt,`k:num`]
                      `16 * k + 16 <= 768`)) in
          let lth = SPECL [a; `768`; kt; v; s] CHECKPK_BYTES128 in
          let fth = MP lth (CONJ th bth) in
          let fth = CONV_RULE (DEPTH_CONV NUM_MULT_CONV) fth in
          let fth = REWRITE_RULE[WORD_ADD_0] fth in
          ASSUME_TAC(if norm then CONV_RULE(ONCE_DEPTH_CONV
                                    NORMALIZE_RELATIVE_ADDRESS_CONV) fth
                     else fth)
    | _ -> NO_TAC);;

let CHECKPK2_EXP_THS =
  NUM_REDUCE_CONV `2 EXP 128` ::
  map (fun k -> NUM_REDUCE_CONV (subst [mk_small_numeral k,`k:num`]
                                  `2 EXP (128 * k)`)) (0--47);;

(*** An accumulator after the code that computes it, as a variable ***)

let CHECKPK2_ABBREV_TAC reg nm var =
  W(fun (asl,w) ->
    let big = rhs(concl(snd(find (fun (_,th) ->
      let c = concl th in
      is_eq c &&
      (let l = lhs c in
       (try fst(dest_const(rator(rator l))) = "read" with Failure _ -> false) &&
       rand(rator l) = reg && rand l = mk_var(nm,`:armstate`))) asl))) in
    ABBREV_TAC(mk_eq(mk_var(var,`:int128`),big)));;

(*** The OR accumulator is zero if and only if the 48 chunks of the key
     and of the encoding agree ***)

let CHECKPK2_CHUNK_IFF_TAC =
  REWRITE_TAC[CHECKPK_MOD_ALL] THEN
  CONV_TAC(RAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_128] THEN
  REWRITE_TAC CHECKPK2_EXP_THS THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  EQ_TAC THEN DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    REPEAT CONJ_TAC THEN FIRST (map ACCEPT_TAC ths));;

let CHECKPK2_IFF_TAC s =
  SUBGOAL_THEN
   `q9:int128 = word 0 <=>
    n MOD 2 EXP (128 * 48) = mm MOD 2 EXP (128 * 48)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `q9:int128`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    CHECKPK2_CHUNK_IFF_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `q9:int128 = word 0 <=>
    !i. i < 512 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329`
   ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = `q9:int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(CHECKPK2_BOUND `pk:int64` s) THEN
    MP_TAC(CHECKPK2_BOUND `word_add stackpointer (word boff):int64` s) THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 768 = 128 * 48`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = mk_eq(CHECKPK_M,`mm:num`))) THEN
    MATCH_MP_TAC CHECKPK_REENCODE THEN
    ASM_REWRITE_TAC[ARITH_RULE `12 * 512 = 128 * 48`];
    ALL_TAC];;

(*** The big terms of the accumulators and the 128-bit words are not
     needed once the facts about the accumulators are derived ***)

let CHECKPK2_CLEAN_TAC =
  DISCARD_ASSUMPTIONS_TAC(fun th ->
    let c = concl th in
    (is_eq c && (rand c = `q9:int128` || rand c = `q0:int128`) &&
     not(is_var(lhand c)) &&
     not(try fst(dest_const(rator(rator(lhand c)))) = "read"
         with Failure _ -> false)) ||
    (is_iff c && lhand c = `q9:int128 = word 0` &&
     not(is_forall(rand c))) ||
    can (term_match [] `read (memory :> bytes128 a) s = x`) c);;

(*** The prologue and the calls that decode, reduce and encode the
     vector ***)

let CHECKPK2_PART1_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (1--11) THEN
  CHECKPK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (12--12) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (13--20) THEN
  CHECKPK_CALL_TAC LOCAL_FROMBYTES_TAC [`read X0 s`; `read X1 s`; `n:num`;
                       `pc:num`; `read SP s`; `read X30 s`] 21 THEN
  CHECKPK_FIX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (22--23) THEN
  CHECKPK_CALL_TAC LOCAL_REDUCE_TAC [`read X0 s`;
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`;
    `pc:num`; `read SP s`; `read X30 s`] 24 THEN
  CHECKPK_FIX_TAC THEN
  CHECKPK_LIST_TAC `s24:armstate` THEN CHECKPK_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (25--28) THEN
  CHECKPK_CALL_TAC LOCAL_TOBYTES_TAC [`read X0 s`; `read X1 s`; CHECKPK_L;
                     `pc:num`; `read SP s`; `read X30 s`] 29 THEN
  CHECKPK_FIX_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CHECKPK_LIST_PROPS]);;

(*** The 128-bit words of the key and of the encoding as the loads read
     them, the OR and XOR accumulations, and the result of the check ***)

let CHECKPK2_COMPARE_TAC =
  ABBREV_TAC(mk_eq(`mm:num`,CHECKPK_M)) THEN
  MAP_EVERY (fun k -> CHECKPK2_CHUNK_TAC false `pk:int64` `n:num` k) (0--47) THEN
  MAP_EVERY (fun k ->
    CHECKPK2_CHUNK_TAC true `word_add stackpointer (word boff):int64` `mm:num` k)
    (0--47) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (30--216) THEN
  CHECKPK2_ABBREV_TAC `Q9` "s216" "q9" THEN
  CHECKPK2_IFF_TAC `s216:armstate` THEN
  CHECKPK2_CLEAN_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (217--225) THEN
  CHECKPK2_ABBREV_TAC `Q0` "s225" "q0" THEN
  CHECKPK2_CLEAN_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (226--243);;

(*** The zeroing of the buffers and the return ***)

let CHECKPK2_TAIL_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (244--244) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC 244 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 249 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (250--253) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC 253 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 258 THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (259--259) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (260--275) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[CHECKPK2_DREG];;

let CHECKPK2_FINAL_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) && lhand(concl th) = `q9:int128 = word 0` &&
       is_forall(rand(concl th))
    then REWRITE_TAC[SYM th] else NO_TAC) THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));;

let MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!pk n guard mf ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (pk,768) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(word_sub stackpointer (word 2000),2000)]
         [(pk,768); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem512_check_pk) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [pk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(pk,768)) s = n)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  (if !i. i < 512
                          ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                   then word 0 else word 0xfffffffc))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 2000),2000)])`;;

let MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the corresponding         *)
(* contract for memset. The events depend only on the address of the key,    *)
(* the stack and the image: the comparison is in constant time and the       *)
(* result is selected without a branch. The buffers are kept at their offset *)
(* from the stack pointer as a conditional (32 or 48).                       *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The addresses in the events in the normalized form, as the callees
     give them ***)

let CHECKPK_EV_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let CHECKPK_EV_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE CHECKPK_EV_CONV th else th);;

let CHECKPK_UNABBREV_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> is_eq(concl th) && rhs(concl th) = `boff:num`));;

let CHECKPK2_ALLOWED =
  [`pc:num`; `pk:int64`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

(*** A call of a callee with the events ***)

let CHECKPK2_CALL_TAC name ilist n =
  CHECKPK_EV_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref CHECKPK2_ALLOWED); LABEL_TAC name safety_th]);;

(*** The regions of the callees, with the offset of the buffers as the
     conditional ***)

let CHECKPK_SAFE_FIX_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term (concl th)
    then REWRITE_RULE
          [ASSUME `word_sub (word (if aligned 32 (stackpointer:int64) then 32 else 48)) (word 32):int64 =
                   word((if aligned 32 (stackpointer:int64) then 32 else 48) - 32)`;
           ASSUME `word_sub (word (if aligned 32 (stackpointer:int64) then 32 else 48)) (word 16):int64 =
                   word((if aligned 32 (stackpointer:int64) then 32 else 48) - 16)`] th
    else th);;

(*** The setup of the proof of the events, with the offset of the
     buffers as the conditional ***)

let CHECKPK2_SAFE_INTRO_TAC thms =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (el 0 thms) "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (el 1 thms) "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (el 2 thms) "H_TOBYTES" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 2000):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP CHECKPK2_BUFFER_ADDRESS
          (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
  SUBGOAL_THEN
   `32 <= (if aligned 32 (stackpointer:int64) then 32 else 48) /\
    (if aligned 32 (stackpointer:int64) then 32 else 48) <= 48`
  MP_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word (if aligned 32 (stackpointer:int64) then 32 else 48)) (word 32):int64 =
    word((if aligned 32 (stackpointer:int64) then 32 else 48) - 32)`
  ASSUME_TAC THENL [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (if aligned 32 (stackpointer:int64) then 32 else 48)) (word 16):int64 =
    word((if aligned 32 (stackpointer:int64) then 32 else 48) - 16)`
  ASSUME_TAC THENL [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

(*** The setup of the proof with the result and the events, with the
     offset of the buffers as the abbreviation boff ***)

let CHECKPK2_FULL_INTRO_TAC thms =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (el 0 thms) "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (el 1 thms) "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (el 2 thms) "H_TOBYTES" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 2000):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP CHECKPK2_BUFFER_ADDRESS
          (ASSUME `aligned 16 (stackpointer:int64)`)) THEN
  SUBGOAL_THEN
   `32 <= (if aligned 32 (stackpointer:int64) then 32 else 48) /\
    (if aligned 32 (stackpointer:int64) then 32 else 48) <= 48`
  MP_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `boff = if aligned 32 (stackpointer:int64) then 32 else 48` THEN
  STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word boff) (word 32):int64 = word(boff - 32)`
  ASSUME_TAC THENL [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word boff) (word 16):int64 = word(boff - 16)`
  ASSUME_TAC THENL [MATCH_MP_TAC WORD_SUB2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

(*** The reduced vector as a list, with the address of its buffer in
     the normalized form of the events ***)

let CHECKPK_LIST_FLAT_TAC s =
  SUBGOAL_THEN (vsubst [s,`s:armstate`]
   `read (memory :> bytes(word_add stackpointer (word (boff + 768)),1024))
         s =
    num_of_wordlist(list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                           2 EXP 12) MOD 3329):int16) 512)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1024 = 2 * 512`] THEN
    MATCH_MP_TAC CHECKPK_BYTES16_LIST THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CHECKPK_REDUCED THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN
     `word_add (word_add stackpointer (word (boff + 768))) (word (2 * i)):int64 =
      word_add stackpointer (word ((boff + 768) + 2 * i))`
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let CHECKPK2_SAFE_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (1--11) THEN
  CHECKPK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (12--12) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (13--20) THEN
  CHECKPK2_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 21 THEN
  CHECKPK_SAFE_FIX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (22--23) THEN
  CHECKPK2_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
    `read X30 s`] 24 THEN
  CHECKPK_SAFE_FIX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (25--28) THEN
  CHECKPK2_CALL_TAC "H_TOBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`; `read SP s`;
    `read X30 s`] 29 THEN
  CHECKPK_SAFE_FIX_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (30--243) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (244--244) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC 244 THEN
  CHECKPK_EV_NORMALIZE_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref CHECKPK2_ALLOWED) 249 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (250--253) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC 253 THEN
  CHECKPK_EV_NORMALIZE_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref CHECKPK2_ALLOWED) 258 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (259--259) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (260--275) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[CHECKPK2_DREG] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
   memset_safety_contract mf ea el ev
   ==> exists f_events.
        forall e pk guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (pk,768) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(word_sub stackpointer (word 2000),2000)]
           [(pk,768); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem512_check_pk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk guard mf pc
                              (word_sub stackpointer (word 2000))
                              returnaddress /\
                       memaccess_inbounds e2
                        [pk,768; word_sub stackpointer (word 2000),2000;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         ea,el]
                        [word_sub stackpointer (word 2000),2000]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 2000),2000)])`;;

let MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof: the result   *)
(* of the check together with the events. It uses the combined theorems for  *)
(* the callees. The offset boff of the buffers is an abbreviation of the     *)
(* conditional, which is restored before the events are matched, so that     *)
(* they are a function of the stack pointer.                                 *)
(* ------------------------------------------------------------------------- *)

(*** The variables that the events may depend on ***)

let CHECKPK2_FULL_ALLOWED = CHECKPK2_ALLOWED @ [`boff:num`];;

let CHECKPK2_FULL_CALL_TAC name ilist n =
  CHECKPK_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref CHECKPK2_FULL_ALLOWED); LABEL_TAC name safety_th]);;

let CHECKPK2_FULL_PART1_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (1--11) THEN
  CHECKPK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (12--12) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (13--20) THEN
  CHECKPK2_FULL_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `n:num`; `pc:num`;
    `read SP s`; `read X30 s`] 21 THEN
  CHECKPK_FIX_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (22--23) THEN
  CHECKPK2_FULL_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`;
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`;
    `pc:num`; `read SP s`; `read X30 s`] 24 THEN
  CHECKPK_FIX_TAC THEN
  CHECKPK_LIST_FLAT_TAC `s24:armstate` THEN CHECKPK_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (25--28) THEN
  CHECKPK2_FULL_CALL_TAC "H_TOBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; CHECKPK_L; `pc:num`;
    `read SP s`; `read X30 s`] 29 THEN
  CHECKPK_FIX_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CHECKPK_LIST_PROPS]);;

let CHECKPK2_FULL_TAIL_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (244--244) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC 244 THEN
  CHECKPK_EV_NORMALIZE_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref CHECKPK2_FULL_ALLOWED) 249 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (250--253) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC 253 THEN
  CHECKPK_EV_NORMALIZE_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref CHECKPK2_FULL_ALLOWED) 258 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (259--259) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_EXEC (260--275) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[CHECKPK2_DREG];;

let CHECKPK2_FULL_FINAL_TAC =
  CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = `q9:int128 = word 0` &&
         is_forall(rand(concl th))
      then REWRITE_TAC[SYM th] else NO_TAC) THEN
    W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
    CHECKPK_UNABBREV_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
   memset_safety_contract mf ea el ev
   ==> exists f_events.
        forall e pk n guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (pk,768) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(word_sub stackpointer (word 2000),2000)]
           [(pk,768); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem512_check_pk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(pk,768)) s = n /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if !i. i < 512
                            ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329
                     then word 0 else word 0xfffffffc) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk guard mf pc
                              (word_sub stackpointer (word 2000))
                              returnaddress /\
                       memaccess_inbounds e2
                        [pk,768; word_sub stackpointer (word 2000),2000;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         ea,el]
                        [word_sub stackpointer (word 2000),2000]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 2000),2000)])`;;

let MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_CHECK_PK_K2_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT;;
