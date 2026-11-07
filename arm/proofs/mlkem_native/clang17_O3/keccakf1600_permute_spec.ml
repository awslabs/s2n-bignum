(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation.                                                 *)
(* This is the code for mlkem_keccakf1600_permute from mlkem-native's        *)
(* portable C implementation compiled by clang 17 with -O3 (see              *)
(* mlkem_native/README.md). Like the gcc code it does two rounds in each     *)
(* iteration of its loop and reads the round constants from the table in the *)
(* read-only data, but it computes the address of the table inside the loop, *)
(* keeps the round counter 2 * i in a register, and spills several lanes to  *)
(* the stack. It is verified in the whole image (see libmlkem.ml), with the  *)
(* same theorems as for gcc, including those for the state as a 1600-bit     *)
(* word, with keccak_f1600 of common/fips202.ml.                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;
needs "arm/proofs/utils/keccak_spec.ml";;

(*** The code in the image:

    mlkem_keccakf1600_permute:
      +0x0: sub     sp, sp, #0xd0
      +0x4: stp     x29, x30, [sp, #112]
      +0x8: stp     x28, x27, [sp, #128]
      +0xc: stp     x26, x25, [sp, #144]
     +0x10: stp     x24, x23, [sp, #160]
     +0x14: stp     x22, x21, [sp, #176]
     +0x18: stp     x20, x19, [sp, #192]
     +0x1c: ldp     x10, x27, [x0, #24]
     +0x20: mov     x14, xzr
     +0x24: str     x0, [sp, #8]
     +0x28: ldr     x8, [x0, #56]
     +0x2c: ldr     x9, [x0, #16]
     +0x30: ldp     x23, x4, [x0]
     +0x34: stp     x8, x10, [sp, #80]
     +0x38: ldp     x8, x1, [x0, #64]
     +0x3c: ldp     x22, x24, [x0, #40]
     +0x40: ldp     x3, x26, [x0, #80]
     +0x44: stp     x8, x9, [sp, #96]
     +0x48: ldp     x29, x2, [x0, #96]
     +0x4c: ldp     x28, x17, [x0, #112]
     +0x50: ldp     x19, x5, [x0, #128]
     +0x54: ldp     x30, x7, [x0, #144]
     +0x58: ldp     x21, x6, [x0, #160]
     +0x5c: ldp     x15, x20, [x0, #176]
     +0x60: ldr     x9, [x0, #192]
     +0x64: stp     x28, x17, [sp, #56]
     +0x68: mov     x18, x22
     +0x6c: eor     x10, x22, x23
     +0x70: eor     x11, x3, x17
     +0x74: ldp     x17, x22, [sp, #80]
     +0x78: eor     x10, x10, x11
     +0x7c: eor     x12, x24, x4
     +0x80: ldr     x8, [sp, #104]
     +0x84: eor     x0, x29, x5
     +0x88: eor     x25, x26, x19
     +0x8c: stp     x26, x27, [sp, #40]
     +0x90: eor     x12, x12, x25
     +0x94: eor     x25, x2, x30
     +0x98: eor     x11, x17, x8
     +0x9c: ldr     x8, [sp, #96]
     +0xa0: eor     x11, x11, x0
     +0xa4: eor     x26, x1, x27
     +0xa8: eor     x27, x28, x7
     +0xac: eor     x10, x10, x21
     +0xb0: eor     x0, x8, x22
     +0xb4: eor     x11, x11, x15
     +0xb8: eor     x0, x0, x25
     +0xbc: eor     x25, x26, x27
     +0xc0: eor     x0, x0, x20
     +0xc4: eor     x13, x25, x9
     +0xc8: eor     x12, x12, x6
     +0xcc: adrp    x16, <page>
     +0xd0: add     x16, x16, #0x780  // rodata_mlk_KeccakF_RoundConstants
     +0xd4: eor     x26, x12, x0, ror #63
     +0xd8: eor     x25, x10, x11, ror #63
     +0xdc: eor     x28, x11, x13, ror #63
     +0xe0: eor     x27, x0, x10, ror #63
     +0xe4: eor     x11, x26, x29
     +0xe8: add     x0, x16, x14, lsl #3
     +0xec: str     x14, [sp, #72]
     +0xf0: eor     x10, x25, x24
     +0xf4: eor     x30, x28, x30
     +0xf8: eor     x14, x27, x9
     +0xfc: eor     x24, x13, x12, ror #63
    +0x100: ror     x9, x11, #21
    +0x104: eor     x23, x24, x23
    +0x108: ldp     x11, x12, [x0]
    +0x10c: ror     x29, x10, #20
    +0x110: ror     x10, x30, #43
    +0x114: ror     x30, x14, #50
    +0x118: eor     x15, x26, x15
    +0x11c: eor     x7, x27, x7
    +0x120: eor     x2, x28, x2
    +0x124: eor     x11, x11, x23
    +0x128: bic     x13, x9, x29
    +0x12c: bic     x14, x30, x10
    +0x130: bic     x0, x23, x30
    +0x134: eor     x13, x11, x13
    +0x138: eor     x11, x14, x9
    +0x13c: bic     x9, x10, x9
    +0x140: eor     x14, x28, x22
    +0x144: eor     x22, x10, x0
    +0x148: eor     x10, x25, x19
    +0x14c: eor     x19, x9, x29
    +0x150: eor     x9, x24, x3
    +0x154: eor     x0, x27, x1
    +0x158: ror     x14, x14, #36
    +0x15c: ror     x15, x15, #3
    +0x160: ror     x1, x10, #19
    +0x164: bic     x10, x29, x23
    +0x168: ror     x3, x9, #61
    +0x16c: ror     x23, x0, #44
    +0x170: str     x12, [sp, #16]
    +0x174: bic     x9, x14, x15
    +0x178: bic     x0, x15, x1
    +0x17c: eor     x12, x10, x30
    +0x180: eor     x10, x9, x1
    +0x184: bic     x29, x1, x3
    +0x188: eor     x1, x0, x3
    +0x18c: eor     x30, x25, x4
    +0x190: bic     x0, x3, x23
    +0x194: eor     x3, x24, x21
    +0x198: eor     x16, x26, x17
    +0x19c: eor     x0, x0, x14
    +0x1a0: eor     x29, x29, x23
    +0x1a4: ror     x21, x30, #63
    +0x1a8: ror     x7, x7, #56
    +0x1ac: ror     x3, x3, #46
    +0x1b0: bic     x14, x23, x14
    +0x1b4: ror     x23, x2, #39
    +0x1b8: ror     x16, x16, #58
    +0x1bc: eor     x14, x14, x15
    +0x1c0: eor     x5, x26, x5
    +0x1c4: bic     x2, x21, x3
    +0x1c8: eor     x6, x25, x6
    +0x1cc: eor     x2, x2, x7
    +0x1d0: bic     x15, x7, x23
    +0x1d4: bic     x7, x3, x7
    +0x1d8: ror     x4, x5, #49
    +0x1dc: eor     x30, x7, x23
    +0x1e0: bic     x7, x23, x16
    +0x1e4: eor     x23, x24, x18
    +0x1e8: ror     x6, x6, #62
    +0x1ec: ldp     x9, x18, [sp, #40]
    +0x1f0: stp     x10, x11, [sp, #24]
    +0x1f4: ror     x23, x23, #28
    +0x1f8: eor     x17, x25, x9
    +0x1fc: eor     x9, x7, x21
    +0x200: eor     x7, x27, x18
    +0x204: eor     x18, x28, x20
    +0x208: eor     x20, x15, x16
    +0x20c: bic     x16, x16, x21
    +0x210: ror     x17, x17, #54
    +0x214: ror     x18, x18, #8
    +0x218: ror     x15, x7, #37
    +0x21c: eor     x7, x16, x3
    +0x220: eor     x16, x28, x8
    +0x224: ldr     x8, [sp, #56]
    +0x228: bic     x5, x17, x23
    +0x22c: bic     x3, x18, x4
    +0x230: eor     x5, x5, x15
    +0x234: eor     x21, x3, x17
    +0x238: ror     x16, x16, #9
    +0x23c: eor     x3, x27, x8
    +0x240: ldr     x8, [sp, #104]
    +0x244: bic     x27, x15, x18
    +0x248: bic     x15, x23, x15
    +0x24c: bic     x17, x4, x17
    +0x250: eor     x27, x27, x4
    +0x254: eor     x26, x26, x8
    +0x258: ldr     x8, [sp, #64]
    +0x25c: ror     x3, x3, #25
    +0x260: eor     x18, x15, x18
    +0x264: eor     x17, x17, x23
    +0x268: eor     x24, x24, x8
    +0x26c: ror     x25, x26, #2
    +0x270: bic     x4, x3, x16
    +0x274: eor     x8, x22, x10
    +0x278: mov     x10, x12
    +0x27c: ror     x24, x24, #23
    +0x280: eor     x26, x4, x25
    +0x284: bic     x15, x24, x3
    +0x288: bic     x23, x6, x24
    +0x28c: eor     x4, x15, x16
    +0x290: bic     x15, x25, x6
    +0x294: bic     x16, x16, x25
    +0x298: eor     x3, x23, x3
    +0x29c: eor     x28, x15, x24
    +0x2a0: eor     x15, x16, x6
    +0x2a4: eor     x16, x0, x5
    +0x2a8: eor     x6, x9, x26
    +0x2ac: eor     x23, x17, x29
    +0x2b0: eor     x24, x4, x19
    +0x2b4: eor     x16, x16, x6
    +0x2b8: eor     x6, x23, x24
    +0x2bc: eor     x23, x6, x20
    +0x2c0: eor     x6, x3, x1
    +0x2c4: eor     x24, x30, x21
    +0x2c8: eor     x25, x28, x2
    +0x2cc: eor     x6, x6, x24
    +0x2d0: eor     x8, x25, x8
    +0x2d4: eor     x24, x7, x12
    +0x2d8: eor     x25, x18, x15
    +0x2dc: eor     x16, x16, x13
    +0x2e0: eor     x6, x6, x11
    +0x2e4: eor     x24, x24, x25
    +0x2e8: eor     x8, x8, x27
    +0x2ec: eor     x24, x24, x14
    +0x2f0: eor     x25, x16, x6, ror #63
    +0x2f4: eor     x16, x8, x16, ror #63
    +0x2f8: eor     x8, x23, x8, ror #63
    +0x2fc: eor     x6, x6, x24, ror #63
    +0x300: eor     x29, x25, x29
    +0x304: eor     x30, x8, x30
    +0x308: eor     x27, x6, x27
    +0x30c: eor     x15, x16, x15
    +0x310: eor     x23, x24, x23, ror #63
    +0x314: ror     x24, x29, #20
    +0x318: ldr     x11, [sp, #16]
    +0x31c: ror     x29, x30, #21
    +0x320: ror     x27, x27, #43
    +0x324: ror     x30, x15, #50
    +0x328: eor     x13, x23, x13
    +0x32c: eor     x12, x11, x13
    +0x330: eor     x9, x23, x9
    +0x334: bic     x15, x29, x24
    +0x338: eor     x14, x16, x14
    +0x33c: eor     x11, x12, x15
    +0x340: bic     x12, x30, x27
    +0x344: eor     x12, x12, x29
    +0x348: ror     x9, x9, #61
    +0x34c: bic     x29, x27, x29
    +0x350: ror     x14, x14, #44
    +0x354: eor     x15, x29, x24
    +0x358: eor     x10, x16, x10
    +0x35c: str     x12, [sp, #104]
    +0x360: bic     x12, x13, x30
    +0x364: eor     x12, x12, x27
    +0x368: bic     x13, x24, x13
    +0x36c: eor     x27, x13, x30
    +0x370: ror     x10, x10, #37
    +0x374: str     x11, [sp, #64]
    +0x378: ldr     x11, [sp, #24]
    +0x37c: str     x12, [sp, #88]
    +0x380: eor     x12, x25, x17
    +0x384: eor     x17, x8, x3
    +0x388: eor     x3, x6, x22
    +0x38c: bic     x22, x9, x14
    +0x390: eor     x11, x6, x11
    +0x394: ror     x12, x12, #19
    +0x398: ror     x17, x17, #3
    +0x39c: ror     x3, x3, #36
    +0x3a0: ror     x11, x11, #9
    +0x3a4: bic     x13, x17, x12
    +0x3a8: eor     x22, x22, x3
    +0x3ac: eor     x13, x13, x9
    +0x3b0: bic     x9, x12, x9
    +0x3b4: eor     x24, x9, x14
    +0x3b8: eor     x9, x25, x19
    +0x3bc: bic     x14, x14, x3
    +0x3c0: str     x13, [sp, #80]
    +0x3c4: bic     x13, x3, x17
    +0x3c8: eor     x12, x13, x12
    +0x3cc: eor     x13, x23, x26
    +0x3d0: ror     x9, x9, #63
    +0x3d4: str     x12, [sp, #96]
    +0x3d8: eor     x12, x16, x18
    +0x3dc: eor     x18, x8, x1
    +0x3e0: eor     x1, x6, x2
    +0x3e4: ror     x13, x13, #46
    +0x3e8: eor     x16, x16, x7
    +0x3ec: ror     x12, x12, #56
    +0x3f0: ror     x18, x18, #58
    +0x3f4: ror     x2, x1, #39
    +0x3f8: eor     x1, x14, x17
    +0x3fc: bic     x14, x13, x12
    +0x400: bic     x17, x2, x18
    +0x404: eor     x29, x14, x2
    +0x408: bic     x14, x12, x2
    +0x40c: bic     x2, x9, x13
    +0x410: eor     x3, x17, x9
    +0x414: eor     x26, x14, x18
    +0x418: bic     x9, x18, x9
    +0x41c: eor     x14, x8, x21
    +0x420: eor     x18, x6, x28
    +0x424: eor     x2, x2, x12
    +0x428: eor     x12, x25, x20
    +0x42c: eor     x28, x9, x13
    +0x430: eor     x9, x23, x0
    +0x434: ror     x13, x14, #49
    +0x438: ror     x14, x18, #8
    +0x43c: eor     x0, x23, x5
    +0x440: ror     x12, x12, #54
    +0x444: ldr     x23, [sp, #64]
    +0x448: ror     x9, x9, #28
    +0x44c: bic     x5, x10, x14
    +0x450: bic     x18, x13, x12
    +0x454: eor     x30, x5, x13
    +0x458: bic     x13, x14, x13
    +0x45c: eor     x19, x18, x9
    +0x460: eor     x5, x13, x12
    +0x464: bic     x12, x12, x9
    +0x468: eor     x13, x25, x4
    +0x46c: eor     x17, x12, x10
    +0x470: ldr     x12, [sp, #32]
    +0x474: bic     x9, x9, x10
    +0x478: eor     x7, x9, x14
    +0x47c: mov     x4, x15
    +0x480: ror     x13, x13, #62
    +0x484: eor     x8, x8, x12
    +0x488: ror     x12, x16, #25
    +0x48c: ror     x16, x0, #23
    +0x490: ror     x8, x8, #2
    +0x494: bic     x9, x12, x11
    +0x498: bic     x14, x13, x16
    +0x49c: bic     x10, x16, x12
    +0x4a0: eor     x15, x14, x12
    +0x4a4: ldr     x14, [sp, #72]
    +0x4a8: bic     x12, x8, x13
    +0x4ac: eor     x21, x9, x8
    +0x4b0: bic     x8, x11, x8
    +0x4b4: eor     x20, x12, x16
    +0x4b8: cmp     x14, #0x16
    +0x4bc: add     x14, x14, #0x2
    +0x4c0: eor     x6, x10, x11
    +0x4c4: eor     x9, x8, x13
    +0x4c8: b.cc    loop1
    +0x4cc: ldr     x8, [sp, #8]
    +0x4d0: ldr     x11, [sp, #104]
    +0x4d4: ldr     x10, [sp, #88]
    +0x4d8: stp     x23, x4, [x8]
    +0x4dc: stp     x27, x22, [x8, #32]
    +0x4e0: stp     x11, x10, [x8, #16]
    +0x4e4: ldr     x10, [sp, #80]
    +0x4e8: stp     x3, x26, [x8, #80]
    +0x4ec: stp     x29, x2, [x8, #96]
    +0x4f0: stp     x24, x10, [x8, #48]
    +0x4f4: ldr     x10, [sp, #96]
    +0x4f8: stp     x28, x17, [x8, #112]
    +0x4fc: stp     x19, x5, [x8, #128]
    +0x500: stp     x30, x7, [x8, #144]
    +0x504: stp     x21, x6, [x8, #160]
    +0x508: stp     x15, x20, [x8, #176]
    +0x50c: ldp     x20, x19, [sp, #192]
    +0x510: stp     x10, x1, [x8, #64]
    +0x514: ldp     x22, x21, [sp, #176]
    +0x518: str     x9, [x8, #192]
    +0x51c: ldp     x24, x23, [sp, #160]
    +0x520: ldp     x26, x25, [sp, #144]
    +0x524: ldp     x28, x27, [sp, #128]
    +0x528: ldp     x29, x30, [sp, #112]
    +0x52c: add     sp, sp, #0xd0
    +0x530: ret
 ***)

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_keccakf1600_permute"];;

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
  let d = layout "rodata_mlk_KeccakF_RoundConstants" in
  let l = mk_list(fst(chop_list 192 (snd(chop_list d
            (dest_list(rhs(concl mlkem_native_libmlkem_clang17_O3_mc)))))),
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
        aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_clang17_O3_mc
        ==> read (memory :> bytes(word(pc + rodata_mlk_KeccakF_RoundConstants),
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
 "[read X23 s; read X4 s;
   read (memory :> bytes64(word_add stackpointer (word 104))) s;
   read (memory :> bytes64(word_add stackpointer (word 88))) s;
   read X27 s; read X22 s; read X24 s;
   read (memory :> bytes64(word_add stackpointer (word 80))) s;
   read (memory :> bytes64(word_add stackpointer (word 96))) s;
   read X1 s; read X3 s; read X26 s; read X29 s; read X2 s; read X28 s;
   read X17 s; read X19 s; read X5 s; read X30 s; read X7 s;
   read X21 s; read X6 s; read X15 s; read X20 s; read X9 s]";;

let keccak_inv_cs = parse_term ("\\i s.
   read SP s = stackpointer /\\
   read X14 s = word(2 * i) /\\
   read (memory :> bytes64(word_add stackpointer (word 8))) s = a /\\
   read (memory :> bytes64(word_add stackpointer (word 112))) s = x29_init /\\
   read (memory :> bytes64(word_add stackpointer (word 120))) s =
   returnaddress /\\
   read (memory :> bytes64(word_add stackpointer (word 128))) s = x28_init /\\
   read (memory :> bytes64(word_add stackpointer (word 136))) s = x27_init /\\
   read (memory :> bytes64(word_add stackpointer (word 144))) s = x26_init /\\
   read (memory :> bytes64(word_add stackpointer (word 152))) s = x25_init /\\
   read (memory :> bytes64(word_add stackpointer (word 160))) s = x24_init /\\
   read (memory :> bytes64(word_add stackpointer (word 168))) s = x23_init /\\
   read (memory :> bytes64(word_add stackpointer (word 176))) s = x22_init /\\
   read (memory :> bytes64(word_add stackpointer (word 184))) s = x21_init /\\
   read (memory :> bytes64(word_add stackpointer (word 192))) s = x20_init /\\
   read (memory :> bytes64(word_add stackpointer (word 200))) s = x19_init /\\
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
  REWRITE_TAC[fst MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_EXEC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping (stackpointer:int64,208) (word rc,192)`
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
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

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
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_EXEC (1--25) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[keccak; MULT_CLAUSES; WORD_ADD_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The address of the pair of round constants, from the counter 2 * i ***)

let SHL3_LEMMA_STMT =
  `word_shl (word (2 * i):int64) 3 = word (16 * i)`;;

let SHL3_LEMMA = assume_spec SHL3_LEMMA_STMT;;

let PERMUTE_CS_BODY1_TAC_N rcth nmax =
  let wth = SYM(GEN_REWRITE_RULE RAND_CONV [WORD_ADD]
                 (AP_TERM `word:num->int64` rcth)) in
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
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_EXEC [n] THEN
    (if n = 28 then
       MLKEM_NATIVE_ADRP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[wth])
     else if n = 34 then RULE_ASSUM_TAC(REWRITE_RULE[SHL3_LEMMA])
     else ALL_TAC) THEN
    KECCAK_ABBREV_STEP_TAC) (1--nmax);;

let PERMUTE_CS_BODY1_TAC rcth = PERMUTE_CS_BODY1_TAC_N rcth 282;;

let PERMUTE_CS_TEST_STMT =
  `!i. i < 12 ==> (val(word (2 * i):int64) < 22 <=> i + 1 < 12)`;;

let PERMUTE_CS_TEST = assume_spec PERMUTE_CS_TEST_STMT;;

let PERMUTE_CS_BODY2_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s282" THEN
  REWRITE_TAC[MP (SPEC `i:num` PERMUTE_CS_TEST) (ASSUME `i < 12`)] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [KECCAK_SECOND_ROUND_TAC; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PERMUTE_CS_TAIL_TAC =
  REWRITE_TAC[] THEN GHOST_STATELIST_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_EXEC (1--26) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_RC_STMT =
  `exists f_events.
       forall e a rc A pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           rc = pc + rodata_mlk_KeccakF_RoundConstants /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 208),208))
           [word pc,libmlkem_size; a,200] /\
           nonoverlapping (a,200) (word pc,libmlkem_size)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
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
                         f_events a rc pc (word_sub stackpointer (word 208))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 208),208;
                          word rc,192]
                         [a,200; word_sub stackpointer (word 208),208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 208),208)])`;;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_RC =
  assume_spec MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_RC_STMT;;

(* ------------------------------------------------------------------------- *)
(* The theorems for the code in the image: the combined one, with the table  *)
(* at its address in the image, and from it those of correctness and of      *)
(* constant time and memory safety, which have the same specifications as    *)
(* for -O2.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a A pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 208),208))
           [word pc,libmlkem_size; a,200] /\
           nonoverlapping (a,200) (word pc,libmlkem_size)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
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
                         f_events a pc (word_sub stackpointer (word 208))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 208),208;
                          word (pc + rodata_mlk_KeccakF_RoundConstants),192]
                         [a,200; word_sub stackpointer (word 208),208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 208),208)])`;;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT;;

(*** Weakening the pre- and postconditions of an ensures ***)

let ENSURES_PREPOST_WEAKEN = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a A pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 208),208))
            [(word pc,libmlkem_size); (a,200)] /\
        nonoverlapping (a,200) (word pc,libmlkem_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
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
                memory :> bytes(word_sub stackpointer (word 208),208)])`;;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 208),208))
           [word pc,libmlkem_size; a,200] /\
           nonoverlapping (a,200) (word pc,libmlkem_size)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
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
                         f_events a pc (word_sub stackpointer (word 208))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 208),208;
                          word (pc + rodata_mlk_KeccakF_RoundConstants),192]
                         [a,200; word_sub stackpointer (word 208),208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 208),208)])`;;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same for the state as a 1600-bit word, read by wbytes, with the       *)
(* permutation keccak_f1600 of common/fips202.ml (see                        *)
(* utils/keccak_fips202.ml), and tactics for callers, which carry the state  *)
(* between calls as 200 bytes.                                               *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/keccak_fips202.ml";;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_F1600_STMT =
  `!a (S:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 208),208))
            [(word pc,libmlkem_size); (a,200)] /\
        nonoverlapping (a,200) (word pc,libmlkem_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
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
                memory :> bytes(word_sub stackpointer (word 208),208)])`;;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_F1600 =
  assume_spec MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_F1600_STMT;;

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

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_F1600_STMT =
  `exists f_events.
       forall e a (S:1600 word) pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 208),208))
           [word pc,libmlkem_size; a,200] /\
           nonoverlapping (a,200) (word pc,libmlkem_size)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
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
                         f_events a pc (word_sub stackpointer (word 208))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 208),208;
                          word (pc + rodata_mlk_KeccakF_RoundConstants),192]
                         [a,200; word_sub stackpointer (word 208),208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 208),208)])`;;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_F1600 =
  assume_spec MLKEM_NATIVE_KECCAKF1600_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_F1600_STMT;;
