(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four Keccak states, with  *)
(* the padding: the statement. This is the code for the static function      *)
(* mld_keccak_absorb_once_x4 from mldsa-native's portable C implementation   *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), where the       *)
(* compiler has made the first byte 0x1F of the padding a constant. It works *)
(* as absorbing on one state does, using mldsa_keccakf1600x4_xor_bytes and   *)
(* mldsa_keccakf1600x4_permute, except that the states are not zeroed first: *)
(* that is done by its callers. Its code is the same as that of              *)
(* mlk_keccak_absorb_once_x4.constprop.0 in the gcc 12 -O2 build of          *)
(* mlkem-native, apart from the addresses, so the statement and proof are    *)
(* those of mlkem_native/gcc12_O2/keccak_absorb_once_x4.ml. It is verified   *)
(* in the whole image (see libmldsa.ml), using the theorems for those        *)
(* functions in the image.                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600x4_xor_bytes_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600x4_permute_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mld_keccak_absorb_once_x4:
       +0x0: stp     x19, x20, [sp, #-96]!
       +0x4: mov     w19, w1
       +0x8: mov     x20, x6
       +0xc: adrp    x7, 1f000 <page>
      +0x10: ldr     x7, [x7, #4088]
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: mov     x21, x2
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: mov     x22, x3
      +0x24: mov     x24, x0
      +0x28: stp     x25, x26, [sp, #48]
      +0x2c: mov     x23, x4
      +0x30: mov     x25, x19
      +0x34: stp     x27, x30, [sp, #64]
      +0x38: mov     x26, x5
      +0x3c: ldr     x1, [x7]
      +0x40: str     x1, [sp, #88]
      +0x44: mov     x1, #0x0
      +0x48: mov     w1, #0x1f
      +0x4c: strb    w1, [sp, #87]
      +0x50: cmp     x19, x6
      +0x54: b.hi    13dc <mld_keccak_absorb_once_x4.constprop.0+0x9c>
      +0x58: mov     x4, x26
      +0x5c: mov     x3, x23
      +0x60: mov     x2, x22
      +0x64: mov     x1, x21
      +0x68: mov     w6, w25
      +0x6c: mov     w5, #0x0
      +0x70: mov     x0, x24
      +0x74: bl      <mldsa_keccakf1600x4_xor_bytes>
      +0x78: mov     x0, x24
      +0x7c: sub     x20, x20, x19
      +0x80: bl      <mldsa_keccakf1600x4_permute>
      +0x84: add     x26, x26, x19
      +0x88: add     x23, x23, x19
      +0x8c: add     x22, x22, x19
      +0x90: add     x21, x21, x19
      +0x94: cmp     x20, x19
      +0x98: b.cs    1398 <mld_keccak_absorb_once_x4.constprop.0+0x58>
      +0x9c: sub     w25, w25, #0x1
      +0xa0: mov     w27, w20
      +0xa4: cbnz    x20, 1468 <mld_keccak_absorb_once_x4.constprop.0+0x128>
      +0xa8: add     x19, sp, #0x57
      +0xac: mov     w5, w27
      +0xb0: mov     x4, x19
      +0xb4: mov     x0, x24
      +0xb8: mov     x3, x19
      +0xbc: mov     x2, x19
      +0xc0: mov     x1, x19
      +0xc4: mov     w6, #0x1
      +0xc8: bl      <mldsa_keccakf1600x4_xor_bytes>
      +0xcc: mov     w5, w25
      +0xd0: mov     x0, x24
      +0xd4: mov     x4, x19
      +0xd8: mov     w7, #0xffffff80
      +0xdc: mov     x2, x4
      +0xe0: mov     x1, x4
      +0xe4: mov     x3, x4
      +0xe8: mov     w6, #0x1
      +0xec: strb    w7, [sp, #87]
      +0xf0: bl      <mldsa_keccakf1600x4_xor_bytes>
      +0xf4: adrp    x0, 1f000 <page>
      +0xf8: ldr     x0, [x0, #4088]
      +0xfc: ldr     x2, [sp, #88]
     +0x100: ldr     x1, [x0]
     +0x104: subs    x2, x2, x1
     +0x108: mov     x1, #0x0
     +0x10c: b.ne    14a8 <mld_keccak_absorb_once_x4.constprop.0+0x168>
     +0x110: ldp     x21, x22, [sp, #16]
     +0x114: ldp     x23, x24, [sp, #32]
     +0x118: ldp     x25, x26, [sp, #48]
     +0x11c: ldp     x27, x30, [sp, #64]
     +0x120: ldp     x19, x20, [sp], #96
     +0x124: ret
     +0x128: mov     x4, x26
     +0x12c: mov     x3, x23
     +0x130: mov     x2, x22
     +0x134: mov     x1, x21
     +0x138: mov     w6, w20
     +0x13c: mov     x0, x24
     +0x140: mov     w5, #0x0
     +0x144: bl      <mldsa_keccakf1600x4_xor_bytes>
     +0x148: cmp     x20, w25, uxtw
     +0x14c: b.ne    13e8 <mld_keccak_absorb_once_x4.constprop.0+0xa8>
     +0x150: ldrb    w7, [sp, #87]
     +0x154: add     x4, sp, #0x57
     +0x158: mov     w5, w20
     +0x15c: mov     x0, x24
     +0x160: orr     w7, w7, #0xffffff80
     +0x164: b       141c <mld_keccak_absorb_once_x4.constprop.0+0xdc>
     +0x168: bl      <__stack_chk_fail@plt>
 ***)

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mld_keccak_absorb_once_x4"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st r m0 m1 m2 m3 mlen M0 M1 M2 M3 guard pc stackpointer
    returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\
        nonoverlapping (st,800) (word_sub stackpointer (word 304),304) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 304),304)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mld_keccak_absorb_once_x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; word r; m0; m1; m2; m3; word mlen] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(st,800)) s = 0 /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb r
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M0 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb r
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M1 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb r
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M2 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb r
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad r 0x1F mlen))
                     (mlen DIV r))
                   (word((M3 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad r 0x1F mlen)) DIV
                         2 EXP (8 * r * mlen DIV r) MOD 2 EXP (8 * r))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 304),304)])`;;

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
