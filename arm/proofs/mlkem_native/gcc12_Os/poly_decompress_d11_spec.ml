(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 11 bits per coefficient. This is the   *)
(* code for mlkem_poly_decompress_d11 from mlkem-native's portable C         *)
(* implementation compiled by gcc 12 with -Os (see mlkem_native/README.md),  *)
(* with a stack protector. It is verified in the whole image (see            *)
(* libmlkem.ml), with the address of the stack guard in the global offset    *)
(* table. As for mlkem_poly_decompress_d5, a loop over groups of 11 bytes    *)
(* unpacks 8 11-bit values into a buffer on the stack, and an inner loop     *)
(* over the 8 values decompresses them. The simulation unrolls the inner     *)
(* loop. The stack frame has 48 bytes.                                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d11:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]  // got_stack_chk_guard
       +0x8: str     x30, [sp, #-48]!
       +0xc: mov     w4, #0x0
      +0x10: mov     w6, #0xd01
      +0x14: ldr     x3, [x2]
      +0x18: str     x3, [sp, #40]
      +0x1c: mov     x3, #0x0
      +0x20: add     x5, sp, #0x18
      +0x24: ldrh    w2, [x1]
      +0x28: ldrb    w3, [x1, #1]
      +0x2c: and     w2, w2, #0x7ff
      +0x30: strh    w2, [sp, #24]
      +0x34: ldrb    w2, [x1, #2]
      +0x38: lsl     w7, w2, #5
      +0x3c: orr     w3, w7, w3, lsr #3
      +0x40: ldrb    w7, [x1, #3]
      +0x44: and     w3, w3, #0x7ff
      +0x48: strh    w3, [sp, #26]
      +0x4c: ldrb    w3, [x1, #4]
      +0x50: lsl     w8, w3, #10
      +0x54: orr     w7, w8, w7, lsl #2
      +0x58: orr     w2, w7, w2, lsr #6
      +0x5c: and     w2, w2, #0x7ff
      +0x60: strh    w2, [sp, #28]
      +0x64: ldrb    w2, [x1, #5]
      +0x68: lsl     w7, w2, #7
      +0x6c: orr     w3, w7, w3, lsr #1
      +0x70: and     w3, w3, #0x7ff
      +0x74: strh    w3, [sp, #30]
      +0x78: ldrb    w3, [x1, #6]
      +0x7c: lsl     w7, w3, #4
      +0x80: orr     w2, w7, w2, lsr #4
      +0x84: ldrb    w7, [x1, #7]
      +0x88: and     w2, w2, #0x7ff
      +0x8c: strh    w2, [sp, #32]
      +0x90: ldrb    w2, [x1, #8]
      +0x94: lsl     w8, w2, #9
      +0x98: orr     w7, w8, w7, lsl #1
      +0x9c: orr     w3, w7, w3, lsr #7
      +0xa0: and     w3, w3, #0x7ff
      +0xa4: strh    w3, [sp, #34]
      +0xa8: ldrb    w3, [x1, #9]
      +0xac: lsl     w7, w3, #6
      +0xb0: ubfx    x3, x3, #5, #16
      +0xb4: orr     w2, w7, w2, lsr #2
      +0xb8: and     w2, w2, #0x7ff
      +0xbc: strh    w2, [sp, #36]
      +0xc0: ldrb    w2, [x1, #10]
      +0xc4: orr     w2, w3, w2, lsl #3
      +0xc8: mov     x3, #0x0
      +0xcc: strh    w2, [sp, #38]
      +0xd0: ldrh    w2, [x5, x3, lsl #1]
      +0xd4: add     w7, w4, w3
      +0xd8: add     x3, x3, #0x1
      +0xdc: mul     w2, w2, w6
      +0xe0: add     w2, w2, #0x400
      +0xe4: lsr     w2, w2, #11
      +0xe8: strh    w2, [x0, x7, lsl #1]
      +0xec: cmp     x3, #0x8
      +0xf0: b.ne    <mlkem_poly_decompress_d11+0xd0>
      +0xf4: add     w4, w4, #0x8
      +0xf8: add     x1, x1, #0xb
      +0xfc: cmp     w4, #0x100
     +0x100: b.ne    <mlkem_poly_decompress_d11+0x24>
     +0x104: adrp    x0, <page>
     +0x108: ldr     x0, [x0, #4088]  // got_stack_chk_guard
     +0x10c: ldr     x2, [sp, #40]
     +0x110: ldr     x1, [x0]
     +0x114: subs    x2, x2, x1
     +0x118: mov     x1, #0x0
     +0x11c: b.eq    <mlkem_poly_decompress_d11+0x124>
     +0x120: bl      <__stack_chk_fail@plt>
     +0x124: ldr     x30, [sp], #48
     +0x128: ret     
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_decompress_d11"];;

(* ------------------------------------------------------------------------- *)
(* The eleven bytes for eight coefficients, as parts of an 88-bit word, and  *)
(* the 11-bit fields in it as parts of the number for the input.             *)
(* ------------------------------------------------------------------------- *)

let D11_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,352)) s = n /\ i < 32 /\ j < 11
        ==> read (memory :> bytes8(word_add a (word(11 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (88 * i)):88 word) (8 * j,8)`;;

let D11_BYTES = assume_spec D11_BYTES_STMT;;

let D11D_FIELD_STMT =
  `!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (88 * i)):88 word)
                          (11 * k,11):11 word) =
         (n DIV 2 EXP (11 * (8 * i + k))) MOD 2048`;;

let D11D_FIELD = assume_spec D11D_FIELD_STMT;;

(*** A property of all 11-bit words follows from that of the words of each
 *** number below 2048 ***)

let FORALL_WORD11_STMT =
  `!P:11 word->bool. (!m. m < 2048 ==> P(word m)) ==> !g. P g`;;

let FORALL_WORD11 = assume_spec FORALL_WORD11_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 11 in                          *)
(* common/fips203/fips203.ml, the result for an 11-bit field y is the        *)
(* integer closest to 3329 * y / 2048, rounding up on ties, i.e.             *)
(* (3329 * y + 1024) DIV 2048. The code reads the address of the stack guard *)
(* from the global offset table and checks the copy of the guard on the      *)
(* stack before returning, as for mlkem_poly_compress_d4.                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,512); (a,352); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
         [(r,512); (word_sub stackpointer (word 48),48)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem_poly_decompress_d11) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(a,352)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (11 * i)) MOD 2 EXP 11 +
                                1024) DIV 2048))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer
                                                  (word 48),48)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_poly_compress_d4.                                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,512; a,352; word_sub stackpointer (word 48),48] /\
       ALLPAIRS nonoverlapping
        [r,512; word_sub stackpointer (word 48),48]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem_poly_decompress_d11) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r guard pc
                           (word_sub stackpointer (word 48)) returnaddress /\
                    memaccess_inbounds e2
                     [a,352; r,512; word_sub stackpointer (word 48),48;
                      word(pc + got_stack_chk_guard),8; guard,8]
                     [r,512; word_sub stackpointer (word 48),48]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,512);
                        memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
