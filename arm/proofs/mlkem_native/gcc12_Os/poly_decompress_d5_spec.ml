(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 5 bits per coefficient. This is the    *)
(* code for mlkem_poly_decompress_d5 from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -Os (see mlkem_native/README.md),  *)
(* with a stack protector. It is verified in the whole image (see            *)
(* libmlkem.ml), with the address of the stack guard in the global offset    *)
(* table. Unlike the code at -O2 it is not vectorized: a loop over groups    *)
(* of 5 bytes unpacks 8 5-bit values into a buffer on the stack, and an      *)
(* inner loop over the 8 values decompresses them. The simulation unrolls    *)
(* the inner loop.                                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d5:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]  // got_stack_chk_guard
       +0x8: str     x30, [sp, #-32]!
       +0xc: mov     w4, #0x0
      +0x10: mov     w6, #0xd01
      +0x14: ldr     x3, [x2]
      +0x18: str     x3, [sp, #24]
      +0x1c: mov     x3, #0x0
      +0x20: add     x5, sp, #0x10
      +0x24: ldrb    w3, [x1]
      +0x28: and     w2, w3, #0x1f
      +0x2c: strb    w2, [sp, #16]
      +0x30: ldrb    w2, [x1, #1]
      +0x34: lsl     w7, w2, #3
      +0x38: orr     w3, w7, w3, lsr #5
      +0x3c: and     w3, w3, #0x1f
      +0x40: strb    w3, [sp, #17]
      +0x44: ubfx    x3, x2, #2, #5
      +0x48: strb    w3, [sp, #18]
      +0x4c: ldrb    w3, [x1, #2]
      +0x50: lsl     w7, w3, #1
      +0x54: orr     w2, w7, w2, lsr #7
      +0x58: and     w2, w2, #0x1f
      +0x5c: strb    w2, [sp, #19]
      +0x60: ldrb    w2, [x1, #3]
      +0x64: lsl     w7, w2, #4
      +0x68: orr     w3, w7, w3, lsr #4
      +0x6c: and     w3, w3, #0x1f
      +0x70: strb    w3, [sp, #20]
      +0x74: ubfx    x3, x2, #1, #5
      +0x78: strb    w3, [sp, #21]
      +0x7c: ldrb    w3, [x1, #4]
      +0x80: lsl     w7, w3, #2
      +0x84: lsr     w3, w3, #3
      +0x88: orr     w2, w7, w2, lsr #6
      +0x8c: strb    w3, [sp, #23]
      +0x90: and     w2, w2, #0x1f
      +0x94: mov     x3, #0x0
      +0x98: strb    w2, [sp, #22]
      +0x9c: ldrb    w2, [x3, x5]
      +0xa0: add     w7, w4, w3
      +0xa4: add     x3, x3, #0x1
      +0xa8: mul     w2, w2, w6
      +0xac: add     w2, w2, #0x10
      +0xb0: lsr     w2, w2, #5
      +0xb4: strh    w2, [x0, x7, lsl #1]
      +0xb8: cmp     x3, #0x8
      +0xbc: b.ne    <mlkem_poly_decompress_d5+0x9c>
      +0xc0: add     w4, w4, #0x8
      +0xc4: add     x1, x1, #0x5
      +0xc8: cmp     w4, #0x100
      +0xcc: b.ne    <mlkem_poly_decompress_d5+0x24>
      +0xd0: adrp    x0, <page>
      +0xd4: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0xd8: ldr     x2, [sp, #24]
      +0xdc: ldr     x1, [x0]
      +0xe0: subs    x2, x2, x1
      +0xe4: mov     x1, #0x0
      +0xe8: b.eq    <mlkem_poly_decompress_d5+0xf0>
      +0xec: bl      <__stack_chk_fail@plt>
      +0xf0: ldr     x30, [sp], #32
      +0xf4: ret     
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_decompress_d5"];;

(* ------------------------------------------------------------------------- *)
(* The five bytes for eight coefficients, as parts of a 40-bit word, and the *)
(* 5-bit fields in it as parts of the number for the input.                  *)
(* ------------------------------------------------------------------------- *)

let D5_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,160)) s = n /\ i < 32 /\ j < 5
        ==> read (memory :> bytes8(word_add a (word(5 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (40 * i)):40 word) (8 * j,8)`;;

let D5_BYTES = assume_spec D5_BYTES_STMT;;

let D5D_FIELD_STMT =
  `!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (40 * i)):40 word)
                          (5 * k,5):5 word) =
         (n DIV 2 EXP (5 * (8 * i + k))) MOD 32`;;

let D5D_FIELD = assume_spec D5D_FIELD_STMT;;

(*** A property of all 5-bit words follows from that of the words of each
 *** number below 32 ***)

let FORALL_WORD5_STMT =
  `!P:5 word->bool. (!m. m < 32 ==> P(word m)) ==> !g. P g`;;

let FORALL_WORD5 = assume_spec FORALL_WORD5_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 5 in                           *)
(* common/fips203/fips203.ml, the result for a 5-bit field y is the integer  *)
(* closest to 3329 * y / 32, rounding up on ties, i.e. (3329 * y + 16) DIV   *)
(* 32. The code reads the address of the stack guard from the global offset  *)
(* table and checks the copy of the guard on the stack before returning, as  *)
(* for mlkem_poly_compress_d4.                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,512); (a,160); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,512); (word_sub stackpointer (word 32),32)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem_poly_decompress_d5) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(a,160)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (5 * i)) MOD 2 EXP 5 +
                                16) DIV 32))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer
                                                  (word 32),32)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_poly_compress_d4.                                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,512; a,160; word_sub stackpointer (word 32),32] /\
       ALLPAIRS nonoverlapping
        [r,512; word_sub stackpointer (word 32),32]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem_poly_decompress_d5) /\
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
                           (word_sub stackpointer (word 32)) returnaddress /\
                    memaccess_inbounds e2
                     [a,160; r,512; word_sub stackpointer (word 32),32;
                      word(pc + got_stack_chk_guard),8; guard,8]
                     [r,512; word_sub stackpointer (word 32),32]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,512);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
