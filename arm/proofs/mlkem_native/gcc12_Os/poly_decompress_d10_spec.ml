(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 10 bits per coefficient. This is the   *)
(* code for mlkem_poly_decompress_d10 from mlkem-native's portable C         *)
(* implementation compiled by gcc 12 with -Os (see mlkem_native/README.md),  *)
(* with a stack protector. It is verified in the whole image (see            *)
(* libmlkem.ml), with the address of the stack guard in the global offset    *)
(* table. As for mlkem_poly_decompress_d5, a loop over groups of 5 bytes     *)
(* unpacks 4 10-bit values into a buffer on the stack, and an inner loop     *)
(* over the 4 values decompresses them. The simulation unrolls the inner     *)
(* loop.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d10:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]  // got_stack_chk_guard
       +0x8: str     x30, [sp, #-32]!
       +0xc: mov     w4, #0x0
      +0x10: mov     w6, #0xd01
      +0x14: ldr     x3, [x2]
      +0x18: str     x3, [sp, #24]
      +0x1c: mov     x3, #0x0
      +0x20: add     x5, sp, #0x10
      +0x24: ldrh    w2, [x1]
      +0x28: ldrb    w3, [x1, #1]
      +0x2c: and     w2, w2, #0x3ff
      +0x30: strh    w2, [sp, #16]
      +0x34: ldrb    w2, [x1, #2]
      +0x38: lsl     w7, w2, #6
      +0x3c: orr     w3, w7, w3, lsr #2
      +0x40: and     w3, w3, #0x3ff
      +0x44: strh    w3, [sp, #18]
      +0x48: ldrb    w3, [x1, #3]
      +0x4c: lsl     w7, w3, #4
      +0x50: ubfx    x3, x3, #6, #16
      +0x54: orr     w2, w7, w2, lsr #4
      +0x58: and     w2, w2, #0x3ff
      +0x5c: strh    w2, [sp, #20]
      +0x60: ldrb    w2, [x1, #4]
      +0x64: orr     w2, w3, w2, lsl #2
      +0x68: mov     x3, #0x0
      +0x6c: strh    w2, [sp, #22]
      +0x70: ldrh    w2, [x5, x3, lsl #1]
      +0x74: add     w7, w4, w3
      +0x78: add     x3, x3, #0x1
      +0x7c: mul     w2, w2, w6
      +0x80: add     w2, w2, #0x200
      +0x84: lsr     w2, w2, #10
      +0x88: strh    w2, [x0, x7, lsl #1]
      +0x8c: cmp     x3, #0x4
      +0x90: b.ne    <mlkem_poly_decompress_d10+0x70>
      +0x94: add     w4, w4, #0x4
      +0x98: add     x1, x1, #0x5
      +0x9c: cmp     w4, #0x100
      +0xa0: b.ne    <mlkem_poly_decompress_d10+0x24>
      +0xa4: adrp    x0, <page>
      +0xa8: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0xac: ldr     x2, [sp, #24]
      +0xb0: ldr     x1, [x0]
      +0xb4: subs    x2, x2, x1
      +0xb8: mov     x1, #0x0
      +0xbc: b.eq    <mlkem_poly_decompress_d10+0xc4>
      +0xc0: bl      <__stack_chk_fail@plt>
      +0xc4: ldr     x30, [sp], #32
      +0xc8: ret     
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_decompress_d10"];;

(* ------------------------------------------------------------------------- *)
(* The five bytes for four coefficients, as parts of a 40-bit word, and the  *)
(* 10-bit fields in it as parts of the number for the input.                 *)
(* ------------------------------------------------------------------------- *)

let D10_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,320)) s = n /\ i < 64 /\ j < 5
        ==> read (memory :> bytes8(word_add a (word(5 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (40 * i)):40 word) (8 * j,8)`;;

let D10_BYTES = assume_spec D10_BYTES_STMT;;

let D10D_FIELD_STMT =
  `!n i k. k < 4
     ==> val(word_subword (word(n DIV 2 EXP (40 * i)):40 word)
                          (10 * k,10):10 word) =
         (n DIV 2 EXP (10 * (4 * i + k))) MOD 1024`;;

let D10D_FIELD = assume_spec D10D_FIELD_STMT;;

(*** A property of all 10-bit words follows from that of the words of each
 *** number below 1024 ***)

let FORALL_WORD10_STMT =
  `!P:10 word->bool. (!m. m < 1024 ==> P(word m)) ==> !g. P g`;;

let FORALL_WORD10 = assume_spec FORALL_WORD10_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 10 in                          *)
(* common/fips203/fips203.ml, the result for a 10-bit field y is the integer *)
(* closest to 3329 * y / 1024, rounding up on ties, i.e.                     *)
(* (3329 * y + 512) DIV 1024. The code reads the address of the stack guard  *)
(* from the global offset table and checks the copy of the guard on the      *)
(* stack before returning, as for mlkem_poly_compress_d4.                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,512); (a,320); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,512); (word_sub stackpointer (word 32),32)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem_poly_decompress_d10) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(a,320)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (10 * i)) MOD 2 EXP 10 +
                                512) DIV 1024))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer
                                                  (word 32),32)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_poly_compress_d4.                                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,512; a,320; word_sub stackpointer (word 32),32] /\
       ALLPAIRS nonoverlapping
        [r,512; word_sub stackpointer (word 32),32]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem_poly_decompress_d10) /\
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
                     [a,320; r,512; word_sub stackpointer (word 32),32;
                      word(pc + got_stack_chk_guard),8; guard,8]
                     [r,512; word_sub stackpointer (word 32),32]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,512);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
