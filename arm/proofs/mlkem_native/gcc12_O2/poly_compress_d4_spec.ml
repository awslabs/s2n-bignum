(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 4 bits per coefficient. This is the code   *)
(* for mlkem_poly_compress_d4 from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), with a stack    *)
(* protector. It is verified in the whole image (see                         *)
(* libmlkem.ml), with the address of the stack guard                         *)
(* in the global offset table.                                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d4:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]  // got_stack_chk_guard
       +0x8: str     x30, [sp, #-32]!
       +0xc: mov     x10, x1
      +0x10: mov     w12, #0xafb0
      +0x14: ldr     x1, [x2]
      +0x18: str     x1, [sp, #24]
      +0x1c: mov     x1, #0x0
      +0x20: add     x13, sp, #0x10
      +0x24: movk    w12, #0x13, lsl #16
      +0x28: mov     w11, #0x8000000
      +0x2c: nop
      +0x30: sub     w3, w1, #0x1
      +0x34: mov     x2, #0x1
      +0x38: str     xzr, [sp, #16]
      +0x3c: nop
      +0x40: add     w4, w3, w2
      +0x44: add     x5, x13, x2
      +0x48: add     x2, x2, #0x1
      +0x4c: ldrsh   w4, [x10, x4, lsl #1]
      +0x50: madd    w4, w4, w12, w11
      +0x54: lsr     w4, w4, #28
      +0x58: sturb   w4, [x5, #-1]
      +0x5c: cmp     x2, #0x9
      +0x60: b.ne    <mlkem_poly_compress_d4+0x40>
      +0x64: ldrb    w9, [sp, #16]
      +0x68: add     w1, w1, #0x8
      +0x6c: ldrb    w8, [sp, #18]
      +0x70: add     x0, x0, #0x4
      +0x74: ldrb    w7, [sp, #20]
      +0x78: ldrb    w6, [sp, #22]
      +0x7c: ldrb    w5, [sp, #17]
      +0x80: ldrb    w4, [sp, #19]
      +0x84: ldrb    w3, [sp, #21]
      +0x88: ldrb    w2, [sp, #23]
      +0x8c: orr     w5, w9, w5, lsl #4
      +0x90: orr     w4, w8, w4, lsl #4
      +0x94: sturb   w5, [x0, #-4]
      +0x98: orr     w3, w7, w3, lsl #4
      +0x9c: sturb   w4, [x0, #-3]
      +0xa0: orr     w2, w6, w2, lsl #4
      +0xa4: sturb   w3, [x0, #-2]
      +0xa8: sturb   w2, [x0, #-1]
      +0xac: cmp     w1, #0x100
      +0xb0: b.ne    <mlkem_poly_compress_d4+0x30>
      +0xb4: adrp    x0, <page>
      +0xb8: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0xbc: ldr     x2, [sp, #24]
      +0xc0: ldr     x1, [x0]
      +0xc4: subs    x2, x2, x1
      +0xc8: mov     x1, #0x0
      +0xcc: b.ne    <mlkem_poly_compress_d4+0xd8>
      +0xd0: ldr     x30, [sp], #32
      +0xd4: ret
      +0xd8: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem_poly_compress_d4"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 4 bits, as computed, and the packing  *)
(* of two such values into a byte.                                           *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D4_ARITH_STMT =
  `!v. v < 3329
       ==> (134217728 + v * 1290160) DIV 268435456 =
           (32 * v + 3329) DIV 6658`;;

let COMPRESS_D4_ARITH = assume_spec COMPRESS_D4_ARITH_STMT;;

let COMPRESS_D4_NIBBLE_STMT =
  `!y:int16.
        val y < 3329
        ==> word_ushr
             (word_zx (word_zx
               (word (134217728 +
                      val (word_zx (word_zx (word_sx y:int32):int64):int32) *
                      1290160):int32):int64):int32) 28 =
            word(((32 * val y + 3329) DIV 6658) MOD 16)`;;

let COMPRESS_D4_NIBBLE = assume_spec COMPRESS_D4_NIBBLE_STMT;;

let COMPRESS_D4_BYTE_STMT =
  `!a. a < 16 ==> !b. b < 16 ==>
     val(word_zx(word_zx(word_zx(word_or
      (word_zx(word_zx(word_zx(word_zx(word_zx(word_zx
        (word a:int32):int64):int32):byte):int32):int64):int32)
      (word_shl (word_zx(word_zx(word_zx(word_zx(word_zx(word_zx
        (word b:int32):int64):int32):byte):int32):int64):int32) 4))
      :int64):int32):byte) = a + 16 * b`;;

let COMPRESS_D4_BYTE = assume_spec COMPRESS_D4_BYTE_STMT;;

let COMPRESS_D4_BYTE_ALT =
  REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] COMPRESS_D4_BYTE;;

(* ------------------------------------------------------------------------- *)
(* In the inner loop, which is unrolled in the simulation, tidy up the index *)
(* 8 * i + k of the coefficient (k the iteration of the inner loop) before   *)
(* it is used in the load with a shifted register offset.                    *)
(* ------------------------------------------------------------------------- *)

let compress_d4_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let COMPRESS_D4_INDEX_TAC k =
  let jt = el k compress_d4_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  let mt = mk_comb(`word_zx:int32->int64`,
            mk_comb(mk_comb(`word_add:int32->int32->int32`,
                            `word_zx(word(8 * i):int64):int32`),
                    mk_comb(`word:num->int32`,mk_small_numeral k))) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X4 s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [TRANS_TAC EQ_TRANS mt THEN CONJ_TAC THENL
         [AP_TERM_TAC THEN SPEC_TAC(`word(8 * i):int64`,`w:int64`) THEN
          GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
          WORD_SMALL_TAC];
        DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "COMPRESS_D4_INDEX_TAC");;

let COMPRESS_D4_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--4) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC [5 + 9 * k] THEN
    COMPRESS_D4_INDEX_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC
     ((6 + 9 * k)--(13 + 9 * k))) (0--7) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (77--94);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 4 in common/fips203.ml, the      *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 16 * x / 3329, rounding up on ties, modulo 16, i.e.                       *)
(* ((32 * x + 3329) DIV 6658) MOD 16, and as for mlkem_encode 4 the 4-bit    *)
(* values are put together little-endian. Like the C code, this relies on    *)
(* the coefficients being in [0,3329).                                       *)
(*                                                                           *)
(* The code reads the address of the stack guard from the global offset      *)
(* table (GOT) in the loaded image, which is outside the code and read-only  *)
(* data covered by the image and so is part of the precondition, and checks  *)
(* before returning that the copy of the guard on the stack is still the     *)
(* same, which it is since neither the guard nor the GOT entry is written by *)
(* the code.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,128); (a,512); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,128); (word_sub stackpointer (word 32),32)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem_poly_compress_d4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                     (word_add a (word(2 * i)))) s =
                           x i))
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,128)) s =
                       nsum {i | i < 256}
                            (\i. ((32 * val(x i) + 3329) DIV 6658) MOD 16 *
                                 2 EXP (4 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128);
                         memory :> bytes(word_sub stackpointer
                                                  (word 32),32)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This is stated directly rather     *)
(* than by mk_safety_spec, since besides the arguments the events depend on  *)
(* the address of the stack guard, read from the GOT, which is also read.    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,128; a,512; word_sub stackpointer (word 32),32] /\
       ALLPAIRS nonoverlapping
        [r,128; word_sub stackpointer (word 32),32]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + mlkem_poly_compress_d4) /\
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
                     [a,512; r,128; word_sub stackpointer (word 32),32;
                      word(pc + got_stack_chk_guard),8; guard,8]
                     [r,128; word_sub stackpointer (word 32),32]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,128);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
