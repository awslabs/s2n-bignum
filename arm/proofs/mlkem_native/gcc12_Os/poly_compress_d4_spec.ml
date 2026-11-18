(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 4 bits per coefficient. This is the code   *)
(* for mlkem_poly_compress_d4 from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -Os (see mlkem_native/README.md), with a stack    *)
(* protector. It is verified in the whole image (see                         *)
(* libmlkem.ml), with the address of the stack guard                         *)
(* in the global offset table.                                               *)
(* The code is not vectorized: an outer loop over groups of 8 coefficients   *)
(* computes their 4-bit values by an inner loop into a buffer on the stack   *)
(* and packs them into bytes. The simulation unrolls the inner loop.         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d4:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]  // got_stack_chk_guard
       +0x8: str     x30, [sp, #-32]!
       +0xc: mov     w6, #0xafb0
      +0x10: mov     w4, #0x0
      +0x14: ldr     x3, [x2]
      +0x18: str     x3, [sp, #24]
      +0x1c: mov     x3, #0x0
      +0x20: add     x5, sp, #0x10
      +0x24: movk    w6, #0x13, lsl #16
      +0x28: mov     w7, #0x8000000
      +0x2c: mov     x2, #0x0
      +0x30: str     xzr, [sp, #16]
      +0x34: add     w3, w4, w2
      +0x38: ldrsh   w3, [x1, x3, lsl #1]
      +0x3c: madd    w3, w3, w6, w7
      +0x40: lsr     w3, w3, #28
      +0x44: strb    w3, [x2, x5]
      +0x48: add     x2, x2, #0x1
      +0x4c: cmp     x2, #0x8
      +0x50: b.ne    <mlkem_poly_compress_d4+0x34>
      +0x54: ldrb    w3, [sp, #16]
      +0x58: add     w4, w4, #0x8
      +0x5c: ldrb    w2, [sp, #17]
      +0x60: add     x0, x0, #0x4
      +0x64: orr     w2, w3, w2, lsl #4
      +0x68: ldrb    w3, [sp, #18]
      +0x6c: sturb   w2, [x0, #-4]
      +0x70: ldrb    w2, [sp, #19]
      +0x74: orr     w2, w3, w2, lsl #4
      +0x78: ldrb    w3, [sp, #20]
      +0x7c: sturb   w2, [x0, #-3]
      +0x80: ldrb    w2, [sp, #21]
      +0x84: orr     w2, w3, w2, lsl #4
      +0x88: ldrb    w3, [sp, #22]
      +0x8c: sturb   w2, [x0, #-2]
      +0x90: ldrb    w2, [sp, #23]
      +0x94: orr     w2, w3, w2, lsl #4
      +0x98: sturb   w2, [x0, #-1]
      +0x9c: cmp     w4, #0x100
      +0xa0: b.ne    <mlkem_poly_compress_d4+0x2c>
      +0xa4: adrp    x0, <page>
      +0xa8: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0xac: ldr     x2, [sp, #24]
      +0xb0: ldr     x1, [x0]
      +0xb4: subs    x2, x2, x1
      +0xb8: mov     x1, #0x0
      +0xbc: b.eq    <mlkem_poly_compress_d4+0xc4>
      +0xc0: bl      <__stack_chk_fail@plt>
      +0xc4: ldr     x30, [sp], #32
      +0xc8: ret     
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_compress_d4"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 4 bits, as computed, and the packing  *)
(* of two such values into a byte.                                         *)
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
(* 8 * i + k of the coefficient (k the iteration of the inner loop) before *)
(* it is used in the load with a shifted register offset.                  *)
(* ------------------------------------------------------------------------- *)

let compress_d4_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let COMPRESS_D4_INDEX_TAC k =
  let jt = el k compress_d4_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X3 s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "COMPRESS_D4_INDEX_TAC");;

(*** The address of the store with a register offset, [x2, x5] with x2 = k
 *** and x5 = sp + 16, is simulated as k + val(sp + 16); rewrite it to the form
 *** that the rest uses ***)

let COMPRESS_D4_ADDRESS_TAC =
  MAP_EVERY (fun k ->
    SUBGOAL_THEN
     (subst [mk_small_numeral k,`k:num`;
             mk_small_numeral(16 + k),`m:num`]
       `word_add (word k) (word (val (word_add stackpointer (word 16)))):int64 =
        word_add stackpointer (word m)`)
     ASSUME_TAC THENL
      [REWRITE_TAC[WORD_VAL] THEN CONV_TAC WORD_RULE; ALL_TAC]) (0--7);;

(*** The 86 steps of an iteration of the outer loop, up to its test: the
 *** initialization of the buffer on the stack, eight iterations of the inner
 *** loop of 8 instructions each, and the packing of the 8 values ***)

let COMPRESS_D4_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_EXEC (1--2) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_EXEC [3 + 8 * k] THEN
    COMPRESS_D4_INDEX_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_EXEC
     ((4 + 8 * k)--(10 + 8 * k))) (0--7) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_EXEC (67--84);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 4 in common/fips203/fips203.ml,  *)
(* the result for a coefficient x in [0,3329) is the integer closest to 16 * *)
(* x / 3329, rounding up on ties, modulo 16, i.e. ((32 * x + 3329) DIV 6658) *)
(* MOD 16, and as for mlkem_encode 4 the 4-bit values are put together     *)
(* little-endian. Like the C code, this relies on the coefficients being in  *)
(* [0,3329).                                                               *)
(*                                                                         *)
(* The code reads the address of the stack guard from the global offset    *)
(* table (GOT) in the loaded image, which is outside the code and read-only  *)
(* data covered by the image and so is part of the precondition, and checks  *)
(* before returning that the copy of the guard on the stack is still the   *)
(* same, which it is since neither the guard nor the GOT entry is written by *)
(* the code.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
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
                    mlkem_native_libmlkem_gcc12_Os_mc /\
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

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This is stated directly rather   *)
(* than by mk_safety_spec, since besides the arguments the events depend on  *)
(* the address of the stack guard, read from the GOT, which is also read.  *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
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
                   mlkem_native_libmlkem_gcc12_Os_mc /\
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

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
