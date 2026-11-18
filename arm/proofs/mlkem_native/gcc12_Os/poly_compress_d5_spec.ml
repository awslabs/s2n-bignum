(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 5 bits per coefficient. This is the code   *)
(* for mlkem_poly_compress_d5 from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -Os (see mlkem_native/README.md), with a stack    *)
(* protector. It is verified in the whole image (see                         *)
(* libmlkem.ml), with the address of the stack guard                         *)
(* in the global offset table.                                               *)
(* The code is not vectorized: an outer loop over groups of 8 coefficients   *)
(* computes their 5-bit values by an inner loop into a buffer on the stack   *)
(* and packs them into bytes. The simulation unrolls the inner loop.         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d5:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]  // got_stack_chk_guard
       +0x8: str     x30, [sp, #-32]!
       +0xc: mov     w8, #0xafc0
      +0x10: mov     w4, #0x0
      +0x14: ldr     x3, [x2]
      +0x18: str     x3, [sp, #24]
      +0x1c: mov     x3, #0x0
      +0x20: add     x7, sp, #0x10
      +0x24: movk    w8, #0x13, lsl #16
      +0x28: mov     w9, #0x4000000
      +0x2c: mov     x2, #0x0
      +0x30: str     xzr, [sp, #16]
      +0x34: add     w3, w4, w2
      +0x38: ldrsh   w3, [x1, x3, lsl #1]
      +0x3c: madd    w3, w3, w8, w9
      +0x40: lsr     w3, w3, #27
      +0x44: strb    w3, [x2, x7]
      +0x48: add     x2, x2, #0x1
      +0x4c: cmp     x2, #0x8
      +0x50: b.ne    <mlkem_poly_compress_d5+0x34>
      +0x54: ldrb    w3, [sp, #17]
      +0x58: add     w4, w4, #0x8
      +0x5c: ldrb    w2, [sp, #16]
      +0x60: add     x0, x0, #0x5
      +0x64: ldrb    w5, [sp, #18]
      +0x68: orr     w2, w2, w3, lsl #5
      +0x6c: sturb   w2, [x0, #-5]
      +0x70: ldrb    w2, [sp, #19]
      +0x74: lsl     w6, w2, #7
      +0x78: orr     w5, w6, w5, lsl #2
      +0x7c: orr     w3, w5, w3, lsr #3
      +0x80: sturb   w3, [x0, #-4]
      +0x84: ldrb    w3, [sp, #20]
      +0x88: lsl     w5, w3, #4
      +0x8c: orr     w2, w5, w2, lsr #1
      +0x90: sturb   w2, [x0, #-3]
      +0x94: ldrb    w2, [sp, #22]
      +0x98: ldrb    w5, [sp, #21]
      +0x9c: lsl     w6, w2, #6
      +0xa0: lsr     w2, w2, #2
      +0xa4: orr     w5, w6, w5, lsl #1
      +0xa8: orr     w3, w5, w3, lsr #4
      +0xac: sturb   w3, [x0, #-2]
      +0xb0: ldrb    w3, [sp, #23]
      +0xb4: orr     w2, w2, w3, lsl #3
      +0xb8: sturb   w2, [x0, #-1]
      +0xbc: cmp     w4, #0x100
      +0xc0: b.ne    <mlkem_poly_compress_d5+0x2c>
      +0xc4: adrp    x0, <page>
      +0xc8: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0xcc: ldr     x2, [sp, #24]
      +0xd0: ldr     x1, [x0]
      +0xd4: subs    x2, x2, x1
      +0xd8: mov     x1, #0x0
      +0xdc: b.eq    <mlkem_poly_compress_d5+0xe4>
      +0xe0: bl      <__stack_chk_fail@plt>
      +0xe4: ldr     x30, [sp], #32
      +0xe8: ret     
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_compress_d5"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 5 bits, as computed. For the 32-bit *)
(* product the bounds do not follow linearly from the division, so it is   *)
(* checked for each coefficient.                                           *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D5_ARITH_STMT =
  `!v. v < 3329
       ==> (67108864 + v * 1290176) DIV 134217728 =
           (64 * v + 3329) DIV 6658`;;

let COMPRESS_D5_ARITH = assume_spec COMPRESS_D5_ARITH_STMT;;

let WORD_SX_SMALL_32_STMT =
  `!y:int16. val y < 32768 ==> (word_sx y:int32) = word_zx y`;;

let WORD_SX_SMALL_32 = assume_spec WORD_SX_SMALL_32_STMT;;

let COMPRESS_D5_FIELD_STMT =
  `!y:int16.
        val y < 3329
        ==> val(word_subword
                 (word (67108864 +
                        val (word_zx (word_zx (word_sx y:int32):int64):
                             int32) * 1290176):int32)
                 (27,5):5 word) =
            ((64 * val y + 3329) DIV 6658) MOD 32`;;

let COMPRESS_D5_FIELD = assume_spec COMPRESS_D5_FIELD_STMT;;

(* ------------------------------------------------------------------------- *)
(* The packing of eight 5-bit values into five bytes.                      *)
(* ------------------------------------------------------------------------- *)

let BYTES_OF_NUM_5_STMT =
  `!n. n < 2 EXP 40
       ==> n MOD 256 + 256 * (n DIV 256) MOD 256 +
           65536 * (n DIV 65536) MOD 256 +
           16777216 * (n DIV 16777216) MOD 256 +
           4294967296 * (n DIV 4294967296) MOD 256 = n`;;

let BYTES_OF_NUM_5 = assume_spec BYTES_OF_NUM_5_STMT;;

let VAL_JOIN_5X8_STMT =
  `!(u0:5 word) (u1:5 word) (u2:5 word) (u3:5 word)
    (u4:5 word) (u5:5 word) (u6:5 word) (u7:5 word).
     val(word_join u7 (word_join u6 (word_join u5 (word_join u4
          (word_join u3 (word_join u2 (word_join u1 u0:10 word):15 word):
           20 word):25 word):30 word):35 word):40 word) =
     val u0 + 32 * val u1 + 1024 * val u2 + 32768 * val u3 +
     1048576 * val u4 + 33554432 * val u5 + 1073741824 * val u6 +
     34359738368 * val u7`;;

let VAL_JOIN_5X8 = assume_spec VAL_JOIN_5X8_STMT;;

(* * The stored bytes as parts of the 40-bit join of the eight fields **   *)

let compress_d5_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let d5_xatoms = map (fun j ->
  vsubst [j,`j:num`]
   `word (67108864 +
          val (word_zx (word_zx (word_sx ((x:num->int16) j):int32):int64):
               int32) * 1290176):int32`) compress_d5_indices;;

let d5_join =
  vsubst (zip d5_xatoms (map (fun k -> mk_var("w"^string_of_int k,`:int32`))
                             (0--7)))
  `word_join (word_subword (w7:int32) (27,5):5 word)
    (word_join (word_subword (w6:int32) (27,5):5 word)
     (word_join (word_subword (w5:int32) (27,5):5 word)
      (word_join (word_subword (w4:int32) (27,5):5 word)
       (word_join (word_subword (w3:int32) (27,5):5 word)
        (word_join (word_subword (w2:int32) (27,5):5 word)
         (word_join (word_subword (w1:int32) (27,5):5 word)
                    (word_subword (w0:int32) (27,5):5 word):10 word):
         15 word):20 word):25 word):30 word):35 word):40 word`;;

let D5_PACK_TAC m =
  let addr =
    if m = 0 then `word_add r (word (5 * i)):int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`r:int64`),
            mk_comb(`word:num->int64`,
                    mk_binop `(+):num->num->num` `5 * i`
                             (mk_small_numeral m))) in
  let pat = vsubst [addr,`addr:int64`]
              `read (memory :> bytes8 addr) s = x` in
  let rule th =
    let v = rand(concl th) in
    let target = mk_comb(mk_comb(`word_subword:40 word->num#num->byte`,
                                 d5_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int32`) d5_xatoms in
    let eq = subst (zip gvs d5_xatoms) (mk_eq(v,target)) in
    TRANS th (INST (zip d5_xatoms gvs) (BITBLAST_RULE eq)) in
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then ASSUME_TAC(rule th) else failwith "D5_PACK_TAC");;

(* ------------------------------------------------------------------------- *)
(* In the inner loop, which is unrolled in the simulation, tidy up the index *)
(* 8 * i + k of the coefficient (k the iteration of the inner loop) before *)
(* it is used in the load with a shifted register offset, as for           *)
(* mlkem_poly_compress_d4. The same holds for the address of the store of  *)
(* the 5-bit value, [x2, x7] with x2 = k and x7 = sp + 16.                 *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D5_INDEX_TAC k =
  let jt = el k compress_d5_indices in
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
    else failwith "COMPRESS_D5_INDEX_TAC");;

let COMPRESS_D5_ADDRESS_TAC =
  MAP_EVERY (fun k ->
    SUBGOAL_THEN
     (subst [mk_small_numeral k,`k:num`;
             mk_small_numeral(16 + k),`m:num`]
       `word_add (word k) (word (val (word_add stackpointer (word 16)))):int64 =
        word_add stackpointer (word m)`)
     ASSUME_TAC THENL
      [REWRITE_TAC[WORD_VAL] THEN CONV_TAC WORD_RULE; ALL_TAC]) (0--7);;

(*** The 92 steps of an iteration of the outer loop, up to its test: the
 *** initialization of the buffer on the stack, eight iterations of the inner
 *** loop of 8 instructions each, and the packing of the 8 values ***)

let COMPRESS_D5_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_OS_EXEC (1--2) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_OS_EXEC [3 + 8 * k] THEN
    COMPRESS_D5_INDEX_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_OS_EXEC
     ((4 + 8 * k)--(10 + 8 * k))) (0--7) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_OS_EXEC (67--92);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 5 in common/fips203/fips203.ml,  *)
(* the result for a coefficient x in [0,3329) is the integer closest to 32 * *)
(* x / 3329, rounding up on ties, modulo 32, i.e. ((64 * x + 3329) DIV 6658) *)
(* MOD 32, and as for mlkem_encode 5 the 5-bit values are put together     *)
(* little-endian. Like the C code, this relies on the coefficients being in  *)
(* [0,3329). The stack guard is handled as for mlkem_poly_compress_d4.     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,160); (a,512); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,160); (word_sub stackpointer (word 32),32)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem_poly_compress_d5) /\
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
                   ==> read(memory :> bytes(r,160)) s =
                       nsum {i | i < 256}
                            (\i. ((64 * val(x i) + 3329) DIV 6658) MOD 32 *
                                 2 EXP (5 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,160);
                         memory :> bytes(word_sub stackpointer
                                                  (word 32),32)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for           *)
(* mlkem_poly_compress_d4.                                                 *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,160; a,512; word_sub stackpointer (word 32),32] /\
       ALLPAIRS nonoverlapping
        [r,160; word_sub stackpointer (word 32),32]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem_poly_compress_d5) /\
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
                     [a,512; r,160; word_sub stackpointer (word 32),32;
                      word(pc + got_stack_chk_guard),8; guard,8]
                     [r,160; word_sub stackpointer (word 32),32]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,160);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
