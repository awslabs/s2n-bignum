(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 5 bits per coefficient. This is the code   *)
(* for mlkem_poly_compress_d5 from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), with a stack    *)
(* protector. It is verified in the whole image (see                         *)
(* libmlkem.ml), with the address of the stack guard                         *)
(* in the global offset table.                                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d5:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]  // got_stack_chk_guard
       +0x8: str     x30, [sp, #-32]!
       +0xc: mov     x12, x1
      +0x10: mov     w14, #0xafc0
      +0x14: ldr     x1, [x2]
      +0x18: str     x1, [sp, #24]
      +0x1c: mov     x1, #0x0
      +0x20: add     x15, sp, #0x10
      +0x24: mov     w6, #0x0
      +0x28: movk    w14, #0x13, lsl #16
      +0x2c: mov     w13, #0x4000000
      +0x30: nop
      +0x34: sub     w2, w6, #0x1
      +0x38: mov     x1, #0x1
      +0x3c: str     xzr, [sp, #16]
      +0x40: nop
      +0x44: add     w3, w2, w1
      +0x48: add     x4, x15, x1
      +0x4c: add     x1, x1, #0x1
      +0x50: ldrsh   w3, [x12, x3, lsl #1]
      +0x54: madd    w3, w3, w14, w13
      +0x58: lsr     w3, w3, #27
      +0x5c: sturb   w3, [x4, #-1]
      +0x60: cmp     x1, #0x9
      +0x64: b.ne    <mlkem_poly_compress_d5+0x44>
      +0x68: ldrb    w3, [sp, #19]
      +0x6c: add     w6, w6, #0x8
      +0x70: ldrb    w1, [sp, #18]
      +0x74: add     x0, x0, #0x5
      +0x78: ldrb    w5, [sp, #22]
      +0x7c: lsl     w4, w3, #7
      +0x80: ldrb    w2, [sp, #20]
      +0x84: ldrb    w8, [sp, #21]
      +0x88: orr     w1, w4, w1, lsl #2
      +0x8c: ldrb    w9, [sp, #16]
      +0x90: lsl     w11, w5, #6
      +0x94: ldrb    w4, [sp, #17]
      +0x98: lsl     w10, w2, #4
      +0x9c: ldrb    w7, [sp, #23]
      +0xa0: lsr     w5, w5, #2
      +0xa4: orr     w8, w11, w8, lsl #1
      +0xa8: orr     w3, w10, w3, lsr #1
      +0xac: orr     w1, w1, w4, lsr #3
      +0xb0: orr     w2, w8, w2, lsr #4
      +0xb4: orr     w5, w5, w7, lsl #3
      +0xb8: orr     w4, w9, w4, lsl #5
      +0xbc: sturb   w4, [x0, #-5]
      +0xc0: sturb   w1, [x0, #-4]
      +0xc4: sturb   w3, [x0, #-3]
      +0xc8: sturb   w2, [x0, #-2]
      +0xcc: sturb   w5, [x0, #-1]
      +0xd0: cmp     w6, #0x100
      +0xd4: b.ne    <mlkem_poly_compress_d5+0x34>
      +0xd8: adrp    x0, <page>
      +0xdc: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0xe0: ldr     x2, [sp, #24]
      +0xe4: ldr     x1, [x0]
      +0xe8: subs    x2, x2, x1
      +0xec: mov     x1, #0x0
      +0xf0: b.ne    <mlkem_poly_compress_d5+0xfc>
      +0xf4: ldr     x30, [sp], #32
      +0xf8: ret
      +0xfc: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem_poly_compress_d5"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 5 bits, as computed. For the 32-bit   *)
(* product the bounds do not follow linearly from the division, so it is     *)
(* checked for each coefficient.                                             *)
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
(* The packing of eight 5-bit values into five bytes.                        *)
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

(*** The stored bytes as parts of the 40-bit join of the eight fields ***)

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
(* 8 * i + k of the coefficient (k the iteration of the inner loop) before   *)
(* it is used in the load with a shifted register offset, as for             *)
(* mlkem_poly_compress_d4.                                                   *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D5_INDEX_TAC k =
  let jt = el k compress_d5_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  let mt = mk_comb(`word_zx:int32->int64`,
            mk_comb(mk_comb(`word_add:int32->int32->int32`,
                            `word_zx(word(8 * i):int64):int32`),
                    mk_comb(`word:num->int32`,mk_small_numeral k))) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X3 s = x`) c then
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
    else failwith "COMPRESS_D5_INDEX_TAC");;

let COMPRESS_D5_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--4) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC [5 + 9 * k] THEN
    COMPRESS_D5_INDEX_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC
     ((6 + 9 * k)--(13 + 9 * k))) (0--7) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (77--102);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 5 in common/fips203.ml, the      *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 32 * x / 3329, rounding up on ties, modulo 32, i.e.                       *)
(* ((64 * x + 3329) DIV 6658) MOD 32, and as for mlkem_encode 5 the 5-bit    *)
(* values are put together little-endian. Like the C code, this relies on    *)
(* the coefficients being in [0,3329). The stack guard is handled as for     *)
(* mlkem_poly_compress_d4.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
                    mlkem_native_libmlkem_gcc12_O2_mc /\
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

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_poly_compress_d4.                                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
                   mlkem_native_libmlkem_gcc12_O2_mc /\
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

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
