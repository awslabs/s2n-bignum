(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 10 bits per coefficient. This is the       *)
(* code for mlk_poly_compress_d10_c from mlkem-native's portable C           *)
(* implementation compiled by gcc 12 with -O2 as one translation unit (see   *)
(* mlkem_native/README.md), with a stack protector. It is the same as        *)
(* mlkem_poly_compress_d10 of the separate -O2 build except for a NOP        *)
(* before the loop there and other registers for the output pointer and      *)
(* the inner loop. It is verified in the whole image (see libmlkem.ml),      *)
(* with the address of the stack guard in the global offset table.           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlk_poly_compress_d10_c:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]
       +0x8: str     x30, [sp, #-32]!
       +0xc: mov     x4, x0
      +0x10: mov     x8, #0xbc00
      +0x14: mov     x6, x1
      +0x18: ldr     x0, [x2]
      +0x1c: str     x0, [sp, #24]
      +0x20: mov     x0, #0x0
      +0x24: add     x12, sp, #0x10
      +0x28: mov     w3, #0x4
      +0x2c: movk    x8, #0x9d7d, lsl #16
      +0x30: mov     x7, #0x100000000
      +0x34: sub     w1, w3, #0x4
      +0x38: mov     x2, x12
      +0x3c: ldrsh   x0, [x6, w1, uxtw #1]   <+ |
      +0x40: add     w1, w1, #0x1             | |
      +0x44: madd    x0, x0, x8, x7           | |
      +0x48: ubfx    x0, x0, #33, #10         | |
      +0x4c: strh    w0, [x2], #2             | |
      +0x50: cmp     w3, w1                   | |
      +0x54: b.ne    <mlk_poly_compress_d10_c+0x3c>                   -+ |
      +0x58: ldrh    w2, [sp, #18]
      +0x5c: add     w3, w3, #0x4
      +0x60: ldrh    w1, [sp, #20]
      +0x64: add     x4, x4, #0x5
      +0x68: ldrh    w0, [sp, #22]
      +0x6c: ldrh    w5, [sp, #16]
      +0x70: lsl     w9, w2, #2
      +0x74: lsl     w11, w1, #4
      +0x78: sturb   w5, [x4, #-5]
      +0x7c: lsl     w10, w0, #6
      +0x80: orr     w2, w11, w2, lsr #6
      +0x84: orr     w1, w10, w1, lsr #4
      +0x88: lsr     w0, w0, #2
      +0x8c: orr     w5, w9, w5, lsr #8
      +0x90: sturb   w5, [x4, #-4]
      +0x94: sturb   w2, [x4, #-3]
      +0x98: sturb   w1, [x4, #-2]
      +0x9c: sturb   w0, [x4, #-1]
      +0xa0: cmp     w3, #0x104
      +0xa4: b.ne    <mlk_poly_compress_d10_c+0x34>
      +0xa8: adrp    x0, <page>
      +0xac: ldr     x0, [x0, #4088]
      +0xb0: ldr     x2, [sp, #24]
      +0xb4: ldr     x1, [x0]
      +0xb8: subs    x2, x2, x1
      +0xbc: mov     x1, #0x0
      +0xc0: b.ne    +0xcc
      +0xc4: ldr     x30, [sp], #32
      +0xc8: ret
      +0xcc: bl      stack_chk_fail
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_poly_compress_d10_c"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 10 bits, as computed.                 *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D10_ARITH_STMT =
  `!v. v < 3329
       ==> (4294967296 + v * 2642263040) DIV 8589934592 =
           (2048 * v + 3329) DIV 6658`;;

let COMPRESS_D10_ARITH = assume_spec COMPRESS_D10_ARITH_STMT;;

let WORD_SX_SMALL_64_STMT =
  `!y:int16. val y < 32768 ==> (word_sx y:int64) = word_zx y`;;

let WORD_SX_SMALL_64 = assume_spec WORD_SX_SMALL_64_STMT;;

let COMPRESS_D10_FIELD_STMT =
  `!y:int16.
        val y < 3329
        ==> val(word_subword
                 (word (4294967296 + val (word_sx y:int64) * 2642263040):int64)
                 (33,10):10 word) =
            ((2048 * val y + 3329) DIV 6658) MOD 1024`;;

let COMPRESS_D10_FIELD = assume_spec COMPRESS_D10_FIELD_STMT;;

(* ------------------------------------------------------------------------- *)
(* The packing of four 10-bit values into five bytes.                        *)
(* ------------------------------------------------------------------------- *)

let BYTES_OF_NUM_5_STMT =
  `!n. n < 2 EXP 40
       ==> n MOD 256 + 256 * (n DIV 256) MOD 256 +
           65536 * (n DIV 65536) MOD 256 +
           16777216 * (n DIV 16777216) MOD 256 +
           4294967296 * (n DIV 4294967296) MOD 256 = n`;;

let BYTES_OF_NUM_5 = assume_spec BYTES_OF_NUM_5_STMT;;

let VAL_JOIN_10X4_STMT =
  `!(u0:10 word) (u1:10 word) (u2:10 word) (u3:10 word).
     val(word_join u3 (word_join u2 (word_join u1 u0:20 word):30 word):
         40 word) =
     val u0 + 1024 * val u1 + 1048576 * val u2 + 1073741824 * val u3`;;

let VAL_JOIN_10X4 = assume_spec VAL_JOIN_10X4_STMT;;

(*** The stored bytes as parts of the 40-bit join of the four fields ***)

let d10_indices = map (fun k ->
  if k = 0 then `4 * i` else
  mk_binop `(+):num->num->num` `4 * i` (mk_small_numeral k)) (0--4);;

let d10_xatoms = map (fun j ->
  vsubst [j,`j:num`]
   `word (4294967296 + val (word_sx ((x:num->int16) j):int64) * 2642263040):
    int64`) (butlast d10_indices);;

let d10_join =
  vsubst (zip d10_xatoms [`w0:int64`; `w1:int64`; `w2:int64`; `w3:int64`])
  `word_join (word_subword (w3:int64) (33,10):10 word)
    (word_join (word_subword (w2:int64) (33,10):10 word)
      (word_join (word_subword (w1:int64) (33,10):10 word)
                 (word_subword (w0:int64) (33,10):10 word):20 word):30 word):
    40 word`;;

let D10_PACK_TAC m =
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
                                 d10_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int64`) d10_xatoms in
    let eq = subst (zip gvs d10_xatoms) (mk_eq(v,target)) in
    TRANS th (INST (zip d10_xatoms gvs) (BITBLAST_RULE eq)) in
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then ASSUME_TAC(rule th) else failwith "D10_PACK_TAC");;

(* ------------------------------------------------------------------------- *)
(* The loops. The inner one, unrolled in the simulation, computes four       *)
(* 10-bit values into a temporary array on the stack; X1 is the index of the *)
(* coefficient, which is tidied up before it is used as a register offset.   *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D10_INDEX_TAC k =
  let jt = el k d10_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read X1 s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC]
    else failwith "COMPRESS_D10_INDEX_TAC");;

let COMPRESS_D10_UXTW_TAC k =
  let jt = el k d10_indices in
  let zt = mk_comb(`word_zx:int32->int64`,
                   mk_comb(`word_zx:int64->int32`,
                           mk_comb(`word:num->int64`,jt))) in
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,zt),jt)) ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT MOD_LT_ASM_TAC THEN REWRITE_TAC[];
    ALL_TAC];;

let COMPRESS_D10_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (1--1) THEN
  COMPRESS_D10_INDEX_TAC 0 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (2--2) THEN
  MAP_EVERY (fun k ->
    COMPRESS_D10_UXTW_TAC k THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC
     ((3 + 7 * k)--(4 + 7 * k)) THEN
    COMPRESS_D10_INDEX_TAC (k + 1) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC
     ((5 + 7 * k)--(8 + 7 * k)) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC
     ((9 + 7 * k)--(9 + 7 * k))) (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_EXEC (31--48);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 10 in common/fips203.ml, the     *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 1024 * x / 3329, rounding up on ties, modulo 1024, i.e.                   *)
(* ((2048 * x + 3329) DIV 6658) MOD 1024, and as for mlkem_encode 10 the     *)
(* 10-bit values are put together little-endian. Like the C code, this       *)
(* relies on the coefficients being in [0,3329). The stack guard is handled  *)
(* as for mlkem_poly_compress_d4.                                            *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,320); (a,512); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,320); (word_sub stackpointer (word 32),32)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_poly_compress_d10_c) /\
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
                   ==> read(memory :> bytes(r,320)) s =
                       nsum {i | i < 256}
                            (\i. ((2048 * val(x i) + 3329) DIV 6658) MOD 1024 *
                                 2 EXP (10 * i))))
             (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                         X11; X12] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,320);
                         memory :> bytes(word_sub stackpointer
                                                  (word 32),32)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_poly_compress_d4.                                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,320; a,512; word_sub stackpointer (word 32),32] /\
       ALLPAIRS nonoverlapping
        [r,320; word_sub stackpointer (word 32),32]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                 read PC s = word (pc + mlk_poly_compress_d10_c) /\
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
                     [a,512; r,320; word_sub stackpointer (word 32),32;
                      word(pc + got_stack_chk_guard),8; guard,8]
                     [r,320; word_sub stackpointer (word 32),32]))
            (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                        X11; X12] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes(r,320);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;
