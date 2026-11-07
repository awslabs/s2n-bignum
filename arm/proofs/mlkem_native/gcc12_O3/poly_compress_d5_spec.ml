(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 5 bits per coefficient. This is the code   *)
(* for mlkem_poly_compress_d5 from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -O3 (see mlkem_native/README.md). It is verified  *)
(* in the whole image (see libmlkem.ml).                                     *)
(*                                                                           *)
(* Unlike at -O2, the code does not go through a temporary array on the     *)
(* stack and has no stack protector, so it uses neither the stack nor the   *)
(* stack guard. The specifications are still those of gcc12_O2, with the    *)
(* 32-byte stack frame and the stack guard, so that the callers can use     *)
(* them in the same way.                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d5:
       +0x0: mov     w9, #0xafc0
       +0x4: mov     x7, x0
       +0x8: mov     x2, x1
       +0xc: add     x10, x0, #0xa0
      +0x10: movk    w9, #0x13, lsl #16
      +0x14: mov     w8, #0x4000000
      +0x18: ldrsh   w1, [x2, #4]
      +0x1c: add     x7, x7, #0x5
      +0x20: ldrsh   w0, [x2, #10]
      +0x24: ldrsh   w5, [x2, #2]
      +0x28: ldrsh   w6, [x2, #8]
      +0x2c: ldrsh   w11, [x2, #14]
      +0x30: madd    w1, w1, w9, w8
      +0x34: ldrsh   w4, [x2, #6]
      +0x38: madd    w0, w0, w9, w8
      +0x3c: ldrsh   w3, [x2, #12]
      +0x40: madd    w5, w5, w9, w8
      +0x44: ldrsh   w12, [x2], #16
      +0x48: madd    w6, w6, w9, w8
      +0x4c: madd    w11, w11, w9, w8
      +0x50: lsr     w1, w1, #27
      +0x54: madd    w4, w4, w9, w8
      +0x58: lsr     w0, w0, #27
      +0x5c: madd    w3, w3, w9, w8
      +0x60: lsr     w5, w5, #27
      +0x64: lsr     w6, w6, #27
      +0x68: madd    w12, w12, w9, w8
      +0x6c: lsr     w11, w11, #27
      +0x70: lsr     w4, w4, #27
      +0x74: lsr     w3, w3, #27
      +0x78: lsl     w1, w1, #2
      +0x7c: lsl     w0, w0, #1
      +0x80: orr     w1, w1, w5, lsr #3
      +0x84: orr     w0, w0, w6, lsr #4
      +0x88: lsl     w11, w11, #3
      +0x8c: lsl     w6, w6, #4
      +0x90: orr     w1, w1, w4, lsl #7
      +0x94: orr     w0, w0, w3, lsl #6
      +0x98: orr     w4, w6, w4, lsr #1
      +0x9c: orr     w3, w11, w3, lsr #2
      +0xa0: extr    w5, w5, w12, #27
      +0xa4: sturb   w5, [x7, #-5]
      +0xa8: sturb   w1, [x7, #-4]
      +0xac: sturb   w4, [x7, #-3]
      +0xb0: sturb   w0, [x7, #-2]
      +0xb4: sturb   w3, [x7, #-1]
      +0xb8: cmp     x10, x7
      +0xbc: b.ne    <mlkem_poly_compress_d5+0x18>
      +0xc0: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
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
(* The loop body, for eight coefficients, with X2 pointing to them and X7 to *)
(* the five bytes for them, advanced at the start of the body so that the    *)
(* stores have negative offsets.                                             *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D5_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O3_EXEC (1--40);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 5 in common/fips203.ml, the      *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 32 * x / 3329, rounding up on ties, modulo 32, i.e.                       *)
(* ((64 * x + 3329) DIV 6658) MOD 32, and as for mlkem_encode 5 the 5-bit    *)
(* values are put together little-endian. Like the C code, this relies on    *)
(* the coefficients being in [0,3329).                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
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
                    mlkem_native_libmlkem_gcc12_O3_mc /\
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

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for gcc12_O2,   *)
(* with the regions of the stack frame and the stack guard, which the code   *)
(* does not access.                                                          *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
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
                   mlkem_native_libmlkem_gcc12_O3_mc /\
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

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
