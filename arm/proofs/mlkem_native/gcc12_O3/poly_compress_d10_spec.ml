(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 10 bits per coefficient. This is the code  *)
(* for mlkem_poly_compress_d10 from mlkem-native's portable C implementation *)
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

    mlkem_poly_compress_d10:
       +0x0: mov     x7, #0xbc00
       +0x4: mov     x3, x0
       +0x8: mov     x5, x1
       +0xc: add     x11, x0, #0x140
      +0x10: movk    x7, #0x9d7d, lsl #16
      +0x14: mov     x6, #0x100000000
      +0x18: ldrsh   x2, [x5, #2]
      +0x1c: add     x3, x3, #0x5
      +0x20: ldrsh   x1, [x5, #4]
      +0x24: add     x5, x5, #0x8
      +0x28: ldursh  x0, [x5, #-2]
      +0x2c: ldursh  x4, [x5, #-8]
      +0x30: madd    x2, x2, x7, x6
      +0x34: madd    x1, x1, x7, x6
      +0x38: madd    x0, x0, x7, x6
      +0x3c: madd    x4, x4, x7, x6
      +0x40: ubfx    x2, x2, #33, #10
      +0x44: ubfx    x1, x1, #33, #10
      +0x48: ubfx    x0, x0, #33, #10
      +0x4c: lsl     w8, w2, #2
      +0x50: ubfx    x4, x4, #33, #10
      +0x54: lsl     w10, w1, #4
      +0x58: lsl     w9, w0, #6
      +0x5c: orr     w2, w10, w2, lsr #6
      +0x60: orr     w8, w8, w4, lsr #8
      +0x64: orr     w1, w9, w1, lsr #4
      +0x68: lsr     w0, w0, #2
      +0x6c: sturb   w4, [x3, #-5]
      +0x70: sturb   w8, [x3, #-4]
      +0x74: sturb   w2, [x3, #-3]
      +0x78: sturb   w1, [x3, #-2]
      +0x7c: sturb   w0, [x3, #-1]
      +0x80: cmp     x11, x3
      +0x84: b.ne    <mlkem_poly_compress_d10+0x18>
      +0x88: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_compress_d10"];;

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
(* The loop, over groups of four coefficients, with X5 pointing to the       *)
(* coefficients and X3 to the five bytes for them, both advanced at the      *)
(* start of the body, so that the last loads and the stores have negative    *)
(* offsets.                                                                  *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D10_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O3_EXEC (1--26);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 10 in common/fips203.ml, the     *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 1024 * x / 3329, rounding up on ties, modulo 1024, i.e.                   *)
(* ((2048 * x + 3329) DIV 6658) MOD 1024, and as for mlkem_encode 10 the     *)
(* 10-bit values are put together little-endian. Like the C code, this       *)
(* relies on the coefficients being in [0,3329).                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
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
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_poly_compress_d10) /\
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
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,320);
                         memory :> bytes(word_sub stackpointer
                                                  (word 32),32)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for gcc12_O2,   *)
(* with the regions of the stack frame and the stack guard, which the code   *)
(* does not access.                                                          *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
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
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s = word (pc + mlkem_poly_compress_d10) /\
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
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,320);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
