(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 5 bits per coefficient. This is the code   *)
(* for mlkem_poly_compress_d5 from mlkem-native's portable C implementation  *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md). It is         *)
(* verified in the whole image (see libmlkem.ml).                            *)
(*                                                                           *)
(* Unlike at gcc -O2, the code does not go through a temporary array on the  *)
(* stack and has no stack protector, so it uses neither the stack nor the    *)
(* stack guard. The specifications are still those of gcc12_O2, with the     *)
(* 32-byte stack frame and the stack guard, so that the callers can use      *)
(* them in the same way.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d5:
       +0x0: mov     w9, #0xafc0
       +0x4: mov     x8, xzr
       +0x8: movk    w9, #0x13, lsl #16
       +0xc: add     x10, x1, #0x8
      +0x10: add     x11, x0, #0x2
      +0x14: mov     w12, #0x4000000
      +0x18: ldursh  w14, [x10, #-6]
      +0x1c: ldursh  w15, [x10, #-4]
      +0x20: ldursh  w13, [x10, #-8]
      +0x24: ldursh  w16, [x10, #-2]
      +0x28: madd    w14, w14, w9, w12
      +0x2c: madd    w15, w15, w9, w12
      +0x30: ldrsh   w17, [x10]
      +0x34: madd    w13, w13, w9, w12
      +0x38: ldrsh   w18, [x10, #2]
      +0x3c: madd    w16, w16, w9, w12
      +0x40: lsr     w15, w15, #25
      +0x44: and     w15, w15, #0x7c
      +0x48: lsr     w0, w14, #27
      +0x4c: bfxil   w15, w14, #30, #2
      +0x50: lsr     w14, w16, #20
      +0x54: ldrsh   w1, [x10, #4]
      +0x58: and     w14, w14, #0x80
      +0x5c: extr    w13, w0, w13, #27
      +0x60: add     x0, x11, x8
      +0x64: orr     w14, w15, w14
      +0x68: madd    w17, w17, w9, w12
      +0x6c: ldrsh   w2, [x10, #6]
      +0x70: madd    w18, w18, w9, w12
      +0x74: madd    w15, w1, w9, w12
      +0x78: sturb   w13, [x0, #-2]
      +0x7c: sturb   w14, [x0, #-1]
      +0x80: lsr     w13, w17, #23
      +0x84: lsr     w14, w18, #26
      +0x88: madd    w1, w2, w9, w12
      +0x8c: bfxil   w13, w16, #28, #4
      +0x90: and     w14, w14, #0x3e
      +0x94: lsr     w16, w15, #21
      +0x98: bfxil   w14, w17, #31, #1
      +0x9c: and     w16, w16, #0xc0
      +0xa0: add     x8, x8, #0x5
      +0xa4: orr     w14, w14, w16
      +0xa8: lsr     w16, w1, #24
      +0xac: bfxil   w16, w15, #29, #3
      +0xb0: add     x10, x10, #0x10
      +0xb4: cmp     x8, #0xa0
      +0xb8: strb    w13, [x0]
      +0xbc: strb    w14, [x0, #1]
      +0xc0: strb    w16, [x0, #2]
      +0xc4: b.ne    <mlkem_poly_compress_d5+0x18>
      +0xc8: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D5_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
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
(* The loop body, for eight coefficients, with X10 pointing to the          *)
(* coefficients plus 8, and X11 plus X8 to the five bytes for them plus 2,   *)
(* so that the loads have offsets from -8 to 6 and the stores from -2 to 2.  *)
(* ------------------------------------------------------------------------- *)

let WORD_ADD_2EXP64_STMT =
  `!n. word(n + 18446744073709551616):int64 = word n`;;

let WORD_ADD_2EXP64 = assume_spec WORD_ADD_2EXP64_STMT;;

(*** The loads are at offsets from -8 to 6 from x10 = a + (16 * i + 8), and
 *** the simulation leaves the sums of the numbers in the address unevaluated,
 *** so the facts about the coefficients are put in that form. ***)

let COMPRESS_D5_ADDR_STMT =
  `!(a:int64) i. word_add a (word(16 * i)) =
         word_add a (word((16 * i + 8) + 18446744073709551608)) /\
         word_add a (word(16 * i + 2)) =
         word_add a (word((16 * i + 8) + 18446744073709551610)) /\
         word_add a (word(16 * i + 4)) =
         word_add a (word((16 * i + 8) + 18446744073709551612)) /\
         word_add a (word(16 * i + 6)) =
         word_add a (word((16 * i + 8) + 18446744073709551614)) /\
         word_add a (word(16 * i + 10)) =
         word_add a (word((16 * i + 8) + 2)) /\
         word_add a (word(16 * i + 12)) =
         word_add a (word((16 * i + 8) + 4)) /\
         word_add a (word(16 * i + 14)) =
         word_add a (word((16 * i + 8) + 6))`;;

let COMPRESS_D5_ADDR = assume_spec COMPRESS_D5_ADDR_STMT;;

(*** The address of the stores is x11 + x8 = (r + 2) + 5 * i, which is
 *** put in the form (r + 5 * i) + 2 so that the numbers in the addresses of
 *** the stores are added up by the simulation. ***)

let COMPRESS_D5_STORE_BASE_STMT =
  `!(r:int64) i. word_add (word_add r (word 2)) (word(5 * i)) =
                 word_add (word_add r (word(5 * i))) (word 2)`;;

let COMPRESS_D5_STORE_BASE = assume_spec COMPRESS_D5_STORE_BASE_STMT;;

(*** The same for the addresses in the events of the safety proof. ***)

let COMPRESS_D5_EVENT_ADDR_STMT =
  `(!(a:int64) i. word_add (word_add a (word(16 * i + 8))) (word 18446744073709551608) =
     word_add a (word(16 * i)) /\
     word_add (word_add a (word(16 * i + 8))) (word 18446744073709551610) =
     word_add a (word(16 * i + 2)) /\
     word_add (word_add a (word(16 * i + 8))) (word 18446744073709551612) =
     word_add a (word(16 * i + 4)) /\
     word_add (word_add a (word(16 * i + 8))) (word 18446744073709551614) =
     word_add a (word(16 * i + 6)) /\
     word_add (word_add a (word(16 * i + 8))) (word 2) =
     word_add a (word(16 * i + 10)) /\
     word_add (word_add a (word(16 * i + 8))) (word 4) =
     word_add a (word(16 * i + 12)) /\
     word_add (word_add a (word(16 * i + 8))) (word 6) =
     word_add a (word(16 * i + 14))) /\
   (!(r:int64) i. word_add (word_add r (word(5 * i))) (word 1) =
     word_add r (word(5 * i + 1)) /\
     word_add (word_add r (word(5 * i))) (word 2) =
     word_add r (word(5 * i + 2)) /\
     word_add (word_add r (word(5 * i))) (word 3) =
     word_add r (word(5 * i + 3)) /\
     word_add (word_add r (word(5 * i))) (word 4) =
     word_add r (word(5 * i + 4)))`;;

let COMPRESS_D5_EVENT_ADDR = assume_spec COMPRESS_D5_EVENT_ADDR_STMT;;

let COMPRESS_D5_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_CLANG17_O3_EXEC (1--44);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 5 in common/fips203.ml, the      *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 32 * x / 3329, rounding up on ties, modulo 32, i.e.                       *)
(* ((64 * x + 3329) DIV 6658) MOD 32, and as for mlkem_encode 5 the 5-bit    *)
(* values are put together little-endian. Like the C code, this relies on    *)
(* the coefficients being in [0,3329).                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D5_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
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
                    mlkem_native_libmlkem_clang17_O3_mc /\
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
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(r,160);
                         memory :> bytes(word_sub stackpointer
                                                  (word 32),32)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D5_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D5_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for gcc12_O2,   *)
(* with the regions of the stack frame and the stack guard, which the code   *)
(* does not access.                                                          *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D5_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
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
                   mlkem_native_libmlkem_clang17_O3_mc /\
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
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE [memory :> bytes(r,160);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D5_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D5_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
