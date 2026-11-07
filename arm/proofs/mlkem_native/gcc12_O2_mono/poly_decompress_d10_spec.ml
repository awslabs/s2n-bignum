(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 10 bits per coefficient. This is the   *)
(* code for mlk_poly_decompress_d10_c from mlkem-native's portable C         *)
(* implementation compiled by gcc 12 with -O2 as one translation unit (see   *)
(* mlkem_native/README.md), which is the same as mlkem_poly_decompress_d10   *)
(* of the separate -O2 build except for the offset of its constant. It is    *)
(* verified in the whole image (see libmlkem.ml), with the proof for the     *)
(* separate -O2 build.                                                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlk_poly_decompress_d10_c:
       +0x0: mov     x5, x0
       +0x4: adrp    x0, <page>
       +0x8: movi    v2.4s, #0x2, lsl #8
       +0xc: add     x7, x1, #0x140
      +0x10: ldr     q3, [x0, #3168]
      +0x14: nop
      +0x18: add     x1, x1, #0x5
      +0x1c: ldurb   w2, [x1, #-3]
      +0x20: ldurb   w3, [x1, #-4]
      +0x24: ldurh   w0, [x1, #-5]
      +0x28: lsl     w6, w2, #6
      +0x2c: ldurb   w4, [x1, #-2]
      +0x30: orr     w3, w6, w3, lsr #2
      +0x34: and     w0, w0, #0x3ff
      +0x38: fmov    s0, w0
      +0x3c: and     w0, w3, #0x3ff
      +0x40: lsl     w6, w4, #4
      +0x44: ldurb   w3, [x1, #-1]
      +0x48: mov     v0.h[1], w0
      +0x4c: orr     w2, w6, w2, lsr #4
      +0x50: and     w2, w2, #0x3ff
      +0x54: ubfx    x4, x4, #6, #16
      +0x58: mov     v1.16b, v2.16b
      +0x5c: orr     w0, w4, w3, lsl #2
      +0x60: mov     v0.h[2], w2
      +0x64: mov     v0.h[3], w0
      +0x68: uxtl    v0.4s, v0.4h
      +0x6c: mla     v1.4s, v0.4s, v3.4s
      +0x70: shrn    v0.4h, v1.4s, #10
      +0x74: str     d0, [x5], #8
      +0x78: cmp     x1, x7
      +0x7c: b.ne    <mlk_poly_decompress_d10_c+0x18>
      +0x80: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_poly_decompress_d10_c"];;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_MONO_CONSTANTS =
  MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlk_poly_decompress_d10_c_consts")
   128;;

(* ------------------------------------------------------------------------- *)
(* The five bytes for four coefficients, as parts of a 40-bit word.          *)
(* ------------------------------------------------------------------------- *)

let D10_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,320)) s = n /\ i < 64 /\ j < 5
        ==> read (memory :> bytes8(word_add a (word(5 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (40 * i)):40 word) (8 * j,8)`;;

let D10_BYTES = assume_spec D10_BYTES_STMT;;

let D10_HALF_STMT =
  `!a n i s.
        read (memory :> bytes(a,320)) s = n /\ i < 64
        ==> read (memory :> bytes16(word_add a (word(5 * i)))) s =
            word_subword (word(n DIV 2 EXP (40 * i)):40 word) (0,16)`;;

let D10_HALF = assume_spec D10_HALF_STMT;;

(* ------------------------------------------------------------------------- *)
(* The computation for each coefficient, with its 10-bit field f in the 40   *)
(* bits, and the field as part of the number for the input bytes.            *)
(* ------------------------------------------------------------------------- *)

let D10_LANE_STMT =
  `!f:10 word.
     word_subword
      (word_ushr
        (word_add (word 512)
          (word_mul (word_shl (word_zx (word_zx f:int16):int32) 0)
                    (word 3329))) 10) (0,16):int16 =
     word((3329 * val f + 512) DIV 1024)`;;

let D10_LANE = assume_spec D10_LANE_STMT;;

let D10_FIELD_STMT =
  `!n i k. k < 4
     ==> val(word_subword (word(n DIV 2 EXP (40 * i)):40 word)
                          (10 * k,10):10 word) =
         (n DIV 2 EXP (10 * (4 * i + k))) MOD 1024`;;

let D10_FIELD = assume_spec D10_FIELD_STMT;;

(*** The stored coefficients, from the 64-bit store, as 16-bit lanes ***)

let D10_LANE_RULE th =
  let v = rand(concl th) in
  let k = dest_small_numeral(lhand(rand v)) / 16 in
  let jn = lhand(lhand v) in
  let h = lhand jn and l = rand jn in
  let lanes = [rand l; lhand l; rand h; lhand h] in
  let gvs = map (fun t -> genvar(type_of t)) lanes in
  let eq = mk_eq(subst (zip gvs lanes) v, el k gvs) in
  let bth = INST (zip lanes gvs) (BITBLAST_RULE eq) in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th bth);;

(*** The value of lane k, using the bit-level form of its 10-bit field ***)

let D10_FIELD_TAC k =
  W(fun (asl,w) ->
     let lk = lhs w in
     let tk = rand(lhand(lhand(rand(lhand(lhand lk))))) in
     let fth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D10_FIELD)
          (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                         (mk_small_numeral k) `4`)))) in
     let st = rand(lhand(concl fth)) in
     let st' = subst [`w:40 word`,`word(n DIV 2 EXP (40 * i)):40 word`] st in
     SUBGOAL_THEN (mk_eq(tk,mk_comb(`word_zx:10 word->int16`,st')))
       SUBST1_TAC THENL [BITBLAST_TAC; ALL_TAC] THEN
     REWRITE_TAC[D10_LANE] THEN EXPAND_TAC "w" THEN REWRITE_TAC[fth] THEN
     REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 10 in common/fips203.ml, the   *)
(* result for a 10-bit field y is the integer closest to 3329 * y / 1024,    *)
(* rounding up on ties, i.e. (3329 * y + 512) DIV 1024.                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,320)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlk_poly_decompress_d10_c) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,320)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (10 * i)) MOD 2 EXP 10 +
                                512) DIV 1024))
             (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_decompress_d10_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 320]", "true")],
   "void",
   [("a", "320", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:
      [`word(pc + mlk_poly_decompress_d10_c_consts):int64`,`16`]
    ~keep_maychanges:true
    mlkem_native_poly_decompress_d10_signature
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_MONO_EXEC;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,320]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlk_poly_decompress_d10_c) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2
                         [a,320; r,512;
                          word (pc + mlk_poly_decompress_d10_c_consts),16]
                         [r,512]))
               (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7] ,,
                MAYCHANGE [Q0; Q1; Q2; Q3] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;
