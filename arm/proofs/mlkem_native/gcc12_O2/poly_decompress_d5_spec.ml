(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 5 bits per coefficient. This is the    *)
(* code for mlkem_poly_decompress_d5 from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see                                    *)
(* libmlkem.ml), with a vector of constants.                                 *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d5:
       +0x0: mov     x6, x0
       +0x4: adrp    x0, <page>
       +0x8: movi    v2.4s, #0x10
       +0xc: add     x9, x1, #0xa0
      +0x10: ldr     q3, [x0, #528]
      +0x14: nop
      +0x18: add     x1, x1, #0x5
      +0x1c: ldurb   w0, [x1, #-4]
      +0x20: ldurb   w2, [x1, #-5]
      +0x24: mov     v4.16b, v2.16b
      +0x28: ldurb   w3, [x1, #-3]
      +0x2c: lsl     w4, w0, #3
      +0x30: and     w5, w2, #0x1f
      +0x34: orr     w2, w4, w2, lsr #5
      +0x38: fmov    s0, w5
      +0x3c: and     w4, w2, #0x1f
      +0x40: ubfx    x7, x0, #2, #5
      +0x44: lsl     w2, w3, #1
      +0x48: ldurb   w5, [x1, #-1]
      +0x4c: mov     v0.b[1], w4
      +0x50: orr     w2, w2, w0, lsr #7
      +0x54: ldurb   w0, [x1, #-2]
      +0x58: and     w2, w2, #0x1f
      +0x5c: fmov    s1, w5
      +0x60: mov     v0.b[2], w7
      +0x64: lsl     w8, w0, #4
      +0x68: orr     w3, w8, w3, lsr #4
      +0x6c: ubfx    x4, x0, #1, #5
      +0x70: and     w3, w3, #0x1f
      +0x74: lsl     w8, w5, #2
      +0x78: orr     w0, w8, w0, lsr #6
      +0x7c: ushr    v1.2s, v1.2s, #3
      +0x80: mov     v0.b[3], w2
      +0x84: and     w0, w0, #0x1f
      +0x88: mov     v0.b[4], w3
      +0x8c: mov     v0.b[5], w4
      +0x90: mov     v0.b[6], w0
      +0x94: mov     v0.b[7], v1.b[0]
      +0x98: mov     v1.16b, v2.16b
      +0x9c: uxtl    v0.8h, v0.8b
      +0xa0: umlal   v1.4s, v0.4h, v3.4h
      +0xa4: umlal2  v4.4s, v0.8h, v3.8h
      +0xa8: shrn    v0.4h, v1.4s, #5
      +0xac: shrn2   v0.8h, v4.4s, #5
      +0xb0: str     q0, [x6], #16
      +0xb4: cmp     x1, x9
      +0xb8: b.ne    <mlkem_poly_decompress_d5+0x18>
      +0xbc: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem_poly_decompress_d5"];;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_CONSTANTS =
  MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlkem_poly_decompress_d5_consts")
   128;;

(* ------------------------------------------------------------------------- *)
(* The five bytes for eight coefficients, as parts of a 40-bit word.         *)
(* ------------------------------------------------------------------------- *)

let D5_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,160)) s = n /\ i < 32 /\ j < 5
        ==> read (memory :> bytes8(word_add a (word(5 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (40 * i)):40 word) (8 * j,8)`;;

let D5_BYTES = assume_spec D5_BYTES_STMT;;

(* ------------------------------------------------------------------------- *)
(* The computation for each coefficient, with its 5-bit field f in the 40    *)
(* bits, and the field as part of the number for the input bytes. The        *)
(* stored lanes are found in the 128-bit store by bit-blasting.              *)
(* ------------------------------------------------------------------------- *)

let D5D_LANE_STMT =
  `!f:5 word.
     word_subword
      (word_ushr
        (word_add
          (word_mul (word_zx (word_shl (word_zx (word_zx f:byte):int16) 0):
                     int32)
                    (word 3329))
          (word 16)) 5) (0,16):int16 =
     word((3329 * val f + 16) DIV 32)`;;

let D5D_LANE = assume_spec D5D_LANE_STMT;;

let D5D_FIELD_STMT =
  `!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (40 * i)):40 word)
                          (5 * k,5):5 word) =
         (n DIV 2 EXP (5 * (8 * i + k))) MOD 32`;;

let D5D_FIELD = assume_spec D5D_FIELD_STMT;;

let d5d_lanepat =
  `word_subword
    (word_ushr
      (word_add
        (word_mul (word_zx (word_shl (word_zx (t:byte):int16) 0):int32)
                  (word 3329))
        (word 16)) 5) (0,16):int16`;;

let D5D_LANE_RULE th =
  let v = rand(concl th) in
  let ls = find_terms (fun t -> can (term_match [] d5d_lanepat) t) v in
  let gs = map (fun t -> genvar(type_of t)) ls in
  let v' = subst (zip gs ls) v in
  let bth = tryfind (fun g -> BITBLAST_RULE(mk_eq(v',g))) gs in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th (INST (zip ls gs) bth));;

let D5D_FIELD_TAC k =
  W(fun (asl,w) ->
     let lk = lhs w in
     let _,tmins,_ = term_match [] d5d_lanepat lk in
     let tk = rev_assoc `t:byte` tmins in
     let fth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D5D_FIELD)
          (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                         (mk_small_numeral k) `8`)))) in
     let st = rand(lhand(concl fth)) in
     let st' = subst [`w:40 word`,`word(n DIV 2 EXP (40 * i)):40 word`] st in
     SUBGOAL_THEN (mk_eq(tk,mk_comb(`word_zx:5 word->byte`,st')))
       SUBST1_TAC THENL
      [W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)); ALL_TAC] THEN
     REWRITE_TAC[D5D_LANE] THEN EXPAND_TAC "w" THEN REWRITE_TAC[fth] THEN
     REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 5 in common/fips203.ml, the    *)
(* result for a 5-bit field y is the integer closest to 3329 * y / 32,       *)
(* rounding up on ties, i.e. (3329 * y + 16) DIV 32.                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,160)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem_poly_decompress_d5) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,160)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (5 * i)) MOD 2 EXP 5 +
                                16) DIV 32))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_decompress_d5_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 160]", "true")],
   "void",
   [("a", "160", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + mlkem_poly_decompress_d5_consts):int64`,`16`]
    ~keep_maychanges:true
    mlkem_native_poly_decompress_d5_signature
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,160]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem_poly_decompress_d5) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2
                         [a,160; r,512;
                          word (pc + mlkem_poly_decompress_d5_consts),16]
                         [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
