(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 11 bits per coefficient. This is the   *)
(* code for mlkem_poly_decompress_d11 from mlkem-native's portable C         *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see                                    *)
(* libmlkem.ml), with a vector of constants.                                 *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d11:
       +0x0: mov     x8, x0
       +0x4: adrp    x0, <page>
       +0x8: movi    v2.4s, #0x4, lsl #8
       +0xc: add     x9, x1, #0x160
      +0x10: ldr     q3, [x0, #528]
      +0x14: nop
      +0x18: add     x1, x1, #0xb
      +0x1c: ldurb   w5, [x1, #-9]
      +0x20: ldurb   w6, [x1, #-10]
      +0x24: ldurb   w4, [x1, #-7]
      +0x28: lsl     w2, w5, #5
      +0x2c: ldurh   w0, [x1, #-11]
      +0x30: orr     w6, w2, w6, lsr #3
      +0x34: ldurb   w2, [x1, #-8]
      +0x38: and     w6, w6, #0x7ff
      +0x3c: and     w0, w0, #0x7ff
      +0x40: fmov    s0, w0
      +0x44: lsl     w0, w4, #10
      +0x48: orr     w0, w0, w2, lsl #2
      +0x4c: ldurb   w3, [x1, #-6]
      +0x50: mov     v0.h[1], w6
      +0x54: orr     w5, w0, w5, lsr #6
      +0x58: and     w5, w5, #0x7ff
      +0x5c: ldurb   w2, [x1, #-5]
      +0x60: lsl     w0, w3, #7
      +0x64: ldurb   w7, [x1, #-4]
      +0x68: mov     v1.16b, v2.16b
      +0x6c: orr     w4, w0, w4, lsr #1
      +0x70: mov     v0.h[2], w5
      +0x74: and     w4, w4, #0x7ff
      +0x78: ldurb   w0, [x1, #-3]
      +0x7c: lsl     w6, w2, #4
      +0x80: orr     w3, w6, w3, lsr #4
      +0x84: ldurb   w5, [x1, #-2]
      +0x88: and     w3, w3, #0x7ff
      +0x8c: ldurb   w6, [x1, #-1]
      +0x90: mov     v0.h[3], w4
      +0x94: lsl     w10, w0, #9
      +0x98: mov     v4.16b, v2.16b
      +0x9c: orr     w4, w10, w7, lsl #1
      +0xa0: orr     w2, w4, w2, lsr #7
      +0xa4: lsl     w4, w5, #6
      +0xa8: and     w2, w2, #0x7ff
      +0xac: orr     w0, w4, w0, lsr #2
      +0xb0: mov     v0.h[4], w3
      +0xb4: and     w0, w0, #0x7ff
      +0xb8: ubfx    x5, x5, #5, #16
      +0xbc: orr     w3, w5, w6, lsl #3
      +0xc0: mov     v0.h[5], w2
      +0xc4: mov     v0.h[6], w0
      +0xc8: mov     v0.h[7], w3
      +0xcc: umlal   v1.4s, v0.4h, v3.4h
      +0xd0: umlal2  v4.4s, v0.8h, v3.8h
      +0xd4: shrn    v0.4h, v1.4s, #11
      +0xd8: shrn2   v0.8h, v4.4s, #11
      +0xdc: str     q0, [x8], #16
      +0xe0: cmp     x9, x1
      +0xe4: b.ne    <mlkem_poly_decompress_d11+0x18>
      +0xe8: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem_poly_decompress_d11"];;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_CONSTANTS =
  MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlkem_poly_decompress_d11_consts")
   128;;

(* ------------------------------------------------------------------------- *)
(* The eleven bytes for eight coefficients, as parts of an 88-bit word.      *)
(* ------------------------------------------------------------------------- *)

let D11_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,352)) s = n /\ i < 32 /\ j < 11
        ==> read (memory :> bytes8(word_add a (word(11 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (88 * i)):88 word) (8 * j,8)`;;

let D11_BYTES = assume_spec D11_BYTES_STMT;;

let D11_HALF_STMT =
  `!a n i s.
        read (memory :> bytes(a,352)) s = n /\ i < 32
        ==> read (memory :> bytes16(word_add a (word(11 * i)))) s =
            word_subword (word(n DIV 2 EXP (88 * i)):88 word) (0,16)`;;

let D11_HALF = assume_spec D11_HALF_STMT;;

(* ------------------------------------------------------------------------- *)
(* The computation for each coefficient, with its 11-bit field f in the 88   *)
(* bits, and the field as part of the number for the input bytes. The        *)
(* stored lanes are found in the 128-bit store by bit-blasting.              *)
(* ------------------------------------------------------------------------- *)

let D11D_LANE_STMT =
  `!f:11 word.
     word_subword
      (word_ushr
        (word_add
          (word_mul (word_zx (word_zx f:int16):int32) (word 3329))
          (word 1024)) 11) (0,16):int16 =
     word((3329 * val f + 1024) DIV 2048)`;;

let D11D_LANE = assume_spec D11D_LANE_STMT;;

let D11D_FIELD_STMT =
  `!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (88 * i)):88 word)
                          (11 * k,11):11 word) =
         (n DIV 2 EXP (11 * (8 * i + k))) MOD 2048`;;

let D11D_FIELD = assume_spec D11D_FIELD_STMT;;

let d11d_lanepat =
  `word_subword
    (word_ushr
      (word_add (word_mul (word_zx (t:int16):int32) (word 3329))
                (word 1024)) 11) (0,16):int16`;;

let D11D_LANE_RULE th =
  let v = rand(concl th) in
  let ls = find_terms (fun t -> can (term_match [] d11d_lanepat) t) v in
  let gs = map (fun t -> genvar(type_of t)) ls in
  let v' = subst (zip gs ls) v in
  let bth = tryfind (fun g -> BITBLAST_RULE(mk_eq(v',g))) gs in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th (INST (zip ls gs) bth));;

let D11D_FIELD_TAC k =
  W(fun (asl,w) ->
     let lk = lhs w in
     let _,tmins,_ = term_match [] d11d_lanepat lk in
     let tk = rev_assoc `t:int16` tmins in
     let fth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D11D_FIELD)
          (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                         (mk_small_numeral k) `8`)))) in
     let st = rand(lhand(concl fth)) in
     let st' = subst [`w:88 word`,`word(n DIV 2 EXP (88 * i)):88 word`] st in
     SUBGOAL_THEN (mk_eq(tk,mk_comb(`word_zx:11 word->int16`,st')))
       SUBST1_TAC THENL
      [W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)); ALL_TAC] THEN
     REWRITE_TAC[D11D_LANE] THEN EXPAND_TAC "w" THEN REWRITE_TAC[fth] THEN
     REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 11 in common/fips203.ml, the   *)
(* result for an 11-bit field y is the integer closest to 3329 * y / 2048,   *)
(* rounding up on ties, i.e. (3329 * y + 1024) DIV 2048.                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,352)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem_poly_decompress_d11) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,352)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (11 * i)) MOD 2 EXP 11 +
                                1024) DIV 2048))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_decompress_d11_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 352]", "true")],
   "void",
   [("a", "352", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:
      [`word(pc + mlkem_poly_decompress_d11_consts):int64`,`16`]
    ~keep_maychanges:true
    mlkem_native_poly_decompress_d11_signature
    MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,352]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem_poly_decompress_d11) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2
                         [a,352; r,512;
                          word (pc + mlkem_poly_decompress_d11_consts),16]
                         [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
