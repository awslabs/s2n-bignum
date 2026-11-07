(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 5 bits per coefficient. This is the    *)
(* code for mlkem_poly_decompress_d5 from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md),  *)
(* which the compiler has partly vectorized. It is verified in the whole     *)
(* image (see libmlkem.ml).                                                  *)
(*                                                                           *)
(* Unlike at -O2, the code loads no constants from the read-only data: the   *)
(* products by 3329 are scalar MULs. So the safety theorem has no read-only  *)
(* region for them, unlike that of gcc12_O2.                                 *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d5:
       +0x0: mov     x6, x1
       +0x4: mov     x8, x0
       +0x8: add     x9, x1, #0xa0
       +0xc: mov     w7, #0xd01
      +0x10: ldrb    w2, [x6, #1]
      +0x14: add     x6, x6, #0x5
      +0x18: ldurb   w0, [x6, #-5]
      +0x1c: ldurb   w3, [x6, #-2]
      +0x20: ldurb   w12, [x6, #-3]
      +0x24: lsl     w4, w2, #3
      +0x28: orr     w4, w4, w0, lsr #5
      +0x2c: and     w0, w0, #0x1f
      +0x30: lsl     w1, w3, #4
      +0x34: and     w4, w4, #0x1f
      +0x38: orr     w1, w1, w12, lsr #4
      +0x3c: ubfx    x11, x3, #1, #5
      +0x40: and     w1, w1, #0x1f
      +0x44: ldurb   w5, [x6, #-1]
      +0x48: mul     w4, w4, w7
      +0x4c: lsl     w12, w12, #1
      +0x50: mul     w0, w0, w7
      +0x54: add     w4, w4, #0x10
      +0x58: mul     w1, w1, w7
      +0x5c: fmov    s0, w4
      +0x60: mul     w11, w11, w7
      +0x64: lsl     w10, w5, #2
      +0x68: add     w0, w0, #0x10
      +0x6c: ushr    v2.2s, v0.2s, #5
      +0x70: orr     w3, w10, w3, lsr #6
      +0x74: add     w1, w1, #0x10
      +0x78: fmov    s0, w0
      +0x7c: fmov    s1, w1
      +0x80: add     w11, w11, #0x10
      +0x84: fmov    s3, w11
      +0x88: ubfx    x10, x2, #2, #5
      +0x8c: and     w3, w3, #0x1f
      +0x90: ushr    v0.2s, v0.2s, #5
      +0x94: ushr    v3.2s, v3.2s, #5
      +0x98: ushr    v1.2s, v1.2s, #5
      +0x9c: mul     w4, w10, w7
      +0xa0: orr     w0, w12, w2, lsr #7
      +0xa4: mul     w1, w3, w7
      +0xa8: and     w0, w0, #0x1f
      +0xac: mov     v0.s[1], v2.s[0]
      +0xb0: add     w2, w4, #0x10
      +0xb4: mov     v1.s[1], v3.s[0]
      +0xb8: add     w1, w1, #0x10
      +0xbc: fmov    s2, w2
      +0xc0: fmov    s3, w1
      +0xc4: lsr     w5, w5, #3
      +0xc8: mul     w0, w0, w7
      +0xcc: ushr    v2.2s, v2.2s, #5
      +0xd0: ushr    v3.2s, v3.2s, #5
      +0xd4: add     w0, w0, #0x10
      +0xd8: mul     w1, w5, w7
      +0xdc: mov     v0.s[2], v2.s[0]
      +0xe0: add     w1, w1, #0x10
      +0xe4: mov     v1.s[2], v3.s[0]
      +0xe8: fmov    s2, w0
      +0xec: fmov    s3, w1
      +0xf0: ushr    v2.2s, v2.2s, #5
      +0xf4: ushr    v3.2s, v3.2s, #5
      +0xf8: mov     v0.s[3], v2.s[0]
      +0xfc: mov     v1.s[3], v3.s[0]
     +0x100: uzp1    v0.8h, v0.8h, v1.8h
     +0x104: str     q0, [x8], #16
     +0x108: cmp     x9, x6
     +0x10c: b.ne    <mlkem_poly_decompress_d5+0x10>
     +0x110: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_decompress_d5"];;

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
(* The 5-bit field k of the 40 bits as part of the number for the input.     *)
(* ------------------------------------------------------------------------- *)

let D5D_FIELD_STMT =
  `!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (40 * i)):40 word)
                          (5 * k,5):5 word) =
         (n DIV 2 EXP (5 * (8 * i + k))) MOD 32`;;

let D5D_FIELD = assume_spec D5D_FIELD_STMT;;


(* ------------------------------------------------------------------------- *)
(* The stored coefficients. Each 16-bit part of the 128-bit store is the    *)
(* low half of (y * 3329 + 16) >> 5 for a 32-bit value y made from the input *)
(* bytes, after SIMD_SIMPLIFY_CONV (LANE_RULE would find it by bit-blasting  *)
(* if it were part of a larger term). The lane is shown to be                *)
(* (3329 * f + 16) DIV 32 for the 5-bit field f of the 40 bits by            *)
(* bit-blasting y into the zero extension of f and then by arithmetic on the *)
(* small values involved (DECOMPRESS_LANE_TAC), whatever the nesting of the  *)
(* zero extensions from the moves between registers.                         *)
(* ------------------------------------------------------------------------- *)

let LANE_RULE pats th =
  let v = rand(concl th) in
  if not(exists (fun p -> can (find_term (can (term_match [] p))) v) pats)
  then CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
        th else
  let ls = setify(find_terms (fun t -> exists (fun p -> can (term_match [] p) t) pats) v) in
  let gs = map (fun t -> genvar(type_of t)) ls in
  let v' = subst (zip gs ls) v in
  let bth = tryfind (fun g -> BITBLAST_RULE(mk_eq(v',g))) gs in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th (INST (zip ls gs) bth));;

let DECOMPRESS_LANE_TAC fieldth fieldk nk d c q =
  let fty = mk_type("word",[mk_finty(Num.num_of_int d)]) in
  let fv = mk_var("f",fty) in
  let valf = mk_comb(inst [mk_finty(Num.num_of_int d),`:N`]
                          `val:N word->num`,fv) in
  let rhs = subst [mk_small_numeral c,`c:num`; mk_small_numeral q,`q:num`;
                   valf,`v:num`]
                  `word((3329 * v + c) DIV q):int16` in
  W(fun (asl,w) ->
     let lk = lhs w in
     let tk = rand(find_term (fun t -> match t with
                  Comb(Const("val",_),_) -> true | _ -> false) lk) in
     let fth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (MP (SPEC (mk_small_numeral fieldk) fieldth)
          (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                         (mk_small_numeral fieldk) (mk_small_numeral nk))))) in
     let st = rand(lhand(concl fth)) in
     let wt = rand(rator st) in
     let st' = subst [mk_var("w",type_of wt),wt] st in
     let zx t = mk_comb(inst [mk_finty(Num.num_of_int d),`:A`;
                              hd(snd(dest_type(type_of tk))),`:B`]
                             `word_zx:A word->B word`, t) in
     let lth = GEN fv (prove(mk_eq(subst [zx fv,tk] lk,rhs),
       REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_USHR;
                   VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
       CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[DIV_1] THEN
       MP_TAC(ISPEC fv VAL_BOUND) THEN
       CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
       SPEC_TAC(valf,`v:num`) THEN
       REPEAT STRIP_TAC THEN REPEAT MOD_LT_ASM_TAC THEN
       AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC)) in
     SUBGOAL_THEN (mk_eq(tk,zx st')) SUBST1_TAC THENL
       [BITBLAST_TAC; ALL_TAC] THEN
     REWRITE_TAC[lth] THEN EXPAND_TAC "w" THEN REWRITE_TAC[fth] THEN
     REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let d5_lanepats =
 [`word_subword (word_ushr (x:int32) 5) (0,16):int16`;
  `word_subword (x:int32) (5,16):int16`];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 5 in common/fips203.ml, the    *)
(* result for a 5-bit field y is the integer closest to 3329 * y / 32,       *)
(* rounding up on ties, i.e. (3329 * y + 16) DIV 32.                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,160)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
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

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

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
    ~keep_maychanges:true
    mlkem_native_poly_decompress_d5_signature
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,160]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_decompress_d5) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,160; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
