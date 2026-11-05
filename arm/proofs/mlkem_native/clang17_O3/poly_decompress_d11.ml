(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 11 bits per coefficient. This is the   *)
(* code for mlkem_poly_decompress_d11 from mlkem-native's portable C         *)
(* implementation compiled by clang 17 with -O3 (see mlkem_native/README.md),*)
(* which the compiler has partly vectorized: four of the eight coefficients  *)
(* of an iteration are computed in a vector register (with the shifts and    *)
(* masks for the fields from two 16-byte constants of the read-only data)    *)
(* and stored together, the others one by one. It is verified in the whole   *)
(* image (see libmlkem.ml).                                                  *)
(*                                                                           *)
(* The specifications are those of gcc12_O2, so that the safety theorem has  *)
(* the constants among the regions read, here the 32 bytes of both of them.  *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d11:
       +0x0: mov     w9, #0xd01
       +0x4: adrp    x11, <page>
       +0x8: adrp    x12, <page>
       +0xc: mov     x8, xzr
      +0x10: add     x10, x1, #0x5
      +0x14: dup     v1.4h, w9
      +0x18: ldr     q0, [x11, #1024]
      +0x1c: ldr     q2, [x12, #1040]
      +0x20: mov     w11, #0x400
      +0x24: ldurb   w13, [x10, #-4]
      +0x28: add     x2, x0, x8
      +0x2c: ldurb   w14, [x10, #-3]
      +0x30: add     x8, x8, #0x10
      +0x34: ldurb   w12, [x10, #-5]
      +0x38: cmp     x8, #0x200
      +0x3c: fmov    s3, w13
      +0x40: ldurb   w16, [x10, #-1]
      +0x44: lsr     w13, w13, #3
      +0x48: ldurb   w15, [x10, #-2]
      +0x4c: fmov    s4, w12
      +0x50: ldrb    w17, [x10]
      +0x54: mov     v3.h[1], w14
      +0x58: lsr     w14, w14, #6
      +0x5c: orr     w14, w14, w15, lsl #2
      +0x60: ldrb    w18, [x10, #1]
      +0x64: mov     v4.s[1], w13
      +0x68: lsr     w13, w16, #1
      +0x6c: ldrb    w1, [x10, #2]
      +0x70: lsr     w15, w17, #4
      +0x74: mov     v3.h[2], w16
      +0x78: ldrb    w3, [x10, #3]
      +0x7c: ldrb    w12, [x10, #4]
      +0x80: lsr     w16, w18, #7
      +0x84: mov     v4.s[2], w14
      +0x88: ldrb    w4, [x10, #5]
      +0x8c: lsr     w14, w3, #2
      +0x90: orr     w16, w16, w1, lsl #1
      +0x94: mov     v3.h[3], w17
      +0x98: lsr     w17, w12, #5
      +0x9c: bfi     w15, w18, #4, #7
      +0xa0: bfi     w14, w12, #6, #5
      +0xa4: mov     v4.s[3], w13
      +0xa8: orr     w12, w17, w4, lsl #3
      +0xac: bfi     w16, w3, #9, #2
      +0xb0: madd    w13, w15, w9, w11
      +0xb4: uxtl    v3.4s, v3.4h
      +0xb8: madd    w14, w14, w9, w11
      +0xbc: madd    w15, w16, w9, w11
      +0xc0: lsr     w13, w13, #11
      +0xc4: ushl    v3.4s, v3.4s, v0.4s
      +0xc8: madd    w12, w12, w9, w11
      +0xcc: lsr     w14, w14, #11
      +0xd0: lsr     w15, w15, #11
      +0xd4: and     v3.16b, v3.16b, v2.16b
      +0xd8: lsr     w12, w12, #11
      +0xdc: orr     v3.16b, v3.16b, v4.16b
      +0xe0: add     x10, x10, #0xb
      +0xe4: xtn     v3.4h, v3.4s
      +0xe8: strh    w13, [x2, #8]
      +0xec: strh    w14, [x2, #12]
      +0xf0: umull   v3.4s, v3.4h, v1.4h
      +0xf4: strh    w15, [x2, #10]
      +0xf8: strh    w12, [x2, #14]
      +0xfc: rshrn   v3.4h, v3.4s, #11
      +0x100: str     d3, [x2]
      +0x104: b.ne    <mlkem_poly_decompress_d11+0x24>
      +0x108: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_decompress_d11"];;

let WORD_ADD_2EXP64 = prove
 (`!n. word(n + 18446744073709551616):int64 = word n`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_CONSTANTS =
  CONJ (MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlkem_poly_decompress_d11_const1") 128)
       (MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlkem_poly_decompress_d11_const2") 128);;

(*** The loads are at offsets from -5 to 5 from x10 = (a + 5) + 11 * i, and
 *** the simulation leaves the sums of the numbers in the address unevaluated,
 *** so the facts about the bytes are put in that form. ***)

let DECOMPRESS_D11_ADDR = prove
 (`!(a:int64) i. word_add a (word(11 * i)) =
         word_add a (word(5 + 11 * i + 18446744073709551611)) /\
         word_add a (word(11 * i + 1)) =
         word_add a (word(5 + 11 * i + 18446744073709551612)) /\
         word_add a (word(11 * i + 2)) =
         word_add a (word(5 + 11 * i + 18446744073709551613)) /\
         word_add a (word(11 * i + 3)) =
         word_add a (word(5 + 11 * i + 18446744073709551614)) /\
         word_add a (word(11 * i + 4)) =
         word_add a (word(5 + 11 * i + 18446744073709551615)) /\
         word_add a (word(11 * i + 5)) =
         word_add a (word(5 + 11 * i)) /\
         word_add a (word(11 * i + 6)) =
         word_add a (word(5 + 11 * i + 1)) /\
         word_add a (word(11 * i + 7)) =
         word_add a (word(5 + 11 * i + 2)) /\
         word_add a (word(11 * i + 8)) =
         word_add a (word(5 + 11 * i + 3)) /\
         word_add a (word(11 * i + 9)) =
         word_add a (word(5 + 11 * i + 4)) /\
         word_add a (word(11 * i + 10)) =
         word_add a (word(5 + 11 * i + 5))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `5 + 11 * i + 18446744073709551611 = 11 * i + 18446744073709551616`;
              ARITH_RULE `5 + 11 * i + 18446744073709551612 = (11 * i + 1) + 18446744073709551616`;
              ARITH_RULE `5 + 11 * i + 18446744073709551613 = (11 * i + 2) + 18446744073709551616`;
              ARITH_RULE `5 + 11 * i + 18446744073709551614 = (11 * i + 3) + 18446744073709551616`;
              ARITH_RULE `5 + 11 * i + 18446744073709551615 = (11 * i + 4) + 18446744073709551616`;
              ARITH_RULE `5 + 11 * i = 11 * i + 5`;
              ARITH_RULE `5 + 11 * i + 1 = 11 * i + 6`;
              ARITH_RULE `5 + 11 * i + 2 = 11 * i + 7`;
              ARITH_RULE `5 + 11 * i + 3 = 11 * i + 8`;
              ARITH_RULE `5 + 11 * i + 4 = 11 * i + 9`;
              ARITH_RULE `5 + 11 * i + 5 = 11 * i + 10`; WORD_ADD_2EXP64]);;

(*** The same for the stores, at offsets 0 and 8 to 14 from x2 = r + 16 * i ***)

let DECOMPRESS_D11_STORE_ADDR = prove
 (`!(r:int64) i.
     word_add (word_add r (word(16 * i))) (word 8) = word_add r (word(16 * i + 8)) /\
     word_add (word_add r (word(16 * i))) (word 10) = word_add r (word(16 * i + 10)) /\
     word_add (word_add r (word(16 * i))) (word 12) = word_add r (word(16 * i + 12)) /\
     word_add (word_add r (word(16 * i))) (word 14) = word_add r (word(16 * i + 14))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

(*** The same for the addresses in the events of the safety proof ***)

let DECOMPRESS_D11_EVENT_ADDR = prove
 (`(!(a:int64) i. word_add (word_add (word_add a (word 5)) (word(11 * i))) (word 18446744073709551611) =
     word_add a (word(11 * i)) /\
     word_add (word_add (word_add a (word 5)) (word(11 * i))) (word 18446744073709551612) =
     word_add a (word(11 * i + 1)) /\
     word_add (word_add (word_add a (word 5)) (word(11 * i))) (word 18446744073709551613) =
     word_add a (word(11 * i + 2)) /\
     word_add (word_add (word_add a (word 5)) (word(11 * i))) (word 18446744073709551614) =
     word_add a (word(11 * i + 3)) /\
     word_add (word_add (word_add a (word 5)) (word(11 * i))) (word 18446744073709551615) =
     word_add a (word(11 * i + 4)) /\
     word_add (word_add a (word 5)) (word(11 * i)) =
     word_add a (word(11 * i + 5)) /\
     word_add (word_add (word_add a (word 5)) (word(11 * i))) (word 1) =
     word_add a (word(11 * i + 6)) /\
     word_add (word_add (word_add a (word 5)) (word(11 * i))) (word 2) =
     word_add a (word(11 * i + 7)) /\
     word_add (word_add (word_add a (word 5)) (word(11 * i))) (word 3) =
     word_add a (word(11 * i + 8)) /\
     word_add (word_add (word_add a (word 5)) (word(11 * i))) (word 4) =
     word_add a (word(11 * i + 9)) /\
     word_add (word_add (word_add a (word 5)) (word(11 * i))) (word 5) =
     word_add a (word(11 * i + 10))) /\
   (!(r:int64) i.
     word_add (word_add r (word(16 * i))) (word 8) = word_add r (word(16 * i + 8)) /\
     word_add (word_add r (word(16 * i))) (word 10) = word_add r (word(16 * i + 10)) /\
     word_add (word_add r (word(16 * i))) (word 12) = word_add r (word(16 * i + 12)) /\
     word_add (word_add r (word(16 * i))) (word 14) = word_add r (word(16 * i + 14)))`,
  SUBGOAL_THEN
   `word 18446744073709551611:int64 = word_neg(word 5) /\
    word 18446744073709551612:int64 = word_neg(word 4) /\
    word 18446744073709551613:int64 = word_neg(word 3) /\
    word 18446744073709551614:int64 = word_neg(word 2) /\
    word 18446744073709551615:int64 = word_neg(word 1)`
  STRIP_ASSUME_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;


(* ------------------------------------------------------------------------- *)
(* The eleven bytes for eight coefficients, as parts of an 88-bit word.      *)
(* ------------------------------------------------------------------------- *)

let D11_BYTES = prove
 (`!a n i s j.
        read (memory :> bytes(a,352)) s = n /\ i < 32 /\ j < 11
        ==> read (memory :> bytes8(word_add a (word(11 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (88 * i)):88 word) (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `352`; `n:num`; `11 * i + j`; `s:armstate`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (11 * i + j) = 88 * i + 8 * j`]);;

let D11_HALF = prove
 (`!a n i s.
        read (memory :> bytes(a,352)) s = n /\ i < 32
        ==> read (memory :> bytes16(word_add a (word(11 * i)))) s =
            word_subword (word(n DIV 2 EXP (88 * i)):88 word) (0,16)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `352`; `n:num`; `11 * i`; `s:armstate`]
                READ_MEMORY_BYTES16_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EXP; DIV_1; ARITH_RULE `2 EXP 16 = 65536`] THEN
  REWRITE_TAC[ARITH_RULE `8 * 11 * i = 88 * i`]);;


(* ------------------------------------------------------------------------- *)
(* The 11-bit field k of the 88 bits as part of the number for the input.    *)
(* ------------------------------------------------------------------------- *)

let D11D_FIELD = prove
 (`!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (88 * i)):88 word)
                          (11 * k,11):11 word) =
         (n DIV 2 EXP (11 * (8 * i + k))) MOD 2048`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 11 11 = 11`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 8 ==> 11 * k + 11 <= 88`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2048 = 2 EXP 11`] THEN
  REWRITE_TAC[ARITH_RULE `88 * i + 11 * k = 11 * (8 * i + k)`]);;


(* ------------------------------------------------------------------------- *)
(* The stored coefficients. Each 16-bit part of the 128-bit store is the     *)
(* low half of (y * 3329 + 1024) >> 11 for a 32-bit value y made from the    *)
(* input bytes, after SIMD_SIMPLIFY_CONV (LANE_RULE would find it by         *)
(* bit-blasting if it were part of a larger term). The lane is shown to be   *)
(* (3329 * f + 1024) DIV 2048 for the 11-bit field f of the 88 bits by       *)
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

let d11_lanepats =
 [`word_subword (word_ushr (x:int32) 11) (0,16):int16`;
  `word_subword (x:int32) (11,16):int16`];;

(* ------------------------------------------------------------------------- *)
(* The lanes of the stores. Each 16-bit part of what is stored is a function *)
(* of the 88 bits w of the input of the iteration (made from its bytes) in   *)
(* which, on the way to the product with 3329, only bit operations are       *)
(* applied to w: a maximal subterm that is zero extended from the field of   *)
(* 11 bits k of w. Once this is found by bit-blasting, what is left is a     *)
(* function of the field, checked for all 2048 values; with the vector code, *)
(* the lane is first found in the store by bit-blasting, as for the 4-bit    *)
(* fields.                                                                   *)
(* ------------------------------------------------------------------------- *)

let d11_pure w t =
  (match type_of t with Tyapp("word",_) -> true | _ -> false) &&
  free_in w t &&
  not(can (find_term (fun x -> match x with
        Const(("val"|"word_mul"|"word_add"),_) -> true | _ -> false)) t);;

let rec d11_max_pure w t acc =
  if d11_pure w t then t::acc else
  match t with
    Comb(f,x) -> d11_max_pure w f (d11_max_pure w x acc)
  | Abs(_,b) -> d11_max_pure w b acc
  | _ -> acc;;

let d11_lane_cache : (term * thm) list ref = ref [];;

let D11_LANE_FIELD_RULE th =
  let w = `w:88 word` and fv = `f:11 word` in
  let l = rand(concl th) in
  let q = match setify(d11_max_pure w l []) with
      [q] -> q | _ -> failwith "D11_LANE_FIELD_RULE: no unique input" in
  let zx = inst [`:11`,`:A`; hd(snd(dest_type(type_of q))),`:B`]
                `word_zx:A word->B word` in
  let rec find k =
    if k > 7 then failwith "D11_LANE_FIELD_RULE: no field" else
    let f = mk_comb(mk_comb(`word_subword:88 word->num#num->11 word`,w),
                    mk_pair(mk_small_numeral(11 * k),`11`)) in
    try f,BITBLAST_RULE(mk_eq(q,mk_comb(zx,f))) with Failure _ -> find (k+1) in
  let f,qth = find 0 in
  let lgen = subst [mk_comb(zx,fv),q] l in
  let lem =
    try assoc lgen !d11_lane_cache with Failure _ ->
      let vv = `v:num` in
      let stmt_v = mk_forall(vv,mk_imp(`v < 2048`,
        mk_eq(subst [mk_comb(`word:num->11 word`,vv),fv] lgen,
              `word((3329 * v + 1024) DIV 2048):int16`))) in
      let lem = prove(mk_eq(lgen,`word((3329 * val(f:11 word) + 1024) DIV 2048):int16`),
        SUBGOAL_THEN stmt_v (MP_TAC o SPEC `val(f:11 word)`) THENL
         [CONV_TAC EXPAND_CASES_CONV THEN
          CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));
          REWRITE_TAC[WORD_VAL] THEN DISCH_THEN MATCH_MP_TAC THEN
          MP_TAC(ISPEC `f:11 word` VAL_BOUND) THEN
          CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC]) in
      d11_lane_cache := (lgen,lem)::!d11_lane_cache; lem in
  let e1 = PURE_REWRITE_CONV [qth] l in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th (TRANS e1 (INST [f,fv] lem)));;

(*** The atoms of the vector lanes ***)

let d11_vecpat =
  `word((val(word_mul (word_zx (t:int16):int32) (word 3329)) + 1024) DIV 2048):
   int16`;;

let D11_VEC_LANE_RULE th =
  let v = rand(concl th) in
  let ls = setify(find_terms (can (term_match [] d11_vecpat)) v) in
  let gs = map (fun t -> genvar(type_of t)) ls in
  let v' = subst (zip gs ls) v in
  let bth = tryfind (fun g -> BITBLAST_RULE(mk_eq(v',g))) gs in
  TRANS th (INST (zip ls gs) bth);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 11 in common/fips203.ml, the   *)
(* result for an 11-bit field y is the integer closest to 3329 * y / 2048,   *)
(* rounding up on ties, i.e. (3329 * y + 1024) DIV 2048.                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,352)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_decompress_d11) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,352)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (11 * i)) MOD 2 EXP 11 +
                                1024) DIV 2048))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the test at the top of the body ***)

  ENSURES_WHILE_UP2_TAC `32` `pc + mlkem_poly_decompress_d11_loop1`
   `pc + mlkem_poly_decompress_d11_loop1_exit`
   `\i s. read X0 s = r /\
          read X8 s = word(16 * i) /\
          read X9 s = word 3329 /\
          read X10 s = word_add (word_add a (word 5)) (word(11 * i)) /\
          read X11 s = word 1024 /\
          read Q0 s = word 0x70000000a0000000500000008 /\
          read Q1 s = word 0x0d010d010d010d01 /\
          read Q2 s = word 0x78000000400000007e000000700 /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,352)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (11 * j)) MOD 2 EXP 11 + 1024)
                        DIV 2048))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the constants from the image ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(fun th -> MAP_EVERY (fun c -> ASSUME_TAC(MATCH_MP c th))
      (CONJUNCTS MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_CONSTANTS)) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (3--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (4--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for eleven bytes and eight coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun j ->
      MP_TAC(REWRITE_RULE[ADD_CLAUSES]
       (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
         (SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`;
                 mk_small_numeral j] D11_BYTES))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) (0--10) THEN
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read (memory :> bytes8 x) s = y`) (concl th)
      then REWRITE_RULE[DECOMPRESS_D11_ADDR] th else th) THEN
    ABBREV_TAC `w:88 word = word(n DIV 2 EXP (88 * i))` THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--57) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DECOMPRESS_D11_STORE_ADDR]) THEN
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read (memory :> bytes16 a) s = x`) (concl th)
      then D11_LANE_FIELD_RULE th else th) THEN
    FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match [] `read (memory :> bytes64 a) s = x`) o
             concl)) THEN
    DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o D11_LANE_FIELD_RULE o
                         D11_VEC_LANE_RULE o
                         CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])))
                         (CONJUNCTS th)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_add (word(16 * i)) (word 18446744073709551120):int64) = 0) <=>
      i + 1 < 32`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      ASM_CASES_TAC `i = 31` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 32 /\ ~(i = 31)
        ==> 16 * i + 18446744073709551120 < 18446744073709551616`] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC;
      REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC]) THEN
    REWRITE_TAC[ARITH_RULE
     `j < 8 * (i + 1) <=>
      j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
      j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
      j = 8 * i + 7`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * 8 * i = 16 * i`;
                ARITH_RULE `2 * (8 * i + 1) = 16 * i + 2`;
                ARITH_RULE `2 * (8 * i + 2) = 16 * i + 4`;
                ARITH_RULE `2 * (8 * i + 3) = 16 * i + 6`;
                ARITH_RULE `2 * (8 * i + 4) = 16 * i + 8`;
                ARITH_RULE `2 * (8 * i + 5) = 16 * i + 10`;
                ARITH_RULE `2 * (8 * i + 6) = 16 * i + 12`;
                ARITH_RULE `2 * (8 * i + 7) = 16 * i + 14`] THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "w" THEN
    REWRITE_TAC(map (fun k ->
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
       (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D11D_FIELD)
           (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                         (mk_small_numeral k) `8`))))) (0--7)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

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
      [`word(pc + mlkem_poly_decompress_d11_consts):int64`,`32`]
    ~keep_maychanges:true
    mlkem_native_poly_decompress_d11_signature
    MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,352]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
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
                          word (pc + mlkem_poly_decompress_d11_consts),32]
                         [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc returnaddress)
        (APPEND
          (ENUMERATEL 32 (\i. f_ev_loop a r pc returnaddress i))
          (f_ev_prol a r pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_decompress_d11_loop1`
   `pc + mlkem_poly_decompress_d11_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = r /\
           read X8 s = word(16 * i) /\
           read X10 s = word_add (word_add a (word 5)) (word(11 * i))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (3--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (4--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (1--57) THEN
  SUBGOAL_THEN
   `~(val(word_add (word(16 * i)) (word 18446744073709551120):int64) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    ASM_CASES_TAC `i = 31` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 /\ ~(i = 31)
      ==> 16 * i + 18446744073709551120 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`;
                ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  REWRITE_TAC[DECOMPRESS_D11_EVENT_ADDR] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
