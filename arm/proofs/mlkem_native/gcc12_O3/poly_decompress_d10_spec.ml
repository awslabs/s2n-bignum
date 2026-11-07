(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 10 bits per coefficient. This is the   *)
(* code for mlkem_poly_decompress_d10 from mlkem-native's portable C         *)
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

    mlkem_poly_decompress_d10:
       +0x0: movi    v1.4s, #0x2, lsl #8
       +0x4: mov     x2, x1
       +0x8: mov     x7, x0
       +0xc: add     x9, x1, #0x140
      +0x10: mov     w6, #0xd01
      +0x14: nop
      +0x18: ldrb    w1, [x2, #2]
      +0x1c: add     x2, x2, #0x5
      +0x20: ldurb   w3, [x2, #-4]
      +0x24: ldurh   w0, [x2, #-5]
      +0x28: lsl     w4, w1, #6
      +0x2c: ldurb   w5, [x2, #-2]
      +0x30: orr     w3, w4, w3, lsr #2
      +0x34: and     w0, w0, #0x3ff
      +0x38: and     w3, w3, #0x3ff
      +0x3c: ldurb   w4, [x2, #-1]
      +0x40: lsl     w8, w5, #4
      +0x44: lsr     w5, w5, #6
      +0x48: mul     w0, w0, w6
      +0x4c: orr     w1, w8, w1, lsr #4
      +0x50: fmov    s0, w0
      +0x54: mul     w0, w3, w6
      +0x58: and     w1, w1, #0x3ff
      +0x5c: orr     w3, w5, w4, lsl #2
      +0x60: mov     v0.s[1], w0
      +0x64: mul     w1, w1, w6
      +0x68: mul     w0, w3, w6
      +0x6c: mov     v0.s[2], w1
      +0x70: mov     v0.s[3], w0
      +0x74: add     v0.4s, v0.4s, v1.4s
      +0x78: shrn    v0.4h, v0.4s, #10
      +0x7c: str     d0, [x7], #8
      +0x80: cmp     x2, x9
      +0x84: b.ne    <mlkem_poly_decompress_d10+0x18>
      +0x88: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_decompress_d10"];;

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
(* The 10-bit field k of the 40 bits as part of the number for the input.    *)
(* ------------------------------------------------------------------------- *)

let D10_FIELD_STMT =
  `!n i k. k < 4
     ==> val(word_subword (word(n DIV 2 EXP (40 * i)):40 word)
                          (10 * k,10):10 word) =
         (n DIV 2 EXP (10 * (4 * i + k))) MOD 1024`;;

let D10_FIELD = assume_spec D10_FIELD_STMT;;

(* ------------------------------------------------------------------------- *)
(* The stored coefficients. Each lane of the 64-bit store is the low half of *)
(* (y * 3329 + 512) >> 10 for a 32-bit value y made from the input bytes,    *)
(* found in the store by bit-blasting (LANE_RULE). The lane is shown to be   *)
(* (3329 * f + 512) DIV 1024 for the 10-bit field f of the 40 bits, by       *)
(* bit-blasting y into the zero extension of f and then by arithmetic on the *)
(* small values involved (DECOMPRESS_LANE_TAC), whatever the nesting of the  *)
(* zero extensions from the moves between registers.                         *)
(* ------------------------------------------------------------------------- *)

let LANE_RULE pat th =
  let v = rand(concl th) in
  let ls = setify(find_terms (fun t -> can (term_match [] pat) t) v) in
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

let d10_lanepat = `word_subword (word_ushr (x:int32) 10) (0,16):int16`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 10 in common/fips203.ml, the   *)
(* result for a 10-bit field y is the integer closest to 3329 * y / 1024,    *)
(* rounding up on ties, i.e. (3329 * y + 512) DIV 1024.                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,320)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_poly_decompress_d10) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,320)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (10 * i)) MOD 2 EXP 10 +
                                512) DIV 1024))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

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
    ~keep_maychanges:true
    mlkem_native_poly_decompress_d10_signature
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O3_EXEC;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,320]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_decompress_d10) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,320; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
