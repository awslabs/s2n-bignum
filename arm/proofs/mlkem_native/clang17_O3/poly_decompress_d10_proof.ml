(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 10 bits per coefficient. This is the   *)
(* code for mlkem_poly_decompress_d10 from mlkem-native's portable C         *)
(* implementation compiled by clang 17 with -O3 (see mlkem_native/README.md).*)
(* It is verified in the whole image (see libmlkem.ml).                      *)
(*                                                                           *)
(* The compiler has vectorized the loop, 16 coefficients from 20 bytes per   *)
(* iteration with TBL and six 16-byte constants of the read-only data, after *)
(* a check that the input and the output do not overlap, with one branch for *)
(* each of the two orders of the arrays; if they overlap, the code falls     *)
(* back to a scalar loop. Since the specification requires them not to       *)
(* overlap, only the vector code runs. The safety theorem has the constants  *)
(* among the regions read, here the 96 bytes of all of them.                 *)
(*                                                                           *)
(* The registers are kept in the bit-level normal form of bitnorm.ml during  *)
(* the simulation, so that each lane before the product with 3329 is a       *)
(* 10-bit field of the 20 bytes and the stored lanes stay small.             *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/bitnorm.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d10:
       +0x0: add     x8, x1, #0x140
       +0x4: cmp     x8, x0
       +0x8: b.ls    <mlkem_poly_decompress_d10+0xa0>
       +0xc: add     x8, x0, #0x200
      +0x10: cmp     x8, x1
      +0x14: b.ls    join1                                ---+
      +0x18: mov     x8, xzr                                 |
      +0x1c: add     x9, x1, #0x2                            |
      +0x20: mov     w10, #0xd01                             |
      +0x24: mov     w11, #0x200                             |
      +0x28: ldurb   w12, [x9, #-2]                       <+ |
      +0x2c: ldurb   w13, [x9, #-1]                        | |
      +0x30: ldrb    w14, [x9]                             | |
      +0x34: ldrb    w15, [x9, #1]                         | |
      +0x38: ldrb    w17, [x9, #2]                         | |
      +0x3c: bfi     w12, w13, #8, #2                      | |
      +0x40: lsr     w13, w13, #2                          | |
      +0x44: lsr     w16, w14, #4                          | |
      +0x48: bfi     w13, w14, #6, #4                      | |
      +0x4c: lsr     w14, w15, #6                          | |
      +0x50: bfi     w16, w15, #4, #6                      | |
      +0x54: orr     w14, w14, w17, lsl #2                 | |
      +0x58: madd    w12, w12, w10, w11                    | |
      +0x5c: add     x9, x9, #0x5                          | |
      +0x60: madd    w13, w13, w10, w11                    | |
      +0x64: madd    w15, w16, w10, w11                    | |
      +0x68: lsr     w12, w12, #10                         | |
      +0x6c: madd    w14, w14, w10, w11                    | |
      +0x70: add     x16, x0, x8                           | |
      +0x74: lsr     w13, w13, #10                         | |
      +0x78: lsr     w15, w15, #10                         | |
      +0x7c: lsr     w14, w14, #10                         | |
      +0x80: add     x8, x8, #0x8                          | |
      +0x84: cmp     x8, #0x200                            | |
      +0x88: strh    w12, [x16]                            | |
      +0x8c: strh    w13, [x16, #2]                        | |
      +0x90: strh    w15, [x16, #4]                        | |
      +0x94: strh    w14, [x16, #6]                        | |
      +0x98: b.ne    loop1                                -+ |
      +0x9c: b       <mlkem_poly_decompress_d10+0x210>
      +0xa0: adrp    x9, <page>                           <--+-+
      +0xa4: adrp    x10, <page>
      +0xa8: adrp    x12, <page>
      +0xac: adrp    x11, <page>
      +0xb0: movi    v5.4s, #0x3, lsl #8
      +0xb4: mov     x8, xzr
      +0xb8: ldr     q0, [x9, #448]
      +0xbc: adrp    x9, <page>
      +0xc0: ldr     q1, [x10, #464]
      +0xc4: mov     w10, #0xd01
      +0xc8: ldr     q3, [x12, #496]
      +0xcc: adrp    x12, <page>
      +0xd0: ldr     q2, [x11, #480]
      +0xd4: mov     w11, #0x3c0
      +0xd8: ldr     q4, [x9, #512]
      +0xdc: mov     w9, #0x3f0
      +0xe0: dup     v6.4h, w10
      +0xe4: ldr     q16, [x12, #528]
      +0xe8: dup     v7.4s, w11
      +0xec: dup     v18.4s, w10
      +0xf0: dup     v17.4s, w9
      +0xf4: ldr     s20, [x1, #16]                       <+
      +0xf8: ldr     q19, [x1], #20                        |
      +0xfc: umov    w9, v19.b[1]                          |
      +0x100: umov    w10, v19.b[2]                         |
      +0x104: umov    w11, v19.b[6]                         |
      +0x108: umov    w12, v19.b[3]                         |
      +0x10c: tbl     v24.16b, {v19.16b-v20.16b}, v1.16b    |
      +0x110: tbl     v25.16b, {v19.16b}, v0.16b            |
      +0x114: fmov    s21, w9                               |
      +0x118: umov    w9, v19.b[7]                          |
      +0x11c: fmov    s22, w10                              |
      +0x120: umov    w10, v19.b[8]                         |
      +0x124: fmov    s23, w12                              |
      +0x128: mov     v21.h[1], w11                         |
      +0x12c: umov    w11, v19.b[11]                        |
      +0x130: tbl     v24.16b, {v24.16b}, v2.16b            |
      +0x134: mov     v22.h[1], w9                          |
      +0x138: umov    w9, v19.b[12]                         |
      +0x13c: mov     v21.h[2], w11                         |
      +0x140: mov     v23.h[1], w10                         |
      +0x144: umov    w10, v19.b[13]                        |
      +0x148: mov     v22.h[2], w9                          |
      +0x14c: umov    w9, v20.b[0]                          |
      +0x150: shl     v24.4s, v24.4s, #8                    |
      +0x154: tbl     v26.16b, {v19.16b-v20.16b}, v3.16b    |
      +0x158: and     v24.16b, v24.16b, v5.16b              |
      +0x15c: mov     v21.h[3], w9                          |
      +0x160: umov    w9, v20.b[1]                          |
      +0x164: mov     v23.h[2], w10                         |
      +0x168: orr     v24.16b, v24.16b, v25.16b             |
      +0x16c: tbl     v25.16b, {v19.16b-v20.16b}, v4.16b    |
      +0x170: mov     v22.h[3], w9                          |
      +0x174: umov    w9, v20.b[2]                          |
      +0x178: tbl     v19.16b, {v19.16b-v20.16b}, v16.16b   |
      +0x17c: bic     v21.4h, #0xff, lsl #8                 |
      +0x180: tbl     v26.16b, {v26.16b}, v2.16b            |
      +0x184: tbl     v25.16b, {v25.16b}, v2.16b            |
      +0x188: mov     v23.h[3], w9                          |
      +0x18c: add     x9, x0, x8                            |
      +0x190: bic     v22.4h, #0xff, lsl #8                 |
      +0x194: add     x8, x8, #0x20                         |
      +0x198: ushr    v22.4h, v22.4h, #4                    |
      +0x19c: ushr    v21.4h, v21.4h, #2                    |
      +0x1a0: tbl     v19.16b, {v19.16b}, v2.16b            |
      +0x1a4: shl     v26.4s, v26.4s, #6                    |
      +0x1a8: uxtl    v20.4s, v22.4h                        |
      +0x1ac: cmp     x8, #0x200                            |
      +0x1b0: shl     v22.4s, v25.4s, #4                    |
      +0x1b4: bic     v23.4h, #0xff, lsl #8                 |
      +0x1b8: uxtl    v21.4s, v21.4h                        |
      +0x1bc: ushr    v23.4h, v23.4h, #6                    |
      +0x1c0: and     v26.16b, v26.16b, v7.16b              |
      +0x1c4: and     v22.16b, v22.16b, v17.16b             |
      +0x1c8: orr     v21.16b, v26.16b, v21.16b             |
      +0x1cc: orr     v20.16b, v22.16b, v20.16b             |
      +0x1d0: uxtl    v22.4s, v23.4h                        |
      +0x1d4: shl     v19.4s, v19.4s, #2                    |
      +0x1d8: xtn     v23.4h, v24.4s                        |
      +0x1dc: xtn     v21.4h, v21.4s                        |
      +0x1e0: xtn     v20.4h, v20.4s                        |
      +0x1e4: orr     v19.16b, v19.16b, v22.16b             |
      +0x1e8: umull   v22.4s, v23.4h, v6.4h                 |
      +0x1ec: umull   v21.4s, v21.4h, v6.4h                 |
      +0x1f0: umull   v20.4s, v20.4h, v6.4h                 |
      +0x1f4: mul     v19.4s, v19.4s, v18.4s                |
      +0x1f8: rshrn   v22.4h, v22.4s, #10                   |
      +0x1fc: rshrn   v23.4h, v21.4s, #10                   |
      +0x200: rshrn   v24.4h, v20.4s, #10                   |
      +0x204: rshrn   v25.4h, v19.4s, #10                   |
      +0x208: st4     {v22.4h-v25.4h}, [x9]                 |
      +0x20c: b.ne    loop2                                -+
      +0x210: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_decompress_d10"];;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_CONSTANTS =
  end_itlist CONJ
   (map (fun k ->
      MLKEM_NATIVE_IMAGE_CONST_RULE
       (layout ("mlkem_poly_decompress_d10_const" ^ string_of_int k)) 128)
    (1--6));;

(* ------------------------------------------------------------------------- *)
(* The 20 bytes for 16 coefficients, as parts of a 160-bit word, from the    *)
(* number for the 320 bytes.                                                 *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES128_OF_NUM = prove
 (`!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 16 <= m
        ==> read (memory :> bytes128(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 128)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let D10_WIN128 = prove
 (`!a n i s.
        read (memory :> bytes(a,320)) s = n /\ i < 16
        ==> read (memory :> bytes128(word_add a (word(20 * i)))) s =
            word_subword (word(n DIV 2 EXP (160 * i)):160 word) (0,128)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `320`; `n:num`; `20 * i`; `s:armstate`]
                READ_MEMORY_BYTES128_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EXP; DIV_1; ARITH_RULE
   `2 EXP 128 = 340282366920938463463374607431768211456`] THEN
  REWRITE_TAC[ARITH_RULE `8 * 20 * i = 160 * i`]);;

let D10_WIN32 = prove
 (`!a n i s.
        read (memory :> bytes(a,320)) s = n /\ i < 16
        ==> read (memory :> bytes32(word_add a (word(20 * i + 16)))) s =
            word_subword (word(n DIV 2 EXP (160 * i)):160 word) (128,32)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `320`; `n:num`; `20 * i + 16`; `s:armstate`]
                READ_MEMORY_BYTES32_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD;
              ARITH_RULE `2 EXP 32 = 4294967296`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (20 * i + 16) = 160 * i + 128`]);;

(* ------------------------------------------------------------------------- *)
(* The 10-bit field k of the 160 bits as part of the number for the input.   *)
(* ------------------------------------------------------------------------- *)

let D10D_FIELD = prove
 (`!n i k. k < 16
     ==> val(word_subword (word(n DIV 2 EXP (160 * i)):160 word)
                          (10 * k,10):10 word) =
         (n DIV 2 EXP (10 * (16 * i + k))) MOD 1024`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 10 10 = 10`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 16 ==> 10 * k + 10 <= 160`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `1024 = 2 EXP 10`] THEN
  REWRITE_TAC[ARITH_RULE `160 * i + 10 * k = 10 * (16 * i + k)`]);;

(* ------------------------------------------------------------------------- *)
(* The lanes of the stores. With the registers in normal form, each 16-bit   *)
(* part of what is stored is (x * 3329 + 512) >> 10 for a 32-bit x made by   *)
(* bit operations from the 160 bits w of the input of the iteration, a       *)
(* maximal subterm that is the zero extension of a field of 10 bits k of w.  *)
(* The field is found from the bits of x and checked by bit-blasting; what   *)
(* is left is a function of the field, checked for all 1024 values (as for   *)
(* D11_LANE_FIELD_RULE in poly_decompress_d11.ml).                           *)
(* ------------------------------------------------------------------------- *)

let d10_pure w t =
  (match type_of t with Tyapp("word",_) -> true | _ -> false) &&
  free_in w t &&
  not(can (find_term (fun x -> match x with
        Const(("val"|"word_mul"|"word_add"),_) -> true | _ -> false)) t);;

let rec d10_max_pure w t acc =
  if d10_pure w t then t::acc else
  match t with
    Comb(f,x) -> d10_max_pure w f (d10_max_pure w x acc)
  | Abs(_,b) -> d10_max_pure w b acc
  | _ -> acc;;

let d10_lane_cache : (term * thm) list ref = ref [];;

let D10_LANE_FIELD_RULE th =
  let w = `w:160 word` and fv = `f:10 word` in
  let l = rand(concl th) in
  let q = match setify(d10_max_pure w l []) with
      [q] -> q | _ -> failwith "D10_LANE_FIELD_RULE: no unique input" in
  let zx = inst [`:10`,`:A`; hd(snd(dest_type(type_of q))),`:B`]
                `word_zx:A word->B word` in
  let k = match filter (fun b -> b >= 0)
                       (Array.to_list(bits_eval (ref [w]) q)) with
            b::_ -> b / 10
          | [] -> failwith "D10_LANE_FIELD_RULE: no field" in
  let f = mk_comb(mk_comb(`word_subword:160 word->num#num->10 word`,w),
                  mk_pair(mk_small_numeral(10 * k),`10`)) in
  let qth = BITBLAST_RULE(mk_eq(q,mk_comb(zx,f))) in
  let lgen = subst [mk_comb(zx,fv),q] l in
  let lem =
    try assoc lgen !d10_lane_cache with Failure _ ->
      let vv = `v:num` in
      let stmt_v = mk_forall(vv,mk_imp(`v < 1024`,
        mk_eq(subst [mk_comb(`word:num->10 word`,vv),fv] lgen,
              `word((3329 * v + 512) DIV 1024):int16`))) in
      let lem = prove(mk_eq(lgen,
                  `word((3329 * val(f:10 word) + 512) DIV 1024):int16`),
        SUBGOAL_THEN stmt_v (MP_TAC o SPEC `val(f:10 word)`) THENL
         [CONV_TAC EXPAND_CASES_CONV THEN
          CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));
          REWRITE_TAC[WORD_VAL] THEN DISCH_THEN MATCH_MP_TAC THEN
          MP_TAC(ISPEC `f:10 word` VAL_BOUND) THEN
          CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC]) in
      d10_lane_cache := (lgen,lem)::!d10_lane_cache; lem in
  let e1 = PURE_REWRITE_CONV [qth] l in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                                   GSYM ADD_ASSOC] THENC NUM_REDUCE_CONV))
   (TRANS th (TRANS e1 (INST [f,fv] lem)));;

(*** After each step: the usual simplification of the new vector register,
 *** the 64-bit parts of the 256 bits stored by ST4 as joins of the lanes,
 *** and every register in normal form ***)

let DD10_SIMD_TAC =
  SIMD_SIMPLIFY_TAC[] THEN BITS_INTERLEAVE_TAC THEN BITS_NORM_TAC;;

(*** The 16 coefficients of an iteration ***)

let D10_LOOP_SPLIT = prove
 (`!P i. (!j. j < 16 * i ==> P j) /\ (!k. k < 16 ==> P(16 * i + k))
         ==> !j. j < 16 * (i + 1) ==> P j`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j < 16 * i` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j - 16 * i`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The check for overlap has one branch for each order of the arrays: with   *)
(* the input a (320 bytes) and the output r (512 bytes), the scalar loop is  *)
(* taken unless a + 320 <= r or r + 512 <= a. In either case the vector code *)
(* is entered at the same instruction, after 3 or 6 steps respectively.      *)
(* ------------------------------------------------------------------------- *)

let DD10_RESOLVE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_FLAG; VAL_WORD_SUB_EQ_0]) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read PC s = if p then x else y`) c then
      let p = rand(rator(rator(rand c))) in
      let decide q = SUBGOAL_THEN q (fun th' ->
        ASSUME_TAC(REWRITE_RULE[th'] th)) THENL [ASM_ARITH_TAC; ALL_TAC] in
      decide p ORELSE decide (mk_neg p)
    else failwith "DD10_RESOLVE_TAC");;

let DD10_CHECK_TAC (body:int->tactic) =
  MP_TAC(SPECL [`r:int64`; `a:int64`; `512`; `320`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC (1--3) THEN
  ASM_CASES_TAC `val(word_add a (word 320):int64) <= val(r:int64)` THENL
   [DD10_RESOLVE_TAC THEN body 3;
    DD10_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC (4--6) THEN
    DD10_RESOLVE_TAC THEN body 6];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 10 in common/fips203.ml, the   *)
(* result for a 10-bit field y is the integer closest to 3329 * y / 1024,    *)
(* rounding up on ties, i.e. (3329 * y + 512) DIV 1024.                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,320)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
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
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the test at the end of the body ***)

  ENSURES_WHILE_UP2_TAC `16` `pc + mlkem_poly_decompress_d10_loop2`
   `pc + mlkem_poly_decompress_d10_loop2_exit`
   `\i s. read X0 s = r /\
          read X1 s = word_add a (word(20 * i)) /\
          read X8 s = word(32 * i) /\
          read Q0 s = word 0xffffff0fffffff0affffff05ffffff00 /\
          read Q1 s = word 0xffffffffffffffffffffffff100b0601 /\
          read Q2 s = word 0xffffff03ffffff02ffffff01ffffff00 /\
          read Q3 s = word 0xffffffffffffffffffffffff110c0702 /\
          read Q4 s = word 0xffffffffffffffffffffffff120d0803 /\
          read Q16 s = word 0xffffffffffffffffffffffff130e0904 /\
          read Q5 s = word 0x00000300000003000000030000000300 /\
          read Q6 s = word 0x0d010d010d010d01 /\
          read Q7 s = word 0x000003c0000003c0000003c0000003c0 /\
          read Q17 s = word 0x000003f0000003f0000003f0000003f0 /\
          read Q18 s = word 0x00000d0100000d0100000d0100000d01 /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,320)) s = n /\
          (!j. j < 16 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (10 * j)) MOD 2 EXP 10 + 512)
                        DIV 1024))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the check for overlap and the constants: the
     *** TBL indices (0xff for a zero byte) in Q0-Q4 and Q16, the masks, and
     *** 3329, with the page of the constants computed by ADRP in steps 1,
     *** 2, 3, 4, 8 and 12 of the vector code ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(fun th -> MAP_EVERY (fun c -> ASSUME_TAC(MATCH_MP c th))
      (CONJUNCTS MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_CONSTANTS)) THEN
    DD10_CHECK_TAC (fun off ->
      MAP_EVERY (fun k ->
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC
          [k + off] THEN
        (if mem k [1;2;3;4;8;12] then MLKEM_NATIVE_ADRP_TAC else ALL_TAC))
       (1--21)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for 20 bytes and 16 coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`] D10_WIN128) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`] D10_WIN32) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC `w:160 word = word(n DIV 2 EXP (160 * i))` THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC [k] THEN
      DD10_SIMD_TAC) (1--71) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> can (term_match [] `read (memory :> bytes64 a) s = x`)
                           (concl th) && free_in `r:int64` (concl th)))) THEN
    REPEAT(DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o D10_LANE_FIELD_RULE o
                         CONV_RULE(RAND_CONV BITS_NORM_CONV))
                         (CONJUNCTS th))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_add (word(32 * i)) (word 18446744073709551136):int64) = 0) <=>
      i + 1 < 16`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      ASM_CASES_TAC `i = 15` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 16 /\ ~(i = 15)
        ==> 32 * i + 18446744073709551136 < 18446744073709551616`] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC;
      REWRITE_TAC[ARITH_RULE `20 * (i + 1) = 20 * i + 20`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC]) THEN
    MATCH_MP_TAC D10_LOOP_SPLIT THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; CONV_TAC EXPAND_CASES_CONV] THEN
    REWRITE_TAC[ARITH_RULE `2 * (16 * i + 0) = 32 * i`;
                ARITH_RULE `2 * (16 * i + 1) = 32 * i + 2`;
                ARITH_RULE `2 * (16 * i + 2) = 32 * i + 4`;
                ARITH_RULE `2 * (16 * i + 3) = 32 * i + 6`;
                ARITH_RULE `2 * (16 * i + 4) = 32 * i + 8`;
                ARITH_RULE `2 * (16 * i + 5) = 32 * i + 10`;
                ARITH_RULE `2 * (16 * i + 6) = 32 * i + 12`;
                ARITH_RULE `2 * (16 * i + 7) = 32 * i + 14`;
                ARITH_RULE `2 * (16 * i + 8) = 32 * i + 16`;
                ARITH_RULE `2 * (16 * i + 9) = 32 * i + 18`;
                ARITH_RULE `2 * (16 * i + 10) = 32 * i + 20`;
                ARITH_RULE `2 * (16 * i + 11) = 32 * i + 22`;
                ARITH_RULE `2 * (16 * i + 12) = 32 * i + 24`;
                ARITH_RULE `2 * (16 * i + 13) = 32 * i + 26`;
                ARITH_RULE `2 * (16 * i + 14) = 32 * i + 28`;
                ARITH_RULE `2 * (16 * i + 15) = 32 * i + 30`] THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "w" THEN
    REWRITE_TAC(map (fun k ->
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
       (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D10D_FIELD)
           (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                         (mk_small_numeral k) `16`))))) (0--15)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events of the check for        *)
(* overlap depend on which of the two branches is taken.                     *)
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
      [`word(pc + mlkem_poly_decompress_d10_consts):int64`,
       `mlkem_poly_decompress_d10_consts_size:num`]
    ~keep_maychanges:true
    mlkem_native_poly_decompress_d10_signature
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,320]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_decompress_d10) /\
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
                          word (pc + mlkem_poly_decompress_d10_consts),
                          mlkem_poly_decompress_d10_consts_size]
                         [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc returnaddress)
        (APPEND
          (ENUMERATEL 16 (\i. f_ev_loop a r pc returnaddress i))
          (APPEND
            (f_ev_vec a r pc returnaddress)
            (if val(word_add a (word 320):int64) <= val r
             then f_ev_check1 a r pc returnaddress
             else f_ev_check2 a r pc returnaddress)))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `16` `pc + mlkem_poly_decompress_d10_loop2`
   `pc + mlkem_poly_decompress_d10_loop2_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = r /\
           read X1 s = word_add a (word(20 * i)) /\
           read X8 s = word(32 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The check for overlap, and the setup of the vector code ***)

    REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_decompress_d10_join1`
     `\s. read X0 s = r /\ read X1 s = a /\
          read X30 s = returnaddress` THEN
    CONJ_TAC THENL
     [REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      DD10_CHECK_TAC (fun _ ->
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC);
      ALL_TAC] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC [k] THEN
      (if mem k [1;2;3;4;8;12] then MLKEM_NATIVE_ADRP_TAC else ALL_TAC))
     (1--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC (1--71) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_add (word(32 * i)) (word 18446744073709551136):int64) = 0) <=>
      i + 1 < 16`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      ASM_CASES_TAC `i = 15` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 16 /\ ~(i = 15)
        ==> 32 * i + 18446744073709551136 < 18446744073709551616`] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `20 * (i + 1) = 20 * i + 20`;
                  ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
