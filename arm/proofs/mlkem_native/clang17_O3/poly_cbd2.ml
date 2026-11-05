(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Centered binomial distribution with eta = 2. This is the code for         *)
(* mlkem_poly_cbd2 from mlkem-native's portable C implementation compiled by *)
(* clang 17 with -O3 (see mlkem_native/README.md). It is verified in the     *)
(* whole image (see libmlkem.ml).                                            *)
(*                                                                           *)
(* The compiler has vectorized the loop, 32 coefficients per iteration from  *)
(* one 128-bit load, after a check that the input and the output do not      *)
(* overlap, with one branch for each of the two orders of the arrays; if     *)
(* they overlap, the code falls back to a loop that handles one 32-bit word  *)
(* at a time. Since the specification requires them not to overlap, only the *)
(* vector code runs. It puts the coefficients in order with TBL, using       *)
(* vectors of byte indices from the read-only data, so the safety theorem    *)
(* has read-only data (the constants of the function are one block in the    *)
(* layout). The eight iterations of the loop are simulated one after the     *)
(* other.                                                                    *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_cbd2:
        +0x0: add     x8, x1, #0x80
        +0x4: cmp     x8, x0
        +0x8: b.ls    join1
        +0xc: add     x8, x0, #0x200
       +0x10: cmp     x8, x1
       +0x14: b.ls    join1
       +0x18: adrp    x9, <page>
       +0x1c: adrp    x10, <page>
       +0x20: adrp    x11, <page>
       +0x24: adrp    x12, <page>
       +0x28: movi    v2.4s, #0x3
       +0x2c: mov     x8, xzr
       +0x30: ldr     d0, [x9, #1888]
                    // mlkem_poly_cbd2_const11
       +0x34: mov     w9, #0x55555555
       +0x38: ldr     q1, [x10, #1600]
                    // mlkem_poly_cbd2_const9
       +0x3c: add     x10, x0, #0x8
       +0x40: ldr     d3, [x11, #1896]
                    // mlkem_poly_cbd2_const12
       +0x44: ldr     q4, [x12, #1616]
                    // mlkem_poly_cbd2_const10
       +0x48: ldr     w11, [x1, x8]
       +0x4c: add     x8, x8, #0x4
       +0x50: cmp     x8, #0x80
       +0x54: and     w12, w11, w9
       +0x58: and     w11, w9, w11, lsr #1
       +0x5c: add     w11, w11, w12
       +0x60: lsr     w12, w11, #26
       +0x64: dup     v5.4s, w11
       +0x68: fmov    s16, w11
       +0x6c: ushl    v6.2s, v5.2s, v3.2s
       +0x70: ushl    v17.2s, v5.2s, v0.2s
       +0x74: mov     v6.s[2], w12
       +0x78: lsr     w12, w11, #4
       +0x7c: mov     v16.s[1], w12
       +0x80: and     v7.16b, v6.16b, v2.16b
       +0x84: mov     v6.s[3], w11
       +0x88: mov     v16.d[1], v17.d[0]
       +0x8c: ushr    v6.4s, v6.4s, #30
       +0x90: mov     v7.s[3], v6.s[3]
       +0x94: ushl    v6.4s, v5.4s, v1.4s
       +0x98: ushl    v5.4s, v5.4s, v4.4s
       +0x9c: and     v6.16b, v6.16b, v2.16b
       +0xa0: and     v16.16b, v16.16b, v2.16b
       +0xa4: and     v5.16b, v5.16b, v2.16b
       +0xa8: sub     v6.4s, v16.4s, v6.4s
       +0xac: sub     v5.4s, v5.4s, v7.4s
       +0xb0: xtn     v6.4h, v6.4s
       +0xb4: xtn     v5.4h, v5.4s
       +0xb8: stur    d6, [x10, #-8]
       +0xbc: str     d5, [x10], #16
       +0xc0: b.ne    loop1
       +0xc4: b       join2
       +0xc8: adrp    x9, <page>
       +0xcc: adrp    x10, <page>
       +0xd0: adrp    x11, <page>
       +0xd4: mov     x8, xzr
       +0xd8: movi    v7.16b, #0x55
       +0xdc: ldr     q0, [x9, #1536]
                    // mlkem_poly_invntt_tomont_const5
       +0xe0: adrp    x9, <page>
       +0xe4: ldr     q1, [x10, #832]
                    // mlkem_poly_decompress_d5_const19
       +0xe8: adrp    x10, <page>
       +0xec: ldr     q2, [x11, #1552]
                    // mlkem_poly_invntt_tomont_const6
       +0xf0: adrp    x11, <page>
       +0xf4: ldr     q3, [x9, #864]
                    // mlkem_poly_decompress_d5_const21
       +0xf8: adrp    x9, <page>
       +0xfc: movi    v16.4s, #0x3
      +0x100: ldr     q4, [x10, #1568]
                    // mlkem_poly_invntt_tomont_const7
      +0x104: ldr     q5, [x11, #896]
                    // mlkem_poly_decompress_d5_const23
      +0x108: ldr     q6, [x9, #1584]
                    // mlkem_poly_invntt_tomont_const8
      +0x10c: adrp    x9, <page>
      +0x110: ldr     q17, [x9, #928]
                    // mlkem_poly_decompress_d5_const25
      +0x114: ldr     q18, [x1, x8]
      +0x118: add     x8, x8, #0x10
      +0x11c: cmp     x8, #0x80
      +0x120: ushr    v19.4s, v18.4s, #1
      +0x124: and     v18.16b, v18.16b, v7.16b
      +0x128: and     v19.16b, v19.16b, v7.16b
      +0x12c: add     v18.4s, v19.4s, v18.4s
      +0x130: ushr    v20.4s, v18.4s, #2
      +0x134: ushr    v21.4s, v18.4s, #4
      +0x138: ushr    v22.4s, v18.4s, #6
      +0x13c: ushr    v23.4s, v18.4s, #8
      +0x140: ushr    v24.4s, v18.4s, #10
      +0x144: ushr    v25.4s, v18.4s, #26
      +0x148: and     v19.16b, v18.16b, v16.16b
      +0x14c: ushr    v26.4s, v18.4s, #30
      +0x150: and     v20.16b, v20.16b, v16.16b
      +0x154: and     v21.16b, v21.16b, v16.16b
      +0x158: and     v22.16b, v22.16b, v16.16b
      +0x15c: and     v23.16b, v23.16b, v16.16b
      +0x160: sub     v19.4s, v19.4s, v20.4s
      +0x164: sub     v20.4s, v21.4s, v22.4s
      +0x168: and     v21.16b, v24.16b, v16.16b
      +0x16c: sub     v21.4s, v23.4s, v21.4s
      +0x170: ushr    v22.4s, v18.4s, #16
      +0x174: ushr    v23.4s, v18.4s, #18
      +0x178: ushr    v24.4s, v18.4s, #22
      +0x17c: and     v22.16b, v22.16b, v16.16b
      +0x180: ushr    v27.4s, v18.4s, #12
      +0x184: and     v23.16b, v23.16b, v16.16b
      +0x188: sub     v22.4s, v22.4s, v23.4s
      +0x18c: ushr    v23.4s, v18.4s, #20
      +0x190: and     v24.16b, v24.16b, v16.16b
      +0x194: and     v23.16b, v23.16b, v16.16b
      +0x198: sub     v23.4s, v23.4s, v24.4s
      +0x19c: ushr    v24.4s, v18.4s, #24
      +0x1a0: bic     v25.4s, #0x3c
      +0x1a4: bic     v24.4s, #0xfc
      +0x1a8: sub     v24.4s, v24.4s, v25.4s
      +0x1ac: ushr    v25.4s, v18.4s, #28
      +0x1b0: ushr    v18.4s, v18.4s, #14
      +0x1b4: bic     v25.4s, #0xc
      +0x1b8: sub     v25.4s, v25.4s, v26.4s
      +0x1bc: and     v26.16b, v27.16b, v16.16b
      +0x1c0: and     v18.16b, v18.16b, v16.16b
      +0x1c4: sub     v18.4s, v26.4s, v18.4s
      +0x1c8: uzp1    v22.8h, v22.8h, v23.8h
      +0x1cc: uzp1    v19.8h, v19.8h, v20.8h
      +0x1d0: uzp1    v23.8h, v24.8h, v25.8h
      +0x1d4: uzp1    v20.8h, v21.8h, v18.8h
      +0x1d8: tbl     v18.16b, {v22.16b-v23.16b}, v0.16b
      +0x1dc: tbl     v21.16b, {v22.16b-v23.16b}, v2.16b
      +0x1e0: tbl     v24.16b, {v22.16b-v23.16b}, v4.16b
      +0x1e4: tbl     v22.16b, {v22.16b-v23.16b}, v6.16b
      +0x1e8: tbl     v23.16b, {v19.16b-v20.16b}, v17.16b
      +0x1ec: tbl     v25.16b, {v19.16b-v20.16b}, v5.16b
      +0x1f0: tbl     v26.16b, {v19.16b-v20.16b}, v3.16b
      +0x1f4: tbl     v19.16b, {v19.16b-v20.16b}, v1.16b
      +0x1f8: mov     v23.d[1], v22.d[1]
      +0x1fc: mov     v25.d[1], v24.d[1]
      +0x200: mov     v26.d[1], v21.d[1]
      +0x204: mov     v19.d[1], v18.d[1]
      +0x208: stp     q25, q23, [x0, #32]
      +0x20c: stp     q19, q26, [x0], #64
      +0x210: b.ne    loop2
      +0x214: ret
 ***)

let MLKEM_NATIVE_POLY_CBD2_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_cbd2"];;

(*** The eight vectors of byte indices for TBL in the vector code ***)

let MLKEM_NATIVE_POLY_CBD2_CLANG17_O3_CONSTANTS =
  map (fun k ->
    MLKEM_NATIVE_IMAGE_CONST_RULE
     (layout("mlkem_poly_cbd2_const" ^ string_of_int k)) 128) (1--8);;

(* ------------------------------------------------------------------------- *)
(* As at -O2, coefficient j of 8 for a 32-bit word t of the input comes from *)
(* its 4-bit field j (CBD2_LANE, with the lemmas of gcc12_O2). Here each     *)
(* 32-bit lane of the vector loaded holds one such word, its pairs of bits   *)
(* are added, and the fields are taken out with USHR, BIC, AND and UZP1,     *)
(* subtracted, and put in order with TBL.                                    *)
(* ------------------------------------------------------------------------- *)

let NIBBLE_BIT = prove
 (`!n m k. k < 4
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 16) DIV 2 EXP k) MOD 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP m`,`x:num`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM(SPEC `2` EXP_1)] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; ARITH_RULE `16 = 2 EXP 4`;
              MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k < 4 ==> MIN 4 (k + 1) = k + 1`]);;

let CBD2_NIBBLE = prove
 (`!m. m < 16
       ==> word_sub
            (word_zx (word_add (word_and (word m:4 word) (word 1))
                               (word_and (word_ushr (word m) 1) (word 1))))
            (word_zx (word_add (word_and (word_ushr (word m:4 word) 2)
                                         (word 1))
                               (word_ushr (word m) 3))):int16 =
           iword(&(m MOD 2 + (m DIV 2) MOD 2) -
                 &((m DIV 4) MOD 2 + (m DIV 8) MOD 2))`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)));;

let CBD2_LANE = prove
 (`!n i j t:int32.
      j < 8 /\ word((n DIV 2 EXP (32 * i)) MOD 4294967296) = t
      ==> let x:4 word = word_subword t (4 * j,4) in
          word_sub
            (word_zx (word_add (word_and x (word 1))
                               (word_and (word_ushr x 1) (word 1))))
            (word_zx (word_add (word_and (word_ushr x 2) (word 1))
                               (word_ushr x 3))):int16 =
          iword(&((n DIV 2 EXP (4 * (8 * i + j))) MOD 2 +
                  (n DIV 2 EXP (4 * (8 * i + j) + 1)) MOD 2) -
                &((n DIV 2 EXP (4 * (8 * i + j) + 2)) MOD 2 +
                  (n DIV 2 EXP (4 * (8 * i + j) + 3)) MOD 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `word_subword (word((n DIV 2 EXP (32 * i)) MOD 4294967296):int32)
                 (4 * j,4):4 word =
    word((n DIV 2 EXP (4 * (8 * i + j))) MOD 16)`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
    ANTS_TAC THENL
     [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`] THEN
    ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `j < 8 ==> 4 * j + 4 <= 32`] THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 4 = 16`] THEN
    REWRITE_TAC[ARITH_RULE `32 * i + 4 * j = 4 * (8 * i + j)`];
    ALL_TAC] THEN
  SIMP_TAC[CBD2_NIBBLE; MOD_LT_EQ; ARITH_EQ] THEN
  SIMP_TAC[NIBBLE_BIT; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GEN_ALL(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`x:num`; `2`; `8`] MOD_MOD))]);;

(*** The 128 bytes as 32-bit words w k, merged into the 128-bit parts that
 *** the loads read ***)

let CBD2_MERGES = map (fun k ->
  let addr = if k = 0 then `a:int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
            mk_comb(`word:num->int64`, mk_small_numeral(16 * k))) in
  READ_MEMORY_MERGE_CONV 2
   (vsubst [addr,`x:int64`] `read (memory :> bytes128 x) s0`)) (0--7);;

let CBD2_INPUT_TAC =
  SUBGOAL_THEN
   `?w:num->int32. !k. word((n DIV 2 EXP (32 * k)) MOD 4294967296) = w k`
   STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\k. word((n DIV 2 EXP (32 * k)) MOD 4294967296):int32` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k < 32
        ==> read (memory :> bytes32 (word_add a (word(4 * k)))) s0 =
            (w:num->int32) k`
   MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `w:num->int32` (concl th)
      then REWRITE_TAC[GSYM th] THEN ASSUME_TAC th else NO_TAC) THEN
    MP_TAC(SPECL [`a:int64`; `128`; `n:num`; `4 * k`; `s0:armstate`]
                 READ_MEMORY_BYTES32_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `8 * 4 * k = 32 * k`];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC CBD2_MERGES THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`];;

(*** The constants of the image, as facts about s0 ***)

let CBD2_CONSTANTS_TAC =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun ath ->
      if can (term_match [] `aligned_bytes_loaded s0 (word pc)
                               mlkem_native_libmlkem_clang17_O3_mc`)
             (concl ath)
      then ASSUME_TAC(MATCH_MP th ath) else failwith ""))
    MLKEM_NATIVE_POLY_CBD2_CLANG17_O3_CONSTANTS;;

(*** After each step, the subwords of the new register value taken through
 *** AND and OR to the lanes of single words ***)

let CBD2_SIMPLIFY_CONV =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC REWR_CONV WORD_SUBWORD_OR ORELSEC
    WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV;;

let CBD2_SIMD_TAC =
  TRY(FIRST_X_ASSUM(ASSUME_TAC o CONV_RULE(RAND_CONV CBD2_SIMPLIFY_CONV) o
    check (can (term_match [] `read X (s:armstate):int128 = whatever`) o
           concl)));;

(*** The stored coefficients, from the 32 stores of 16 bytes ***)

let CBD2_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (fun th -> can (term_match []
                     `read (memory :> bytes128 a) s = x`) (concl th) &&
                     free_in `r:int64` (concl th)))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o
      CONV_RULE(RAND_CONV CBD2_SIMPLIFY_CONV) o
      CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]
                          THENC NUM_REDUCE_CONV)))
     (CONJUNCTS th)));;

(*** Each coefficient i = 8 * g + c in the canonical form of CBD2_LANE for
 *** the field c of w g, to be bit-blasted against the stored value ***)

let CBD2_FIELDS_TAC =
  let norm = CONV_RULE(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) in
  FIRST_ASSUM(fun def ->
    if is_forall(concl def) && free_in `w:num->int32` (concl def) &&
       not(is_imp(snd(dest_forall(concl def))))
    then
      let ths = map (fun i ->
        let g = i / 8 and c = i mod 8 in
        let gt = mk_small_numeral g and ct = mk_small_numeral c in
        let wg = mk_comb(`w:num->int32`,gt) in
        let th = MP (SPECL [`n:num`; gt; ct; wg] CBD2_LANE)
                    (CONJ (EQT_ELIM(NUM_LT_CONV(mk_binop
                             `(<):num->num->bool` ct `8`)))
                          (SPEC gt def)) in
        GSYM(norm(CONV_RULE(TOP_DEPTH_CONV let_CONV) th))) (0--255) in
      REWRITE_TAC ths
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The check for overlap has one branch for each order of the arrays: with   *)
(* the input a (128 bytes) and the output r (512 bytes), the scalar loop is  *)
(* taken unless a + 128 <= r or r + 512 <= a. In either case the vector code *)
(* is entered at the same instruction, after 3 or 6 steps respectively.      *)
(* ------------------------------------------------------------------------- *)

let CBD2_RESOLVE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_FLAG; VAL_WORD_SUB_EQ_0]) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read PC s = if p then x else y`) c then
      let p = rand(rator(rator(rand c))) in
      let decide q = SUBGOAL_THEN q (fun th' ->
        ASSUME_TAC(REWRITE_RULE[th'] th)) THENL [ASM_ARITH_TAC; ALL_TAC] in
      decide p ORELSE decide (mk_neg p)
    else failwith "CBD2_RESOLVE_TAC");;

let CBD2_CHECK_TAC (body:int->tactic) =
  MP_TAC(SPECL [`r:int64`; `a:int64`; `512`; `128`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_CLANG17_O3_EXEC (1--3) THEN
  ASM_CASES_TAC `val(word_add a (word 128):int64) <= val(r:int64)` THENL
   [CBD2_RESOLVE_TAC THEN body 3;
    CBD2_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_CLANG17_O3_EXEC (4--6) THEN
    CBD2_RESOLVE_TAC THEN body 6];;

(*** The vector code from join1 on: the setup of 19 steps with the page
 *** of the constants computed by ADRP (steps 1, 2, 3, 7, 9, 11, 13 and 18),
 *** eight iterations of 64 steps, and the return ***)

let CBD2_ADRP_STEPS = [1;2;3;7;9;11;13;18];;

let CBD2_BODY_TAC (simp:tactic) off =
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_CLANG17_O3_EXEC [k + off] THEN
    (if mem k CBD2_ADRP_STEPS then MLKEM_NATIVE_ADRP_TAC else ALL_TAC) THEN
    simp) (1--532);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_cbd 2 in common/fips203.ml, coefficient i *)
(* of the result is the number of 1 bits among bits 4 * i and 4 * i + 1 of   *)
(* the 128 bytes as a number n, minus the number among bits 4 * i + 2 and    *)
(* 4 * i + 3, here as a 16-bit integer rather than modulo 3329.              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_cbd2) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  CBD2_INPUT_TAC THEN
  CBD2_CONSTANTS_TAC THEN

  (*** The overlap check, and the vector code ***)

  CBD2_CHECK_TAC (CBD2_BODY_TAC CBD2_SIMD_TAC) THEN
  CBD2_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient from its 4-bit field ***)

  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN CBD2_FIELDS_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_cbd2_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 128]", "true")],
   "void",
   [("a", "128", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + mlkem_poly_cbd2_consts):int64`,
                       `mlkem_poly_cbd2_consts_size:num`]
    ~keep_maychanges:true
    mlkem_native_poly_cbd2_signature
    MLKEM_NATIVE_POLY_CBD2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_CBD2_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_CBD2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,128]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_cbd2) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2
                         [a,128; r,512;
                          word (pc + mlkem_poly_cbd2_consts),
                          mlkem_poly_cbd2_consts_size]
                         [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      (if val(word_add a (word 128):int64) <= val r
       then f_ev1 a r pc returnaddress
       else f_ev2 a r pc returnaddress):(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_CBD2_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  CBD2_CONSTANTS_TAC THEN
  CBD2_CHECK_TAC (CBD2_BODY_TAC ALL_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
