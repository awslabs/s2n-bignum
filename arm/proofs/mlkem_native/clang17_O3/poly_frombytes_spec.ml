(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of polynomial coefficients from 12-bit chunks of a byte array.  *)
(* This is the code for mlkem_poly_frombytes from mlkem-native's portable C  *)
(* implementation compiled by clang 17 with -O3 (see mlkem_native/README.md).*)
(* It is verified in the whole image (see libmlkem.ml).                      *)
(*                                                                           *)
(* The compiler has vectorized the loop completely, with LD3 and ST2, after  *)
(* a check that the input and the output do not overlap, with one branch for *)
(* each of the two orders of the arrays; if they overlap, the code falls     *)
(* back to a scalar loop. Since the specification requires them not to       *)
(* overlap, only the vector code runs, which uses neither the stack nor X18, *)
(* so the specifications are those of gcc12_O2.                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_frombytes:
       +0x0: add     x8, x1, #0x180
       +0x4: cmp     x8, x0
       +0x8: b.ls    <mlkem_poly_frombytes+0x54>
       +0xc: add     x8, x0, #0x200
      +0x10: cmp     x8, x1
      +0x14: b.ls    join1                       ---+
      +0x18: mov     x8, xzr                        |
      +0x1c: add     x9, x1, #0x2                   |
      +0x20: ldurb   w10, [x9, #-2]              <+ |
      +0x24: add     x13, x0, x8                  | |
      +0x28: ldurb   w11, [x9, #-1]               | |
      +0x2c: add     x8, x8, #0x4                 | |
      +0x30: ldrb    w12, [x9], #3                | |
      +0x34: cmp     x8, #0x200                   | |
      +0x38: bfi     w10, w11, #8, #4             | |
      +0x3c: lsr     w11, w11, #4                 | |
      +0x40: orr     w11, w11, w12, lsl #4        | |
      +0x44: strh    w10, [x13]                   | |
      +0x48: strh    w11, [x13, #2]               | |
      +0x4c: b.ne    loop1                       -+ |
      +0x50: ret                                    |
      +0x54: mov     x8, x1
      +0x58: mov     x9, x0
      +0x5c: add     x10, x1, #0x150
      +0x60: ld3     {v0.16b-v2.16b}, [x8], #48
      +0x64: shll    v6.8h, v1.8b, #8
      +0x68: ushr    v7.16b, v1.16b, #4
      +0x6c: uxtl    v3.8h, v0.8b
      +0x70: bic     v6.8h, #0xf0, lsl #8
      +0x74: uxtl    v16.8h, v7.8b
      +0x78: ushll   v17.8h, v2.8b, #4
      +0x7c: orr     v18.16b, v6.16b, v3.16b
      +0x80: orr     v19.16b, v17.16b, v16.16b
      +0x84: shll2   v5.8h, v1.16b, #8
      +0x88: st2     {v18.8h-v19.8h}, [x9], #32
      +0x8c: uxtl2   v4.8h, v0.16b
      +0x90: bic     v5.8h, #0xf0, lsl #8
      +0x94: uxtl2   v3.8h, v7.16b
      +0x98: ushll2  v0.8h, v2.16b, #4
      +0x9c: orr     v1.16b, v5.16b, v4.16b
      +0xa0: orr     v2.16b, v0.16b, v3.16b
      +0xa4: st2     {v1.8h-v2.8h}, [x9]
      +0xa8: add     x9, x0, #0x60
      +0xac: ld3     {v0.16b-v2.16b}, [x8]
      +0xb0: add     x8, x0, #0x40
      +0xb4: shll    v4.8h, v1.8b, #8
      +0xb8: ushr    v5.16b, v1.16b, #4
      +0xbc: uxtl    v3.8h, v0.8b
      +0xc0: ushll   v6.8h, v2.8b, #4
      +0xc4: bic     v4.8h, #0xf0, lsl #8
      +0xc8: uxtl    v7.8h, v5.8b
      +0xcc: orr     v3.16b, v4.16b, v3.16b
      +0xd0: orr     v4.16b, v6.16b, v7.16b
      +0xd4: st2     {v3.8h-v4.8h}, [x8]
      +0xd8: add     x8, x1, #0x60
      +0xdc: shll2   v4.8h, v1.16b, #8
      +0xe0: uxtl2   v3.8h, v0.16b
      +0xe4: ushll2  v0.8h, v2.16b, #4
      +0xe8: bic     v4.8h, #0xf0, lsl #8
      +0xec: uxtl2   v1.8h, v5.16b
      +0xf0: orr     v2.16b, v4.16b, v3.16b
      +0xf4: orr     v3.16b, v0.16b, v1.16b
      +0xf8: st2     {v2.8h-v3.8h}, [x9]
      +0xfc: add     x9, x0, #0xa0
      +0x100: ld3     {v0.16b-v2.16b}, [x8]
      +0x104: add     x8, x0, #0x80
      +0x108: shll    v4.8h, v1.8b, #8
      +0x10c: ushr    v5.16b, v1.16b, #4
      +0x110: uxtl    v3.8h, v0.8b
      +0x114: ushll   v6.8h, v2.8b, #4
      +0x118: bic     v4.8h, #0xf0, lsl #8
      +0x11c: uxtl    v7.8h, v5.8b
      +0x120: orr     v3.16b, v4.16b, v3.16b
      +0x124: orr     v4.16b, v6.16b, v7.16b
      +0x128: st2     {v3.8h-v4.8h}, [x8]
      +0x12c: add     x8, x1, #0x90
      +0x130: shll2   v4.8h, v1.16b, #8
      +0x134: uxtl2   v3.8h, v0.16b
      +0x138: ushll2  v0.8h, v2.16b, #4
      +0x13c: bic     v4.8h, #0xf0, lsl #8
      +0x140: uxtl2   v1.8h, v5.16b
      +0x144: orr     v2.16b, v4.16b, v3.16b
      +0x148: orr     v3.16b, v0.16b, v1.16b
      +0x14c: st2     {v2.8h-v3.8h}, [x9]
      +0x150: add     x9, x0, #0xe0
      +0x154: ld3     {v0.16b-v2.16b}, [x8]
      +0x158: add     x8, x0, #0xc0
      +0x15c: shll    v4.8h, v1.8b, #8
      +0x160: ushr    v5.16b, v1.16b, #4
      +0x164: uxtl    v3.8h, v0.8b
      +0x168: ushll   v6.8h, v2.8b, #4
      +0x16c: bic     v4.8h, #0xf0, lsl #8
      +0x170: uxtl    v7.8h, v5.8b
      +0x174: orr     v3.16b, v4.16b, v3.16b
      +0x178: orr     v4.16b, v6.16b, v7.16b
      +0x17c: st2     {v3.8h-v4.8h}, [x8]
      +0x180: add     x8, x1, #0xc0
      +0x184: shll2   v4.8h, v1.16b, #8
      +0x188: uxtl2   v3.8h, v0.16b
      +0x18c: ushll2  v0.8h, v2.16b, #4
      +0x190: bic     v4.8h, #0xf0, lsl #8
      +0x194: uxtl2   v1.8h, v5.16b
      +0x198: orr     v2.16b, v4.16b, v3.16b
      +0x19c: orr     v3.16b, v0.16b, v1.16b
      +0x1a0: st2     {v2.8h-v3.8h}, [x9]
      +0x1a4: add     x9, x0, #0x120
      +0x1a8: ld3     {v0.16b-v2.16b}, [x8]
      +0x1ac: add     x8, x0, #0x100
      +0x1b0: shll    v4.8h, v1.8b, #8
      +0x1b4: ushr    v5.16b, v1.16b, #4
      +0x1b8: uxtl    v3.8h, v0.8b
      +0x1bc: ushll   v6.8h, v2.8b, #4
      +0x1c0: bic     v4.8h, #0xf0, lsl #8
      +0x1c4: uxtl    v7.8h, v5.8b
      +0x1c8: orr     v3.16b, v4.16b, v3.16b
      +0x1cc: orr     v4.16b, v6.16b, v7.16b
      +0x1d0: st2     {v3.8h-v4.8h}, [x8]
      +0x1d4: add     x8, x1, #0xf0
      +0x1d8: shll2   v4.8h, v1.16b, #8
      +0x1dc: uxtl2   v3.8h, v0.16b
      +0x1e0: ushll2  v0.8h, v2.16b, #4
      +0x1e4: bic     v4.8h, #0xf0, lsl #8
      +0x1e8: uxtl2   v1.8h, v5.16b
      +0x1ec: orr     v2.16b, v4.16b, v3.16b
      +0x1f0: orr     v3.16b, v0.16b, v1.16b
      +0x1f4: st2     {v2.8h-v3.8h}, [x9]
      +0x1f8: add     x9, x0, #0x160
      +0x1fc: ld3     {v0.16b-v2.16b}, [x8]
      +0x200: add     x8, x0, #0x140
      +0x204: shll    v4.8h, v1.8b, #8
      +0x208: ushr    v5.16b, v1.16b, #4
      +0x20c: uxtl    v3.8h, v0.8b
      +0x210: ushll   v6.8h, v2.8b, #4
      +0x214: bic     v4.8h, #0xf0, lsl #8
      +0x218: uxtl    v7.8h, v5.8b
      +0x21c: orr     v3.16b, v4.16b, v3.16b
      +0x220: orr     v4.16b, v6.16b, v7.16b
      +0x224: st2     {v3.8h-v4.8h}, [x8]
      +0x228: add     x8, x1, #0x120
      +0x22c: shll2   v4.8h, v1.16b, #8
      +0x230: uxtl2   v3.8h, v0.16b
      +0x234: ushll2  v0.8h, v2.16b, #4
      +0x238: bic     v4.8h, #0xf0, lsl #8
      +0x23c: uxtl2   v1.8h, v5.16b
      +0x240: orr     v2.16b, v4.16b, v3.16b
      +0x244: orr     v3.16b, v0.16b, v1.16b
      +0x248: st2     {v2.8h-v3.8h}, [x9]
      +0x24c: add     x9, x0, #0x1a0
      +0x250: ld3     {v0.16b-v2.16b}, [x8]
      +0x254: add     x8, x0, #0x180
      +0x258: shll    v6.8h, v1.8b, #8
      +0x25c: ushr    v7.16b, v1.16b, #4
      +0x260: uxtl    v3.8h, v0.8b
      +0x264: uxtl2   v4.8h, v0.16b
      +0x268: shll2   v5.8h, v1.16b, #8
      +0x26c: ushll   v0.8h, v2.8b, #4
      +0x270: bic     v6.8h, #0xf0, lsl #8
      +0x274: uxtl    v1.8h, v7.8b
      +0x278: ushll2  v16.8h, v2.16b, #4
      +0x27c: orr     v2.16b, v6.16b, v3.16b
      +0x280: orr     v3.16b, v0.16b, v1.16b
      +0x284: bic     v5.8h, #0xf0, lsl #8
      +0x288: st2     {v2.8h-v3.8h}, [x8]
      +0x28c: uxtl2   v0.8h, v7.16b
      +0x290: add     x8, x0, #0x1c0
      +0x294: orr     v1.16b, v5.16b, v4.16b
      +0x298: orr     v2.16b, v16.16b, v0.16b
      +0x29c: st2     {v1.8h-v2.8h}, [x9]
      +0x2a0: add     x9, x0, #0x1e0
      +0x2a4: ld3     {v0.16b-v2.16b}, [x10]
      +0x2a8: shll    v6.8h, v1.8b, #8
      +0x2ac: ushr    v7.16b, v1.16b, #4
      +0x2b0: uxtl    v3.8h, v0.8b
      +0x2b4: uxtl2   v4.8h, v0.16b
      +0x2b8: shll2   v5.8h, v1.16b, #8
      +0x2bc: ushll   v0.8h, v2.8b, #4
      +0x2c0: bic     v6.8h, #0xf0, lsl #8
      +0x2c4: uxtl    v1.8h, v7.8b
      +0x2c8: ushll2  v16.8h, v2.16b, #4
      +0x2cc: orr     v2.16b, v6.16b, v3.16b
      +0x2d0: orr     v3.16b, v0.16b, v1.16b
      +0x2d4: bic     v5.8h, #0xf0, lsl #8
      +0x2d8: st2     {v2.8h-v3.8h}, [x8]
      +0x2dc: uxtl2   v0.8h, v7.16b
      +0x2e0: orr     v1.16b, v5.16b, v4.16b
      +0x2e4: orr     v2.16b, v16.16b, v0.16b
      +0x2e8: st2     {v1.8h-v2.8h}, [x9]
      +0x2ec: ret
 ***)

let MLKEM_NATIVE_POLY_FROMBYTES_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_frombytes"];;

(* ------------------------------------------------------------------------- *)
(* The input as 128 words of 24 bits w k, each holding two coefficients, and *)
(* its 128-bit parts, as LD3 reads them, as joins of their bytes.            *)
(* ------------------------------------------------------------------------- *)

let FB_BYTES_STMT =
  `!a n k s j.
        read (memory :> bytes(a,384)) s = n /\ k < 128 /\ j < 3
        ==> read (memory :> bytes8(word_add a (word(3 * k + j)))) s =
            word_subword (word(n DIV 2 EXP (24 * k)):24 word) (8 * j,8)`;;

let FB_BYTES = assume_spec FB_BYTES_STMT;;

let FB_FIELD_STMT =
  `!n k e. e < 2
           ==> word((n DIV 2 EXP (12 * (2 * k + e))) MOD 2 EXP 12):int16 =
               word_zx(word_subword (word(n DIV 2 EXP (24 * k)):24 word)
                                    (12 * e,12):12 word)`;;

let FB_FIELD = assume_spec FB_FIELD_STMT;;

let FB_MERGES = map (fun k ->
  let addr = if k = 0 then `a:int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
            mk_comb(`word:num->int64`, mk_small_numeral(16 * k))) in
  READ_MEMORY_MERGE_CONV 4
   (vsubst [addr,`x:int64`] `read (memory :> bytes128 x) s0`)) (0--23);;

let FB_INPUT_TAC =
  SUBGOAL_THEN `?w:num->24 word. !k. word(n DIV 2 EXP (24 * k)) = w k`
   STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\k. word(n DIV 2 EXP (24 * k)):24 word` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k < 128
        ==> read (memory :> bytes8 (word_add a (word(3 * k)))) s0 =
            word_subword ((w:num->24 word) k) (0,8) /\
            read (memory :> bytes8 (word_add a (word(3 * k + 1)))) s0 =
            word_subword (w k) (8,8) /\
            read (memory :> bytes8 (word_add a (word(3 * k + 2)))) s0 =
            word_subword (w k) (16,8)`
   MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `w:num->24 word` (concl th)
      then REWRITE_TAC[GSYM th] THEN ASSUME_TAC th else NO_TAC) THEN
    MP_TAC(CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES])
     (SPECL [`a:int64`; `n:num`; `k:num`; `s0:armstate`; `0`] FB_BYTES)) THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
     (SPECL [`a:int64`; `n:num`; `k:num`; `s0:armstate`; `1`] FB_BYTES)) THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
     (SPECL [`a:int64`; `n:num`; `k:num`; `s0:armstate`; `2`] FB_BYTES)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC FB_MERGES THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes8 a) s = x`];;

(*** After each step, the registers loaded by LD3 as joins of bytes ***)

let FB_SIMD_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> match t with
              Const("word_subdeinterleave",_) -> true | _ -> false))
           (concl th)
    then CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV []))
          (CONV_RULE(TOP_DEPTH_CONV MLKEM_NATIVE_INTERLEAVE_CONV) th)
    else th) THEN
  SIMD_SIMPLIFY_TAC[];;

(*** The 32-byte stores, as the 16 coefficients in each ***)

let FB_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
    check (can (term_match [] `read (memory :> bytes256 a) s = x`) o
           concl))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o
      CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])) o
      CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD])))
     (CONJUNCTS th)));;

(*** The coefficients as the 12-bit fields of the w k ***)

let FB_FIELDS_TAC =
  FIRST_ASSUM(fun def ->
    if is_forall(concl def) && free_in `w:num->24 word` (concl def) &&
       not(is_imp(snd(dest_forall(concl def))))
    then
      let ths = map (fun i ->
        let k = i / 2 and e = i mod 2 in
        let th = MP (SPECL [`n:num`; mk_small_numeral k; mk_small_numeral e]
                           FB_FIELD)
                    (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                                 (mk_small_numeral e) `2`))) in
        CONV_RULE(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV))
         (REWRITE_RULE[def; ARITH_RULE `2 EXP 12 = 4096`] th)) (0--255) in
      REWRITE_TAC ths
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The check for overlap has one branch for each order of the arrays: with   *)
(* the input a (384 bytes) and the output r (512 bytes), the scalar loop is  *)
(* taken unless a + 384 <= r or r + 512 <= a. In either case the vector code *)
(* is entered at the same instruction, after 3 or 6 steps respectively.      *)
(* ------------------------------------------------------------------------- *)

let FB_RESOLVE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_FLAG; VAL_WORD_SUB_EQ_0]) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read PC s = if p then x else y`) c then
      let p = rand(rator(rator(rand c))) in
      let decide q = SUBGOAL_THEN q (fun th' ->
        ASSUME_TAC(REWRITE_RULE[th'] th)) THENL [ASM_ARITH_TAC; ALL_TAC] in
      decide p ORELSE decide (mk_neg p)
    else failwith "FB_RESOLVE_TAC");;

let FB_CHECK_TAC (body:int->tactic) =
  MP_TAC(SPECL [`r:int64`; `a:int64`; `512`; `384`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_CLANG17_O3_EXEC (1--3) THEN
  ASM_CASES_TAC `val(word_add a (word 384):int64) <= val(r:int64)` THENL
   [FB_RESOLVE_TAC THEN body 3;
    FB_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_CLANG17_O3_EXEC (4--6) THEN
    FB_RESOLVE_TAC THEN body 6];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decode 12 in common/fips203.ml,           *)
(* coefficient i of the result is bits 12 * i to 12 * i + 11 of the number   *)
(* given by the 384 bytes.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMBYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_frombytes) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,384)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMBYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_FROMBYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_FROMBYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,384]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_frombytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,384; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_FROMBYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_FROMBYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* gcc12_O2, with the same simulation as for correctness.                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMBYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e r a n pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,384]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_frombytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,384)) s = n /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes16
                                   (word_add r (word(2 * i)))) s =
                             word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,384; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_FROMBYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_FROMBYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT;;
