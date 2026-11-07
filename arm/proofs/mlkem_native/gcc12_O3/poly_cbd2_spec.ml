(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Centered binomial distribution with eta = 2. This is the code for         *)
(* mlkem_poly_cbd2 from mlkem-native's portable C implementation compiled by *)
(* gcc 12 with -O3 (see mlkem_native/README.md). It is verified in the whole *)
(* image (see libmlkem.ml).                                                  *)
(*                                                                           *)
(* The compiler has vectorized the loop, 64 coefficients per iteration from  *)
(* two 128-bit loads, after a check that the input and the output do not    *)
(* overlap; if they do, the code falls back to the loop of gcc12_O2. Since   *)
(* the specification requires them not to overlap, only the vector code     *)
(* runs. Its constants are made with MOVI, so unlike that of gcc12_O2 the    *)
(* safety specification has no read-only data. The four iterations of the   *)
(* loop are simulated one after the other.                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_cbd2:
       +0x0: mov     x3, x1
       +0x4: mov     x1, x0
       +0x8: add     x4, x3, #0x80
       +0xc: add     x0, x0, #0x200
      +0x10: cmp     x1, x4
      +0x14: ccmp    x3, x0, #0x2, cc
      +0x18: b.cc    <mlkem_poly_cbd2+0x1c4>
      +0x1c: movi    v18.16b, #0x55
      +0x20: mov     x2, x3
      +0x24: movi    v2.8h, #0x3
      +0x28: mov     x0, x1
      +0x2c: ldp     q1, q0, [x2]
      +0x30: add     x2, x2, #0x20
      +0x34: ushr    v4.4s, v1.4s, #1
      +0x38: ushr    v3.4s, v0.4s, #1
      +0x3c: and     v1.16b, v1.16b, v18.16b
      +0x40: and     v0.16b, v0.16b, v18.16b
      +0x44: and     v4.16b, v4.16b, v18.16b
      +0x48: and     v3.16b, v3.16b, v18.16b
      +0x4c: add     v1.4s, v4.4s, v1.4s
      +0x50: add     v0.4s, v3.4s, v0.4s
      +0x54: shrn    v26.4h, v1.4s, #2
      +0x58: ushr    v17.4s, v0.4s, #18
      +0x5c: ushr    v27.4s, v0.4s, #22
      +0x60: ushr    v19.4s, v0.4s, #28
      +0x64: ushr    v25.4s, v1.4s, #18
      +0x68: ushr    v16.4s, v1.4s, #24
      +0x6c: ushr    v31.4s, v0.4s, #24
      +0x70: ushr    v23.4s, v1.4s, #26
      +0x74: ushr    v30.4s, v0.4s, #26
      +0x78: shrn    v4.4h, v1.4s, #8
      +0x7c: shrn    v22.4h, v1.4s, #10
      +0x80: ushr    v7.4s, v1.4s, #20
      +0x84: ushr    v29.4s, v0.4s, #20
      +0x88: ushr    v21.4s, v1.4s, #22
      +0x8c: shrn    v24.4h, v1.4s, #4
      +0x90: shrn    v20.4h, v1.4s, #6
      +0x94: ushr    v6.4s, v1.4s, #28
      +0x98: shrn    v3.4h, v1.4s, #12
      +0x9c: shrn    v5.4h, v1.4s, #14
      +0xa0: shrn2   v26.8h, v0.4s, #2
      +0xa4: uzp1    v28.8h, v1.8h, v0.8h
      +0xa8: uzp1    v25.8h, v25.8h, v17.8h
      +0xac: shrn2   v4.8h, v0.4s, #8
      +0xb0: uzp2    v17.8h, v1.8h, v0.8h
      +0xb4: shrn2   v22.8h, v0.4s, #10
      +0xb8: uzp1    v21.8h, v21.8h, v27.8h
      +0xbc: shrn2   v24.8h, v0.4s, #4
      +0xc0: shrn2   v20.8h, v0.4s, #6
      +0xc4: uzp1    v6.8h, v6.8h, v19.8h
      +0xc8: ushr    v27.4s, v0.4s, #30
      +0xcc: ushr    v19.4s, v1.4s, #30
      +0xd0: shrn2   v3.8h, v0.4s, #12
      +0xd4: shrn2   v5.8h, v0.4s, #14
      +0xd8: uzp1    v16.8h, v16.8h, v31.8h
      +0xdc: uzp1    v23.8h, v23.8h, v30.8h
      +0xe0: uzp1    v7.8h, v7.8h, v29.8h
      +0xe4: uzp1    v19.8h, v19.8h, v27.8h
      +0xe8: and     v5.16b, v5.16b, v2.16b
      +0xec: and     v26.16b, v26.16b, v2.16b
      +0xf0: and     v0.16b, v28.16b, v2.16b
      +0xf4: and     v25.16b, v25.16b, v2.16b
      +0xf8: and     v17.16b, v17.16b, v2.16b
      +0xfc: and     v16.16b, v16.16b, v2.16b
     +0x100: and     v23.16b, v23.16b, v2.16b
     +0x104: and     v4.16b, v4.16b, v2.16b
     +0x108: and     v22.16b, v22.16b, v2.16b
     +0x10c: and     v7.16b, v7.16b, v2.16b
     +0x110: and     v21.16b, v21.16b, v2.16b
     +0x114: and     v1.16b, v24.16b, v2.16b
     +0x118: and     v20.16b, v20.16b, v2.16b
     +0x11c: and     v6.16b, v6.16b, v2.16b
     +0x120: and     v3.16b, v3.16b, v2.16b
     +0x124: sub     v17.8h, v17.8h, v25.8h
     +0x128: sub     v16.8h, v16.8h, v23.8h
     +0x12c: sub     v6.8h, v6.8h, v19.8h
     +0x130: sub     v7.8h, v7.8h, v21.8h
     +0x134: sub     v3.8h, v3.8h, v5.8h
     +0x138: sub     v0.8h, v0.8h, v26.8h
     +0x13c: sub     v4.8h, v4.8h, v22.8h
     +0x140: sub     v1.8h, v1.8h, v20.8h
     +0x144: zip1    v5.8h, v0.8h, v17.8h
     +0x148: zip1    v19.8h, v4.8h, v16.8h
     +0x14c: zip2    v4.8h, v4.8h, v16.8h
     +0x150: zip1    v16.8h, v1.8h, v7.8h
     +0x154: zip2    v1.8h, v1.8h, v7.8h
     +0x158: zip1    v7.8h, v3.8h, v6.8h
     +0x15c: zip2    v0.8h, v0.8h, v17.8h
     +0x160: zip2    v3.8h, v3.8h, v6.8h
     +0x164: zip1    v17.8h, v5.8h, v19.8h
     +0x168: zip2    v5.8h, v5.8h, v19.8h
     +0x16c: zip1    v19.8h, v16.8h, v7.8h
     +0x170: zip2    v6.8h, v16.8h, v7.8h
     +0x174: zip1    v7.8h, v0.8h, v4.8h
     +0x178: zip2    v0.8h, v0.8h, v4.8h
     +0x17c: zip1    v4.8h, v1.8h, v3.8h
     +0x180: zip2    v1.8h, v1.8h, v3.8h
     +0x184: zip1    v3.8h, v17.8h, v19.8h
     +0x188: zip2    v17.8h, v17.8h, v19.8h
     +0x18c: zip1    v16.8h, v5.8h, v6.8h
     +0x190: zip2    v5.8h, v5.8h, v6.8h
     +0x194: zip1    v6.8h, v7.8h, v4.8h
     +0x198: zip2    v7.8h, v7.8h, v4.8h
     +0x19c: stp     q3, q17, [x0]
     +0x1a0: zip1    v3.8h, v0.8h, v1.8h
     +0x1a4: stp     q16, q5, [x0, #32]
     +0x1a8: zip2    v0.8h, v0.8h, v1.8h
     +0x1ac: stp     q6, q7, [x0, #64]
     +0x1b0: stp     q3, q0, [x0, #96]
     +0x1b4: add     x0, x0, #0x80
     +0x1b8: cmp     x4, x2
     +0x1bc: b.ne    <mlkem_poly_cbd2+0x2c>
     +0x1c0: ret
     +0x1c4: movi    v7.8h, #0x3
     +0x1c8: mov     x2, #0x0
     +0x1cc: nop
     +0x1d0: ldr     w0, [x3, x2, lsl #2]
     +0x1d4: lsl     x4, x2, #4
     +0x1d8: add     x2, x2, #0x1
     +0x1dc: and     w5, w0, #0x55555555
     +0x1e0: lsr     w0, w0, #1
     +0x1e4: and     w0, w0, #0x55555555
     +0x1e8: add     w9, w0, w5
     +0x1ec: fmov    s0, w9
     +0x1f0: fmov    s16, w9
     +0x1f4: ushr    v2.2s, v0.2s, #20
     +0x1f8: ushr    v3.2s, v0.2s, #16
     +0x1fc: ubfx    x6, x9, #6, #2
     +0x200: ubfx    x0, x9, #2, #2
     +0x204: fmov    d1, x0
     +0x208: ubfx    x5, x9, #10, #2
     +0x20c: ushr    v4.2s, v0.2s, #4
     +0x210: ubfx    x8, x9, #14, #2
     +0x214: mov     v1.h[1], w6
     +0x218: ushr    v0.2s, v0.2s, #24
     +0x21c: mov     v3.s[1], v2.s[0]
     +0x220: ubfx    x7, x9, #18, #2
     +0x224: fmov    s2, w9
     +0x228: ushr    v5.2s, v16.2s, #28
     +0x22c: ubfx    x6, x9, #22, #2
     +0x230: ushr    v6.2s, v2.2s, #8
     +0x234: mov     v1.h[2], w5
     +0x238: mov     v2.16b, v16.16b
     +0x23c: ubfx    x5, x9, #26, #2
     +0x240: mov     v3.s[2], v0.s[0]
     +0x244: ushr    v0.2s, v16.2s, #30
     +0x248: mov     v1.h[3], w8
     +0x24c: mov     v2.s[1], v4.s[0]
     +0x250: ushr    v4.2s, v16.2s, #12
     +0x254: mov     v3.s[3], v5.s[0]
     +0x258: mov     v1.h[4], w7
     +0x25c: mov     v2.s[2], v6.s[0]
     +0x260: mov     v1.h[5], w6
     +0x264: mov     v2.s[3], v4.s[0]
     +0x268: mov     v1.h[6], w5
     +0x26c: uzp1    v2.8h, v2.8h, v3.8h
     +0x270: mov     v1.h[7], v0.h[0]
     +0x274: and     v2.16b, v2.16b, v7.16b
     +0x278: sub     v0.8h, v2.8h, v1.8h
     +0x27c: str     q0, [x1, x4]
     +0x280: cmp     x2, #0x20
     +0x284: b.ne    <mlkem_poly_cbd2+0x1d0>
     +0x288: ret
 ***)

let MLKEM_NATIVE_POLY_CBD2_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_cbd2"];;

(* ------------------------------------------------------------------------- *)
(* As at -O2, coefficient j of 8 for a 32-bit word t of the input comes from *)
(* its 4-bit field j (CBD2_LANE, with the lemmas of gcc12_O2). Here each     *)
(* 32-bit lane of the two vectors loaded holds one such word, its pairs of   *)
(* bits are added, and the fields are taken out with SHRN, USHR, UZP1, UZP2  *)
(* and AND with 3, subtracted, and put in order with ZIP1 and ZIP2.          *)
(* ------------------------------------------------------------------------- *)

let NIBBLE_BIT_STMT =
  `!n m k. k < 4
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 16) DIV 2 EXP k) MOD 2`;;

let NIBBLE_BIT = assume_spec NIBBLE_BIT_STMT;;

let CBD2_NIBBLE_STMT =
  `!m. m < 16
       ==> word_sub
            (word_zx (word_add (word_and (word m:4 word) (word 1))
                               (word_and (word_ushr (word m) 1) (word 1))))
            (word_zx (word_add (word_and (word_ushr (word m:4 word) 2)
                                         (word 1))
                               (word_ushr (word m) 3))):int16 =
           iword(&(m MOD 2 + (m DIV 2) MOD 2) -
                 &((m DIV 4) MOD 2 + (m DIV 8) MOD 2))`;;

let CBD2_NIBBLE = assume_spec CBD2_NIBBLE_STMT;;

let CBD2_LANE_STMT =
  `!n i j t:int32.
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
                  (n DIV 2 EXP (4 * (8 * i + j) + 3)) MOD 2))`;;

let CBD2_LANE = assume_spec CBD2_LANE_STMT;;

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

(*** The loop branch, between pointers with known offsets ***)

let CBD2_BRANCH_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read PC s = if p then x else y`) (concl th)
    then CONV_RULE(RAND_CONV
          (REWRITE_CONV[WORD_RULE
            `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`]
           THENC DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
           REWRITE_CONV[])) th
    else th);;

let CBD2_STEPS_TAC k =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O3_EXEC [k] THEN CBD2_SIMD_TAC;;

let CBD2_ITERATION_TAC it =
  MAP_EVERY CBD2_STEPS_TAC ((12 + 101 * it)--(112 + 101 * it)) THEN
  CBD2_BRANCH_TAC;;

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
(* Correctness proof. As for mlkem_cbd 2 in common/fips203.ml, coefficient i *)
(* of the result is the number of 1 bits among bits 4 * i and 4 * i + 1 of   *)
(* the 128 bytes as a number n, minus the number among bits 4 * i + 2 and    *)
(* 4 * i + 3, here as a 16-bit integer rather than modulo 3329.              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
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
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_CBD2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

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
    ~keep_maychanges:true
    mlkem_native_poly_cbd2_signature
    MLKEM_NATIVE_POLY_CBD2_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_CBD2_GCC12_O3_EXEC;;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,128]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_cbd2) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,128; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_CBD2_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
