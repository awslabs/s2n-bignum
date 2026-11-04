(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 4 bits per coefficient. This is the code   *)
(* for mlkem_poly_compress_d4 from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -O3 (see mlkem_native/README.md). It is verified  *)
(* in the whole image (see libmlkem.ml).                                     *)
(*                                                                           *)
(* The compiler has vectorized the loop, 32 coefficients per iteration with  *)
(* 32-bit lanes, after a check that the input and the output do not         *)
(* overlap; if they do, the code falls back to a scalar loop. Since the      *)
(* specification requires them not to overlap, only the vector code runs.    *)
(* Unlike at -O2, the code uses neither the stack nor the stack guard. The   *)
(* specifications are still those of gcc12_O2, with the 32-byte stack frame  *)
(* and the stack guard, so that the callers can use them in the same way.    *)
(* The eight iterations of the loop are simulated one after the other.       *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/utils/mlkem_native_overlap.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d4:
       +0x0: mov     x2, x0
       +0x4: mov     x0, x1
       +0x8: add     x1, x2, #0x80
       +0xc: add     x11, x0, #0x200
      +0x10: cmp     x0, x1
      +0x14: ccmp    x2, x11, #0x2, cc
      +0x18: b.cc    <mlkem_poly_compress_d4+0xfc>
      +0x1c: movi    v1.4s, #0x8, lsl #24
      +0x20: adrp    x1, <page>
      +0x24: ldr     q2, [x1, #2352]  // mlkem_poly_compress_d4_consts
      +0x28: mov     x1, x2
      +0x2c: nop
      +0x30: ldp     q4, q0, [x0]
      +0x34: ldp     q3, q6, [x0, #32]
      +0x38: add     x0, x0, #0x40
      +0x3c: uzp2    v5.8h, v4.8h, v0.8h
      +0x40: mov     v18.16b, v1.16b
      +0x44: uzp1    v4.8h, v4.8h, v0.8h
      +0x48: uzp2    v0.8h, v3.8h, v6.8h
      +0x4c: uzp1    v3.8h, v3.8h, v6.8h
      +0x50: sxtl2   v6.4s, v5.8h
      +0x54: sxtl    v16.4s, v5.4h
      +0x58: sxtl    v7.4s, v0.4h
      +0x5c: sxtl2   v5.4s, v0.8h
      +0x60: mla     v18.4s, v6.4s, v2.4s
      +0x64: mov     v17.16b, v1.16b
      +0x68: mov     v0.16b, v1.16b
      +0x6c: mov     v6.16b, v1.16b
      +0x70: ushr    v18.4s, v18.4s, #28
      +0x74: mla     v17.4s, v5.4s, v2.4s
      +0x78: mla     v0.4s, v16.4s, v2.4s
      +0x7c: sxtl2   v5.4s, v4.8h
      +0x80: sxtl    v16.4s, v4.4h
      +0x84: mla     v6.4s, v7.4s, v2.4s
      +0x88: sxtl2   v4.4s, v3.8h
      +0x8c: sxtl    v7.4s, v3.4h
      +0x90: mov     v3.16b, v1.16b
      +0x94: ushr    v0.4s, v0.4s, #28
      +0x98: ushr    v6.4s, v6.4s, #28
      +0x9c: ushr    v17.4s, v17.4s, #28
      +0xa0: mla     v3.4s, v16.4s, v2.4s
      +0xa4: mov     v16.16b, v1.16b
      +0xa8: uzp1    v0.8h, v0.8h, v18.8h
      +0xac: uzp1    v6.8h, v6.8h, v17.8h
      +0xb0: ushr    v3.4s, v3.4s, #28
      +0xb4: mla     v16.4s, v5.4s, v2.4s
      +0xb8: mov     v5.16b, v1.16b
      +0xbc: uzp1    v0.16b, v0.16b, v6.16b
      +0xc0: ushr    v16.4s, v16.4s, #28
      +0xc4: mla     v5.4s, v7.4s, v2.4s
      +0xc8: mov     v7.16b, v1.16b
      +0xcc: shl     v0.16b, v0.16b, #4
      +0xd0: uzp1    v3.8h, v3.8h, v16.8h
      +0xd4: mla     v7.4s, v4.4s, v2.4s
      +0xd8: ushr    v4.4s, v5.4s, #28
      +0xdc: ushr    v5.4s, v7.4s, #28
      +0xe0: uzp1    v4.8h, v4.8h, v5.8h
      +0xe4: uzp1    v3.16b, v3.16b, v4.16b
      +0xe8: orr     v0.16b, v0.16b, v3.16b
      +0xec: str     q0, [x1], #16
      +0xf0: cmp     x11, x0
      +0xf4: b.ne    <mlkem_poly_compress_d4+0x30>
      +0xf8: ret
      +0xfc: mov     w3, #0xafb0
     +0x100: mov     x1, x2
     +0x104: movk    w3, #0x13, lsl #16
     +0x108: mov     w2, #0x8000000
     +0x10c: nop
     +0x110: ldrsh   w6, [x0, #6]
     +0x114: add     x1, x1, #0x4
     +0x118: ldrsh   w5, [x0, #10]
     +0x11c: ldrsh   w4, [x0, #14]
     +0x120: ldrsh   w7, [x0, #2]
     +0x124: ldrsh   w12, [x0, #4]
     +0x128: madd    w6, w6, w3, w2
     +0x12c: ldrsh   w10, [x0, #8]
     +0x130: madd    w5, w5, w3, w2
     +0x134: ldrsh   w9, [x0, #12]
     +0x138: madd    w4, w4, w3, w2
     +0x13c: ldrsh   w8, [x0], #16
     +0x140: madd    w7, w7, w3, w2
     +0x144: madd    w12, w12, w3, w2
     +0x148: lsr     w6, w6, #28
     +0x14c: madd    w10, w10, w3, w2
     +0x150: lsr     w5, w5, #28
     +0x154: madd    w9, w9, w3, w2
     +0x158: lsr     w4, w4, #28
     +0x15c: madd    w8, w8, w3, w2
     +0x160: lsr     w7, w7, #28
     +0x164: extr    w6, w6, w12, #28
     +0x168: extr    w5, w5, w10, #28
     +0x16c: extr    w4, w4, w9, #28
     +0x170: sturb   w6, [x1, #-3]
     +0x174: extr    w7, w7, w8, #28
     +0x178: sturb   w7, [x1, #-4]
     +0x17c: sturb   w5, [x1, #-2]
     +0x180: sturb   w4, [x1, #-1]
     +0x184: cmp     x0, x11
     +0x188: b.ne    <mlkem_poly_compress_d4+0x110>
     +0x18c: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_compress_d4"];;

(*** The vector of 32-bit lanes 1290160 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_CONSTANTS =
  MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlkem_poly_compress_d4_consts") 128;;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 4 bits, as computed in a 32-bit lane  *)
(* (COMPRESS_D4_ARITH is that of gcc12_O2), and the 128 bytes of the result  *)
(* from the pairs of 4-bit values in them.                                   *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D4_ARITH = prove
 (`!v. v < 3329
       ==> (134217728 + v * 1290160) DIV 268435456 =
           (32 * v + 3329) DIV 6658`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`32 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(32 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(32 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `32 * v + 3329 = q * 6658 + r` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH];
    ALL_TAC] THEN
  MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(134217728 + v * 1290160) - q * 268435456` THEN
  ASM_ARITH_TAC);;

let COMPRESS_D4_LANE = prove
 (`!y:int16.
        val y < 3329
        ==> word_subword (word_add (word 134217728)
                                   (word_mul (word_sx y) (word 1290160)):int32)
                         (28,4):4 word =
            word((32 * val y + 3329) DIV 6658)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SX_SMALL; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_ADD; VAL_WORD_MUL;
              VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_16;
              DIMINDEX_4] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`;
               ARITH_RULE `y < 3329 ==> y * 1290160 < 4294967296`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 268435456 * 16`; GSYM DIV_MOD] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN ASM_SIMP_TAC[COMPRESS_D4_ARITH]);;

let COMPRESS_D4_PACK = prove
 (`!r s (c:num->num).
     (!m. m < 128
          ==> read (memory :> bytes8 (word_add r (word m))) s =
              word_join (word(c(2 * m + 1)):4 word) (word(c(2 * m)):4 word))
     ==> read (memory :> bytes(r,128)) s =
         nsum {i | i < 256} (\i. c i MOD 16 * 2 EXP (4 * i))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!k. k <= 128
        ==> read (memory :> bytes(r,k)) s =
            nsum {i | i < 2 * k} (\i. (c:num->num) i MOD 16 * 2 EXP (4 * i))`
   (MP_TAC o SPEC `128`) THENL
   [ALL_TAC; CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; NSUM_CLAUSES_NUMSEG_LT;
                READ_MEMORY_BYTES_TRIVIAL];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC k <= 128` THEN ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC k <= 128` THEN ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[ADD1; READ_MEMORY_BYTES_SNOC] THEN
  REWRITE_TAC[ARITH_RULE `2 * (k + 1) = SUC(SUC(2 * k))`;
              NSUM_CLAUSES_NUMSEG_LT] THEN
  REWRITE_TAC[ADD1; VAL_WORD_JOIN; VAL_WORD; DIMINDEX_4; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `16 * c(2 * k + 1) MOD 16 + c(2 * k) MOD 16 < 256`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [MP_TAC(SPECL [`c(2 * k + 1):num`; `16`] MOD_LT_EQ) THEN
    MP_TAC(SPECL [`c(2 * k):num`; `16`] MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4 * 2 * k = 8 * k`;
              ARITH_RULE `4 * (2 * k + 1) = 8 * k + 4`; EXP_ADD] THEN
  SPEC_TAC(`nsum {i | i < 2 * k} (\i. (c:num->num) i MOD 16 * 2 EXP (4 * i))`,
           `n:num`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUM_RING);;

(*** The 256 coefficients, merged into the 128-bit parts that the loads
 *** read ***)

let COMPRESS_D4_MERGES = map (fun k ->
  let addr = if k = 0 then `a:int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
            mk_comb(`word:num->int64`, mk_small_numeral(16 * k))) in
  READ_MEMORY_MERGE_CONV 3
   (vsubst [addr,`x:int64`] `read (memory :> bytes128 x) s0`)) (0--31);;

let COMPRESS_D4_INPUT_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_forall(concl th) && free_in `x:num->int16` (concl th))) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC COMPRESS_D4_MERGES THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`];;

(*** The loop branch, between pointers with known offsets ***)

let COMPRESS_D4_BRANCH_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read PC s = if p then x else y`) (concl th)
    then CONV_RULE(RAND_CONV
          (REWRITE_CONV[WORD_RULE
            `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`]
           THENC DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
           REWRITE_CONV[])) th
    else th);;

let COMPRESS_D4_ITERATION_TAC it =
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) ((13 + 50 * it)--(62 + 50 * it)) THEN
  COMPRESS_D4_BRANCH_TAC;;

(*** After the simulation, the subwords of the stores taken through AND and
 *** OR to the lanes ***)

let COMPRESS_D4_SIMPLIFY_CONV =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC REWR_CONV WORD_SUBWORD_OR ORELSEC
    WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV;;

(*** Each stored byte as the bits 28 to 31 of the two lanes for it, found
 *** by bit-blasting with the lanes, multiply-accumulates, as variables ***)

let compress_d4_lanepat =
  `word_add (word 134217728)
            (word_mul (word_shl (word_sx (y:int16)) 0) (word 1290160)):int32`;;

let COMPRESS_D4_BYTE_RULE th =
  let v = rand(concl th) in
  let ms = setify(find_terms (can (term_match [] compress_d4_lanepat)) v) in
  let idx m = dest_small_numeral(rand(find_term
    (fun t -> is_comb t && rator t = `x:num->int16`) m)) in
  let ims = sort (fun (i,_) (j,_) -> i < j) (map (fun m -> idx m,m) ms) in
  if length ims <> 2 then
    (print_term v; Format.print_newline();
     failwith "COMPRESS_D4_BYTE_RULE") else
  let gs = map (fun _ -> genvar `:int32`) ims in
  let v' = subst (zip gs (map snd ims)) v in
  let nib g = mk_comb(mk_comb(`word_subword:int32->num#num->4 word`,g),
                      `(28,4)`) in
  let tgt = mk_comb(mk_comb(`word_join:4 word->4 word->byte`,
                            nib(el 1 gs)),nib(el 0 gs)) in
  let bth = BITBLAST_RULE(mk_eq(v',tgt)) in
  CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_SHL_ZERO]))
   (TRANS th (INST (zip (map snd ims) gs) bth));;

(*** The stored bytes, from the 8 stores of 16 bytes ***)

let COMPRESS_D4_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
    check (fun th -> can (term_match []
                     `read (memory :> bytes128 a) s = x`) (concl th) &&
                     free_in `r:int64` (concl th)))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o COMPRESS_D4_BYTE_RULE o
      CONV_RULE(RAND_CONV COMPRESS_D4_SIMPLIFY_CONV) o
      CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                                       WORD_ADD_0]
                          THENC NUM_REDUCE_CONV)))
     (CONJUNCTS th)));;

(*** The 4-bit value of each coefficient, given the bounds ***)

let COMPRESS_D4_NIBBLES_TAC =
  DISCH_THEN(fun bth ->
    let lths = map (fun k ->
      let kt = mk_small_numeral k in
      MP (SPEC (mk_comb(`x:num->int16`,kt)) COMPRESS_D4_LANE)
         (MP (SPEC kt bth)
             (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` kt
                                            `256`))))) (0--255) in
    RULE_ASSUM_TAC(REWRITE_RULE lths));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 4 in common/fips203.ml, the      *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 16 * x / 3329, rounding up on ties, modulo 16, i.e.                       *)
(* ((32 * x + 3329) DIV 6658) MOD 16, and as for mlkem_encode 4 the 4-bit    *)
(* values are put together little-endian. Like the C code, this relies on    *)
(* the coefficients being in [0,3329).                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,128); (a,512); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,128); (word_sub stackpointer (word 32),32)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_poly_compress_d4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                     (word_add a (word(2 * i)))) s =
                           x i))
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,128)) s =
                       nsum {i | i < 256}
                            (\i. ((32 * val(x i) + 3329) DIV 6658) MOD 16 *
                                 2 EXP (4 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128);
                         memory :> bytes(word_sub stackpointer
                                                  (word 32),32)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `guard:int64`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  COMPRESS_D4_INPUT_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_CONSTANTS) THEN

  (*** The overlap check, the setup, the eight iterations and the exit ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_EXEC (1--7) THEN
  ALIAS_BRANCH_TAC `r:int64` `128` `a:int64` `512` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_EXEC (8--9) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_EXEC (10--12) THEN
  MAP_EVERY COMPRESS_D4_ITERATION_TAC (0--7) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_EXEC (413--413) THEN
  COMPRESS_D4_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each byte from the 4-bit values of its two coefficients ***)

  COMPRESS_D4_NIBBLES_TAC THEN
  W(fun (_,w) ->
    MP_TAC(ISPECL [`r:int64`; rand(lhand w);
                   `\i. (32 * val((x:num->int16) i) + 3329) DIV 6658`]
                  COMPRESS_D4_PACK)) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This is stated directly rather     *)
(* than by mk_safety_spec, as for gcc12_O2, with the events depending on the *)
(* address of the stack guard although the code no longer reads it. Unlike  *)
(* at -O2, the code reads 16 bytes of constants.                             *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,128; a,512; word_sub stackpointer (word 32),32] /\
       ALLPAIRS nonoverlapping
        [r,128; word_sub stackpointer (word 32),32]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O3_mc /\
                 read PC s = word (pc + mlkem_poly_compress_d4) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r guard pc
                           (word_sub stackpointer (word 32)) returnaddress /\
                    memaccess_inbounds e2
                     [a,512; r,128; word_sub stackpointer (word 32),32;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + mlkem_poly_compress_d4_consts),16]
                     [r,128; word_sub stackpointer (word 32),32]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,128);
                        memory :> bytes(word_sub stackpointer (word 32),32)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (guard:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      f_ev a r guard pc stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_EXEC (1--7) THEN
  ALIAS_BRANCH_TAC `r:int64` `128` `a:int64` `512` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_EXEC (8--9) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_EXEC (10--12) THEN
  MAP_EVERY (fun it ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_EXEC
     ((13 + 50 * it)--(62 + 50 * it)) THEN
    COMPRESS_D4_BRANCH_TAC) (0--7) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O3_EXEC (413--413) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
