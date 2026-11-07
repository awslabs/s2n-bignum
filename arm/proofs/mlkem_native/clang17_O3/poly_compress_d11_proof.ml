(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 11 bits per coefficient. This is the code  *)
(* for mlkem_poly_compress_d11 from mlkem-native's portable C implementation *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md). It is         *)
(* verified in the whole image (see libmlkem.ml).                            *)
(*                                                                           *)
(* Unlike at gcc -O2, the code does not go through a temporary array on the  *)
(* stack and has no stack protector, so it uses neither the stack nor the    *)
(* stack guard. The specifications are still those of gcc12_O2, with the     *)
(* 48-byte stack frame and the stack guard, so that the callers can use      *)
(* them in the same way.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d11:
       +0x0: mov     x9, #0x7800
       +0x4: mov     x8, xzr
       +0x8: movk    x9, #0x3afb, lsl #16
       +0xc: add     x10, x1, #0xe
      +0x10: movk    x9, #0x1, lsl #32
      +0x14: add     x11, x0, #0x5
      +0x18: mov     x12, #0x100000000
      +0x1c: add     x13, x10, x8
      +0x20: add     x8, x8, #0x10
      +0x24: cmp     x8, #0x200
      +0x28: ldursh  x15, [x13, #-12]
      +0x2c: ldursh  x14, [x13, #-14]
      +0x30: ldursh  x16, [x13, #-10]
      +0x34: madd    x15, x15, x9, x12
      +0x38: ldursh  x0, [x13, #-4]
      +0x3c: madd    x14, x14, x9, x12
      +0x40: ldursh  x17, [x13, #-8]
      +0x44: lsr     x3, x15, #30
      +0x48: madd    x16, x16, x9, x12
      +0x4c: lsr     x2, x14, #33
      +0x50: ubfx    x14, x14, #41, #3
      +0x54: and     w3, w3, #0xf8
      +0x58: ldursh  x18, [x13, #-6]
      +0x5c: orr     w14, w3, w14
      +0x60: lsr     x4, x16, #33
      +0x64: madd    x0, x0, x9, x12
      +0x68: ldursh  x1, [x13, #-2]
      +0x6c: madd    x17, x17, x9, x12
      +0x70: ldrsh   x13, [x13]
      +0x74: madd    x18, x18, x9, x12
      +0x78: lsr     x15, x15, #38
      +0x7c: sturb   w14, [x11, #-4]
      +0x80: lsr     x14, x16, #35
      +0x84: lsr     x3, x0, #33
      +0x88: bfi     w15, w4, #6, #26
      +0x8c: sturb   w2, [x11, #-5]
      +0x90: lsr     x16, x17, #32
      +0x94: lsr     x2, x18, #29
      +0x98: bfxil   w16, w4, #10, #1
      +0x9c: ubfx    x17, x17, #40, #4
      +0xa0: and     w2, w2, #0xf0
      +0xa4: madd    x13, x13, x9, x12
      +0xa8: sturb   w14, [x11, #-2]
      +0xac: lsr     x14, x18, #37
      +0xb0: madd    x1, x1, x9, x12
      +0xb4: sturb   w15, [x11, #-3]
      +0xb8: orr     w15, w2, w17
      +0xbc: bfi     w14, w3, #7, #25
      +0xc0: lsr     x17, x13, #28
      +0xc4: sturb   w16, [x11, #-1]
      +0xc8: lsr     x16, x1, #31
      +0xcc: ubfx    x18, x1, #39, #5
      +0xd0: and     w17, w17, #0xe0
      +0xd4: strb    w15, [x11]
      +0xd8: lsr     x15, x0, #34
      +0xdc: bfxil   w16, w3, #9, #2
      +0xe0: strb    w14, [x11, #1]
      +0xe4: orr     w14, w17, w18
      +0xe8: lsr     x13, x13, #36
      +0xec: strb    w15, [x11, #2]
      +0xf0: strb    w16, [x11, #3]
      +0xf4: strb    w14, [x11, #4]
      +0xf8: strb    w13, [x11, #5]
      +0xfc: add     x11, x11, #0xb
      +0x100: b.ne    <mlkem_poly_compress_d11+0x1c>
      +0x104: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_compress_d11"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 11 bits, as computed.                 *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D11_ARITH = prove
 (`!v. v < 3329
       ==> (4294967296 + v * 5284526080) DIV 8589934592 =
           (4096 * v + 3329) DIV 6658`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`4096 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(4096 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(4096 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(4294967296 + v * 5284526080) - q * 8589934592` THEN
  ASM_ARITH_TAC);;

let WORD_SX_SMALL_64 = prove
 (`!y:int16. val y < 32768 ==> (word_sx y:int64) = word_zx y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SX_ZX_GEN; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~bit 15 (y:int16)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[BIT_VAL] THEN
    ASM_SIMP_TAC[DIV_LT; ARITH_RULE `2 EXP 15 = 32768`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[WORD_OR_0]]);;

let COMPRESS_D11_FIELD = prove
 (`!y:int16.
        val y < 3329
        ==> val(word_subword
                 (word (4294967296 + val (word_sx y:int64) * 5284526080):
                  int64)
                 (33,11):11 word) =
            ((4096 * val y + 3329) DIV 6658) MOD 2048`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SX_SMALL_64; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_64; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 18446744073709551616`;
    ARITH_RULE `y < 3329
                ==> 4294967296 + y * 5284526080 < 18446744073709551616`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[COMPRESS_D11_ARITH]);;

(* ------------------------------------------------------------------------- *)
(* The packing of eight 11-bit values into eleven bytes.                     *)
(* ------------------------------------------------------------------------- *)

let VAL_JOIN_11X8 = prove
 (`!(u0:11 word) (u1:11 word) (u2:11 word) (u3:11 word)
    (u4:11 word) (u5:11 word) (u6:11 word) (u7:11 word).
     val(word_join u7 (word_join u6 (word_join u5 (word_join u4
          (word_join u3 (word_join u2 (word_join u1 u0:22 word):33 word):
           44 word):55 word):66 word):77 word):88 word) =
     val u0 + 2048 * val u1 + 4194304 * val u2 + 8589934592 * val u3 +
     17592186044416 * val u4 + 36028797018963968 * val u5 +
     73786976294838206464 * val u6 + 151115727451828646838272 * val u7`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`u0:11 word`; `u1:11 word`; `u2:11 word`; `u3:11 word`;
    `u4:11 word`; `u5:11 word`; `u6:11 word`; `u7:11 word`] THEN
  REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun k ->
    SPEC_TAC(mk_comb(`val:11 word->num`,
                     mk_var("u"^string_of_int k,`:11 word`)),
             mk_var("n"^string_of_int k,`:num`))) (0--7) THEN
  REPEAT STRIP_TAC THEN REPEAT MOD_LT_ASM_TAC THEN ARITH_TAC);;

let WORD_SUBWORD_BYTE = prove
 (`!(w:N word) p.
        word_subword w (p,8):byte = word((val w DIV 2 EXP p) MOD 256)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(*** The stored bytes as parts of the 88-bit join of the eight fields ***)

let compress_d11_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--8);;

let d11_xatoms = map (fun j ->
  vsubst [j,`j:num`]
   `word (4294967296 + val (word_sx ((x:num->int16) j):int64) * 5284526080):
    int64`) (butlast compress_d11_indices);;

let d11_join =
  vsubst (zip d11_xatoms
              (map (fun k -> mk_var("w"^string_of_int k,`:int64`)) (0--7)))
  `word_join (word_subword (w7:int64) (33,11):11 word)
    (word_join (word_subword (w6:int64) (33,11):11 word)
     (word_join (word_subword (w5:int64) (33,11):11 word)
      (word_join (word_subword (w4:int64) (33,11):11 word)
       (word_join (word_subword (w3:int64) (33,11):11 word)
        (word_join (word_subword (w2:int64) (33,11):11 word)
         (word_join (word_subword (w1:int64) (33,11):11 word)
                    (word_subword (w0:int64) (33,11):11 word):22 word):
         33 word):44 word):55 word):66 word):77 word):88 word`;;

let D11_PACK_TAC m =
  let addr =
    if m = 0 then `word_add r (word (11 * i)):int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`r:int64`),
            mk_comb(`word:num->int64`,
                    mk_binop `(+):num->num->num` `11 * i`
                             (mk_small_numeral m))) in
  let pat = vsubst [addr,`addr:int64`]
              `read (memory :> bytes8 addr) s = x` in
  let rule th =
    let v = rand(concl th) in
    let target = mk_comb(mk_comb(`word_subword:88 word->num#num->byte`,
                                 d11_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int64`) d11_xatoms in
    let eq = subst (zip gvs d11_xatoms) (mk_eq(v,target)) in
    TRANS th (INST (zip d11_xatoms gvs) (BITBLAST_RULE eq)) in
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then ASSUME_TAC(rule th) else failwith "D11_PACK_TAC");;

let WORD_ADD_2EXP64 = prove
 (`!n. word(n + 18446744073709551616):int64 = word n`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE);;

(*** The loads are at offsets from -14 to 0 from x13 = a + 14 + 16 * i, and
 *** the simulation leaves the sums of the numbers in the address unevaluated,
 *** so the facts about the coefficients are put in that form. ***)

let COMPRESS_D11_ADDR = prove
 (`!(a:int64) i. word_add a (word(16 * i)) =
         word_add a (word(14 + 16 * i + 18446744073709551602)) /\
         word_add a (word(16 * i + 2)) =
         word_add a (word(14 + 16 * i + 18446744073709551604)) /\
         word_add a (word(16 * i + 4)) =
         word_add a (word(14 + 16 * i + 18446744073709551606)) /\
         word_add a (word(16 * i + 6)) =
         word_add a (word(14 + 16 * i + 18446744073709551608)) /\
         word_add a (word(16 * i + 8)) =
         word_add a (word(14 + 16 * i + 18446744073709551610)) /\
         word_add a (word(16 * i + 10)) =
         word_add a (word(14 + 16 * i + 18446744073709551612)) /\
         word_add a (word(16 * i + 12)) =
         word_add a (word(14 + 16 * i + 18446744073709551614)) /\
         word_add a (word(16 * i + 14)) =
         word_add a (word(14 + 16 * i))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `14 + 16 * i + 18446744073709551602 = 16 * i + 18446744073709551616`;
              ARITH_RULE `14 + 16 * i + 18446744073709551604 = (16 * i + 2) + 18446744073709551616`;
              ARITH_RULE `14 + 16 * i + 18446744073709551606 = (16 * i + 4) + 18446744073709551616`;
              ARITH_RULE `14 + 16 * i + 18446744073709551608 = (16 * i + 6) + 18446744073709551616`;
              ARITH_RULE `14 + 16 * i + 18446744073709551610 = (16 * i + 8) + 18446744073709551616`;
              ARITH_RULE `14 + 16 * i + 18446744073709551612 = (16 * i + 10) + 18446744073709551616`;
              ARITH_RULE `14 + 16 * i + 18446744073709551614 = (16 * i + 12) + 18446744073709551616`;
              ARITH_RULE `14 + 16 * i = 16 * i + 14`; WORD_ADD_2EXP64]);;

(*** The same for the addresses in the events of the safety proof, which are
 *** put in the form base + offset, for the loads and for the stores. ***)

let COMPRESS_D11_EVENT_ADDR = prove
 (`(!(a:int64) i. word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551602) =
     word_add a (word(16 * i)) /\
     word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551604) =
     word_add a (word(16 * i + 2)) /\
     word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551606) =
     word_add a (word(16 * i + 4)) /\
     word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551608) =
     word_add a (word(16 * i + 6)) /\
     word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551610) =
     word_add a (word(16 * i + 8)) /\
     word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551612) =
     word_add a (word(16 * i + 10)) /\
     word_add (word_add (word_add a (word 14)) (word(16 * i))) (word 18446744073709551614) =
     word_add a (word(16 * i + 12)) /\
     word_add (word_add a (word 14)) (word(16 * i)) =
     word_add a (word(16 * i + 14))) /\
   (!(r:int64) i. word_add (word_add r (word(11 * i))) (word 1) =
     word_add r (word(11 * i + 1)) /\
     word_add (word_add r (word(11 * i))) (word 2) =
     word_add r (word(11 * i + 2)) /\
     word_add (word_add r (word(11 * i))) (word 3) =
     word_add r (word(11 * i + 3)) /\
     word_add (word_add r (word(11 * i))) (word 4) =
     word_add r (word(11 * i + 4)) /\
     word_add (word_add r (word(11 * i))) (word 5) =
     word_add r (word(11 * i + 5)) /\
     word_add (word_add r (word(11 * i))) (word 6) =
     word_add r (word(11 * i + 6)) /\
     word_add (word_add r (word(11 * i))) (word 7) =
     word_add r (word(11 * i + 7)) /\
     word_add (word_add r (word(11 * i))) (word 8) =
     word_add r (word(11 * i + 8)) /\
     word_add (word_add r (word(11 * i))) (word 9) =
     word_add r (word(11 * i + 9)) /\
     word_add (word_add r (word(11 * i))) (word 10) =
     word_add r (word(11 * i + 10)))`,
  SUBGOAL_THEN
   `word 18446744073709551602:int64 = word_neg(word 14) /\
    word 18446744073709551604:int64 = word_neg(word 12) /\
    word 18446744073709551606:int64 = word_neg(word 10) /\
    word 18446744073709551608:int64 = word_neg(word 8) /\
    word 18446744073709551610:int64 = word_neg(word 6) /\
    word 18446744073709551612:int64 = word_neg(word 4) /\
    word 18446744073709551614:int64 = word_neg(word 2)`
  STRIP_ASSUME_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* The loop body, for eight coefficients, with X13 pointing to them (via    *)
(* X10 and X8) and X11 to the eleven bytes for them plus 5, advanced at the  *)
(* end of the body, so that the loads have offsets from -14 to 0 and the     *)
(* stores from -5 to 5.                                                      *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D11_BODY_TAC =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_EXEC (1--58);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 11 in common/fips203.ml, the     *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 2048 * x / 3329, rounding up on ties, modulo 2048, i.e.                   *)
(* ((4096 * x + 3329) DIV 6658) MOD 2048, and as for mlkem_encode 11 the     *)
(* 11-bit values are put together little-endian. Like the C code, this       *)
(* relies on the coefficients being in [0,3329).                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,352); (a,512); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
         [(r,352); (word_sub stackpointer (word 48),48)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_compress_d11) /\
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
                   ==> read(memory :> bytes(r,352)) s =
                       nsum {i | i < 256}
                            (\i. ((4096 * val(x i) + 3329) DIV 6658) MOD
                                 2048 * 2 EXP (11 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(r,352);
                         memory :> bytes(word_sub stackpointer
                                                  (word 48),48)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `guard:int64`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop, over groups of 8 coefficients ***)

  ENSURES_WHILE_UP2_TAC `32` `pc + mlkem_poly_compress_d11_loop1`
   `pc + mlkem_poly_compress_d11_loop1_exit`
   `\i s. read X8 s = word(16 * i) /\
          read X9 s = word 5284526080 /\
          read X10 s = word_add a (word 14) /\
          read X11 s = word_add (word_add r (word(11 * i))) (word 5) /\
          read X12 s = word 4294967296 /\
          read X30 s = returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          ((!j. j < 256 ==> val(x j) < 3329)
           ==> read(memory :> bytes(r,11 * i)) s =
               nsum {j | j < 8 * i}
                (\j. ((4096 * val(x j) + 3329) DIV 6658) MOD 2048 *
                     2 EXP (11 * j)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                NSUM_CLAUSES_NUMSEG_LT; READ_MEMORY_BYTES_TRIVIAL];

    (*** The loop body, for eight coefficients and eleven bytes ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun jt ->
      FIRST_ASSUM(MP_TAC o SPEC jt o check (is_forall o concl)) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i < 32` THEN ARITH_TAC; DISCH_TAC])
     (butlast compress_d11_indices) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `2 * 8 * i = 16 * i`;
      ARITH_RULE `2 * (8 * i + 1) = 16 * i + 2`;
      ARITH_RULE `2 * (8 * i + 2) = 16 * i + 4`;
      ARITH_RULE `2 * (8 * i + 3) = 16 * i + 6`;
      ARITH_RULE `2 * (8 * i + 4) = 16 * i + 8`;
      ARITH_RULE `2 * (8 * i + 5) = 16 * i + 10`;
      ARITH_RULE `2 * (8 * i + 6) = 16 * i + 12`;
      ARITH_RULE `2 * (8 * i + 7) = 16 * i + 14`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COMPRESS_D11_ADDR]) THEN
    COMPRESS_D11_BODY_TAC THEN
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
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[];
      REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    (*** The new bytes as parts of the join of the 11-bit fields ***)

    MAP_EVERY D11_PACK_TAC (0--10) THEN
    REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`word_add r (word(11 * i)):int64`; `11`;
                  mk_comb(`val:88 word->num`,d11_join); `s58:armstate`]
                 READ_MEMORY_BYTES_OF_BYTES8) THEN
    ANTS_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_CLAUSES;
                  WORD_ADD_0] THEN
      ASM_REWRITE_TAC[WORD_SUBWORD_BYTE] THEN CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPEC d11_join VAL_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    SIMP_TAC[MOD_LT] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[VAL_JOIN_11X8] THEN

    (*** The compression of each coefficient ***)

    MAP_EVERY (fun jt ->
      MP_TAC(SPEC (mk_comb(`x:num->int16`,jt)) COMPRESS_D11_FIELD) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (can (term_match []
                `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o concl)) THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) (butlast compress_d11_indices) THEN

    (*** The new values in the number for the output ***)

    REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`; NSUM_LT_ADD] THEN
    REWRITE_TAC[NUMSEG_LT; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC NUM_RING;

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (is_imp o concl))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for gcc12_O2,   *)
(* with the regions of the stack frame and the stack guard, which the code   *)
(* does not access.                                                          *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e r a guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,352; a,512; word_sub stackpointer (word 48),48] /\
       ALLPAIRS nonoverlapping
        [r,352; word_sub stackpointer (word 48),48]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem_poly_compress_d11) /\
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
                           (word_sub stackpointer (word 48)) returnaddress /\
                    memaccess_inbounds e2
                     [a,512; r,352; word_sub stackpointer (word 48),48;
                      word(pc + got_stack_chk_guard),8; guard,8]
                     [r,352; word_sub stackpointer (word 48),48]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE [memory :> bytes(r,352);
                        memory :> bytes(word_sub stackpointer (word 48),48)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (guard:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a r guard pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 32
            (\i. f_ev_loop a r guard pc stackpointer returnaddress i))
          (f_ev_prol a r guard pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_compress_d11_loop1`
   `pc + mlkem_poly_compress_d11_loop1_exit`
    `\i s. read X8 s = word(16 * i) /\
           read X10 s = word_add a (word 14) /\
           read X11 s = word_add (word_add r (word(11 * i))) (word 5) /\
           read X30 s = returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_EXEC (1--7) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_COMPRESS_D11_CLANG17_O3_EXEC (1--58) THEN
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
  REWRITE_TAC[COMPRESS_D11_EVENT_ADDR] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
