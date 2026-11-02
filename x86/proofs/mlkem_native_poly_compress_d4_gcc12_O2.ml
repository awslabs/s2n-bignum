(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 4 bits per coefficient.                    *)
(* This is the code for mlkem_poly_compress_d4 from mlkem-native's portable  *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mlkem_native/README.md). It is verified in the whole image (see           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2460. The    *)
(* constant vectors that it uses, of 2^27s for the rounding and of masks of  *)
(* the low bytes of 16-bit lanes, are at 0x8000 and 0x8008 in the image.     *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2460: movq   xmm3,QWORD PTR [rip+0x5b98]
    2468: mov    rdx,rsi
    246b: mov    rcx,rdi
    246e: lea    rsi,[rsi+0x200]
    2475: movq   xmm5,QWORD PTR [rip+0x5b8b]
    247d: pxor   xmm4,xmm4
    2481: nop    DWORD PTR [rax+0x0]
    2488: movq   xmm1,QWORD PTR [rdx]
    248c: movdqa xmm6,xmm4
    2490: movq   xmm0,QWORD PTR [rdx+0x8]
    2495: movdqa xmm8,xmm4
    249a: add    rdx,0x10
    249e: add    rcx,0x4
    24a2: pcmpgtw xmm6,xmm1
    24a6: pcmpgtw xmm8,xmm0
    24ab: movdqa xmm7,xmm1
    24af: punpcklwd xmm1,xmm6
    24b3: punpcklwd xmm7,xmm6
    24b7: movdqa xmm6,xmm0
    24bb: pshufd xmm1,xmm1,0x4e
    24c0: punpcklwd xmm6,xmm8
    24c5: movdqa xmm2,xmm1
    24c9: movdqa xmm1,xmm0
    24cd: movdqa xmm0,xmm7
    24d1: pslld  xmm0,0x6
    24d6: punpcklwd xmm1,xmm8
    24db: psubd  xmm0,xmm7
    24df: pshufd xmm1,xmm1,0x4e
    24e4: pslld  xmm0,0x8
    24e9: psubd  xmm0,xmm7
    24ed: movdqa xmm7,xmm2
    24f1: pslld  xmm7,0x6
    24f6: psubd  xmm7,xmm2
    24fa: pslld  xmm7,0x8
    24ff: psubd  xmm7,xmm2
    2503: movdqa xmm2,xmm6
    2507: pslld  xmm2,0x6
    250c: psubd  xmm2,xmm6
    2510: pslld  xmm2,0x8
    2515: psubd  xmm2,xmm6
    2519: movdqa xmm6,xmm1
    251d: pslld  xmm6,0x6
    2522: psubd  xmm6,xmm1
    2526: pslld  xmm6,0x8
    252b: psubd  xmm6,xmm1
    252f: movdqa xmm1,xmm0
    2533: pslld  xmm1,0x2
    2538: paddd  xmm1,xmm0
    253c: movdqa xmm0,xmm7
    2540: pslld  xmm0,0x2
    2545: paddd  xmm0,xmm7
    2549: pslld  xmm1,0x4
    254e: paddd  xmm1,xmm3
    2552: pslld  xmm0,0x4
    2557: paddd  xmm0,xmm3
    255b: psrld  xmm1,0x1c
    2560: movdqa xmm7,xmm1
    2564: psrld  xmm0,0x1c
    2569: punpcklwd xmm7,xmm0
    256d: punpcklwd xmm1,xmm0
    2571: movdqa xmm0,xmm2
    2575: pslld  xmm0,0x2
    257a: pshufd xmm7,xmm7,0x4e
    257f: paddd  xmm0,xmm2
    2583: movdqa xmm2,xmm6
    2587: punpcklwd xmm1,xmm7
    258b: pslld  xmm2,0x2
    2590: pand   xmm1,xmm5
    2594: paddd  xmm2,xmm6
    2598: movdqa xmm7,xmm1
    259c: pslld  xmm0,0x4
    25a1: paddd  xmm0,xmm3
    25a5: pslld  xmm2,0x4
    25aa: paddd  xmm2,xmm3
    25ae: psrld  xmm0,0x1c
    25b3: movdqa xmm6,xmm0
    25b7: psrld  xmm2,0x1c
    25bc: punpcklwd xmm6,xmm2
    25c0: punpcklwd xmm0,xmm2
    25c4: pshufd xmm6,xmm6,0x4e
    25c9: punpcklwd xmm0,xmm6
    25cd: pand   xmm0,xmm5
    25d1: packuswb xmm7,xmm0
    25d5: pshufd xmm7,xmm7,0x8
    25da: movq   rax,xmm7
    25df: mov    r8,rax
    25e2: mov    r9,rax
    25e5: mov    r10,rax
    25e8: mov    r11,rax
    25eb: shr    r8,0x18
    25ef: shr    r9,0x10
    25f3: movzx  edi,ah
    25f6: shl    r8d,0x4
    25fa: shr    r10,0x20
    25fe: shr    r11,0x38
    2602: or     r8d,r9d
    2605: mov    r9,rax
    2608: shl    edi,0x4
    260b: shr    r9,0x28
    260f: or     edi,eax
    2611: shr    rax,0x30
    2615: movzx  r8d,r8b
    2619: shl    r9d,0x4
    261d: movzx  edi,dil
    2621: or     r9d,r10d
    2624: mov    r10,r11
    2627: shl    r10d,0x4
    262b: movzx  r9d,r9b
    262f: or     eax,r10d
    2632: movzx  eax,al
    2635: shl    eax,0x8
    2638: or     eax,r9d
    263b: shl    eax,0x8
    263e: or     eax,r8d
    2641: shl    eax,0x8
    2644: or     eax,edi
    2646: mov    DWORD PTR [rcx-0x4],eax
    2649: cmp    rsi,rdx
    264c: jne    2488 <mlkem_poly_compress_d4+0x28>
    2652: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2460,0x2653];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 4 bits, as computed. Each coefficient *)
(* is sign-extended to 32 bits and multiplied by 1290160 with shifts,        *)
(* additions and subtractions, and the rounding constant 2^27 is added.      *)
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

let COMPRESS_D4_FIELD = prove
 (`!y:int16.
        val y < 3329
        ==> let x:int32 = word_join ((if word_igt (word 0) y
                                      then word 65535 else word 0):int16) y in
            let t = word_sub (word_shl (word_sub (word_shl x 6) x) 8) x in
            val(word_subword
                 (word_add (word_shl (word_add (word_shl t 2) t) 4)
                           (word 134217728))
                 (28,4):4 word) =
            ((32 * val y + 3329) DIV 6658) MOD 16`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[WORD_JOIN_SIGN_SMALL; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[WORD_SHL_MUL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_RULE
   `word_mul (word_add (word_mul (word_sub (word_mul (word_sub
      (word_mul x (word 64)) x) (word 256)) x) (word 4))
      (word_sub (word_mul (word_sub (word_mul x (word 64)) x) (word 256)) x))
      (word 16):int32 =
    word_mul x (word 1290160)`] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
              VAL_WORD; DIMINDEX_32; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`;
    ARITH_RULE `y < 3329 ==> y * 1290160 < 4294967296`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 268435456 * 16`; GSYM DIV_MOD] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ADD_SYM] THEN
  ASM_SIMP_TAC[COMPRESS_D4_ARITH]);;

(* ------------------------------------------------------------------------- *)
(* The packing of eight 4-bit values into four bytes.                        *)
(* ------------------------------------------------------------------------- *)

let BYTES_OF_NUM_4 = prove
 (`!n. n < 2 EXP 32
       ==> n MOD 256 + 256 * (n DIV 256) MOD 256 +
           65536 * (n DIV 65536) MOD 256 +
           16777216 * (n DIV 16777216) MOD 256 = n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(n DIV 16777216) MOD 256 = n DIV 16777216`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `n < 2 EXP 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 256`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 65536`; `256`] DIVISION) THEN
  REWRITE_TAC[DIV_DIV; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let VAL_JOIN_4X8 = prove
 (`!(u0:4 word) (u1:4 word) (u2:4 word) (u3:4 word)
    (u4:4 word) (u5:4 word) (u6:4 word) (u7:4 word).
     val(word_join u7 (word_join u6 (word_join u5 (word_join u4
          (word_join u3 (word_join u2 (word_join u1 u0:8 word):12 word):
           16 word):20 word):24 word):28 word):32 word) =
     val u0 + 16 * val u1 + 256 * val u2 + 4096 * val u3 +
     65536 * val u4 + 1048576 * val u5 + 16777216 * val u6 +
     268435456 * val u7`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`u0:4 word`; `u1:4 word`; `u2:4 word`; `u3:4 word`;
    `u4:4 word`; `u5:4 word`; `u6:4 word`; `u7:4 word`] THEN
  REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun k ->
    SPEC_TAC(mk_comb(`val:4 word->num`,mk_var("u"^string_of_int k,`:4 word`)),
             mk_var("n"^string_of_int k,`:num`))) (0--7) THEN
  REPEAT STRIP_TAC THEN REPEAT MOD_LT_ASM_TAC THEN ARITH_TAC);;

(*** The stored bytes as parts of the 32-bit join of the eight fields, with
 *** the computations for the coefficients as atoms for the bit-blasting
 ***)

let compress_d4_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let d4_xatoms =
  let tm = rand(concl(TOP_DEPTH_CONV let_CONV
   `let x:int32 = word_join ((if word_igt (word 0) (y:int16)
                              then word 65535 else word 0):int16) y in
    let t = word_sub (word_shl (word_sub (word_shl x 6) x) 8) x in
    word_add (word_shl (word_add (word_shl t 2) t) 4) (word 134217728)`)) in
  map (fun j -> vsubst [mk_comb(`x:num->int16`,j),`y:int16`] tm)
      compress_d4_indices;;

let d4_join =
  vsubst (zip d4_xatoms (map (fun k -> mk_var("w"^string_of_int k,`:int32`))
                             (0--7)))
  `word_join (word_subword (w7:int32) (28,4):4 word)
    (word_join (word_subword (w6:int32) (28,4):4 word)
     (word_join (word_subword (w5:int32) (28,4):4 word)
      (word_join (word_subword (w4:int32) (28,4):4 word)
       (word_join (word_subword (w3:int32) (28,4):4 word)
        (word_join (word_subword (w2:int32) (28,4):4 word)
         (word_join (word_subword (w1:int32) (28,4):4 word)
                    (word_subword (w0:int32) (28,4):4 word):8 word):
         12 word):16 word):20 word):24 word):28 word):32 word`;;

let D4_PACK_TAC =
  let rule m th =
    let v = rand(concl th) in
    let target = mk_comb(mk_comb(`word_subword:32 word->num#num->byte`,
                                 d4_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int32`) d4_xatoms in
    let eq = subst (zip gvs d4_xatoms) (mk_eq(v,target)) in
    let bth = INST (zip d4_xatoms gvs) (BITBLAST_RULE eq) in
    CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                        NUM_REDUCE_CONV)) (TRANS th bth) in
  W(fun (asl,w) ->
    let th4 = snd(find (fun (_,th) -> can (term_match []
      `read (memory :> bytes32 (word_add r (word (4 * i)))) s = x`)
      (concl th)) asl) in
    let bytes = map (CONV_RULE(RAND_CONV(REWRITE_CONV
                  [WORD_VAL_MOD_256; WORD_VAL_MOD_65536;
                   WORD_VAL_DIV_256_MOD_256] THENC
                  SIMD_SIMPLIFY_CONV [])))
                (CONJUNCTS(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th4)) in
    MAP_EVERY ASSUME_TAC (map2 rule (0--3) bytes));;

(* ------------------------------------------------------------------------- *)
(* The two loads of four coefficients, and the bytes of the result of the    *)
(* vector computation, moved to RAX after PACKUSWB.                          *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D4_LOADS_TAC =
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`a:int64`; `s0:x86state`; `x:num->int16`; k]
                 READ_MEMORY_BYTES64_JOIN_16) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < 32` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `8 * 2 * i = 16 * i`;
                ARITH_RULE `8 * (2 * i + 1) = 16 * i + 8`;
                ARITH_RULE `4 * 2 * i = 8 * i`;
                ARITH_RULE `4 * (2 * i + 1) = 8 * i + 4`;
                ARITH_RULE `(8 * i + 4) + 1 = 8 * i + 5`;
                ARITH_RULE `(8 * i + 4) + 2 = 8 * i + 6`;
                ARITH_RULE `(8 * i + 4) + 3 = 8 * i + 7`] THEN
    DISCH_TAC) [`2 * i`; `2 * i + 1`];;

let COMPRESS_D4_TIDY_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RAX s = x`) (concl th) &&
       can (find_term (fun t -> try fst(dest_const(rator t)) = "MIN"
                                with Failure _ -> false)) (concl th)
    then CONV_RULE(RAND_CONV(REWRITE_CONV[PACKUSWB_SAT_255] THENC
                             REWRITE_CONV[PACKUSWB_JOIN] THENC
                             SIMD_SIMPLIFY_CONV [])) th
    else th);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 4 in common/fips203.ml, the      *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 16 * x / 3329, rounding up on ties, modulo 16, i.e.                       *)
(* ((32 * x + 3329) DIV 6658) MOD 16, and as for mlkem_encode 4 the 4-bit    *)
(* values are put together little-endian. Like the C code, this relies on    *)
(* the coefficients being in [0,3329).                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_CORRECT = prove
 (`!r a x pc.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,128)) [(word pc,0x82a0); (a,512)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + 0x2460) /\
           C_ARGUMENTS [r; a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
      (\s. read RIP s = word (pc + 0x2652) /\
           ((!i. i < 256 ==> val(x i) < 3329)
            ==> read(memory :> bytes(r,128)) s =
                nsum {i | i < 256}
                     (\i. ((32 * val(x i) + 3329) DIV 6658) MOD 16 *
                          2 EXP (4 * i))))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,128)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop, over groups of 8 coefficients ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x2488` `pc + 0x2649`
   `\i s. read RDX s = word_add a (word(16 * i)) /\
          read RCX s = word_add r (word(4 * i)) /\
          read RSI s = word_add a (word 512) /\
          read XMM3 s = word 0x00000000000000000800000008000000 /\
          read XMM4 s = word 0 /\
          read XMM5 s = word 0x000000000000000000ff00ff00ff00ff /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          ((!j. j < 256 ==> val(x j) < 3329)
           ==> read(memory :> bytes(r,4 * i)) s =
               nsum {j | j < 8 * i}
                (\j. ((32 * val(x j) + 3329) DIV 6658) MOD 16 *
                     2 EXP (4 * j)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vectors of constants from the image ***)

    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE 0x2468 0x8000 64)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE 0x247d 0x8008 64)) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[XMM3; XMM4; XMM5; READ_ZEROTOP_128] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                NSUM_CLAUSES_NUMSEG_LT; READ_MEMORY_BYTES_TRIVIAL] THEN
    REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST;

    (*** The loop body, for eight coefficients and four bytes ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
    GHOST_INTRO_TAC `ymm7_init:int256` `read YMM7` THEN
    GHOST_INTRO_TAC `ymm8_init:int256` `read YMM8` THEN
    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top3" `YMM3` THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    XMM_EXISTSTOP_TAC "top5" `YMM5` THEN
    COMPRESS_D4_LOADS_TAC THEN
    MAP_EVERY (fun k ->
      X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--78) THEN
    COMPRESS_D4_TIDY_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (79--110) THEN

    (*** The new bytes as parts of the join of the 4-bit fields ***)

    D4_PACK_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[XMM3; XMM4; XMM5; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `4 * (i + 1) = (((4 * i + 1) + 1) + 1) + 1`] THEN
    REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN
    REWRITE_TAC[ARITH_RULE `(4 * i + 1) + 1 = 4 * i + 2`;
                ARITH_RULE `(4 * i + 2) + 1 = 4 * i + 3`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INST_TYPE [`:32`,`:M`; `:8`,`:N`] VAL_WORD_SUBWORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_1] THEN
    MP_TAC(SPEC (mk_comb(`val:32 word->num`,d4_join)) BYTES_OF_NUM_4) THEN
    MP_TAC(ISPEC d4_join VAL_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MP th)) THEN
    REWRITE_TAC[VAL_JOIN_4X8] THEN

    (*** The compression of each coefficient ***)

    MAP_EVERY (fun jt ->
      MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
        (SPEC (mk_comb(`x:num->int16`,jt)) COMPRESS_D4_FIELD)) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (can (term_match []
                `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o concl)) THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) compress_d4_indices THEN

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

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word 512))
                     (word_add a (word (16 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 16 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--2) THEN
    PTR_DECIDE_RIP_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (is_imp o concl))]);;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a x pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,128))
        [(word pc,0x82a0); (a,512); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + 0x2460) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [r; a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           ((!i. i < 256 ==> val(x i) < 3329)
            ==> read(memory :> bytes(r,128)) s =
                nsum {i | i < 256}
                     (\i. ((32 * val(x i) + 3329) DIV 6658) MOD 16 *
                          2 EXP (4 * i))))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,128)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SAFE = time prove
 (`exists f_events.
       forall e r a pc.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,128)) [word pc,0x82a0; a,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x2460) /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0x2652) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2
                          [a,512; r,128; word (pc + 0x8000),8;
                           word (pc + 0x8008),8]
                          [r,128]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,128)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num).
      APPEND
        (f_ev_epil a r pc)
        (APPEND
          (ENUMERATEL 32 (\i. f_ev_loop a r pc i))
          (f_ev_prol a r pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x2488` `pc + 0x2652`
    `\i s. read RDX s = word_add a (word(16 * i)) /\
           read RCX s = word_add r (word(4 * i)) /\
           read RSI s = word_add a (word 512)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--7) THEN
    REWRITE_TAC[MULT_0; WORD_ADD_0; WORD_VAL_ADD_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC (1--112) THEN
  SUBGOAL_THEN
   `~(val(word_add a (word 512):int64) =
      val(word_add (word_add a (word (16 * i))) (word 16):int64)) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 16 * i + 16 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun _ -> CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`;
                ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) (1--2) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,128))
               [word pc,0x82a0; a,512; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x2460) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [a,512; r,128; word (pc + 0x8000),8;
                           word (pc + 0x8008),8; stackpointer,8]
                          [r,128]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,128)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_IMAGE_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
