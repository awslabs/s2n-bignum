(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 5 bits per coefficient. This is the    *)
(* code for mlkem_poly_decompress_d5 from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see libmlkem.ml). The constant vector  *)
(* of 16s that it uses for the rounding is in the image. It saves three      *)
(* registers on the stack, so it is verified directly as a subroutine, with  *)
(* that part of the stack.                                                   *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d5:
       +0x0: push   r12
       +0x2: mov    rdx,rsi
       +0x5: mov    rcx,rdi
       +0x8: lea    rsi,[rsi+0xa0]
       +0xf: push   rbp
      +0x10: pxor   xmm4,xmm4
      +0x14: pxor   xmm2,xmm2
      +0x18: movq   xmm3,QWORD PTR [rip+0x5220]
      +0x20: push   rbx
      +0x21: nop    DWORD PTR [rax+0x0]
      +0x28: movzx  edi,BYTE PTR [rdx]
      +0x2b: movzx  r10d,BYTE PTR [rdx+0x1]
      +0x30: movzx  r11d,BYTE PTR [rdx+0x2]
      +0x35: movzx  ebx,BYTE PTR [rdx+0x3]
      +0x39: mov    r9d,edi
      +0x3c: lea    r8d,[r10*8+0x0]
      +0x44: movzx  eax,BYTE PTR [rdx+0x4]
      +0x48: and    edi,0x1f
      +0x4b: shr    r9b,0x5
      +0x4f: lea    ebp,[r11+r11*1]
      +0x53: shr    r11b,0x4
      +0x57: or     r8d,r9d
      +0x5a: mov    r9d,r10d
      +0x5d: shr    r10b,0x7
      +0x61: lea    r12d,[rax*4+0x0]
      +0x69: shr    al,0x3
      +0x6c: or     r10d,ebp
      +0x6f: mov    ebp,ebx
      +0x71: shr    r9b,0x2
      +0x75: shl    ebp,0x4
      +0x78: movzx  eax,al
      +0x7b: and    r10d,0x1f
      +0x7f: and    r9d,0x1f
      +0x83: or     r11d,ebp
      +0x86: mov    ebp,ebx
      +0x88: shr    bl,0x6
      +0x8b: and    r8d,0x1f
      +0x8f: shl    rax,0x8
      +0x93: or     ebx,r12d
      +0x96: shr    bpl,1
      +0x99: and    r11d,0x1f
      +0x9d: and    ebx,0x1f
      +0xa0: and    ebp,0x1f
      +0xa3: or     rax,rbx
      +0xa6: shl    rax,0x8
      +0xaa: or     rax,rbp
      +0xad: shl    rax,0x8
      +0xb1: or     rax,r11
      +0xb4: shl    rax,0x8
      +0xb8: or     rax,r10
      +0xbb: shl    rax,0x8
      +0xbf: or     rax,r9
      +0xc2: shl    rax,0x8
      +0xc6: or     rax,r8
      +0xc9: shl    rax,0x8
      +0xcd: or     rax,rdi
      +0xd0: add    rdx,0x5
      +0xd4: add    rcx,0x10
      +0xd8: movq   xmm0,rax
      +0xdd: movdqa xmm6,xmm0
      +0xe1: punpcklbw xmm0,xmm4
      +0xe5: punpcklbw xmm6,xmm4
      +0xe9: pshufd xmm0,xmm0,0x4e
      +0xee: movdqa xmm5,xmm6
      +0xf2: punpcklwd xmm6,xmm2
      +0xf6: movdqa xmm7,xmm0
      +0xfa: punpcklwd xmm5,xmm2
      +0xfe: pshufd xmm6,xmm6,0x4e
     +0x103: punpcklwd xmm7,xmm2
     +0x107: movdqa xmm1,xmm5
     +0x10b: punpcklwd xmm0,xmm2
     +0x10f: pslld  xmm1,0x1
     +0x114: pshufd xmm0,xmm0,0x4e
     +0x119: paddd  xmm1,xmm5
     +0x11d: pslld  xmm1,0x2
     +0x122: paddd  xmm1,xmm5
     +0x126: paddd  xmm5,xmm3
     +0x12a: pslld  xmm1,0x8
     +0x12f: paddd  xmm1,xmm5
     +0x133: movdqa xmm5,xmm6
     +0x137: pslld  xmm5,0x1
     +0x13c: paddd  xmm5,xmm6
     +0x140: psrld  xmm1,0x5
     +0x145: pslld  xmm5,0x2
     +0x14a: paddd  xmm5,xmm6
     +0x14e: paddd  xmm6,xmm3
     +0x152: pslld  xmm5,0x8
     +0x157: paddd  xmm5,xmm6
     +0x15b: movdqa xmm6,xmm1
     +0x15f: psrld  xmm5,0x5
     +0x164: punpcklwd xmm6,xmm5
     +0x168: punpcklwd xmm1,xmm5
     +0x16c: movdqa xmm5,xmm0
     +0x170: pshufd xmm6,xmm6,0x4e
     +0x175: pslld  xmm5,0x1
     +0x17a: punpcklwd xmm1,xmm6
     +0x17e: paddd  xmm5,xmm0
     +0x182: movq   QWORD PTR [rcx-0x10],xmm1
     +0x187: movdqa xmm1,xmm7
     +0x18b: pslld  xmm1,0x1
     +0x190: paddd  xmm1,xmm7
     +0x194: pslld  xmm5,0x2
     +0x199: paddd  xmm5,xmm0
     +0x19d: paddd  xmm0,xmm3
     +0x1a1: pslld  xmm1,0x2
     +0x1a6: paddd  xmm1,xmm7
     +0x1aa: paddd  xmm7,xmm3
     +0x1ae: pslld  xmm5,0x8
     +0x1b3: paddd  xmm0,xmm5
     +0x1b7: pslld  xmm1,0x8
     +0x1bc: paddd  xmm1,xmm7
     +0x1c0: psrld  xmm0,0x5
     +0x1c5: psrld  xmm1,0x5
     +0x1ca: movdqa xmm5,xmm1
     +0x1ce: punpcklwd xmm1,xmm0
     +0x1d2: punpcklwd xmm5,xmm0
     +0x1d6: pshufd xmm5,xmm5,0x4e
     +0x1db: punpcklwd xmm1,xmm5
     +0x1df: movq   QWORD PTR [rcx-0x8],xmm1
     +0x1e4: cmp    rdx,rsi
     +0x1e7: jne    <mlkem_poly_decompress_d5+0x28>
     +0x1ed: pop    rbx
     +0x1ee: pop    rbp
     +0x1ef: pop    r12
     +0x1f1: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_decompress_d5"];;

(* ------------------------------------------------------------------------- *)
(* The five bytes for eight coefficients, as parts of a 40-bit word.         *)
(* ------------------------------------------------------------------------- *)

let D5_BYTES = prove
 (`!a n i s j.
        read (memory :> bytes(a,160)) s = n /\ i < 32 /\ j < 5
        ==> read (memory :> bytes8(word_add a (word(5 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (40 * i)):40 word) (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `160`; `n:num`; `5 * i + j`; `s:x86state`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (5 * i + j) = 40 * i + 8 * j`]);;

(* ------------------------------------------------------------------------- *)
(* The computation for each coefficient, with its 5-bit field f in the 40    *)
(* bits, multiplying by 3329 with shifts and additions, and the field as     *)
(* part of the number for the input bytes.                                   *)
(* ------------------------------------------------------------------------- *)

let D5_LANE = prove
 (`!f:5 word.
     word_subword
      (word_ushr
        (word_add
          (word_shl (word_add (word_shl (word_add (word_shl
             (word_zx f:int32) 1) (word_zx f)) 2) (word_zx f)) 8)
          (word_add (word_zx f) (word 16))) 5) (0,16):int16 =
     word((3329 * val f + 16) DIV 32)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_USHR; VAL_WORD_ADD;
              VAL_WORD_SHL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1] THEN
  MP_TAC(ISPEC `f:5 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:5 word)`,`v:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let D5_FIELD = prove
 (`!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (40 * i)):40 word)
                          (5 * k,5):5 word) =
         (n DIV 2 EXP (5 * (8 * i + k))) MOD 32`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 5 5 = 5`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 8 ==> 5 * k + 5 <= 40`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `32 = 2 EXP 5`] THEN
  REWRITE_TAC[ARITH_RULE `40 * i + 5 * k = 5 * (8 * i + k)`]);;

(*** The stored coefficient k, from its lane of one of the two 64-bit
 *** stores, using the bit-level form of the computation of its 5-bit field
 ***)

let D5_LANE_RULE k th =
  let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV
     [WORD_VAL_MOD_256; WORD_VAL_MOD_65536] THENC SIMD_SIMPLIFY_CONV [])) th in
  let v = rand(concl th1) in
  let f = subst [mk_small_numeral (5 * k),`j:num`]
                `word_subword (w:40 word) (j,5):5 word` in
  let lth = SPEC f D5_LANE in
  let bth = BITBLAST_RULE (mk_eq(v,lhs(concl lth))) in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                      NUM_REDUCE_CONV))
   (TRANS th1 (TRANS bth lth));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 5 in                           *)
(* common/fips203/fips203.ml, the result for a 5-bit field y is the integer  *)
(* closest to 3329 * y / 32, rounding up on ties, i.e.                       *)
(* (3329 * y + 16) DIV 32.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a n pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,512))
            [(word pc,libmlkem_size); (a,160);
             (word_sub stackpointer (word 24),32)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),32))
            [(word pc,libmlkem_size); (a,160)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_poly_decompress_d5) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,160)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (5 * i)) MOD 2 EXP 5 +
                                16) DIV 32))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer
                                                  (word 24),24)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 24 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + mlkem_poly_decompress_d5_loop1` `pc + mlkem_poly_decompress_d5_loop1_test`
   `\i s. read RDX s = word_add a (word(5 * i)) /\
          read RCX s = word_add r (word(16 * i)) /\
          read RSI s = word_add a (word 160) /\
          read XMM3 s = word 0x00000000000000000000001000000010 /\
          read XMM4 s = word 0 /\
          read XMM2 s = word 0 /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          returnaddress /\
          read (memory :> bytes(a,160)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (5 * j)) MOD 2 EXP 5 + 16)
                        DIV 32))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the registers, with the vector of        ***)
    (*** constants from the image                                        ***)

    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE (layout "mlkem_poly_decompress_d5" + 0x20) (layout "mlkem_poly_decompress_d5_consts") 64)) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[XMM2; XMM3; XMM4; READ_ZEROTOP_128] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[];

    (*** The loop body, for five bytes and eight coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
    GHOST_INTRO_TAC `ymm7_init:int256` `read YMM7` THEN
    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top2" `YMM2` THEN
    XMM_EXISTSTOP_TAC "top3" `YMM3` THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    MAP_EVERY (fun j ->
      MP_TAC(REWRITE_RULE[ADD_CLAUSES]
       (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
         (SPECL [`a:int64`; `n:num`; `i:num`; `s0:x86state`;
                 mk_small_numeral j] D5_BYTES))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) (0--4) THEN
    ABBREV_TAC `w:40 word = word(n DIV 2 EXP (40 * i))` THEN
    MAP_EVERY (fun k ->
      X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--109) THEN
    FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match []
        `read (memory :> bytes64 (word_add (word_add r (word (16 * i)))
                                           (word 8))) s = x`) o concl)) THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC
      (map2 D5_LANE_RULE (4--7) (CONJUNCTS th))) THEN
    FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match []
        `read (memory :> bytes64 (word_add r (word (16 * i)))) s = x`) o
             concl)) THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC
      (map2 D5_LANE_RULE (0--3) (CONJUNCTS th))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[XMM2; XMM3; XMM4; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
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
    MAP_EVERY (fun k ->
      MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
       (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D5_FIELD)
           (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                          (mk_small_numeral k) `8`))))) THEN
      DISCH_THEN SUBST1_TAC) (0--7) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word (5 * i)))
                     (word_add a (word 160)):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 5 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit, restoring the registers, and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (1--2) THEN
    PTR_DECIDE_RIP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (3--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,libmlkem_size; a,160; word_sub stackpointer (word 24),32] /\
           ALL (nonoverlapping (word_sub stackpointer (word 24),32))
               [word pc,libmlkem_size; a,160]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_decompress_d5) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc
                                (word_sub stackpointer (word 24))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,160; r,512; word (pc + mlkem_poly_decompress_d5_consts),8;
                           word_sub stackpointer (word 24),32]
                          [r,512; word_sub stackpointer (word 24),24]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512);
                           memory :> bytes(word_sub stackpointer (word 24),
                                           24)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 32
            (\i. f_ev_loop a r pc stackpointer returnaddress i))
          (f_ev_prol a r pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `a:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 24 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_decompress_d5_loop1` `pc + mlkem_poly_decompress_d5_loop1_exit`
   `\i s. read RDX s = word_add a (word(5 * i)) /\
          read RCX s = word_add r (word(16 * i)) /\
          read RSI s = word_add a (word 160) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (1--10) THEN
    REWRITE_TAC[MULT_0; WORD_ADD_0; WORD_VAL_ADD_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (1--4) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (1--111) THEN
  SUBGOAL_THEN
   `~(val(word_add (word_add a (word (5 * i))) (word 5):int64) =
      val(word_add a (word 160):int64)) <=> i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 5 * i + 5 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun _ -> CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`;
                ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) (1--2) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
