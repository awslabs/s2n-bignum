(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 5 bits per coefficient.                *)
(* This is the code for mlkem_poly_decompress_d5 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). It is verified in the whole image (see           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2de0. The    *)
(* constant vector of 16s that it uses for the rounding is at 0x8020 in the  *)
(* image. It saves three registers on the stack, so it is verified directly  *)
(* as a subroutine, with that part of the stack.                             *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2de0: push   r12
    2de2: mov    rdx,rsi
    2de5: mov    rcx,rdi
    2de8: lea    rsi,[rsi+0xa0]
    2def: push   rbp
    2df0: pxor   xmm4,xmm4
    2df4: pxor   xmm2,xmm2
    2df8: movq   xmm3,QWORD PTR [rip+0x5220]
    2e00: push   rbx
    2e01: nop    DWORD PTR [rax+0x0]
    2e08: movzx  edi,BYTE PTR [rdx]
    2e0b: movzx  r10d,BYTE PTR [rdx+0x1]
    2e10: movzx  r11d,BYTE PTR [rdx+0x2]
    2e15: movzx  ebx,BYTE PTR [rdx+0x3]
    2e19: mov    r9d,edi
    2e1c: lea    r8d,[r10*8+0x0]
    2e24: movzx  eax,BYTE PTR [rdx+0x4]
    2e28: and    edi,0x1f
    2e2b: shr    r9b,0x5
    2e2f: lea    ebp,[r11+r11*1]
    2e33: shr    r11b,0x4
    2e37: or     r8d,r9d
    2e3a: mov    r9d,r10d
    2e3d: shr    r10b,0x7
    2e41: lea    r12d,[rax*4+0x0]
    2e49: shr    al,0x3
    2e4c: or     r10d,ebp
    2e4f: mov    ebp,ebx
    2e51: shr    r9b,0x2
    2e55: shl    ebp,0x4
    2e58: movzx  eax,al
    2e5b: and    r10d,0x1f
    2e5f: and    r9d,0x1f
    2e63: or     r11d,ebp
    2e66: mov    ebp,ebx
    2e68: shr    bl,0x6
    2e6b: and    r8d,0x1f
    2e6f: shl    rax,0x8
    2e73: or     ebx,r12d
    2e76: shr    bpl,1
    2e79: and    r11d,0x1f
    2e7d: and    ebx,0x1f
    2e80: and    ebp,0x1f
    2e83: or     rax,rbx
    2e86: shl    rax,0x8
    2e8a: or     rax,rbp
    2e8d: shl    rax,0x8
    2e91: or     rax,r11
    2e94: shl    rax,0x8
    2e98: or     rax,r10
    2e9b: shl    rax,0x8
    2e9f: or     rax,r9
    2ea2: shl    rax,0x8
    2ea6: or     rax,r8
    2ea9: shl    rax,0x8
    2ead: or     rax,rdi
    2eb0: add    rdx,0x5
    2eb4: add    rcx,0x10
    2eb8: movq   xmm0,rax
    2ebd: movdqa xmm6,xmm0
    2ec1: punpcklbwxmm0,xmm4
    2ec5: punpcklbwxmm6,xmm4
    2ec9: pshufd xmm0,xmm0,0x4e
    2ece: movdqa xmm5,xmm6
    2ed2: punpcklwdxmm6,xmm2
    2ed6: movdqa xmm7,xmm0
    2eda: punpcklwdxmm5,xmm2
    2ede: pshufd xmm6,xmm6,0x4e
    2ee3: punpcklwdxmm7,xmm2
    2ee7: movdqa xmm1,xmm5
    2eeb: punpcklwdxmm0,xmm2
    2eef: pslld  xmm1,0x1
    2ef4: pshufd xmm0,xmm0,0x4e
    2ef9: paddd  xmm1,xmm5
    2efd: pslld  xmm1,0x2
    2f02: paddd  xmm1,xmm5
    2f06: paddd  xmm5,xmm3
    2f0a: pslld  xmm1,0x8
    2f0f: paddd  xmm1,xmm5
    2f13: movdqa xmm5,xmm6
    2f17: pslld  xmm5,0x1
    2f1c: paddd  xmm5,xmm6
    2f20: psrld  xmm1,0x5
    2f25: pslld  xmm5,0x2
    2f2a: paddd  xmm5,xmm6
    2f2e: paddd  xmm6,xmm3
    2f32: pslld  xmm5,0x8
    2f37: paddd  xmm5,xmm6
    2f3b: movdqa xmm6,xmm1
    2f3f: psrld  xmm5,0x5
    2f44: punpcklwdxmm6,xmm5
    2f48: punpcklwdxmm1,xmm5
    2f4c: movdqa xmm5,xmm0
    2f50: pshufd xmm6,xmm6,0x4e
    2f55: pslld  xmm5,0x1
    2f5a: punpcklwdxmm1,xmm6
    2f5e: paddd  xmm5,xmm0
    2f62: movq   QWORD PTR [rcx-0x10],xmm1
    2f67: movdqa xmm1,xmm7
    2f6b: pslld  xmm1,0x1
    2f70: paddd  xmm1,xmm7
    2f74: pslld  xmm5,0x2
    2f79: paddd  xmm5,xmm0
    2f7d: paddd  xmm0,xmm3
    2f81: pslld  xmm1,0x2
    2f86: paddd  xmm1,xmm7
    2f8a: paddd  xmm7,xmm3
    2f8e: pslld  xmm5,0x8
    2f93: paddd  xmm0,xmm5
    2f97: pslld  xmm1,0x8
    2f9c: paddd  xmm1,xmm7
    2fa0: psrld  xmm0,0x5
    2fa5: psrld  xmm1,0x5
    2faa: movdqa xmm5,xmm1
    2fae: punpcklwdxmm1,xmm0
    2fb2: punpcklwdxmm5,xmm0
    2fb6: pshufd xmm5,xmm5,0x4e
    2fbb: punpcklwdxmm1,xmm5
    2fbf: movq   QWORD PTR [rcx-0x8],xmm1
    2fc4: cmp    rdx,rsi
    2fc7: jne    2e08 <mlkem_poly_decompress_d5+0x28>
    2fcd: pop    rbx
    2fce: pop    rbp
    2fcf: pop    r12
    2fd1: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2de0,0x2fd2];;

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
(* Correctness proof. As for mlkem_decompress 5 in common/fips203.ml, the    *)
(* result for a 5-bit field y is the integer closest to 3329 * y / 32,       *)
(* rounding up on ties, i.e. (3329 * y + 16) DIV 32.                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a n pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,512))
            [(word pc,0x82a0); (a,160);
             (word_sub stackpointer (word 24),32)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 24),32))
            [(word pc,0x82a0); (a,160)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x2de0) /\
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

  ENSURES_WHILE_UP_TAC `32` `pc + 0x2e08` `pc + 0x2fc4`
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
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE 0x2e00 0x8020 64)) THEN
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
               [word pc,0x82a0; a,160; word_sub stackpointer (word 24),32] /\
           ALL (nonoverlapping (word_sub stackpointer (word 24),32))
               [word pc,0x82a0; a,160]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x2de0) /\
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
                          [a,160; r,512; word (pc + 0x8020),8;
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

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x2e08` `pc + 0x2fcd`
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
