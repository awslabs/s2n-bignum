(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 11 bits per coefficient.               *)
(* This is the code for mlkem_poly_decompress_d11 from mlkem-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). It is verified in the whole image (see           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2fe0. The    *)
(* constant vectors of 3329s and 1024s that it uses are at 0x8050 and 0x8060 *)
(* in the image. It saves four registers on the stack, so it is verified     *)
(* directly as a subroutine, with that part of the stack.                    *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2fe0: movdqa xmm4,XMMWORD PTR [rip+0x5068]
    2fe8: movdqa xmm3,XMMWORD PTR [rip+0x5070]
    2ff0: push   r13
    2ff2: push   r12
    2ff4: push   rbp
    2ff5: lea    rbp,[rsi+0x160]
    2ffc: push   rbx
    2ffd: mov    rbx,rdi
    3000: mov    rdi,rsi
    3003: nop    DWORD PTR [rax+rax*1+0x0]
    3008: movzx  r10d,BYTE PTR [rdi+0x1]
    300d: movzx  r8d,BYTE PTR [rdi+0x2]
    3012: movzx  r9d,BYTE PTR [rdi+0x4]
    3017: movzx  r13d,BYTE PTR [rdi+0x3]
    301c: shr    r10b,0x3
    3020: mov    r11d,r8d
    3023: shl    r8d,0x5
    3027: movzx  eax,BYTE PTR [rdi+0x5]
    302b: movzx  r10d,r10b
    302f: shl    r13d,0x2
    3033: movzx  r12d,BYTE PTR [rdi+0x6]
    3038: movzx  ecx,WORD PTR [rdi]
    303b: or     r10d,r8d
    303e: mov    r8d,r9d
    3041: shr    r11b,0x6
    3045: movzx  edx,BYTE PTR [rdi+0x8]
    3049: shl    r8d,0xa
    304d: movzx  r11d,r11b
    3051: shr    r9b,1
    3054: movzx  esi,BYTE PTR [rdi+0x9]
    3058: or     r8d,r13d
    305b: movzx  r9d,r9b
    305f: movzx  r13d,BYTE PTR [rdi+0x7]
    3064: and    cx,0x7ff
    3069: or     r8d,r11d
    306c: movzx  r11d,al
    3070: shr    al,0x4
    3073: and    r10w,0x7ff
    3079: shl    r11d,0x7
    307d: movzx  eax,al
    3080: add    r13d,r13d
    3083: and    r8w,0x7ff
    3089: or     r9d,r11d
    308c: movd   xmm1,ecx
    3090: movd   xmm5,r8d
    3095: movzx  r11d,r12b
    3099: shl    r11d,0x4
    309d: shr    r12b,0x7
    30a1: and    r9w,0x7ff
    30a7: pinsrw xmm1,r10d,0x1
    30ad: or     eax,r11d
    30b0: mov    r11d,edx
    30b3: movzx  r12d,r12b
    30b7: shr    dl,0x2
    30ba: shl    r11d,0x9
    30be: movzx  edx,dl
    30c1: and    ax,0x7ff
    30c5: or     r11d,r13d
    30c8: movd   xmm0,eax
    30cc: pinsrw xmm5,r9d,0x1
    30d2: or     r11d,r12d
    30d5: movzx  r12d,sil
    30d9: shr    sil,0x5
    30dd: punpckldq xmm1,xmm5
    30e1: shl    r12d,0x6
    30e5: movzx  esi,sil
    30e9: and    r11w,0x7ff
    30ef: or     edx,r12d
    30f2: movzx  r12d,BYTE PTR [rdi+0xa]
    30f7: pinsrw xmm0,r11d,0x1
    30fd: and    dx,0x7ff
    3102: shl    r12d,0x3
    3106: movd   xmm2,edx
    310a: or     esi,r12d
    310d: add    rdi,0xb
    3111: add    rbx,0x10
    3115: pinsrw xmm2,esi,0x1
    311a: punpckldq xmm0,xmm2
    311e: movdqa xmm2,xmm4
    3122: punpcklqdq xmm1,xmm0
    3126: pmullw xmm2,xmm1
    312a: pmulhuw xmm1,xmm4
    312e: movdqa xmm0,xmm2
    3132: punpckhwd xmm2,xmm1
    3136: punpcklwd xmm0,xmm1
    313a: movdqa xmm1,xmm2
    313e: paddd  xmm0,xmm3
    3142: paddd  xmm1,xmm3
    3146: psrld  xmm1,0xb
    314b: psrld  xmm0,0xb
    3150: movdqa xmm2,xmm0
    3154: punpcklwd xmm0,xmm1
    3158: punpckhwd xmm2,xmm1
    315c: movdqa xmm1,xmm0
    3160: punpckhwd xmm1,xmm2
    3164: punpcklwd xmm0,xmm2
    3168: punpcklwd xmm0,xmm1
    316c: movaps XMMWORD PTR [rbx-0x10],xmm0
    3170: cmp    rbp,rdi
    3173: jne    3008 <mlkem_poly_decompress_d11+0x28>
    3179: pop    rbx
    317a: pop    rbp
    317b: pop    r12
    317d: pop    r13
    317f: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2fe0,0x3180];;

(* ------------------------------------------------------------------------- *)
(* The eleven bytes for eight coefficients, as parts of an 88-bit word.      *)
(* ------------------------------------------------------------------------- *)

let D11_BYTES = prove
 (`!a n i s j.
        read (memory :> bytes(a,352)) s = n /\ i < 32 /\ j < 11
        ==> read (memory :> bytes8(word_add a (word(11 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (88 * i)):88 word) (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `352`; `n:num`; `11 * i + j`; `s:x86state`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (11 * i + j) = 88 * i + 8 * j`]);;

let D11_HALF = prove
 (`!a n i s.
        read (memory :> bytes(a,352)) s = n /\ i < 32
        ==> read (memory :> bytes16(word_add a (word(11 * i)))) s =
            word_subword (word(n DIV 2 EXP (88 * i)):88 word) (0,16)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `352`; `n:num`; `11 * i`; `s:x86state`]
                READ_MEMORY_BYTES16_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EXP; DIV_1; ARITH_RULE `2 EXP 16 = 65536`] THEN
  REWRITE_TAC[ARITH_RULE `8 * 11 * i = 88 * i`]);;

(* ------------------------------------------------------------------------- *)
(* The computation for each coefficient, with its 11-bit field f in the 88   *)
(* bits, and the field as part of the number for the input bytes. The        *)
(* products by 3329 are computed with PMULLW and PMULHUW, giving their low   *)
(* and high halves, which are put together as 32-bit products.               *)
(* ------------------------------------------------------------------------- *)

let D11D_LANE = prove
 (`!f:11 word.
     word_subword
      (word_ushr
        (word_add
          (word_mul (word_zx (word_zx f:int16):int32) (word 3329))
          (word 1024)) 11) (0,16):int16 =
     word((3329 * val f + 1024) DIV 2048)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_USHR; VAL_WORD_ADD;
              VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1] THEN
  MP_TAC(ISPEC `f:11 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:11 word)`,`v:num`) THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v MOD 65536 = v /\ v MOD 4294967296 = v`
   (fun th -> REWRITE_TAC[th])
  THENL [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `v < 2048 ==> v * 3329 < 4294967296 /\ v * 3329 + 1024 < 4294967296`] THEN
  SUBGOAL_THEN `(v * 3329 + 1024) DIV 2048 < 65536 /\
                (3329 * v + 1024) DIV 2048 < 65536`
   (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;

let D11D_FIELD = prove
 (`!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (88 * i)):88 word)
                          (11 * k,11):11 word) =
         (n DIV 2 EXP (11 * (8 * i + k))) MOD 2048`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 11 11 = 11`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 8 ==> 11 * k + 11 <= 88`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2048 = 2 EXP 11`] THEN
  REWRITE_TAC[ARITH_RULE `88 * i + 11 * k = 11 * (8 * i + k)`]);;

let WORD_JOIN_MULHU_MULLO = prove
 (`!x y:int16.
        word_join (word_subword (word_mul (word_zx x:int32) (word_zx y:int32))
                                (16,16):int16)
                  (word_mul x y:int16):int32 =
        word_mul (word_zx x) (word_zx y)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `word_mul x y:int16 =
    word_subword (word_mul (word_zx x:int32) (word_zx y:int32)) (0,16)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
                DIMINDEX_16; DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
    MP_TAC(ISPEC `x:int16` VAL_BOUND) THEN
    MP_TAC(ISPEC `y:int16` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(x:int16) MOD 4294967296 = val x /\
                  val(y:int16) MOD 4294967296 = val y`
     (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `4294967296 = 65536 * 65536`; MOD_MOD];
    SPEC_TAC(`word_mul (word_zx x:int32) (word_zx y:int32)`,`p:int32`) THEN
    BITBLAST_TAC]);;

let WORD_JOIN_MULHU_MULLO_3329 = prove
 (`!x:int16.
        word_join (word_subword (word_mul (word_zx x:int32) (word 3329))
                                (16,16):int16)
                  (word_mul (word 3329) x:int16):int32 =
        word_mul (word_zx x) (word 3329)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`x:int16`; `word 3329:int16`] WORD_JOIN_MULHU_MULLO) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_MUL_SYM]);;

(*** The stored coefficient k, from its lane of the 128-bit store, with the
 *** extraction of its 11-bit field checked by bit-blasting
 ***)

let D11_LANE_RULE k th =
  let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_VAL_MOD_256;
                                             WORD_VAL_MOD_65536] THENC
                                SIMD_SIMPLIFY_CONV [] THENC
                                REWRITE_CONV[WORD_JOIN_MULHU_MULLO_3329]))
              th in
  let v = rand(concl th1) in
  let m = find_term (can (term_match []
            `word_mul (word_zx (t:int16):int32) (word 3329)`)) v in
  let t = rand(lhand m) in
  let f = subst [mk_small_numeral (11 * k),`j:num`]
                `word_subword (w:88 word) (j,11):11 word` in
  let tth = BITBLAST_RULE (mk_eq(t,mk_comb(`word_zx:11 word->int16`,f))) in
  let th2 = CONV_RULE(RAND_CONV(REWRITE_CONV[tth; D11D_LANE])) th1 in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                      NUM_REDUCE_CONV)) th2;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 11 in common/fips203.ml, the   *)
(* result for an 11-bit field y is the integer closest to 3329 * y / 2048,   *)
(* rounding up on ties, i.e. (3329 * y + 1024) DIV 2048. The result is       *)
(* written with aligned SSE stores, so the specification requires r to be    *)
(* aligned, as it is in mlkem-native.                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a n pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ aligned 16 r /\
        ALL (nonoverlapping (r,512))
            [(word pc,0x82a0); (a,352);
             (word_sub stackpointer (word 32),40)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),40))
            [(word pc,0x82a0); (a,352)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x2fe0) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,352)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (11 * i)) MOD 2 EXP 11 +
                                1024) DIV 2048))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer
                                                  (word 32),32)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x3008` `pc + 0x3170`
   `\i s. read RDI s = word_add a (word(11 * i)) /\
          read RBX s = word_add r (word(16 * i)) /\
          read RBP s = word_add a (word 352) /\
          read XMM4 s = word 0x0d010d010d010d010d010d010d010d01 /\
          read XMM3 s = word 0x00000400000004000000040000000400 /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
          returnaddress /\
          read (memory :> bytes(a,352)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (11 * j)) MOD 2 EXP 11 + 1024)
                        DIV 2048))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vectors of constants from the image,  ***)
    (*** and saving the registers                                       ***)

    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC 0x2fe8 0x8050 THEN
    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC 0x2ff0 0x8060 THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE 0x2fe8 0x8050 128)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE 0x2ff0 0x8060 128)) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[XMM3; XMM4; READ_ZEROTOP_128] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    CONJ_TAC THEN CONV_TAC WORD_BLAST;

    (*** The loop body, for eleven bytes and eight coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top3" `YMM3` THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    MAP_EVERY (fun j ->
      MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
       (SPECL [`a:int64`; `n:num`; `i:num`; `s0:x86state`;
               mk_small_numeral j] D11_BYTES)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) (1--10) THEN
    MP_TAC(SPECL [`a:int64`; `n:num`; `i:num`; `s0:x86state`] D11_HALF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC `w:88 word = word(n DIV 2 EXP (88 * i))` THEN
    SUBGOAL_THEN `aligned 16 (word_add r (word (16 * i)):int64)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC ALIGNED_WORD_ADD THEN
      ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    MAP_EVERY (fun k ->
      X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--88) THEN
    FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match []
        `read (memory :> bytes128 (word_add r (word (16 * i)))) s = x`) o
             concl)) THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC
      (map2 D11_LANE_RULE (0--7) (CONJUNCTS th))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[XMM3; XMM4; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
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
       (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D11D_FIELD)
           (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                          (mk_small_numeral k) `8`))))) THEN
      DISCH_THEN SUBST1_TAC) (0--7) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word 352))
                     (word_add a (word (11 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 11 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit, restoring the registers, and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (1--2) THEN
    PTR_DECIDE_RIP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (3--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\ aligned 16 r /\
           ALL (nonoverlapping (r,512))
               [word pc,0x82a0; a,352; word_sub stackpointer (word 32),40] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),40))
               [word pc,0x82a0; a,352]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x2fe0) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc
                                (word_sub stackpointer (word 32))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,352; r,512; word (pc + 0x8050),16;
                           word (pc + 0x8060),16;
                           word_sub stackpointer (word 32),40]
                          [r,512; word_sub stackpointer (word 32),32]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512);
                           memory :> bytes(word_sub stackpointer (word 32),
                                           32)])`,
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
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x3008` `pc + 0x3179`
   `\i s. read RDI s = word_add a (word(11 * i)) /\
          read RBX s = word_add r (word(16 * i)) /\
          read RBP s = word_add a (word 352) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
          returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC 0x2fe8 0x8050 THEN
    MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC 0x2ff0 0x8060 THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (1--10) THEN
    REWRITE_TAC[MULT_0; WORD_ADD_0; WORD_VAL_ADD_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (1--5) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `aligned 16 (word_add r (word (16 * i)):int64)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ALIGNED_WORD_ADD THEN
    ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_DECOMPRESS_D11_GCC12_O2_EXEC (1--90) THEN
  SUBGOAL_THEN
   `~(val(word_add a (word 352):int64) =
      val(word_add (word_add a (word (11 * i))) (word 11):int64)) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 11 * i + 11 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun _ -> CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`;
                ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) (1--2) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
