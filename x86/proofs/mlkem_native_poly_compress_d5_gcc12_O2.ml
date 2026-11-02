(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 5 bits per coefficient.                    *)
(* This is the code for mlkem_poly_compress_d5 from mlkem-native's portable  *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mlkem_native/README.md). It is verified in the whole image (see           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x28c0. The    *)
(* constant vectors that it uses, of 2^26s for the rounding and of masks of  *)
(* the low bytes of 16-bit lanes, are at 0x8018 and 0x8008 in the image. It  *)
(* saves two registers on the stack, so it is verified directly as a         *)
(* subroutine, with that part of the stack.                                  *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    28c0: push   rbp
    28c1: mov    rcx,rsi
    28c4: mov    rdx,rdi
    28c7: lea    rsi,[rdi+0xa0]
    28ce: movq   xmm2,QWORD PTR [rip+0x5742]
    28d6: push   rbx
    28d7: pxor   xmm3,xmm3
    28db: movq   xmm4,QWORD PTR [rip+0x5725]
    28e3: nop    DWORD PTR [rax+rax*1+0x0]
    28e8: movq   xmm0,QWORD PTR [rcx]
    28ec: movdqa xmm1,xmm3
    28f0: add    rdx,0x5
    28f4: add    rcx,0x10
    28f8: movq   xmm6,QWORD PTR [rcx-0x8]
    28fd: pcmpgtw xmm1,xmm0
    2901: movdqa xmm9,xmm0
    2906: movdqa xmm8,xmm6
    290b: punpcklwd xmm0,xmm1
    290f: punpcklwd xmm9,xmm1
    2914: pshufd xmm0,xmm0,0x4e
    2919: movdqa xmm10,xmm0
    291e: movdqa xmm0,xmm3
    2922: pcmpgtw xmm0,xmm6
    2926: movdqa xmm5,xmm10
    292b: pslld  xmm5,0x2
    2930: paddd  xmm5,xmm10
    2935: punpcklwd xmm8,xmm0
    293a: punpcklwd xmm6,xmm0
    293e: movdqa xmm0,xmm9
    2943: pslld  xmm0,0x2
    2948: pshufd xmm6,xmm6,0x4e
    294d: movdqa xmm11,xmm8
    2952: paddd  xmm0,xmm9
    2957: pslld  xmm11,0x2
    295d: movdqa xmm7,xmm6
    2961: paddd  xmm11,xmm8
    2966: pslld  xmm7,0x2
    296b: paddd  xmm7,xmm6
    296f: movdqa xmm1,xmm0
    2973: pslld  xmm1,0x6
    2978: psubd  xmm1,xmm0
    297c: movdqa xmm0,xmm5
    2980: pslld  xmm0,0x6
    2985: psubd  xmm0,xmm5
    2989: pslld  xmm1,0x6
    298e: psubd  xmm1,xmm9
    2993: pslld  xmm0,0x6
    2998: psubd  xmm0,xmm10
    299d: pslld  xmm1,0x6
    29a2: paddd  xmm1,xmm2
    29a6: pslld  xmm0,0x6
    29ab: paddd  xmm0,xmm2
    29af: psrld  xmm1,0x1b
    29b4: movdqa xmm5,xmm1
    29b8: psrld  xmm0,0x1b
    29bd: punpcklwd xmm5,xmm0
    29c1: punpcklwd xmm1,xmm0
    29c5: movdqa xmm0,xmm11
    29ca: pshufd xmm5,xmm5,0x4e
    29cf: pslld  xmm0,0x6
    29d4: punpcklwd xmm1,xmm5
    29d8: movdqa xmm5,xmm7
    29dc: psubd  xmm0,xmm11
    29e1: pslld  xmm5,0x6
    29e6: pand   xmm1,xmm4
    29ea: psubd  xmm5,xmm7
    29ee: movdqa xmm7,xmm1
    29f2: pslld  xmm0,0x6
    29f7: psubd  xmm0,xmm8
    29fc: pslld  xmm5,0x6
    2a01: psubd  xmm5,xmm6
    2a05: pslld  xmm0,0x6
    2a0a: paddd  xmm0,xmm2
    2a0e: pslld  xmm5,0x6
    2a13: paddd  xmm5,xmm2
    2a17: psrld  xmm0,0x1b
    2a1c: movdqa xmm6,xmm0
    2a20: psrld  xmm5,0x1b
    2a25: punpcklwd xmm6,xmm5
    2a29: punpcklwd xmm0,xmm5
    2a2d: pshufd xmm6,xmm6,0x4e
    2a32: punpcklwd xmm0,xmm6
    2a36: pand   xmm0,xmm4
    2a3a: packuswb xmm7,xmm0
    2a3e: pshufd xmm7,xmm7,0x8
    2a43: movq   rax,xmm7
    2a48: mov    rdi,rax
    2a4b: mov    rbp,rax
    2a4e: movzx  ebx,ah
    2a51: mov    r8,rax
    2a54: shr    rdi,0x18
    2a58: shr    rbp,0x10
    2a5c: mov    r11,rbx
    2a5f: mov    rbx,rax
    2a62: shl    ebp,0x2
    2a65: mov    r10d,edi
    2a68: shr    rbx,0x20
    2a6c: mov    r9,r11
    2a6f: shl    r10d,0x7
    2a73: shr    r11b,0x3
    2a77: shr    r8,0x30
    2a7b: or     r10d,ebp
    2a7e: shr    dil,1
    2a81: mov    rbp,rax
    2a84: shr    rbp,0x28
    2a88: or     r10d,r11d
    2a8b: mov    r11d,ebx
    2a8e: shr    bl,0x4
    2a91: shl    r11d,0x4
    2a95: add    ebp,ebp
    2a97: shl    r9d,0x5
    2a9b: movzx  r10d,r10b
    2a9f: or     r11d,edi
    2aa2: mov    edi,r8d
    2aa5: or     r9d,eax
    2aa8: shr    rax,0x38
    2aac: shl    edi,0x6
    2aaf: movzx  r11d,r11b
    2ab3: movzx  r9d,r9b
    2ab7: shr    r8b,0x2
    2abb: or     edi,ebp
    2abd: shl    eax,0x3
    2ac0: or     edi,ebx
    2ac2: or     r8d,eax
    2ac5: movzx  edi,dil
    2ac9: mov    BYTE PTR [rdx-0x1],r8b
    2acd: shl    edi,0x8
    2ad0: or     edi,r11d
    2ad3: shl    edi,0x8
    2ad6: or     edi,r10d
    2ad9: shl    edi,0x8
    2adc: or     edi,r9d
    2adf: mov    DWORD PTR [rdx-0x5],edi
    2ae2: cmp    rdx,rsi
    2ae5: jne    28e8 <mlkem_poly_compress_d5+0x28>
    2aeb: pop    rbx
    2aec: pop    rbp
    2aed: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x28c0,0x2aee];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 5 bits, as computed. Each coefficient *)
(* is sign-extended to 32 bits and multiplied by 1290176 with shifts,        *)
(* additions and subtractions, and the rounding constant 2^26 is added. As   *)
(* on AArch64, the result of the division is checked for each coefficient.   *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D5_ARITH = prove
 (`!v. v < 3329
       ==> (67108864 + v * 1290176) DIV 134217728 =
           (64 * v + 3329) DIV 6658`,
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let COMPRESS_D5_FIELD = prove
 (`!y:int16.
        val y < 3329
        ==> let x:int32 = word_join ((if word_igt (word 0) y
                                      then word 65535 else word 0):int16) y in
            val(word_subword
                 (word_add
                   (word_shl
                     (word_sub (word_shl (word_sub (word_shl
                       (word_add (word_shl x 2) x) 6)
                       (word_add (word_shl x 2) x)) 6) x) 6)
                   (word 67108864))
                 (27,5):5 word) =
            ((64 * val y + 3329) DIV 6658) MOD 32`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[WORD_JOIN_SIGN_SMALL; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[WORD_SHL_MUL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_RULE
   `word_mul (word_sub (word_mul (word_sub (word_mul (word_add
      (word_mul x (word 4)) x) (word 64)) (word_add (word_mul x (word 4)) x))
      (word 64)) x) (word 64):int32 =
    word_mul x (word 1290176)`] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
              VAL_WORD; DIMINDEX_32; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`;
    ARITH_RULE `y < 3329 ==> y * 1290176 < 4294967296`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 134217728 * 32`; GSYM DIV_MOD] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ADD_SYM] THEN
  ASM_SIMP_TAC[COMPRESS_D5_ARITH]);;

(* ------------------------------------------------------------------------- *)
(* The packing of eight 5-bit values into five bytes.                        *)
(* ------------------------------------------------------------------------- *)

let BYTES_OF_NUM_5 = prove
 (`!n. n < 2 EXP 40
       ==> n MOD 256 + 256 * (n DIV 256) MOD 256 +
           65536 * (n DIV 65536) MOD 256 +
           16777216 * (n DIV 16777216) MOD 256 +
           4294967296 * (n DIV 4294967296) MOD 256 = n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(n DIV 4294967296) MOD 256 = n DIV 4294967296`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `n < 2 EXP 40` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 256`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 65536`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 16777216`; `256`] DIVISION) THEN
  REWRITE_TAC[DIV_DIV; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let VAL_JOIN_5X8 = prove
 (`!(u0:5 word) (u1:5 word) (u2:5 word) (u3:5 word)
    (u4:5 word) (u5:5 word) (u6:5 word) (u7:5 word).
     val(word_join u7 (word_join u6 (word_join u5 (word_join u4
          (word_join u3 (word_join u2 (word_join u1 u0:10 word):15 word):
           20 word):25 word):30 word):35 word):40 word) =
     val u0 + 32 * val u1 + 1024 * val u2 + 32768 * val u3 +
     1048576 * val u4 + 33554432 * val u5 + 1073741824 * val u6 +
     34359738368 * val u7`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`u0:5 word`; `u1:5 word`; `u2:5 word`; `u3:5 word`;
    `u4:5 word`; `u5:5 word`; `u6:5 word`; `u7:5 word`] THEN
  REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun k ->
    SPEC_TAC(mk_comb(`val:5 word->num`,mk_var("u"^string_of_int k,`:5 word`)),
             mk_var("n"^string_of_int k,`:num`))) (0--7) THEN
  REPEAT STRIP_TAC THEN REPEAT MOD_LT_ASM_TAC THEN ARITH_TAC);;

(*** The stored bytes as parts of the 40-bit join of the eight fields, with
 *** the computations for the coefficients as atoms for the bit-blasting
 ***)

let compress_d5_indices = map (fun k ->
  if k = 0 then `8 * i` else
  mk_binop `(+):num->num->num` `8 * i` (mk_small_numeral k)) (0--7);;

let d5_xatoms =
  let tm = rand(concl(TOP_DEPTH_CONV let_CONV
   `let x:int32 = word_join ((if word_igt (word 0) (y:int16)
                              then word 65535 else word 0):int16) y in
    word_add
     (word_shl
       (word_sub (word_shl (word_sub (word_shl
         (word_add (word_shl x 2) x) 6)
         (word_add (word_shl x 2) x)) 6) x) 6)
     (word 67108864)`)) in
  map (fun j -> vsubst [mk_comb(`x:num->int16`,j),`y:int16`] tm)
      compress_d5_indices;;

let d5_join =
  vsubst (zip d5_xatoms (map (fun k -> mk_var("w"^string_of_int k,`:int32`))
                             (0--7)))
  `word_join (word_subword (w7:int32) (27,5):5 word)
    (word_join (word_subword (w6:int32) (27,5):5 word)
     (word_join (word_subword (w5:int32) (27,5):5 word)
      (word_join (word_subword (w4:int32) (27,5):5 word)
       (word_join (word_subword (w3:int32) (27,5):5 word)
        (word_join (word_subword (w2:int32) (27,5):5 word)
         (word_join (word_subword (w1:int32) (27,5):5 word)
                    (word_subword (w0:int32) (27,5):5 word):10 word):
         15 word):20 word):25 word):30 word):35 word):40 word`;;

let D5_PACK_TAC =
  let rule m th =
    let v = rand(concl th) in
    let target = mk_comb(mk_comb(`word_subword:40 word->num#num->byte`,
                                 d5_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int32`) d5_xatoms in
    let eq = subst (zip gvs d5_xatoms) (mk_eq(v,target)) in
    let bth = INST (zip d5_xatoms gvs) (BITBLAST_RULE eq) in
    CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                        NUM_REDUCE_CONV)) (TRANS th bth) in
  W(fun (asl,w) ->
    let get pat =
      snd(find (fun (_,th) -> can (term_match [] pat) (concl th)) asl) in
    let th4 = get
      `read (memory :> bytes32 (word_add r (word (5 * i)))) s = x`
    and th1 = get
      `read (memory :> bytes8 (word_add (word_add r (word (5 * i)))
                                        (word 4))) s = x` in
    let bytes = map (CONV_RULE(RAND_CONV(REWRITE_CONV
                  [WORD_VAL_MOD_256; WORD_VAL_MOD_65536;
                   WORD_VAL_DIV_256_MOD_256] THENC
                  SIMD_SIMPLIFY_CONV [])))
                (CONJUNCTS(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th4) @ [th1]) in
    MAP_EVERY ASSUME_TAC (map2 rule (0--4) bytes));;

(* ------------------------------------------------------------------------- *)
(* The two loads of four coefficients, and the bytes of the result of the    *)
(* vector computation, moved to RAX after PACKUSWB.                          *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D5_LOADS_TAC =
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
    REWRITE_TAC[WORD_RULE
     `word_add a (word (16 * i + 8)):int64 =
      word_add (word_add a (word (16 * i))) (word 8)`] THEN
    DISCH_TAC) [`2 * i`; `2 * i + 1`];;

let COMPRESS_D5_TIDY_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RAX s = x`) (concl th) &&
       can (find_term (fun t -> try fst(dest_const(rator t)) = "MIN"
                                with Failure _ -> false)) (concl th)
    then CONV_RULE(RAND_CONV(REWRITE_CONV[PACKUSWB_SAT_255] THENC
                             REWRITE_CONV[PACKUSWB_JOIN] THENC
                             SIMD_SIMPLIFY_CONV [])) th
    else th);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 5 in common/fips203.ml, the      *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 32 * x / 3329, rounding up on ties, modulo 32, i.e.                       *)
(* ((64 * x + 3329) DIV 6658) MOD 32, and as for mlkem_encode 5 the 5-bit    *)
(* values are put together little-endian. Like the C code, this relies on    *)
(* the coefficients being in [0,3329).                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,160))
            [(word pc,0x82a0); (a,512);
             (word_sub stackpointer (word 16),24)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 16),24))
            [(word pc,0x82a0); (a,512)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x28c0) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                     (word_add a (word(2 * i)))) s =
                           x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,160)) s =
                       nsum {i | i < 256}
                            (\i. ((64 * val(x i) + 3329) DIV 6658) MOD 32 *
                                 2 EXP (5 * i))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,160);
                         memory :> bytes(word_sub stackpointer
                                                  (word 16),16)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN

  (*** The loop, over groups of 8 coefficients ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x28e8` `pc + 0x2ae2`
   `\i s. read RCX s = word_add a (word(16 * i)) /\
          read RDX s = word_add r (word(5 * i)) /\
          read RSI s = word_add r (word 160) /\
          read XMM2 s = word 0x00000000000000000400000004000000 /\
          read XMM3 s = word 0 /\
          read XMM4 s = word 0x000000000000000000ff00ff00ff00ff /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          ((!j. j < 256 ==> val(x j) < 3329)
           ==> read(memory :> bytes(r,5 * i)) s =
               nsum {j | j < 8 * i}
                (\j. ((64 * val(x j) + 3329) DIV 6658) MOD 32 *
                     2 EXP (5 * j)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the registers, with the vectors of       ***)
    (*** constants from the image                                        ***)

    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE 0x28d6 0x8018 64)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE 0x28e3 0x8008 64)) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[XMM2; XMM3; XMM4; READ_ZEROTOP_128] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                NSUM_CLAUSES_NUMSEG_LT; READ_MEMORY_BYTES_TRIVIAL] THEN
    REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST;

    (*** The loop body, for eight coefficients and five bytes ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
    GHOST_INTRO_TAC `ymm7_init:int256` `read YMM7` THEN
    GHOST_INTRO_TAC `ymm8_init:int256` `read YMM8` THEN
    GHOST_INTRO_TAC `ymm9_init:int256` `read YMM9` THEN
    GHOST_INTRO_TAC `ymm10_init:int256` `read YMM10` THEN
    GHOST_INTRO_TAC `ymm11_init:int256` `read YMM11` THEN
    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top2" `YMM2` THEN
    XMM_EXISTSTOP_TAC "top3" `YMM3` THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    COMPRESS_D5_LOADS_TAC THEN
    MAP_EVERY (fun k ->
      X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--77) THEN
    COMPRESS_D5_TIDY_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (78--124) THEN

    (*** The new bytes as parts of the join of the 5-bit fields ***)

    D5_PACK_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[XMM2; XMM3; XMM4; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
      CONV_TAC WORD_RULE;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE
     `5 * (i + 1) = ((((5 * i + 1) + 1) + 1) + 1) + 1`] THEN
    REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN
    REWRITE_TAC[ARITH_RULE `(5 * i + 1) + 1 = 5 * i + 2`;
                ARITH_RULE `(5 * i + 2) + 1 = 5 * i + 3`;
                ARITH_RULE `(5 * i + 3) + 1 = 5 * i + 4`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INST_TYPE [`:40`,`:M`; `:8`,`:N`] VAL_WORD_SUBWORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_1] THEN
    MP_TAC(SPEC (mk_comb(`val:40 word->num`,d5_join)) BYTES_OF_NUM_5) THEN
    MP_TAC(ISPEC d5_join VAL_BOUND) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MP th)) THEN
    REWRITE_TAC[VAL_JOIN_5X8] THEN

    (*** The compression of each coefficient ***)

    MAP_EVERY (fun jt ->
      MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)
        (SPEC (mk_comb(`x:num->int16`,jt)) COMPRESS_D5_FIELD)) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (can (term_match []
                `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o concl)) THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) compress_d5_indices THEN

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
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add r (word (5 * i)))
                     (word_add r (word 160)):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 5 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit, restoring the registers, and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--2) THEN
    PTR_DECIDE_RIP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (3--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (is_imp o concl))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,160))
               [word pc,0x82a0; a,512; word_sub stackpointer (word 16),24] /\
           ALL (nonoverlapping (word_sub stackpointer (word 16),24))
               [word pc,0x82a0; a,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x28c0) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc
                                (word_sub stackpointer (word 16))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,512; r,160; word (pc + 0x8018),8;
                           word (pc + 0x8008),8;
                           word_sub stackpointer (word 16),24]
                          [r,160; word_sub stackpointer (word 16),16]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,160);
                           memory :> bytes(word_sub stackpointer (word 16),
                                           16)])`,
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
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x28e8` `pc + 0x2aeb`
   `\i s. read RCX s = word_add a (word(16 * i)) /\
          read RDX s = word_add r (word(5 * i)) /\
          read RSI s = word_add r (word 160) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--9) THEN
    REWRITE_TAC[MULT_0; WORD_ADD_0; WORD_VAL_ADD_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--3) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_COMPRESS_D5_GCC12_O2_EXEC (1--126) THEN
  SUBGOAL_THEN
   `~(val(word_add (word_add r (word (5 * i))) (word 5):int64) =
      val(word_add r (word 160):int64)) <=> i + 1 < 32`
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
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`;
                ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) (1--2) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
