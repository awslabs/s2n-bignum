(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Forward number-theoretic transform from ML-KEM.                         *)
(* This is the code for mlkem_poly_ntt from mlkem-native's portable C      *)
(* implementation compiled by gcc 12 with -Os (see                         *)
(* mlkem_native/README.md), verified in the whole image (see libmlkem.ml). *)
(* The statements are those of the -O2 code.                               *)
(*                                                                         *)
(* At -Os the code is not unrolled or vectorized. It is the three nested   *)
(* loops of the C code, with 16-bit loads and stores: the layers (X2 is    *)
(* one more than the number of layers done), the blocks of a layer (X5 is  *)
(* the start of the block, X3 the start of its upper half), and the        *)
(* butterflies of a block (X4 and X9 point at the coefficients of the      *)
(* lower and upper half). It loads the zeta of a block from the table of   *)
(* zetas by its index (X6), uses no stack and no callee-saved register,    *)
(* and reads no constants other than the table of zetas.                   *)
(*                                                                         *)
(*     +0x0  mov     w2, #0x1                                              *)
(*     +0x4  adrp    x8, <page of mlk_zetas>                               *)
(*     +0x8  mov     w11, w2                                               *)
(*     +0xc  add     x8, x8, #0xb00                                        *)
(*    +0x10  mov     w12, #0x100                                           *)
(*    +0x14  mov     w13, #0xfffff301                                      *)
(*    +0x18  mov     w14, #0xfffff2ff                                      *)
(*  loop1:                                                                 *)
(*    +0x1c  sub     w6, w2, #0x1                                          *)
(*    +0x20  lsr     w3, w12, w2                                           *)
(*    +0x24  lsl     w10, w3, #1                                           *)
(*    +0x28  mov     w5, #0x0                                              *)
(*    +0x2c  lsl     w6, w11, w6                                           *)
(*  loop2:                                                                 *)
(*    +0x30  mov     w1, w6                                                *)
(*    +0x34  add     w6, w6, #0x1                                          *)
(*    +0x38  ldrsh   w15, [x8, w1, uxtw #1]                                *)
(*    +0x3c  cmp     w5, w3                                                *)
(*    +0x40  b.cs    join1                                                 *)
(*    +0x44  mov     w4, w5                                                *)
(*    +0x48  add     x9, x0, w3, uxtw #1                                   *)
(*  loop3:                                                                 *)
(*    +0x4c  ldrsh   w7, [x9]                                              *)
(*    +0x50  mul     w7, w7, w15                                           *)
(*    +0x54  mul     w1, w7, w13                                           *)
(*    +0x58  sxth    w1, w1                                                *)
(*    +0x5c  madd    w1, w1, w14, w7                                       *)
(*    +0x60  ldrh    w7, [x0, x4, lsl #1]                                  *)
(*    +0x64  sub     w7, w7, w1, asr #16                                   *)
(*    +0x68  strh    w7, [x9], #2                                          *)
(*    +0x6c  ldrh    w7, [x0, x4, lsl #1]                                  *)
(*    +0x70  add     w1, w7, w1, asr #16                                   *)
(*    +0x74  strh    w1, [x0, x4, lsl #1]                                  *)
(*    +0x78  add     x4, x4, #0x1                                          *)
(*    +0x7c  cmp     w3, w4                                                *)
(*    +0x80  b.hi    loop3                                                 *)
(*  join1:                                                                 *)
(*    +0x84  add     w5, w5, w10                                           *)
(*    +0x88  add     w3, w3, w10                                           *)
(*    +0x8c  cmp     w5, #0xff                                             *)
(*    +0x90  b.ls    loop2                                                 *)
(*    +0x94  add     w2, w2, #0x1                                          *)
(*    +0x98  cmp     w2, #0x8                                              *)
(*    +0x9c  b.ne    loop1                                                 *)
(*    +0xa0  ret                                                           *)
(*                                                                         *)
(* The proof of correctness has a loop for the layers, a loop for the      *)
(* blocks of a layer (for each of the seven layers), and a loop for the    *)
(* butterflies of a block. The proof of memory safety does the seven       *)
(* layers one after the other, as at -O2.                                  *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;
needs "common/int_linear.ml";;

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_poly_ntt"];;

(* ------------------------------------------------------------------------- *)
(* The computation done by the C code, with its 16-bit and 32-bit integer    *)
(* arithmetic. The NTT is done in 7 layers, layer l+1 consisting of 2^l      *)
(* blocks of 2^(8-l) consecutive coefficients. A block uses one zeta to do   *)
(* butterflies on pairs of coefficients 2^(7-l) apart, independently.        *)
(* ------------------------------------------------------------------------- *)

let ntt_fqmul_c = define
 `ntt_fqmul_c (z:int16) (y:int16) =
    montred_scalar(word_mul (word_sx y) (word_sx z))`;;

let ntt_block_c = define
 `ntt_block_c (z:int16) start len (m:num->int16) i =
    if start <= i /\ i < start + len
    then word_add (m i) (ntt_fqmul_c z (m(i + len)))
    else if start + len <= i /\ i < start + 2 * len
    then word_sub (m(i - len)) (ntt_fqmul_c z (m i))
    else m i`;;

let ntt_blocks_c = define
 `ntt_blocks_c l 0 (r:num->int16) = r /\
  ntt_blocks_c l (SUC b) r =
    ntt_block_c (iword(EL (2 EXP l + b) mlk_zetas))
                (2 * 2 EXP (7 - l) * b) (2 EXP (7 - l))
                (ntt_blocks_c l b r)`;;

let ntt_layers_c = define
 `ntt_layers_c 0 (x:num->int16) = x /\
  ntt_layers_c (SUC l) x = ntt_blocks_c l (2 EXP l) (ntt_layers_c l x)`;;

(* ------------------------------------------------------------------------- *)
(* Some lemmas and tactics for the butterflies.                              *)
(* ------------------------------------------------------------------------- *)

(*** Adding a 16-bit coefficient given as the low part of a 32-bit word ***)

let NTT_ZX_ZX_ADD_16_STMT =
  `!t:int32 x:int16. word_zx (word_add (word_zx x) t):int16 =
                     word_add x (word_zx t)`;;

let NTT_ZX_ZX_ADD_16 = assume_spec NTT_ZX_ZX_ADD_16_STMT;;

(*** Prepare a load of zeta number n using UXTW indexing ***)

let ZETA_UXTW_TAC n =
  MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mlk_zetas` (concl th)
    then MP_TAC(SPEC n th) else failwith "") THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;

(*** Rewrite the assumption that gives the value of register r ***)

let REG_REWRITE_TAC r ths =
  FIRST_X_ASSUM(fun th ->
    let l,t = dest_eq(concl th) in
    if is_comb l && is_comb(rator l) && rand(rator l) = r
    then ASSUME_TAC(REWRITE_RULE ths th)
    else failwith "REG_REWRITE_TAC");;

(* ------------------------------------------------------------------------- *)
(* One block, from the load of its zeta through the inner loop and the       *)
(* update of the start and the end of the block.                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_BLOCK_STMT =
  `!a zetas pc start len k (m:num->int16) w2 w11 w12.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)] /\
     1 <= len /\ start + 2 * len <= 256 /\ k < 128
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2) /\
               read X0 s = a /\ read X2 s = w2 /\
               read X3 s = word(start + len) /\ read X5 s = word start /\
               read X6 s = word k /\ read X8 s = word zetas /\
               read X10 s = word(2 * len) /\
               read X11 s = w11 /\ read X12 s = w12 /\
               read X13 s = word 4294963969 /\ read X14 s = word 4294963967 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_test) /\
               read X0 s = a /\ read X2 s = w2 /\
               read X3 s = word(start + 3 * len) /\
               read X5 s = word(start + 2 * len) /\
               read X6 s = word(k + 1) /\ read X8 s = word zetas /\
               read X10 s = word(2 * len) /\
               read X11 s = w11 /\ read X12 s = w12 /\
               read X13 s = word 4294963969 /\ read X14 s = word 4294963967 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_block_c (iword(EL k mlk_zetas)) start len m i))
          (MAYCHANGE [PC; X1; X3; X4; X5; X6; X7; X9; X15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_BLOCK =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_OS_BLOCK_STMT;;

(* ------------------------------------------------------------------------- *)
(* One layer, with its blocks in a loop.                                     *)
(* ------------------------------------------------------------------------- *)

(*** Assertion at the head of the block loop, with b blocks of layer l done.
 *** At the test at its end it is the same assertion, with the number of
 *** the blocks done one higher.
 ***)

let ntt_blockhead_tm =
  let headtm =
   `\s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_Os_mc /\
        read X0 s = a /\ read X2 s = word(L + 1) /\
        read X3 s = word(2 * LEN * B + LEN) /\
        read X5 s = word(2 * LEN * B) /\
        read X6 s = word(2 EXP L + B) /\ read X8 s = word zetas /\
        read X10 s = word(2 * LEN) /\
        read X11 s = word 1 /\ read X12 s = word 256 /\
        read X13 s = word 4294963969 /\ read X14 s = word 4294963967 /\
        (!k. k < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * k)))) s =
                 iword(EL k mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 ntt_blocks_c L B r i)` in
  fun l b ->
    let len = mk_small_numeral(1 lsl (7 - l)) in
    let tm' = subst [mk_small_numeral l,`L:num`; len,`LEN:num`; b,`B:num`]
                    headtm in
    rhs(concl(NUM_REDUCE_CONV tm'));;

(*** Apply the block lemma at the head of block b of layer l ***)

let NTT_BLOCK_TAC l b =
  let red t =
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] t))) in
  let th = SPECL
   [`a:int64`; `zetas:num`; `pc:num`;
    red `2 * LEN * B`; red `LEN:num`; red `2 EXP L + B`;
    red `ntt_blocks_c L B r`; red `word(L + 1):int64`;
    `word 1:int64`; `word 256:int64`] MLKEM_NATIVE_POLY_NTT_GCC12_OS_BLOCK in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`; b,`b:num`]
          (SPEC_ALL(CONJUNCT2 ntt_blocks_c)))) in
  MP_TAC th THEN ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ENSURES_WEAKEN_TAC o CONV_RULE NUM_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth] THEN
    REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;


(*** Apply the block lemma at the head of block b of layer l ***)

let NTT_LAYER_TAC l =
  let n = mk_small_numeral(1 lsl l) in
  ENSURES_WHILE_UP_TAC n `pc + mlkem_poly_ntt_loop2`
    `pc + mlkem_poly_ntt_loop2_test`
    (mk_abs(`b:num`,ntt_blockhead_tm l `b:num`)) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** The layer head, setting up the registers for the first block ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[ntt_blocks_c] THEN ASM_REWRITE_TAC[];

    (*** One block ***)

    X_GEN_TAC `b:num` THEN STRIP_TAC THEN NTT_BLOCK_TAC l `b:num`;

    (*** The back edge of the block loop ***)

    X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The exit from the block loop ***)

    ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_LAYER_STMT =
  `!a zetas pc l (r:num->int16).
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)] /\
     l < 7
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop1) /\
               read X0 s = a /\ read X2 s = word(l + 1) /\
               read X8 s = word zetas /\
               read X11 s = word 1 /\ read X12 s = word 256 /\
               read X13 s = word 4294963969 /\ read X14 s = word 4294963967 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        r i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_exit) /\
               read X0 s = a /\ read X2 s = word(l + 1) /\
               read X8 s = word zetas /\
               read X11 s = word 1 /\ read X12 s = word 256 /\
               read X13 s = word 4294963969 /\ read X14 s = word 4294963967 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_blocks_c l (2 EXP l) r i))
          (MAYCHANGE [PC; X1; X3; X4; X5; X6; X7; X9; X10; X15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_LAYER =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_OS_LAYER_STMT;;


(*** Apply the lemma for layer l at its head, giving the state after the
 *** layer, before the increment of the layer counter
 ***)

let NTT_LAYER_APPLY_TAC =
  let sth = REWRITE_RULE[ADD1] (SPEC_ALL(CONJUNCT2 ntt_layers_c)) in
  MP_TAC(SPECL [`a:int64`; `zetas:num`; `pc:num`; `l:num`;
                `ntt_layers_c l x`] MLKEM_NATIVE_POLY_NTT_GCC12_OS_LAYER) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(ENSURES_WEAKEN_TAC) THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sth];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;


(* ------------------------------------------------------------------------- *)
(* The computation of the C code gives the NTT, within the same bounds as    *)
(* the hand-written kernel.                                                  *)
(* ------------------------------------------------------------------------- *)

let NTT_BLOCKS_C_CLOSED_STMT =
  `!l b r i.
     ntt_blocks_c l b r i =
     if i < 2 * 2 EXP (7 - l) * b
     then let z = iword(EL (2 EXP l + i DIV (2 * 2 EXP (7 - l))) mlk_zetas) in
          if i MOD (2 * 2 EXP (7 - l)) < 2 EXP (7 - l)
          then word_add (r i) (ntt_fqmul_c z (r(i + 2 EXP (7 - l))))
          else word_sub (r(i - 2 EXP (7 - l))) (ntt_fqmul_c z (r i))
     else r i`;;

let NTT_BLOCKS_C_CLOSED = assume_spec NTT_BLOCKS_C_CLOSED_STMT;;

let NTT_LAYERS_C_STEP_STMT =
  `!l x i.
     l < 7 /\ i < 256
     ==> ntt_layers_c (SUC l) x i =
         let z = iword(EL (2 EXP l + i DIV (2 * 2 EXP (7 - l))) mlk_zetas) in
         if i MOD (2 * 2 EXP (7 - l)) < 2 EXP (7 - l)
         then word_add (ntt_layers_c l x i)
                       (ntt_fqmul_c z (ntt_layers_c l x (i + 2 EXP (7 - l))))
         else word_sub (ntt_layers_c l x (i - 2 EXP (7 - l)))
                       (ntt_fqmul_c z (ntt_layers_c l x i))`;;

let NTT_LAYERS_C_STEP = assume_spec NTT_LAYERS_C_STEP_STMT;;

let MLK_ZETAS_ELS =
  map (fun k -> (REWRITE_CONV[mlk_zetas] THENC EL_CONV)
                 (mk_comb(mk_comb(`EL:num->int list->int`,mk_small_numeral k),
                          `mlk_zetas`))) (0--127);;

let NTT_LAYER_EQUATION =
  let conv =
    NUM_REDUCE_CONV THENC TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV(CONJUNCT1 ntt_layers_c :: MLK_ZETAS_ELS) THENC
    ONCE_DEPTH_CONV WORD_IWORD_CONV THENC REWRITE_CONV[ntt_fqmul_c] THENC
    DEPTH_CONV WORD_RED_CONV in
  fun l i ->
    let th = SPECL [mk_small_numeral l; `x:num->int16`; mk_small_numeral i]
                   NTT_LAYERS_C_STEP in
    let th' = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
    CONV_RULE(BINOP_CONV conv) th';;

(*** All the layer equations, in the order of the layers ***)

let NTT_LAYER_EQUATIONS =
  map (fun (l,i) -> SYM(NTT_LAYER_EQUATION l i))
      (List.concat (map (fun l -> map (fun i -> (l,i)) (0--255)) (0--6)));;

let NTT_FINAL_TAC lfn =
  W(fun (asl,w) ->
    let tm = find_term (can (term_match [] `ntt_layers_c 7 x i`)) w in
    let th = apply lfn tm in
    if not(fst(dest_const(repeat rator w)) = "int_le") then
      MP_TAC(CONJUNCT1 th) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV FORWARD_NTT_CONV) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN INT_LINEAR_CONG_TAC
    else
      MP_TAC(CONJUNCT2 th) THEN INT_ARITH_TAC);;

let NTT_LAYERS_C_CORRECT_STMT =
  `!x. (!i. i < 256 ==> abs(ival(x i)) <= &8191)
       ==> !i. i < 256
               ==> (ival(ntt_layers_c 7 x i) == forward_ntt (ival o x) i)
                   (mod &3329) /\
                   abs(ival(ntt_layers_c 7 x i)) <= &23594`;;

let NTT_LAYERS_C_CORRECT = assume_spec NTT_LAYERS_C_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The seven layers, with the loop over them.                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_LAYERS_STMT =
  `!a zetas (x:num->int16) pc.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop1) /\
               read X0 s = a /\ read X2 s = word 1 /\
               read X8 s = word zetas /\
               read X11 s = word 1 /\ read X12 s = word 256 /\
               read X13 s = word 4294963969 /\ read X14 s = word 4294963967 /\
               (!k. k < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * k)))) s =
                        iword(EL k mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i))
          (\s. read PC s = word(pc + mlkem_poly_ntt_ret) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_layers_c 7 x i))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X9; X10; X15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_LAYERS =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_OS_LAYERS_STMT;;


(*** The loop over the seven layers ***)

let NTT_LAYERS_TAC =
  MAP_EVERY X_GEN_TAC [`a:int64`; `zetas:num`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `7` `pc + mlkem_poly_ntt_loop1`
    `pc + mlkem_poly_ntt_loop1_test`
   `\l s. aligned_bytes_loaded s (word pc)
            mlkem_native_libmlkem_gcc12_Os_mc /\
          read X0 s = a /\ read X2 s = word(l + 1) /\
          read X8 s = word zetas /\
          read X11 s = word 1 /\ read X12 s = word 256 /\
          read X13 s = word 4294963969 /\ read X14 s = word 4294963967 /\
          (!k. k < 128
               ==> read(memory :> bytes16(word_add (word zetas)
                                                   (word(2 * k)))) s =
                   iword(EL k mlk_zetas)) /\
          (!i. i < 256
               ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                   ntt_layers_c l x i)` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** The entry, with no layer done ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ntt_layers_c; ADD_CLAUSES];

    (*** One layer and the increment of the layer counter ***)

    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    ENSURES_SEQUENCE_TAC `pc + mlkem_poly_ntt_loop2_exit`
     `\s. aligned_bytes_loaded s (word pc)
            mlkem_native_libmlkem_gcc12_Os_mc /\
          read X0 s = a /\ read X2 s = word(l + 1) /\
          read X8 s = word zetas /\
          read X11 s = word 1 /\ read X12 s = word 256 /\
          read X13 s = word 4294963969 /\ read X14 s = word 4294963967 /\
          (!k. k < 128
               ==> read(memory :> bytes16(word_add (word zetas)
                                                   (word(2 * k)))) s =
                   iword(EL k mlk_zetas)) /\
          (!i. i < 256
               ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                   ntt_layers_c (l + 1) x i)` THEN
    CONJ_TAC THENL
     [NTT_LAYER_APPLY_TAC;
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (1--1) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      WORD_SMALL_TAC];

    (*** The back edge of the layer loop ***)

    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The exit after the last layer ***)

    ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_ZETAS_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data (layout "rodata_mlk_zetas");;

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a (x:num->int16) pc returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_Os_mc /\
           read PC s = word (pc + mlkem_poly_ntt) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
            ==> !i. i < 256
                    ==> let zi =
                          read(memory :> bytes16(word_add a (word(2 * i)))) s
                        in (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                           abs(ival zi) <= &23594))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This follows the structure of the  *)
(* correctness proof, with the events of a block and of each layer given by  *)
(* functions obtained from the corresponding lemmas.                         *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** One block, from the load of its zeta through the inner loop ***)

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_BLOCK_SAFE_STMT =
  `exists f_ev_blk.
   forall e a zetas pc start len k w2 w11 w12 returnaddress.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)] /\
     1 <= len /\ start + 2 * len <= 256 /\ k < 128
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2) /\
               read X0 s = a /\ read X2 s = w2 /\
               read X3 s = word(start + len) /\ read X5 s = word start /\
               read X6 s = word k /\ read X8 s = word zetas /\
               read X10 s = word(2 * len) /\
               read X11 s = w11 /\ read X12 s = w12 /\
               read X30 s = returnaddress /\ read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_test) /\
               read X0 s = a /\ read X2 s = w2 /\
               read X3 s = word(start + 3 * len) /\
               read X5 s = word(start + 2 * len) /\
               read X6 s = word(k + 1) /\ read X8 s = word zetas /\
               read X10 s = word(2 * len) /\
               read X11 s = w11 /\ read X12 s = w12 /\
               read X30 s = returnaddress /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a zetas pc start len k /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE [PC; X1; X3; X4; X5; X6; X7; X9; X15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_BLOCK_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_OS_BLOCK_SAFE_STMT;;

let NTT_GCC12_OS_BLOCK_EVENTS =
  new_specification ["ntt_gcc12_Os_block_events"]
                    MLKEM_NATIVE_POLY_NTT_GCC12_OS_BLOCK_SAFE;;

(*** One layer, for each of the seven layers ***)

let lsafe_goal l =
  let tm =
  `exists f_ev_lay.
    forall e a zetas pc returnaddress.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size);
                                   (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop1) /\
               read X0 s = a /\ read X2 s = word(L + 1) /\
               read X8 s = word zetas /\
               read X11 s = word 1 /\ read X12 s = word 256 /\
               read X30 s = returnaddress /\ read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_gcc12_Os_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_exit) /\
               read X0 s = a /\ read X2 s = word(L + 1) /\
               read X8 s = word zetas /\
               read X11 s = word 1 /\ read X12 s = word 256 /\
               read X30 s = returnaddress /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_lay a zetas pc /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE [PC; X1; X3; X4; X5; X6; X7; X9; X10; X15] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])` in
  rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm)));;

(*** The event template for layer l ***)

let lsafe_template l =
  let len = mk_small_numeral(1 lsl (7 - l)) in
  subst [len,`LEN:num`; mk_small_numeral(1 lsl l),`N:num`;
         mk_small_numeral(1 lsl l),`P:num`]
   `\(a:int64) (zetas:num) (pc:num).
      APPEND []
       (APPEND
         (ENUMERATEL N
           (\i. APPEND (f_ev_ltest a zetas pc i)
                       (ntt_gcc12_Os_block_events a zetas pc (2 * LEN * i) LEN
                                                  (P + i))))
         (f_ev_lhead a zetas pc))
     :(uarch_event)list`;;

(*** The block lemma for block b of layer l ***)

let ntt_block_events_inst l b ev =
  let red t = rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] t))) in
  SPECL [ev; `a:int64`; `zetas:num`; `pc:num`;
         red `2 * LEN * B`; red `LEN:num`; red `2 EXP L + B`;
         red `word(L + 1):int64`; `word 1:int64`; `word 256:int64`;
         `returnaddress:int64`]
        NTT_GCC12_OS_BLOCK_EVENTS;;

(*** Register state at the block head and block end (b blocks done) ***)

let lsafe_blockhead_tm =
  let headtm =
   `\s. read X0 s = a /\ read X2 s = word(L + 1) /\
        read X3 s = word(2 * LEN * B + LEN) /\
        read X5 s = word(2 * LEN * B) /\
        read X6 s = word(2 EXP L + B) /\ read X8 s = word zetas /\
        read X10 s = word(2 * LEN) /\
        read X11 s = word 1 /\ read X12 s = word 256 /\
        read X30 s = returnaddress` in
  fun l b ->
    rhs(concl(NUM_REDUCE_CONV(subst
     [mk_small_numeral l,`L:num`; mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
      b,`B:num`] headtm)));;

(*** The test at the end of a block of a layer with n blocks ***)

let LSAFE_TEST_TAC n =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (fun (asl,w) ->
     match find_terms is_cond w with
       [] -> ALL_TAC (asl,w)
     | tms ->
         let c = rand(rator(rator(hd(sort (fun a b -> free_in b a) tms)))) in
         (SUBGOAL_THEN (mk_eq(c,subst [n,`N:num`] `i + 1 < N`))
           SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) (asl,w)) THEN
  REPEAT(CONJ_TAC THENL
   [REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    (ASM_ARITH_TAC ORELSE (AP_TERM_TAC THEN ASM_ARITH_TAC));
    ALL_TAC]) THEN
  REWRITE_TAC[APPEND_NIL] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let NTT_LAYER_SAFE_TAC l =
  let n = mk_small_numeral(1 lsl l) in
  CONCRETIZE_F_EVENTS_TAC (lsafe_template l) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC n `pc + mlkem_poly_ntt_loop2`
   `pc + mlkem_poly_ntt_loop2_exit`
   (mk_abs(`i:num`,lsafe_blockhead_tm l `i:num`)) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** The layer head ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** One block and the test of the block loop ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_ntt_loop2_test`
      (lsafe_blockhead_tm l `(i:num) + 1`) THEN
    CONJ_TAC THENL
     [EVENTS_LEMMA_TAC (ntt_block_events_inst l `i:num`);
      LSAFE_TEST_TAC n];

    (*** The exit ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND; APPEND_NIL]) THEN
    REWRITE_TAC[APPEND; APPEND_NIL] THEN
    FIRST_X_ASSUM ACCEPT_TAC];;

let NTT_GCC12_OS_LAYER_EVENTS = assuming_proofs (fun () ->
  map (fun l ->
        new_specification ["ntt_gcc12_Os_layer_events_" ^ string_of_int l]
                          (prove(lsafe_goal l,NTT_LAYER_SAFE_TAC l)))
      (0--6));;

(*** The whole code, with the events of the layers and of the steps
 *** between them
 ***)

let ntt_top_template =
  let lay l = list_mk_comb(
     mk_const("ntt_gcc12_Os_layer_events_" ^ string_of_int l,[]),
     [`a:int64`; `pc + rodata_mlk_zetas`; `pc:num`])
  and fev n =
    list_mk_comb(mk_var(n,`:int64->num->int64->(uarch_event)list`),
                 [`a:int64`;`pc:num`;`returnaddress:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain l acc =
    if l > 6 then acc else
    let acc' = app (lay l) acc in
    if l = 6 then acc' else
    chain (l + 1) (app (fev ("f_ev_back" ^ string_of_int l)) acc') in
  let body = app (fev "f_ev_fin") (chain 0 (fev "f_ev_init")) in
  list_mk_abs([`a:int64`;`pc:num`;`returnaddress:int64`],body);;

(*** The state at the head of the layer loop with l layers done, and at the
 *** end of layer l
 ***)

let ntt_safe_layerhead_tm,ntt_safe_layerend_tm =
  let headtm =
   `\s. read X0 s = a /\ read X2 s = word(L + 1) /\
        read X8 s = word(pc + rodata_mlk_zetas) /\
        read X11 s = word 1 /\ read X12 s = word 256 /\
        read X30 s = returnaddress` in
  let mk tm l =
    rhs(concl(NUM_REDUCE_CONV(subst [mk_small_numeral l,`L:num`] tm))) in
  (fun l -> mk headtm l),(fun l -> mk headtm l);;

let ntt_layer_events_inst l ev =
  SPECL [ev; `a:int64`; `pc + rodata_mlk_zetas`; `pc:num`;
         `returnaddress:int64`]
        (el l NTT_GCC12_OS_LAYER_EVENTS);;

let NTT_SAFE_SIM_TAC n =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC [i] THEN
    TRY W32_DECIDE_FLAGS_TAC) (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let NTT_SAFE_TOP_TAC =
  CONCRETIZE_F_EVENTS_TAC ntt_top_template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,512)
                  (word(pc + rodata_mlk_zetas),256)` ASSUME_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_poly_ntt_loop2_exit` (ntt_safe_layerend_tm 6) THEN
  CONJ_TAC THENL [ALL_TAC; NTT_SAFE_SIM_TAC 4] THEN
  MAP_EVERY (fun l ->
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlkem_poly_ntt_loop1` (ntt_safe_layerhead_tm l) THEN
    CONJ_TAC THENL [ALL_TAC; EVENTS_LEMMA_TAC (ntt_layer_events_inst l)] THEN
    if l = 0 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlkem_poly_ntt_loop2_exit` (ntt_safe_layerend_tm (l - 1)) THEN
    CONJ_TAC THENL [ALL_TAC; NTT_SAFE_SIM_TAC 3]) (rev(0--6)) THEN

  (*** The setup of the layer loop, with the address of the zetas ***)

  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (1--2) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC (3--7) THEN
  REG_REWRITE_TAC `X8` [GSYM WORD_ADD] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + rodata_mlk_zetas):int64`,`256`]
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_NTT_GCC12_OS_EXEC;;

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e a pc returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       nonoverlapping (a,512) (word pc,libmlkem_size)
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_gcc12_Os_mc /\
                read PC s = word (pc + mlkem_poly_ntt) /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a pc returnaddress /\
                  memaccess_inbounds e2
                   [a,512; word (pc + rodata_mlk_zetas),256] [a,512])
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
