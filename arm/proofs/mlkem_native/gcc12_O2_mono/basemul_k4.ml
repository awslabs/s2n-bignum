(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of 4-element polynomial vectors in NTT domain. This is     *)
(* the code for mlk_polyvec_basemul_acc_montgomery_cached_c1024 from         *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 as   *)
(* one translation unit (see mlkem_native/README.md). It computes the same   *)
(* as mlkem1024_polyvec_basemul_acc_montgomery_cached of the separate -O2    *)
(* build, but the compiler has allocated registers differently. It is        *)
(* verified in the whole image (see libmlkem.ml), with the proof for the     *)
(* separate -O2 build adapted to the image.                                  *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlk_polyvec_basemul_acc_montgomery_cached_c1024:
       +0x0: mov     x10, x1
       +0x4: mov     x11, x2
       +0x8: mov     x14, x3
       +0xc: add     x13, x1, #0x2
      +0x10: mov     x15, x0
      +0x14: add     x12, x2, #0x2
      +0x18: add     x18, x3, #0x100
      +0x1c: mov     w17, #0xfffff301
      +0x20: mov     w16, #0xfffff2ff
      +0x24: nop
      +0x28: mov     x4, x14
      +0x2c: mov     x0, #0x0
      +0x30: mov     w8, #0x0
      +0x34: mov     w7, #0x0
      +0x38: ldrsh   w6, [x13, x0]     <+ |
      +0x3c: add     x4, x4, #0x100     | |
      +0x40: ldrsh   w5, [x10, x0]      | |
      +0x44: ldrsh   w1, [x11, x0]      | |
      +0x48: ldrsh   w2, [x12, x0]      | |
      +0x4c: add     x0, x0, #0x200     | |
      +0x50: ldursh  w3, [x4, #-256]    | |
      +0x54: mul     w9, w5, w1         | |
      +0x58: mul     w1, w6, w1         | |
      +0x5c: madd    w3, w3, w6, w9     | |
      +0x60: madd    w1, w2, w5, w1     | |
      +0x64: add     w7, w7, w3         | |
      +0x68: add     w8, w8, w1         | |
      +0x6c: cmp     x0, #0x800         | |
      +0x70: b.ne    <mlk_polyvec_basemul_acc_montgomery_cached_c1024+0x38>             -+ |
      +0x74: mul     w1, w7, w17
      +0x78: add     x14, x14, #0x2
      +0x7c: mul     w0, w8, w17
      +0x80: add     x13, x13, #0x4
      +0x84: add     x10, x10, #0x4
      +0x88: add     x11, x11, #0x4
      +0x8c: sxth    w1, w1
      +0x90: add     x12, x12, #0x4
      +0x94: sxth    w0, w0
      +0x98: add     x15, x15, #0x4
      +0x9c: madd    w1, w1, w16, w7
      +0xa0: madd    w0, w0, w16, w8
      +0xa4: asr     w1, w1, #16
      +0xa8: sturh   w1, [x15, #-4]
      +0xac: asr     w0, w0, #16
      +0xb0: sturh   w0, [x15, #-2]
      +0xb4: cmp     x18, x14
      +0xb8: b.ne    <mlk_polyvec_basemul_acc_montgomery_cached_c1024+0x28>
      +0xbc: ret
 ***)

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_polyvec_basemul_acc_montgomery_cached_c1024"];;

(* ------------------------------------------------------------------------- *)
(* Definitions used to state specification, as for mlkem_basemul_k4.         *)
(* ------------------------------------------------------------------------- *)

let pmull = define
  `pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;

let pmull_acc4 = define
  `pmull_acc4 (x00: int) (x01 : int) (y00 : int) (y01 : int)
              (x10: int) (x11 : int) (y10 : int) (y11 : int)
              (x20: int) (x21 : int) (y20 : int) (y21 : int)
              (x30: int) (x31 : int) (y30 : int) (y31 : int) =
              pmull x30 x31 y30 y31 + pmull x20 x21 y20 y21 +
              pmull x10 x11 y10 y11 + pmull x00 x01 y00 y01`;;

let pmul_acc4 = define
  `pmul_acc4 (x00: int) (x01 : int) (y00 : int) (y01 : int)
             (x10: int) (x11 : int) (y10 : int) (y11 : int)
             (x20: int) (x21 : int) (y20 : int) (y21 : int)
             (x30: int) (x31 : int) (y30 : int) (y31 : int) =
             (&(inverse_mod 3329 65536) *
    pmull_acc4 x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21
               x30 x31 y30 y31) rem &3329`;;

let basemul4_even = define
 `basemul4_even x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t = \i.
    pmul_acc4 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i)) (y0t i)
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i)) (y1t i)
              (x2 (2 * i)) (x2 (2 * i + 1))
              (y2 (2 * i)) (y2t i)
              (x3 (2 * i)) (x3 (2 * i + 1))
              (y3 (2 * i)) (y3t i)`;;

let basemul4_odd = define
 `basemul4_odd x0 y0 x1 y1 x2 y2 x3 y3 = \i.
  pmul_acc4 (x0 (2 * i)) (x0 (2 * i + 1))
            (y0 (2 * i + 1)) (y0 (2 * i))
            (x1 (2 * i)) (x1 (2 * i + 1))
            (y1 (2 * i + 1)) (y1 (2 * i))
            (x2 (2 * i)) (x2 (2 * i + 1))
            (y2 (2 * i + 1)) (y2 (2 * i))
            (x3 (2 * i)) (x3 (2 * i + 1))
            (y3 (2 * i + 1)) (y3 (2 * i))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** Instantiate a quantified input fact at a particular index, and put   ***)
(*** the address in the form that the simulation will produce            ***)

let BASEMUL_SPECIALIZE_LOAD_TAC (f,idx,tgt) =
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in f (concl th) then
      MP_TAC(SPEC idx th) else failwith "BASEMUL_SPECIALIZE_LOAD_TAC") THEN
  ANTS_TAC THENL
   [W(fun (asl,w) -> MP_TAC(ARITH_RULE (mk_imp(`i < 128`,w)))) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
      let wt = find_term (fun t -> is_comb t && rator t = `word:num->int64`)
                         (lhand(concl th)) in
      ASSUME_TAC(REWRITE_RULE[ARITH_RULE(mk_eq(rand wt,tgt))] th))];;

(*** Prove the congruence for a Montgomery-reduced sum of products ***)

let BASEMUL_CONG_TAC =
  ASSUM_LIST(fun ths -> W(fun (asl,w) ->
    let tm = rand(rand(lhand(rator w))) in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE ths tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2)))) in
    MP_TAC(CONJUNCT1 th3))) THEN
  REWRITE_TAC[basemul4_even; basemul4_odd;
              pmul_acc4; pmull_acc4; pmull; o_THM] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING;;

(*** Unlike mlkem_basemul_k4, this uses X18 as a temporary register ***)

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t pc.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc,libmlkem_size); (srcA, 2048); (srcB, 2048);
          (srcBt, 1024)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_gcc12_O2_mono_mc /\
            read PC s = word (pc + mlk_polyvec_basemul_acc_montgomery_cached_c1024) /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (2 * i)))) s = y0 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (2 * i)))) s = y0t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1536 + 2 * i)))) s = x3 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1536 + 2 * i)))) s = y3 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (768 + 2 * i)))) s = y3t i))
       (\s. read PC s = word (pc + mlk_polyvec_basemul_acc_montgomery_cached_c1024_ret) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12 /\
                       abs(ival(x3 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul4_even
                            (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                            (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                            (ival o y2t) (ival o x3) (ival o y3) (ival o y3t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul4_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2) (ival o x3) (ival o y3)
                            i) (mod &3329))))
       (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                   X12; X13; X14; X15; X16; X17; X18] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`,
  MAP_EVERY X_GEN_TAC
   [`srcA:int64`; `srcB:int64`; `srcBt:int64`; `dst:int64`;
    `x0:num->int16`;
    `y0:num->int16`;
    `y0t:num->int16`;
    `x1:num->int16`;
    `y1:num->int16`;
    `y1t:num->int16`;
    `x2:num->int16`;
    `y2:num->int16`;
    `y2t:num->int16`;
    `x3:num->int16`;
    `y3:num->int16`;
    `y3t:num->int16`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant for the outer loop, with the loop test as a ***)
  (*** separate step. The inner loop has a fixed number of iterations  ***)
  (*** so it is simply unrolled during the simulation.                 ***)

  ENSURES_WHILE_UP_TAC `128` `pc + mlk_polyvec_basemul_acc_montgomery_cached_c1024_loop1`
   `pc + mlk_polyvec_basemul_acc_montgomery_cached_c1024_loop1_test`
   `\i s. read X10 s = word_add srcA (word(4 * i)) /\
          read X13 s = word_add (word_add srcA (word(4 * i))) (word 2) /\
          read X11 s = word_add srcB (word(4 * i)) /\
          read X12 s = word_add (word_add srcB (word(4 * i))) (word 2) /\
          read X14 s = word_add srcBt (word(2 * i)) /\
          read X15 s = word_add dst (word(4 * i)) /\
          read X18 s = word_add srcBt (word 256) /\
          read X17 s = word 4294963969 /\ read X16 s = word 4294963967 /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (2 * i)))) s = x0 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB (word (2 * i)))) s = y0 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (2 * i)))) s = y0t i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (512 + 2 * i)))) s = y2t i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (1536 + 2 * i)))) s = x3 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB (word (1536 + 2 * i)))) s = y3 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (768 + 2 * i)))) s = y3t i) /\
          ((!i. i < 256
                    ==> abs(ival(x0 i)) <= &2 pow 12 /\
                         abs(ival(x1 i)) <= &2 pow 12 /\
                         abs(ival(x2 i)) <= &2 pow 12 /\
                         abs(ival(x3 i)) <= &2 pow 12)
               ==> (!j. j < i
                        ==> (ival(read(memory :> bytes16
                               (word_add dst (word (4 * j)))) s) ==
                             basemul4_even
                              (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                              (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                              (ival o y2t) (ival o x3) (ival o y3) (ival o y3t)
                              j) (mod &3329) /\
                            (ival(read(memory :> bytes16
                               (word_add dst (word (4 * j + 2)))) s) ==
                             basemul4_odd
                              (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                              (ival o x2) (ival o y2) (ival o x3) (ival o y3)
                              j) (mod &3329)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of pointers and constants ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT];

    (*** The loop body, computing two output coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY BASEMUL_SPECIALIZE_LOAD_TAC
     [`x0:num->int16`,`2 * i`,`4 * i`;
      `x0:num->int16`,`2 * i + 1`,`4 * i + 2`;
      `y0:num->int16`,`2 * i`,`4 * i`;
      `y0:num->int16`,`2 * i + 1`,`4 * i + 2`;
      `y0t:num->int16`,`i:num`,`2 * i`;
      `x1:num->int16`,`2 * i`,`4 * i + 512`;
      `x1:num->int16`,`2 * i + 1`,`4 * i + 514`;
      `y1:num->int16`,`2 * i`,`4 * i + 512`;
      `y1:num->int16`,`2 * i + 1`,`4 * i + 514`;
      `y1t:num->int16`,`i:num`,`2 * i + 256`;
      `x2:num->int16`,`2 * i`,`4 * i + 1024`;
      `x2:num->int16`,`2 * i + 1`,`4 * i + 1026`;
      `y2:num->int16`,`2 * i`,`4 * i + 1024`;
      `y2:num->int16`,`2 * i + 1`,`4 * i + 1026`;
      `y2t:num->int16`,`i:num`,`2 * i + 512`;
      `x3:num->int16`,`2 * i`,`4 * i + 1536`;
      `x3:num->int16`,`2 * i + 1`,`4 * i + 1538`;
      `y3:num->int16`,`2 * i`,`4 * i + 1536`;
      `y3:num->int16`,`2 * i + 1`,`4 * i + 1538`;
      `y3t:num->int16`,`i:num`,`2 * i + 768`] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_EXEC (1--80) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`;
                  ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[WORD_ADD_0] THEN REWRITE_TAC[GSYM montred_scalar] THEN
    SUBGOAL_THEN
     `abs(ival(x0(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x0(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x2(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x2(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x3(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x3(2 * i + 1):int16)) <= &2 pow 12`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> 2 * i < 256 /\ 2 * i + 1 < 256`];
      ALL_TAC] THEN
    CONJ_TAC THEN BASEMUL_CONG_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add srcBt (word 256))
                     (word_add srcBt (word (2 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y) = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> 2 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t
    pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc,libmlkem_size); (srcA, 2048); (srcB, 2048);
          (srcBt, 1024)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_gcc12_O2_mono_mc /\
            read PC s = word (pc + mlk_polyvec_basemul_acc_montgomery_cached_c1024) /\
            read X30 s = returnaddress /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (2 * i)))) s = y0 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (2 * i)))) s = y0t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1536 + 2 * i)))) s = x3 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1536 + 2 * i)))) s = y3 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (768 + 2 * i)))) s = y3t i))
       (\s. read PC s = returnaddress /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12 /\
                       abs(ival(x3 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul4_even
                            (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                            (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                            (ival o y2t) (ival o x3) (ival o y3) (ival o y3t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul4_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2) (ival o x3) (ival o y3)
                            i) (mod &3329))))
       (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                   X12; X13; X14; X15; X16; X17; X18] ,,
        MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_EXEC
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_basemul_k4 ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_basemul_k4" subroutine_signatures)
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_EXEC;;

let MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e srcA srcB srcBt dst pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (dst,512))
           [word pc,libmlkem_size; srcA,2048; srcB,2048; srcBt,1024]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlk_polyvec_basemul_acc_montgomery_cached_c1024) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events srcA srcB srcBt dst pc returnaddress /\
                        memaccess_inbounds e2
                         [srcA,2048; srcB,2048; srcBt,1024; dst,512]
                         [dst,512])
               (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                           X11; X12; X13; X14; X15; X16; X17; X18] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes(dst, 512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(srcA:int64) (srcB:int64) (srcBt:int64) (dst:int64) (pc:num)
      (returnaddress:int64).
      APPEND
        (f_ev_epil srcA srcB srcBt dst pc returnaddress)
        (APPEND
          (ENUMERATEL 128
            (\i. f_ev_loop srcA srcB srcBt dst pc returnaddress i))
          (f_ev_prol srcA srcB srcBt dst pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              SOME_FLAGS; ALL;
              fst MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + mlk_polyvec_basemul_acc_montgomery_cached_c1024_loop1`
   `pc + mlk_polyvec_basemul_acc_montgomery_cached_c1024_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X10 s = word_add srcA (word(4 * i)) /\
           read X13 s = word_add (word_add srcA (word(4 * i))) (word 2) /\
           read X11 s = word_add srcB (word(4 * i)) /\
           read X12 s = word_add (word_add srcB (word(4 * i))) (word 2) /\
           read X14 s = word_add srcBt (word(2 * i)) /\
           read X15 s = word_add dst (word(4 * i)) /\
           read X18 s = word_add srcBt (word 256)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_EXEC (1--10) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O2_MONO_EXEC (1--82) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add srcBt (word 256))
                   (word_add (word_add srcBt (word (2 * i))) (word 2))
          :int64) = 0) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
      word_sub x (word_add y z)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 128 ==> 2 * i + 2 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`;
                ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image (see libmlkem.ml).                       *)
(* ------------------------------------------------------------------------- *)

