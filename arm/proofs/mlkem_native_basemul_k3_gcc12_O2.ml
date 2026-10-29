(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of 3-element polynomial vectors in NTT domain.             *)
(* This is the code for mlkem768_polyvec_basemul_acc_montgomery_cached from  *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mlkem_native/README.md).                                             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;

(**** print_literal_from_elf
        "arm/mlkem_native/mlkem_native_basemul_k3_gcc12_O2.o";;
 ****)

let mlkem_native_basemul_k3_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_basemul_k3_gcc12_O2_mc"
  "arm/mlkem_native/mlkem_native_basemul_k3_gcc12_O2.o"
[
  0x91000807;       (* arm_ADD X7 X0 (rvalue (word 2)) *)
  0xaa0103e6;       (* arm_MOV X6 X1 *)
  0x91000845;       (* arm_ADD X5 X2 (rvalue (word 2)) *)
  0x91040071;       (* arm_ADD X17 X3 (rvalue (word 256)) *)
  0x12819fca;       (* arm_MOVN W10 (word 3326) 0 *)
  0x1281a009;       (* arm_MOVN W9 (word 3328) 0 *)
  0xaa0303e1;       (* arm_MOV X1 X3 *)
  0x910008ce;       (* arm_ADD X14 X6 (rvalue (word 2)) *)
  0xd10008ad;       (* arm_SUB X13 X5 (rvalue (word 2)) *)
  0xd2800000;       (* arm_MOV X0 (rvalue (word 0)) *)
  0x52800004;       (* arm_MOV W4 (rvalue (word 0)) *)
  0x52800002;       (* arm_MOV W2 (rvalue (word 0)) *)
  0x78e069d0;       (* arm_LDRSH W16 X14 (Register_Offset X0) *)
  0x91040021;       (* arm_ADD X1 X1 (rvalue (word 256)) *)
  0x78e068cf;       (* arm_LDRSH W15 X6 (Register_Offset X0) *)
  0x78e069a8;       (* arm_LDRSH W8 X13 (Register_Offset X0) *)
  0x78e068ab;       (* arm_LDRSH W11 X5 (Register_Offset X0) *)
  0x91080000;       (* arm_ADD X0 X0 (rvalue (word 512)) *)
  0x78d0002c;       (* arm_LDRSH W12 X1 (Immediate_Offset (word
                       18446744073709551360)) *)
  0x1b087df2;       (* arm_MUL W18 W15 W8 *)
  0x1b087e08;       (* arm_MUL W8 W16 W8 *)
  0x1b10498c;       (* arm_MADD W12 W12 W16 W18 *)
  0x1b0f2168;       (* arm_MADD W8 W11 W15 W8 *)
  0x0b0c0042;       (* arm_ADD W2 W2 W12 *)
  0x0b080084;       (* arm_ADD W4 W4 W8 *)
  0xf118001f;       (* arm_CMP X0 (rvalue (word 1536)) *)
  0x54fffe41;       (* arm_BNE (word 2097096) *)
  0x1b0a7c41;       (* arm_MUL W1 W2 W10 *)
  0x91000863;       (* arm_ADD X3 X3 (rvalue (word 2)) *)
  0x1b0a7c80;       (* arm_MUL W0 W4 W10 *)
  0x910010c6;       (* arm_ADD X6 X6 (rvalue (word 4)) *)
  0x910010a5;       (* arm_ADD X5 X5 (rvalue (word 4)) *)
  0x13003c21;       (* arm_SBFM W1 W1 0 15 *)
  0x13003c00;       (* arm_SBFM W0 W0 0 15 *)
  0x1b090821;       (* arm_MADD W1 W1 W9 W2 *)
  0x1b091000;       (* arm_MADD W0 W0 W9 W4 *)
  0x13107c21;       (* arm_ASR W1 W1 16 *)
  0x781fe0e1;       (* arm_STRH W1 X7 (Immediate_Offset (word
                       18446744073709551614)) *)
  0x13107c00;       (* arm_ASR W0 W0 16 *)
  0x780044e0;       (* arm_STRH W0 X7 (Postimmediate_Offset (word 4)) *)
  0xeb03023f;       (* arm_CMP X17 X3 *)
  0x54fffba1;       (* arm_BNE (word 2097012) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_basemul_k3_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* Definitions used to state specification, as for mlkem_basemul_k3.         *)
(* ------------------------------------------------------------------------- *)

let pmull = define
  `pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;

let pmull_acc3 = define
  `pmull_acc3 (x00: int) (x01 : int) (y00 : int) (y01 : int)
              (x10: int) (x11 : int) (y10 : int) (y11 : int)
              (x20: int) (x21 : int) (y20 : int) (y21 : int) =
              pmull x20 x21 y20 y21 + pmull x10 x11 y10 y11 +
              pmull x00 x01 y00 y01`;;

let pmul_acc3 = define
  `pmul_acc3 (x00: int) (x01 : int) (y00 : int) (y01 : int)
             (x10: int) (x11 : int) (y10 : int) (y11 : int)
             (x20: int) (x21 : int) (y20 : int) (y21 : int) =
             (&(inverse_mod 3329 65536) *
    pmull_acc3 x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21) rem &3329`;;

let basemul3_even = define
 `basemul3_even x0 y0 y0t x1 y1 y1t x2 y2 y2t = \i.
    pmul_acc3 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i)) (y0t i)
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i)) (y1t i)
              (x2 (2 * i)) (x2 (2 * i + 1))
              (y2 (2 * i)) (y2t i)`;;

let basemul3_odd = define
 `basemul3_odd x0 y0 x1 y1 x2 y2 = \i.
   pmul_acc3 (x0 (2 * i)) (x0 (2 * i + 1))
             (y0 (2 * i + 1)) (y0 (2 * i))
             (x1 (2 * i)) (x1 (2 * i + 1))
             (y1 (2 * i + 1)) (y1 (2 * i))
             (x2 (2 * i)) (x2 (2 * i + 1))
             (y2 (2 * i + 1)) (y2 (2 * i))`;;

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
  REWRITE_TAC[basemul3_even; basemul3_odd;
              pmul_acc3; pmull_acc3; pmull; o_THM] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING;;

(*** Unlike mlkem_basemul_k3, this uses X18 as a temporary register ***)

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t pc.
     ALL (nonoverlapping (dst, 512))
         [(word pc, 0xac); (srcA, 1536); (srcB, 1536); (srcBt, 768)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_basemul_k3_gcc12_O2_mc /\
            read PC s = word pc /\
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
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i))
       (\s. read PC s = word (pc + 0xa8) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul3_even
                            (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                            (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                            (ival o y2t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul3_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2)
                            i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
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
    `y2t:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant for the outer loop, with the loop test as a ***)
  (*** separate step. The inner loop has a fixed number of iterations  ***)
  (*** so it is simply unrolled during the simulation.                 ***)

  ENSURES_WHILE_UP_TAC `128` `pc + 0x18` `pc + 0xa0`
   `\i s. read X6 s = word_add srcA (word(4 * i)) /\
          read X5 s = word_add (word_add srcB (word(4 * i))) (word 2) /\
          read X3 s = word_add srcBt (word(2 * i)) /\
          read X7 s = word_add (word_add dst (word(4 * i))) (word 2) /\
          read X17 s = word_add srcBt (word 256) /\
          read X10 s = word 4294963969 /\ read X9 s = word 4294963967 /\
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
          ((!i. i < 256
                    ==> abs(ival(x0 i)) <= &2 pow 12 /\
                         abs(ival(x1 i)) <= &2 pow 12 /\
                         abs(ival(x2 i)) <= &2 pow 12)
               ==> (!j. j < i
                        ==> (ival(read(memory :> bytes16
                               (word_add dst (word (4 * j)))) s) ==
                             basemul3_even
                              (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                              (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                              (ival o y2t)
                              j) (mod &3329) /\
                            (ival(read(memory :> bytes16
                               (word_add dst (word (4 * j + 2)))) s) ==
                             basemul3_odd
                              (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                              (ival o x2) (ival o y2)
                              j) (mod &3329)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of pointers and constants ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--6) THEN
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
      `y2t:num->int16`,`i:num`,`2 * i + 512`] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--64) THEN
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
      abs(ival(x2(2 * i + 1):int16)) <= &2 pow 12`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> 2 * i < 256 /\ 2 * i + 1 < 256`];
      ALL_TAC] THEN
    CONJ_TAC THEN BASEMUL_CONG_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--2) THEN
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
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t pc returnaddress.
     ALL (nonoverlapping (dst, 512))
         [(word pc, 0xac); (srcA, 1536); (srcB, 1536); (srcBt, 768)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_basemul_k3_gcc12_O2_mc /\
            read PC s = word pc /\
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
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i))
       (\s. read PC s = returnaddress /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul3_even
                            (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                            (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                            (ival o y2t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul3_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2)
                            i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_basemul_k3 ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_basemul_k3" subroutine_signatures)
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_CORRECT
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC;;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e srcA srcB srcBt dst pc returnaddress.
           ALL (nonoverlapping (dst,512))
           [word pc,172; srcA,1536; srcB,1536; srcBt,768]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_basemul_k3_gcc12_O2_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events srcA srcB srcBt dst pc returnaddress /\
                        memaccess_inbounds e2
                         [srcA,1536; srcB,1536; srcBt,768; dst,512]
                         [dst,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
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
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + 0x18` `pc + 0xa8`
    `\i s. read X30 s = returnaddress /\
           read X6 s = word_add srcA (word(4 * i)) /\
           read X5 s = word_add (word_add srcB (word(4 * i))) (word 2) /\
           read X3 s = word_add srcBt (word(2 * i)) /\
           read X7 s = word_add (word_add dst (word(4 * i))) (word 2) /\
           read X17 s = word_add srcBt (word 256)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--6) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--66) THEN
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
(* The same code in the whole image, at address 0x5f40 (see                  *)
(* mlkem_native_libmlkem_gcc12_O2.ml).                                       *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_basemul_k3_gcc12_O2_mc
    0x5f40 [];;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc, 0x6480); (srcA, 1536); (srcB, 1536); (srcBt, 768)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_gcc12_O2_mc /\
            read PC s = word (pc + 0x5f40) /\
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
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i))
       (\s. read PC s = returnaddress /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul3_even
                            (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                            (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                            (ival o y2t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul3_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2)
                            i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`,
  MLKEM_NATIVE_IMAGE_TAC
   (INST [`pc + 0x5f40`,`pc:num`]
     (SPEC_ALL MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_CORRECT))
   [MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IN_IMAGE]);;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e srcA srcB srcBt dst pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           ALL (nonoverlapping (dst,512))
           [word pc,0x6480; srcA,1536; srcB,1536; srcBt,768]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x5f40) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events srcA srcB srcBt dst pc returnaddress /\
                        memaccess_inbounds e2
                         [srcA,1536; srcB,1536; srcBt,768; dst,512]
                         [dst,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE [memory :> bytes(dst, 512)])`,
  MLKEM_NATIVE_IMAGE_SAFE_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_SAFE
   [`pc + 0x5f40`,`pc:num`]
   [MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IN_IMAGE]);;
