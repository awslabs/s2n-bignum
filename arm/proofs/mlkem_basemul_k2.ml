(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar multiplication of 2-element polynomial vectors in NTT domain.      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/mlkem.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_basemul_k2.o";;
 ****)

let mlkem_basemul_k2_mc = define_assert_from_elf
 "mlkem_basemul_k2_mc" "arm/mlkem/mlkem_basemul_k2.o"
[
  0xd10103ff;       (* arm_SUB SP SP (rvalue (word 64)) *)
  0x6d0027e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x5281a02e;       (* arm_MOV W14 (rvalue (word 3329)) *)
  0x4e020dc0;       (* arm_DUP_GEN Q0 X14 16 128 *)
  0x52819fee;       (* arm_MOV W14 (rvalue (word 3327)) *)
  0x4e020dc2;       (* arm_DUP_GEN Q2 X14 16 128 *)
  0x91080024;       (* arm_ADD X4 X1 (rvalue (word 512)) *)
  0x91080045;       (* arm_ADD X5 X2 (rvalue (word 512)) *)
  0x91040066;       (* arm_ADD X6 X3 (rvalue (word 256)) *)
  0xd280020d;       (* arm_MOV X13 (rvalue (word 16)) *)
  0x3cc20489;       (* arm_LDR Q9 X4 (Postimmediate_Offset (word 32)) *)
  0x3cdf0085;       (* arm_LDR Q5 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc204ab;       (* arm_LDR Q11 X5 (Postimmediate_Offset (word 32)) *)
  0x4e451937;       (* arm_UZP1 Q23 Q9 Q5 16 *)
  0x4e455929;       (* arm_UZP2 Q9 Q9 Q5 16 *)
  0x3cc20445;       (* arm_LDR Q5 X2 (Postimmediate_Offset (word 32)) *)
  0x3cdf00a7;       (* arm_LDR Q7 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cdf0055;       (* arm_LDR Q21 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e47596a;       (* arm_UZP2 Q10 Q11 Q7 16 *)
  0x4e47196b;       (* arm_UZP1 Q11 Q11 Q7 16 *)
  0x4e5518a7;       (* arm_UZP1 Q7 Q5 Q21 16 *)
  0x4e5558a5;       (* arm_UZP2 Q5 Q5 Q21 16 *)
  0x3cc20435;       (* arm_LDR Q21 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0039;       (* arm_LDR Q25 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x4cdf7466;       (* arm_LDR Q6 X3 (Postimmediate_Offset (word 16)) *)
  0x4e591aba;       (* arm_UZP1 Q26 Q21 Q25 16 *)
  0x4e595ab5;       (* arm_UZP2 Q21 Q21 Q25 16 *)
  0x0e65c359;       (* arm_SMULL_VEC Q25 Q26 Q5 16 *)
  0x4e65c345;       (* arm_SMULL2_VEC Q5 Q26 Q5 16 *)
  0x0e67c353;       (* arm_SMULL_VEC Q19 Q26 Q7 16 *)
  0x4e67c35a;       (* arm_SMULL2_VEC Q26 Q26 Q7 16 *)
  0x0e6782b9;       (* arm_SMLAL_VEC Q25 Q21 Q7 16 *)
  0x4e6782a5;       (* arm_SMLAL2_VEC Q5 Q21 Q7 16 *)
  0x0e6682b3;       (* arm_SMLAL_VEC Q19 Q21 Q6 16 *)
  0x4e6682ba;       (* arm_SMLAL2_VEC Q26 Q21 Q6 16 *)
  0x0e6a82f9;       (* arm_SMLAL_VEC Q25 Q23 Q10 16 *)
  0x4e6a82e5;       (* arm_SMLAL2_VEC Q5 Q23 Q10 16 *)
  0x0e6b82f3;       (* arm_SMLAL_VEC Q19 Q23 Q11 16 *)
  0x4e6b82fa;       (* arm_SMLAL2_VEC Q26 Q23 Q11 16 *)
  0x4cdf74d7;       (* arm_LDR Q23 X6 (Postimmediate_Offset (word 16)) *)
  0x0e6b8139;       (* arm_SMLAL_VEC Q25 Q9 Q11 16 *)
  0x4e6b8125;       (* arm_SMLAL2_VEC Q5 Q9 Q11 16 *)
  0x4e77813a;       (* arm_SMLAL2_VEC Q26 Q9 Q23 16 *)
  0x0e778133;       (* arm_SMLAL_VEC Q19 Q9 Q23 16 *)
  0x3cc20489;       (* arm_LDR Q9 X4 (Postimmediate_Offset (word 32)) *)
  0x4e451b2b;       (* arm_UZP1 Q11 Q25 Q5 16 *)
  0x4e5a1a77;       (* arm_UZP1 Q23 Q19 Q26 16 *)
  0x4e629d6b;       (* arm_MUL_VEC Q11 Q11 Q2 16 128 *)
  0x4e629ef7;       (* arm_MUL_VEC Q23 Q23 Q2 16 128 *)
  0x3cc204a7;       (* arm_LDR Q7 X5 (Postimmediate_Offset (word 32)) *)
  0x4e608165;       (* arm_SMLAL2_VEC Q5 Q11 Q0 16 *)
  0x0e608179;       (* arm_SMLAL_VEC Q25 Q11 Q0 16 *)
  0x3cc2044b;       (* arm_LDR Q11 X2 (Postimmediate_Offset (word 32)) *)
  0x3cdf0055;       (* arm_LDR Q21 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cdf0086;       (* arm_LDR Q6 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e551971;       (* arm_UZP1 Q17 Q11 Q21 16 *)
  0x3cc2042a;       (* arm_LDR Q10 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf003d;       (* arm_LDR Q29 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e55596b;       (* arm_UZP2 Q11 Q11 Q21 16 *)
  0x4e46192d;       (* arm_UZP1 Q13 Q9 Q6 16 *)
  0x4e5d1943;       (* arm_UZP1 Q3 Q10 Q29 16 *)
  0x4e5d594a;       (* arm_UZP2 Q10 Q10 Q29 16 *)
  0x0e6bc06c;       (* arm_SMULL_VEC Q12 Q3 Q11 16 *)
  0x4e6bc06b;       (* arm_SMULL2_VEC Q11 Q3 Q11 16 *)
  0x3cdf00b5;       (* arm_LDR Q21 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e71814c;       (* arm_SMLAL_VEC Q12 Q10 Q17 16 *)
  0x4e71814b;       (* arm_SMLAL2_VEC Q11 Q10 Q17 16 *)
  0x4e5558fd;       (* arm_UZP2 Q29 Q7 Q21 16 *)
  0x4e5518ef;       (* arm_UZP1 Q15 Q7 Q21 16 *)
  0x0e7d81ac;       (* arm_SMLAL_VEC Q12 Q13 Q29 16 *)
  0x4e7d81ab;       (* arm_SMLAL2_VEC Q11 Q13 Q29 16 *)
  0x4e46593c;       (* arm_UZP2 Q28 Q9 Q6 16 *)
  0x4e6082fa;       (* arm_SMLAL2_VEC Q26 Q23 Q0 16 *)
  0x0e6f838c;       (* arm_SMLAL_VEC Q12 Q28 Q15 16 *)
  0x4e6f838b;       (* arm_SMLAL2_VEC Q11 Q28 Q15 16 *)
  0x0e6082f3;       (* arm_SMLAL_VEC Q19 Q23 Q0 16 *)
  0x4e455b3b;       (* arm_UZP2 Q27 Q25 Q5 16 *)
  0x0e71c077;       (* arm_SMULL_VEC Q23 Q3 Q17 16 *)
  0x4e4b1989;       (* arm_UZP1 Q9 Q12 Q11 16 *)
  0x4e5a5a73;       (* arm_UZP2 Q19 Q19 Q26 16 *)
  0x4e629d2e;       (* arm_MUL_VEC Q14 Q9 Q2 16 128 *)
  0x4cdf74d6;       (* arm_LDR Q22 X6 (Postimmediate_Offset (word 16)) *)
  0x4e5b7a69;       (* arm_ZIP2 Q9 Q19 Q27 16 128 *)
  0x4e6081cb;       (* arm_SMLAL2_VEC Q11 Q14 Q0 16 *)
  0x4cdf7464;       (* arm_LDR Q4 X3 (Postimmediate_Offset (word 16)) *)
  0xd10009ad;       (* arm_SUB X13 X13 (rvalue (word 2)) *)
  0x4e71c074;       (* arm_SMULL2_VEC Q20 Q3 Q17 16 *)
  0x3cc20492;       (* arm_LDR Q18 X4 (Postimmediate_Offset (word 32)) *)
  0x3cc204be;       (* arm_LDR Q30 X5 (Postimmediate_Offset (word 32)) *)
  0x4e648154;       (* arm_SMLAL2_VEC Q20 Q10 Q4 16 *)
  0x0e6081cc;       (* arm_SMLAL_VEC Q12 Q14 Q0 16 *)
  0x0e648157;       (* arm_SMLAL_VEC Q23 Q10 Q4 16 *)
  0x3d800409;       (* arm_STR Q9 X0 (Immediate_Offset (word 16)) *)
  0x4e6f81b4;       (* arm_SMLAL2_VEC Q20 Q13 Q15 16 *)
  0x3cc20448;       (* arm_LDR Q8 X2 (Postimmediate_Offset (word 32)) *)
  0x0e6f81b7;       (* arm_SMLAL_VEC Q23 Q13 Q15 16 *)
  0x4e768394;       (* arm_SMLAL2_VEC Q20 Q28 Q22 16 *)
  0x4e5b3a7a;       (* arm_ZIP1 Q26 Q19 Q27 16 128 *)
  0x3cdf0049;       (* arm_LDR Q9 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e768397;       (* arm_SMLAL_VEC Q23 Q28 Q22 16 *)
  0x4e4b599b;       (* arm_UZP2 Q27 Q12 Q11 16 *)
  0x4e491911;       (* arm_UZP1 Q17 Q8 Q9 16 *)
  0x4e495904;       (* arm_UZP2 Q4 Q8 Q9 16 *)
  0x4e541ae5;       (* arm_UZP1 Q5 Q23 Q20 16 *)
  0x3c82041a;       (* arm_STR Q26 X0 (Postimmediate_Offset (word 32)) *)
  0x4e629cbf;       (* arm_MUL_VEC Q31 Q5 Q2 16 128 *)
  0x3cdf0093;       (* arm_LDR Q19 X4 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cc2043d;       (* arm_LDR Q29 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf002c;       (* arm_LDR Q12 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e6083f4;       (* arm_SMLAL2_VEC Q20 Q31 Q0 16 *)
  0x4e531a4d;       (* arm_UZP1 Q13 Q18 Q19 16 *)
  0x4e4c1ba3;       (* arm_UZP1 Q3 Q29 Q12 16 *)
  0x4e4c5baa;       (* arm_UZP2 Q10 Q29 Q12 16 *)
  0x0e64c06c;       (* arm_SMULL_VEC Q12 Q3 Q4 16 *)
  0x4e64c06b;       (* arm_SMULL2_VEC Q11 Q3 Q4 16 *)
  0x3cdf00a5;       (* arm_LDR Q5 X5 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e71814c;       (* arm_SMLAL_VEC Q12 Q10 Q17 16 *)
  0x4e71814b;       (* arm_SMLAL2_VEC Q11 Q10 Q17 16 *)
  0x4e455bce;       (* arm_UZP2 Q14 Q30 Q5 16 *)
  0x4e451bcf;       (* arm_UZP1 Q15 Q30 Q5 16 *)
  0x0e6e81ac;       (* arm_SMLAL_VEC Q12 Q13 Q14 16 *)
  0x4e6e81ab;       (* arm_SMLAL2_VEC Q11 Q13 Q14 16 *)
  0x4e535a5c;       (* arm_UZP2 Q28 Q18 Q19 16 *)
  0x0e6083f7;       (* arm_SMLAL_VEC Q23 Q31 Q0 16 *)
  0x0e6f838c;       (* arm_SMLAL_VEC Q12 Q28 Q15 16 *)
  0x4e6f838b;       (* arm_SMLAL2_VEC Q11 Q28 Q15 16 *)
  0x4cdf74d6;       (* arm_LDR Q22 X6 (Postimmediate_Offset (word 16)) *)
  0x4e545af3;       (* arm_UZP2 Q19 Q23 Q20 16 *)
  0x4e4b1981;       (* arm_UZP1 Q1 Q12 Q11 16 *)
  0x0e71c077;       (* arm_SMULL_VEC Q23 Q3 Q17 16 *)
  0x4e629c2e;       (* arm_MUL_VEC Q14 Q1 Q2 16 128 *)
  0x4e5b7a69;       (* arm_ZIP2 Q9 Q19 Q27 16 128 *)
  0x4cdf7464;       (* arm_LDR Q4 X3 (Postimmediate_Offset (word 16)) *)
  0x4e6081cb;       (* arm_SMLAL2_VEC Q11 Q14 Q0 16 *)
  0xd10005ad;       (* arm_SUB X13 X13 (rvalue (word 1)) *)
  0xb5fff9ed;       (* arm_CBNZ X13 (word 2096956) *)
  0x4e71c065;       (* arm_SMULL2_VEC Q5 Q3 Q17 16 *)
  0x0e6081cc;       (* arm_SMLAL_VEC Q12 Q14 Q0 16 *)
  0x0e648157;       (* arm_SMLAL_VEC Q23 Q10 Q4 16 *)
  0x3d800409;       (* arm_STR Q9 X0 (Immediate_Offset (word 16)) *)
  0x4e648145;       (* arm_SMLAL2_VEC Q5 Q10 Q4 16 *)
  0x4e4b598b;       (* arm_UZP2 Q11 Q12 Q11 16 *)
  0x4e5b3a69;       (* arm_ZIP1 Q9 Q19 Q27 16 128 *)
  0x0e6f81b7;       (* arm_SMLAL_VEC Q23 Q13 Q15 16 *)
  0x4e6f81a5;       (* arm_SMLAL2_VEC Q5 Q13 Q15 16 *)
  0x3c820409;       (* arm_STR Q9 X0 (Postimmediate_Offset (word 32)) *)
  0x0e768397;       (* arm_SMLAL_VEC Q23 Q28 Q22 16 *)
  0x4e768385;       (* arm_SMLAL2_VEC Q5 Q28 Q22 16 *)
  0x4e451ae9;       (* arm_UZP1 Q9 Q23 Q5 16 *)
  0x4e629d29;       (* arm_MUL_VEC Q9 Q9 Q2 16 128 *)
  0x4e608125;       (* arm_SMLAL2_VEC Q5 Q9 Q0 16 *)
  0x0e608137;       (* arm_SMLAL_VEC Q23 Q9 Q0 16 *)
  0x4e455ae9;       (* arm_UZP2 Q9 Q23 Q5 16 *)
  0x4e4b7925;       (* arm_ZIP2 Q5 Q9 Q11 16 128 *)
  0x4e4b3929;       (* arm_ZIP1 Q9 Q9 Q11 16 128 *)
  0x3d800405;       (* arm_STR Q5 X0 (Immediate_Offset (word 16)) *)
  0x3c820409;       (* arm_STR Q9 X0 (Postimmediate_Offset (word 32)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_BASEMUL_K2_EXEC = ARM_MK_EXEC_RULE mlkem_basemul_k2_mc;;

(* ------------------------------------------------------------------------- *)
(* Definitions used to state specification.                                  *)
(* ------------------------------------------------------------------------- *)

let pmull = define
  `pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;

let pmull_acc2 = define
    `pmull_acc2 (x00: int) (x01 : int) (y00 : int) (y01 : int)
          (x10: int) (x11 : int) (y10 : int) (y11 : int) =
      pmull x10 x11 y10 y11 + pmull x00 x01 y00 y01`;;

let pmul_acc2 = define
    `pmul_acc2 (x00: int) (x01 : int) (y00 : int) (y01 : int)
          (x10: int) (x11 : int) (y10 : int) (y11 : int) =
     (&(inverse_mod 3329 65536) *
      pmull_acc2 x00 x01 y00 y01 x10 x11 y10 y11) rem &3329`;;

let basemul2_even = define
   `basemul2_even x0 y0 y0t x1 y1 y1t = \i.
      pmul_acc2 (x0 (2 * i)) (x0 (2 * i + 1))
                (y0 (2 * i)) (y0t i)
                (x1 (2 * i)) (x1 (2 * i + 1))
                (y1 (2 * i)) (y1t i)`;;

let basemul2_odd = define
 `basemul2_odd x0 y0 x1 y1 = \i.
    pmul_acc2 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i + 1)) (y0 (2 * i))
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i + 1)) (y1 (2 * i))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_BASEMUL_K2_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc.
     ALL (nonoverlapping (dst, 512))
         [(word pc, LENGTH mlkem_basemul_k2_mc);
          (srcA, 1024); (srcB, 1024); (srcBt, 512)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc) mlkem_basemul_k2_mc /\
            read PC s = word (pc + 0x14)  /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB  (word (2 * i)))) s = y0 i) /\
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
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i))
       (\s. read PC s = word (pc + 0x280) /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                      abs(ival(x1 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                         (ival o x1) (ival o y1) (ival o y1t)
                                         i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul2_odd (ival o x0) (ival o y0) (ival o x1)
                           (ival o y1) i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`,
  REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS;
    NONOVERLAPPING_CLAUSES; ALL; C_ARGUMENTS; fst MLKEM_BASEMUL_K2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (* Split quantified assumptions into separate cases *)
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
           ONCE_DEPTH_CONV NUM_ADD_CONV) THEN

  (* Initialize symbolic execution *)
  ENSURES_INIT_TAC "s0" THEN

  (* Rewrite memory-read assumptions from 16-bit granularity
   * to 128-bit granularity. *)
  MEMORY_128_FROM_16_TAC "srcA" 64 THEN
  MEMORY_128_FROM_16_TAC "srcB" 64 THEN
  MEMORY_128_FROM_16_TAC "srcBt" 32 THEN
  ASM_REWRITE_TAC [WORD_ADD_0] THEN
  (* Forget original shape of assumption *)
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 any) s = x`] THEN

  (* Symbolic execution
     Note that we simplify eagerly after every step.
     This reduces the proof time *)
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_BASEMUL_K2_EXEC [n] THEN
             (SIMD_SIMPLIFY_TAC [montred])) (1--805) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN
  ASM_REWRITE_TAC [] THEN

  (* Reverse restructuring *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE (SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (* Split quantified post-condition into separate cases *)
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV
           THENC (TRY_CONV (ONCE_DEPTH_CONV NUM_ADD_CONV))) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC [WORD_ADD_0] THEN

  (* Forget all state-related assumptions, but keep bounds at least *)
  DISCARD_STATE_TAC "s805" THEN

  (* Split into one congruence goal per index. *)
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[basemul2_even; basemul2_odd;
              pmul_acc2; pmull_acc2; pmull; o_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN

  (* Solve the congruence goals *)

  ASSUM_LIST((fun ths -> W(MP_TAC o CONJUNCT1 o GEN_CONGBOUND_RULE ths o
    rand o lhand o rator o snd))) THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING);;

let MLKEM_BASEMUL_K2_SUBROUTINE_CORRECT = prove
 (`!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(dst, 512); (word_sub stackpointer (word 64),64)]
        [(word pc, LENGTH mlkem_basemul_k2_mc); (srcA, 1024);
         (srcB, 1024); (srcBt, 512)] /\
      nonoverlapping (dst,512) (word_sub stackpointer (word 64),64)
      ==>
      ensures arm
       (\s. // Assert that mlkem_basemul_k2 is loaded at PC
            aligned_bytes_loaded s (word pc) mlkem_basemul_k2_mc /\
            read PC s = word pc /\
            read SP s = stackpointer /\
            read X30 s = returnaddress /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            // Give names to in-memory data to be
            // able to refer to them in the post-condition
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB  (word (2 * i)))) s = y0 i) /\
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
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i)
       )
       (\s. read PC s = returnaddress /\
            ((!i. i < 256
                 ==> abs(ival(x0 i)) <= &2 pow 12 /\
                     abs(ival(x1 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                         (ival o x1) (ival o y1) (ival o y1t)
                                         i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul2_odd (ival o x0) (ival o y0) (ival o x1)
                           (ival o y1) i) (mod &3329)))
      )
      // Register and memory footprint
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(dst, 512);
                 memory :> bytes(word_sub stackpointer (word 64),64)])`,
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) MLKEM_BASEMUL_K2_EXEC
     (REWRITE_RULE[fst MLKEM_BASEMUL_K2_EXEC] MLKEM_BASEMUL_K2_CORRECT)
      `[D8; D9; D10; D11; D12; D13; D14; D15]` 64  THEN
   WORD_ARITH_TAC);;
