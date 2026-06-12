(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform rejection sampling for ML-DSA, filtering packed numbers < Q.      *)
(*                                                                           *)
(* ML-DSA uses q = 8380417 with 23-bit coefficients packed as 3 bytes each.  *)
(* The assembly processes 48 bytes (16 coefficients) per main-loop iteration *)
(* and stores accepted coefficients as 32-bit words.                         *)
(* ========================================================================= *)

(* Load base theories for AArch64 from s2n-bignum *)
needs "arm/proofs/base.ml";;

needs "common/mlkem_mldsa.ml";;

(* Table definition inlined from mldsa_rej_uniform_table.ml *)

let mldsa_rej_uniform_table = (REWRITE_RULE[MAP] o define)
  `mldsa_rej_uniform_table:byte list = MAP word [
  255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255;
    0;   1;   2;   3; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255;
    4;   5;   6;   7; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255;
    0;   1;   2;   3;   4;   5;   6;   7; 255; 255; 255; 255; 255; 255; 255; 255;
    8;   9;  10;  11; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255;
    0;   1;   2;   3;   8;   9;  10;  11; 255; 255; 255; 255; 255; 255; 255; 255;
    4;   5;   6;   7;   8;   9;  10;  11; 255; 255; 255; 255; 255; 255; 255; 255;
    0;   1;   2;   3;   4;   5;   6;   7;   8;   9;  10;  11; 255; 255; 255; 255;
   12;  13;  14;  15; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255; 255;
    0;   1;   2;   3;  12;  13;  14;  15; 255; 255; 255; 255; 255; 255; 255; 255;
    4;   5;   6;   7;  12;  13;  14;  15; 255; 255; 255; 255; 255; 255; 255; 255;
    0;   1;   2;   3;   4;   5;   6;   7;  12;  13;  14;  15; 255; 255; 255; 255;
    8;   9;  10;  11;  12;  13;  14;  15; 255; 255; 255; 255; 255; 255; 255; 255;
    0;   1;   2;   3;   8;   9;  10;  11;  12;  13;  14;  15; 255; 255; 255; 255;
    4;   5;   6;   7;   8;   9;  10;  11;  12;  13;  14;  15; 255; 255; 255; 255;
    0;   1;   2;   3;   4;   5;   6;   7;   8;   9;  10;  11;  12;  13;  14;  15
  ]`;;

(* Utility for executing until target PC is reached *)
let MAP_UNTIL_TARGET_PC f n = fun (asl, w) ->
  let is_pc_condition = can (term_match [] `read PC some_state = some_value`) in
  let extract_target_pc_from_goal goal =
    let _, insts, _ = term_match [] `eventually arm (\s'. P) some_state` goal in
    insts |> rev_assoc `P: bool` |> conjuncts |> find is_pc_condition in
  let extract_pc_assumption asl =
    try Some (find (is_pc_condition o concl o snd) asl |> snd |> concl) with _ -> None in
  let has_matching_pc_assumption asl target_pc =
    match extract_pc_assumption asl with
     | None -> false
     | Some(asm) -> can (term_match [`returnaddress: 64 word`; `pc: num`] target_pc) asm in
  let target_pc = extract_target_pc_from_goal w in
  let TARGET_PC_REACHED_TAC target_pc = fun (asl, w) ->
    if has_matching_pc_assumption asl target_pc then ALL_TAC (asl, w)
    else NO_TAC (asl, w) in
  let rec core n (asl, w) =
    (TARGET_PC_REACHED_TAC target_pc ORELSE (f n THEN core (n + 1))) (asl, w)
  in core n (asl, w);;

(**** print_literal_from_elf "arm/mldsa/mldsa_rej_uniform_VARIABLE_TIME.o";;
 ****)

let mldsa_rej_uniform_mc = define_assert_from_elf
  "mldsa_rej_uniform_mc" "arm/mldsa/mldsa_rej_uniform_VARIABLE_TIME.o"
(*** BYTECODE START ***)
[
  0xd11103ff;       (* arm_SUB SP SP (rvalue (word 1088)) *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0xf2c00047;       (* arm_MOVK X7 (word 2) 32 *)
  0x4e081cff;       (* arm_INS_GEN Q31 X7 0 64 *)
  0xd2800087;       (* arm_MOV X7 (rvalue (word 4)) *)
  0xf2c00107;       (* arm_MOVK X7 (word 8) 32 *)
  0x4e181cff;       (* arm_INS_GEN Q31 X7 64 64 *)
  0x529c0027;       (* arm_MOV W7 (rvalue (word 57345)) *)
  0x72a00fe7;       (* arm_MOVK W7 (word 127) 16 *)
  0x4e040cfe;       (* arm_DUP_GEN Q30 X7 32 128 *)
  0x910003e8;       (* arm_ADD X8 SP (rvalue (word 0)) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0xd280000b;       (* arm_MOV X11 (rvalue (word 0)) *)
  0x6e301e10;       (* arm_EOR_VEC Q16 Q16 Q16 128 *)
  0x3c8404f0;       (* arm_STR Q16 X7 (Postimmediate_Offset (word 64)) *)
  0x3c9d00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x9100416b;       (* arm_ADD X11 X11 (rvalue (word 16)) *)
  0xf104017f;       (* arm_CMP X11 (rvalue (word 256)) *)
  0x54ffff4b;       (* arm_BLT (word 2097128) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0xd2800009;       (* arm_MOV X9 (rvalue (word 0)) *)
  0xd2802004;       (* arm_MOV X4 (rvalue (word 256)) *)
  0xf100c05f;       (* arm_CMP X2 (rvalue (word 48)) *)
  0x54000823;       (* arm_BCC (word 260) *)
  0xeb04013f;       (* arm_CMP X9 X4 *)
  0x54000c62;       (* arm_BCS (word 396) *)
  0xd100c042;       (* arm_SUB X2 X2 (rvalue (word 48)) *)
  0x4cdf4020;       (* arm_LD3 [Q0; Q1; Q2] X1 (Postimmediate_Offset (word 48)) 128 8 *)
  0x4f04e404;       (* UNSUPPORTED: movi v4.16b, #0x80 *)
  0x4e641c42;       (* arm_BIC_VEC Q2 Q2 Q4 128 *)
  0x4e013804;       (* arm_ZIP1 Q4 Q0 Q1 8 128 *)
  0x4e017805;       (* arm_ZIP2 Q5 Q0 Q1 8 128 *)
  0x2f08a446;       (* UNSUPPORTED: ushll v6.8h, v2.8b, #0 *)
  0x6f08a447;       (* UNSUPPORTED: ushll2 v7.8h, v2.16b, #0 *)
  0x4e463890;       (* arm_ZIP1 Q16 Q4 Q6 16 128 *)
  0x4e467891;       (* arm_ZIP2 Q17 Q4 Q6 16 128 *)
  0x4e4738b2;       (* arm_ZIP1 Q18 Q5 Q7 16 128 *)
  0x4e4778b3;       (* arm_ZIP2 Q19 Q5 Q7 16 128 *)
  0x6eb037c4;       (* arm_CMHI_VEC Q4 Q30 Q16 32 128 *)
  0x6eb137c5;       (* arm_CMHI_VEC Q5 Q30 Q17 32 128 *)
  0x6eb237c6;       (* arm_CMHI_VEC Q6 Q30 Q18 32 128 *)
  0x6eb337c7;       (* arm_CMHI_VEC Q7 Q30 Q19 32 128 *)
  0x4e3f1c84;       (* arm_AND_VEC Q4 Q4 Q31 128 *)
  0x4e3f1ca5;       (* arm_AND_VEC Q5 Q5 Q31 128 *)
  0x4e3f1cc6;       (* arm_AND_VEC Q6 Q6 Q31 128 *)
  0x4e3f1ce7;       (* arm_AND_VEC Q7 Q7 Q31 128 *)
  0x6eb03894;       (* arm_UADDLV Q20 Q4 32 64 *)
  0x6eb038b5;       (* arm_UADDLV Q21 Q5 32 64 *)
  0x6eb038d6;       (* arm_UADDLV Q22 Q6 32 64 *)
  0x6eb038f7;       (* arm_UADDLV Q23 Q7 32 64 *)
  0x9e66028c;       (* UNSUPPORTED: fmov x12, d20 *)
  0x9e6602ad;       (* UNSUPPORTED: fmov x13, d21 *)
  0x9e6602ce;       (* UNSUPPORTED: fmov x14, d22 *)
  0x9e6602ef;       (* UNSUPPORTED: fmov x15, d23 *)
  0x3cec7878;       (* arm_LDR Q24 X3 (Shiftreg_Offset X12 4) *)
  0x3ced7879;       (* arm_LDR Q25 X3 (Shiftreg_Offset X13 4) *)
  0x3cee787a;       (* arm_LDR Q26 X3 (Shiftreg_Offset X14 4) *)
  0x3cef787b;       (* arm_LDR Q27 X3 (Shiftreg_Offset X15 4) *)
  0x4e205884;       (* arm_CNT Q4 Q4 128 *)
  0x4e2058a5;       (* arm_CNT Q5 Q5 128 *)
  0x4e2058c6;       (* arm_CNT Q6 Q6 128 *)
  0x4e2058e7;       (* arm_CNT Q7 Q7 128 *)
  0x6eb03894;       (* arm_UADDLV Q20 Q4 32 64 *)
  0x6eb038b5;       (* arm_UADDLV Q21 Q5 32 64 *)
  0x6eb038d6;       (* arm_UADDLV Q22 Q6 32 64 *)
  0x6eb038f7;       (* arm_UADDLV Q23 Q7 32 64 *)
  0x9e66028c;       (* UNSUPPORTED: fmov x12, d20 *)
  0x9e6602ad;       (* UNSUPPORTED: fmov x13, d21 *)
  0x9e6602ce;       (* UNSUPPORTED: fmov x14, d22 *)
  0x9e6602ef;       (* UNSUPPORTED: fmov x15, d23 *)
  0x4e180210;       (* arm_TBL Q16 [Q16] Q24 128 *)
  0x4e190231;       (* arm_TBL Q17 [Q17] Q25 128 *)
  0x4e1a0252;       (* arm_TBL Q18 [Q18] Q26 128 *)
  0x4e1b0273;       (* arm_TBL Q19 [Q19] Q27 128 *)
  0x4c0078f0;       (* UNSUPPORTED: st1 {v16.4s}, [x7] *)
  0x8b0c08e7;       (* arm_ADD X7 X7 (Shiftedreg X12 LSL 2) *)
  0x4c0078f1;       (* UNSUPPORTED: st1 {v17.4s}, [x7] *)
  0x8b0d08e7;       (* arm_ADD X7 X7 (Shiftedreg X13 LSL 2) *)
  0x4c0078f2;       (* UNSUPPORTED: st1 {v18.4s}, [x7] *)
  0x8b0e08e7;       (* arm_ADD X7 X7 (Shiftedreg X14 LSL 2) *)
  0x4c0078f3;       (* UNSUPPORTED: st1 {v19.4s}, [x7] *)
  0x8b0f08e7;       (* arm_ADD X7 X7 (Shiftedreg X15 LSL 2) *)
  0x8b0d018c;       (* arm_ADD X12 X12 X13 *)
  0x8b0f01ce;       (* arm_ADD X14 X14 X15 *)
  0x8b0c0129;       (* arm_ADD X9 X9 X12 *)
  0x8b0e0129;       (* arm_ADD X9 X9 X14 *)
  0xf100c05f;       (* arm_CMP X2 (rvalue (word 48)) *)
  0x54fff822;       (* arm_BCS (word 2096900) *)
  0xeb04013f;       (* arm_CMP X9 X4 *)
  0x54000462;       (* arm_BCS (word 140) *)
  0xf100605f;       (* arm_CMP X2 (rvalue (word 24)) *)
  0x54000423;       (* arm_BCC (word 132) *)
  0xd1006042;       (* arm_SUB X2 X2 (rvalue (word 24)) *)
  0x0cdf4020;       (* arm_LD3 [Q0; Q1; Q2] X1 (Postimmediate_Offset (word 24)) 64 8 *)
  0x4f04e404;       (* UNSUPPORTED: movi v4.16b, #0x80 *)
  0x4e641c42;       (* arm_BIC_VEC Q2 Q2 Q4 128 *)
  0x4e013804;       (* arm_ZIP1 Q4 Q0 Q1 8 128 *)
  0x2f08a446;       (* UNSUPPORTED: ushll v6.8h, v2.8b, #0 *)
  0x4e463890;       (* arm_ZIP1 Q16 Q4 Q6 16 128 *)
  0x4e467891;       (* arm_ZIP2 Q17 Q4 Q6 16 128 *)
  0x6eb037c4;       (* arm_CMHI_VEC Q4 Q30 Q16 32 128 *)
  0x6eb137c5;       (* arm_CMHI_VEC Q5 Q30 Q17 32 128 *)
  0x4e3f1c84;       (* arm_AND_VEC Q4 Q4 Q31 128 *)
  0x4e3f1ca5;       (* arm_AND_VEC Q5 Q5 Q31 128 *)
  0x6eb03894;       (* arm_UADDLV Q20 Q4 32 64 *)
  0x6eb038b5;       (* arm_UADDLV Q21 Q5 32 64 *)
  0x9e66028c;       (* UNSUPPORTED: fmov x12, d20 *)
  0x9e6602ad;       (* UNSUPPORTED: fmov x13, d21 *)
  0x3cec7878;       (* arm_LDR Q24 X3 (Shiftreg_Offset X12 4) *)
  0x3ced7879;       (* arm_LDR Q25 X3 (Shiftreg_Offset X13 4) *)
  0x4e205884;       (* arm_CNT Q4 Q4 128 *)
  0x4e2058a5;       (* arm_CNT Q5 Q5 128 *)
  0x6eb03894;       (* arm_UADDLV Q20 Q4 32 64 *)
  0x6eb038b5;       (* arm_UADDLV Q21 Q5 32 64 *)
  0x9e66028c;       (* UNSUPPORTED: fmov x12, d20 *)
  0x9e6602ad;       (* UNSUPPORTED: fmov x13, d21 *)
  0x4e180210;       (* arm_TBL Q16 [Q16] Q24 128 *)
  0x4e190231;       (* arm_TBL Q17 [Q17] Q25 128 *)
  0x3d8000f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 0)) *)
  0x8b0c08e7;       (* arm_ADD X7 X7 (Shiftedreg X12 LSL 2) *)
  0x3d8000f1;       (* arm_STR Q17 X7 (Immediate_Offset (word 0)) *)
  0x8b0d08e7;       (* arm_ADD X7 X7 (Shiftedreg X13 LSL 2) *)
  0x8b0c0129;       (* arm_ADD X9 X9 X12 *)
  0x8b0d0129;       (* arm_ADD X9 X9 X13 *)
  0xeb04013f;       (* arm_CMP X9 X4 *)
  0x9a843129;       (* arm_CSEL X9 X9 X4 Condition_CC *)
  0xd280000b;       (* arm_MOV X11 (rvalue (word 0)) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0x3cc404f0;       (* arm_LDR Q16 X7 (Postimmediate_Offset (word 64)) *)
  0x3cdd00f1;       (* arm_LDR Q17 X7 (Immediate_Offset (word 18446744073709551568)) *)
  0x3cde00f2;       (* arm_LDR Q18 X7 (Immediate_Offset (word 18446744073709551584)) *)
  0x3cdf00f3;       (* arm_LDR Q19 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x3c840410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 64)) *)
  0x3c9d0011;       (* arm_STR Q17 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e0012;       (* arm_STR Q18 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f0013;       (* arm_STR Q19 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x9100416b;       (* arm_ADD X11 X11 (rvalue (word 16)) *)
  0xf104017f;       (* arm_CMP X11 (rvalue (word 256)) *)
  0x54fffecb;       (* arm_BLT (word 2097112) *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x14000001;       (* arm_B (word 4) *)
  0x911103ff;       (* arm_ADD SP SP (rvalue (word 1088)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLDSA_REJ_UNIFORM_EXEC = ARM_MK_EXEC_RULE mldsa_rej_uniform_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLDSA_REJ_UNIFORM_MC =
  REWRITE_CONV[mldsa_rej_uniform_mc] `LENGTH mldsa_rej_uniform_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLDSA_REJ_UNIFORM_PREAMBLE_LENGTH = new_definition
  `MLDSA_REJ_UNIFORM_PREAMBLE_LENGTH = 4`;;

let MLDSA_REJ_UNIFORM_POSTAMBLE_LENGTH = new_definition
  `MLDSA_REJ_UNIFORM_POSTAMBLE_LENGTH = 8`;;

let MLDSA_REJ_UNIFORM_CORE_START = new_definition
  `MLDSA_REJ_UNIFORM_CORE_START = MLDSA_REJ_UNIFORM_PREAMBLE_LENGTH`;;

let MLDSA_REJ_UNIFORM_CORE_END = new_definition
  `MLDSA_REJ_UNIFORM_CORE_END = LENGTH mldsa_rej_uniform_mc - MLDSA_REJ_UNIFORM_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLDSA_REJ_UNIFORM_MC;
              MLDSA_REJ_UNIFORM_CORE_START; MLDSA_REJ_UNIFORM_CORE_END;
              MLDSA_REJ_UNIFORM_PREAMBLE_LENGTH; MLDSA_REJ_UNIFORM_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* General wordlist helpers (same as ML-KEM proof)                           *)
(* ------------------------------------------------------------------------- *)

let num_of_wordlist = define
 `num_of_wordlist [] = 0 /\
  num_of_wordlist (CONS (h:N word) t) =
     val h + 2 EXP dimindex(:N) * num_of_wordlist t`;;

let NUM_OF_WORDLIST_SING = prove
 (`!h:N word. num_of_wordlist [h] = val h`,
  REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_APPEND = prove
 (`!lis1 lis2:(N word)list.
        num_of_wordlist(APPEND lis1 lis2) =
        num_of_wordlist lis1 +
        2 EXP (dimindex(:N) * LENGTH lis1) * num_of_wordlist lis2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; num_of_wordlist] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
  REWRITE_TAC[EXP_ADD] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND_LENGTH = prove
 (`!l:(N word)list. num_of_wordlist l < 2 EXP (dimindex(:N) * LENGTH l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; num_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; EXP_ADD; ARITH] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o lhand o snd) THEN
  MATCH_MP_TAC(ARITH_RULE
   `n * (x + 1) <= y ==> h < n ==> h + n * x < y`) THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND = prove
 (`!l:(N word)list n.
        LENGTH l <= n ==> num_of_wordlist l < 2 EXP (dimindex(:N) * n)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LTE_TRANS `2 EXP (dimindex(:N) * LENGTH(l:(N word)list))` THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_BOUND_LENGTH; LE_EXP; LE_MULT_LCANCEL] THEN
  ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND_GEN = prove
 (`!l:((N word)list) n.
        dimindex(:N) * LENGTH l <= n ==> num_of_wordlist l < 2 EXP n`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand NUM_OF_WORDLIST_BOUND_LENGTH o
    lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LTE_TRANS) THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_SUB_LIST_0 = prove
 (`!(l:(N word)list) n.
        num_of_wordlist(SUB_LIST(0,n) l) =
        num_of_wordlist l MOD 2 EXP (dimindex(:N) * n)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist; DIV_0; MOD_0] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[EXP_ADD] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN MATCH_MP_TAC(ARITH_RULE
     `h < n /\ n * (t + 1) <= n * e
      ==> h + n * t < n * e`) THEN
    REWRITE_TAC[VAL_BOUND; LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`; MOD_LT_EQ] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    MATCH_MP_TAC(NUMBER_RULE
     `(t == t') (mod d)
      ==> (h + e * t == h + e * t') (mod (e * d))`) THEN
    REWRITE_TAC[CONG_RMOD; CONG_REFL]]);;

let NUM_OF_WORDLIST_SUB_LIST = prove
 (`!(l:(N word)list) m n.
        num_of_wordlist (SUB_LIST(m,n) l) =
        (num_of_wordlist l DIV 2 EXP (dimindex(:N) * m)) MOD
        2 EXP (dimindex(:N) * n)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist; DIV_0; MOD_0] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST_0; GSYM(CONJUNCT2 num_of_wordlist);
              EXP; DIV_1; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist] THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN X_GEN_TAC `n:num` THEN
  SIMP_TAC[EXP_ADD; GSYM DIV_DIV; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; VAL_BOUND; ADD_CLAUSES]);;

let SUB_LIST_REFL = prove
 (`!(l:A list) n. LENGTH l <= n ==> SUB_LIST(0,n) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_LIST_CLAUSES] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; LE_SUC; LENGTH] THEN
  ARITH_TAC);;

let SUB_LIST_1 = prove
 (`!(l:A list) n. SUB_LIST(n,1) l = if n < LENGTH l then [EL n l] else []`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; SUB_LIST_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`h:A`; `t:A list`] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; LT_0; num_CONV `1`; EL; TL] THEN
  ASM_REWRITE_TAC[GSYM(num_CONV `1`); LT_SUC; HD]);;

let SUB_LIST_APPEND_LEFT = prove
 (`!(l:A list) m n.
        n <= LENGTH l ==> SUB_LIST(0,n) (APPEND l m) = SUB_LIST(0,n) l`,
  LIST_INDUCT_TAC THEN
  SIMP_TAC[LENGTH; CONJUNCT1 LE; SUB_LIST_CLAUSES] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; APPEND; LE_SUC]);;

let NUM_OF_WORDLIST_EL = prove
 (`!(l:(N word)list) m.
        (num_of_wordlist l DIV 2 EXP (dimindex(:N) * m)) MOD
        2 EXP (dimindex(:N)) =
        if m < LENGTH l then val(EL m l) else 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`l:(N word)list`; `m:num`; `1`]
   NUM_OF_WORDLIST_SUB_LIST) THEN
  REWRITE_TAC[SUB_LIST_1; MULT_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN COND_CASES_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SING; num_of_wordlist]);;

let pair_wordlist = define
 `(!hi (lo:N word) rest.
     pair_wordlist (CONS lo (CONS hi rest)) =
     CONS (word_join hi lo:((N)tybit0)word) (pair_wordlist rest)) /\
  (!w. pair_wordlist [w] = [word_join (word 0:N word) w]) /\
  pair_wordlist [] = []`;;

let NUM_OF_PAIR_WORDLIST = prove
 (`!l:(N word)list. num_of_wordlist (pair_wordlist l) = num_of_wordlist l`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(l:(N word)list)` THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l:(N word)list`,`l:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; num_of_wordlist] THEN
  MAP_EVERY X_GEN_TAC [`lo:N word`; `med:(N word)list`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`med:(N word)list`,`med:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; num_of_wordlist] THEN
  SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN_SIMPLE; DIMINDEX_TYBIT0;
           VAL_WORD_0; GSYM MULT_2; LENGTH; ARITH_RULE `n < SUC(SUC n)`] THEN
  REWRITE_TAC[MULT_2; EXP_ADD] THEN ARITH_TAC);;

let BYTES_EQ_NUM_OF_WORDLIST_EXPAND = prove
 (`!m (a:int64) len (s:S) (h:((((N)tybit0)tybit0)tybit0) word) t.
    dimindex(:N) <= len
    ==> (read (m :> bytes(a,len)) s = num_of_wordlist (CONS h t) <=>
         read (m :> wbytes a) s = h /\
         read (m :> bytes(word_add a (word(dimindex(:N))),len-dimindex(:N))) s =
         num_of_wordlist t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_READ_WBYTES; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_TYBIT0] THEN
  REWRITE_TAC[ARITH_RULE `2 * 2 * 2 * n = 8 * n`] THEN
  REWRITE_TAC[ARITH_RULE `(8 * n) DIV 8 = n`] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `d:num <= l ==> l = d + (l - d)`)) THEN
  REWRITE_TAC[READ_BYTES_COMBINE; ADD_SUB2] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[READ_BYTES_BOUND] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; ARITH_RULE `2 * 2 * 2 * n = 8 * n`]);;

let BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV =
  let pth = prove
   (`!m (a:int64) len (s:S) (h:((((N)tybit0)tybit0)tybit0) word).
        dimindex(:N) = len
        ==> (read (m :> bytes(a,len)) s = num_of_wordlist [h] <=>
             read (m :> wbytes a) s = h)`,
    SIMP_TAC[BYTES_EQ_NUM_OF_WORDLIST_EXPAND; LE_REFL] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; SUB_REFL; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[num_of_wordlist]) in
  let frule = PART_MATCH (lhand o rand) pth
  and brule = PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_EXPAND in
  let baseconv tm =
    let ith = frule tm in
    let sth = (LAND_CONV DIMINDEX_CONV THENC NUM_EQ_CONV)
              (lhand(concl ith)) in
    MP ith (EQT_ELIM sth) in
  let rec conv tm =
    try baseconv tm with Failure _ ->
    let ith = brule tm in
    let dth = DIMINDEX_CONV(lhand(lhand(concl ith))) in
    let ith' = SUBS[dth] ith in
    let ath = MP ith' (EQT_ELIM(NUM_LE_CONV(lhand(concl ith')))) in
    let bth = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV
               (RAND_CONV
                 (BINOP2_CONV (TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                              NUM_SUB_CONV))))))) ath in
    CONV_RULE(RAND_CONV(RAND_CONV conv)) bth in
  conv;;

let BYTES_EQ_NUM_OF_WORDLIST_APPEND = prove
 (`!m (a:int64) (s:S) lis1 (lis2:(N word)list) len1 len2.
        dimindex(:N) * LENGTH lis1 = 8 * len1
        ==>  (read (m :> bytes(a,len1+len2)) s =
              num_of_wordlist(APPEND lis1 lis2) <=>
              read (m :> bytes(a,len1)) s = num_of_wordlist lis1 /\
              read (m :> bytes(word_add a (word len1),len2)) s =
              num_of_wordlist lis2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_APPEND] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[READ_BYTES_BOUND] THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN ASM_REWRITE_TAC[LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Memory read merging and splitting conversions                             *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_MERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let MEMORY_128_FROM_64_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v boff n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(boff + 16*i) in
      READ_MEMORY_MERGE_CONV 1 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

let READ_MEMORY_SPLIT_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_UNSPLIT] THENC
    BINOP_CONV(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV)))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Filter length bound                                                       *)
(* ------------------------------------------------------------------------- *)

let LENGTH_FILTER = prove
 (`!P l:A list. LENGTH(FILTER P l) <= LENGTH l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Helper: val(w:24 word) MOD 2^23 as pure word operation                   *)
(* ------------------------------------------------------------------------- *)

let VAL_MOD_23_EQ_AND = prove
 (`!w:24 word. (word(val w MOD 2 EXP 23):int32) =
               word_and (word_zx w:int32) (word 8388607)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* ML-DSA rejection sampling specification                                   *)
(* ------------------------------------------------------------------------- *)

let REJ_SAMPLE = define
 `REJ_SAMPLE l = FILTER (\x:int32. val x < 8380417)
    (MAP (\x:24 word. word(val x MOD 2 EXP 23):int32) l)`;;

let REJ_SAMPLE_EMPTY = prove
 (`REJ_SAMPLE [] = []`,
  REWRITE_TAC[REJ_SAMPLE; FILTER; MAP]);;

let REJ_SAMPLE_APPEND = prove
 (`!l1 l2. REJ_SAMPLE(APPEND l1 l2) =
           APPEND (REJ_SAMPLE l1) (REJ_SAMPLE l2)`,
  REWRITE_TAC[REJ_SAMPLE; MAP_APPEND; FILTER_APPEND]);;

let DIMINDEX_24 = DIMINDEX_CONV `dimindex(:24)`;;
let DIMINDEX_192 = DIMINDEX_CONV `dimindex(:192)`;;
let DIMINDEX_384 = DIMINDEX_CONV `dimindex(:384)`;;

(* ------------------------------------------------------------------------- *)
(* The main correctness theorem.                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_REJ_UNIFORM_CORRECT = prove
 (`!res buf buflen table (inlist:(24 word)list) pc stackpointer.
        24 divides val buflen /\
        8 * val buflen = 24 * LENGTH inlist /\
        ALL (nonoverlapping (stackpointer,1088))
            [(word pc,LENGTH mldsa_rej_uniform_mc); (buf,val buflen); (table,256)] /\
        ALL (nonoverlapping (res,1024))
            [(word pc,LENGTH mldsa_rej_uniform_mc); (stackpointer,1088)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_mc /\
                  read PC s = word(pc + MLDSA_REJ_UNIFORM_CORE_START) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [res;buf;buflen;table] s /\
                  read(memory :> bytes(table,256)) s =
                  num_of_wordlist mldsa_rej_uniform_table /\
                  read(memory :> bytes(buf,val buflen)) s =
                  num_of_wordlist inlist)
             (\s. read PC s = word(pc + MLDSA_REJ_UNIFORM_CORE_END) /\
                  let outlist = SUB_LIST(0,256) (REJ_SAMPLE inlist) in
                  let outlen = LENGTH outlist in
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,4 * outlen)) s =
                  num_of_wordlist outlist)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024);
                         memory :> bytes(stackpointer,1088)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`] THEN
  W64_GEN_TAC `buflen:num` THEN
  MAP_EVERY X_GEN_TAC
   [`table:int64`; `inlist:(24 word)list`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; C_RETURN; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** First split off and handle the writeback tail once and for all ***)

  ENSURES_SEQUENCE_TAC `pc + 0x1f8`
   `\s. read X0 s = res /\
        read X4 s = word 256 /\
        read X8 s = stackpointer /\
        ?n. let outlist = REJ_SAMPLE (SUB_LIST (0,8 * n) inlist) in
            let outlen = LENGTH outlist in
            outlen < 272 /\
            read X9 s = word outlen /\
            (buflen < 24 * (n + 1) \/ 256 <= outlen) /\
            read (memory :> bytes (stackpointer,4 * outlen)) s =
            num_of_wordlist outlist` THEN
  CONJ_TAC THENL
   [ALL_TAC;

    (*** Writeback: unroll the copy loop ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ABBREV_TAC `outlist = REJ_SAMPLE (SUB_LIST (0,8 * n) inlist)` THEN
    ABBREV_TAC `outlen = LENGTH(outlist:int32 list)` THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    VAL_INT64_TAC `outlen:num` THEN
    BIGNUM_LDIGITIZE_TAC "b_"
      `read (memory :> bytes(stackpointer,8 * 128)) s0` THEN
    MEMORY_128_FROM_64_TAC "stackpointer" 0 64 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (1--182) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `read (memory :> bytes (res,4 * MIN 256 outlen)) s182 =
      num_of_wordlist (SUB_LIST (0,256) outlist:int32 list)`
    ASSUME_TAC THENL
     [REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST_0; DIMINDEX_32] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[ARITH_RULE `4 * MIN 256 l = MIN (4 * l) 1024`] THEN
      REWRITE_TAC[ARITH_RULE `32 * 256 = 8 * 1024`] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `MIN a b = MIN b a`] THEN
      REWRITE_TAC[GSYM READ_BYTES_MOD] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
      REWRITE_TAC[ARITH_RULE `1024 = 8 * 128`] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(READ_MEMORY_SPLIT_CONV 1))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [SUBGOAL_THEN `SUB_LIST (0,8 * n) (inlist:(24 word)list) = inlist`
      SUBST_ALL_TAC THENL
       [MATCH_MP_TAC SUB_LIST_REFL THEN FIRST_X_ASSUM(MATCH_MP_TAC o
        MATCH_MP
         (ARITH_RULE `8 * b = 24 * l ==> b <= 24 * n ==> l <= 8 * n`)) THEN
        UNDISCH_TAC `buflen < 24 * (n + 1)` THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
        SIMP_TAC[LEFT_IMP_EXISTS_THM; LE_MULT_LCANCEL; LT_MULT_LCANCEL] THEN
        ARITH_TAC;
        ASM_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0]] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM COND_RAND] THEN
      REWRITE_TAC[ARITH_RULE `(if l < p then l else p) = MIN p l`];
      ASM_REWRITE_TAC[GSYM NOT_LE; LENGTH_SUB_LIST; SUB_0] THEN
      MATCH_MP_TAC(MESON[]
       `y = x /\ (y = x ==> P) ==> word x = word y /\ P`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN
        TRANS_TAC LE_TRANS `outlen:num` THEN ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(ASSUME `LENGTH(outlist:int32 list) = outlen`)) THEN
        EXPAND_TAC "outlist" THEN
        MP_TAC(ISPECL [`inlist:(24 word)list`; `8 * n`]
          SUB_LIST_TOPSPLIT) THEN
        DISCH_THEN(fun th ->
          GEN_REWRITE_TAC (funpow 3 RAND_CONV) [SYM th]) THEN
        REWRITE_TAC[REJ_SAMPLE_APPEND; LENGTH_APPEND; LE_ADD];
        DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN
       `SUB_LIST (0,256) (REJ_SAMPLE inlist) = SUB_LIST (0,256) outlist`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`inlist:(24 word)list`; `8 * n`]
          SUB_LIST_TOPSPLIT) THEN
        DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
        ASM_SIMP_TAC[REJ_SAMPLE_APPEND; SUB_LIST_APPEND_LEFT];
        ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
       `256 <= l ==> 4 * 256 = 4 * MIN 256 l`)) THEN
      FIRST_ASSUM ACCEPT_TAC]] THEN

  (*** The computation half: main loop + tail ***)

  (*** Characterize the number of times round the main loop ***)
  (*** ML-DSA processes 16 coefficients (48 bytes) per iteration ***)

  SUBGOAL_THEN
   `?i. buflen < 48 * (i + 1) \/
        256 <= LENGTH(REJ_SAMPLE(SUB_LIST(0,16 * i) inlist))`
  MP_TAC THENL
   [EXISTS_TAC `buflen:num` THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN

  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN STRIP_TAC THEN

  (*** Slightly elaborated sequencing to handle N = 0 case as well ***)
  (*** Intermediate state P' at pc + 0x168 (loop48_end: CMP X9,X4) ***)

  MATCH_MP_TAC(MESON[]
   `!P'. (ensures arm P' Q R ==> ensures arm P Q R) /\ ensures arm P' Q R
        ==> ensures arm P Q R`) THEN
  EXISTS_TAC
   `\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_mc /\
        read PC s = word (pc + 0x168) /\
        read (memory :> bytes (table,256)) s =
        num_of_wordlist mldsa_rej_uniform_table /\
        read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
        read Q30 s = word 663965040167895004928633208018296833 /\
        read Q31 s = word 633825300187901677051779743745 /\
        let outlist = REJ_SAMPLE (SUB_LIST (0,16 * N) inlist) in
        let outlen = LENGTH outlist in
        read X0 s = res /\
        read X1 s = word_add buf (word (48 * N)) /\
        read X2 s = word_sub (word buflen) (word (48 * N)) /\
        read X3 s = table /\
        read X4 s = word 256 /\
        read X7 s = word_add stackpointer (word (4 * outlen)) /\
        read X8 s = stackpointer /\
        read X9 s = word outlen /\
        read (memory :> bytes (stackpointer,4 * outlen)) s =
        num_of_wordlist outlist` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `N = 0` THENL
     [(*** N = 0 case: execute preamble + init loop to reach P' ***)
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
       (REWRITE_RULE[CONJ_ASSOC] ENSURES_TRANS_SIMPLE)) THEN
      CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THENL
       [ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN DISCH_TAC;
        ASM_REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES] THEN
        REWRITE_TAC[REJ_SAMPLE_EMPTY; LENGTH] THEN
        CONV_TAC NUM_REDUCE_CONV] THEN
      GHOST_INTRO_TAC `q31_init:int128` `read Q31` THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (1--130) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
      REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist];

      FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `~(N = 0) ==> 0 < N`)) THEN
      DISCH_TAC] THEN

    (*** Set up the loop invariant ***)

    ENSURES_WHILE_UP_TAC `N:num` `pc + 0x070` `pc + 0x160`
     `\i s. read (memory :> bytes (table,256)) s =
            num_of_wordlist mldsa_rej_uniform_table /\
            read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
            read Q30 s = word 663965040167895004928633208018296833 /\
            read Q31 s = word 633825300187901677051779743745 /\
            let outlist = REJ_SAMPLE(SUB_LIST(0,16 * i) inlist) in
            let outlen = LENGTH outlist in
            read X0 s = res /\
            read X1 s = word_add buf (word(48 * i)) /\
            read X2 s = word_sub (word buflen) (word(48 * i)) /\
            read X3 s = table /\
            read X4 s = word 256 /\
            read X7 s = word_add stackpointer (word(4 * outlen)) /\
            read X8 s = stackpointer /\
            read X9 s = word outlen /\
            read (memory :> bytes (stackpointer,4*outlen)) s =
            num_of_wordlist outlist` THEN
    REPEAT CONJ_TAC THENL
     [(*** 0 < N ***)
      ASM_ARITH_TAC;

      (*** Pre-loop initialization: reach invariant at i=0 ***)
      FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `q31_init:int128` `read Q31` THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (1--132) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
      REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist];

      (*** Main loop body preservation: invariant i ==> invariant i+1 ***)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ABBREV_TAC `cur:int64 = word_add buf (word (48 * i))` THEN
      ABBREV_TAC `curlist = REJ_SAMPLE (SUB_LIST(0,16 * i) inlist)` THEN
      ABBREV_TAC `curlen = LENGTH(curlist:int32 list)` THEN
      CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
      ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
      MAP_EVERY ABBREV_TAC
       [`q0 = read (memory :> bytes128 cur) s0`;
        `q1 = read (memory :> bytes128 (word_add cur (word 16))) s0`;
        `q2 = read (memory :> bytes128 (word_add cur (word 32))) s0`] THEN

      (*** Abbreviate the 16 coefficients as 32-bit words ***)

      ABBREV_TAC
       `(x:num->int32) j =
        word_and (word_zx(word_subword
          (read (memory :> wbytes cur) s0:384 word)
          (24 * j,24):24 word):int32) (word 8388607)` THEN

      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i:num < N`)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

      (*** Steps 1-12: LD3 + BIC + ZIP + USHLL byte extraction ***)

      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (1--12) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN

      (*** Prove Q16-Q19 contain the correct coefficients ***)

      SUBGOAL_THEN
       `read Q16 s12 =
            word_join (word_join ((x:num->int32) 3) (x 2):int64)
                      (word_join (x 1) (x 0):int64) /\
        read Q17 s12 =
            word_join (word_join ((x:num->int32) 7) (x 6):int64)
                      (word_join (x 5) (x 4):int64) /\
        read Q18 s12 =
            word_join (word_join ((x:num->int32) 11) (x 10):int64)
                      (word_join (x 9) (x 8):int64) /\
        read Q19 s12 =
            word_join (word_join ((x:num->int32) 15) (x 14):int64)
                      (word_join (x 13) (x 12):int64)`
      MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
        ASM_REWRITE_TAC[READ_MEMORY_TRIPLES_SPLIT] THEN REPEAT CONJ_TAC THEN
        GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
        REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC EXPAND_CASES_CONV THEN
        CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
        CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
        REWRITE_TAC[word_subdeinterleave; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
        REWRITE_TAC[] THEN NO_TAC;
        DISCARD_MATCHING_ASSUMPTIONS
         [`read Q16 s = x`; `read Q17 s = x`;
          `read Q18 s = x`; `read Q19 s = x`] THEN
        STRIP_TAC] THEN

      (*** Connect x to EL of SUB_LIST (needed for postcondition) ***)

      SUBGOAL_THEN
       `!j. j < 16
            ==> EL j (MAP (\x:24 word. word(val x MOD 2 EXP 23):int32)
                      (SUB_LIST(16 * i,16) inlist)) = (x:num->int32) j`
      ASSUME_TAC THENL
       [UNDISCH_THEN
         `read (memory :> bytes (buf,buflen)) s12 =
          num_of_wordlist(inlist:(24 word)list)`
         (MP_TAC o AP_TERM
           `\x. x DIV 2 EXP (8 * 48 * i) MOD 2 EXP (8 * 48)`) THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV] THEN
        REWRITE_TAC[READ_BYTES_MOD] THEN
        REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
        REWRITE_TAC[ARITH_RULE `8 * 48 = 24 * 16 * 1`] THEN
        REWRITE_TAC[ARITH_RULE `8 * 48 * x = 24 * 16 * x`] THEN
        REWRITE_TAC[GSYM DIMINDEX_24; GSYM NUM_OF_WORDLIST_SUB_LIST] THEN
        SUBGOAL_THEN
         `MIN (buflen - 48 * i) 48 = dimindex(:384) DIV 8`
        SUBST1_TAC THENL
         [REWRITE_TAC[DIMINDEX_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
          MATCH_MP_TAC(ARITH_RULE
           `~(b < 48 * (i + 1)) ==> MIN (b - 48 * i) 48 = 48`) THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM VAL_READ_WBYTES] THEN
          ASM_REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE]] THEN
        DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN
         `j < LENGTH(SUB_LIST(16 * i,16) (inlist:(24 word)list))`
        ASSUME_TAC THENL
         [REWRITE_TAC[LENGTH_SUB_LIST] THEN
          MAP_EVERY UNDISCH_TAC
           [`j:num < 16`; `~(buflen < 48 * (i + 1))`;
            `8 * buflen = 24 * LENGTH(inlist:(24 word)list)`] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[EL_MAP] THEN REWRITE_TAC[VAL_MOD_23_EQ_AND] THEN
        FIRST_X_ASSUM(fun th ->
          GEN_REWRITE_TAC RAND_CONV [SYM(SPEC `j:num` th)]) THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; DIMINDEX_24;
                    ARITH_RULE `MIN 24 24 = 24`] THEN
        ASM_REWRITE_TAC[GSYM DIMINDEX_24; NUM_OF_WORDLIST_EL;
                        LENGTH_SUB_LIST] THEN
        COND_CASES_TAC THENL [REFL_TAC; ASM_MESON_TAC[]];
        ALL_TAC] THEN

      (*** Steps 13-28: CMHI + AND + UADDLV + FMOV ***)

      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (13--28) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [word_ugt; relational2; GT; WORD_AND_MASK]) THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

      (*** Abbreviate table indices and entries ***)

      MAP_EVERY REABBREV_TAC
       [`idx0 = read X12 s28`; `idx1 = read X13 s28`;
        `idx2 = read X14 s28`; `idx3 = read X15 s28`] THEN
      MAP_EVERY ABBREV_TAC
       [`tab0 = read(memory :> bytes128(word_add table
                    (word(16 * val(idx0:int64))))) s28`;
        `tab1 = read(memory :> bytes128(word_add table
                    (word(16 * val(idx1:int64))))) s28`;
        `tab2 = read(memory :> bytes128(word_add table
                    (word(16 * val(idx2:int64))))) s28`;
        `tab3 = read(memory :> bytes128(word_add table
                    (word(16 * val(idx3:int64))))) s28`] THEN

      (*** Steps 29-48: table loads + CNT + UADDLV + FMOV + TBL ***)

      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (29--48) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [word_ugt; relational2; GT; WORD_AND_MASK]) THEN
      RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
      RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

      (*** TBL correctness: Q16-Q19 = word(num_of_wordlist(FILTER ...)) ***)
      (*** TODO: 16-case brute force per group ***)

      SUBGOAL_THEN
       `read Q16 s48 = word(num_of_wordlist (FILTER (\x:int32. val x < 8380417)
                         [(x:num->int32) 0; x 1; x 2; x 3])) /\
        read Q17 s48 = word(num_of_wordlist (FILTER (\x. val x < 8380417)
                         [x 4; x 5; x 6; x 7])) /\
        read Q18 s48 = word(num_of_wordlist (FILTER (\x. val x < 8380417)
                         [x 8; x 9; x 10; x 11])) /\
        read Q19 s48 = word(num_of_wordlist (FILTER (\x. val x < 8380417)
                         [x 12; x 13; x 14; x 15]))`
      MP_TAC THENL
       [UNDISCH_TAC
         `read(memory :> bytes(table,256)) s48 =
          num_of_wordlist mldsa_rej_uniform_table` THEN
        REPLICATE_TAC 4
         (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
               [GSYM NUM_OF_PAIR_WORDLIST]) THEN
        REWRITE_TAC[mldsa_rej_uniform_table; pair_wordlist] THEN
        CONV_TAC WORD_REDUCE_CONV THEN
        CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
        REWRITE_TAC[GSYM BYTES128_WBYTES] THEN REPEAT STRIP_TAC THEN
        DISCARD_MATCHING_ASSUMPTIONS
         [`read Q24 s = x`; `read Q25 s = x`;
          `read Q26 s = x`; `read Q27 s = x`] THEN
        REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
          (fun th -> is_var(rhs(concl th)) &&
                     let n = fst(dest_var(rhs(concl th))) in
                     n = "tab0" || n = "tab1" || n = "tab2" || n = "tab3"))) THEN
        DISCARD_MATCHING_ASSUMPTIONS
         [`read X12 s = x`; `read X13 s = x`;
          `read X14 s = x`; `read X15 s = x`] THEN
        REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
          (fun th -> is_var(rhs(concl th)) &&
                     let n = fst(dest_var(rhs(concl th))) in
                     n = "idx0" || n = "idx1" || n = "idx2" || n = "idx3"))) THEN
        ASM_REWRITE_TAC[] THEN
        DISCARD_MATCHING_ASSUMPTIONS
         [`read Q16 s = x`; `read Q17 s = x`;
          `read Q18 s = x`; `read Q19 s = x`] THEN
        ASM_REWRITE_TAC[FILTER] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
        ASM_REWRITE_TAC[bitval] THEN
        CONV_TAC WORD_REDUCE_CONV THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        ASM_REWRITE_TAC[WORD_ADD_0] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        REPLICATE_TAC 2
         (ONCE_REWRITE_TAC[GSYM NUM_OF_PAIR_WORDLIST]) THEN
        REWRITE_TAC[pair_wordlist; NUM_OF_WORDLIST_SING; WORD_VAL] THEN
        REWRITE_TAC[num_of_wordlist] THEN CONV_TAC WORD_BLAST;
        DISCARD_MATCHING_ASSUMPTIONS
         [`read Q16 s = x`; `read Q17 s = x`;
          `read Q18 s = x`; `read Q19 s = x`] THEN
        STRIP_TAC] THEN

      (*** Counting: X12-X15 = word(LENGTH(FILTER ...)) ***)

      SUBGOAL_THEN
       `read X12 s48 = word(LENGTH (FILTER (\x:int32. val x < 8380417)
                         [(x:num->int32) 0; x 1; x 2; x 3])) /\
        read X13 s48 = word(LENGTH (FILTER (\x. val x < 8380417)
                         [x 4; x 5; x 6; x 7])) /\
        read X14 s48 = word(LENGTH (FILTER (\x. val x < 8380417)
                         [x 8; x 9; x 10; x 11])) /\
        read X15 s48 = word(LENGTH (FILTER (\x. val x < 8380417)
                         [x 12; x 13; x 14; x 15]))`
      MP_TAC THENL
       [ASM_REWRITE_TAC[WORD_AND_0; WORD_POPCOUNT_0; BITBLAST_RULE
         `word_popcount(word_and (word 1) x:byte) = bitval(bit 0 x) /\
          word_popcount(word_and (word 2) x:byte) = bitval(bit 1 x) /\
          word_popcount(word_and (word 4) x:byte) = bitval(bit 2 x) /\
          word_popcount(word_and (word 8) x:byte) = bitval(bit 3 x) /\
          word_popcount(word_and (word 16) x:byte) = bitval(bit 4 x) /\
          word_popcount(word_and (word 32) x:byte) = bitval(bit 5 x) /\
          word_popcount(word_and (word 64) x:byte) = bitval(bit 6 x) /\
          word_popcount(word_and (word 128) x:byte) = bitval(bit 7 x)`] THEN
        DISCARD_STATE_TAC "s48" THEN REPEAT CONJ_TAC THEN
        REWRITE_TAC[WORD_MASK_ALT] THEN
        REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
        ASM_REWRITE_TAC[FILTER] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
        REWRITE_TAC[LENGTH] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
        DISCARD_MATCHING_ASSUMPTIONS
         [`read X12 s = x`; `read X13 s = x`;
          `read X14 s = x`; `read X15 s = x`] THEN
        STRIP_TAC] THEN

      (*** Abbreviate filtered lists and their lengths ***)

      MAP_EVERY ABBREV_TAC
       [`lis0 = FILTER (\x:int32. val x < 8380417)
                       [(x:num->int32) 0; x 1; x 2; x 3]`;
        `lis1 = FILTER (\x:int32. val x < 8380417)
                       [(x:num->int32) 4; x 5; x 6; x 7]`;
        `lis2 = FILTER (\x:int32. val x < 8380417)
                       [(x:num->int32) 8; x 9; x 10; x 11]`;
        `lis3 = FILTER (\x:int32. val x < 8380417)
                       [(x:num->int32) 12; x 13; x 14; x 15]`;
        `len0 = LENGTH(lis0:int32 list)`;
        `len1 = LENGTH(lis1:int32 list)`;
        `len2 = LENGTH(lis2:int32 list)`;
        `len3 = LENGTH(lis3:int32 list)`] THEN

      SUBGOAL_THEN `len0 <= 4 /\ len1 <= 4 /\ len2 <= 4 /\ len3 <= 4`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["len0"; "len1"; "len2"; "len3"] THEN
        MAP_EVERY EXPAND_TAC ["lis0"; "lis1"; "lis2"; "lis3"] THEN
        REPEAT CONJ_TAC THEN
        W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        ALL_TAC] THEN

      (*** First writeback: ST1 Q16 + ADD X7 ***)

      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (49--50) THEN
      ABBREV_TAC `curlist1:int32 list = APPEND curlist lis0` THEN
      ABBREV_TAC `curlen1:num = curlen + len0` THEN

      SUBGOAL_THEN
       `curlen1 < 260 /\
        read (memory :> bytes (stackpointer,4*curlen1)) s50 =
        num_of_wordlist(curlist1:int32 list)`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlen1"; "curlist1"] THEN CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`curlen < 256`; `len0 <= 4`] THEN ARITH_TAC;
          REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
        W(MP_TAC o PART_MATCH (lhand o rand)
          BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
        ASM_REWRITE_TAC[DIMINDEX_32; ARITH_RULE `8 * 4 * l = 32 * l`] THEN
        DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN
         `read (memory :> bytes128
                (word_add stackpointer (word (4 * curlen)))) s50 =
          word (num_of_wordlist(lis0:int32 list))`
        MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                    VAL_READ_WBYTES;
                    DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
        SUBGOAL_THEN `4 * len0 = MIN 16 (4 * len0)` SUBST1_TAC THENL
         [UNDISCH_TAC `len0 <= 4` THEN ARITH_TAC;
          REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
        REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
        MATCH_MP_TAC MOD_LT THEN
        MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
        ASM_REWRITE_TAC[DIMINDEX_32] THEN
        UNDISCH_TAC `len0 <= 4` THEN ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
          [WORD_RULE `word_add (word_add a (word (4 * l0)))
                               (word_shl (word l1) 2) =
                      word_add a (word(4 * (l0 + l1)))`]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      SUBGOAL_THEN `LENGTH(curlist1:int32 list) = curlen1` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlist1"; "curlen1"] THEN
        REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN

      (*** Second writeback ***)

      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (51--52) THEN
      ABBREV_TAC `curlist2:int32 list = APPEND curlist1 lis1` THEN
      ABBREV_TAC `curlen2:num = curlen1 + len1` THEN
      SUBGOAL_THEN
       `curlen2 < 264 /\
        read (memory :> bytes (stackpointer,4*curlen2)) s52 =
        num_of_wordlist(curlist2:int32 list)`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlen2"; "curlist2"] THEN CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`curlen1 < 260`; `len1 <= 4`] THEN ARITH_TAC;
          REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
        W(MP_TAC o PART_MATCH (lhand o rand)
          BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
        ASM_REWRITE_TAC[DIMINDEX_32; ARITH_RULE `8 * 4 * l = 32 * l`] THEN
        DISCH_THEN SUBST1_TAC THEN
        UNDISCH_THEN
         `read (memory :> bytes128
                (word_add stackpointer (word (4 * curlen1)))) s52 =
          word (num_of_wordlist(lis1:int32 list))`
         (MP_TAC o AP_TERM `val:int128->num`) THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                    VAL_READ_WBYTES;
                    DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
        SUBGOAL_THEN `4 * len1 = MIN 16 (4 * len1)` SUBST1_TAC THENL
         [UNDISCH_TAC `len1 <= 4` THEN ARITH_TAC;
          REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
        REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
        MATCH_MP_TAC MOD_LT THEN
        MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
        ASM_REWRITE_TAC[DIMINDEX_32] THEN
        UNDISCH_TAC `len1 <= 4` THEN ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
          [WORD_RULE `word_add (word_add a (word (4 * l0)))
                               (word_shl (word l1) 2) =
                      word_add a (word(4 * (l0 + l1)))`]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      SUBGOAL_THEN `LENGTH(curlist2:int32 list) = curlen2` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlist2"; "curlen2"] THEN
        REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN

      (*** Third writeback ***)

      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (53--54) THEN
      ABBREV_TAC `curlist3:int32 list = APPEND curlist2 lis2` THEN
      ABBREV_TAC `curlen3:num = curlen2 + len2` THEN
      SUBGOAL_THEN
       `curlen3 < 268 /\
        read (memory :> bytes (stackpointer,4*curlen3)) s54 =
        num_of_wordlist(curlist3:int32 list)`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlen3"; "curlist3"] THEN CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`curlen2 < 264`; `len2 <= 4`] THEN ARITH_TAC;
          REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
        W(MP_TAC o PART_MATCH (lhand o rand)
          BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
        ASM_REWRITE_TAC[DIMINDEX_32; ARITH_RULE `8 * 4 * l = 32 * l`] THEN
        DISCH_THEN SUBST1_TAC THEN
        UNDISCH_THEN
         `read (memory :> bytes128
                (word_add stackpointer (word (4 * curlen2)))) s54 =
          word (num_of_wordlist(lis2:int32 list))`
         (MP_TAC o AP_TERM `val:int128->num`) THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                    VAL_READ_WBYTES;
                    DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
        SUBGOAL_THEN `4 * len2 = MIN 16 (4 * len2)` SUBST1_TAC THENL
         [UNDISCH_TAC `len2 <= 4` THEN ARITH_TAC;
          REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
        REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
        MATCH_MP_TAC MOD_LT THEN
        MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
        ASM_REWRITE_TAC[DIMINDEX_32] THEN
        UNDISCH_TAC `len2 <= 4` THEN ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
          [WORD_RULE `word_add (word_add a (word (4 * l0)))
                               (word_shl (word l1) 2) =
                      word_add a (word(4 * (l0 + l1)))`]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      SUBGOAL_THEN `LENGTH(curlist3:int32 list) = curlen3` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlist3"; "curlen3"] THEN
        REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN

      (*** Fourth writeback ***)

      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (55--56) THEN
      ABBREV_TAC `curlist4:int32 list = APPEND curlist3 lis3` THEN
      ABBREV_TAC `curlen4:num = curlen3 + len3` THEN
      SUBGOAL_THEN
       `curlen4 < 272 /\
        read (memory :> bytes (stackpointer,4*curlen4)) s56 =
        num_of_wordlist(curlist4:int32 list)`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlen4"; "curlist4"] THEN CONJ_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`curlen3 < 268`; `len3 <= 4`] THEN ARITH_TAC;
          REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
        W(MP_TAC o PART_MATCH (lhand o rand)
          BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
        ASM_REWRITE_TAC[DIMINDEX_32; ARITH_RULE `8 * 4 * l = 32 * l`] THEN
        DISCH_THEN SUBST1_TAC THEN
        UNDISCH_THEN
         `read (memory :> bytes128
                (word_add stackpointer (word (4 * curlen3)))) s56 =
          word (num_of_wordlist(lis3:int32 list))`
         (MP_TAC o AP_TERM `val:int128->num`) THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                    VAL_READ_WBYTES;
                    DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
        SUBGOAL_THEN `4 * len3 = MIN 16 (4 * len3)` SUBST1_TAC THENL
         [UNDISCH_TAC `len3 <= 4` THEN ARITH_TAC;
          REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
        REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
        MATCH_MP_TAC MOD_LT THEN
        MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
        ASM_REWRITE_TAC[DIMINDEX_32] THEN
        UNDISCH_TAC `len3 <= 4` THEN ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
          [WORD_RULE `word_add (word_add a (word (4 * l0)))
                               (word_shl (word l1) 2) =
                      word_add a (word(4 * (l0 + l1)))`]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      SUBGOAL_THEN `LENGTH(curlist4:int32 list) = curlen4` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["curlist4"; "curlen4"] THEN
        REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN

      (*** Steps 57-60: accumulation (use MAP_UNTIL_TARGET_PC) ***)

      MAP_UNTIL_TARGET_PC
        (fun n -> ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [n]) 57 THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

      (*** Postcondition: connect to loop invariant at i+1 ***)

      REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; ADD_CLAUSES] THEN
      SUBGOAL_THEN
       `REJ_SAMPLE (SUB_LIST (16 * i,16) inlist) =
        APPEND (APPEND (APPEND lis0 lis1) lis2) lis3`
      SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["lis0"; "lis1"; "lis2"; "lis3"] THEN
        REWRITE_TAC[GSYM APPEND_ASSOC; GSYM FILTER_APPEND] THEN
        REWRITE_TAC[APPEND; REJ_SAMPLE] THEN AP_TERM_TAC THEN
        REWRITE_TAC[LIST_EQ] THEN CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
        REWRITE_TAC[LENGTH_MAP] THEN
        MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
         [REWRITE_TAC[LENGTH_SUB_LIST] THEN MATCH_MP_TAC(ARITH_RULE
           `16 * (i + 1) <= l ==> MIN 16 (l - 16 * i) = 16`) THEN
          MAP_EVERY UNDISCH_TAC
           [`~(buflen < 48 * (i + 1))`;
            `8 * buflen = 24 * LENGTH(inlist:(24 word)list)`] THEN
          ARITH_TAC;
          ASM_SIMP_TAC[EL_MAP] THEN DISCH_THEN(K ALL_TAC) THEN
          CONV_TAC EXPAND_CASES_CONV THEN
          CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]];
        ASM_REWRITE_TAC[APPEND_ASSOC] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV)] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "cur" THEN
      REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
      SUBST1_TAC(SYM(ASSUME `curlen3 + len3:num = curlen4`)) THEN
      SUBST1_TAC(SYM(ASSUME `curlen2 + len2:num = curlen3`)) THEN
      SUBST1_TAC(SYM(ASSUME `curlen1 + len1:num = curlen2`)) THEN
      SUBST1_TAC(SYM(ASSUME `curlen + len0:num = curlen1`)) THEN
      CONV_TAC WORD_RULE;

      (*** Loop back: from end_pc (pc+0x160) to start_pc (pc+0x070) ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `48 <= val(word_sub (word buflen:int64) (word (48 * i)))`
      ASSUME_TAC THENL
       [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
        VAL_INT64_TAC `48 * i` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(buflen < 48 * (i + 1))` THEN ARITH_TAC;
        ALL_TAC] THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(MESON[] `~p ==> (if p then x else y) = y`) THEN
      ASM_SIMP_TAC[NOT_LE; VAL_WORD_LT];

      (*** Post-loop exit: from end_pc (invariant N) to split point ***)
      (*** Handle cases: outlen >= 256 direct, or fall through to P' ***)
      SUBGOAL_THEN
       `LENGTH (REJ_SAMPLE (SUB_LIST (0,16 * N) inlist)) < 272`
      ASSUME_TAC THENL
       [ASM_CASES_TAC `N = 0` THENL
         [ASM_REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY] THEN
          REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
          FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`)] THEN
        ASM_REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
        MATCH_MP_TAC(ARITH_RULE
         `l' <= l + 16 ==> ~(b < x) /\ l < 256 ==> l' < 272`) THEN
        MP_TAC(ISPECL [`inlist:(24 word)list`; `16 * (N - 1)`; `16`; `0`]
            SUB_LIST_SPLIT) THEN
        ASM_SIMP_TAC[ARITH_RULE `~(N = 0) ==> 16 * (N - 1) + 16 = 16 * N`] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
        REWRITE_TAC[LENGTH_APPEND; LE_ADD_LCANCEL; ADD_CLAUSES] THEN
        REWRITE_TAC[REJ_SAMPLE] THEN
        W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
        REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN ARITH_TAC;
        ALL_TAC] THEN
      VAL_INT64_TAC `LENGTH (REJ_SAMPLE (SUB_LIST (0,16 * N) inlist))` THEN
      SUBGOAL_THEN
       `48 <= val(word_sub (word buflen:int64) (word (48 * N))) <=>
        48 * (N + 1) <= buflen`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `48 * N < 2 EXP 64` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN SIMPLE_ARITH_TAC;
          MAP_EVERY VAL_INT64_TAC [`48 * N`; `buflen:num`]] THEN
        ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      ASM_CASES_TAC `48 * (N + 1) <= buflen` THENL
       [ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (1--2) THEN
        FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
        ASM_REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
        ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (3--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `2 * N` THEN
        ASM_REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`];
        ALL_TAC] THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
          (REWRITE_RULE[CONJ_ASSOC] ENSURES_TRANS_SIMPLE))) THEN
      CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    ALL_TAC] THEN

  (*** The tail computation from P' at pc+0x168 to split at pc+0x1f8 ***)
  (*** Handles: outlen >= 256 direct, or 24-byte tail body ***)

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `LENGTH (REJ_SAMPLE (SUB_LIST (0,16 * N) inlist)) < 272`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `N = 0` THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY] THEN
      REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
      FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`)] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
    MATCH_MP_TAC(ARITH_RULE
     `l' <= l + 16 ==> ~(b < x) /\ l < 256 ==> l' < 272`) THEN
    MP_TAC(ISPECL [`inlist:(24 word)list`; `16 * (N - 1)`; `16`; `0`]
        SUB_LIST_SPLIT) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(N = 0) ==> 16 * (N - 1) + 16 = 16 * N`] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
    REWRITE_TAC[LENGTH_APPEND; LE_ADD_LCANCEL; ADD_CLAUSES] THEN
    REWRITE_TAC[REJ_SAMPLE] THEN
    W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LE_TRANS) THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST] THEN ARITH_TAC;
    ALL_TAC] THEN
  VAL_INT64_TAC `LENGTH (REJ_SAMPLE (SUB_LIST (0,16 * N) inlist))` THEN
  SUBGOAL_THEN
   `24 <= val(word_sub (word buflen:int64) (word (48 * N))) <=>
    48 * N + 24 <= buflen`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `48 * N < 2 EXP 64` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN SIMPLE_ARITH_TAC;
      MAP_EVERY VAL_INT64_TAC [`48 * N`; `buflen:num`]] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `256 <= LENGTH (REJ_SAMPLE (SUB_LIST (0,16 * N) inlist))` THEN
  ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (1--2) THENL
   [ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `2 * N` THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`];
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ASM_CASES_TAC `48 * N + 24 <= buflen` THEN
  ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (3--4) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]);
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `2 * N` THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`] THEN
    UNDISCH_TAC `~(48 * N + 24 <= buflen)` THEN ARITH_TAC] THEN

  (*** Because of divisibility, exactly 24 buffer elements left ***)

  FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
  SUBGOAL_THEN `48 * N + 24 = buflen` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`48 * N + 24 <= buflen`; `buflen < 48 * (N + 1)`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
    SIMP_TAC[LEFT_IMP_EXISTS_THM; ARITH_RULE `48 = 24 * 2`] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; ARITH_RULE `24 * n + 24 = 24 * (n + 1)`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL; LT_MULT_LCANCEL] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The tail computation body: 8 coefficients in 2 groups ***)
  (*** TODO: Half-sized version of main loop body. Key differences:
       - 192-bit wbytes (24 bytes) instead of 384-bit
       - bytes64 reads for q0,q1,q2 instead of bytes128
       - 2 groups of 4 coefficients (Q16-Q17 only)
       - Steps start at 5 (s4 from ENSURES_INIT_TAC at line 1306)
       - EXISTS witness is 2*N+1
       - SUB_LIST(16*N,8) instead of SUB_LIST(16*i,16)
       - 48*N+24=buflen (exact) instead of ~(buflen<48*(i+1))
  ***)
  ABBREV_TAC `cur:int64 = word_add buf (word (48 * N))` THEN
  ABBREV_TAC `curlist = REJ_SAMPLE (SUB_LIST(0,16 * N) inlist)` THEN
  ABBREV_TAC `curlen = LENGTH(curlist:int32 list)` THEN

  MAP_EVERY ABBREV_TAC
   [`q0 = read (memory :> bytes64 cur) s4`;
    `q1 = read (memory :> bytes64 (word_add cur (word 8))) s4`;
    `q2 = read (memory :> bytes64 (word_add cur (word 16))) s4`] THEN

  ABBREV_TAC
   `(x:num->int32) j =
    word_and (word_zx(word_subword
      (read (memory :> wbytes cur) s4:192 word)
      (24 * j,24):24 word):int32) (word 8388607)` THEN

  ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (5--12) THEN

  SUBGOAL_THEN
   `read Q16 s12 =
        word_join (word_join ((x:num->int32) 3) (x 2):int64)
                  (word_join (x 1) (x 0):int64) /\
    read Q17 s12 =
        word_join (word_join ((x:num->int32) 7) (x 6):int64)
                  (word_join (x 5) (x 4):int64)`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[READ_MEMORY_TRIPLES_SPLIT] THEN REPEAT CONJ_TAC THEN
    GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
    REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
    REWRITE_TAC[word_subdeinterleave; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
    REWRITE_TAC[] THEN NO_TAC;
    DISCARD_MATCHING_ASSUMPTIONS
     [`read Q16 s = x`; `read Q17 s = x`] THEN
    STRIP_TAC] THEN

  SUBGOAL_THEN
   `!j. j < 8
        ==> EL j (MAP (\w:24 word. word(val w MOD 2 EXP 23):int32)
                  (SUB_LIST(16 * N,8) inlist)) = (x:num->int32) j`
  ASSUME_TAC THENL
   [UNDISCH_THEN
     `read (memory :> bytes (buf,buflen)) s12 =
      num_of_wordlist(inlist:(24 word)list)`
     (MP_TAC o AP_TERM
       `\n:num. n DIV 2 EXP (8 * 48 * N) MOD 2 EXP (8 * 24)`) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    REWRITE_TAC[ARITH_RULE `8 * 24 = 24 * 8 * 1`;
                ARITH_RULE `8 * 48 * n = 24 * 16 * n`] THEN
    REWRITE_TAC[GSYM DIMINDEX_24; GSYM NUM_OF_WORDLIST_SUB_LIST] THEN
    SUBGOAL_THEN `MIN (buflen - 48 * N) (dimindex(:24)) = dimindex(:192) DIV 8`
    SUBST1_TAC THENL
     [REWRITE_TAC[DIMINDEX_24; DIMINDEX_192] THEN
      UNDISCH_TAC `48 * N + 24 = buflen` THEN ARITH_TAC;
      REWRITE_TAC[MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM VAL_READ_WBYTES] THEN
      ASM_REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE]] THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `j < LENGTH(SUB_LIST(16 * N,8) (inlist:(24 word)list))`
    ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST] THEN
      MAP_EVERY UNDISCH_TAC [`j:num < 8`; `48 * N + 24 = buflen`;
        `8 * buflen = 24 * LENGTH(inlist:(24 word)list)`] THEN
      ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP] THEN REWRITE_TAC[VAL_MOD_23_EQ_AND] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC RAND_CONV [SYM(SPEC `j:num` th)]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; DIMINDEX_24;
                ARITH_RULE `MIN 24 24 = 24`] THEN
    ASM_REWRITE_TAC[GSYM DIMINDEX_24; NUM_OF_WORDLIST_EL;
                    LENGTH_SUB_LIST] THEN
    COND_CASES_TAC THENL [REFL_TAC; ASM_MESON_TAC[]]; ALL_TAC] THEN
  ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (13--20) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_ugt; relational2; GT; WORD_AND_MASK]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
  MAP_EVERY REABBREV_TAC
   [`idx0 = read X12 s20`; `idx1 = read X13 s20`] THEN
  MAP_EVERY ABBREV_TAC
   [`tab0 = read(memory :> bytes128(word_add table
                (word(16 * val(idx0:int64))))) s20`;
    `tab1 = read(memory :> bytes128(word_add table
                (word(16 * val(idx1:int64))))) s20`] THEN

  (*** Steps 21-28: LDR Q24/Q25 + CNT + UADDLV + FMOV ***)

  ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (21--28) THEN

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_AND]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_ugt; relational2; GT; WORD_AND_MASK]) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[COND_RAND]) THEN
  RULE_ASSUM_TAC(CONV_RULE WORD_REDUCE_CONV) THEN

  (*** Steps 29-30: TBL Q16/Q17 ***)

  ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (29--30) THEN

  (*** TBL correctness: Q16/Q17 = word(num_of_wordlist(FILTER ...)) ***)

  SUBGOAL_THEN
   `read Q16 s30 = word(num_of_wordlist (FILTER (\x:int32. val x < 8380417)
                         [(x:num->int32) 0; x 1; x 2; x 3])) /\
    read Q17 s30 = word(num_of_wordlist (FILTER (\x. val x < 8380417)
                         [x 4; x 5; x 6; x 7]))`
  MP_TAC THENL
   [UNDISCH_TAC
     `read(memory :> bytes(table,256)) s30 =
      num_of_wordlist mldsa_rej_uniform_table` THEN
    REPLICATE_TAC 4
     (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
           [GSYM NUM_OF_PAIR_WORDLIST]) THEN
    REWRITE_TAC[mldsa_rej_uniform_table; pair_wordlist] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
    REWRITE_TAC[GSYM BYTES128_WBYTES] THEN REPEAT STRIP_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`read Q24 s = x`; `read Q25 s = x`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
      (fun th -> is_var(rhs(concl th)) &&
                 let n = fst(dest_var(rhs(concl th))) in
                 n = "tab0" || n = "tab1"))) THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`read X12 s = x`; `read X13 s = x`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
      (fun th -> is_var(rhs(concl th)) &&
                 let n = fst(dest_var(rhs(concl th))) in
                 n = "idx0" || n = "idx1"))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`read Q16 s = x`; `read Q17 s = x`] THEN
    ASM_REWRITE_TAC[FILTER] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_REWRITE_TAC[bitval] THEN
    CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REPLICATE_TAC 2
     (ONCE_REWRITE_TAC[GSYM NUM_OF_PAIR_WORDLIST]) THEN
    REWRITE_TAC[pair_wordlist; NUM_OF_WORDLIST_SING; WORD_VAL] THEN
    REWRITE_TAC[num_of_wordlist] THEN CONV_TAC WORD_BLAST;
    DISCARD_MATCHING_ASSUMPTIONS
     [`read Q16 s = x`; `read Q17 s = x`] THEN
    STRIP_TAC] THEN

  (*** Counting: X12/X13 = word(LENGTH(FILTER ...)) ***)

  SUBGOAL_THEN
   `read X12 s30 = word(LENGTH (FILTER (\x:int32. val x < 8380417)
                         [(x:num->int32) 0; x 1; x 2; x 3])) /\
    read X13 s30 = word(LENGTH (FILTER (\x. val x < 8380417)
                         [x 4; x 5; x 6; x 7]))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[WORD_AND_0; WORD_POPCOUNT_0; BITBLAST_RULE
     `word_popcount(word_and (word 1) x:byte) = bitval(bit 0 x) /\
      word_popcount(word_and (word 2) x:byte) = bitval(bit 1 x) /\
      word_popcount(word_and (word 4) x:byte) = bitval(bit 2 x) /\
      word_popcount(word_and (word 8) x:byte) = bitval(bit 3 x) /\
      word_popcount(word_and (word 16) x:byte) = bitval(bit 4 x) /\
      word_popcount(word_and (word 32) x:byte) = bitval(bit 5 x) /\
      word_popcount(word_and (word 64) x:byte) = bitval(bit 6 x) /\
      word_popcount(word_and (word 128) x:byte) = bitval(bit 7 x)`] THEN
    DISCARD_STATE_TAC "s30" THEN REPEAT CONJ_TAC THEN
    REWRITE_TAC[WORD_MASK_ALT] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_REWRITE_TAC[FILTER] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[LENGTH] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV);
    DISCARD_MATCHING_ASSUMPTIONS
     [`read X12 s = x`; `read X13 s = x`] THEN
    STRIP_TAC] THEN

  (*** Abbreviate filtered lists and their lengths ***)

  MAP_EVERY ABBREV_TAC
   [`lis0 = FILTER (\x:int32. val x < 8380417)
                   [(x:num->int32) 0; x 1; x 2; x 3]`;
    `lis1 = FILTER (\x:int32. val x < 8380417)
                   [(x:num->int32) 4; x 5; x 6; x 7]`;
    `len0 = LENGTH(lis0:int32 list)`;
    `len1 = LENGTH(lis1:int32 list)`] THEN

  SUBGOAL_THEN `len0 <= 4 /\ len1 <= 4`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["len0"; "len1"] THEN
    MAP_EVERY EXPAND_TAC ["lis0"; "lis1"] THEN
    REPEAT CONJ_TAC THEN
    W(MP_TAC o PART_MATCH lhand LENGTH_FILTER o lhand o snd) THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** First writeback: STR Q16 + ADD X7 ***)

  ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (31--32) THEN
  ABBREV_TAC `curlist1:int32 list = APPEND curlist lis0` THEN
  ABBREV_TAC `curlen1:num = curlen + len0` THEN

  SUBGOAL_THEN
   `curlen1 < 260 /\
    read (memory :> bytes (stackpointer,4*curlen1)) s32 =
    num_of_wordlist(curlist1:int32 list)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen1"; "curlist1"] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`curlen < 256`; `len0 <= 4`] THEN ARITH_TAC;
      REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_32; ARITH_RULE `8 * 4 * l = 32 * l`] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes128
            (word_add stackpointer (word (4 * curlen)))) s32 =
      word (num_of_wordlist(lis0:int32 list))`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                VAL_READ_WBYTES;
                DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
    SUBGOAL_THEN `4 * len0 = MIN 16 (4 * len0)` SUBST1_TAC THENL
     [UNDISCH_TAC `len0 <= 4` THEN ARITH_TAC;
      REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
    MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
    ASM_REWRITE_TAC[DIMINDEX_32] THEN
    UNDISCH_TAC `len0 <= 4` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
      [WORD_RULE `word_add (word_add a (word (4 * l0)))
                           (word_shl (word l1) 2) =
                  word_add a (word(4 * (l0 + l1)))`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `LENGTH(curlist1:int32 list) = curlen1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlist1"; "curlen1"] THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** Second writeback: STR Q17 + ADD X7 ***)

  ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC (33--34) THEN
  ABBREV_TAC `curlist2:int32 list = APPEND curlist1 lis1` THEN
  ABBREV_TAC `curlen2:num = curlen1 + len1` THEN

  SUBGOAL_THEN
   `curlen2 < 264 /\
    read (memory :> bytes (stackpointer,4*curlen2)) s34 =
    num_of_wordlist(curlist2:int32 list)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlen2"; "curlist2"] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`curlen1 < 260`; `len1 <= 4`] THEN ARITH_TAC;
      REWRITE_TAC[LEFT_ADD_DISTRIB]] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      BYTES_EQ_NUM_OF_WORDLIST_APPEND o snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_32; ARITH_RULE `8 * 4 * l = 32 * l`] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes128
            (word_add stackpointer (word (4 * curlen1)))) s34 =
      word (num_of_wordlist(lis1:int32 list))`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES128_WBYTES;
                VAL_READ_WBYTES;
                DIMINDEX_128; ARITH_RULE `128 DIV 8 = 16`] THEN
    SUBGOAL_THEN `4 * len1 = MIN 16 (4 * len1)` SUBST1_TAC THENL
     [UNDISCH_TAC `len1 <= 4` THEN ARITH_TAC;
      REWRITE_TAC[GSYM READ_BYTES_MOD]] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_128; MOD_MOD_EXP_MIN] THEN
    MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN
    ASM_REWRITE_TAC[DIMINDEX_32] THEN
    UNDISCH_TAC `len1 <= 4` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
      [WORD_RULE `word_add (word_add a (word (4 * l0)))
                           (word_shl (word l1) 2) =
                  word_add a (word(4 * (l0 + l1)))`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `LENGTH(curlist2:int32 list) = curlen2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["curlist2"; "curlen2"] THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** REJ_SAMPLE connection ***)

  SUBGOAL_THEN
   `REJ_SAMPLE (SUB_LIST (0,16 * N + 8) inlist) = curlist2:int32 list`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUB_LIST_SPLIT; REJ_SAMPLE_APPEND; ADD_CLAUSES] THEN
    SUBGOAL_THEN
     `REJ_SAMPLE (SUB_LIST (16 * N,8) inlist) = APPEND lis0 lis1`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["lis0"; "lis1"] THEN
      REWRITE_TAC[GSYM FILTER_APPEND; APPEND; REJ_SAMPLE] THEN
      AP_TERM_TAC THEN
      REWRITE_TAC[LIST_EQ] THEN CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
      REWRITE_TAC[LENGTH_MAP] THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [REWRITE_TAC[LENGTH_SUB_LIST] THEN MATCH_MP_TAC(ARITH_RULE
         `16 * N + 8 <= l ==> MIN 8 (l - 16 * N) = 8`) THEN
        MAP_EVERY UNDISCH_TAC
         [`48 * N + 24 = buflen`;
          `8 * buflen = 24 * LENGTH(inlist:(24 word)list)`] THEN
        ARITH_TAC;
        ASM_SIMP_TAC[EL_MAP] THEN DISCH_THEN(K ALL_TAC) THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]];
      MAP_EVERY EXPAND_TAC ["curlist2"; "curlist1"] THEN
      ASM_REWRITE_TAC[APPEND_ASSOC]];
    ALL_TAC] THEN

  (*** Steps 35-36: accumulation (ADD X9 + ADD X9) + final steps ***)

  MAP_UNTIL_TARGET_PC
    (fun n -> ARM_STEPS_TAC MLDSA_REJ_UNIFORM_EXEC [n]) 35 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Postcondition: exists n with witness 2*N+1 ***)

  EXISTS_TAC `2 * N + 1` THEN
  REWRITE_TAC[ARITH_RULE `8 * (2 * N + 1) = 16 * N + 8`;
              ARITH_RULE `24 * (2 * N + 1 + 1) = 48 * N + 48`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `curlen2 < 264` THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `curlen1 + len1:num = curlen2`)) THEN
    SUBST1_TAC(SYM(ASSUME `curlen + len0:num = curlen1`)) THEN
    CONV_TAC WORD_RULE; ALL_TAC] THEN
  DISJ1_TAC THEN UNDISCH_TAC `48 * N + 24 = buflen` THEN ARITH_TAC);;

let MLDSA_REJ_UNIFORM_SUBROUTINE_CORRECT = prove
 (`!res buf buflen table (inlist:(24 word)list) pc stackpointer returnaddress.
        24 divides val buflen /\
        8 * val buflen = 24 * LENGTH inlist /\
        ALL (nonoverlapping (word_sub stackpointer (word 1088),1088))
            [(word pc,LENGTH mldsa_rej_uniform_mc); (buf,val buflen); (table,256)] /\
        ALL (nonoverlapping (res,1024))
            [(word pc,LENGTH mldsa_rej_uniform_mc);
             (word_sub stackpointer (word 1088),1088)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [res;buf;buflen;table] s /\
                  read(memory :> bytes(table,256)) s =
                  num_of_wordlist mldsa_rej_uniform_table /\
                  read(memory :> bytes(buf,val buflen)) s =
                  num_of_wordlist inlist)
             (\s. read PC s = returnaddress /\
                  let outlist = SUB_LIST(0,256) (REJ_SAMPLE inlist) in
                  let outlen = LENGTH outlist in
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,4 * outlen)) s =
                  num_of_wordlist outlist)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024);
                         memory :> bytes(word_sub stackpointer (word 1088),1088)])`,
  let TWEAK_CONV = TOP_DEPTH_CONV let_CONV THENC LENGTH_SIMPLIFY_CONV in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC MLDSA_REJ_UNIFORM_EXEC
   (CONV_RULE TWEAK_CONV MLDSA_REJ_UNIFORM_CORRECT)
    `[]:int64 list` 1088);;

