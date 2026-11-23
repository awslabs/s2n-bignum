(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 10 bits, and packing them.      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_compress_d10.o";;
 ****)

let mlkem_compress_d10_mc = define_assert_from_elf
  "mlkem_compress_d10_mc" "arm/mlkem/mlkem_compress_d10.o"
[
  0xd503245f;       (* arm_BTI *)
  0x6dbf27e8;       (* arm_STP D8 D9 SP (Preimmediate_Offset (iword (-- &16))) *)
  0x6dbf2fea;       (* arm_STP D10 D11 SP (Preimmediate_Offset (iword (-- &16))) *)
  0x6dbf37ec;       (* arm_STP D12 D13 SP (Preimmediate_Offset (iword (-- &16))) *)
  0x6dbf3fee;       (* arm_STP D14 D15 SP (Preimmediate_Offset (iword (-- &16))) *)
  0x528dda02;       (* arm_MOV W2 (rvalue (word 28368)) *)
  0x72a4ebe2;       (* arm_MOVK W2 (word 10079) 16 *)
  0x4e040c58;       (* arm_DUP_GEN Q24 X2 32 128 *)
  0x6f00e419;       (* arm_MOVI Q25 (word 0) *)
  0xd2800002;       (* arm_MOV X2 (rvalue (word 0)) *)
  0xf2a00042;       (* arm_MOVK X2 (word 2) 16 *)
  0xf2c00082;       (* arm_MOVK X2 (word 4) 32 *)
  0xf2e000c2;       (* arm_MOVK X2 (word 6) 48 *)
  0x4e080c5a;       (* arm_DUP_GEN Q26 X2 64 128 *)
  0xd2804002;       (* arm_MOV X2 (rvalue (word 512)) *)
  0xf2a0c082;       (* arm_MOVK X2 (word 1540) 16 *)
  0xf2c11fe2;       (* arm_MOVK X2 (word 2303) 32 *)
  0xf2e18142;       (* arm_MOVK X2 (word 3082) 48 *)
  0xd29fe1c3;       (* arm_MOV X3 (rvalue (word 65294)) *)
  0xf2bfffe3;       (* arm_MOVK X3 (word 65535) 16 *)
  0xf2dfffe3;       (* arm_MOVK X3 (word 65535) 32 *)
  0xf2ffffe3;       (* arm_MOVK X3 (word 65535) 48 *)
  0x9e67005b;       (* arm_FMOV_ItoF Q27 X2 0 *)
  0x4e181c7b;       (* arm_INS_GEN Q27 X3 64 64 *)
  0xd2803fe2;       (* arm_MOV X2 (rvalue (word 511)) *)
  0xf2a0a062;       (* arm_MOVK X2 (word 1283) 16 *)
  0xf2dfe0e2;       (* arm_MOVK X2 (word 65287) 32 *)
  0xf2e16122;       (* arm_MOVK X2 (word 2825) 48 *)
  0xd281e1a3;       (* arm_MOV X3 (rvalue (word 3853)) *)
  0xf2bfffe3;       (* arm_MOVK X3 (word 65535) 16 *)
  0xf2dfffe3;       (* arm_MOVK X3 (word 65535) 32 *)
  0xf2ffffe3;       (* arm_MOVK X3 (word 65535) 48 *)
  0x9e67005c;       (* arm_FMOV_ItoF Q28 X2 0 *)
  0x4e181c7c;       (* arm_INS_GEN Q28 X3 64 64 *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0xacc10420;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc10c22;       (* arm_LDP Q2 Q3 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc11424;       (* arm_LDP Q4 Q5 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc11c26;       (* arm_LDP Q6 Q7 X1 (Postimmediate_Offset (iword (&32))) *)
  0x4e403b28;       (* arm_ZIP1 Q8 Q25 Q0 16 128 *)
  0x4e407b29;       (* arm_ZIP2 Q9 Q25 Q0 16 128 *)
  0x4e413b2a;       (* arm_ZIP1 Q10 Q25 Q1 16 128 *)
  0x4e417b2b;       (* arm_ZIP2 Q11 Q25 Q1 16 128 *)
  0x4e423b2c;       (* arm_ZIP1 Q12 Q25 Q2 16 128 *)
  0x4e427b2d;       (* arm_ZIP2 Q13 Q25 Q2 16 128 *)
  0x4e433b2e;       (* arm_ZIP1 Q14 Q25 Q3 16 128 *)
  0x4e437b2f;       (* arm_ZIP2 Q15 Q25 Q3 16 128 *)
  0x4e443b30;       (* arm_ZIP1 Q16 Q25 Q4 16 128 *)
  0x4e447b31;       (* arm_ZIP2 Q17 Q25 Q4 16 128 *)
  0x4e453b32;       (* arm_ZIP1 Q18 Q25 Q5 16 128 *)
  0x4e457b33;       (* arm_ZIP2 Q19 Q25 Q5 16 128 *)
  0x4e463b34;       (* arm_ZIP1 Q20 Q25 Q6 16 128 *)
  0x4e467b35;       (* arm_ZIP2 Q21 Q25 Q6 16 128 *)
  0x4e473b36;       (* arm_ZIP1 Q22 Q25 Q7 16 128 *)
  0x4e477b37;       (* arm_ZIP2 Q23 Q25 Q7 16 128 *)
  0x4eb8b508;       (* arm_SQDMULH_VEC Q8 Q8 Q24 32 128 *)
  0x4eb8b529;       (* arm_SQDMULH_VEC Q9 Q9 Q24 32 128 *)
  0x4eb8b54a;       (* arm_SQDMULH_VEC Q10 Q10 Q24 32 128 *)
  0x4eb8b56b;       (* arm_SQDMULH_VEC Q11 Q11 Q24 32 128 *)
  0x4eb8b58c;       (* arm_SQDMULH_VEC Q12 Q12 Q24 32 128 *)
  0x4eb8b5ad;       (* arm_SQDMULH_VEC Q13 Q13 Q24 32 128 *)
  0x4eb8b5ce;       (* arm_SQDMULH_VEC Q14 Q14 Q24 32 128 *)
  0x4eb8b5ef;       (* arm_SQDMULH_VEC Q15 Q15 Q24 32 128 *)
  0x4eb8b610;       (* arm_SQDMULH_VEC Q16 Q16 Q24 32 128 *)
  0x4eb8b631;       (* arm_SQDMULH_VEC Q17 Q17 Q24 32 128 *)
  0x4eb8b652;       (* arm_SQDMULH_VEC Q18 Q18 Q24 32 128 *)
  0x4eb8b673;       (* arm_SQDMULH_VEC Q19 Q19 Q24 32 128 *)
  0x4eb8b694;       (* arm_SQDMULH_VEC Q20 Q20 Q24 32 128 *)
  0x4eb8b6b5;       (* arm_SQDMULH_VEC Q21 Q21 Q24 32 128 *)
  0x4eb8b6d6;       (* arm_SQDMULH_VEC Q22 Q22 Q24 32 128 *)
  0x4eb8b6f7;       (* arm_SQDMULH_VEC Q23 Q23 Q24 32 128 *)
  0x2e794100;       (* arm_RADDHN Q0 Q8 Q25 16 *)
  0x6e794120;       (* arm_RADDHN2 Q0 Q9 Q25 16 *)
  0x2e794141;       (* arm_RADDHN Q1 Q10 Q25 16 *)
  0x6e794161;       (* arm_RADDHN2 Q1 Q11 Q25 16 *)
  0x2e794182;       (* arm_RADDHN Q2 Q12 Q25 16 *)
  0x6e7941a2;       (* arm_RADDHN2 Q2 Q13 Q25 16 *)
  0x2e7941c3;       (* arm_RADDHN Q3 Q14 Q25 16 *)
  0x6e7941e3;       (* arm_RADDHN2 Q3 Q15 Q25 16 *)
  0x2e794204;       (* arm_RADDHN Q4 Q16 Q25 16 *)
  0x6e794224;       (* arm_RADDHN2 Q4 Q17 Q25 16 *)
  0x2e794245;       (* arm_RADDHN Q5 Q18 Q25 16 *)
  0x6e794265;       (* arm_RADDHN2 Q5 Q19 Q25 16 *)
  0x2e794286;       (* arm_RADDHN Q6 Q20 Q25 16 *)
  0x6e7942a6;       (* arm_RADDHN2 Q6 Q21 Q25 16 *)
  0x2e7942c7;       (* arm_RADDHN Q7 Q22 Q25 16 *)
  0x6e7942e7;       (* arm_RADDHN2 Q7 Q23 Q25 16 *)
  0x6f07b780;       (* arm_BIC_VEC Q0 Q0 (rvalue (word 334970566183010332722197645145925549056)) 128 *)
  0x6f07b781;       (* arm_BIC_VEC Q1 Q1 (rvalue (word 334970566183010332722197645145925549056)) 128 *)
  0x6f07b782;       (* arm_BIC_VEC Q2 Q2 (rvalue (word 334970566183010332722197645145925549056)) 128 *)
  0x6f07b783;       (* arm_BIC_VEC Q3 Q3 (rvalue (word 334970566183010332722197645145925549056)) 128 *)
  0x6f07b784;       (* arm_BIC_VEC Q4 Q4 (rvalue (word 334970566183010332722197645145925549056)) 128 *)
  0x6f07b785;       (* arm_BIC_VEC Q5 Q5 (rvalue (word 334970566183010332722197645145925549056)) 128 *)
  0x6f07b786;       (* arm_BIC_VEC Q6 Q6 (rvalue (word 334970566183010332722197645145925549056)) 128 *)
  0x6f07b787;       (* arm_BIC_VEC Q7 Q7 (rvalue (word 334970566183010332722197645145925549056)) 128 *)
  0x6e7a4400;       (* arm_USHL_VEC Q0 Q0 Q26 16 128 *)
  0x6e7a4421;       (* arm_USHL_VEC Q1 Q1 Q26 16 128 *)
  0x6e7a4442;       (* arm_USHL_VEC Q2 Q2 Q26 16 128 *)
  0x6e7a4463;       (* arm_USHL_VEC Q3 Q3 Q26 16 128 *)
  0x6e7a4484;       (* arm_USHL_VEC Q4 Q4 Q26 16 128 *)
  0x6e7a44a5;       (* arm_USHL_VEC Q5 Q5 Q26 16 128 *)
  0x6e7a44c6;       (* arm_USHL_VEC Q6 Q6 Q26 16 128 *)
  0x6e7a44e7;       (* arm_USHL_VEC Q7 Q7 Q26 16 128 *)
  0x4e1b0008;       (* arm_TBL Q8 [Q0] Q27 128 *)
  0x4e1c0010;       (* arm_TBL Q16 [Q0] Q28 128 *)
  0x4e1b0029;       (* arm_TBL Q9 [Q1] Q27 128 *)
  0x4e1c0031;       (* arm_TBL Q17 [Q1] Q28 128 *)
  0x4e1b004a;       (* arm_TBL Q10 [Q2] Q27 128 *)
  0x4e1c0052;       (* arm_TBL Q18 [Q2] Q28 128 *)
  0x4e1b006b;       (* arm_TBL Q11 [Q3] Q27 128 *)
  0x4e1c0073;       (* arm_TBL Q19 [Q3] Q28 128 *)
  0x4e1b008c;       (* arm_TBL Q12 [Q4] Q27 128 *)
  0x4e1c0094;       (* arm_TBL Q20 [Q4] Q28 128 *)
  0x4e1b00ad;       (* arm_TBL Q13 [Q5] Q27 128 *)
  0x4e1c00b5;       (* arm_TBL Q21 [Q5] Q28 128 *)
  0x4e1b00ce;       (* arm_TBL Q14 [Q6] Q27 128 *)
  0x4e1c00d6;       (* arm_TBL Q22 [Q6] Q28 128 *)
  0x4e1b00ef;       (* arm_TBL Q15 [Q7] Q27 128 *)
  0x4e1c00f7;       (* arm_TBL Q23 [Q7] Q28 128 *)
  0x4eb01d00;       (* arm_ORR_VEC Q0 Q8 Q16 128 *)
  0x4eb11d21;       (* arm_ORR_VEC Q1 Q9 Q17 128 *)
  0x4eb21d42;       (* arm_ORR_VEC Q2 Q10 Q18 128 *)
  0x4eb31d63;       (* arm_ORR_VEC Q3 Q11 Q19 128 *)
  0x4eb41d84;       (* arm_ORR_VEC Q4 Q12 Q20 128 *)
  0x4eb51da5;       (* arm_ORR_VEC Q5 Q13 Q21 128 *)
  0x4eb61dc6;       (* arm_ORR_VEC Q6 Q14 Q22 128 *)
  0x4eb71de7;       (* arm_ORR_VEC Q7 Q15 Q23 128 *)
  0x6e013328;       (* arm_EXT Q8 Q25 Q1 48 *)
  0x6e19302c;       (* arm_EXT Q12 Q1 Q25 48 *)
  0x6e033329;       (* arm_EXT Q9 Q25 Q3 48 *)
  0x6e19306d;       (* arm_EXT Q13 Q3 Q25 48 *)
  0x6e05332a;       (* arm_EXT Q10 Q25 Q5 48 *)
  0x6e1930ae;       (* arm_EXT Q14 Q5 Q25 48 *)
  0x6e07332b;       (* arm_EXT Q11 Q25 Q7 48 *)
  0x6e1930ef;       (* arm_EXT Q15 Q7 Q25 48 *)
  0x4ea81c00;       (* arm_ORR_VEC Q0 Q0 Q8 128 *)
  0x4ea91c42;       (* arm_ORR_VEC Q2 Q2 Q9 128 *)
  0x4eaa1c84;       (* arm_ORR_VEC Q4 Q4 Q10 128 *)
  0x4eab1cc6;       (* arm_ORR_VEC Q6 Q6 Q11 128 *)
  0x3c810400;       (* arm_STR Q0 X0 (Postimmediate_Offset (word 16)) *)
  0xbc00440c;       (* arm_STR (SREG 12) X0 (Postimmediate_Offset (word 4)) *)
  0x3c810402;       (* arm_STR Q2 X0 (Postimmediate_Offset (word 16)) *)
  0xbc00440d;       (* arm_STR (SREG 13) X0 (Postimmediate_Offset (word 4)) *)
  0x3c810404;       (* arm_STR Q4 X0 (Postimmediate_Offset (word 16)) *)
  0xbc00440e;       (* arm_STR (SREG 14) X0 (Postimmediate_Offset (word 4)) *)
  0x3c810406;       (* arm_STR Q6 X0 (Postimmediate_Offset (word 16)) *)
  0xbc00440f;       (* arm_STR (SREG 15) X0 (Postimmediate_Offset (word 4)) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fff1e1;       (* arm_BNE (word 2096700) *)
  0x6cc13fee;       (* arm_LDP D14 D15 SP (Postimmediate_Offset (iword (&16))) *)
  0x6cc137ec;       (* arm_LDP D12 D13 SP (Postimmediate_Offset (iword (&16))) *)
  0x6cc12fea;       (* arm_LDP D10 D11 SP (Postimmediate_Offset (iword (&16))) *)
  0x6cc127e8;       (* arm_LDP D8 D9 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_compress_d10_tmc =
  define_trimmed "mlkem_compress_d10_tmc" mlkem_compress_d10_mc;;

let MLKEM_COMPRESS_D10_EXEC = ARM_MK_EXEC_RULE mlkem_compress_d10_tmc;;

(* ------------------------------------------------------------------------- *)
(* The rounding of each coefficient, as the code computes it (abbreviated,   *)
(* to keep the terms small in the simulation), checked for all the 3329      *)
(* possible values.                                                          *)
(* ------------------------------------------------------------------------- *)

let compress_d10_lane = new_definition
 `compress_d10_lane (x:int16) =
  word_subword
   (word_add
     (iword_saturate((&2 * ival(word_join x (word 0:int16):int32) *
                      &660565712) div &4294967296):int32)
     (word 32768))
   (16,16):int16`;;

let COMPRESS_D10_LANE = time prove
 (`!x:int16.
        val x < 3329
        ==> ((2048 * val x + 3329) DIV 6658) MOD 1024 =
            val(compress_d10_lane x) MOD 1024`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[compress_d10_lane] THEN
  SUBST1_TAC(SYM(ISPEC `x:int16` WORD_VAL)) THEN
  UNDISCH_TAC `val(x:int16) < 3329` THEN
  SPEC_TAC(`val(x:int16)`,`n:num`) THEN
  REWRITE_TAC[iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_32] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

let BIT_OF_VAL_MOD1024 = GEN `y:int16`
  (CONV_RULE (ONCE_DEPTH_CONV NUM_EXP_CONV)
    (ISPECL [`y:int16`; `10`] BIT_OF_VAL_MOD));;

(* The lookups of the out-of-range index 255 give 0. *)

let SUBWORD_BEYOND_TAC =
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o CONV_RULE(RAND_CONV(DEPTH_CONV WORD_SUBWORD_BEYOND_CONV)) o
    check (can (term_match [] `read X (s:armstate):int128 = whatever`) o
           concl)));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The result is checked bit by bit.                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_COMPRESS_D10_CORRECT = prove
 (`!r a x pc.
        ALL (nonoverlapping (r,320)) [(word pc,0x264); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d10_tmc /\
                  read PC s = word(pc + 0x10) /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = word(pc + 0x250) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,320)) s =
                       nsum {i | i < 256}
                            (\i. ((2048 * val(x i) + 3329) DIV 6658) MOD 1024 *
                                 2 EXP (10 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
              MAYCHANGE [memory :> bytes(r,320)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Restructure the inputs to match the 128-bit loads ***)

  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
            (subst[mk_small_numeral(16*n),`n:num`]
                  `read (memory :> bytes128(word_add a (word n))) s0`))
            (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  STRIP_TAC THEN

  (*** Simulate the whole thing, unrolling the loop ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_COMPRESS_D10_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[compress_d10_lane] THEN
                      SUBWORD_BEYOND_TAC) (1--486) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES_EQ_BITS THEN
  REWRITE_TAC[ARITH_RULE `8 * 320 = 10 * 256`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_FIELD_BOUND THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ];
    ALL_TAC] THEN

  (*** Bit p of the result is bit p MOD 10 of coefficient p DIV 10 ***)

  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP p = 2 EXP (10 * p DIV 10 + p MOD 10)` SUBST1_TAC THENL
   [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ODD_MOD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_FIELD_BIT o
    lhand o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `p < 10 * 256` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p DIV 10` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `p < 10 * 256` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP COMPRESS_D10_LANE) THEN
  SIMP_TAC[BIT_OF_VAL_MOD1024; MOD_LT_EQ; ARITH_EQ] THEN

  (*** Split the stored data into bytes, and check each bit ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
   check (can (term_match [] `read (memory :> bytes128 a) s = xxx`) o
          concl))) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
   check (can (term_match [] `read (memory :> bytes32 a) s = xxx`) o
          concl))) THEN
  UNDISCH_TAC `p < 10 * 256` THEN SPEC_TAC(`p:num`,`p:num`) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s486" THEN
  CONV_TAC(DEPTH_CONV WORD_MUL_POW2_CONV) THEN
  CHUNKED_ATOMS_BITBLAST_TAC 8 [`compress_d10_lane y`]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad. The lower     *)
(* halves of Q8-Q15, used in the core, are saved on the stack and restored.  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_COMPRESS_D10_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a x pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALLPAIRS nonoverlapping
         [(r,320); (word_sub stackpointer (word 64),64)]
         [(word pc,0x264); (a,512)] /\
        nonoverlapping (r,320) (word_sub stackpointer (word 64),64)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d10_tmc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,320)) s =
                       nsum {i | i < 256}
                            (\i. ((2048 * val(x i) + 3329) DIV 6658) MOD 1024 *
                                 2 EXP (10 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,320);
                       memory :> bytes(word_sub stackpointer (word 64),64)])`,
  let TWEAK_CONV =
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0] in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(4,4) MLKEM_COMPRESS_D10_EXEC
   (CONV_RULE TWEAK_CONV MLKEM_COMPRESS_D10_CORRECT)
   `[D8; D9; D10; D11; D12; D13; D14; D15]` 64);;

let MLKEM_COMPRESS_D10_SUBROUTINE_CORRECT = prove
 (`!r a x pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALLPAIRS nonoverlapping
         [(r,320); (word_sub stackpointer (word 64),64)]
         [(word pc,0x268); (a,512)] /\
        nonoverlapping (r,320) (word_sub stackpointer (word 64),64)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d10_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,320)) s =
                       nsum {i | i < 256}
                            (\i. ((2048 * val(x i) + 3329) DIV 6658) MOD 1024 *
                                 2 EXP (10 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,320);
                       memory :> bytes(word_sub stackpointer (word 64),64)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_compress_d10_mc mlkem_compress_d10_tmc
    MLKEM_COMPRESS_D10_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_compress_d10" subroutine_signatures)
    MLKEM_COMPRESS_D10_NOIBT_SUBROUTINE_CORRECT
    MLKEM_COMPRESS_D10_EXEC;;

let MLKEM_COMPRESS_D10_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 stackpointer /\
           ALLPAIRS nonoverlapping
            [(r,320); (word_sub stackpointer (word 64),64)]
            [(word pc,0x264); (a,512)] /\
           nonoverlapping (r,320) (word_sub stackpointer (word 64),64)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d10_tmc /\
                    read PC s = word pc /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc (word_sub stackpointer (word 64))
                                      returnaddress /\
                        memaccess_inbounds e2
                         [a,512; r,320; word_sub stackpointer (word 64),64]
                         [r,320; word_sub stackpointer (word 64),64])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_COMPRESS_D10_EXEC);;

let MLKEM_COMPRESS_D10_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 stackpointer /\
           ALLPAIRS nonoverlapping
            [(r,320); (word_sub stackpointer (word 64),64)]
            [(word pc,0x268); (a,512)] /\
           nonoverlapping (r,320) (word_sub stackpointer (word 64),64)
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d10_mc /\
                    read PC s = word pc /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc (word_sub stackpointer (word 64))
                                      returnaddress /\
                        memaccess_inbounds e2
                         [a,512; r,320; word_sub stackpointer (word 64),64]
                         [r,320; word_sub stackpointer (word 64),64])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_compress_d10_mc mlkem_compress_d10_tmc
    MLKEM_COMPRESS_D10_NOIBT_SUBROUTINE_SAFE));;
