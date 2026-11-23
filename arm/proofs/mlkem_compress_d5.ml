(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 5 bits, and packing them.       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_compress_d5.o";;
 ****)

let mlkem_compress_d5_mc = define_assert_from_elf
  "mlkem_compress_d5_mc" "arm/mlkem/mlkem_compress_d5.o"
[
  0xd503245f;       (* arm_BTI *)
  0xd2806002;       (* arm_MOV X2 (rvalue (word 768)) *)
  0xf2a120e2;       (* arm_MOVK X2 (word 2311) 16 *)
  0xf2c201a2;       (* arm_MOVK X2 (word 4109) 32 *)
  0xf2e2e262;       (* arm_MOVK X2 (word 5907) 48 *)
  0xd283a323;       (* arm_MOV X3 (rvalue (word 7449)) *)
  0xf2bfffe3;       (* arm_MOVK X3 (word 65535) 16 *)
  0xf2dfffe3;       (* arm_MOVK X3 (word 65535) 32 *)
  0xf2ffffe3;       (* arm_MOVK X3 (word 65535) 48 *)
  0x9e67005c;       (* arm_FMOV_ItoF Q28 X2 0 *)
  0x4e181c7c;       (* arm_INS_GEN Q28 X3 64 64 *)
  0xd2808042;       (* arm_MOV X2 (rvalue (word 1026)) *)
  0xf2a14102;       (* arm_MOVK X2 (word 2568) 16 *)
  0xf2c241c2;       (* arm_MOVK X2 (word 4622) 32 *)
  0xf2e30282;       (* arm_MOVK X2 (word 6164) 48 *)
  0xd283c343;       (* arm_MOV X3 (rvalue (word 7706)) *)
  0xf2bfffe3;       (* arm_MOVK X3 (word 65535) 16 *)
  0xf2dfffe3;       (* arm_MOVK X3 (word 65535) 32 *)
  0xf2ffffe3;       (* arm_MOVK X3 (word 65535) 48 *)
  0x9e67005d;       (* arm_FMOV_ItoF Q29 X2 0 *)
  0x4e181c7d;       (* arm_INS_GEN Q29 X3 64 64 *)
  0xd280dfe2;       (* arm_MOV X2 (rvalue (word 1791)) *)
  0xf2a19fe2;       (* arm_MOVK X2 (word 3327) 16 *)
  0xf2dfffe2;       (* arm_MOVK X2 (word 65535) 32 *)
  0xf2ffe2c2;       (* arm_MOVK X2 (word 65302) 48 *)
  0xd29fe383;       (* arm_MOV X3 (rvalue (word 65308)) *)
  0xf2bfffe3;       (* arm_MOVK X3 (word 65535) 16 *)
  0xf2dfffe3;       (* arm_MOVK X3 (word 65535) 32 *)
  0xf2ffffe3;       (* arm_MOVK X3 (word 65535) 48 *)
  0x9e67005e;       (* arm_FMOV_ItoF Q30 X2 0 *)
  0x4e181c7e;       (* arm_INS_GEN Q30 X3 64 64 *)
  0xd2800022;       (* arm_MOV X2 (rvalue (word 1)) *)
  0xf2a00402;       (* arm_MOVK X2 (word 32) 16 *)
  0xf2c00082;       (* arm_MOVK X2 (word 4) 32 *)
  0xf2e01002;       (* arm_MOVK X2 (word 128) 48 *)
  0xd2800203;       (* arm_MOV X3 (rvalue (word 16)) *)
  0xf2a00043;       (* arm_MOVK X3 (word 2) 16 *)
  0xf2c00803;       (* arm_MOVK X3 (word 64) 32 *)
  0xf2e00103;       (* arm_MOVK X3 (word 8) 48 *)
  0x9e67005f;       (* arm_FMOV_ItoF Q31 X2 0 *)
  0x4e181c7f;       (* arm_INS_GEN Q31 X3 64 64 *)
  0x5289d7e2;       (* arm_MOV W2 (rvalue (word 20159)) *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x4e020c5a;       (* arm_DUP_GEN Q26 X2 16 128 *)
  0x4f0087fb;       (* arm_MOVI Q27 (word 8725857424048159) *)
  0xacc10420;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc10c22;       (* arm_LDP Q2 Q3 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc11424;       (* arm_LDP Q4 Q5 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc11c26;       (* arm_LDP Q6 Q7 X1 (Postimmediate_Offset (iword (&32))) *)
  0x4e7ab400;       (* arm_SQDMULH_VEC Q0 Q0 Q26 16 128 *)
  0x4e7ab421;       (* arm_SQDMULH_VEC Q1 Q1 Q26 16 128 *)
  0x4e7ab442;       (* arm_SQDMULH_VEC Q2 Q2 Q26 16 128 *)
  0x4e7ab463;       (* arm_SQDMULH_VEC Q3 Q3 Q26 16 128 *)
  0x4e7ab484;       (* arm_SQDMULH_VEC Q4 Q4 Q26 16 128 *)
  0x4e7ab4a5;       (* arm_SQDMULH_VEC Q5 Q5 Q26 16 128 *)
  0x4e7ab4c6;       (* arm_SQDMULH_VEC Q6 Q6 Q26 16 128 *)
  0x4e7ab4e7;       (* arm_SQDMULH_VEC Q7 Q7 Q26 16 128 *)
  0x6f1a2400;       (* arm_URSHR_VEC Q0 Q0 6 16 128 *)
  0x6f1a2421;       (* arm_URSHR_VEC Q1 Q1 6 16 128 *)
  0x6f1a2442;       (* arm_URSHR_VEC Q2 Q2 6 16 128 *)
  0x6f1a2463;       (* arm_URSHR_VEC Q3 Q3 6 16 128 *)
  0x6f1a2484;       (* arm_URSHR_VEC Q4 Q4 6 16 128 *)
  0x6f1a24a5;       (* arm_URSHR_VEC Q5 Q5 6 16 128 *)
  0x6f1a24c6;       (* arm_URSHR_VEC Q6 Q6 6 16 128 *)
  0x6f1a24e7;       (* arm_URSHR_VEC Q7 Q7 6 16 128 *)
  0x4e3b1c00;       (* arm_AND_VEC Q0 Q0 Q27 128 *)
  0x4e3b1c21;       (* arm_AND_VEC Q1 Q1 Q27 128 *)
  0x4e3b1c42;       (* arm_AND_VEC Q2 Q2 Q27 128 *)
  0x4e3b1c63;       (* arm_AND_VEC Q3 Q3 Q27 128 *)
  0x4e3b1c84;       (* arm_AND_VEC Q4 Q4 Q27 128 *)
  0x4e3b1ca5;       (* arm_AND_VEC Q5 Q5 Q27 128 *)
  0x4e3b1cc6;       (* arm_AND_VEC Q6 Q6 Q27 128 *)
  0x4e3b1ce7;       (* arm_AND_VEC Q7 Q7 Q27 128 *)
  0x4e7f9c00;       (* arm_MUL_VEC Q0 Q0 Q31 16 128 *)
  0x4e7f9c21;       (* arm_MUL_VEC Q1 Q1 Q31 16 128 *)
  0x4e7f9c42;       (* arm_MUL_VEC Q2 Q2 Q31 16 128 *)
  0x4e7f9c63;       (* arm_MUL_VEC Q3 Q3 Q31 16 128 *)
  0x4e7f9c84;       (* arm_MUL_VEC Q4 Q4 Q31 16 128 *)
  0x4e7f9ca5;       (* arm_MUL_VEC Q5 Q5 Q31 16 128 *)
  0x4e7f9cc6;       (* arm_MUL_VEC Q6 Q6 Q31 16 128 *)
  0x4e7f9ce7;       (* arm_MUL_VEC Q7 Q7 Q31 16 128 *)
  0x4e1c2018;       (* arm_TBL2 Q24 Q0 Q1 Q28 128 *)
  0x4e1d2010;       (* arm_TBL2 Q16 Q0 Q1 Q29 128 *)
  0x4e1e2014;       (* arm_TBL2 Q20 Q0 Q1 Q30 128 *)
  0x4e1c2059;       (* arm_TBL2 Q25 Q2 Q3 Q28 128 *)
  0x4e1d2051;       (* arm_TBL2 Q17 Q2 Q3 Q29 128 *)
  0x4e1e2055;       (* arm_TBL2 Q21 Q2 Q3 Q30 128 *)
  0x4e1c209a;       (* arm_TBL2 Q26 Q4 Q5 Q28 128 *)
  0x4e1d2092;       (* arm_TBL2 Q18 Q4 Q5 Q29 128 *)
  0x4e1e2096;       (* arm_TBL2 Q22 Q4 Q5 Q30 128 *)
  0x4e1c20db;       (* arm_TBL2 Q27 Q6 Q7 Q28 128 *)
  0x4e1d20d3;       (* arm_TBL2 Q19 Q6 Q7 Q29 128 *)
  0x4e1e20d7;       (* arm_TBL2 Q23 Q6 Q7 Q30 128 *)
  0x4eb01f18;       (* arm_ORR_VEC Q24 Q24 Q16 128 *)
  0x4eb11f39;       (* arm_ORR_VEC Q25 Q25 Q17 128 *)
  0x4eb21f5a;       (* arm_ORR_VEC Q26 Q26 Q18 128 *)
  0x4eb31f7b;       (* arm_ORR_VEC Q27 Q27 Q19 128 *)
  0x4eb41f18;       (* arm_ORR_VEC Q24 Q24 Q20 128 *)
  0x4eb51f39;       (* arm_ORR_VEC Q25 Q25 Q21 128 *)
  0x4eb61f5a;       (* arm_ORR_VEC Q26 Q26 Q22 128 *)
  0x4eb71f7b;       (* arm_ORR_VEC Q27 Q27 Q23 128 *)
  0xfc008418;       (* arm_STR D24 X0 (Postimmediate_Offset (word 8)) *)
  0x4d9f4018;       (* arm_ST1 Q24 X0 (Postimmediate_Offset (word 2)) 16 4 *)
  0xfc008419;       (* arm_STR D25 X0 (Postimmediate_Offset (word 8)) *)
  0x4d9f4019;       (* arm_ST1 Q25 X0 (Postimmediate_Offset (word 2)) 16 4 *)
  0xfc00841a;       (* arm_STR D26 X0 (Postimmediate_Offset (word 8)) *)
  0x4d9f401a;       (* arm_ST1 Q26 X0 (Postimmediate_Offset (word 2)) 16 4 *)
  0xfc00841b;       (* arm_STR D27 X0 (Postimmediate_Offset (word 8)) *)
  0x4d9f401b;       (* arm_ST1 Q27 X0 (Postimmediate_Offset (word 2)) 16 4 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fff7a1;       (* arm_BNE (word 2096884) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_compress_d5_tmc =
  define_trimmed "mlkem_compress_d5_tmc" mlkem_compress_d5_mc;;

let MLKEM_COMPRESS_D5_EXEC = ARM_MK_EXEC_RULE mlkem_compress_d5_tmc;;

(* ------------------------------------------------------------------------- *)
(* The rounding of each coefficient, as the code computes it (abbreviated,   *)
(* to keep the terms small in the simulation), checked for all the 3329      *)
(* possible values.                                                          *)
(* ------------------------------------------------------------------------- *)

let compress_d5_lane = new_definition
 `compress_d5_lane (x:int16) =
  word((val(iword_saturate((&2 * ival x * &20159) div &65536):int16) + 32)
       DIV 64):int16`;;

let COMPRESS_D5_LANE = time prove
 (`!x:int16.
        val x < 3329
        ==> ((64 * val x + 3329) DIV 6658) MOD 32 =
            val(compress_d5_lane x) MOD 32`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[compress_d5_lane] THEN
  ASM_SIMP_TAC[IVAL_VAL_SMALL; ARITH_RULE `n < 3329 ==> n < 32768`] THEN
  UNDISCH_TAC `val(x:int16) < 3329` THEN
  SPEC_TAC(`val(x:int16)`,`n:num`) THEN
  REWRITE_TAC[iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_16] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

let BIT_OF_VAL_MOD32 = GEN `y:int16`
  (CONV_RULE (ONCE_DEPTH_CONV NUM_EXP_CONV)
    (ISPECL [`y:int16`; `5`] BIT_OF_VAL_MOD));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The result is checked bit by bit.                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_COMPRESS_D5_CORRECT = prove
 (`!r a x pc.
        ALL (nonoverlapping (r,160)) [(word pc,0x1bc); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d5_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = word(pc + 0x1b8) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,160)) s =
                       nsum {i | i < 256}
                            (\i. ((64 * val(x i) + 3329) DIV 6658) MOD 32 *
                                 2 EXP (5 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,160)])`,
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

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_COMPRESS_D5_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[compress_d5_lane]) (1--314) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES_EQ_BITS THEN
  REWRITE_TAC[ARITH_RULE `8 * 160 = 5 * 256`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_FIELD_BOUND THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ];
    ALL_TAC] THEN

  (*** Bit p of the result is bit p MOD 5 of coefficient p DIV 5 ***)

  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP p = 2 EXP (5 * p DIV 5 + p MOD 5)` SUBST1_TAC THENL
   [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ODD_MOD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_FIELD_BIT o
    lhand o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `p < 5 * 256` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p DIV 5` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `p < 5 * 256` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP COMPRESS_D5_LANE) THEN
  SIMP_TAC[BIT_OF_VAL_MOD32; MOD_LT_EQ; ARITH_EQ] THEN

  (*** Split the stored data into bytes, and check each bit ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
   check (can (term_match [] `read (memory :> bytes128 a) s = xxx`) o
          concl))) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read (memory :> bytes64 a) s = xxx`) o
          concl))) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 1) o
   check (can (term_match [] `read (memory :> bytes16 a) s = xxx`) o
          concl))) THEN
  UNDISCH_TAC `p < 5 * 256` THEN SPEC_TAC(`p:num`,`p:num`) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s314" THEN
  CONV_TAC(DEPTH_CONV WORD_MUL_POW2_CONV) THEN
  CHUNKED_ATOMS_BITBLAST_TAC 8 [`compress_d5_lane y`]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_COMPRESS_D5_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a x pc returnaddress.
        ALL (nonoverlapping (r,160)) [(word pc,0x1bc); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d5_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,160)) s =
                       nsum {i | i < 256}
                            (\i. ((64 * val(x i) + 3329) DIV 6658) MOD 32 *
                                 2 EXP (5 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,160)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_COMPRESS_D5_EXEC
    MLKEM_COMPRESS_D5_CORRECT);;

let MLKEM_COMPRESS_D5_SUBROUTINE_CORRECT = prove
 (`!r a x pc returnaddress.
        ALL (nonoverlapping (r,160)) [(word pc,0x1c0); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d5_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,160)) s =
                       nsum {i | i < 256}
                            (\i. ((64 * val(x i) + 3329) DIV 6658) MOD 32 *
                                 2 EXP (5 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,160)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE mlkem_compress_d5_mc mlkem_compress_d5_tmc
    MLKEM_COMPRESS_D5_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_compress_d5" subroutine_signatures)
    MLKEM_COMPRESS_D5_NOIBT_SUBROUTINE_CORRECT
    MLKEM_COMPRESS_D5_EXEC;;

let MLKEM_COMPRESS_D5_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,160)) [(word pc,0x1bc); (a,512)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d5_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,160] [r,160])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_COMPRESS_D5_EXEC);;

let MLKEM_COMPRESS_D5_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,160)) [(word pc,0x1c0); (a,512)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d5_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,160] [r,160])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE mlkem_compress_d5_mc mlkem_compress_d5_tmc
    MLKEM_COMPRESS_D5_NOIBT_SUBROUTINE_SAFE));;
