(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 4 bits, and packing them.       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_compress_d4.o";;
 ****)

let mlkem_compress_d4_mc = define_assert_from_elf
  "mlkem_compress_d4_mc" "arm/mlkem/mlkem_compress_d4.o"
[
  0xd503245f;       (* arm_BTI *)
  0x5289d7e2;       (* arm_MOV W2 (rvalue (word 20159)) *)
  0x4e020c5f;       (* arm_DUP_GEN Q31 X2 16 128 *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0xacc10420;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc10c22;       (* arm_LDP Q2 Q3 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc11424;       (* arm_LDP Q4 Q5 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc11c26;       (* arm_LDP Q6 Q7 X1 (Postimmediate_Offset (iword (&32))) *)
  0x4e7fb400;       (* arm_SQDMULH_VEC Q0 Q0 Q31 16 128 *)
  0x4e7fb421;       (* arm_SQDMULH_VEC Q1 Q1 Q31 16 128 *)
  0x4e7fb442;       (* arm_SQDMULH_VEC Q2 Q2 Q31 16 128 *)
  0x4e7fb463;       (* arm_SQDMULH_VEC Q3 Q3 Q31 16 128 *)
  0x4e7fb484;       (* arm_SQDMULH_VEC Q4 Q4 Q31 16 128 *)
  0x4e7fb4a5;       (* arm_SQDMULH_VEC Q5 Q5 Q31 16 128 *)
  0x4e7fb4c6;       (* arm_SQDMULH_VEC Q6 Q6 Q31 16 128 *)
  0x4e7fb4e7;       (* arm_SQDMULH_VEC Q7 Q7 Q31 16 128 *)
  0x6f192400;       (* arm_URSHR_VEC Q0 Q0 7 16 128 *)
  0x6f192421;       (* arm_URSHR_VEC Q1 Q1 7 16 128 *)
  0x6f192442;       (* arm_URSHR_VEC Q2 Q2 7 16 128 *)
  0x6f192463;       (* arm_URSHR_VEC Q3 Q3 7 16 128 *)
  0x6f192484;       (* arm_URSHR_VEC Q4 Q4 7 16 128 *)
  0x6f1924a5;       (* arm_URSHR_VEC Q5 Q5 7 16 128 *)
  0x6f1924c6;       (* arm_URSHR_VEC Q6 Q6 7 16 128 *)
  0x6f1924e7;       (* arm_URSHR_VEC Q7 Q7 7 16 128 *)
  0x4e011810;       (* arm_UZP1 Q16 Q0 Q1 8 128 *)
  0x4e031851;       (* arm_UZP1 Q17 Q2 Q3 8 128 *)
  0x4e051892;       (* arm_UZP1 Q18 Q4 Q5 8 128 *)
  0x4e0718d3;       (* arm_UZP1 Q19 Q6 Q7 8 128 *)
  0x4e111a14;       (* arm_UZP1 Q20 Q16 Q17 8 128 *)
  0x4e115a15;       (* arm_UZP2 Q21 Q16 Q17 8 128 *)
  0x4e131a56;       (* arm_UZP1 Q22 Q18 Q19 8 128 *)
  0x4e135a57;       (* arm_UZP2 Q23 Q18 Q19 8 128 *)
  0x6f0c56b4;       (* arm_SLI_VEC Q20 Q21 4 128 8 *)
  0x6f0c56f6;       (* arm_SLI_VEC Q22 Q23 4 128 8 *)
  0xac815814;       (* arm_STP Q20 Q22 X0 (Postimmediate_Offset (iword (&32))) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffc01;       (* arm_BNE (word 2097024) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_compress_d4_tmc =
  define_trimmed "mlkem_compress_d4_tmc" mlkem_compress_d4_mc;;

let MLKEM_COMPRESS_D4_EXEC = ARM_MK_EXEC_RULE mlkem_compress_d4_tmc;;

(* ------------------------------------------------------------------------- *)
(* The rounding of each coefficient, as the code computes it, checked for    *)
(* all the 3329 possible values.                                             *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D4_LANE = time prove
 (`!x:int16.
        val x < 3329
        ==> ((32 * val x + 3329) DIV 6658) MOD 16 =
            val(word((val(iword_saturate((&2 * ival x * &20159) div &65536)
                          :int16) + 64) DIV 128):int16) MOD 16`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[IVAL_VAL_SMALL; ARITH_RULE `n < 3329 ==> n < 32768`] THEN
  UNDISCH_TAC `val(x:int16) < 3329` THEN
  SPEC_TAC(`val(x:int16)`,`n:num`) THEN
  REWRITE_TAC[iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_16] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

let BIT_OF_VAL_MOD16 = GEN `y:int16`
  (CONV_RULE (ONCE_DEPTH_CONV NUM_EXP_CONV)
    (ISPECL [`y:int16`; `4`] BIT_OF_VAL_MOD));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The result is checked bit by bit.                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_COMPRESS_D4_CORRECT = prove
 (`!r a x pc.
        ALL (nonoverlapping (r,128)) [(word pc,0x94); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d4_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = word(pc + 0x90) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,128)) s =
                       nsum {i | i < 256}
                            (\i. ((32 * val(x i) + 3329) DIV 6658) MOD 16 *
                                 2 EXP (4 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
            (subst[mk_small_numeral(16*n),`n:num`]
                  `read (memory :> bytes128(word_add a (word n))) s0`))
            (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_COMPRESS_D4_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (1--135) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES_EQ_BITS THEN
  REWRITE_TAC[ARITH_RULE `8 * 128 = 4 * 256`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_FIELD_BOUND THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ];
    ALL_TAC] THEN

  (*** Bit p of the result is bit p MOD 4 of coefficient p DIV 4 ***)

  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP p = 2 EXP (4 * p DIV 4 + p MOD 4)` SUBST1_TAC THENL
   [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ODD_MOD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_FIELD_BIT o
    lhand o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `p < 4 * 256` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p DIV 4` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `p < 4 * 256` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP COMPRESS_D4_LANE) THEN
  SIMP_TAC[BIT_OF_VAL_MOD16; MOD_LT_EQ; ARITH_EQ] THEN

  (*** Split the stored vectors into bytes, and check each bit ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
   check (can (term_match [] `read (memory :> bytes128 a) s = xxx`) o
          concl))) THEN
  UNDISCH_TAC `p < 4 * 256` THEN SPEC_TAC(`p:num`,`p:num`) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s135" THEN
  CHUNKED_ATOMS_BITBLAST_TAC 8 [`word((val (y:int16) + 64) DIV 128):int16`]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_COMPRESS_D4_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a x pc returnaddress.
        ALL (nonoverlapping (r,128)) [(word pc,0x94); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d4_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,128)) s =
                       nsum {i | i < 256}
                            (\i. ((32 * val(x i) + 3329) DIV 6658) MOD 16 *
                                 2 EXP (4 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_COMPRESS_D4_EXEC
    MLKEM_COMPRESS_D4_CORRECT);;

let MLKEM_COMPRESS_D4_SUBROUTINE_CORRECT = prove
 (`!r a x pc returnaddress.
        ALL (nonoverlapping (r,128)) [(word pc,0x98); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d4_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,128)) s =
                       nsum {i | i < 256}
                            (\i. ((32 * val(x i) + 3329) DIV 6658) MOD 16 *
                                 2 EXP (4 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE mlkem_compress_d4_mc mlkem_compress_d4_tmc
    MLKEM_COMPRESS_D4_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_compress_d4" subroutine_signatures)
    MLKEM_COMPRESS_D4_NOIBT_SUBROUTINE_CORRECT
    MLKEM_COMPRESS_D4_EXEC;;

let MLKEM_COMPRESS_D4_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,128)) [(word pc,0x94); (a,512)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d4_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,128] [r,128])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_COMPRESS_D4_EXEC);;

let MLKEM_COMPRESS_D4_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,128)) [(word pc,0x98); (a,512)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d4_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,128] [r,128])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE mlkem_compress_d4_mc mlkem_compress_d4_tmc
    MLKEM_COMPRESS_D4_NOIBT_SUBROUTINE_SAFE));;
