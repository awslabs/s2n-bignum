(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a polynomial to a 32-byte message.                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_tomsg.o";;
 ****)

let mlkem_tomsg_mc = define_assert_from_elf
  "mlkem_tomsg_mc" "arm/mlkem/mlkem_tomsg.o"
[
  0xd503245f;       (* arm_BTI *)
  0x4f00a47d;       (* arm_MOVI Q29 (word 216176080698999552) *)
  0x4f02943d;       (* arm_ORR_VEC Q29 Q29 (rvalue (word 337504445713908600368037681896161345)) 128 *)
  0x4f00a4df;       (* arm_MOVI Q31 (word 432352161397999104) *)
  0x4f04941f;       (* arm_ORR_VEC Q31 Q31 (rvalue (word 664624139252004628417058819733979264)) 128 *)
  0xd2800022;       (* arm_MOV X2 (rvalue (word 1)) *)
  0xf2a00042;       (* arm_MOVK X2 (word 2) 16 *)
  0xf2c00082;       (* arm_MOVK X2 (word 4) 32 *)
  0xf2e00102;       (* arm_MOVK X2 (word 8) 48 *)
  0xd2800203;       (* arm_MOV X3 (rvalue (word 16)) *)
  0xf2a00403;       (* arm_MOVK X3 (word 32) 16 *)
  0xf2c00803;       (* arm_MOVK X3 (word 64) 32 *)
  0xf2e01003;       (* arm_MOVK X3 (word 128) 48 *)
  0x9e67005e;       (* arm_FMOV_ItoF Q30 X2 0 *)
  0x4e181c7e;       (* arm_INS_GEN Q30 X3 64 64 *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0xacc10420;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc10c22;       (* arm_LDP Q2 Q3 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc11424;       (* arm_LDP Q4 Q5 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc11c26;       (* arm_LDP Q6 Q7 X1 (Postimmediate_Offset (iword (&32))) *)
  0x6e7d8400;       (* arm_SUB_VEC Q0 Q0 Q29 16 128 *)
  0x6e7d8421;       (* arm_SUB_VEC Q1 Q1 Q29 16 128 *)
  0x6e7d8442;       (* arm_SUB_VEC Q2 Q2 Q29 16 128 *)
  0x6e7d8463;       (* arm_SUB_VEC Q3 Q3 Q29 16 128 *)
  0x6e7d8484;       (* arm_SUB_VEC Q4 Q4 Q29 16 128 *)
  0x6e7d84a5;       (* arm_SUB_VEC Q5 Q5 Q29 16 128 *)
  0x6e7d84c6;       (* arm_SUB_VEC Q6 Q6 Q29 16 128 *)
  0x6e7d84e7;       (* arm_SUB_VEC Q7 Q7 Q29 16 128 *)
  0x6e6037e0;       (* arm_CMHI_VEC Q0 Q31 Q0 16 128 *)
  0x6e6137e1;       (* arm_CMHI_VEC Q1 Q31 Q1 16 128 *)
  0x6e6237e2;       (* arm_CMHI_VEC Q2 Q31 Q2 16 128 *)
  0x6e6337e3;       (* arm_CMHI_VEC Q3 Q31 Q3 16 128 *)
  0x6e6437e4;       (* arm_CMHI_VEC Q4 Q31 Q4 16 128 *)
  0x6e6537e5;       (* arm_CMHI_VEC Q5 Q31 Q5 16 128 *)
  0x6e6637e6;       (* arm_CMHI_VEC Q6 Q31 Q6 16 128 *)
  0x6e6737e7;       (* arm_CMHI_VEC Q7 Q31 Q7 16 128 *)
  0x4e3e1c00;       (* arm_AND_VEC Q0 Q0 Q30 128 *)
  0x4e3e1c21;       (* arm_AND_VEC Q1 Q1 Q30 128 *)
  0x4e3e1c42;       (* arm_AND_VEC Q2 Q2 Q30 128 *)
  0x4e3e1c63;       (* arm_AND_VEC Q3 Q3 Q30 128 *)
  0x4e3e1c84;       (* arm_AND_VEC Q4 Q4 Q30 128 *)
  0x4e3e1ca5;       (* arm_AND_VEC Q5 Q5 Q30 128 *)
  0x4e3e1cc6;       (* arm_AND_VEC Q6 Q6 Q30 128 *)
  0x4e3e1ce7;       (* arm_AND_VEC Q7 Q7 Q30 128 *)
  0x4e61bc00;       (* arm_ADDP_VEC Q0 Q0 Q1 16 128 *)
  0x4e63bc42;       (* arm_ADDP_VEC Q2 Q2 Q3 16 128 *)
  0x4e65bc84;       (* arm_ADDP_VEC Q4 Q4 Q5 16 128 *)
  0x4e67bcc6;       (* arm_ADDP_VEC Q6 Q6 Q7 16 128 *)
  0x4e62bc00;       (* arm_ADDP_VEC Q0 Q0 Q2 16 128 *)
  0x4e66bc84;       (* arm_ADDP_VEC Q4 Q4 Q6 16 128 *)
  0x4e64bc00;       (* arm_ADDP_VEC Q0 Q0 Q4 16 128 *)
  0x0e212800;       (* arm_XTN Q0 Q0 8 *)
  0xfc008400;       (* arm_STR D0 X0 (Postimmediate_Offset (word 8)) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffb41;       (* arm_BNE (word 2097000) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_tomsg_tmc = define_trimmed "mlkem_tomsg_tmc" mlkem_tomsg_mc;;

let MLKEM_TOMSG_EXEC = ARM_MK_EXEC_RULE mlkem_tomsg_tmc;;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to one bit, as the code computes it.     *)
(* ------------------------------------------------------------------------- *)

let TOMSG_COMPRESS = prove
 (`!x:int16.
        val x < 3329
        ==> ((4 * val x + 3329) DIV 6658) MOD 2 =
            bitval(word_ugt (word 1664) (word_sub x (word 833)))`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_UGT; VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(x:int16)`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `n < 833` THENL
   [SUBGOAL_THEN `(4 * n + 3329) DIV 6658 = 0` SUBST1_TAC THENL
     [REWRITE_TAC[DIV_EQ_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `n < 833 ==> ~(833 <= n)`];
    ASM_SIMP_TAC[ARITH_RULE `~(n < 833) ==> 833 <= n`] THEN
    ASM_CASES_TAC `n < 2497` THENL
     [SUBGOAL_THEN `(4 * n + 3329) DIV 6658 = 1` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `4 * n - 3329` THEN
        REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;
        ALL_TAC];
      SUBGOAL_THEN `(4 * n + 3329) DIV 6658 = 2` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `4 * n - 9987` THEN
        ASM_ARITH_TAC;
        ALL_TAC]]] THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The message is checked bit by bit.                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_TOMSG_CORRECT = prove
 (`!r a x pc.
        ALL (nonoverlapping (r,32)) [(word pc,0xdc); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_tomsg_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = word(pc + 0xd8) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,32)) s =
                       nsum {i | i < 256}
                            (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 *
                                 2 EXP i)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,32)])`,
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
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_TOMSG_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (1--171) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES_EQ_BITS THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * 32 = 256`] THEN
    MATCH_MP_TAC(REWRITE_RULE[MULT_CLAUSES] (SPEC `1` NSUM_FIELD_BOUND)) THEN
    REWRITE_TAC[EXP_1; MOD_LT_EQ; ARITH_EQ];
    ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  UNDISCH_TAC `p < 8 * 32` THEN REWRITE_TAC[ARITH_RULE `8 * 32 = 256`] THEN
  DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_BIT o rand o snd) THEN
  ASM_REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP TOMSG_COMPRESS) THEN
  REWRITE_TAC[BITVAL_EQ_1] THEN

  (*** Split the stored words into bytes and look at each bit ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read (memory :> bytes64 a) s = xxx`) o
          concl))) THEN
  UNDISCH_TAC `p < 256` THEN SPEC_TAC(`p:num`,`p:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s171" THEN
  REWRITE_TAC[WORD_NEG_BITVAL] THEN CHUNKED_CMP_BITBLAST_TAC 8);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_TOMSG_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a x pc returnaddress.
        ALL (nonoverlapping (r,32)) [(word pc,0xdc); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_tomsg_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,32)) s =
                       nsum {i | i < 256}
                            (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 *
                                 2 EXP i)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,32)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_TOMSG_EXEC MLKEM_TOMSG_CORRECT);;

let MLKEM_TOMSG_SUBROUTINE_CORRECT = prove
 (`!r a x pc returnaddress.
        ALL (nonoverlapping (r,32)) [(word pc,0xe0); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_tomsg_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,32)) s =
                       nsum {i | i < 256}
                            (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 *
                                 2 EXP i)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,32)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE mlkem_tomsg_mc mlkem_tomsg_tmc
    MLKEM_TOMSG_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_tomsg" subroutine_signatures)
    MLKEM_TOMSG_NOIBT_SUBROUTINE_CORRECT
    MLKEM_TOMSG_EXEC;;

let MLKEM_TOMSG_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,32)) [(word pc,0xdc); (a,512)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_tomsg_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,32] [r,32])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_TOMSG_EXEC);;

let MLKEM_TOMSG_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,32)) [(word pc,0xe0); (a,512)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_tomsg_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,32] [r,32])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE mlkem_tomsg_mc mlkem_tomsg_tmc
    MLKEM_TOMSG_NOIBT_SUBROUTINE_SAFE));;
