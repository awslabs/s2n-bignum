(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling from the centered binomial distribution with eta = 3.            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_cbd3.o";;
 ****)

let mlkem_cbd3_mc = define_assert_from_elf
  "mlkem_cbd3_mc" "arm/mlkem/mlkem_cbd3.o"
[
  0xd503245f;       (* arm_BTI *)
  0xd2808062;       (* arm_MOV X2 (rvalue (word 1027)) *)
  0xf2a0a082;       (* arm_MOVK X2 (word 1284) 16 *)
  0xf2c0a082;       (* arm_MOVK X2 (word 1284) 32 *)
  0xf2e0c0a2;       (* arm_MOVK X2 (word 1541) 48 *)
  0x4e080c58;       (* arm_DUP_GEN Q24 X2 64 128 *)
  0x6f00e41f;       (* arm_MOVI Q31 (word 0) *)
  0x4f00e43e;       (* arm_MOVI Q30 (word 72340172838076673) *)
  0x4f00e47d;       (* arm_MOVI Q29 (word 217020518514230019) *)
  0x4f01e7fc;       (* arm_MOVI Q28 (word 4557430888798830399) *)
  0x6f07e7e7;       (* arm_MOVI Q7 (word 18446744073709551615) *)
  0x6e0743e7;       (* arm_EXT Q7 Q31 Q7 64 *)
  0x4e278718;       (* arm_ADD_VEC Q24 Q24 Q7 8 128 *)
  0x6e3e8719;       (* arm_SUB_VEC Q25 Q24 Q30 8 128 *)
  0x4eb91f3a;       (* arm_MOV_VEC Q26 Q25 128 *)
  0x6e3e873b;       (* arm_SUB_VEC Q27 Q25 Q30 8 128 *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x4cdf4020;       (* arm_LD3 [Q0; Q1; Q2] X1 (Postimmediate_Offset (word 48)) 128 8 *)
  0x4e3c1c03;       (* arm_AND_VEC Q3 Q0 Q28 128 *)
  0x6f0a0404;       (* arm_USHR_VEC Q4 Q0 6 8 128 *)
  0x6f0c0425;       (* arm_USHR_VEC Q5 Q1 4 8 128 *)
  0x6f0e0446;       (* arm_USHR_VEC Q6 Q2 2 8 128 *)
  0x6f0a5424;       (* arm_SLI_VEC Q4 Q1 2 128 8 *)
  0x6f0c5445;       (* arm_SLI_VEC Q5 Q2 4 128 8 *)
  0x4e3c1c84;       (* arm_AND_VEC Q4 Q4 Q28 128 *)
  0x4e3c1ca5;       (* arm_AND_VEC Q5 Q5 Q28 128 *)
  0x4e036303;       (* arm_TBL4 Q3 Q24 Q25 Q26 Q27 Q3 128 *)
  0x4e046304;       (* arm_TBL4 Q4 Q24 Q25 Q26 Q27 Q4 128 *)
  0x4e056305;       (* arm_TBL4 Q5 Q24 Q25 Q26 Q27 Q5 128 *)
  0x4e066306;       (* arm_TBL4 Q6 Q24 Q25 Q26 Q27 Q6 128 *)
  0x4e043860;       (* arm_ZIP1 Q0 Q3 Q4 8 128 *)
  0x4e0638a1;       (* arm_ZIP1 Q1 Q5 Q6 8 128 *)
  0x4e047862;       (* arm_ZIP2 Q2 Q3 Q4 8 128 *)
  0x4e0678a7;       (* arm_ZIP2 Q7 Q5 Q6 8 128 *)
  0x4e413810;       (* arm_ZIP1 Q16 Q0 Q1 16 128 *)
  0x4e417811;       (* arm_ZIP2 Q17 Q0 Q1 16 128 *)
  0x4e473852;       (* arm_ZIP1 Q18 Q2 Q7 16 128 *)
  0x4e477853;       (* arm_ZIP2 Q19 Q2 Q7 16 128 *)
  0x2e3d2200;       (* arm_USUBL Q0 Q16 Q29 8 *)
  0x6e3d2201;       (* arm_USUBL2 Q1 Q16 Q29 8 *)
  0x2e3d2222;       (* arm_USUBL Q2 Q17 Q29 8 *)
  0x6e3d2223;       (* arm_USUBL2 Q3 Q17 Q29 8 *)
  0x2e3d2244;       (* arm_USUBL Q4 Q18 Q29 8 *)
  0x6e3d2245;       (* arm_USUBL2 Q5 Q18 Q29 8 *)
  0x2e3d2266;       (* arm_USUBL Q6 Q19 Q29 8 *)
  0x6e3d2267;       (* arm_USUBL2 Q7 Q19 Q29 8 *)
  0xac810400;       (* arm_STP Q0 Q1 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac810c02;       (* arm_STP Q2 Q3 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac811404;       (* arm_STP Q4 Q5 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac811c06;       (* arm_STP Q6 Q7 X0 (Postimmediate_Offset (iword (&32))) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffbc1;       (* arm_BNE (word 2097016) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_cbd3_tmc =
  define_trimmed "mlkem_cbd3_tmc" mlkem_cbd3_mc;;

let MLKEM_CBD3_EXEC = ARM_MK_EXEC_RULE mlkem_cbd3_tmc;;

(* ------------------------------------------------------------------------- *)
(* The coefficient of each 6-bit field as the code computes it, by a lookup  *)
(* of the field in the table in Q24-Q27 and a subtraction of 3 (abbreviated, *)
(* to keep the terms small in the simulation), checked for all 64 values.    *)
(* ------------------------------------------------------------------------- *)

let cbd3_table = new_definition
 `cbd3_table:512 word =
  word_join
   (word_join (word 0x03020201020101000403030203020201:int128)
              (word 0x04030302030202010504040304030302:int128):256 word)
   (word_join (word 0x04030302030202010504040304030302:int128)
              (word 0x05040403040303020605050405040403:int128):256 word)`;;

let CBD3_TABLE =
  (REWRITE_CONV[cbd3_table] THENC DEPTH_CONV WORD_RED_CONV) `cbd3_table`;;

let cbd3_lane = new_definition
 `cbd3_lane (x:byte) =
  word_sub (word_zx (word_subword cbd3_table (8 * val x,8):byte))
           (word 3):int16`;;

let CBD3_LANE = prove
 (`!n p. iword(&((n DIV 2 EXP p) MOD 2 + (n DIV 2 EXP (p + 1)) MOD 2 +
                 (n DIV 2 EXP (p + 2)) MOD 2) -
               &((n DIV 2 EXP (p + 3)) MOD 2 + (n DIV 2 EXP (p + 4)) MOD 2 +
                 (n DIV 2 EXP (p + 5)) MOD 2)):int16 =
         cbd3_lane(word((n DIV 2 EXP p) MOD 2 EXP 6))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!t. t < 6
        ==> (n DIV 2 EXP (p + t)) MOD 2 =
            (((n DIV 2 EXP p) MOD 2 EXP 6) DIV 2 EXP t) MOD 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
    CONV_TAC SYM_CONV THEN
    MP_TAC(SPECL [`n DIV 2 EXP p`; `6`; `t:num`; `1`] DIV_MOD_EXP_LOW) THEN
    REWRITE_TAC[EXP_1] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(MP_TAC o SPEC(mk_small_numeral t)))
   (0--5) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; DIV_1] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ARITH_RULE `(n DIV 2 EXP p) MOD 64 < 64`) THEN
  SPEC_TAC(`(n DIV 2 EXP p) MOD 64`,`x:num`) THEN
  REWRITE_TAC[cbd3_lane; CBD3_TABLE] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CBD3_CORRECT = prove
 (`!r a n pc.
        ALL (nonoverlapping (r,512)) [(word pc,0xd0); (a,192)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_cbd3_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = n)
             (\s. read PC s = word(pc + 0xcc) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 5)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The words of the input, as loaded, are subwords of word n ***)

  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `192`; `n:num`; mk_small_numeral k;
                    `s0:armstate`] READ_MEMORY_BYTES128_OF_NUM in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th)
    (map (fun k -> 16 * k) (0--11)))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:1536`,`:N`] QWORD128_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:1536)`; ARITH] THEN STRIP_TAC THEN

  (*** Simulate the whole thing, unrolling the loop ***)

  MAP_EVERY (fun n ->
    ARM_STEPS_TAC MLKEM_CBD3_EXEC [n] THEN
    if mem n [17; 52; 87; 122] then
      RULE_ASSUM_TAC(fun th ->
        if can (term_match [] `read (Q:(armstate,int128)component) s =
                               word_subdeinterleave 3 8 x j`) (concl th)
        then CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_SUBDEINTERLEAVE_3_8] THENC
                                 SIMD_SIMPLIFY_CONV[])) th
        else th)
    else SIMD_SIMPLIFY_TAC[CBD3_TABLE; cbd3_lane]) (1--156) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient is the lane function of a 6-bit field of word n ***)

  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[CBD3_LANE] THEN
  MP_TAC(ISPECL [`n:num`; `6 * i`; `6`]
    (INST_TYPE [`:1536`,`:N`; `:8`,`:M`] WORD_SUBWORD_WORD)) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1536)`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  UNDISCH_TAC `i < 256` THEN SPEC_TAC(`i:num`,`i:num`) THEN

  (*** Split the stored vectors, and check the argument of each lane ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read (memory :> bytes128 a) s = xxx`) o
          concl))) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s156" THEN
  LANE_ARGS_BITBLAST_TAC 8 [`word (n:num):1536 word`]);;


(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CBD3_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0xd0); (a,192)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_cbd3_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 5)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_CBD3_EXEC
    MLKEM_CBD3_CORRECT);;

let MLKEM_CBD3_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0xd4); (a,192)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_cbd3_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 5)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_cbd3_mc mlkem_cbd3_tmc
    MLKEM_CBD3_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_cbd3" subroutine_signatures)
    MLKEM_CBD3_NOIBT_SUBROUTINE_CORRECT
    MLKEM_CBD3_EXEC;;

let MLKEM_CBD3_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0xd0); (a,192)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_cbd3_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,192; r,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_CBD3_EXEC);;

let MLKEM_CBD3_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0xd4); (a,192)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_cbd3_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,192; r,512] [r,512])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_cbd3_mc mlkem_cbd3_tmc
    MLKEM_CBD3_NOIBT_SUBROUTINE_SAFE));;
