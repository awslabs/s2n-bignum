(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling from the centered binomial distribution with eta = 2.            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_cbd2.o";;
 ****)

let mlkem_cbd2_mc = define_assert_from_elf
  "mlkem_cbd2_mc" "arm/mlkem/mlkem_cbd2.o"
[
  0xd503245f;       (* arm_BTI *)
  0x4f00e5fd;       (* arm_MOVI Q29 (word 1085102592571150095) *)
  0x4f00e47f;       (* arm_MOVI Q31 (word 217020518514230019) *)
  0xd2808062;       (* arm_MOV X2 (rvalue (word 1027)) *)
  0xf2a0a082;       (* arm_MOVK X2 (word 1284) 16 *)
  0xf2c06042;       (* arm_MOVK X2 (word 770) 32 *)
  0xf2e08062;       (* arm_MOVK X2 (word 1027) 48 *)
  0xd2806043;       (* arm_MOV X3 (rvalue (word 770)) *)
  0xf2a08063;       (* arm_MOVK X3 (word 1027) 16 *)
  0xf2c04023;       (* arm_MOVK X3 (word 513) 32 *)
  0xf2e06043;       (* arm_MOVK X3 (word 770) 48 *)
  0x9e67005e;       (* arm_FMOV_ItoF Q30 X2 0 *)
  0x4e181c7e;       (* arm_INS_GEN Q30 X3 64 64 *)
  0xd2800042;       (* arm_MOV X2 (rvalue (word 2)) *)
  0xacc10420;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc10c22;       (* arm_LDP Q2 Q3 X1 (Postimmediate_Offset (iword (&32))) *)
  0x4e3d1c04;       (* arm_AND_VEC Q4 Q0 Q29 128 *)
  0x4e3d1c25;       (* arm_AND_VEC Q5 Q1 Q29 128 *)
  0x4e3d1c46;       (* arm_AND_VEC Q6 Q2 Q29 128 *)
  0x4e3d1c67;       (* arm_AND_VEC Q7 Q3 Q29 128 *)
  0x6f0c0400;       (* arm_USHR_VEC Q0 Q0 4 8 128 *)
  0x6f0c0421;       (* arm_USHR_VEC Q1 Q1 4 8 128 *)
  0x6f0c0442;       (* arm_USHR_VEC Q2 Q2 4 8 128 *)
  0x6f0c0463;       (* arm_USHR_VEC Q3 Q3 4 8 128 *)
  0x4e003890;       (* arm_ZIP1 Q16 Q4 Q0 8 128 *)
  0x4e007891;       (* arm_ZIP2 Q17 Q4 Q0 8 128 *)
  0x4e0138b2;       (* arm_ZIP1 Q18 Q5 Q1 8 128 *)
  0x4e0178b3;       (* arm_ZIP2 Q19 Q5 Q1 8 128 *)
  0x4e0238d4;       (* arm_ZIP1 Q20 Q6 Q2 8 128 *)
  0x4e0278d5;       (* arm_ZIP2 Q21 Q6 Q2 8 128 *)
  0x4e0338f6;       (* arm_ZIP1 Q22 Q7 Q3 8 128 *)
  0x4e0378f7;       (* arm_ZIP2 Q23 Q7 Q3 8 128 *)
  0x4e1003d0;       (* arm_TBL Q16 [Q30] Q16 128 *)
  0x4e1103d1;       (* arm_TBL Q17 [Q30] Q17 128 *)
  0x4e1203d2;       (* arm_TBL Q18 [Q30] Q18 128 *)
  0x4e1303d3;       (* arm_TBL Q19 [Q30] Q19 128 *)
  0x4e1403d4;       (* arm_TBL Q20 [Q30] Q20 128 *)
  0x4e1503d5;       (* arm_TBL Q21 [Q30] Q21 128 *)
  0x4e1603d6;       (* arm_TBL Q22 [Q30] Q22 128 *)
  0x4e1703d7;       (* arm_TBL Q23 [Q30] Q23 128 *)
  0x2e3f2218;       (* arm_USUBL Q24 Q16 Q31 8 *)
  0x6e3f2219;       (* arm_USUBL2 Q25 Q16 Q31 8 *)
  0x2e3f223a;       (* arm_USUBL Q26 Q17 Q31 8 *)
  0x6e3f223b;       (* arm_USUBL2 Q27 Q17 Q31 8 *)
  0xac816418;       (* arm_STP Q24 Q25 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac816c1a;       (* arm_STP Q26 Q27 X0 (Postimmediate_Offset (iword (&32))) *)
  0x2e3f2240;       (* arm_USUBL Q0 Q18 Q31 8 *)
  0x6e3f2241;       (* arm_USUBL2 Q1 Q18 Q31 8 *)
  0x2e3f2262;       (* arm_USUBL Q2 Q19 Q31 8 *)
  0x6e3f2263;       (* arm_USUBL2 Q3 Q19 Q31 8 *)
  0xac810400;       (* arm_STP Q0 Q1 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac810c02;       (* arm_STP Q2 Q3 X0 (Postimmediate_Offset (iword (&32))) *)
  0x2e3f2284;       (* arm_USUBL Q4 Q20 Q31 8 *)
  0x6e3f2285;       (* arm_USUBL2 Q5 Q20 Q31 8 *)
  0x2e3f22a6;       (* arm_USUBL Q6 Q21 Q31 8 *)
  0x6e3f22a7;       (* arm_USUBL2 Q7 Q21 Q31 8 *)
  0xac811404;       (* arm_STP Q4 Q5 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac811c06;       (* arm_STP Q6 Q7 X0 (Postimmediate_Offset (iword (&32))) *)
  0x2e3f22d8;       (* arm_USUBL Q24 Q22 Q31 8 *)
  0x6e3f22d9;       (* arm_USUBL2 Q25 Q22 Q31 8 *)
  0x2e3f22fa;       (* arm_USUBL Q26 Q23 Q31 8 *)
  0x6e3f22fb;       (* arm_USUBL2 Q27 Q23 Q31 8 *)
  0xac816418;       (* arm_STP Q24 Q25 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac816c1a;       (* arm_STP Q26 Q27 X0 (Postimmediate_Offset (iword (&32))) *)
  0xf1000442;       (* arm_SUBS X2 X2 (rvalue (word 1)) *)
  0x54fff9a1;       (* arm_BNE (word 2096948) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_cbd2_tmc =
  define_trimmed "mlkem_cbd2_tmc" mlkem_cbd2_mc;;

let MLKEM_CBD2_EXEC = ARM_MK_EXEC_RULE mlkem_cbd2_tmc;;

(* ------------------------------------------------------------------------- *)
(* The coefficient of each nibble as the code computes it, by a lookup of    *)
(* the nibble in the table in Q30 and a subtraction of 3 (abbreviated, to    *)
(* keep the terms small in the simulation), checked for all 16 values.       *)
(* ------------------------------------------------------------------------- *)

let cbd2_lane = new_definition
 `cbd2_lane (x:byte) =
  word_sub (word_zx (word_subword
    (word 3998109226360768112599906688614794243:int128) (8 * val x,8):byte))
   (word 3):int16`;;

let CBD2_LANE = prove
 (`!n p. iword(&((n DIV 2 EXP p) MOD 2 + (n DIV 2 EXP (p + 1)) MOD 2) -
               &((n DIV 2 EXP (p + 2)) MOD 2 +
                 (n DIV 2 EXP (p + 3)) MOD 2)):int16 =
         cbd2_lane(word((n DIV 2 EXP p) MOD 2 EXP 4))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!t. t < 4
        ==> (n DIV 2 EXP (p + t)) MOD 2 =
            (((n DIV 2 EXP p) MOD 2 EXP 4) DIV 2 EXP t) MOD 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
    CONV_TAC SYM_CONV THEN
    MP_TAC(SPECL [`n DIV 2 EXP p`; `4`; `t:num`; `1`] DIV_MOD_EXP_LOW) THEN
    REWRITE_TAC[EXP_1] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN FIRST_ASSUM(MP_TAC o SPEC `1`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `3`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; DIV_1] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ARITH_RULE `(n DIV 2 EXP p) MOD 16 < 16`) THEN
  SPEC_TAC(`(n DIV 2 EXP p) MOD 16`,`x:num`) THEN
  REWRITE_TAC[cbd2_lane] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CBD2_CORRECT = prove
 (`!r a n pc.
        ALL (nonoverlapping (r,512)) [(word pc,0x108); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_cbd2_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read PC s = word(pc + 0x104) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The words of the input, as loaded, are subwords of word n ***)

  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `128`; `n:num`; mk_small_numeral k;
                    `s0:armstate`] READ_MEMORY_BYTES128_OF_NUM in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th)
    [0; 16; 32; 48; 64; 80; 96; 112])) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:1024`,`:N`] QWORD128_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:1024)`; ARITH] THEN STRIP_TAC THEN

  (*** Simulate the whole thing, unrolling the loop ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_CBD2_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[cbd2_lane]) (1--117) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient is the lane function of a 4-bit field of word n ***)

  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[CBD2_LANE] THEN
  MP_TAC(ISPECL [`n:num`; `4 * i`; `4`]
    (INST_TYPE [`:1024`,`:N`; `:8`,`:M`] WORD_SUBWORD_WORD)) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1024)`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  UNDISCH_TAC `i < 256` THEN SPEC_TAC(`i:num`,`i:num`) THEN

  (*** Split the stored vectors, and check the argument of each lane ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read (memory :> bytes128 a) s = xxx`) o
          concl))) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s117" THEN
  LANE_ARGS_BITBLAST_TAC 8 [`word (n:num):1024 word`]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_CBD2_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x108); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_cbd2_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_CBD2_EXEC
    MLKEM_CBD2_CORRECT);;

let MLKEM_CBD2_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x10c); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_cbd2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_cbd2_mc mlkem_cbd2_tmc
    MLKEM_CBD2_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_cbd2" subroutine_signatures)
    MLKEM_CBD2_NOIBT_SUBROUTINE_CORRECT
    MLKEM_CBD2_EXEC;;

let MLKEM_CBD2_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0x108); (a,128)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_cbd2_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,128; r,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_CBD2_EXEC);;

let MLKEM_CBD2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0x10c); (a,128)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_cbd2_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,128; r,512] [r,512])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_cbd2_mc mlkem_cbd2_tmc
    MLKEM_CBD2_NOIBT_SUBROUTINE_SAFE));;
