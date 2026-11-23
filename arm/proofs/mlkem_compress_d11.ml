(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of polynomial coefficients to 11 bits, and packing them.      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_compress_d11.o";;
 ****)

let mlkem_compress_d11_mc = define_assert_from_elf
  "mlkem_compress_d11_mc" "arm/mlkem/mlkem_compress_d11.o"
[
  0xd503245f;       (* arm_BTI *)
  0x529bb402;       (* arm_MOV W2 (rvalue (word 56736)) *)
  0x72a9d7c2;       (* arm_MOVK W2 (word 20158) 16 *)
  0x4e040c5f;       (* arm_DUP_GEN Q31 X2 32 128 *)
  0x529a0202;       (* arm_MOV W2 (rvalue (word 53264)) *)
  0x4e020c59;       (* arm_DUP_GEN Q25 X2 16 128 *)
  0x6f00e41b;       (* arm_MOVI Q27 (word 0) *)
  0xd2800022;       (* arm_MOV X2 (rvalue (word 1)) *)
  0xf2a00102;       (* arm_MOVK X2 (word 8) 16 *)
  0xf2c00802;       (* arm_MOVK X2 (word 64) 32 *)
  0xf2e00042;       (* arm_MOVK X2 (word 2) 48 *)
  0xd2800203;       (* arm_MOV X3 (rvalue (word 16)) *)
  0xf2a01003;       (* arm_MOVK X3 (word 128) 16 *)
  0xf2c00083;       (* arm_MOVK X3 (word 4) 32 *)
  0xf2e00403;       (* arm_MOVK X3 (word 32) 48 *)
  0x9e67005e;       (* arm_FMOV_ItoF Q30 X2 0 *)
  0x4e181c7e;       (* arm_INS_GEN Q30 X3 64 64 *)
  0xd2802002;       (* arm_MOV X2 (rvalue (word 256)) *)
  0xf2a120a2;       (* arm_MOVK X2 (word 2309) 16 *)
  0xf2c1a142;       (* arm_MOVK X2 (word 3338) 32 *)
  0xf2e2a222;       (* arm_MOVK X2 (word 5393) 48 *)
  0xd28322c3;       (* arm_MOV X3 (rvalue (word 6422)) *)
  0xf2bfe3a3;       (* arm_MOVK X3 (word 65309) 16 *)
  0xf2dfffe3;       (* arm_MOVK X3 (word 65535) 32 *)
  0xf2ffffe3;       (* arm_MOVK X3 (word 65535) 48 *)
  0x9e67005c;       (* arm_FMOV_ItoF Q28 X2 0 *)
  0x4e181c7c;       (* arm_INS_GEN Q28 X3 64 64 *)
  0xd2809fe2;       (* arm_MOV X2 (rvalue (word 1279)) *)
  0xf2bfe102;       (* arm_MOVK X2 (word 65288) 16 *)
  0xf2c20182;       (* arm_MOVK X2 (word 4108) 32 *)
  0xf2ffe282;       (* arm_MOVK X2 (word 65300) 48 *)
  0xd2838303;       (* arm_MOV X3 (rvalue (word 7192)) *)
  0xf2bfffe3;       (* arm_MOVK X3 (word 65535) 16 *)
  0xf2dfffe3;       (* arm_MOVK X3 (word 65535) 32 *)
  0xf2ffffe3;       (* arm_MOVK X3 (word 65535) 48 *)
  0x9e67005d;       (* arm_FMOV_ItoF Q29 X2 0 *)
  0x4e181c7d;       (* arm_INS_GEN Q29 X3 64 64 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0xacc10420;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (iword (&32))) *)
  0xacc10c22;       (* arm_LDP Q2 Q3 X1 (Postimmediate_Offset (iword (&32))) *)
  0x4e403b30;       (* arm_ZIP1 Q16 Q25 Q0 16 128 *)
  0x4e407b31;       (* arm_ZIP2 Q17 Q25 Q0 16 128 *)
  0x4e413b32;       (* arm_ZIP1 Q18 Q25 Q1 16 128 *)
  0x4e417b33;       (* arm_ZIP2 Q19 Q25 Q1 16 128 *)
  0x4e423b34;       (* arm_ZIP1 Q20 Q25 Q2 16 128 *)
  0x4e427b35;       (* arm_ZIP2 Q21 Q25 Q2 16 128 *)
  0x4e433b36;       (* arm_ZIP1 Q22 Q25 Q3 16 128 *)
  0x4e437b37;       (* arm_ZIP2 Q23 Q25 Q3 16 128 *)
  0x4ebfb610;       (* arm_SQDMULH_VEC Q16 Q16 Q31 32 128 *)
  0x4ebfb631;       (* arm_SQDMULH_VEC Q17 Q17 Q31 32 128 *)
  0x4ebfb652;       (* arm_SQDMULH_VEC Q18 Q18 Q31 32 128 *)
  0x4ebfb673;       (* arm_SQDMULH_VEC Q19 Q19 Q31 32 128 *)
  0x4ebfb694;       (* arm_SQDMULH_VEC Q20 Q20 Q31 32 128 *)
  0x4ebfb6b5;       (* arm_SQDMULH_VEC Q21 Q21 Q31 32 128 *)
  0x4ebfb6d6;       (* arm_SQDMULH_VEC Q22 Q22 Q31 32 128 *)
  0x4ebfb6f7;       (* arm_SQDMULH_VEC Q23 Q23 Q31 32 128 *)
  0x4e515a00;       (* arm_UZP2 Q0 Q16 Q17 16 128 *)
  0x4e535a41;       (* arm_UZP2 Q1 Q18 Q19 16 128 *)
  0x4e555a82;       (* arm_UZP2 Q2 Q20 Q21 16 128 *)
  0x4e575ac3;       (* arm_UZP2 Q3 Q22 Q23 16 128 *)
  0x2e7ec010;       (* arm_UMULL_VEC Q16 Q0 Q30 16 *)
  0x6e7ec011;       (* arm_UMULL2_VEC Q17 Q0 Q30 16 *)
  0x2e7ec032;       (* arm_UMULL_VEC Q18 Q1 Q30 16 *)
  0x6e7ec033;       (* arm_UMULL2_VEC Q19 Q1 Q30 16 *)
  0x2e7ec054;       (* arm_UMULL_VEC Q20 Q2 Q30 16 *)
  0x6e7ec055;       (* arm_UMULL2_VEC Q21 Q2 Q30 16 *)
  0x2e7ec076;       (* arm_UMULL_VEC Q22 Q3 Q30 16 *)
  0x6e7ec077;       (* arm_UMULL2_VEC Q23 Q3 Q30 16 *)
  0x4e1c2204;       (* arm_TBL2 Q4 Q16 Q17 Q28 128 *)
  0x4e1d2210;       (* arm_TBL2 Q16 Q16 Q17 Q29 128 *)
  0x4e1c2245;       (* arm_TBL2 Q5 Q18 Q19 Q28 128 *)
  0x4e1d2252;       (* arm_TBL2 Q18 Q18 Q19 Q29 128 *)
  0x4e1c2286;       (* arm_TBL2 Q6 Q20 Q21 Q28 128 *)
  0x4e1d2294;       (* arm_TBL2 Q20 Q20 Q21 Q29 128 *)
  0x4e1c22c7;       (* arm_TBL2 Q7 Q22 Q23 Q28 128 *)
  0x4e1d22d6;       (* arm_TBL2 Q22 Q22 Q23 Q29 128 *)
  0x4eb01c84;       (* arm_ORR_VEC Q4 Q4 Q16 128 *)
  0x4eb21ca5;       (* arm_ORR_VEC Q5 Q5 Q18 128 *)
  0x4eb41cc6;       (* arm_ORR_VEC Q6 Q6 Q20 128 *)
  0x4eb61ce7;       (* arm_ORR_VEC Q7 Q7 Q22 128 *)
  0x6e052b71;       (* arm_EXT Q17 Q27 Q5 40 *)
  0x6e1b28a5;       (* arm_EXT Q5 Q5 Q27 40 *)
  0x6e065373;       (* arm_EXT Q19 Q27 Q6 80 *)
  0x6e1b50c6;       (* arm_EXT Q6 Q6 Q27 80 *)
  0x6e077b75;       (* arm_EXT Q21 Q27 Q7 120 *)
  0x4eb11c84;       (* arm_ORR_VEC Q4 Q4 Q17 128 *)
  0x4eb31ca5;       (* arm_ORR_VEC Q5 Q5 Q19 128 *)
  0x4eb51cc6;       (* arm_ORR_VEC Q6 Q6 Q21 128 *)
  0x3c810404;       (* arm_STR Q4 X0 (Postimmediate_Offset (word 16)) *)
  0x3c810405;       (* arm_STR Q5 X0 (Postimmediate_Offset (word 16)) *)
  0xfc008406;       (* arm_STR D6 X0 (Postimmediate_Offset (word 8)) *)
  0x4d9f8006;       (* arm_ST1 Q6 X0 (Postimmediate_Offset (word 4)) 32 2 *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fff921;       (* arm_BNE (word 2096932) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_compress_d11_tmc =
  define_trimmed "mlkem_compress_d11_tmc" mlkem_compress_d11_mc;;

let MLKEM_COMPRESS_D11_EXEC = ARM_MK_EXEC_RULE mlkem_compress_d11_tmc;;

(* ------------------------------------------------------------------------- *)
(* The rounding of each coefficient, as the code computes it (abbreviated,   *)
(* to keep the terms small in the simulation), checked for all the 3329      *)
(* possible values.                                                          *)
(* ------------------------------------------------------------------------- *)

let compress_d11_lane = new_definition
 `compress_d11_lane (x:int16) =
  word_subword
   (iword_saturate((&2 * ival(word_join x (word 53264:int16):int32) *
                    &1321131424) div &4294967296):int32)
   (16,16):int16`;;

let COMPRESS_D11_LANE = time prove
 (`!x:int16.
        val x < 3329
        ==> ((4096 * val x + 3329) DIV 6658) MOD 2048 =
            val(compress_d11_lane x) MOD 2048 /\
            val(compress_d11_lane x) < 2048`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[compress_d11_lane] THEN
  SUBST1_TAC(SYM(ISPEC `x:int16` WORD_VAL)) THEN
  UNDISCH_TAC `val(x:int16) < 3329` THEN
  SPEC_TAC(`val(x:int16)`,`n:num`) THEN
  REWRITE_TAC[iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_32] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

(* The result is less than 2^11, so its upper 5 bits can be dropped. *)

let COMPRESS_D11_LANE_SUBWORD = prove
 (`!x:int16.
        val x < 3329
        ==> compress_d11_lane x =
            word_zx(word_subword (compress_d11_lane x) (0,11):11 word)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP COMPRESS_D11_LANE) THEN
  SPEC_TAC(`compress_d11_lane x`,`y:int16`) THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_SUBWORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[DIV_1; MOD_LT; ARITH_RULE `y < 2048 ==> y < 65536`]);;

let BIT_OF_VAL_MOD2048 = GEN `y:int16`
  (CONV_RULE (ONCE_DEPTH_CONV NUM_EXP_CONV)
    (ISPECL [`y:int16`; `11`] BIT_OF_VAL_MOD));;

(* The lookups of the out-of-range index 255 give 0. *)

let SUBWORD_BEYOND_TAC =
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o CONV_RULE(RAND_CONV(DEPTH_CONV WORD_SUBWORD_BEYOND_CONV)) o
    check (can (term_match [] `read X (s:armstate):int128 = whatever`) o
           concl)));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The result is checked bit by bit.                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_COMPRESS_D11_CORRECT = prove
 (`!r a x pc.
        ALL (nonoverlapping (r,352)) [(word pc,0x178); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d11_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = word(pc + 0x174) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,352)) s =
                       nsum {i | i < 256}
                            (\i. ((4096 * val(x i) + 3329) DIV 6658) MOD 2048 *
                                 2 EXP (11 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,352)])`,
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

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_COMPRESS_D11_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[compress_d11_lane] THEN
                      SUBWORD_BEYOND_TAC) (1--485) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES_EQ_BITS THEN
  REWRITE_TAC[ARITH_RULE `8 * 352 = 11 * 256`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_FIELD_BOUND THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_LT_EQ; ARITH_EQ];
    ALL_TAC] THEN

  (*** Bit p of the result is bit p MOD 11 of coefficient p DIV 11 ***)

  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP p = 2 EXP (11 * p DIV 11 + p MOD 11)` SUBST1_TAC THENL
   [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ODD_MOD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_FIELD_BIT o
    lhand o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `p < 11 * 256` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `p DIV 11` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `p < 11 * 256` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1 o MATCH_MP COMPRESS_D11_LANE) THEN
  SIMP_TAC[BIT_OF_VAL_MOD2048; MOD_LT_EQ; ARITH_EQ] THEN

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
   CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
   check (can (term_match [] `read (memory :> bytes32 a) s = xxx`) o
          concl))) THEN
  UNDISCH_TAC `p < 11 * 256` THEN SPEC_TAC(`p:num`,`p:num`) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s485" THEN
  CONV_TAC(DEPTH_CONV WORD_MUL_POW2_CONV) THEN
  FIRST_ASSUM(fun th ->
    let hyp = check (can (term_match []
                `!i. i < 256 ==> val(x i:int16) < 3329`) o concl) th in
    GEN_REWRITE_TAC ONCE_DEPTH_CONV
     (map (fun i -> MATCH_MP COMPRESS_D11_LANE_SUBWORD
                     (MP (SPEC (mk_small_numeral i) hyp)
                         (EQT_ELIM(NUM_LT_CONV
                           (mk_binop `(<):num->num->bool`
                              (mk_small_numeral i) `256`)))))
          (0--255))) THEN
  CHUNKED_ATOMS_BITBLAST_TAC 8 [`compress_d11_lane y`]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_COMPRESS_D11_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a x pc returnaddress.
        ALL (nonoverlapping (r,352)) [(word pc,0x178); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d11_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,352)) s =
                       nsum {i | i < 256}
                            (\i. ((4096 * val(x i) + 3329) DIV 6658) MOD 2048 *
                                 2 EXP (11 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,352)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_COMPRESS_D11_EXEC
    MLKEM_COMPRESS_D11_CORRECT);;

let MLKEM_COMPRESS_D11_SUBROUTINE_CORRECT = prove
 (`!r a x pc returnaddress.
        ALL (nonoverlapping (r,352)) [(word pc,0x17c); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d11_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,352)) s =
                       nsum {i | i < 256}
                            (\i. ((4096 * val(x i) + 3329) DIV 6658) MOD 2048 *
                                 2 EXP (11 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,352)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_compress_d11_mc mlkem_compress_d11_tmc
    MLKEM_COMPRESS_D11_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_compress_d11" subroutine_signatures)
    MLKEM_COMPRESS_D11_NOIBT_SUBROUTINE_CORRECT
    MLKEM_COMPRESS_D11_EXEC;;

let MLKEM_COMPRESS_D11_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,352)) [(word pc,0x178); (a,512)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d11_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,352] [r,352])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_COMPRESS_D11_EXEC);;

let MLKEM_COMPRESS_D11_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,352)) [(word pc,0x17c); (a,512)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_compress_d11_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,352] [r,352])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_compress_d11_mc mlkem_compress_d11_tmc
    MLKEM_COMPRESS_D11_NOIBT_SUBROUTINE_SAFE));;
