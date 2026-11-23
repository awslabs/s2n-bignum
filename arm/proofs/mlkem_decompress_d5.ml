(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of 5-bit fields and decompression of them to coefficients.      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_decompress_d5.o";;
 ****)

let mlkem_decompress_d5_mc = define_assert_from_elf
  "mlkem_decompress_d5_mc" "arm/mlkem/mlkem_decompress_d5.o"
[
  0xd503245f;       (* arm_BTI *)
  0x5281a022;       (* arm_MOV W2 (rvalue (word 3329)) *)
  0x4e020c59;       (* arm_DUP_GEN Q25 X2 16 128 *)
  0x6f00e41a;       (* arm_MOVI Q26 (word 0) *)
  0x4f03a79b;       (* arm_MOVI Q27 (word 8935278002225314816) *)
  0xd2802002;       (* arm_MOV X2 (rvalue (word 256)) *)
  0xf2a02002;       (* arm_MOVK X2 (word 256) 16 *)
  0xf2c04022;       (* arm_MOVK X2 (word 513) 32 *)
  0xf2e04022;       (* arm_MOVK X2 (word 513) 48 *)
  0xd2806043;       (* arm_MOV X3 (rvalue (word 770)) *)
  0xf2a08063;       (* arm_MOVK X3 (word 1027) 16 *)
  0xf2c08063;       (* arm_MOVK X3 (word 1027) 32 *)
  0xf2e0a083;       (* arm_MOVK X3 (word 1284) 48 *)
  0x9e67005c;       (* arm_FMOV_ItoF Q28 X2 0 *)
  0x4e181c7c;       (* arm_INS_GEN Q28 X3 64 64 *)
  0xd280c0a2;       (* arm_MOV X2 (rvalue (word 1541)) *)
  0xf2a0c0a2;       (* arm_MOVK X2 (word 1541) 16 *)
  0xf2c0e0c2;       (* arm_MOVK X2 (word 1798) 32 *)
  0xf2e0e0c2;       (* arm_MOVK X2 (word 1798) 48 *)
  0xd28100e3;       (* arm_MOV X3 (rvalue (word 2055)) *)
  0xf2a12103;       (* arm_MOVK X3 (word 2312) 16 *)
  0xf2c12103;       (* arm_MOVK X3 (word 2312) 32 *)
  0xf2e14123;       (* arm_MOVK X3 (word 2569) 48 *)
  0x9e67005d;       (* arm_FMOV_ItoF Q29 X2 0 *)
  0x4e181c7d;       (* arm_INS_GEN Q29 X3 64 64 *)
  0xd2816142;       (* arm_MOV X2 (rvalue (word 2826)) *)
  0xf2a16142;       (* arm_MOVK X2 (word 2826) 16 *)
  0xf2c18162;       (* arm_MOVK X2 (word 3083) 32 *)
  0xf2e18162;       (* arm_MOVK X2 (word 3083) 48 *)
  0xd281a183;       (* arm_MOV X3 (rvalue (word 3340)) *)
  0xf2a1c1a3;       (* arm_MOVK X3 (word 3597) 16 *)
  0xf2c1c1a3;       (* arm_MOVK X3 (word 3597) 32 *)
  0xf2e1e1c3;       (* arm_MOVK X3 (word 3854) 48 *)
  0x9e67005e;       (* arm_FMOV_ItoF Q30 X2 0 *)
  0x4e181c7e;       (* arm_INS_GEN Q30 X3 64 64 *)
  0xd2800142;       (* arm_MOV X2 (rvalue (word 10)) *)
  0xf2a000a2;       (* arm_MOVK X2 (word 5) 16 *)
  0xf2c00102;       (* arm_MOVK X2 (word 8) 32 *)
  0xf2e00062;       (* arm_MOVK X2 (word 3) 48 *)
  0xd28000c3;       (* arm_MOV X3 (rvalue (word 6)) *)
  0xf2a00123;       (* arm_MOVK X3 (word 9) 16 *)
  0xf2c00083;       (* arm_MOVK X3 (word 4) 32 *)
  0xf2e000e3;       (* arm_MOVK X3 (word 7) 48 *)
  0x9e67005f;       (* arm_FMOV_ItoF Q31 X2 0 *)
  0x4e181c7f;       (* arm_INS_GEN Q31 X3 64 64 *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0xacc10420;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (iword (&32))) *)
  0xfc408422;       (* arm_LDR D2 X1 (Postimmediate_Offset (word 8)) *)
  0x6e017803;       (* arm_EXT Q3 Q0 Q1 120 *)
  0x6e027024;       (* arm_EXT Q4 Q1 Q2 112 *)
  0x4e1c0010;       (* arm_TBL Q16 [Q0] Q28 128 *)
  0x4e1d0011;       (* arm_TBL Q17 [Q0] Q29 128 *)
  0x4e1e0012;       (* arm_TBL Q18 [Q0] Q30 128 *)
  0x4e1c0073;       (* arm_TBL Q19 [Q3] Q28 128 *)
  0x4e1d0074;       (* arm_TBL Q20 [Q3] Q29 128 *)
  0x4e1e0075;       (* arm_TBL Q21 [Q3] Q30 128 *)
  0x4e1c0096;       (* arm_TBL Q22 [Q4] Q28 128 *)
  0x4e1d0097;       (* arm_TBL Q23 [Q4] Q29 128 *)
  0x6e7f4610;       (* arm_USHL_VEC Q16 Q16 Q31 16 128 *)
  0x6e7f4631;       (* arm_USHL_VEC Q17 Q17 Q31 16 128 *)
  0x6e7f4652;       (* arm_USHL_VEC Q18 Q18 Q31 16 128 *)
  0x6e7f4673;       (* arm_USHL_VEC Q19 Q19 Q31 16 128 *)
  0x6e7f4694;       (* arm_USHL_VEC Q20 Q20 Q31 16 128 *)
  0x6e7f46b5;       (* arm_USHL_VEC Q21 Q21 Q31 16 128 *)
  0x6e7f46d6;       (* arm_USHL_VEC Q22 Q22 Q31 16 128 *)
  0x6e7f46f7;       (* arm_USHL_VEC Q23 Q23 Q31 16 128 *)
  0x4e3b1e10;       (* arm_AND_VEC Q16 Q16 Q27 128 *)
  0x4e3b1e31;       (* arm_AND_VEC Q17 Q17 Q27 128 *)
  0x4e3b1e52;       (* arm_AND_VEC Q18 Q18 Q27 128 *)
  0x4e3b1e73;       (* arm_AND_VEC Q19 Q19 Q27 128 *)
  0x4e3b1e94;       (* arm_AND_VEC Q20 Q20 Q27 128 *)
  0x4e3b1eb5;       (* arm_AND_VEC Q21 Q21 Q27 128 *)
  0x4e3b1ed6;       (* arm_AND_VEC Q22 Q22 Q27 128 *)
  0x4e3b1ef7;       (* arm_AND_VEC Q23 Q23 Q27 128 *)
  0x6e79b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 16 128 *)
  0x6e79b631;       (* arm_SQRDMULH_VEC Q17 Q17 Q25 16 128 *)
  0x6e79b652;       (* arm_SQRDMULH_VEC Q18 Q18 Q25 16 128 *)
  0x6e79b673;       (* arm_SQRDMULH_VEC Q19 Q19 Q25 16 128 *)
  0x6e79b694;       (* arm_SQRDMULH_VEC Q20 Q20 Q25 16 128 *)
  0x6e79b6b5;       (* arm_SQRDMULH_VEC Q21 Q21 Q25 16 128 *)
  0x6e79b6d6;       (* arm_SQRDMULH_VEC Q22 Q22 Q25 16 128 *)
  0x6e79b6f7;       (* arm_SQRDMULH_VEC Q23 Q23 Q25 16 128 *)
  0xac814410;       (* arm_STP Q16 Q17 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac814c12;       (* arm_STP Q18 Q19 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac815414;       (* arm_STP Q20 Q21 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac815c16;       (* arm_STP Q22 Q23 X0 (Postimmediate_Offset (iword (&32))) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffae1;       (* arm_BNE (word 2096988) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_decompress_d5_tmc =
  define_trimmed "mlkem_decompress_d5_tmc" mlkem_decompress_d5_mc;;

let MLKEM_DECOMPRESS_D5_EXEC = ARM_MK_EXEC_RULE mlkem_decompress_d5_tmc;;

(* ------------------------------------------------------------------------- *)
(* The decompression of each 5-bit field u as the code computes it, from     *)
(* the lane u * 2^10 (abbreviated, to keep the terms small in the            *)
(* simulation), checked for all 32 values.                                   *)
(* ------------------------------------------------------------------------- *)

let decompress_d5_lane = new_definition
 `decompress_d5_lane (v:int16) =
  iword_saturate((&2 * ival v * &3329 + &32768) div &65536):int16`;;

let DECOMPRESS_D5_LANE = time prove
 (`!f:(5)word.
        decompress_d5_lane (word_shl (word_zx f:int16) 10) =
        word((3329 * val f + 16) DIV 32)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM(ISPEC `f:(5)word` WORD_VAL)] THEN
  MP_TAC(ISPEC `f:(5)word` VAL_BOUND) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:(5)word)`,`k:num`) THEN
  REWRITE_TAC[decompress_d5_lane; iword_saturate; word_INT_MIN;
              word_INT_MAX; DIMINDEX_16] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_DECOMPRESS_D5_CORRECT = prove
 (`!r a n pc.
        ALL (nonoverlapping (r,512)) [(word pc,0x160); (a,160)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d5_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,160)) s = n)
             (\s. read PC s = word(pc + 0x15c) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (5 * i)) MOD 2 EXP 5 +
                                16) DIV 32))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The words of the input, as loaded, are subwords of word n ***)

  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `160`; `n:num`; mk_small_numeral k;
                    `s0:armstate`] READ_MEMORY_BYTES64_OF_NUM in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th) [32; 72; 112; 152])) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:1280`,`:N`] QWORD64_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:1280)`; ARITH] THEN STRIP_TAC THEN
  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `160`; `n:num`; mk_small_numeral k;
                    `s0:armstate`] READ_MEMORY_BYTES128_OF_NUM in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th)
    [0; 16; 40; 56; 80; 96; 120; 136])) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:1280`,`:N`] QWORD128_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:1280)`; ARITH] THEN STRIP_TAC THEN

  (*** Simulate the whole thing, unrolling the loop ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_DECOMPRESS_D5_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[decompress_d5_lane]) (1--213) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient is the lane function of a 5-bit field of word n ***)

  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `5 * i`]
    (INST_TYPE [`:5`,`:M`; `:1280`,`:N`] FIELD_AS_SUBWORD)) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM DECOMPRESS_D5_LANE] THEN
  UNDISCH_TAC `i < 256` THEN SPEC_TAC(`i:num`,`i:num`) THEN

  (*** Split the stored vectors, and check the argument of each lane ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read (memory :> bytes128 a) s = xxx`) o
          concl))) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s213" THEN
  LANE_ARGS_BITBLAST_TAC 8 [`word (n:num):1280 word`]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_DECOMPRESS_D5_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x160); (a,160)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d5_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,160)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (5 * i)) MOD 2 EXP 5 +
                                16) DIV 32))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_DECOMPRESS_D5_EXEC
    MLKEM_DECOMPRESS_D5_CORRECT);;

let MLKEM_DECOMPRESS_D5_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x164); (a,160)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d5_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,160)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (5 * i)) MOD 2 EXP 5 +
                                16) DIV 32))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_decompress_d5_mc mlkem_decompress_d5_tmc
    MLKEM_DECOMPRESS_D5_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_decompress_d5" subroutine_signatures)
    MLKEM_DECOMPRESS_D5_NOIBT_SUBROUTINE_CORRECT
    MLKEM_DECOMPRESS_D5_EXEC;;

let MLKEM_DECOMPRESS_D5_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0x160); (a,160)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d5_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,160; r,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_DECOMPRESS_D5_EXEC);;

let MLKEM_DECOMPRESS_D5_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0x164); (a,160)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d5_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,160; r,512] [r,512])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_decompress_d5_mc mlkem_decompress_d5_tmc
    MLKEM_DECOMPRESS_D5_NOIBT_SUBROUTINE_SAFE));;
