(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of 4-bit fields and decompression of them to coefficients.      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_decompress_d4.o";;
 ****)

let mlkem_decompress_d4_mc = define_assert_from_elf
  "mlkem_decompress_d4_mc" "arm/mlkem/mlkem_decompress_d4.o"
[
  0xd503245f;       (* arm_BTI *)
  0x528d0102;       (* arm_MOV W2 (rvalue (word 26632)) *)
  0x4e020c5f;       (* arm_DUP_GEN Q31 X2 16 128 *)
  0x6f00e41e;       (* arm_MOVI Q30 (word 0) *)
  0x4f00e5fd;       (* arm_MOVI Q29 (word 1085102592571150095) *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0xacc10420;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (iword (&32))) *)
  0x4e3d1c02;       (* arm_AND_VEC Q2 Q0 Q29 128 *)
  0x4e3d1c23;       (* arm_AND_VEC Q3 Q1 Q29 128 *)
  0x6f0c0400;       (* arm_USHR_VEC Q0 Q0 4 8 128 *)
  0x6f0c0421;       (* arm_USHR_VEC Q1 Q1 4 8 128 *)
  0x4e003844;       (* arm_ZIP1 Q4 Q2 Q0 8 128 *)
  0x4e007845;       (* arm_ZIP2 Q5 Q2 Q0 8 128 *)
  0x4e013862;       (* arm_ZIP1 Q2 Q3 Q1 8 128 *)
  0x4e017863;       (* arm_ZIP2 Q3 Q3 Q1 8 128 *)
  0x4e043bd0;       (* arm_ZIP1 Q16 Q30 Q4 8 128 *)
  0x4e047bd1;       (* arm_ZIP2 Q17 Q30 Q4 8 128 *)
  0x4e053bd2;       (* arm_ZIP1 Q18 Q30 Q5 8 128 *)
  0x4e057bd3;       (* arm_ZIP2 Q19 Q30 Q5 8 128 *)
  0x4e023bd4;       (* arm_ZIP1 Q20 Q30 Q2 8 128 *)
  0x4e027bd5;       (* arm_ZIP2 Q21 Q30 Q2 8 128 *)
  0x4e033bd6;       (* arm_ZIP1 Q22 Q30 Q3 8 128 *)
  0x4e037bd7;       (* arm_ZIP2 Q23 Q30 Q3 8 128 *)
  0x6e7fb610;       (* arm_SQRDMULH_VEC Q16 Q16 Q31 16 128 *)
  0x6e7fb631;       (* arm_SQRDMULH_VEC Q17 Q17 Q31 16 128 *)
  0x6e7fb652;       (* arm_SQRDMULH_VEC Q18 Q18 Q31 16 128 *)
  0x6e7fb673;       (* arm_SQRDMULH_VEC Q19 Q19 Q31 16 128 *)
  0x6e7fb694;       (* arm_SQRDMULH_VEC Q20 Q20 Q31 16 128 *)
  0x6e7fb6b5;       (* arm_SQRDMULH_VEC Q21 Q21 Q31 16 128 *)
  0x6e7fb6d6;       (* arm_SQRDMULH_VEC Q22 Q22 Q31 16 128 *)
  0x6e7fb6f7;       (* arm_SQRDMULH_VEC Q23 Q23 Q31 16 128 *)
  0xac814410;       (* arm_STP Q16 Q17 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac814c12;       (* arm_STP Q18 Q19 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac815414;       (* arm_STP Q20 Q21 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac815c16;       (* arm_STP Q22 Q23 X0 (Postimmediate_Offset (iword (&32))) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffc41;       (* arm_BNE (word 2097032) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_decompress_d4_tmc =
  define_trimmed "mlkem_decompress_d4_tmc" mlkem_decompress_d4_mc;;

let MLKEM_DECOMPRESS_D4_EXEC = ARM_MK_EXEC_RULE mlkem_decompress_d4_tmc;;

(* ------------------------------------------------------------------------- *)
(* The decompression of each 4-bit field u as the code computes it, from the *)
(* lane u * 2^8 (abbreviated, to keep the terms small in the simulation),    *)
(* checked for all 16 values.                                                *)
(* ------------------------------------------------------------------------- *)

let decompress_d4_lane = new_definition
 `decompress_d4_lane (v:int16) =
  iword_saturate((&2 * ival v * &26632 + &32768) div &65536):int16`;;

let DECOMPRESS_D4_LANE = time prove
 (`!f:(4)word.
        decompress_d4_lane (word_join (word_zx f:byte) (word 0:byte)) =
        word((3329 * val f + 8) DIV 16)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM(ISPEC `f:(4)word` WORD_VAL)] THEN
  MP_TAC(ISPEC `f:(4)word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_4] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:(4)word)`,`k:num`) THEN
  REWRITE_TAC[decompress_d4_lane; iword_saturate; word_INT_MIN;
              word_INT_MAX; DIMINDEX_16] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_DECOMPRESS_D4_CORRECT = prove
 (`!r a n pc.
        ALL (nonoverlapping (r,512)) [(word pc,0x94); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d4_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read PC s = word(pc + 0x90) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (4 * i)) MOD 2 EXP 4 + 8)
                               DIV 16))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The 128-bit words of the input, as loaded, are subwords of word n ***)

  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `128`; `n:num`; mk_small_numeral(16 * k);
                    `s0:armstate`] READ_MEMORY_BYTES128_OF_NUM in
    let th' = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                        REWRITE_CONV[WORD_ADD_0]) th in
    REWRITE_RULE[ARITH_RULE(mk_comb(mk_comb(`(<=):num->num->bool`,
      mk_binop `(+):num->num->num` (mk_small_numeral(16*k)) `16`), `128`))]
     th') (0--7))) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:1024`,`:N`] QWORD128_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:1024)`; ARITH] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_DECOMPRESS_D4_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[decompress_d4_lane]) (1--129) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient is the lane function of a 4-bit field of word n ***)

  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `4 * i`]
    (INST_TYPE [`:4`,`:M`; `:1024`,`:N`] FIELD_AS_SUBWORD)) THEN
  REWRITE_TAC[DIMINDEX_4; DIMINDEX_CONV `dimindex(:1024)`] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM DECOMPRESS_D4_LANE] THEN
  UNDISCH_TAC `i < 256` THEN SPEC_TAC(`i:num`,`i:num`) THEN

  (*** Split the stored vectors, and check the argument of each lane ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read (memory :> bytes128 a) s = xxx`) o
          concl))) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s129" THEN
  LANE_ARGS_BITBLAST_TAC 8 [`word (n:num):1024 word`]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_DECOMPRESS_D4_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x94); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d4_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (4 * i)) MOD 2 EXP 4 + 8)
                               DIV 16))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_DECOMPRESS_D4_EXEC
    MLKEM_DECOMPRESS_D4_CORRECT);;

let MLKEM_DECOMPRESS_D4_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x98); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d4_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (4 * i)) MOD 2 EXP 4 + 8)
                               DIV 16))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_decompress_d4_mc mlkem_decompress_d4_tmc
    MLKEM_DECOMPRESS_D4_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_decompress_d4" subroutine_signatures)
    MLKEM_DECOMPRESS_D4_NOIBT_SUBROUTINE_CORRECT
    MLKEM_DECOMPRESS_D4_EXEC;;

let MLKEM_DECOMPRESS_D4_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0x94); (a,128)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d4_tmc /\
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
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_DECOMPRESS_D4_EXEC);;

let MLKEM_DECOMPRESS_D4_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0x98); (a,128)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d4_mc /\
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
    mlkem_decompress_d4_mc mlkem_decompress_d4_tmc
    MLKEM_DECOMPRESS_D4_NOIBT_SUBROUTINE_SAFE));;
