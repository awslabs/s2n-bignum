(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of 10-bit fields and decompression of them to coefficients.     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_decompress_d10.o";;
 ****)

let mlkem_decompress_d10_mc = define_assert_from_elf
  "mlkem_decompress_d10_mc" "arm/mlkem/mlkem_decompress_d10.o"
[
  0xd503245f;       (* arm_BTI *)
  0x5281a022;       (* arm_MOV W2 (rvalue (word 3329)) *)
  0x4e020c5f;       (* arm_DUP_GEN Q31 X2 16 128 *)
  0x4f03a7fc;       (* arm_MOVI Q28 (word 9151454082924314368) *)
  0x4f07941c;       (* arm_ORR_VEC Q28 Q28 (rvalue (word 1163092243691008099729852934534463712)) 128 *)
  0xd2802002;       (* arm_MOV X2 (rvalue (word 256)) *)
  0xf2a04022;       (* arm_MOVK X2 (word 513) 16 *)
  0xf2c06042;       (* arm_MOVK X2 (word 770) 32 *)
  0xf2e08062;       (* arm_MOVK X2 (word 1027) 48 *)
  0xd280c0a3;       (* arm_MOV X3 (rvalue (word 1541)) *)
  0xf2a0e0c3;       (* arm_MOVK X3 (word 1798) 16 *)
  0xf2c100e3;       (* arm_MOVK X3 (word 2055) 32 *)
  0xf2e12103;       (* arm_MOVK X3 (word 2312) 48 *)
  0x9e67005e;       (* arm_FMOV_ItoF Q30 X2 0 *)
  0x4e181c7e;       (* arm_INS_GEN Q30 X3 64 64 *)
  0xd28000a2;       (* arm_MOV X2 (rvalue (word 5)) *)
  0xf2a00062;       (* arm_MOVK X2 (word 3) 16 *)
  0xf2c00022;       (* arm_MOVK X2 (word 1) 32 *)
  0xf2ffffe2;       (* arm_MOVK X2 (word 65535) 48 *)
  0x4e080c5d;       (* arm_DUP_GEN Q29 X2 64 128 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0xacc10420;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (iword (&32))) *)
  0xfc408422;       (* arm_LDR D2 X1 (Postimmediate_Offset (word 8)) *)
  0x6e015004;       (* arm_EXT Q4 Q0 Q1 80 *)
  0x6e022025;       (* arm_EXT Q5 Q1 Q2 32 *)
  0x6e027026;       (* arm_EXT Q6 Q1 Q2 112 *)
  0x4e1e0003;       (* arm_TBL Q3 [Q0] Q30 128 *)
  0x4e1e0084;       (* arm_TBL Q4 [Q4] Q30 128 *)
  0x4e1e00a5;       (* arm_TBL Q5 [Q5] Q30 128 *)
  0x4e1e00c6;       (* arm_TBL Q6 [Q6] Q30 128 *)
  0x6e7d4463;       (* arm_USHL_VEC Q3 Q3 Q29 16 128 *)
  0x6e7d4484;       (* arm_USHL_VEC Q4 Q4 Q29 16 128 *)
  0x6e7d44a5;       (* arm_USHL_VEC Q5 Q5 Q29 16 128 *)
  0x6e7d44c6;       (* arm_USHL_VEC Q6 Q6 Q29 16 128 *)
  0x4e3c1c63;       (* arm_AND_VEC Q3 Q3 Q28 128 *)
  0x4e3c1c84;       (* arm_AND_VEC Q4 Q4 Q28 128 *)
  0x4e3c1ca5;       (* arm_AND_VEC Q5 Q5 Q28 128 *)
  0x4e3c1cc6;       (* arm_AND_VEC Q6 Q6 Q28 128 *)
  0x6e7fb463;       (* arm_SQRDMULH_VEC Q3 Q3 Q31 16 128 *)
  0x6e7fb484;       (* arm_SQRDMULH_VEC Q4 Q4 Q31 16 128 *)
  0x6e7fb4a5;       (* arm_SQRDMULH_VEC Q5 Q5 Q31 16 128 *)
  0x6e7fb4c6;       (* arm_SQRDMULH_VEC Q6 Q6 Q31 16 128 *)
  0xac811003;       (* arm_STP Q3 Q4 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac811805;       (* arm_STP Q5 Q6 X0 (Postimmediate_Offset (iword (&32))) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffd01;       (* arm_BNE (word 2097056) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_decompress_d10_tmc =
  define_trimmed "mlkem_decompress_d10_tmc" mlkem_decompress_d10_mc;;

let MLKEM_DECOMPRESS_D10_EXEC = ARM_MK_EXEC_RULE mlkem_decompress_d10_tmc;;

(* ------------------------------------------------------------------------- *)
(* The decompression of each 10-bit field u as the code computes it, from    *)
(* the lane u * 2^5 (abbreviated, to keep the terms small in the             *)
(* simulation), checked for all 1024 values.                                 *)
(* ------------------------------------------------------------------------- *)

let decompress_d10_lane = new_definition
 `decompress_d10_lane (v:int16) =
  iword_saturate((&2 * ival v * &3329 + &32768) div &65536):int16`;;

let DECOMPRESS_D10_LANE = time prove
 (`!f:(10)word.
        decompress_d10_lane (word_shl (word_zx f:int16) 5) =
        word((3329 * val f + 512) DIV 1024)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM(ISPEC `f:(10)word` WORD_VAL)] THEN
  MP_TAC(ISPEC `f:(10)word` VAL_BOUND) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:(10)word)`,`k:num`) THEN
  REWRITE_TAC[decompress_d10_lane; iword_saturate; word_INT_MIN;
              word_INT_MAX; DIMINDEX_16] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_DECOMPRESS_D10_CORRECT = prove
 (`!r a n pc.
        ALL (nonoverlapping (r,512)) [(word pc,0xb8); (a,320)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d10_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,320)) s = n)
             (\s. read PC s = word(pc + 0xb4) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (10 * i)) MOD 2 EXP 10 +
                                512) DIV 1024))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The words of the input, as loaded, are subwords of word n ***)

  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `320`; `n:num`; mk_small_numeral k;
                    `s0:armstate`] READ_MEMORY_BYTES64_OF_NUM in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th)
    [32; 72; 112; 152; 192; 232; 272; 312])) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:2560`,`:N`] QWORD64_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:2560)`; ARITH] THEN STRIP_TAC THEN
  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `320`; `n:num`; mk_small_numeral k;
                    `s0:armstate`] READ_MEMORY_BYTES128_OF_NUM in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th)
    [0; 16; 40; 56; 80; 96; 120; 136; 160; 176; 200; 216; 240; 256; 280;
     296])) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:2560`,`:N`] QWORD128_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:2560)`; ARITH] THEN STRIP_TAC THEN

  (*** Simulate the whole thing, unrolling the loop ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_DECOMPRESS_D10_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[decompress_d10_lane]) (1--220) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient is the lane function of a 10-bit field of word n ***)

  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `10 * i`]
    (INST_TYPE [`:10`,`:M`; `:2560`,`:N`] FIELD_AS_SUBWORD)) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM DECOMPRESS_D10_LANE] THEN
  UNDISCH_TAC `i < 256` THEN SPEC_TAC(`i:num`,`i:num`) THEN

  (*** Split the stored vectors, and check the argument of each lane ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read (memory :> bytes128 a) s = xxx`) o
          concl))) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s220" THEN
  LANE_ARGS_BITBLAST_TAC 8 [`word (n:num):2560 word`]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_DECOMPRESS_D10_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0xb8); (a,320)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d10_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,320)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (10 * i)) MOD 2 EXP 10 +
                                512) DIV 1024))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_DECOMPRESS_D10_EXEC
    MLKEM_DECOMPRESS_D10_CORRECT);;

let MLKEM_DECOMPRESS_D10_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0xbc); (a,320)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d10_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,320)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (10 * i)) MOD 2 EXP 10 +
                                512) DIV 1024))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_decompress_d10_mc mlkem_decompress_d10_tmc
    MLKEM_DECOMPRESS_D10_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_decompress_d10" subroutine_signatures)
    MLKEM_DECOMPRESS_D10_NOIBT_SUBROUTINE_CORRECT
    MLKEM_DECOMPRESS_D10_EXEC;;

let MLKEM_DECOMPRESS_D10_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0xb8); (a,320)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_decompress_d10_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,320; r,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_DECOMPRESS_D10_EXEC);;

let MLKEM_DECOMPRESS_D10_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0xbc); (a,320)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d10_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,320; r,512] [r,512])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_decompress_d10_mc mlkem_decompress_d10_tmc
    MLKEM_DECOMPRESS_D10_NOIBT_SUBROUTINE_SAFE));;
