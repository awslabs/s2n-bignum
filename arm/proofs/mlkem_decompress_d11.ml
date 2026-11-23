(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of 11-bit fields and decompression of them to coefficients.     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_decompress_d11.o";;
 ****)

let mlkem_decompress_d11_mc = define_assert_from_elf
  "mlkem_decompress_d11_mc" "arm/mlkem/mlkem_decompress_d11.o"
[
  0xd503245f;       (* arm_BTI *)
  0x5281a022;       (* arm_MOV W2 (rvalue (word 3329)) *)
  0x4e020c59;       (* arm_DUP_GEN Q25 X2 16 128 *)
  0x6f00e41a;       (* arm_MOVI Q26 (word 0) *)
  0x6f04a41b;       (* arm_MOVI Q27 (word 9223231297218904063) *)
  0x6f0095fb;       (* arm_BIC_VEC Q27 Q27 (rvalue (word 77885641318594292392624080437575695)) 128 *)
  0xd2802002;       (* arm_MOV X2 (rvalue (word 256)) *)
  0xf2a06042;       (* arm_MOVK X2 (word 770) 16 *)
  0xf2c04022;       (* arm_MOVK X2 (word 513) 32 *)
  0xf2e08062;       (* arm_MOVK X2 (word 1027) 48 *)
  0xd2806043;       (* arm_MOV X3 (rvalue (word 770)) *)
  0xf2a0a083;       (* arm_MOVK X3 (word 1284) 16 *)
  0xf2c0a083;       (* arm_MOVK X3 (word 1284) 32 *)
  0xf2e0e0c3;       (* arm_MOVK X3 (word 1798) 48 *)
  0x9e67005c;       (* arm_FMOV_ItoF Q28 X2 0 *)
  0x4e181c7c;       (* arm_INS_GEN Q28 X3 64 64 *)
  0xd280c0a2;       (* arm_MOV X2 (rvalue (word 1541)) *)
  0xf2a100e2;       (* arm_MOVK X2 (word 2055) 16 *)
  0xf2c0e0c2;       (* arm_MOVK X2 (word 1798) 32 *)
  0xf2e12102;       (* arm_MOVK X2 (word 2312) 48 *)
  0xd2812103;       (* arm_MOV X3 (rvalue (word 2312)) *)
  0xf2a16143;       (* arm_MOVK X3 (word 2826) 16 *)
  0xf2c14123;       (* arm_MOVK X3 (word 2569) 32 *)
  0xf2e18163;       (* arm_MOVK X3 (word 3083) 48 *)
  0x9e67005d;       (* arm_FMOV_ItoF Q29 X2 0 *)
  0x4e181c7d;       (* arm_INS_GEN Q29 X3 64 64 *)
  0xd2800082;       (* arm_MOV X2 (rvalue (word 4)) *)
  0xf2c00022;       (* arm_MOVK X2 (word 1) 32 *)
  0xd29fffc3;       (* arm_MOV X3 (rvalue (word 65534)) *)
  0xf2bfffe3;       (* arm_MOVK X3 (word 65535) 16 *)
  0xf2c00063;       (* arm_MOVK X3 (word 3) 32 *)
  0x9e67005e;       (* arm_FMOV_ItoF Q30 X2 0 *)
  0x4e181c7e;       (* arm_INS_GEN Q30 X3 64 64 *)
  0xd2800002;       (* arm_MOV X2 (rvalue (word 0)) *)
  0xf2dfffa2;       (* arm_MOVK X2 (word 65533) 32 *)
  0xf2ffffe2;       (* arm_MOVK X2 (word 65535) 48 *)
  0xd2800043;       (* arm_MOV X3 (rvalue (word 2)) *)
  0xf2dfffe3;       (* arm_MOVK X3 (word 65535) 32 *)
  0xf2ffffe3;       (* arm_MOVK X3 (word 65535) 48 *)
  0x9e67005f;       (* arm_FMOV_ItoF Q31 X2 0 *)
  0x4e181c7f;       (* arm_INS_GEN Q31 X3 64 64 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0xacc10420;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (iword (&32))) *)
  0xfc408422;       (* arm_LDR D2 X1 (Postimmediate_Offset (word 8)) *)
  0x4ddf8022;       (* arm_LD1 Q2 X1 (Postimmediate_Offset (word 4)) 32 2 *)
  0x6e015804;       (* arm_EXT Q4 Q0 Q1 88 *)
  0x6e023025;       (* arm_EXT Q5 Q1 Q2 48 *)
  0x6e1a0846;       (* arm_EXT Q6 Q2 Q26 8 *)
  0x4e1c0010;       (* arm_TBL Q16 [Q0] Q28 128 *)
  0x4e1d0011;       (* arm_TBL Q17 [Q0] Q29 128 *)
  0x4e1c0092;       (* arm_TBL Q18 [Q4] Q28 128 *)
  0x4e1d0093;       (* arm_TBL Q19 [Q4] Q29 128 *)
  0x4e1c00b4;       (* arm_TBL Q20 [Q5] Q28 128 *)
  0x4e1d00b5;       (* arm_TBL Q21 [Q5] Q29 128 *)
  0x4e1c00d6;       (* arm_TBL Q22 [Q6] Q28 128 *)
  0x4e1d00d7;       (* arm_TBL Q23 [Q6] Q29 128 *)
  0x6ebe4610;       (* arm_USHL_VEC Q16 Q16 Q30 32 128 *)
  0x6ebf4631;       (* arm_USHL_VEC Q17 Q17 Q31 32 128 *)
  0x6ebe4652;       (* arm_USHL_VEC Q18 Q18 Q30 32 128 *)
  0x6ebf4673;       (* arm_USHL_VEC Q19 Q19 Q31 32 128 *)
  0x6ebe4694;       (* arm_USHL_VEC Q20 Q20 Q30 32 128 *)
  0x6ebf46b5;       (* arm_USHL_VEC Q21 Q21 Q31 32 128 *)
  0x6ebe46d6;       (* arm_USHL_VEC Q22 Q22 Q30 32 128 *)
  0x6ebf46f7;       (* arm_USHL_VEC Q23 Q23 Q31 32 128 *)
  0x4e511a10;       (* arm_UZP1 Q16 Q16 Q17 16 128 *)
  0x4e531a51;       (* arm_UZP1 Q17 Q18 Q19 16 128 *)
  0x4e551a92;       (* arm_UZP1 Q18 Q20 Q21 16 128 *)
  0x4e571ad3;       (* arm_UZP1 Q19 Q22 Q23 16 128 *)
  0x4e3b1e10;       (* arm_AND_VEC Q16 Q16 Q27 128 *)
  0x4e3b1e31;       (* arm_AND_VEC Q17 Q17 Q27 128 *)
  0x4e3b1e52;       (* arm_AND_VEC Q18 Q18 Q27 128 *)
  0x4e3b1e73;       (* arm_AND_VEC Q19 Q19 Q27 128 *)
  0x6e79b610;       (* arm_SQRDMULH_VEC Q16 Q16 Q25 16 128 *)
  0x6e79b631;       (* arm_SQRDMULH_VEC Q17 Q17 Q25 16 128 *)
  0x6e79b652;       (* arm_SQRDMULH_VEC Q18 Q18 Q25 16 128 *)
  0x6e79b673;       (* arm_SQRDMULH_VEC Q19 Q19 Q25 16 128 *)
  0xac814410;       (* arm_STP Q16 Q17 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac814c12;       (* arm_STP Q18 Q19 X0 (Postimmediate_Offset (iword (&32))) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffb61;       (* arm_BNE (word 2097004) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_decompress_d11_tmc =
  define_trimmed "mlkem_decompress_d11_tmc" mlkem_decompress_d11_mc;;

let MLKEM_DECOMPRESS_D11_EXEC = ARM_MK_EXEC_RULE mlkem_decompress_d11_tmc;;

(* ------------------------------------------------------------------------- *)
(* The decompression of each 11-bit field u as the code computes it, from    *)
(* the lane u * 2^4 (abbreviated, to keep the terms small in the             *)
(* simulation), checked for all 2048 values.                                 *)
(* ------------------------------------------------------------------------- *)

let decompress_d11_lane = new_definition
 `decompress_d11_lane (v:int16) =
  iword_saturate((&2 * ival v * &3329 + &32768) div &65536):int16`;;

let DECOMPRESS_D11_LANE = time prove
 (`!f:(11)word.
        decompress_d11_lane (word_shl (word_zx f:int16) 4) =
        word((3329 * val f + 1024) DIV 2048)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM(ISPEC `f:(11)word` WORD_VAL)] THEN
  MP_TAC(ISPEC `f:(11)word` VAL_BOUND) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:(11)word)`,`k:num`) THEN
  REWRITE_TAC[decompress_d11_lane; iword_saturate; word_INT_MIN;
              word_INT_MAX; DIMINDEX_16] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_DECOMPRESS_D11_CORRECT = prove
 (`!r a n pc.
        ALL (nonoverlapping (r,512)) [(word pc,0x140); (a,352)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d11_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,352)) s = n)
             (\s. read PC s = word(pc + 0x13c) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (11 * i)) MOD 2 EXP 11 +
                                1024) DIV 2048))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The words of the input, as loaded, are subwords of word n ***)

  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `352`; `n:num`; mk_small_numeral k;
                    `s0:armstate`] READ_MEMORY_BYTES32_OF_NUM in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th)
    [40; 84; 128; 172; 216; 260; 304; 348])) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:2816`,`:N`] QWORD32_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:2816)`; ARITH] THEN STRIP_TAC THEN
  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `352`; `n:num`; mk_small_numeral k;
                    `s0:armstate`] READ_MEMORY_BYTES64_OF_NUM in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th)
    [32; 76; 120; 164; 208; 252; 296; 340])) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:2816`,`:N`] QWORD64_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:2816)`; ARITH] THEN STRIP_TAC THEN
  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `352`; `n:num`; mk_small_numeral k;
                    `s0:armstate`] READ_MEMORY_BYTES128_OF_NUM in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th)
    [0; 16; 44; 60; 88; 104; 132; 148; 176; 192; 220; 236; 264; 280; 308;
     324])) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:2816`,`:N`] QWORD128_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:2816)`; ARITH] THEN STRIP_TAC THEN

  (*** Simulate the whole thing, unrolling the loop ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_DECOMPRESS_D11_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[decompress_d11_lane]) (1--345) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient is the lane function of a 11-bit field of word n ***)

  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `11 * i`]
    (INST_TYPE [`:11`,`:M`; `:2816`,`:N`] FIELD_AS_SUBWORD)) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM DECOMPRESS_D11_LANE] THEN
  UNDISCH_TAC `i < 256` THEN SPEC_TAC(`i:num`,`i:num`) THEN

  (*** Split the stored vectors, and check the argument of each lane ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read (memory :> bytes128 a) s = xxx`) o
          concl))) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s345" THEN
  LANE_ARGS_BITBLAST_TAC 8 [`word (n:num):2816 word`]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_DECOMPRESS_D11_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x140); (a,352)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d11_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,352)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (11 * i)) MOD 2 EXP 11 +
                                1024) DIV 2048))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_DECOMPRESS_D11_EXEC
    MLKEM_DECOMPRESS_D11_CORRECT);;

let MLKEM_DECOMPRESS_D11_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x144); (a,352)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d11_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,352)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (11 * i)) MOD 2 EXP 11 +
                                1024) DIV 2048))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_decompress_d11_mc mlkem_decompress_d11_tmc
    MLKEM_DECOMPRESS_D11_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_decompress_d11" subroutine_signatures)
    MLKEM_DECOMPRESS_D11_NOIBT_SUBROUTINE_CORRECT
    MLKEM_DECOMPRESS_D11_EXEC;;

let MLKEM_DECOMPRESS_D11_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0x140); (a,352)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_decompress_d11_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,352; r,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_DECOMPRESS_D11_EXEC);;

let MLKEM_DECOMPRESS_D11_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0x144); (a,352)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_decompress_d11_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,352; r,512] [r,512])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_decompress_d11_mc mlkem_decompress_d11_tmc
    MLKEM_DECOMPRESS_D11_NOIBT_SUBROUTINE_SAFE));;
