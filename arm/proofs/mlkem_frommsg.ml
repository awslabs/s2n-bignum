(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 32-byte message to a polynomial.                          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_frommsg.o";;
 ****)

let mlkem_frommsg_mc = define_assert_from_elf
  "mlkem_frommsg_mc" "arm/mlkem/mlkem_frommsg.o"
[
  0xd503245f;       (* arm_BTI *)
  0x5280d022;       (* arm_MOV W2 (rvalue (word 1665)) *)
  0x4e020c5f;       (* arm_DUP_GEN Q31 X2 16 128 *)
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
  0xfc408420;       (* arm_LDR D0 X1 (Postimmediate_Offset (word 8)) *)
  0x4e010410;       (* arm_DUP_ELEM Q16 Q0 0 8 128 *)
  0x4e030411;       (* arm_DUP_ELEM Q17 Q0 1 8 128 *)
  0x4e050412;       (* arm_DUP_ELEM Q18 Q0 2 8 128 *)
  0x4e070413;       (* arm_DUP_ELEM Q19 Q0 3 8 128 *)
  0x4e090414;       (* arm_DUP_ELEM Q20 Q0 4 8 128 *)
  0x4e0b0415;       (* arm_DUP_ELEM Q21 Q0 5 8 128 *)
  0x4e0d0416;       (* arm_DUP_ELEM Q22 Q0 6 8 128 *)
  0x4e0f0417;       (* arm_DUP_ELEM Q23 Q0 7 8 128 *)
  0x4e7e8e10;       (* arm_CMTST_VEC Q16 Q16 Q30 16 128 *)
  0x4e7e8e31;       (* arm_CMTST_VEC Q17 Q17 Q30 16 128 *)
  0x4e7e8e52;       (* arm_CMTST_VEC Q18 Q18 Q30 16 128 *)
  0x4e7e8e73;       (* arm_CMTST_VEC Q19 Q19 Q30 16 128 *)
  0x4e7e8e94;       (* arm_CMTST_VEC Q20 Q20 Q30 16 128 *)
  0x4e7e8eb5;       (* arm_CMTST_VEC Q21 Q21 Q30 16 128 *)
  0x4e7e8ed6;       (* arm_CMTST_VEC Q22 Q22 Q30 16 128 *)
  0x4e7e8ef7;       (* arm_CMTST_VEC Q23 Q23 Q30 16 128 *)
  0x4e3f1e10;       (* arm_AND_VEC Q16 Q16 Q31 128 *)
  0x4e3f1e31;       (* arm_AND_VEC Q17 Q17 Q31 128 *)
  0x4e3f1e52;       (* arm_AND_VEC Q18 Q18 Q31 128 *)
  0x4e3f1e73;       (* arm_AND_VEC Q19 Q19 Q31 128 *)
  0x4e3f1e94;       (* arm_AND_VEC Q20 Q20 Q31 128 *)
  0x4e3f1eb5;       (* arm_AND_VEC Q21 Q21 Q31 128 *)
  0x4e3f1ed6;       (* arm_AND_VEC Q22 Q22 Q31 128 *)
  0x4e3f1ef7;       (* arm_AND_VEC Q23 Q23 Q31 128 *)
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

let mlkem_frommsg_tmc = define_trimmed "mlkem_frommsg_tmc" mlkem_frommsg_mc;;

let MLKEM_FROMMSG_EXEC = ARM_MK_EXEC_RULE mlkem_frommsg_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. Each coefficient is a bit of one of the four 64-bit    *)
(* words of the message as loaded.                                           *)
(* ------------------------------------------------------------------------- *)

let FROMMSG_COND = prove
 (`!b. word((3329 * bitval b + 1) DIV 2):int16 =
       if b then word 1665 else word 0`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_FROMMSG_CORRECT = prove
 (`!r a n pc.
        ALL (nonoverlapping (r,512)) [(word pc,0xb4); (a,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_frommsg_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,32)) s = n)
             (\s. read PC s = word(pc + 0xb0) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The four 64-bit words of the message, as loaded ***)

  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `32`; `n:num`; mk_small_numeral(8 * k);
                    `s0:armstate`] READ_MEMORY_BYTES64_OF_NUM in
    CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[WORD_ADD_0]) th) (0--3))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  (*** Simulate the whole thing, unrolling the loop ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_FROMMSG_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (1--137) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Split the stored 128-bit words into the coefficients ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s137" THEN

  (*** Each coefficient is a bit of one of the 64-bit words ***)

  ONCE_REWRITE_TAC[QWORD_BIT_ALT] THEN
  CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_DIV_CONV ORELSEC
                      NUM_MOD_CONV)) THEN
  SIMP_TAC[BIT_OF_MOD64; ARITH] THEN
  REWRITE_TAC[FROMMSG_COND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_NEG_BITVAL] THEN
  REPEAT CONJ_TAC THEN QWORDS_BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_FROMMSG_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0xb4); (a,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_frommsg_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,32)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_FROMMSG_EXEC MLKEM_FROMMSG_CORRECT);;

let MLKEM_FROMMSG_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0xb8); (a,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_frommsg_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,32)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE mlkem_frommsg_mc mlkem_frommsg_tmc
    MLKEM_FROMMSG_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_frommsg" subroutine_signatures)
    MLKEM_FROMMSG_NOIBT_SUBROUTINE_CORRECT
    MLKEM_FROMMSG_EXEC;;

let MLKEM_FROMMSG_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0xb4); (a,32)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_frommsg_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,32; r,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_FROMMSG_EXEC);;

let MLKEM_FROMMSG_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0xb8); (a,32)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_frommsg_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,32; r,512] [r,512])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE mlkem_frommsg_mc mlkem_frommsg_tmc
    MLKEM_FROMMSG_NOIBT_SUBROUTINE_SAFE));;
