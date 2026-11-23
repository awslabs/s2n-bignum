(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of polynomial coefficients as 12-bit fields.                    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_frombytes.o";;
 ****)

let mlkem_frombytes_mc = define_assert_from_elf
  "mlkem_frombytes_mc" "arm/mlkem/mlkem_frombytes.o"
[
  0xd503245f;       (* arm_BTI *)
  0xd2802002;       (* arm_MOV X2 (rvalue (word 256)) *)
  0xf2a04022;       (* arm_MOVK X2 (word 513) 16 *)
  0xf2c08062;       (* arm_MOVK X2 (word 1027) 32 *)
  0xf2e0a082;       (* arm_MOVK X2 (word 1284) 48 *)
  0xd280e0c3;       (* arm_MOV X3 (rvalue (word 1798)) *)
  0xf2a100e3;       (* arm_MOVK X3 (word 2055) 16 *)
  0xf2c14123;       (* arm_MOVK X3 (word 2569) 32 *)
  0xf2e16143;       (* arm_MOVK X3 (word 2826) 48 *)
  0x9e67005f;       (* arm_FMOV_ItoF Q31 X2 0 *)
  0x4e181c7f;       (* arm_INS_GEN Q31 X3 64 64 *)
  0xd2800002;       (* arm_MOV X2 (rvalue (word 0)) *)
  0xf2bfff82;       (* arm_MOVK X2 (word 65532) 16 *)
  0xf2ffff82;       (* arm_MOVK X2 (word 65532) 48 *)
  0x4e080c5e;       (* arm_DUP_GEN Q30 X2 64 128 *)
  0x6f07a61d;       (* arm_MOVI Q29 (word 1152657617789587455) *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0xacc10420;       (* arm_LDP Q0 Q1 X1 (Postimmediate_Offset (iword (&32))) *)
  0x3cc10422;       (* arm_LDR Q2 X1 (Postimmediate_Offset (word 16)) *)
  0x6e016004;       (* arm_EXT Q4 Q0 Q1 96 *)
  0x6e024025;       (* arm_EXT Q5 Q1 Q2 64 *)
  0x6e022046;       (* arm_EXT Q6 Q2 Q2 32 *)
  0x4e1f0003;       (* arm_TBL Q3 [Q0] Q31 128 *)
  0x4e1f0084;       (* arm_TBL Q4 [Q4] Q31 128 *)
  0x4e1f00a5;       (* arm_TBL Q5 [Q5] Q31 128 *)
  0x4e1f00c6;       (* arm_TBL Q6 [Q6] Q31 128 *)
  0x6e7e4463;       (* arm_USHL_VEC Q3 Q3 Q30 16 128 *)
  0x6e7e4484;       (* arm_USHL_VEC Q4 Q4 Q30 16 128 *)
  0x6e7e44a5;       (* arm_USHL_VEC Q5 Q5 Q30 16 128 *)
  0x6e7e44c6;       (* arm_USHL_VEC Q6 Q6 Q30 16 128 *)
  0x4e3d1c63;       (* arm_AND_VEC Q3 Q3 Q29 128 *)
  0x4e3d1c84;       (* arm_AND_VEC Q4 Q4 Q29 128 *)
  0x4e3d1ca5;       (* arm_AND_VEC Q5 Q5 Q29 128 *)
  0x4e3d1cc6;       (* arm_AND_VEC Q6 Q6 Q29 128 *)
  0xac811003;       (* arm_STP Q3 Q4 X0 (Postimmediate_Offset (iword (&32))) *)
  0xac811805;       (* arm_STP Q5 Q6 X0 (Postimmediate_Offset (iword (&32))) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0x54fffd81;       (* arm_BNE (word 2097072) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_frombytes_tmc =
  define_trimmed "mlkem_frombytes_tmc" mlkem_frombytes_mc;;

let MLKEM_FROMBYTES_EXEC = ARM_MK_EXEC_RULE mlkem_frombytes_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_FROMBYTES_CORRECT = prove
 (`!r a n pc.
        ALL (nonoverlapping (r,512)) [(word pc,0x98); (a,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_frombytes_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,384)) s = n)
             (\s. read PC s = word(pc + 0x94) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The words of the input, as loaded, are subwords of word n ***)

  MP_TAC(end_itlist CONJ (map (fun k ->
    let th = SPECL [`a:int64`; `384`; `n:num`; mk_small_numeral k;
                    `s0:armstate`] READ_MEMORY_BYTES128_OF_NUM in
    CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
              REWRITE_CONV[WORD_ADD_0]) th)
    [0; 16; 32; 48; 64; 80; 96; 112; 128; 144; 160; 176; 192; 208; 224; 240;
     256; 272; 288; 304; 320; 336; 352; 368])) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV THENC
           ONCE_DEPTH_CONV NUM_LE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INST_TYPE [`:3072`,`:N`] QWORD128_AS_SUBWORD;
           DIMINDEX_CONV `dimindex(:3072)`; ARITH] THEN STRIP_TAC THEN

  (*** Simulate the whole thing, unrolling the loop ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_FROMBYTES_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (1--184) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient is a 12-bit field of word n ***)

  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `12 * i`]
    (INST_TYPE [`:12`,`:M`; `:3072`,`:N`] FIELD_AS_SUBWORD)) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM word_zx] THEN
  UNDISCH_TAC `i < 256` THEN SPEC_TAC(`i:num`,`i:num`) THEN

  (*** Split the stored vectors, and check the argument of each lane ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read (memory :> bytes128 a) s = xxx`) o
          concl))) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN DISCARD_STATE_TAC "s184" THEN
  CHUNKED_ATOMS_BITBLAST_TAC 8 [`word (n:num):3072 word`]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine forms, without and with the BTI landing pad.               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_FROMBYTES_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x98); (a,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_frombytes_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,384)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_FROMBYTES_EXEC
    MLKEM_FROMBYTES_CORRECT);;

let MLKEM_FROMBYTES_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0x9c); (a,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_frombytes_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,384)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_frombytes_mc mlkem_frombytes_tmc
    MLKEM_FROMBYTES_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_frombytes" subroutine_signatures)
    MLKEM_FROMBYTES_NOIBT_SUBROUTINE_CORRECT
    MLKEM_FROMBYTES_EXEC;;

let MLKEM_FROMBYTES_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0x98); (a,384)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_frombytes_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,384; r,512] [r,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_FROMBYTES_EXEC);;

let MLKEM_FROMBYTES_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [(word pc,0x9c); (a,384)]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_frombytes_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,384; r,512] [r,512])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_frombytes_mc mlkem_frombytes_tmc
    MLKEM_FROMBYTES_NOIBT_SUBROUTINE_SAFE));;
