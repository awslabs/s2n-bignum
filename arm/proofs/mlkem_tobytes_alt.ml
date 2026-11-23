(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of polynomial coefficients as 12-bit fields (alternative code).   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_tobytes_alt.o";;
 ****)

let mlkem_tobytes_alt_mc = define_assert_from_elf
 "mlkem_tobytes_alt_mc" "arm/mlkem/mlkem_tobytes_alt.o"
[
  0xd503245f;       (* arm_BTI *)
  0xd2800202;       (* arm_MOV X2 (rvalue (word 16)) *)
  0x3dc00425;       (* arm_LDR Q5 X1 (Immediate_Offset (word 16)) *)
  0x3cc20423;       (* arm_LDR Q3 X1 (Postimmediate_Offset (word 32)) *)
  0x3cc2043d;       (* arm_LDR Q29 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0022;       (* arm_LDR Q2 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc0043b;       (* arm_LDR Q27 X1 (Immediate_Offset (word 16)) *)
  0x3dc00c37;       (* arm_LDR Q23 X1 (Immediate_Offset (word 48)) *)
  0x3cc20431;       (* arm_LDR Q17 X1 (Postimmediate_Offset (word 32)) *)
  0x3cc20430;       (* arm_LDR Q16 X1 (Postimmediate_Offset (word 32)) *)
  0x4e45587a;       (* arm_UZP2 Q26 Q3 Q5 16 128 *)
  0x4e451873;       (* arm_UZP1 Q19 Q3 Q5 16 128 *)
  0x4e425ba0;       (* arm_UZP2 Q0 Q29 Q2 16 128 *)
  0x4e421ba1;       (* arm_UZP1 Q1 Q29 Q2 16 128 *)
  0x0e212b45;       (* arm_XTN Q5 Q26 8 *)
  0x0f088663;       (* arm_SHRN Q3 Q19 8 8 *)
  0x0f0c8744;       (* arm_SHRN Q4 Q26 4 8 *)
  0x0e212812;       (* arm_XTN Q18 Q0 8 *)
  0x0f0c841e;       (* arm_SHRN Q30 Q0 4 8 *)
  0x0e21283c;       (* arm_XTN Q28 Q1 8 *)
  0x0f08843d;       (* arm_SHRN Q29 Q1 8 8 *)
  0x2f0c54a3;       (* arm_SLI_VEC Q3 Q5 4 64 8 *)
  0x0e212a62;       (* arm_XTN Q2 Q19 8 *)
  0x2f0c565d;       (* arm_SLI_VEC Q29 Q18 4 64 8 *)
  0xd341fc42;       (* arm_LSR X2 X2 1 *)
  0xd1000842;       (* arm_SUB X2 X2 (rvalue (word 2)) *)
  0x4e5b1a39;       (* arm_UZP1 Q25 Q17 Q27 16 128 *)
  0x4e5b5a3f;       (* arm_UZP2 Q31 Q17 Q27 16 128 *)
  0x4e571a18;       (* arm_UZP1 Q24 Q16 Q23 16 128 *)
  0x4e575a06;       (* arm_UZP2 Q6 Q16 Q23 16 128 *)
  0x0c9f4002;       (* arm_ST3 [Q2; Q3; Q4] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0f088723;       (* arm_SHRN Q3 Q25 8 8 *)
  0x3cc20431;       (* arm_LDR Q17 X1 (Postimmediate_Offset (word 32)) *)
  0x0f0c87e4;       (* arm_SHRN Q4 Q31 4 8 *)
  0x0e2128d5;       (* arm_XTN Q21 Q6 8 *)
  0x3dc00437;       (* arm_LDR Q23 X1 (Immediate_Offset (word 16)) *)
  0x0c9f401c;       (* arm_ST3 [Q28; Q29; Q30] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0f08871d;       (* arm_SHRN Q29 Q24 8 8 *)
  0x3cdf003b;       (* arm_LDR Q27 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x0e212bf4;       (* arm_XTN Q20 Q31 8 *)
  0x3cc20430;       (* arm_LDR Q16 X1 (Postimmediate_Offset (word 32)) *)
  0x2f0c56bd;       (* arm_SLI_VEC Q29 Q21 4 64 8 *)
  0x0e212b22;       (* arm_XTN Q2 Q25 8 *)
  0x2f0c5683;       (* arm_SLI_VEC Q3 Q20 4 64 8 *)
  0x0e212b1c;       (* arm_XTN Q28 Q24 8 *)
  0x0f0c84de;       (* arm_SHRN Q30 Q6 4 8 *)
  0xf1000442;       (* arm_SUBS X2 X2 (rvalue (word 1)) *)
  0xb5fffd62;       (* arm_CBNZ X2 (word 2097068) *)
  0x4e5b5a27;       (* arm_UZP2 Q7 Q17 Q27 16 128 *)
  0x4e5b1a39;       (* arm_UZP1 Q25 Q17 Q27 16 128 *)
  0x4e575a00;       (* arm_UZP2 Q0 Q16 Q23 16 128 *)
  0x0c9f4002;       (* arm_ST3 [Q2; Q3; Q4] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0c9f401c;       (* arm_ST3 [Q28; Q29; Q30] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0f088735;       (* arm_SHRN Q21 Q25 8 8 *)
  0x4e571a02;       (* arm_UZP1 Q2 Q16 Q23 16 128 *)
  0x0f0c84f6;       (* arm_SHRN Q22 Q7 4 8 *)
  0x0f0c8404;       (* arm_SHRN Q4 Q0 4 8 *)
  0x0e2128fc;       (* arm_XTN Q28 Q7 8 *)
  0x0e21281b;       (* arm_XTN Q27 Q0 8 *)
  0x0f088443;       (* arm_SHRN Q3 Q2 8 8 *)
  0x2f0c5795;       (* arm_SLI_VEC Q21 Q28 4 64 8 *)
  0x0e212842;       (* arm_XTN Q2 Q2 8 *)
  0x2f0c5763;       (* arm_SLI_VEC Q3 Q27 4 64 8 *)
  0x0e212b34;       (* arm_XTN Q20 Q25 8 *)
  0x0c9f4014;       (* arm_ST3 [Q20; Q21; Q22] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0x0c9f4002;       (* arm_ST3 [Q2; Q3; Q4] X0 (Postimmediate_Offset (word 24)) 64 8 *)
  0xd65f03c0        (* arm_RET X30 *)
];;

(* The code begins with the BTI landing pad (bti c). As for x86 IBT, the     *)
(* proofs are about the trimmed code without it, which is also the code of a *)
(* -DNO_IBT build, and the subroutine theorems for the full code are derived *)
(* from them by ARM_ADD_IBT_RULE.                                            *)

let mlkem_tobytes_alt_tmc =
  define_trimmed "mlkem_tobytes_alt_tmc" mlkem_tobytes_alt_mc;;

let MLKEM_TOBYTES_ALT_EXEC = ARM_MK_EXEC_RULE mlkem_tobytes_alt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Main proof.                                                               *)
(* ------------------------------------------------------------------------- *)

let lemma =
  let th = (GEN_REWRITE_CONV I [word_interleave] THENC
            ONCE_DEPTH_CONV LENGTH_CONV THENC let_CONV)
           `word_interleave 8 [x:int64; y; z]:192 word` in
  let th' = REWRITE_RULE[WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; IN_ELIM_THM;
             DIMINDEX_CONV `dimindex(:192)`; LET_DEF; LET_END_DEF] th in
  CONV_RULE(EXPAND_CASES_CONV THENC
            DEPTH_CONV (NUM_RED_CONV ORELSEC EL_CONV)) th';;

let MLKEM_TOBYTES_ALT_CORRECT = prove
 (`!r a (l:int16 list) pc.
        ALL (nonoverlapping (r,384)) [(word pc,0x108); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_tobytes_alt_tmc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = word(pc + 0x104) /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `l:int16 list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Globalize the LENGTH l = 256 hypothesis ***)

  ASM_CASES_TAC `LENGTH(l:int16 list) = 256` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0";
    ARM_QUICKSIM_TAC MLKEM_TOBYTES_ALT_EXEC
     [`read X0 s = a`; `read X1 s = z`; `read X2 s = i`] (1--175)] THEN

  (*** Digitize and tweak the input digits to match 128-bit load size  ****)

  UNDISCH_TAC
   `read(memory :> bytes(a,512)) s0 = num_of_wordlist(l:int16 list)` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
   [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV LIST_OF_SEQ_CONV))) THEN
  REWRITE_TAC[] THEN
  REPLICATE_TAC 3
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [GSYM NUM_OF_PAIR_WORDLIST]) THEN
  REWRITE_TAC[pair_wordlist] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV) THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES] THEN STRIP_TAC THEN

  (*** Unroll and simulate to the end ***)

  MAP_EVERY (fun n ->
    ARM_STEPS_TAC MLKEM_TOBYTES_ALT_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
   (1--175) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Now fiddle round to make things match up nicely ***)

  REWRITE_TAC[ARITH_RULE `384 = 8 * 48`] THEN
  CONV_TAC(LAND_CONV BIGNUM_LEXPAND_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (funpow 3 RAND_CONV) [GSYM LIST_OF_SEQ_EQ_SELF] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(funpow 3 RAND_CONV (LIST_OF_SEQ_CONV)) THEN
  REWRITE_TAC[MAP] THEN
  REWRITE_TAC[num_of_wordlist; VAL] THEN

  (*** Now more or less brute-force except avoid creating big numbers ***)

  REWRITE_TAC[bignum_of_wordlist; VAL] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV
   (BIT_WORD_CONV ORELSEC
    GEN_REWRITE_CONV I [lemma] ORELSEC
    GEN_REWRITE_CONV I [BITVAL_CLAUSES; OR_CLAUSES; AND_CLAUSES])) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  ABBREV_TAC `twae = &2:real` THEN REAL_ARITH_TAC);;

let MLKEM_TOBYTES_ALT_NOIBT_SUBROUTINE_CORRECT = prove
 (`!r a (l:int16 list) pc returnaddress.
        ALL (nonoverlapping (r,384)) [(word pc,0x108); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_tobytes_alt_tmc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_TOBYTES_ALT_EXEC
   MLKEM_TOBYTES_ALT_CORRECT);;

(* The same for the full code, with its BTI landing pad. *)

let MLKEM_TOBYTES_ALT_SUBROUTINE_CORRECT = prove
 (`!r a (l:int16 list) pc returnaddress.
        ALL (nonoverlapping (r,384)) [(word pc,0x10c); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_tobytes_alt_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 256
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_tobytes_alt_mc mlkem_tobytes_alt_tmc
    MLKEM_TOBYTES_ALT_NOIBT_SUBROUTINE_CORRECT));;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_tobytes_alt" subroutine_signatures)
    MLKEM_TOBYTES_ALT_NOIBT_SUBROUTINE_CORRECT
    MLKEM_TOBYTES_ALT_EXEC;;

let MLKEM_TOBYTES_ALT_NOIBT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,384)) [word pc,0x108; a,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_tobytes_alt_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,384] [r,384])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_TOBYTES_ALT_EXEC);;

(* The same for the full code, with its BTI landing pad. *)

let MLKEM_TOBYTES_ALT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,384)) [word pc,0x10c; a,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_tobytes_alt_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a r pc returnaddress /\
                        memaccess_inbounds e2 [a,512; r,384] [r,384])
               (\s s'. true)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_tobytes_alt_mc mlkem_tobytes_alt_tmc
    MLKEM_TOBYTES_ALT_NOIBT_SUBROUTINE_SAFE));;
