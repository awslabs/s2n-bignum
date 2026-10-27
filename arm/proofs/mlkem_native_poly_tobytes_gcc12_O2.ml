(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of polynomial coefficients in 12-bit chunks to a byte array.      *)
(* This is the code for mlkem_poly_tobytes from mlkem-native's portable C    *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;

(**** print_literal_from_elf
        "arm/mlkem_native/mlkem_native_poly_tobytes_gcc12_O2.o";;
 ****)

let mlkem_native_poly_tobytes_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_poly_tobytes_gcc12_O2_mc"
  "arm/mlkem_native/mlkem_native_poly_tobytes_gcc12_O2.o"
[
  0x91060004;       (* arm_ADD X4 X0 (rvalue (word 384)) *)
  0xd503201f;       (* arm_NOP *)
  0x79c00022;       (* arm_LDRSH W2 X1 (Immediate_Offset (word 0)) *)
  0x91000c00;       (* arm_ADD X0 X0 (rvalue (word 3)) *)
  0x79400423;       (* arm_LDRH W3 X1 (Immediate_Offset (word 2)) *)
  0x91001021;       (* arm_ADD X1 X1 (rvalue (word 4)) *)
  0x381fd002;       (* arm_STRB W2 X0
                       (Immediate_Offset (word 18446744073709551613)) *)
  0xd3483c42;       (* arm_UBFM X2 X2 8 15 *)
  0x2a031042;       (* arm_ORR W2 W2 (Shiftedreg W3 LSL 4) *)
  0x53047c63;       (* arm_LSR W3 W3 4 *)
  0x381fe002;       (* arm_STRB W2 X0
                       (Immediate_Offset (word 18446744073709551614)) *)
  0x381ff003;       (* arm_STRB W3 X0
                       (Immediate_Offset (word 18446744073709551615)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54fffea1;       (* arm_BNE (word 2097108) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_poly_tobytes_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(*                                                                           *)
(* Unlike the hand-written kernel mlkem_tobytes, the C code relies on the    *)
(* coefficients being < 2^12, as stated in its contract (in fact requiring   *)
(* them to be < 3329), so this is an additional assumption here.             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_CORRECT = prove
 (`!r a (l:int16 list) pc.
        ALL (nonoverlapping (r,384)) [(word pc,0x3c); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_poly_tobytes_gcc12_O2_mc /\
                  read PC s = word pc /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = word(pc + 0x38) /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `l:int16 list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + 0x8` `pc + 0x30`
   `\i s. read X0 s = word_add r (word(3 * i)) /\
          read X1 s = word_add a (word(4 * i)) /\
          read X4 s = word_add r (word 384) /\
          read (memory :> bytes(a,512)) s = num_of_wordlist(l:int16 list) /\
          (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
           ==> read (memory :> bytes(r,3 * i)) s =
               num_of_wordlist
                (MAP word_zx (SUB_LIST(0,2 * i) l):(12 word)list))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of the end pointer ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_LIST_CLAUSES; MAP;
                num_of_wordlist; READ_MEMORY_BYTES_TRIVIAL];

    (*** The loop body, processing two coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ASM_CASES_TAC `LENGTH(l:int16 list) = 256 /\ ALL (\x. val x < 4096) l`
    THENL
     [ALL_TAC;
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`;
                  ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`a:int64`; `l:int16 list`; `256`; `2 * i`; `s0:armstate`]
       READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
    MP_TAC(SPECL [`a:int64`; `l:int16 list`; `256`; `2 * i + 1`;
                  `s0:armstate`]
       READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 256 = 512`;
                    ARITH_RULE `2 * (2 * i + 1) = 4 * i + 2`;
                    ARITH_RULE `2 * 2 * i = 4 * i`] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> 2 * i < 256 /\ 2 * i + 1 < 256`] THEN
    REPEAT STRIP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`;
                  ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN

    (*** Split the new bytes and list elements off and match them up ***)

    REWRITE_TAC[ARITH_RULE `3 * (i + 1) = ((3 * i + 1) + 1) + 1`;
                ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
    REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN
    REWRITE_TAC[ARITH_RULE `(3 * i + 1) + 1 = 3 * i + 2`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUB_LIST_0_SNOC2;
                 ARITH_RULE `i < 128 ==> 2 * i + 2 <= 256`] THEN
    REWRITE_TAC[MAP_APPEND; MAP; NUM_OF_WORDLIST_APPEND; LENGTH_MAP;
                LENGTH_SUB_LIST; num_of_wordlist] THEN
    SUBGOAL_THEN `val(EL (2 * i) (l:int16 list)) < 4096` MP_TAC THENL
     [UNDISCH_TAC `ALL (\x. val x < 4096) (l:int16 list)` THEN
      REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `2 * i`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_0] THEN CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> MIN (2 * i) 256 = 2 * i`] THEN
    REWRITE_TAC[ARITH_RULE `8 * 3 * i = 24 * i`;
                ARITH_RULE `12 * 2 * i = 24 * i`;
                ARITH_RULE `8 * (3 * i + 1) = 24 * i + 8`;
                ARITH_RULE `8 * (3 * i + 2) = 24 * i + 16`; EXP_ADD] THEN
    DISCH_TAC THEN MATCH_MP_TAC(NUM_RING
     `v0 + 2 EXP 8 * v1 + 2 EXP 16 * v2 = w0 + 2 EXP 12 * w1
      ==> ((n + a * v0) + (a * 2 EXP 8) * v1) + (a * 2 EXP 16) * v2 =
          n + a * (w0 + 2 EXP 12 * (w1 + 2 EXP 12 * 0))`) THEN

    (*** The bit-level packing of two coefficients into three bytes ***)

    UNDISCH_TAC `val(EL (2 * i) (l:int16 list)) < 4096` THEN
    SPEC_TAC(`EL (2 * i + 1) (l:int16 list)`, `t1:int16`) THEN
    SPEC_TAC(`EL (2 * i) (l:int16 list)`, `t0:int16`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add r (word 384))
                     (word_add r (word (3 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y) = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> 3 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MP th) THEN
                         STRIP_ASSUME_TAC th) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = `LENGTH(l:int16 list) = 256`)) THEN
    REWRITE_TAC[SUB_LIST_LENGTH]]);;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!r a (l:int16 list) pc returnaddress.
        ALL (nonoverlapping (r,384)) [(word pc,0x3c); (a,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_poly_tobytes_gcc12_O2_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read PC s = returnaddress /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_tobytes ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mlkem_tobytes" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,384)) [word pc,60; a,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_poly_tobytes_gcc12_O2_mc /\
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
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc returnaddress)
        (APPEND
          (ENUMERATEL 128 (\i. f_ev_loop a r pc returnaddress i))
          (f_ev_prol a r pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              fst MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + 0x8` `pc + 0x38`
    `\i s. read X30 s = returnaddress /\
           read X0 s = word_add r (word(3 * i)) /\
           read X1 s = word_add a (word(4 * i)) /\
           read X4 s = word_add r (word 384)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--2) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--12) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add r (word 384))
                   (word_add (word_add r (word (3 * i))) (word 3)):int64) =
      0) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
      word_sub x (word_add y z)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 128 ==> 3 * i + 3 < 18446744073709551616`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`;
                ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
