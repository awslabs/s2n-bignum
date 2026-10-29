(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* XOR of bytes into a Keccak state. This is the code for                    *)
(* mlkem_keccakf1600_xor_bytes from mlkem-native's portable C implementation *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which XORs len  *)
(* bytes of data into the 200-byte state starting at byte off. It is         *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x2c90.                                            *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2c90: mov     w2, w2
    2c94: cbz     w3, 2cc4 <mlkem_keccakf1600_xor_bytes+0x34>
    2c98: mov     w5, w3
    2c9c: add     x3, x0, x2
    2ca0: mov     x0, #0x0
    2ca4: nop
    2ca8: ldrb    w2, [x3, x0]
    2cac: ldrb    w4, [x1, x0]
    2cb0: eor     w2, w2, w4
    2cb4: strb    w2, [x3, x0]
    2cb8: add     x0, x0, #0x1
    2cbc: cmp     x5, x0
    2cc0: b.ne    2ca8 <mlkem_keccakf1600_xor_bytes+0x18>
    2cc4: ret
 ***)

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2c90,0x2cc8];;

(*** The zero-extended arguments off and len, and the test of len ***)

let XOR_BYTES_ARGS_TAC =
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  FIRST_ASSUM(fun th ->
    if concl th <> `~(len = 0)` then NO_TAC else
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = concl th then th' else REWRITE_RULE[th] th'));;

(* ------------------------------------------------------------------------- *)
(* The state after i of the bytes of the data m have been XORed into it, as  *)
(* bytes. Only byte off + i changes in the next step.                        *)
(* ------------------------------------------------------------------------- *)

let BYTE_UPDATE = prove
 (`!x c k j.
        x < 2 EXP (8 * k) /\ c < 256
        ==> ((x + 2 EXP (8 * k) * c) DIV 2 EXP (8 * j)) MOD 256 =
            if j = k then c else (x DIV 2 EXP (8 * j)) MOD 256`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES; MOD_LT];
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `~(j = k) ==> j < k \/ k < j`))] THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[LT_EXISTS]) THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; LEFT_ADD_DISTRIB; EXP_ADD] THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    SIMP_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `256 * y + z = y * 256 + z`] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    SUBGOAL_THEN `x + 2 EXP (8 * k) * c < 2 EXP (8 * j) /\ x < 2 EXP (8 * j)`
     (fun th -> SIMP_TAC[th; DIV_LT; MOD_0]) THEN
    SUBGOAL_THEN `2 EXP (8 * k) * 256 <= 2 EXP (8 * j)` MP_TAC THENL
     [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_ADD; LE_EXP] THEN
      ASM_ARITH_TAC;
      UNDISCH_TAC `c < 256` THEN UNDISCH_TAC `x < 2 EXP (8 * k)` THEN
      SPEC_TAC(`2 EXP (8 * j)`,`q:num`) THEN
      SPEC_TAC(`2 EXP (8 * k)`,`p:num`) THEN
      REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `x + p * c < p * 256` MP_TAC THENL
       [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `p + p * c` THEN
        ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
        REWRITE_TAC[ARITH_RULE `p + p * c = p * (c + 1)`; LE_MULT_LCANCEL] THEN
        ASM_ARITH_TAC;
        MP_TAC(SPECL [`p:num`; `c:num`] LE_MULT_LCANCEL) THEN
        ASM_ARITH_TAC]]]);;

let XOR_BYTES_STEP = prove
 (`!(S:1600 word) m off i j.
        off + i < 200 /\ j < 200
        ==> word_subword
             (word_xor S (word(2 EXP (8 * off) *
                               m MOD 2 EXP (8 * (i + 1)))))
             (8 * j,8):byte =
            if j = off + i
            then word_xor
                  (word_subword
                    (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                    (8 * j,8))
                  (word((m DIV 2 EXP (8 * i)) MOD 256))
            else word_subword
                  (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                  (8 * j,8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
   `2 EXP (8 * off) * m MOD 2 EXP (8 * (i + 1)) =
    2 EXP (8 * off) * m MOD 2 EXP (8 * i) +
    2 EXP (8 * (off + i)) * (m DIV 2 EXP (8 * i)) MOD 256`
  SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES;
                ARITH_RULE `2 EXP 8 = 256`; MOD_MULT_MOD] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUBWORD_WORD; DIMINDEX_CONV `dimindex(:1600)`;
               DIMINDEX_8; ARITH_RULE `j < 200 ==> 8 * j + 8 <= 1600`] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) BYTE_UPDATE o
    rand o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; LT_MULT_LCANCEL] THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SUBGOAL_THEN `2 EXP (8 * off) * m MOD 2 EXP (8 * i) < 2 EXP (8 * (off + i))`
   (fun th -> SIMP_TAC[th; DIV_LT; MOD_0; WORD_XOR_0]) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; LT_MULT_LCANCEL] THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

(*** The invariant for the bytes other than byte t ***)

let XOR_BYTES_RESTRICT_RULE t th =
  let j,bod = dest_forall(concl th) in
  let p,q = dest_imp bod in
  let p' = mk_conj(p,mk_neg(mk_eq(j,t))) in
  GEN j (DISCH p' (MP (SPEC j th) (CONJUNCT1(ASSUME p'))));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As in keccak_absorb in common/fips202.ml, the state is *)
(* a 1600-bit word S. The len bytes of data, as a number m, are XORed into   *)
(* it starting at byte off, giving word_xor S (word(2 EXP (8 * off) * m)).   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!a d off len (S:1600 word) m pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (a,200)) [(word pc,0x6480); (d,len)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2c90) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read (memory :> wbytes a) s = S /\
                  read (memory :> bytes(d,len)) s = m)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s =
                  word_xor S (word(2 EXP (8 * off) * m)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,200)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `S:1600 word`; `m:num`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; READ_MEMORY_WBYTES_VAL] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The case len = 0, where m = 0 and nothing is done ***)

  ASM_CASES_TAC `len = 0` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC
     (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      `read (memory :> bytes (d,0)) s = m`) o concl)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_XOR_0];
    ALL_TAC] THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `len:num` `pc + 0x2ca8` `pc + 0x2cbc`
   `\i s. read X0 s = word i /\ read X1 s = d /\ read X5 s = word len /\
          read X3 s = word_add a (word off) /\
          read X30 s = returnaddress /\
          read (memory :> bytes(d,len)) s = m /\
          !j. j < 200
              ==> read (memory :> bytes8(word_add a (word j))) s =
                  word_subword
                   (word_xor (S:1600 word)
                     (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                   (8 * j,8)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization, with the bytes of the state ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC
     (1--2) THEN
    XOR_BYTES_ARGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC
     (3--6) THEN
    ARGS_32_TAC [`off:num`; `len:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; WORD_XOR_0; word_subword] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES8_OF_NUM THEN
    EXISTS_TAC `200` THEN ASM_REWRITE_TAC[];

    (*** The loop body, for byte off + i of the state ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `off + i < 200` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `bytes8` (concl th) then
        ASSUME_TAC(MP (SPEC `off + i` th) (ASSUME `off + i < 200`)) THEN
        ASSUME_TAC(XOR_BYTES_RESTRICT_RULE `off + i` th)
      else failwith "XOR_BYTES_RESTRICT_RULE") THEN
    MP_TAC(SPECL [`d:int64`; `len:num`; `m:num`; `i:num`; `s0:armstate`]
                 READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC
     (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[XOR_BYTES_STEP] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    W(fun (_,w) -> SPEC_TAC(lhand(rand w),`b1:byte`) THEN
                   SPEC_TAC(rand(rand w),`b2:byte`)) THEN
    REPEAT GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC
     (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC
     (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return, with the whole state ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC
     (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC
     (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `m MOD 2 EXP (8 * len) = m`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC MOD_LT THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
        `read (memory :> bytes (d,len)) s = m`) o concl)) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
      ALL_TAC] THEN
    W(fun (_,w) -> MP_TAC(ISPEC (rand(rand w)) VAL_BOUND)) THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    DISCH_THEN(fun th -> SUBST1_TAC(SYM(MATCH_MP MOD_LT th))) THEN
    REWRITE_TAC[ARITH_RULE `1600 = 8 * 200`] THEN
    MATCH_MP_TAC READ_MEMORY_BYTES_OF_BYTES8 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[word_subword; ARITH_RULE `2 EXP 8 = 256`]) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend on off as well   *)
(* as len, so the theorem is stated directly rather than by mk_safety_spec.  *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e a d off len pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (a,200)) [word pc,0x6480; d,len]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x2c90) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc returnaddress /\
                         memaccess_inbounds e2 [a,200; d,len] [a,200]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (a,200)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (d:int64) (off:num) (len:num) (pc:num)
      (returnaddress:int64).
      if len = 0 then f_ev_len0 a d off len pc returnaddress
      else
        APPEND
          (f_ev_epil a d off len pc returnaddress)
          (APPEND
            (ENUMERATEL len (\i. f_ev_loop a d off len pc returnaddress i))
            (f_ev_prol a d off len pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[] THENL
   [ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC (1--3) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + 0x2ca8` `pc + 0x2cc4`
    `\i s. read X30 s = returnaddress /\
           read X0 s = word i /\ read X1 s = d /\ read X5 s = word len /\
           read X3 s = word_add a (word off)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC
     (1--2) THEN
    XOR_BYTES_ARGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC
     (3--6) THEN
    ARGS_32_TAC [`off:num`; `len:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(val(word_sub (word len) (word_add (word i) (word 1)):int64) = 0) <=>
    i + 1 < len`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `len < 2 EXP 64 /\ i + 1 < 2 EXP 64` MP_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
