(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mld_keccak_absorb_once_x4 (see                              *)
(* keccak_absorb_once_x4_spec.ml): that of the same code in the x86 proofs   *)
(* of mlkem-native (mlkem_native_keccak_absorb_once_x4_gcc12_O2.ml), with    *)
(* the names changed.                                                        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/keccak_absorb_once_x4_spec.ml";;
needs "x86/proofs/utils/keccak_fips202.ml";;
needs "x86/proofs/utils/mldsa_native_absorb.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The four states zero at the start, as 200 bytes each.                     *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_ZERO_SPLIT = prove
 (`!a:int64 m n s:x86state.
        read (memory :> bytes(a,m + n)) s = 0 <=>
        read (memory :> bytes(a,m)) s = 0 /\
        read (memory :> bytes(word_add a (word m),n)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let BYTES800_ZERO = prove
 (`!a:int64 s:x86state.
        read (memory :> bytes(a,800)) s = 0
        ==> read (memory :> bytes(a,200)) s = 0 /\
            read (memory :> bytes(word_add a (word 200),200)) s = 0 /\
            read (memory :> bytes(word_add a (word 400),200)) s = 0 /\
            read (memory :> bytes(word_add a (word 600),200)) s = 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `800 = 200 + 600`; READ_MEMORY_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `600 = 200 + 400`; READ_MEMORY_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `400 = 200 + 200`; READ_MEMORY_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the calls, which act on all four states, and for the padding  *)
(* byte on the stack, which is used for all four. The messages are read in   *)
(* blocks as for absorbing on one state, and the four lanes of the result    *)
(* are proved in the same way.                                               *)
(* ------------------------------------------------------------------------- *)

let ABSX4_STATES_TAC =
  MAP_EVERY KECCAK_STATE_AT_TAC
   [`st:int64`; `word_add (st:int64) (word 200)`;
    `word_add (st:int64) (word 400)`; `word_add (st:int64) (word 600)`];;

let ABSX4_STATES_THEN (ttac:term->term->term->term->tactic) =
  KECCAK_STATE_THEN `st:int64` (fun v0 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 200)` (fun v1 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 400)` (fun v2 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 600)` (fun v3 ->
    ttac v0 v1 v2 v3))));;

let ABSX4_MBOUND_TAC =
  MAP_EVERY (fun mm ->
    SUBGOAL_THEN (subst [mm,`M:num`] `M < 2 EXP (8 * mlen)`) ASSUME_TAC THENL
     [FIRST_ASSUM(fun th ->
        let c = concl th in
        if is_eq c && rand c = mm &&
           can (term_match [`mlen:num`]
                 `read (memory :> bytes (m,mlen)) s = x`) c
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
      ALL_TAC])
   [`M0:num`; `M1:num`; `M2:num`; `M3:num`];;

let ABSX4_LASTBLOCK_TAC =
  MAP_EVERY (fun (pp,mm,pn) ->
    SUBGOAL_THEN
     (subst [pp,`P:num`; mm,`M:num`]
       `(P DIV 2 EXP (8 * r * q)) MOD 2 EXP (8 * r) =
        M DIV 2 EXP (8 * r * q) +
        2 EXP (8 * t) * num_of_bytelist(keccak_pad r 31 mlen)`)
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC [pn; "q"; "t"] THEN
      MATCH_MP_TAC KECCAK_BLOCK_LAST THEN
      ASM_SIMP_TAC[KECCAK_PAD_BOUND; ARITH_RULE `31 < 128`];
      ALL_TAC])
   [`P0:num`,`M0:num`,"P0"; `P1:num`,`M1:num`,"P1";
    `P2:num`,`M2:num`,"P2"; `P3:num`,`M3:num`,"P3"];;

let ABSX4_BYTE_FACT_TAC sname n =
  let s = mk_var(sname,`:x86state`) in
  SUBGOAL_THEN
   (subst [s,`s:x86state`; n,`n:num`]
     `read (memory :> bytes (word_add stackpointer (word 327),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let ABSX4_T0_LANE_TAC =
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_SIMP_TAC[MOD_MULT; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES; SUB_0] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `0 = r - 1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV);
    MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
    TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `~(0 = r - 1)` THEN
      ARITH_TAC]];;

let ABSX4_B_LANE_TAC =
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];;

let ABSX4_C_LANE_TAC =
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP] THEN
  SUBGOAL_THEN
   `2 EXP (8 * (r - 1)) = 2 EXP (8 * t) * 2 EXP (8 * (r - t - 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `t < r` THEN ARITH_TAC;
    ALL_TAC] THEN
  W(fun (_,w) -> MP_TAC(ISPECL
    [`2 EXP (8 * t) * 31`; `128`; `8 * t + 8 * (r - t - 1)`]
    (INST_TYPE [`:1600`,`:N`] WORD_XOR_DISJOINT_ADD))) THEN
  REWRITE_TAC[EXP_ADD] THEN ANTS_TAC THENL
   [REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `~(r - 1 = t)` THEN
      UNDISCH_TAC `t < r` THEN ARITH_TAC];
    REWRITE_TAC[GSYM MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];;

(*** The flag ZF of the comparison of r - 1 with t, as r - 1 = t ***)

let ABSX4_ZF_TAC =
  ARGS_32_TAC [`r - 1`] THEN
  SUBGOAL_THEN `val(word(r - 1):int64) = r - 1` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if free_in `ZF` (concl th) && is_iff (concl th)
    then ASSUME_TAC(REWRITE_RULE[VAL_WORD_SUB_EQ_0;
           ASSUME `val(word t:int64) = t`;
           ASSUME `val(word(r - 1):int64) = r - 1`] th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the events, as for absorbing on one state. The seventh        *)
(* argument of each call of mldsa_keccakf1600x4_xor_bytes is put in the form *)
(* that it reads by STACK_ARG32_TAC.                                         *)
(* ------------------------------------------------------------------------- *)

(*** The abbreviations q and t in the last block expanded ***)

let ABSX4_UNABBREV_TAC =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `mlen DIV r = q` || c = `mlen MOD r = t` then SYM th
      else failwith "") asl in
    if ths = [] then ALL_TAC else REWRITE_TAC ths);;

(*** EXISTS_E2_TAC, also allowing the event functions f_ev_... ***)

let ABSX4_EXISTS_E2_TAC allowed_vars_e =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  ABSX4_UNABBREV_TAC THEN
  ((MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL [
    REFL_TAC;
    SAFE_UNIFY_REFL_TAC allowed_vars_e pfx
  ]) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV CONS_TO_APPEND_CONV)) THEN
   TRY (GEN_REWRITE_TAC LAND_CONV [APPEND_ASSOC]) THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e pfx) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [APPEND_ASSOC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e pfx));;

(*** DISCHARGE_SAFETY_PROPERTY_TAC, also when the events for the last  ***)
(*** block are already known from the case of a short message          ***)

let ABSX4_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W (fun (asl,w) ->
    (if is_conj w then
      (CONJ_TAC THENL
        [FULL_UNIFY_F_EVENTS_TAC ORELSE
         (REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC);
         ALL_TAC])
     else ALL_TAC) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let ABSX4_SAFE_VARS =
  [`pc:num`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`; `st:int64`;
   `r:num`; `mlen:num`; `stackpointer:int64`; `returnaddress:int64`];;

let ABSX4_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_gcc12_O2_mc,
       MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC,
       0x0,mldsa_native_libmldsa_gcc12_O2_mc,safety_th)
      ilist n THENL
     [ABSX4_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, as for absorbing on one     *)
(* state. The four states must be zero at the start, and each is then the    *)
(* state after absorbing the corresponding message, with the first byte 0x1F *)
(* of the padding, as for SHAKE, before the last permutation. The stack is   *)
(* the 88 bytes of the function, 16 bytes for the seventh argument of the    *)
(* calls, their return address and the 272 bytes used by                     *)
(* mldsa_keccakf1600x4_permute below that, 384 bytes in all, and the seventh *)
(* argument above the return address is read. The events depend only on the  *)
(* addresses and the lengths.                                                *)
(* ------------------------------------------------------------------------- *)

let ABSX4_CS_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m0:int64) (m1:int64) (m2:int64) (m3:int64) (st:int64) (r:num)
      (mlen:num) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND
       (if mlen MOD r = 0
        then f_ev_t0 m0 m1 m2 m3 st r mlen pc stackpointer returnaddress
        else if mlen MOD r = r - 1
        then f_ev_t1 m0 m1 m2 m3 st r mlen pc stackpointer returnaddress
        else f_ev_t2 m0 m1 m2 m3 st r mlen pc stackpointer returnaddress)
       (if mlen < r
        then f_ev_short m0 m1 m2 m3 st r mlen pc stackpointer returnaddress
        else APPEND
              (f_ev_epil m0 m1 m2 m3 st r mlen pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV r)
                  (\i. f_ev_loop m0 m1 m2 m3 st r mlen pc stackpointer
                                 returnaddress i))
                (f_ev_prol m0 m1 m2 m3 st r mlen pc stackpointer
                           returnaddress)))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `800 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun (p,m) ->
    ABBREV_TAC (subst [p,`P:num`; m,`M:num`]
     `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r 0x1F mlen)`))
   [`P0:num`,`M0:num`; `P1:num`,`M1:num`; `P2:num`,`M2:num`;
    `P3:num`,`M3:num`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

let ABSX4_CS_FRAME =
 `read R14 s = st /\ read RBX s = word r /\
  read RSP s = word_add stackpointer (word 296) /\
  read (memory :> bytes64 (word_add stackpointer (word 336))) s = rbx_init /\
  read (memory :> bytes64 (word_add stackpointer (word 344))) s = rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 352))) s = r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 360))) s = r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 368))) s = r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 376))) s = r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 384))) s =
  returnaddress /\
  read (memory :> bytes32 (word_add stackpointer (word 308))) s =
  word_zx(word r:int64) /\
  read (memory :> bytes8 (word_add stackpointer (word 327))) s = word 31 /\
  read (memory :> bytes(m0,mlen)) s = M0 /\
  read (memory :> bytes(m1,mlen)) s = M1 /\
  read (memory :> bytes(m2,mlen)) s = M2 /\
  read (memory :> bytes(m3,mlen)) s = M3`;;

let ABSX4_CS_MID = mk_abs(`s:x86state`,list_mk_conj
 [`read RBP s = word(mlen MOD r)`;
  `read R12 s = word_add m0 (word(r * mlen DIV r))`;
  `read R13 s = word_add m1 (word(r * mlen DIV r))`;
  `read R15 s = word_add m2 (word(r * mlen DIV r))`;
  `read R8 s = word_add m3 (word(r * mlen DIV r))`; ABSX4_CS_FRAME;
  `read (memory :> bytes(st,200)) s = val(keccak_absorb r P0 (mlen DIV r))`;
  `read (memory :> bytes(word_add st (word 200),200)) s =
   val(keccak_absorb r P1 (mlen DIV r))`;
  `read (memory :> bytes(word_add st (word 400),200)) s =
   val(keccak_absorb r P2 (mlen DIV r))`;
  `read (memory :> bytes(word_add st (word 600),200)) s =
   val(keccak_absorb r P3 (mlen DIV r))`]);;

let ABSX4_CS_INV = list_mk_abs([`k:num`; `s:x86state`],list_mk_conj
 [`read RBP s = word(mlen - r * k)`;
  `read R12 s = word_add m0 (word(r * k))`;
  `read R13 s = word_add m1 (word(r * k))`;
  `read R15 s = word_add m2 (word(r * k))`;
  `read R8 s = word_add m3 (word(r * k))`; ABSX4_CS_FRAME;
  `read (memory :> bytes(st,200)) s = val(keccak_absorb r P0 k)`;
  `read (memory :> bytes(word_add st (word 200),200)) s =
   val(keccak_absorb r P1 k)`;
  `read (memory :> bytes(word_add st (word 400),200)) s =
   val(keccak_absorb r P2 k)`;
  `read (memory :> bytes(word_add st (word 600),200)) s =
   val(keccak_absorb r P3 k)`]);;

let ABSX4_CS_XOR_TAC off len ms vars n =
  TRY(STACK_ARG32_TAC `word_add stackpointer (word 280):int64`) THEN
  ABSX4_STATES_TAC THEN
  ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
    ABSX4_CALL_TAC "H_XOR"
     ([`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
       `read RCX s`; `read R8 s`; off; len; v0; v1; v2; v3] @ ms @
      [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
     vars n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let ABSX4_CS_EVENTS_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV r = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD r = t`))) THEN
  ABSX4_DISCHARGE_TAC;;

let ABSX4_CS_LANES_TAC pre lane =
  MAP_EVERY (fun _ -> CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) && rhs(concl th) = `mlen:num` &&
                       is_binary "+" (lhs(concl th)))) THEN
    pre THEN lane;
    ALL_TAC]) (1--4) THEN
  ABSX4_CS_EVENTS_TAC;;

let ABSX4_CS_SHORT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BYTES800_ZERO o check
   (can (term_match []
     `read (memory :> bytes(st,800)) s = 0`) o concl)) THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (1--16) THEN
  ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (17--18) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let ABSX4_CS_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r`
   `pc + mld_keccak_absorb_once_x4_loop1`
   `pc + mld_keccak_absorb_once_x4_loop1_exit`
    ABSX4_CS_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];

    (*** Initialization of the loop, with the states zero ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BYTES800_ZERO o check
     (can (term_match []
       `read (memory :> bytes(st,800)) s = 0`) o concl)) THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (1--16) THEN
    ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (17--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body: XOR in a block of each message, permute, and the
     *** loop test
     ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY (fun (m,mm) ->
      MP_TAC(SPECL [m; `mlen:num`; mm; `r * i`; `r:num`; `s0:x86state`]
                   READ_MEMORY_BYTES_SUB) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC)
     [`m0:int64`,`M0:num`; `m1:int64`,`M1:num`; `m2:int64`,`M2:num`;
      `m3:int64`,`M3:num`] THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (1--14) THEN
    ARGS_32_TAC [`r:num`] THEN
    ABSX4_CS_XOR_TAC `0` `r:num`
     [`(M0 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
      `(M1 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
      `(M2 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`;
      `(M3 DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`]
     (ABSX4_SAFE_VARS @ [`i:num`]) 15 THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (16--17) THEN
    ABSX4_STATES_TAC THEN
    ABSX4_STATES_THEN (fun v0 v1 v2 v3 ->
      ABSX4_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read RDI s`; v0; v1; v2; v3; `pc:num`;
         `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
        (ABSX4_SAFE_VARS @ [`i:num`]) 18) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    SUBGOAL_THEN `word_sub (word (mlen - r * i)) (word r):int64 =
                  word(mlen - r * (i + 1))` SUBST_ALL_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
      ANTS_TAC THENL [UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
                      DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (19--23) THEN
    SUBGOAL_THEN
     `val(word(mlen - r * (i + 1)):int64) = mlen - r * (i + 1) /\
      val(word r:int64) = r`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC [24] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_LOOP_TEST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
      ALL_TAC]) (1--4) THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[MULT_CLAUSES; EXP] THEN
      MAP_EVERY (fun v -> TRY(EXPAND_TAC v)) ["P0"; "P1"; "P2"; "P3"] THEN
      CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
      MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
      UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
      ALL_TAC]) (1--4) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop exit ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let ABSX4_CS_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
  SUBGOAL_THEN `r * q + t = mlen /\ t < r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ABSX4_MBOUND_TAC THEN ABSX4_LASTBLOCK_TAC THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (1--1) THEN
  ARGS_32_TAC [`r:num`] THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (2--3) THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (4--4) THEN
  ARGS_32_TAC [`t:num`] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [(*** A whole number of blocks: 0x1F at byte 0 and 128 at byte r - 1 ***)

    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (5--16) THEN
    ARGS_32_TAC [`t:num`] THEN
    ABSX4_BYTE_FACT_TAC "s16" `31` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_CS_XOR_TAC `t:num` `1` [`31`; `31`; `31`; `31`]
      ABSX4_SAFE_VARS 17 THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (18--26) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSX4_BYTE_FACT_TAC "s26" `128` THEN
    ABSX4_CS_XOR_TAC `r - 1` `1` [`128`; `128`; `128`; `128`]
      ABSX4_SAFE_VARS 27 THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (28--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ABSX4_CS_LANES_TAC
     (SUBGOAL_THEN
       `!M. M < 2 EXP (8 * (r * q + t)) ==> M DIV 2 EXP (8 * r * q) = 0`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_LT THEN
        UNDISCH_TAC `M < 2 EXP (8 * (r * q + t))` THEN
        ASM_REWRITE_TAC[ADD_CLAUSES];
        ALL_TAC])
     ABSX4_T0_LANE_TAC;
    ALL_TAC] THEN

  (*** Otherwise, first the t bytes of each message after its blocks ***)

  SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (m,mm) ->
    SUBGOAL_THEN
     (subst [mm,`M:num`] `M DIV 2 EXP (8 * r * q) < 2 EXP (8 * t)`)
    ASSUME_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
      FIRST_ASSUM(SUBST1_TAC o
        check (fun th -> concl th = `r * q + t = mlen`)) THEN
      FIRST_X_ASSUM(fun th -> if concl th = subst [mm,`M:num`]
        `M < 2 EXP (8 * mlen)` then ACCEPT_TAC th else NO_TAC);
      ALL_TAC] THEN
    MP_TAC(SPECL [m; `mlen:num`; mm; `r * q`; `t:num`; `s4:x86state`]
                 READ_MEMORY_BYTES_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC)
   [`m0:int64`,`M0:num`; `m1:int64`,`M1:num`; `m2:int64`,`M2:num`;
    `m3:int64`,`M3:num`] THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (5--14) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSX4_CS_XOR_TAC `0` `t:num`
   [`M0 DIV 2 EXP (8 * r * q)`; `M1 DIV 2 EXP (8 * r * q)`;
    `M2 DIV 2 EXP (8 * r * q)`; `M3 DIV 2 EXP (8 * r * q)`]
   ABSX4_SAFE_VARS 15 THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (16--16) THEN
  ARGS_32_TAC [`r - 1`] THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (17--19) THEN
  ABSX4_ZF_TAC THEN
  ABSORB_CASE_FLAG_TAC `r - 1 = t` THENL
   [(*** The padding is just the single byte 0x9F at byte r - 1 ***)

    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> concl th = `r - 1 = t`)) THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (20--30) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSX4_BYTE_FACT_TAC "s30" `159` THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_CS_XOR_TAC `r - 1` `1` [`159`; `159`; `159`; `159`]
      ABSX4_SAFE_VARS 31 THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (32--41) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ABSX4_CS_LANES_TAC
     (SUBGOAL_THEN `(r * q + r - 1) MOD r = r - 1` ASSUME_TAC THENL
       [SUBGOAL_THEN `r * q + r - 1 = q * r + (r - 1)` SUBST1_TAC THENL
         [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT; ARITH_RULE `0 < r ==> r - 1 < r`];
        ALL_TAC])
     ABSX4_B_LANE_TAC;

    (*** Otherwise 0x1F at byte t and 128 at byte r - 1 ***)

    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (20--30) THEN
    ARGS_32_TAC [`t:num`] THEN
    ABSX4_BYTE_FACT_TAC "s30" `31` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_CS_XOR_TAC `t:num` `1` [`31`; `31`; `31`; `31`]
      ABSX4_SAFE_VARS 31 THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (32--40) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSX4_BYTE_FACT_TAC "s40" `128` THEN
    ABSX4_CS_XOR_TAC `r - 1` `1` [`128`; `128`; `128`; `128`]
      ABSX4_SAFE_VARS 41 THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (42--51) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ABSX4_CS_LANES_TAC
     (SUBGOAL_THEN `(r * q + t) MOD r = t` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
        ALL_TAC])
     ABSX4_C_LANE_TAC];;

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ABSX4_CS_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mld_keccak_absorb_once_x4_loop1_exit` ABSX4_CS_MID THEN CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [ABSX4_CS_SHORT_TAC; ABSX4_CS_LOOP_TAC];
    ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THEN
    ABSX4_CS_TAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, derived from the above.                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, which do not need the states to be *)
(* zero at the start, so are proved separately (as for mlkem-native), with   *)
(* the events in the same parts as above.                                    *)
(* ------------------------------------------------------------------------- *)

let ABSX4_SAFE_XOR_TAC off len vars n =
  TRY(STACK_ARG32_TAC `word_add stackpointer (word 280):int64`) THEN
  ABSX4_CALL_TAC "H_XOR"
    [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
     `read RCX s`; `read R8 s`; off; len; `pc:num`; `read RSP s`;
     `read (memory :> bytes64(read RSP s)) s`] vars n;;

let ABSX4_SAFE_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV r = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD r = t`))) THEN
  ABSX4_DISCHARGE_TAC;;

let ABSX4_SAFE_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
  SUBGOAL_THEN `r * q + t = mlen /\ t < r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (1--1) THEN
  ARGS_32_TAC [`r:num`] THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (2--3) THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (4--4) THEN
  ARGS_32_TAC [`t:num`] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (5--16) THEN
    ARGS_32_TAC [`t:num`] THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_SAFE_XOR_TAC `t:num` `1` ABSX4_SAFE_VARS 17 THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (18--26) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSX4_SAFE_XOR_TAC `r - 1` `1` ABSX4_SAFE_VARS 27 THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (28--37) THEN
    ABSX4_SAFE_FINAL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (5--14) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSX4_SAFE_XOR_TAC `0` `t:num` ABSX4_SAFE_VARS 15 THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (16--16) THEN
  ARGS_32_TAC [`r - 1`] THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC (17--19) THEN
  ABSX4_ZF_TAC THEN
  ABSORB_CASE_FLAG_TAC `r - 1 = t` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> concl th = `r - 1 = t`)) THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (20--30) THEN
    ARGS_32_TAC [`r - 1`] THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_SAFE_XOR_TAC `r - 1` `1` ABSX4_SAFE_VARS 31 THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (32--41) THEN
    ABSX4_SAFE_FINAL_TAC;
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (20--30) THEN
    ARGS_32_TAC [`t:num`] THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ABSX4_SAFE_XOR_TAC `t:num` `1` ABSX4_SAFE_VARS 31 THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (32--40) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSX4_SAFE_XOR_TAC `r - 1` `1` ABSX4_SAFE_VARS 41 THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
     (42--51) THEN
    ABSX4_SAFE_FINAL_TAC];;

let ABSX4_SAFE_FRAME =
 `read R14 s = st /\ read RBX s = word r /\
  read RSP s = word_add stackpointer (word 296) /\
  read (memory :> bytes64 (word_add stackpointer (word 336))) s = rbx_init /\
  read (memory :> bytes64 (word_add stackpointer (word 344))) s = rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 352))) s = r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 360))) s = r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 368))) s = r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 376))) s = r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 384))) s =
  returnaddress /\
  read (memory :> bytes32 (word_add stackpointer (word 308))) s =
  word_zx(word r:int64)`;;

let ABSX4_SAFE_MID = mk_abs(`s:x86state`,list_mk_conj
 [`read RBP s = word(mlen MOD r)`;
  `read R12 s = word_add m0 (word(r * mlen DIV r))`;
  `read R13 s = word_add m1 (word(r * mlen DIV r))`;
  `read R15 s = word_add m2 (word(r * mlen DIV r))`;
  `read R8 s = word_add m3 (word(r * mlen DIV r))`; ABSX4_SAFE_FRAME]);;

let ABSX4_SAFE_INV = list_mk_abs([`k:num`; `s:x86state`],list_mk_conj
 [`read RBP s = word(mlen - r * k)`;
  `read R12 s = word_add m0 (word(r * k))`;
  `read R13 s = word_add m1 (word(r * k))`;
  `read R15 s = word_add m2 (word(r * k))`;
  `read R8 s = word_add m3 (word(r * k))`; ABSX4_SAFE_FRAME]);;

let MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m0:int64) (m1:int64) (m2:int64) (m3:int64) (st:int64) (r:num)
      (mlen:num) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND
       (if mlen MOD r = 0
        then f_ev_t0 m0 m1 m2 m3 st r mlen pc stackpointer returnaddress
        else if mlen MOD r = r - 1
        then f_ev_t1 m0 m1 m2 m3 st r mlen pc stackpointer returnaddress
        else f_ev_t2 m0 m1 m2 m3 st r mlen pc stackpointer returnaddress)
       (if mlen < r
        then f_ev_short m0 m1 m2 m3 st r mlen pc stackpointer returnaddress
        else APPEND
              (f_ev_epil m0 m1 m2 m3 st r mlen pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV r)
                  (\i. f_ev_loop m0 m1 m2 m3 st r mlen pc stackpointer
                                 returnaddress i))
                (f_ev_prol m0 m1 m2 m3 st r mlen pc stackpointer
                           returnaddress)))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `800 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mld_keccak_absorb_once_x4_loop1_exit` ABSX4_SAFE_MID THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [(*** A message shorter than a block, with no loop ***)

      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (1--16) THEN
      ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
      X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (17--18) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ALL_TAC] THEN

    (*** Otherwise the loop over the whole blocks ***)

    ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r`
   `pc + mld_keccak_absorb_once_x4_loop1`
   `pc + mld_keccak_absorb_once_x4_loop1_exit`
      ABSX4_SAFE_INV THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];

      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (1--16) THEN
      ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
      X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (17--19) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (1--14) THEN
      ARGS_32_TAC [`r:num`] THEN
      ABSX4_SAFE_XOR_TAC `0` `r:num`
        (ABSX4_SAFE_VARS @ [`i:num`]) 15 THEN
      X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (16--17) THEN
      ABSX4_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
         `read (memory :> bytes64(read RSP s)) s`]
        (ABSX4_SAFE_VARS @ [`i:num`]) 18 THEN
      SUBGOAL_THEN `word_sub (word (mlen - r * i)) (word r):int64 =
                    word(mlen - r * (i + 1))` SUBST_ALL_TAC THENL
       [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
        ANTS_TAC THENL [UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
                        DISCH_THEN SUBST1_TAC] THEN
        AP_TERM_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (19--23) THEN
      SUBGOAL_THEN
       `val(word(mlen - r * (i + 1)):int64) = mlen - r * (i + 1) /\
        val(word r:int64) = r`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
        REWRITE_TAC[DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      X86_STEPS_TAC MLDSA_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC [24] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_LOOP_TEST) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
      MAP_EVERY (fun _ -> CONJ_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
        ALL_TAC]) (1--4) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The last block ***)

    ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THEN
    ABSX4_SAFE_TAIL_TAC]);;
