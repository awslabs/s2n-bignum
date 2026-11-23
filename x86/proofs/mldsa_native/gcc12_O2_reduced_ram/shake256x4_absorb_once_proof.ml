(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_shake256x4_absorb_once (see                           *)
(* shake256x4_absorb_once_spec.ml). In this build gcc has inlined            *)
(* mld_keccak_absorb_once_x4 with the rate 136 of SHAKE256, so the proof is  *)
(* that of mldsa_shake256x4_absorb_once of gcc12_O2 (the zeroing of the      *)
(* context) followed by that of mld_keccak_absorb_once_x4 of gcc12_O2        *)
(* (../gcc12_O2/keccak_absorb_once_x4_proof.ml, as for mlkem-native), with   *)
(* the rate a constant and the registers of this code.                       *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256x4_absorb_once_spec.ml";;
needs "x86/proofs/utils/keccak_fips202.ml";;
needs "x86/proofs/utils/mldsa_native_absorb.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_memset.ml";;

let SHK4_EXEC = MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The four states zeroed, as 200 bytes each.                                *)
(* ------------------------------------------------------------------------- *)

let SHK4_BYTES_ZERO_SPLIT = prove
 (`!a:int64 m n s:x86state.
        read (memory :> bytes(a,m + n)) s = 0 <=>
        read (memory :> bytes(a,m)) s = 0 /\
        read (memory :> bytes(word_add a (word m),n)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let SHK4_BYTES800_ZERO = prove
 (`!a:int64 s:x86state.
        read (memory :> bytes(a,800)) s = 0
        ==> read (memory :> bytes(a,200)) s = 0 /\
            read (memory :> bytes(word_add a (word 200),200)) s = 0 /\
            read (memory :> bytes(word_add a (word 400),200)) s = 0 /\
            read (memory :> bytes(word_add a (word 600),200)) s = 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `800 = 200 + 600`; SHK4_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `600 = 200 + 400`; SHK4_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `400 = 200 + 200`; SHK4_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The tests of the code on the remaining length x, against 135: x > 135 for *)
(* another block and x <= 135 for none.                                      *)
(* ------------------------------------------------------------------------- *)

let SHK4_GT135 = prove
 (`!x. ~(x < 135) /\ ~(x = 135) <=> 136 <= x`,
  ARITH_TAC);;

let SHK4_LE135 = prove
 (`!x. x < 135 \/ x = 135 <=> x < 136`,
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the calls, which act on all four states, and for the padding  *)
(* byte on the stack, which is used for all four, as for                     *)
(* mld_keccak_absorb_once_x4 of gcc12_O2 with the rate 136.                  *)
(* ------------------------------------------------------------------------- *)

let SHK4_STATES_TAC =
  MAP_EVERY KECCAK_STATE_AT_TAC
   [`st:int64`; `word_add (st:int64) (word 200)`;
    `word_add (st:int64) (word 400)`; `word_add (st:int64) (word 600)`];;

let SHK4_STATES_THEN (ttac:term->term->term->term->tactic) =
  KECCAK_STATE_THEN `st:int64` (fun v0 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 200)` (fun v1 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 400)` (fun v2 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 600)` (fun v3 ->
    ttac v0 v1 v2 v3))));;

let SHK4_MBOUND_TAC =
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

let SHK4_LASTBLOCK_TAC =
  MAP_EVERY (fun (pp,mm,pn) ->
    SUBGOAL_THEN
     (subst [pp,`P:num`; mm,`M:num`]
       `(P DIV 2 EXP (8 * 136 * q)) MOD 2 EXP (8 * 136) =
        M DIV 2 EXP (8 * 136 * q) +
        2 EXP (8 * t) * num_of_bytelist(keccak_pad 136 31 mlen)`)
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC [pn; "q"; "t"] THEN
      MATCH_MP_TAC KECCAK_BLOCK_LAST THEN
      ASM_SIMP_TAC[KECCAK_PAD_BOUND; ARITH_RULE `31 < 128`;
                   ARITH_RULE `0 < 136`];
      ALL_TAC])
   [`P0:num`,`M0:num`,"P0"; `P1:num`,`M1:num`,"P1";
    `P2:num`,`M2:num`,"P2"; `P3:num`,`M3:num`,"P3"];;

let SHK4_BYTE_FACT_TAC sname n =
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

(*** The last block when it is just the padding: 0x1F and 128 ***)

let SHK4_T0_LANE_TAC =
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`;
               ARITH_RULE `0 < 136`] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  SIMP_TAC[MOD_MULT; ARITH_EQ] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES; SUB_0;
              ARITH_RULE `136 - 1 = 135`; ARITH_RULE `~(0 = 135)`] THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN CONV_TAC NUM_REDUCE_CONV;;

(*** The last block with 135 bytes of the message: the byte 0x9F ***)

let SHK4_B_LANE_TAC =
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`;
               ARITH_RULE `0 < 136`; ARITH_RULE `136 - 1 = 135`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ARITH_RULE `31 + 128 = 159`] THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];;

(*** The last block with t bytes of the message, 0 < t < 135 ***)

let SHK4_C_LANE_TAC =
  AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[KECCAK_PAD_NUM; ARITH_RULE `31 < 128`;
               ARITH_RULE `0 < 136`; ARITH_RULE `136 - 1 = 135`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP] THEN
  SUBGOAL_THEN
   `2 EXP (8 * 135) = 2 EXP (8 * t) * 2 EXP (8 * (136 - t - 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `t < 136` THEN ARITH_TAC;
    ALL_TAC] THEN
  W(fun (_,w) -> MP_TAC(ISPECL
    [`2 EXP (8 * t) * 31`; `128`; `8 * t + 8 * (136 - t - 1)`]
    (INST_TYPE [`:1600`,`:N`] WORD_XOR_DISJOINT_ADD))) THEN
  REWRITE_TAC[EXP_ADD] THEN ANTS_TAC THENL
   [REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[LE_EXP] THEN UNDISCH_TAC `~(t = 135)` THEN
      UNDISCH_TAC `t < 136` THEN ARITH_TAC];
    REWRITE_TAC[GSYM MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
  MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Tactics for the events, as for mld_keccak_absorb_once_x4 of gcc12_O2. The *)
(* seventh argument of each call of mldsa_keccakf1600x4_xor_bytes is put in  *)
(* the form that it reads by STACK_ARG32_TAC.                                *)
(* ------------------------------------------------------------------------- *)

(*** The abbreviations q and t in the last block expanded ***)

let SHK4_UNABBREV_TAC =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `mlen DIV 136 = q` || c = `mlen MOD 136 = t` then SYM th
      else failwith "") asl in
    if ths = [] then ALL_TAC else REWRITE_TAC ths);;

(*** EXISTS_E2_TAC, also allowing the event functions f_ev_... ***)

let SHK4_EXISTS_E2_TAC allowed_vars_e =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  SHK4_UNABBREV_TAC THEN
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

let SHK4_DISCHARGE_TAC =
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

let SHK4_VARS =
  [`pc:num`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`; `st:int64`;
   `mlen:num`; `stackpointer:int64`; `returnaddress:int64`];;

let SHK4_CALL_TAC name ilist vars n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc,SHK4_EXEC,
       0x0,mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc,safety_th)
      ilist n THENL
     [SHK4_EXISTS_E2_TAC (ref vars); LABEL_TAC name safety_th]);;

let SHK4_XOR_TAC off len ms vars n =
  TRY(STACK_ARG32_TAC `word_add stackpointer (word 280):int64`) THEN
  SHK4_STATES_TAC THEN
  SHK4_STATES_THEN (fun v0 v1 v2 v3 ->
    SHK4_CALL_TAC "H_XOR"
     ([`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
       `read RCX s`; `read R8 s`; off; len; v0; v1; v2; v3] @ ms @
      [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
     vars n) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

(* ------------------------------------------------------------------------- *)
(* The setup: the callee theorems, the template of the events, as for        *)
(* mld_keccak_absorb_once_x4 of gcc12_O2 with the rate 136, the frame of 384 *)
(* bytes at stackpointer, the padded messages P0, ..., P3, and the saved     *)
(* registers. The function pushes six registers and reserves 40 bytes (RSP = *)
(* stackpointer + 296), with the padding byte at stackpointer + 327, and a   *)
(* call puts the seventh argument of mldsa_keccakf1600x4_xor_bytes at        *)
(* stackpointer + 280, below which mldsa_keccakf1600x4_permute uses 280      *)
(* bytes with its return address.                                            *)
(* ------------------------------------------------------------------------- *)

let SHK4_INTRO_TAC =
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m0:int64) (m1:int64) (m2:int64) (m3:int64) (st:int64) (mlen:num)
      (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND
       (if mlen MOD 136 = 0
        then f_ev_t0 m0 m1 m2 m3 st mlen pc stackpointer returnaddress
        else if mlen MOD 136 = 135
        then f_ev_t1 m0 m1 m2 m3 st mlen pc stackpointer returnaddress
        else f_ev_t2 m0 m1 m2 m3 st mlen pc stackpointer returnaddress)
       (if mlen < 136
        then f_ev_short m0 m1 m2 m3 st mlen pc stackpointer returnaddress
        else APPEND
              (f_ev_epil m0 m1 m2 m3 st mlen pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV 136)
                  (\i. f_ev_loop m0 m1 m2 m3 st mlen pc stackpointer
                                 returnaddress i))
                (f_ev_prol m0 m1 m2 m3 st mlen pc stackpointer
                           returnaddress)))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600; fst SHK4_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `800 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun (p,m) ->
    ABBREV_TAC (subst [p,`P:num`; m,`M:num`]
     `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad 136 0x1F mlen)`))
   [`P0:num`,`M0:num`; `P1:num`,`M1:num`; `P2:num`,`M2:num`;
    `P3:num`,`M3:num`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`;;

(* ------------------------------------------------------------------------- *)
(* The facts at the head of the loop and at its exit: the state address in   *)
(* R15, the frame, the padding byte 0x1F, the messages, the remaining length *)
(* in RBX, the addresses in the messages in RBP, R12, R13 and R14, and the   *)
(* states after k blocks, as 200 bytes each.                                 *)
(* ------------------------------------------------------------------------- *)

let SHK4_FRAME =
 `read R15 s = st /\
  read RSP s = word_add stackpointer (word 296) /\
  read (memory :> bytes64 (word_add stackpointer (word 336))) s = rbx_init /\
  read (memory :> bytes64 (word_add stackpointer (word 344))) s = rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 352))) s = r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 360))) s = r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 368))) s = r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 376))) s = r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 384))) s =
  returnaddress /\
  read (memory :> bytes8 (word_add stackpointer (word 327))) s = word 31 /\
  read (memory :> bytes(m0,mlen)) s = M0 /\
  read (memory :> bytes(m1,mlen)) s = M1 /\
  read (memory :> bytes(m2,mlen)) s = M2 /\
  read (memory :> bytes(m3,mlen)) s = M3`;;

let SHK4_MID = mk_abs(`s:x86state`,list_mk_conj
 [`read RBX s = word(mlen MOD 136)`;
  `read RBP s = word_add m0 (word(136 * mlen DIV 136))`;
  `read R12 s = word_add m1 (word(136 * mlen DIV 136))`;
  `read R13 s = word_add m2 (word(136 * mlen DIV 136))`;
  `read R14 s = word_add m3 (word(136 * mlen DIV 136))`; SHK4_FRAME;
  `read (memory :> bytes(st,200)) s =
   val(keccak_absorb 136 P0 (mlen DIV 136))`;
  `read (memory :> bytes(word_add st (word 200),200)) s =
   val(keccak_absorb 136 P1 (mlen DIV 136))`;
  `read (memory :> bytes(word_add st (word 400),200)) s =
   val(keccak_absorb 136 P2 (mlen DIV 136))`;
  `read (memory :> bytes(word_add st (word 600),200)) s =
   val(keccak_absorb 136 P3 (mlen DIV 136))`]);;

let SHK4_INV = list_mk_abs([`k:num`; `s:x86state`],list_mk_conj
 [`read RBX s = word(mlen - 136 * k)`;
  `read RBP s = word_add m0 (word(136 * k))`;
  `read R12 s = word_add m1 (word(136 * k))`;
  `read R13 s = word_add m2 (word(136 * k))`;
  `read R14 s = word_add m3 (word(136 * k))`; SHK4_FRAME;
  `read (memory :> bytes(st,200)) s = val(keccak_absorb 136 P0 k)`;
  `read (memory :> bytes(word_add st (word 200),200)) s =
   val(keccak_absorb 136 P1 k)`;
  `read (memory :> bytes(word_add st (word 400),200)) s =
   val(keccak_absorb 136 P2 k)`;
  `read (memory :> bytes(word_add st (word 600),200)) s =
   val(keccak_absorb 136 P3 k)`]);;


(* ------------------------------------------------------------------------- *)
(* The branches on the remaining length x, as 64-bit words with              *)
(* val(word x) = x in the assumptions: SHK4_RIP_TAC turns the condition of a *)
(* conditional RIP into x < 136 (no more block), 136 <= x (one more) or      *)
(* x = 135, and decides it when it or its negation is an assumption.         *)
(* SHK4_ZF_TAC does the same for ZF after the comparison of t with 135.      *)
(* ------------------------------------------------------------------------- *)

let SHK4_VAL135 = prove
 (`val(word 135:int64) = 135`,
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let SHK4_RIP_TAC =
  W(fun (asl,w) ->
    let vths = mapfilter (fun (_,th) ->
      if can (term_match [] `val(word n:int64) = n`) (concl th) then th
      else failwith "") asl in
    let asms = map (concl o snd) asl in
    let decide th =
      let th' = REWRITE_RULE([VAL_WORD_SUB_EQ_0; SHK4_VAL135; SHK4_LE135;
                              SHK4_GT135] @ vths) th in
      try let p,_ = dest_cond(rand(concl th')) in
          if mem p asms then REWRITE_RULE[EQT_INTRO(ASSUME p)] th'
          else if mem (mk_neg p) asms
          then REWRITE_RULE[EQF_INTRO(ASSUME(mk_neg p))] th'
          else th'
      with Failure _ -> th' in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read RIP s = (if p then x else y)`) (concl th)
      then decide th else th));;

let SHK4_ZF_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `ZF` (concl th) && is_iff (concl th)
    then REWRITE_RULE[VAL_WORD_SUB_EQ_0; SHK4_VAL135;
                      ASSUME `val(word t:int64) = t`] th
    else th);;

(* ------------------------------------------------------------------------- *)
(* From the entry: the pushes, the zeroing of the 800 bytes of the context,  *)
(* which may not be aligned, inlined as zero quadword stores at its start    *)
(* and end and a REP STOSQ in between (see MEMSET_PREP_TAC in                *)
(* utils/mldsa_native_memset.ml), so that the four states are zero, the      *)
(* padding byte 0x1F, and the test of whether there is a whole block, after  *)
(* which a message shorter than a block goes to the exit of the loop.        *)
(* ------------------------------------------------------------------------- *)

let SHK4_VAL_MLEN_TAC =
  SUBGOAL_THEN `val(word mlen:int64) = mlen`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

let SHK4_PROLOGUE_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC SHK4_EXEC (1--22) THEN
  MEMSET_PREP_TAC THEN
  MEMSET_STEP_TAC SHK4_EXEC 23 THEN
  MEMSET_DONE_TAC `st:int64` 800 "s23" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SHK4_BYTES800_ZERO o check
   (can (term_match []
     `read (memory :> bytes(st,800)) s = 0`) o concl)) THEN
  SHK4_VAL_MLEN_TAC THEN
  X86_STEPS_TAC SHK4_EXEC (24--26) THEN SHK4_RIP_TAC;;

let SHK4_SHORT_TAC =
  SHK4_PROLOGUE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop over the whole blocks, with its initialization from the entry:   *)
(* the body XORs in a block of each message and permutes, and tests the      *)
(* remaining length, decremented before the calls.                           *)
(* ------------------------------------------------------------------------- *)

let SHK4_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `136`; `i:num`] ABSORB_BLOCK_BOUND) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < 136`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `0 + 136 <= 200` ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MAP_EVERY (fun (m,mm) ->
    MP_TAC(SPECL [m; `mlen:num`; mm; `136 * i`; `136`; `s0:x86state`]
                 READ_MEMORY_BYTES_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC)
   [`m0:int64`,`M0:num`; `m1:int64`,`M1:num`; `m2:int64`,`M2:num`;
    `m3:int64`,`M3:num`] THEN
  X86_STEPS_TAC SHK4_EXEC (1--14) THEN
  SHK4_XOR_TAC `0` `136`
   [`(M0 DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)`;
    `(M1 DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)`;
    `(M2 DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)`;
    `(M3 DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)`]
   (SHK4_VARS @ [`i:num`]) 15 THEN
  X86_STEPS_TAC SHK4_EXEC (16--17) THEN
  SHK4_STATES_TAC THEN
  SHK4_STATES_THEN (fun v0 v1 v2 v3 ->
    SHK4_CALL_TAC "H_PERMUTE"
      [`e:(uarch_event)list`; `read RDI s`; v0; v1; v2; v3; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
      (SHK4_VARS @ [`i:num`]) 18) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  SUBGOAL_THEN `word_sub (word (mlen - 136 * i)) (word 136):int64 =
                word(mlen - 136 * (i + 1))` SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [UNDISCH_TAC `136 * i + 136 <= mlen` THEN ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC SHK4_EXEC (19--21) THEN
  SUBGOAL_THEN
   `val(word(mlen - 136 * (i + 1)):int64) = mlen - 136 * (i + 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC SHK4_EXEC [22] THEN SHK4_RIP_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_LT] THEN
  MP_TAC(SPECL [`mlen:num`; `136`; `i:num`] ABSORB_LOOP_TEST) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < 136`] THEN DISCH_THEN SUBST1_TAC THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun _ -> CONJ_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`];
    ALL_TAC]) (1--4) THEN
  MAP_EVERY (fun _ -> CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; EXP] THEN
    MAP_EVERY (fun v -> TRY(EXPAND_TAC v)) ["P0"; "P1"; "P2"; "P3"] THEN
    CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
    MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
    UNDISCH_TAC `136 * i + 136 <= mlen` THEN ARITH_TAC;
    ALL_TAC]) (1--4) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let SHK4_LOOP_TAC =
  ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV 136`
   `pc + mldsa_shake256x4_absorb_once_loop1`
   `pc + mldsa_shake256x4_absorb_once_loop1_exit` SHK4_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[DIV_EQ_0; ARITH_EQ];

    (*** Initialization of the loop, with the states zero ***)

    SHK4_PROLOGUE_TAC THEN X86_STEPS_TAC SHK4_EXEC [27] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body ***)

    SHK4_BODY_TAC;

    (*** The loop exit ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* The last block of each message, q = mlen DIV 136 blocks after the start,  *)
(* with its t = mlen MOD 136 bytes, then the padding: the first byte 0x1F at *)
(* byte t and 128 at byte 135, or 0x9F if t = 135, XORed in from the padding *)
(* byte on the stack, which is used for all four. The lanes of the result    *)
(* are proved as for mld_keccak_absorb_once_x4 of gcc12_O2, after mlen is    *)
(* replaced by 136 * q + t, and then the events, with q and t expanded.      *)
(* ------------------------------------------------------------------------- *)

let SHK4_EVENTS_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen DIV 136 = q`))) THEN
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
        check (fun th -> concl th = `mlen MOD 136 = t`))) THEN
  SHK4_DISCHARGE_TAC;;

let SHK4_LANES_TAC pre lane =
  MAP_EVERY (fun _ -> CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) && rhs(concl th) = `mlen:num` &&
                       is_binary "+" (lhs(concl th)))) THEN
    pre THEN lane;
    ALL_TAC]) (1--4) THEN
  SHK4_EVENTS_TAC;;

let SHK4_T0_PRE_TAC =
  SUBGOAL_THEN
   `!M. M < 2 EXP (8 * (136 * q + t)) ==> M DIV 2 EXP (8 * 136 * q) = 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_LT THEN
    UNDISCH_TAC `M < 2 EXP (8 * (136 * q + t))` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC];;

let SHK4_B_PRE_TAC =
  SUBGOAL_THEN `(136 * q + 135) MOD 136 = 135` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN
    SIMP_TAC[MOD_MULT_ADD; MOD_LT; ARITH_RULE `135 < 136`];
    ALL_TAC];;

let SHK4_C_PRE_TAC =
  SUBGOAL_THEN `(136 * q + t) MOD 136 = t` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    ALL_TAC];;

let SHK4_TAIL_TAC =
  ABBREV_TAC `q = mlen DIV 136` THEN ABBREV_TAC `t = mlen MOD 136` THEN
  SUBGOAL_THEN `136 * q + t = mlen /\ t < 136` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `136`] DIVISION) THEN
    REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  FULL_INIT_TAC THEN SHK4_MBOUND_TAC THEN SHK4_LASTBLOCK_TAC THEN
  X86_STEPS_TAC SHK4_EXEC (1--1) THEN ARGS_32_TAC [`t:num`] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [(*** A whole number of blocks: 0x1F at byte 0 and 128 at byte 135 ***)

    X86_STEPS_TAC SHK4_EXEC (2--13) THEN ARGS_32_TAC [`t:num`] THEN
    SHK4_BYTE_FACT_TAC "s13" `31` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ 135 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SHK4_XOR_TAC `0` `1` [`31`; `31`; `31`; `31`] SHK4_VARS 14 THEN
    X86_STEPS_TAC SHK4_EXEC (15--23) THEN
    SHK4_BYTE_FACT_TAC "s23" `128` THEN
    SHK4_XOR_TAC `135` `1` [`128`; `128`; `128`; `128`] SHK4_VARS 24 THEN
    X86_STEPS_TAC SHK4_EXEC (25--34) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHK4_LANES_TAC SHK4_T0_PRE_TAC SHK4_T0_LANE_TAC;
    ALL_TAC] THEN

  (*** Otherwise, first the t bytes of each message after its blocks ***)

  SUBGOAL_THEN `0 + t <= 200` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (m,mm) ->
    SUBGOAL_THEN
     (subst [mm,`M:num`] `M DIV 2 EXP (8 * 136 * q) < 2 EXP (8 * t)`)
    ASSUME_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
      FIRST_ASSUM(SUBST1_TAC o
        check (fun th -> concl th = `136 * q + t = mlen`)) THEN
      FIRST_X_ASSUM(fun th -> if concl th = subst [mm,`M:num`]
        `M < 2 EXP (8 * mlen)` then ACCEPT_TAC th else NO_TAC);
      ALL_TAC] THEN
    MP_TAC(SPECL [m; `mlen:num`; mm; `136 * q`; `t:num`; `s1:x86state`]
                 READ_MEMORY_BYTES_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC)
   [`m0:int64`,`M0:num`; `m1:int64`,`M1:num`; `m2:int64`,`M2:num`;
    `m3:int64`,`M3:num`] THEN
  X86_STEPS_TAC SHK4_EXEC (2--13) THEN
  SHK4_XOR_TAC `0` `t:num`
   [`M0 DIV 2 EXP (8 * 136 * q)`; `M1 DIV 2 EXP (8 * 136 * q)`;
    `M2 DIV 2 EXP (8 * 136 * q)`; `M3 DIV 2 EXP (8 * 136 * q)`]
   SHK4_VARS 14 THEN
  X86_STEPS_TAC SHK4_EXEC (15--18) THEN ARGS_32_TAC [`t:num`] THEN
  SHK4_ZF_TAC THEN ABSORB_CASE_FLAG_TAC `t = 135` THENL
   [(*** The padding is just the single byte 0x9F at byte 135 ***)

    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `t = 135`)) THEN
    X86_STEPS_TAC SHK4_EXEC (19--29) THEN
    SHK4_BYTE_FACT_TAC "s29" `159` THEN
    SUBGOAL_THEN `135 + 1 <= 200` ASSUME_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SHK4_XOR_TAC `135` `1` [`159`; `159`; `159`; `159`] SHK4_VARS 30 THEN
    X86_STEPS_TAC SHK4_EXEC (31--40) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHK4_LANES_TAC SHK4_B_PRE_TAC SHK4_B_LANE_TAC;

    (*** Otherwise 0x1F at byte t and 128 at byte 135 ***)

    X86_STEPS_TAC SHK4_EXEC (19--29) THEN ARGS_32_TAC [`t:num`] THEN
    SHK4_BYTE_FACT_TAC "s29" `31` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ 135 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SHK4_XOR_TAC `t:num` `1` [`31`; `31`; `31`; `31`] SHK4_VARS 30 THEN
    X86_STEPS_TAC SHK4_EXEC (31--39) THEN
    SHK4_BYTE_FACT_TAC "s39" `128` THEN
    SHK4_XOR_TAC `135` `1` [`128`; `128`; `128`; `128`] SHK4_VARS 40 THEN
    X86_STEPS_TAC SHK4_EXEC (41--50) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SHK4_LANES_TAC SHK4_C_PRE_TAC SHK4_C_LANE_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the four states    *)
(* are zeroed and then each is the state after absorbing the corresponding   *)
(* message, with the first byte 0x1F of the padding, as for SHAKE, before    *)
(* the last permutation. The events depend only on the addresses and the     *)
(* length.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  SHK4_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mldsa_shake256x4_absorb_once_loop1_exit` SHK4_MID THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < 136` THEN ASM_REWRITE_TAC[] THENL
     [SHK4_SHORT_TAC; SHK4_LOOP_TAC];
    ASM_CASES_TAC `mlen < 136` THEN ASM_REWRITE_TAC[] THEN
    SHK4_TAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
