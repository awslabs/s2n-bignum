(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proof of mldsa_poly_uniform of the clang 23 -O3 build: the *)
(* two loops that clang 23 made of mld_rej_uniform_c, each from its head to  *)
(* its exit, with the events of every iteration.                             *)
(*                                                                           *)
(* PU_SCAN1 is the first one, over the bytes of the first 5 blocks of the    *)
(* SHAKE128 output (840 bytes in the buffer at sp + 224, from the count 0 to *)
(* at most 280 groups); PU_SCAN2 is the one over a block of 168 bytes, from  *)
(* the count c of the coefficients so far and at most 56 groups. Both read   *)
(* the 3 bytes of a group, form the candidate of mld_rej_uniform_cand, store *)
(* it at the count if it is below q, and stop when the polynomial has 256    *)
(* coefficients or the groups are used up. The iteration events are those of *)
(* the cases: a (accepted), r (rejected), and for the last iteration, ah and *)
(* rh (the group count is used up, the b.hi is taken) and af (the            *)
(* polynomial is full). The buffer is aligned to 32 bytes with an and of the *)
(* stack pointer, so the lemmas take the aligned stack pointer sp.           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "arm/proofs/utils/mldsa_native_sampling.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

let PU_EXEC = MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic of the loop tests and the facts about the groups.              *)
(* ------------------------------------------------------------------------- *)

let PTR_ADD_G = prove(`!b:int64 n k. word_add (word_add b (word n)) (word k) = word_add b (word (n + k))`, REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

let PU_VAL_ADD = prove(`!x k. x + k < 2 EXP 64 ==> val(word_add (word x:int64) (word k)) = x + k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `x < 2 EXP 64 /\ k < 2 EXP 64` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;
let PU_HI1 = prove(`!i. i < 280 ==> ((837 <= val(word_add (word (3 * i)) (word 3):int64) /\ ~(val(word_add (word (3 * i)) (word 18446744073709550782):int64) = 0)) <=> 280 <= i + 1)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[]);;
let PU_HI1B = prove(`!i. i < 280 ==> ((837 <= 3 * i + 3 /\ ~(val(word_add (word (3 * i)) (word 18446744073709550782):int64) = 0)) <=> 280 <= i + 1)`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `i:num` PU_HI1) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word_add (word (3 * i)) (word 3):int64) = 3 * i + 3` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC PU_VAL_ADD THEN ASM_ARITH_TAC);;
let PU_VAL_WORD = prove(`!c. c < 2 EXP 64 ==> val(word c:int64) = c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT]);;
let PU_ZX64_32 = prove(`!t. t < 2 EXP 32 ==> word_zx(word t:int64):int32 = word t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `t < 2 EXP 64` (fun th -> ASM_SIMP_TAC[th; MOD_LT; MOD_LT_EQ]) THEN ASM_ARITH_TAC);;

let PU_COND_REWRITE_TAC ths =
  let pats = map (fun th -> lhs(snd(dest_imp(snd(strip_forall(concl th))))),th)
                 (flat(map CONJUNCTS ths)) in
  W(fun (asl,w) ->
    let tml = list_mk_conj(w::map (concl o snd) asl) in
    let jobs = itlist (fun (pat,th) acc ->
       map (fun t -> t,th)
           (setify (find_terms (can (term_match [] pat)) tml)) @ acc)
       pats [] in
    MAP_EVERY (fun (t,th) ->
      TRY(let lth = PART_MATCH (lhs o rand) th t in
      MP_TAC lth THEN
      ANTS_TAC THENL
       [TRY(CONV_TAC NUM_REDUCE_CONV) THEN SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                             REWRITE_TAC[th])])) jobs);;

let PU_PCS = [`word(pc + 239404):int64`; `word(pc + 239460):int64`];;



let PU_STORE_TAC =
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_CASES_TAC `k < c` THENL
   [REWRITE_TAC[EL_APPEND; ASSUME `LENGTH (mld_rej_uniform_list (b:num->byte) i) = c`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(k:num) = c` SUBST_ALL_TAC THENL [MAP_EVERY UNDISCH_TAC [`k < c + 1`; `~(k < c)`] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL_APPEND; ASSUME `LENGTH (mld_rej_uniform_list (b:num->byte) i) = c`; ARITH_RULE `~(c < c)`; SUB_REFL; EL; HD] THEN
    SUBGOAL_THEN `val(word c:int64) = c` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [MATCH_MP_TAC PU_VAL_WORD THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_zx(word tv:int64):int32 = word tv` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [MATCH_MP_TAC PU_ZX64_32 THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[]];;

let PU_HI2 = prove(`!i. i < 56 ==> ((165 <= val(word (3 * i + 3):int64) /\ ~(val(word_sub (word (3 * i + 3)) (word 165):int64) = 0)) <=> 56 <= i + 1)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[]);;
let PU_HI2B = prove(`!i. i < 56 ==> ((165 <= 3 * i + 3 /\ ~(val(word_sub (word (3 * i + 3)) (word 165):int64) = 0)) <=> 56 <= i + 1)`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPEC `i:num` PU_HI2) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word (3 * i + 3):int64) = 3 * i + 3` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC PU_VAL_WORD THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let PU_STEP_TAC execth n (asl,w) =
  (ARM_STEPS_TAC execth [n] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
   PU_COND_REWRITE_TAC [PU_HI1; PU_HI1B; PU_HI2; PU_HI2B; PU_VAL_ADD; PU_VAL_WORD; SAMPLING_WORD_ZX_SMALL] THEN
   TRY SAMPLING_DECIDE_CONDS_TAC THEN TRY SAMPLING_DECIDE_BRANCH_TAC) (asl,w);;
let rec PU_RUN_TAC execth n stop (asl,w) =
  (PU_STEP_TAC execth n THEN
   (fun g -> let pcv = SAMPLING_REGVAL `PC` g in
             if is_cond pcv || mem pcv stop then ALL_TAC g
             else PU_RUN_TAC execth (n + 1) stop g)) (asl,w);;

let PU2_STORE_TAC =
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_CASES_TAC `k < m` THENL
   [FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) && free_in `f:num->int32` (concl th) then MP_TAC(SPEC `k:num` th) else NO_TAC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[EL_APPEND; ASSUME `LENGTH (mld_rej_uniform_list (b:num->byte) i) = l`] THEN
    SUBGOAL_THEN `k - c < l` (fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY UNDISCH_TAC [`k < m`; `c + l = m`; `~(k < c)`] THEN ARITH_TAC;
    SUBGOAL_THEN `(k:num) = m` SUBST_ALL_TAC THENL [MAP_EVERY UNDISCH_TAC [`k < c + l + 1`; `c + l = m`; `~(k < m)`] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(m < c)` (fun th -> REWRITE_TAC[th]) THENL [UNDISCH_TAC `c + l = m` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `m - c = l` (fun th -> REWRITE_TAC[th; EL_APPEND; ASSUME `LENGTH (mld_rej_uniform_list (b:num->byte) i) = l`; ARITH_RULE `~(l < l)`; SUB_REFL; EL; HD]) THENL [UNDISCH_TAC `c + l = m` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word m:int64) = m` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [MATCH_MP_TAC PU_VAL_WORD THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_zx(word tv:int64):int32 = word tv` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [MATCH_MP_TAC PU_ZX64_32 THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[]];;

let PU_BYTE_FACT k =
  let t = subst [k,`k:num`] `read (memory :> bytes8 (word_add sp (word (224 + 3 * i + k)))) s0 = (b:num->byte) (3 * i + k)` in
  let eqt = subst [k,`k:num`] `word_add (word_add sp (word 224)) (word (3 * i + k)):int64 = word_add sp (word (224 + 3 * i + k))` in
  SUBGOAL_THEN t (ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES]) THENL
   [SUBGOAL_THEN eqt ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th) then MP_TAC(SPEC (subst [k,`k:num`] `3 * i + k`) th) else NO_TAC) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; REWRITE_TAC[ASSUME eqt] THEN DISCH_THEN ACCEPT_TAC];
    ALL_TAC];;
let PU_CAND_RAW = prove(`!(b:num->byte) i. word_insert (word_zx (word_join (b (3 * i + 1)) (b (3 * i)):int16):int32) (16,7) (word_zx (b (3 * i + 2)):int32) = mld_rej_uniform_cand b i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_rej_uniform_cand] THEN BITBLAST_TAC);;

let PU_G_FACTS = prove(`!(b:num->byte) G. mld_rej_uniform_groups 256 0 b 840 = G
  ==> LENGTH(mld_rej_uniform_list b G) <= 256 /\
      MIN 256 (LENGTH(mld_rej_uniform_list b 280)) = LENGTH(mld_rej_uniform_list b G) /\
      (!k. k < LENGTH(mld_rej_uniform_list b G)
           ==> EL k (mld_rej_uniform_list b 280) = EL k (mld_rej_uniform_list b G))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o MATCH_MP MLD_REJ_UNIFORM_GROUPS) THEN
  SUBGOAL_THEN `LENGTH(mld_rej_uniform_list (b:num->byte) G) <= 256` ASSUME_TAC THENL
   [ASM_CASES_TAC `G = 0` THENL
     [ASM_REWRITE_TAC[mld_rej_uniform_list; list_of_seq; FILTER; LENGTH; ARITH_RULE `0 <= n`];
      SUBGOAL_THEN `?g. G = g + 1` STRIP_ASSUME_TAC THENL [EXISTS_TAC `G - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `g:num` o check (fun th -> is_forall(concl th))) THEN
      ASM_REWRITE_TAC[ARITH_RULE `g < g + 1`] THEN
      REWRITE_TAC[MLD_REJ_UNIFORM_LIST_SUC; LENGTH_APPEND; SAMPLING_LENGTH_COND] THEN
      COND_CASES_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`256`; `0`; `b:num->byte`; `840`] MLD_REJ_UNIFORM_CTR) THEN
    MP_TAC(SPEC `b:num->byte` MLD_REJ_UNIFORM_CTR_FIRST) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN ASM_ARITH_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC EL_MLD_REJ_UNIFORM_LIST_PREFIX THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `G <= 840 DIV 3` THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN ACCEPT_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The first loop.                                                           *)
(* ------------------------------------------------------------------------- *)

let PU_MC = `mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc`;;

let PU_SCAN1_TM = parse_term
 "exists f_events.
    forall e (a:int64) (sp:int64) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 sp /\\
      nonoverlapping (a,1024) (word_add sp (word 216),848) /\\
      ALL (nonoverlapping (word pc,libmldsa_size))
          [(a,1024); (word_add sp (word 216),848)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa_poly_uniform_loop1_exit) /\\
                read SP s = sp /\\ read X19 s = a /\\ read X22 s = word 168 /\\
                (!j. j < 840
                     ==> read (memory :> bytes8 (word_add (word_add sp (word 224)) (word j))) s = b j) /\\
                read events s = e)
           (\\s. read PC s = word (pc + mldsa_poly_uniform_loop2_exit) /\\
                read SP s = sp /\\ read X19 s = a /\\ read X22 s = word 168 /\\
                read X23 s = word 8380417 /\\
                read X9 s = word_add sp (word 224) /\\
                read X24 s = word (MIN 256 (LENGTH(mld_rej_uniform_list b 280))) /\\
                (!k. k < MIN 256 (LENGTH(mld_rej_uniform_list b 280))
                     ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                         EL k (mld_rej_uniform_list b 280)) /\\
                (!j. j < 840
                     ==> read (memory :> bytes8 (word_add (word_add sp (word 224)) (word j))) s = b j) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events a sp b pc /\\
                   memaccess_inbounds e2
                    [a,1024; word_add sp (word 216),848]
                    [a,1024; word_add sp (word 216),4]))
           (MAYCHANGE [PC; X8; X9; X10; X11; X23; X24] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,1024);
                       memory :> bytes(word_add sp (word 216),4)])";;

let PU_S1_G = `mld_rej_uniform_groups 256 0 (b:num->byte) 840`;;
let PU_S1_TEMPLATE =
 `\(a:int64) (sp:int64) (b:num->byte) (pc:num).
    APPEND (f_ev_epil a sp b pc)
     (APPEND
       (ENUMERATEL (mld_rej_uniform_groups 256 0 b 840)
         (\i. if i + 1 < mld_rej_uniform_groups 256 0 b 840
              then if val(mld_rej_uniform_cand b i) < 8380417
                   then f_ev_a a sp b pc i else f_ev_r a sp b pc i
              else if mld_rej_uniform_groups 256 0 b 840 = 280
                   then if val(mld_rej_uniform_cand b i) < 8380417
                        then f_ev_ah a sp b pc i else f_ev_rh a sp b pc i
                   else f_ev_af a sp b pc i))
       (f_ev_prol a sp b pc)):(uarch_event)list`;;
let PU_S1_INV =
 `\i s. read X8 s = word (3 * i) /\ read X9 s = word_add sp (word 224) /\
        read X19 s = a /\ read X22 s = word 168 /\ read X23 s = word 8380417 /\
        read SP s = sp /\
        read X24 s = word (LENGTH(mld_rej_uniform_list b i)) /\
        (!j. j < 840
             ==> read (memory :> bytes8 (word_add (word_add sp (word 224)) (word j))) s = b j) /\
        (!k. k < LENGTH(mld_rej_uniform_list b i)
             ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                 EL k (mld_rej_uniform_list b i))`;;

(*** The tactics of the paths of the loop body ***)

let PU_ITER_SETUP_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < G`) o check (fun th -> is_forall(concl th) && can (term_match [] `!m. m < G ==> P m`) (concl th))) THEN STRIP_TAC THEN
  FULL_INIT_TAC THEN
  MAP_EVERY PU_BYTE_FACT [`0`;`1`;`2`] THEN
  SUBGOAL_THEN `read (memory :> bytes16 (word_add sp (word (224 + 3 * i)))) s0 = word_join ((b:num->byte) (3 * i + 1)) (b (3 * i))` ASSUME_TAC THENL
   [REWRITE_TAC[el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    SUBGOAL_THEN `word_add (word_add sp (word (224 + 3 * i))) (word 1):int64 = word_add sp (word (224 + 3 * i + 1))` ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0]; ALL_TAC] THEN
  MP_TAC(MATCH_MP MLD_REJ_UNIFORM_GROUPS_NEXT (CONJ (ASSUME `mld_rej_uniform_groups 256 0 (b:num->byte) 840 = G`) (ASSUME `i < G`))) THEN
  MP_TAC(ISPECL [`word_or (word_or (word_zx((b:num->byte)(3 * i))) (word_shl (word_zx(b(3 * i + 1))) 8)) (word_shl (word_zx(b(3 * i + 2))) 16):int32`; `8388607`] (CONJUNCT1 VAL_WORD_AND_WORD_LE)) THEN
  REWRITE_TAC[GSYM mld_rej_uniform_cand] THEN
  REWRITE_TAC[MLD_REJ_UNIFORM_LIST_SUC; LENGTH_APPEND; SAMPLING_LENGTH_COND] THEN
  ABBREV_TAC `c = LENGTH(mld_rej_uniform_list (b:num->byte) i)` THEN
  ABBREV_TAC `tv = val(mld_rej_uniform_cand (b:num->byte) i)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `mld_rej_uniform_cand (b:num->byte) i = word tv` ASSUME_TAC THENL [EXPAND_TAC "tv" THEN REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  ARM_STEPS_TAC PU_EXEC (1--6) THEN
  SAMPLING_REG_TAC `X10` `word_zx(mld_rej_uniform_cand (b:num->byte) i):int64` [mld_rej_uniform_cand] THEN
  RULE_ASSUM_TAC(fun th -> if is_eq(concl th) && can (term_match [] `read c s`) (lhs(concl th)) then REWRITE_RULE [ASSUME `mld_rej_uniform_cand (b:num->byte) i = word tv`] th else th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
  RULE_ASSUM_TAC(fun th -> if is_eq(concl th) && rhs(concl th) = `tv:num` then th else if is_eq(concl th) && rhs(concl th) = `word tv:int32` then th else REWRITE_RULE[WORD_ZX_ZX_32_64_32; PU_CAND_RAW; ASSUME `mld_rej_uniform_cand (b:num->byte) i = word tv`] th) THEN
  SUBGOAL_THEN `i < 280` ASSUME_TAC THENL [UNDISCH_TAC `i < 840 DIV 3` THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN ACCEPT_TAC; ALL_TAC];;

let PU_IFF_TAC =
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhand(concl th) = `i + 1 < G` then MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC;;

let PU_DECIDE_TAC =
  TRY SAMPLING_DECIDE_FLAGS_TAC THEN TRY SAMPLING_DECIDE_CONDS_TAC THEN TRY SAMPLING_DECIDE_BRANCH_TAC;;

let PU_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAMPLING_W64_TAC THEN SAMPLING_SELECT_TAC THEN REPEAT CONJ_TAC;;

let PU_ADD_TAC = REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;;

let PU_SUBST_C_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `c:num` && can (term_match [] `LENGTH(mld_rej_uniform_list b i)`) (lhs(concl th))));;

let PU_VALWORD_C_TAC =
  SUBGOAL_THEN `val(word c:int64) = c` (fun th -> REWRITE_TAC[th]) THENL [MATCH_MP_TAC PU_VAL_WORD THEN CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC];;

let PU_SUBST_TV_TAC =
  SUBGOAL_THEN `val(mld_rej_uniform_cand (b:num->byte) i) = tv` ASSUME_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `tv:num` && can (term_match [] `val(mld_rej_uniform_cand b i)`) (lhs(concl th))));;

let PU_LAST_EVENTS_TAC =
  REWRITE_TAC[GSYM (ASSUME `i + 1 = G`); LT_REFL] THEN
  REWRITE_TAC[ENUMERATEL_ADD1] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  REWRITE_TAC[LT_REFL] THEN SAMPLING_PATH_DISCHARGE_TAC;;

let PU_FREEZE_TAC =
  RULE_ASSUM_TAC(fun th -> if concl th = `G = 280` || concl th = `i + 1 = G` then EQT_INTRO th else th);;

(* acc, continue *)
let PU_ACC_CONT_TAC =
  PU_IFF_TAC THEN PU_DECIDE_TAC THEN PU_RUN_TAC PU_EXEC 7 PU_PCS THEN PU_FINAL_TAC THENL
   [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE; PU_STORE_TAC;
    PU_VALWORD_C_TAC THEN PU_SUBST_C_TAC THEN PU_SUBST_TV_TAC THEN SAMPLING_PATH_DISCHARGE_TAC];;

(* rej, continue *)
let PU_REJ_CONT_TAC =
  PU_IFF_TAC THEN PU_DECIDE_TAC THEN PU_RUN_TAC PU_EXEC 7 PU_PCS THEN PU_FINAL_TAC THENL
   [CONV_TAC WORD_RULE; REWRITE_TAC[ADD_CLAUSES];
    REWRITE_TAC[ADD_CLAUSES; APPEND_NIL] THEN FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) then MATCH_ACCEPT_TAC th else NO_TAC);
    PU_SUBST_C_TAC THEN PU_SUBST_TV_TAC THEN SAMPLING_PATH_DISCHARGE_TAC];;

(* rej, last: G = 280 *)
let PU_REJ_LAST_TAC =
  PU_IFF_TAC THEN
  SUBGOAL_THEN `i + 1 = G` ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [`i < G`; `~(i + 1 < G)`] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `G = 280` ASSUME_TAC THENL [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)))) THEN MAP_EVERY UNDISCH_TAC [`i + 1 = G`; `i < 280`; `0 + c < 256`; `G <= 840 DIV 3`] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  PU_DECIDE_TAC THEN PU_RUN_TAC PU_EXEC 7 PU_PCS THEN
  SUBGOAL_THEN `i + 2 = 281` ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [`i + 1 = G`; `G = 280`] THEN ARITH_TAC; ALL_TAC] THEN
  PU_FREEZE_TAC THEN PU_FINAL_TAC THENL
   [PU_ADD_TAC; REWRITE_TAC[ADD_CLAUSES];
    REWRITE_TAC[ADD_CLAUSES; APPEND_NIL] THEN FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) then MATCH_ACCEPT_TAC th else NO_TAC);
    PU_SUBST_TV_TAC THEN
    SUBGOAL_THEN `280 = i + 1` (fun th -> REWRITE_TAC[th; LT_REFL]) THENL [UNDISCH_TAC `i + 2 = 281` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
    REWRITE_TAC[LT_REFL] THEN SAMPLING_PATH_DISCHARGE_TAC];;

(* acc, last *)
let PU_ACC_LAST_TAC =
  PU_IFF_TAC THEN
  SUBGOAL_THEN `i + 1 = G` ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [`i < G`; `~(i + 1 < G)`] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `G = 280` THENL
   [PU_DECIDE_TAC THEN PU_RUN_TAC PU_EXEC 7 PU_PCS THEN
    SUBGOAL_THEN `i + 2 = 281` ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [`i + 1 = G`; `G = 280`] THEN ARITH_TAC; ALL_TAC] THEN
    PU_FREEZE_TAC THEN PU_FINAL_TAC THENL
     [PU_ADD_TAC; CONV_TAC WORD_RULE; PU_STORE_TAC;
      PU_VALWORD_C_TAC THEN PU_SUBST_C_TAC THEN PU_SUBST_TV_TAC THEN
      SUBGOAL_THEN `280 = i + 1` (fun th -> REWRITE_TAC[th; LT_REFL]) THENL [UNDISCH_TAC `i + 2 = 281` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
      REWRITE_TAC[LT_REFL] THEN SAMPLING_PATH_DISCHARGE_TAC];
    SUBGOAL_THEN `i + 1 < 280` ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [`i + 1 = G`; `~(G = 280)`; `G <= 840 DIV 3`] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `c + 2 = 257` ASSUME_TAC THENL [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)))) THEN MAP_EVERY UNDISCH_TAC [`i + 1 < 280`; `0 + c < 256`] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
    PU_DECIDE_TAC THEN PU_RUN_TAC PU_EXEC 7 PU_PCS THEN PU_FINAL_TAC THENL
     [PU_ADD_TAC; CONV_TAC WORD_RULE; PU_STORE_TAC;
      PU_VALWORD_C_TAC THEN PU_SUBST_C_TAC THEN PU_SUBST_TV_TAC THEN PU_LAST_EVENTS_TAC]];;

let PU_BODY_TAC =
  PU_ITER_SETUP_TAC THEN
  ASM_CASES_TAC `tv < 8380417` THENL
   [ASM_CASES_TAC `i + 1 < G` THENL [PU_ACC_CONT_TAC; PU_ACC_LAST_TAC];
    ASM_CASES_TAC `i + 1 < G` THENL [PU_REJ_CONT_TAC; PU_REJ_LAST_TAC]];;

let PU_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(MATCH_MP PU_G_FACTS (ASSUME `mld_rej_uniform_groups 256 0 (b:num->byte) 840 = G`)) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PU_SCAN1 = prove(PU_SCAN1_TM,
  CONCRETIZE_F_EVENTS_TAC PU_S1_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `sp:int64`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst PU_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`256`; `0`; `b:num->byte`; `840`; `mld_rej_uniform_groups 256 0 (b:num->byte) 840`] MLD_REJ_UNIFORM_GROUPS) THEN REWRITE_TAC[] THEN
  ABBREV_TAC `G = mld_rej_uniform_groups 256 0 (b:num->byte) 840` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `0 < G` ASSUME_TAC THENL [EXPAND_TAC "G" THEN MATCH_MP_TAC MLD_REJ_UNIFORM_GROUPS_POS THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `G:num` `pc + mldsa_poly_uniform_loop2` `pc + mldsa_poly_uniform_loop2_exit` PU_S1_INV THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `0 < G` THEN ARITH_TAC;
    FULL_INIT_TAC THEN ARM_STEPS_TAC PU_EXEC (1--6) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mld_rej_uniform_list; list_of_seq; FILTER; LENGTH; ARITH_RULE `~(a < 0)`; WORD_ADD_0; MULT_CLAUSES; ENUMERATEL] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    PU_BODY_TAC;
    PU_EXIT_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The second loop.                                                          *)
(* ------------------------------------------------------------------------- *)

let PU_ORR2 = prove(`!sp:int64. aligned 32 sp ==> word_or (word_add sp (word 224)) (word 2) = word_add sp (word 226)`,
  GEN_TAC THEN REWRITE_TAC[SAMPLING_ALIGNED_16_32] THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let PU_SCAN2_TM = parse_term
 "exists f_events.
    forall e (a:int64) (sp:int64) (c:num) (f:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 sp /\\ aligned 32 sp /\\ c < 256 /\\
      nonoverlapping (a,1024) (word_add sp (word 8),1056) /\\
      ALL (nonoverlapping (word pc,libmldsa_size))
          [(a,1024); (word_add sp (word 8),1056)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa_poly_uniform_loop4_exit) /\\
                read SP s = sp /\\ read X25 s = word_add sp (word 224) /\\
                read X22 s = word 168 /\\ read X23 s = word 8380417 /\\
                read X24 s = word c /\\
                read (memory :> bytes64 (word_add sp (word 8))) s = a /\\
                (!j. j < 168
                     ==> read (memory :> bytes8 (word_add (word_add sp (word 224)) (word j))) s = b j) /\\
                (!k. k < c
                     ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s = f k) /\\
                read events s = e)
           (\\s. read PC s = word (pc + mldsa_poly_uniform_loop3_test) /\\
                read SP s = sp /\\ read X19 s = a /\\ read X25 s = word_add sp (word 224) /\\
                read X22 s = word 168 /\\ read X23 s = word 8380417 /\\
                read X24 s = word (c + MIN (256 - c) (LENGTH(mld_rej_uniform_list b 56))) /\\
                read (memory :> bytes64 (word_add sp (word 8))) s = a /\\
                (!j. j < 168
                     ==> read (memory :> bytes8 (word_add (word_add sp (word 224)) (word j))) s = b j) /\\
                (!k. k < c + MIN (256 - c) (LENGTH(mld_rej_uniform_list b 56))
                     ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                         (if k < c then f k else EL (k - c) (mld_rej_uniform_list b 56))) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events a sp c b pc /\\
                   memaccess_inbounds e2
                    [a,1024; word_add sp (word 8),1056]
                    [a,1024; word_add sp (word 216),4]))
           (MAYCHANGE [PC; X8; X9; X10; X11; X19; X24] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,1024);
                       memory :> bytes(word_add sp (word 216),4)])";;

let PU_NEG2 = prove(`!sp:int64 i. word_add sp (word ((226 + 3 * i) + 18446744073709551614)) = word_add sp (word (224 + 3 * i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN
  SUBGOAL_THEN `word 18446744073709551614:int64 = word_neg (word 2)` SUBST1_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let PU_NEG2B = prove(`!sp:int64 i. word_add (word_add sp (word (226 + 3 * i))) (word 18446744073709551614) = word_add sp (word (224 + 3 * i))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `word 18446744073709551614:int64 = word_neg (word 2)` SUBST1_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let PU_G_FACTS2 = prove(`!(b:num->byte) c G. c < 256 /\ mld_rej_uniform_groups 256 c b 168 = G
  ==> c + LENGTH(mld_rej_uniform_list b G) <= 256 /\
      c + MIN (256 - c) (LENGTH(mld_rej_uniform_list b 56)) = c + LENGTH(mld_rej_uniform_list b G) /\
      (!k. k < LENGTH(mld_rej_uniform_list b G)
           ==> EL k (mld_rej_uniform_list b 56) = EL k (mld_rej_uniform_list b G))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o MATCH_MP MLD_REJ_UNIFORM_GROUPS) THEN
  SUBGOAL_THEN `c + LENGTH(mld_rej_uniform_list (b:num->byte) G) <= 256` ASSUME_TAC THENL
   [ASM_CASES_TAC `G = 0` THENL
     [ASM_REWRITE_TAC[mld_rej_uniform_list; list_of_seq; FILTER; LENGTH] THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `?g. G = g + 1` STRIP_ASSUME_TAC THENL [EXISTS_TAC `G - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `g:num` o check (fun th -> is_forall(concl th))) THEN
      ASM_REWRITE_TAC[ARITH_RULE `g < g + 1`] THEN
      REWRITE_TAC[MLD_REJ_UNIFORM_LIST_SUC; LENGTH_APPEND; SAMPLING_LENGTH_COND] THEN
      COND_CASES_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`256`; `c:num`; `b:num->byte`; `168`] MLD_REJ_UNIFORM_CTR) THEN
    REWRITE_TAC[mld_rej_uniform_ctr] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
    ASM_REWRITE_TAC[EQ_ADD_LCANCEL] THEN DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC EL_MLD_REJ_UNIFORM_LIST_PREFIX THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `G <= 168 DIV 3` THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN ACCEPT_TAC]);;

let PU_S2_TEMPLATE =
 `\(a:int64) (sp:int64) (c:num) (b:num->byte) (pc:num).
    APPEND (f_ev_epil a sp c b pc)
     (APPEND
       (ENUMERATEL (mld_rej_uniform_groups 256 c b 168)
         (\i. if i + 1 < mld_rej_uniform_groups 256 c b 168
              then if val(mld_rej_uniform_cand b i) < 8380417
                   then f_ev_a a sp c b pc i else f_ev_r a sp c b pc i
              else if mld_rej_uniform_groups 256 c b 168 = 56
                   then if val(mld_rej_uniform_cand b i) < 8380417
                        then f_ev_ah a sp c b pc i else f_ev_rh a sp c b pc i
                   else f_ev_af a sp c b pc i))
       (f_ev_prol a sp c b pc)):(uarch_event)list`;;
let PU_S2_INV =
 `\i s. (i < G ==> read X8 s = word_add sp (word (226 + 3 * i)) /\ read X9 s = word (3 * i + 3)) /\
        read X19 s = a /\ read X22 s = word 168 /\ read X23 s = word 8380417 /\
        read X25 s = word_add sp (word 224) /\ read SP s = sp /\
        read X24 s = word (c + LENGTH(mld_rej_uniform_list b i)) /\
        read (memory :> bytes64 (word_add sp (word 8))) s = a /\
        (!j. j < 168
             ==> read (memory :> bytes8 (word_add (word_add sp (word 224)) (word j))) s = b j) /\
        (!k. k < c + LENGTH(mld_rej_uniform_list b i)
             ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                 (if k < c then f k else EL (k - c) (mld_rej_uniform_list b i)))`;;
let PU_PCS2 = [`word(pc + 239608):int64`; `word(pc + 239488):int64`];;

let PU2_ITER_SETUP_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < G`) o check (fun th -> is_forall(concl th) && can (term_match [] `!m. m < G ==> P m`) (concl th))) THEN STRIP_TAC THEN
  FULL_INIT_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) && is_conj(rand(concl th)) && free_in `X8` (concl th) then STRIP_ASSUME_TAC(MP th (ASSUME `i < G`)) else NO_TAC) THEN
  MAP_EVERY PU_BYTE_FACT [`0`;`1`;`2`] THEN
  SUBGOAL_THEN `read (memory :> bytes16 (word_add sp (word (224 + 3 * i)))) s0 = word_join ((b:num->byte) (3 * i + 1)) (b (3 * i))` ASSUME_TAC THENL
   [REWRITE_TAC[el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    SUBGOAL_THEN `word_add (word_add sp (word (224 + 3 * i))) (word 1):int64 = word_add sp (word (224 + 3 * i + 1))` ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes16 (word_add sp (word ((226 + 3 * i) + 18446744073709551614)))) s0 = word_join ((b:num->byte) (3 * i + 1)) (b (3 * i))` ASSUME_TAC THENL [REWRITE_TAC[PU_NEG2] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes8 (word_add sp (word (226 + 3 * i)))) s0 = (b:num->byte) (3 * i + 2)` ASSUME_TAC THENL [MP_TAC(ASSUME `read (memory :> bytes8 (word_add sp (word (224 + 3 * i + 2)))) s0 = (b:num->byte) (3 * i + 2)`) THEN REWRITE_TAC[ARITH_RULE `224 + 3 * i + 2 = 226 + 3 * i`]; ALL_TAC] THEN
  MP_TAC(MATCH_MP MLD_REJ_UNIFORM_GROUPS_NEXT (CONJ (ASSUME `mld_rej_uniform_groups 256 c (b:num->byte) 168 = G`) (ASSUME `i < G`))) THEN
  MP_TAC(ISPECL [`word_or (word_or (word_zx((b:num->byte)(3 * i))) (word_shl (word_zx(b(3 * i + 1))) 8)) (word_shl (word_zx(b(3 * i + 2))) 16):int32`; `8388607`] (CONJUNCT1 VAL_WORD_AND_WORD_LE)) THEN
  REWRITE_TAC[GSYM mld_rej_uniform_cand] THEN
  REWRITE_TAC[MLD_REJ_UNIFORM_LIST_SUC; LENGTH_APPEND; SAMPLING_LENGTH_COND] THEN
  ABBREV_TAC `l = LENGTH(mld_rej_uniform_list (b:num->byte) i)` THEN
  ABBREV_TAC `m = c + l` THEN
  ABBREV_TAC `tv = val(mld_rej_uniform_cand (b:num->byte) i)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `mld_rej_uniform_cand (b:num->byte) i = word tv` ASSUME_TAC THENL [EXPAND_TAC "tv" THEN REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  ARM_STEPS_TAC PU_EXEC (1--5) THEN
  SAMPLING_REG_TAC `X10` `word_zx(mld_rej_uniform_cand (b:num->byte) i):int64` [mld_rej_uniform_cand] THEN
  RULE_ASSUM_TAC(fun th -> if is_eq(concl th) && can (term_match [] `read c s`) (lhs(concl th)) then REWRITE_RULE [ASSUME `mld_rej_uniform_cand (b:num->byte) i = word tv`] th else th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
  RULE_ASSUM_TAC(fun th -> if is_eq(concl th) && rhs(concl th) = `tv:num` then th else if is_eq(concl th) && rhs(concl th) = `word tv:int32` then th else REWRITE_RULE[WORD_ZX_ZX_32_64_32; PU_CAND_RAW; ASSUME `mld_rej_uniform_cand (b:num->byte) i = word tv`] th) THEN
  SUBGOAL_THEN `i < 56` ASSUME_TAC THENL [UNDISCH_TAC `i < 168 DIV 3` THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN ACCEPT_TAC; ALL_TAC];;

let PU2_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAMPLING_W64_TAC THEN SAMPLING_SELECT_TAC THEN REPEAT CONJ_TAC;;

let PU2_SUBST_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `m:num` && lhs(concl th) = `c + l:num`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `l:num` && can (term_match [] `LENGTH(mld_rej_uniform_list b i)`) (lhs(concl th)))) THEN
  SUBGOAL_THEN `val(mld_rej_uniform_cand (b:num->byte) i) = tv` ASSUME_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `tv:num` && can (term_match [] `val(mld_rej_uniform_cand b i)`) (lhs(concl th)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PU_NEG2B]) THEN REWRITE_TAC[PU_NEG2B];;

let PU2_LAST_ARITH_TAC =
  SUBGOAL_THEN `i = 55` SUBST_ALL_TAC THENL [UNDISCH_TAC `i + 2 = 57` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN CONV_TAC WORD_RULE;;

let PU2_ACC_CONT_TAC =
  PU_IFF_TAC THEN PU_DECIDE_TAC THEN PU_RUN_TAC PU_EXEC 6 PU_PCS2 THEN PU2_FINAL_TAC THENL
   [(CONV_TAC WORD_RULE); (CONV_TAC WORD_RULE); (EXPAND_TAC "m" THEN CONV_TAC WORD_RULE); PU2_STORE_TAC;
    (PU2_SUBST_TAC THEN SAMPLING_PATH_DISCHARGE_TAC)];;

let PU2_REJ_CONT_TAC =
  PU_IFF_TAC THEN PU_DECIDE_TAC THEN PU_RUN_TAC PU_EXEC 6 PU_PCS2 THEN PU2_FINAL_TAC THENL
   [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE; EXPAND_TAC "m" THEN REWRITE_TAC[ADD_CLAUSES];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[APPEND_NIL] THEN
    SUBGOAL_THEN `k < m` ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [`k < c + l + 0`; `c + l = m`] THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) && free_in `f:num->int32` (concl th) then MP_TAC(SPEC `k:num` th) else NO_TAC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    PU2_SUBST_TAC THEN SAMPLING_PATH_DISCHARGE_TAC];;

let PU_ARITH_TAC =
  W(fun (asl,w) ->
    MAP_EVERY (fun (_,th) ->
      let c = concl th in
      if (is_eq c && (try type_of(lhs c) = `:num` with _ -> false)) ||
         is_binary "<" c || is_binary "<=" c ||
         (is_neg c && (is_conj(rand c) || is_binary "<" (rand c) || is_binary "<=" (rand c) ||
                       (is_eq (rand c) && (try type_of(lhs(rand c)) = `:num` with _ -> false))))
      then MP_TAC th else ALL_TAC) asl) THEN ARITH_TAC;;

let PU_FREEZE2_TAC =
  RULE_ASSUM_TAC(fun th -> if concl th = `G = 56` || concl th = `i + 1 = G` then EQT_INTRO th else th);;

let PU2_REJ_LAST_TAC =
  PU_IFF_TAC THEN
  SUBGOAL_THEN `i + 1 = G` ASSUME_TAC THENL [PU_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `G = 56` ASSUME_TAC THENL [PU_ARITH_TAC; ALL_TAC] THEN
  PU_DECIDE_TAC THEN PU_RUN_TAC PU_EXEC 6 PU_PCS2 THEN
  SUBGOAL_THEN `i + 2 = 57` ASSUME_TAC THENL [PU_ARITH_TAC; ALL_TAC] THEN
  PU_FREEZE2_TAC THEN PU2_FINAL_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[ADD_CLAUSES];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[APPEND_NIL] THEN
    SUBGOAL_THEN `k < m` ASSUME_TAC THENL [PU_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) && free_in `f:num->int32` (concl th) then MP_TAC(SPEC `k:num` th) else NO_TAC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    PU2_SUBST_TAC THEN
    SUBGOAL_THEN `56 = i + 1` (fun th -> REWRITE_TAC[th; LT_REFL]) THENL [PU_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
    REWRITE_TAC[LT_REFL] THEN SAMPLING_PATH_DISCHARGE_TAC];;

let PU2_ACC_LAST_TAC =
  PU_IFF_TAC THEN
  SUBGOAL_THEN `i + 1 = G` ASSUME_TAC THENL [PU_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `G = 56` THENL
   [PU_DECIDE_TAC THEN PU_RUN_TAC PU_EXEC 6 PU_PCS2 THEN
    SUBGOAL_THEN `i + 2 = 57` ASSUME_TAC THENL [PU_ARITH_TAC; ALL_TAC] THEN
    PU_FREEZE2_TAC THEN PU2_FINAL_TAC THENL
     [EXPAND_TAC "m" THEN CONV_TAC WORD_RULE; PU2_STORE_TAC;
      PU2_SUBST_TAC THEN
      SUBGOAL_THEN `56 = i + 1` (fun th -> REWRITE_TAC[th; LT_REFL]) THENL [PU_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
      REWRITE_TAC[LT_REFL] THEN SAMPLING_PATH_DISCHARGE_TAC];
    SUBGOAL_THEN `i + 1 < 56` ASSUME_TAC THENL [PU_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `c + l + 2 = 257` ASSUME_TAC THENL [PU_ARITH_TAC; ALL_TAC] THEN
    PU_DECIDE_TAC THEN PU_RUN_TAC PU_EXEC 6 PU_PCS2 THEN PU2_FINAL_TAC THENL
     [EXPAND_TAC "m" THEN CONV_TAC WORD_RULE; PU2_STORE_TAC;
      PU2_SUBST_TAC THEN
      REWRITE_TAC[GSYM (ASSUME `i + 1 = G`); LT_REFL] THEN
      REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
      REWRITE_TAC[LT_REFL] THEN SAMPLING_PATH_DISCHARGE_TAC]];;

let PU2_BODY_TAC =
  PU2_ITER_SETUP_TAC THEN
  ASM_CASES_TAC `tv < 8380417` THENL
   [ASM_CASES_TAC `i + 1 < G` THENL [PU2_ACC_CONT_TAC; PU2_ACC_LAST_TAC];
    ASM_CASES_TAC `i + 1 < G` THENL [PU2_REJ_CONT_TAC; PU2_REJ_LAST_TAC]];;

let PU2_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(MATCH_MP PU_G_FACTS2 (CONJ (ASSUME `c < 256`) (ASSUME `mld_rej_uniform_groups 256 c (b:num->byte) 168 = G`))) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) && free_in `f:num->int32` (concl th) then MP_TAC(SPEC `k:num` th) else NO_TAC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k - c` o check (fun th -> is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "EL" with _ -> false)) (concl th) && not (free_in `bytes32` (concl th)))) THEN
    ANTS_TAC THENL [PU_ARITH_TAC; DISCH_THEN(ACCEPT_TAC o SYM)];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PU_SCAN2 = prove(PU_SCAN2_TM,
  CONCRETIZE_F_EVENTS_TAC PU_S2_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `sp:int64`; `c:num`; `f:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst PU_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`256`; `c:num`; `b:num->byte`; `168`; `mld_rej_uniform_groups 256 c (b:num->byte) 168`] MLD_REJ_UNIFORM_GROUPS) THEN REWRITE_TAC[] THEN
  ABBREV_TAC `G = mld_rej_uniform_groups 256 c (b:num->byte) 168` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `0 < G` ASSUME_TAC THENL [EXPAND_TAC "G" THEN MATCH_MP_TAC MLD_REJ_UNIFORM_GROUPS_POS THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `G:num` `pc + mldsa_poly_uniform_loop5` `pc + mldsa_poly_uniform_loop3_test` PU_S2_INV THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `0 < G` THEN ARITH_TAC;
    FULL_INIT_TAC THEN ARM_STEPS_TAC PU_EXEC (1--4) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `sp:int64` PU_ORR2) (ASSUME `aligned 32 (sp:int64)`)]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mld_rej_uniform_list; list_of_seq; FILTER; LENGTH; ARITH_RULE `~(a < 0)`; WORD_ADD_0; MULT_CLAUSES; ADD_CLAUSES; ENUMERATEL; COND_ID] THEN
    CONJ_TAC THENL [X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[]; DISCHARGE_SAFETY_PROPERTY_TAC];
    PU2_BODY_TAC;
    PU2_EXIT_TAC]);;
