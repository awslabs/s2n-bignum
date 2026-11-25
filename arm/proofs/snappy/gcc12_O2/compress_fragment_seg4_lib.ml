(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* CompressFragment, the segment from loop6 (phase 4 of the model, the head *)
(* of the emit_match loop): FindMatchLength (loop7, loop8), EmitCopy        *)
(* (loop9), the table updates and the check for the next match, to loop6   *)
(* again, to loop1 (phase 1) or to join4 (emit_remainder): the lemmas and   *)
(* the tactics (S4_SEG_TAC). The segment is proved in five jobs by the      *)
(* match length ML (compress_fragment_seg4{a,...,e}_proof.ml), combined in  *)
(* compress_fragment_seg4_proof.ml. The state of the tactics (s4_counter,   *)
(* s4_rewrites, s4_pc_extra) is per domain (common/par_domains.ml).         *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_lib.ml";;


let S4_EXEC = SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC;;


(* The arithmetic of this segment from the numeric facts that are relevant  *)
(* to the goal: those that share an atom with it, twice transitively (the    *)
(* atoms are the free variables, with LENGTH inp as one). The segment has   *)
(* many facts with DIV, and with all of them the decision procedure (linear *)
(* arithmetic by elimination) takes much time and memory, most of all when  *)
(* the goal does not follow, as in the attempts of TRY and FIRST.            *)

let s4_atoms tm =
  let tm' = subst [`n_len_atom:num`,`LENGTH(inp:byte list)`] tm in
  filter (fun v -> not(fst(dest_var v) = "inp")) (frees tm');;

let s4_divmods tm =
  find_terms (fun t -> is_binary "DIV" t || is_binary "MOD" t) tm;;

(* A fact with DIV or MOD only if the goal has one of its DIV/MOD terms, or  *)
(* both mention mcl (the bounds of the output region).                       *)

let s4_relevant_facts asl w =
  let gdm = s4_divmods w in
  let gm = vfree_in `mcl:num` w in
  let facts = filter (fun th -> let c = concl th in is_num_fact c &&
     (let dm = s4_divmods c in
      dm = [] || exists (fun t -> mem t gdm) dm ||
      (gm && vfree_in `mcl:num` c))) (map snd asl) in
  let grow vs = itlist (fun th acc ->
      let a = s4_atoms(concl th) in
      if intersect a vs <> [] then union a acc else acc) facts vs in
  let vs = grow(grow(s4_atoms w)) in
  filter (fun th -> intersect (s4_atoms(concl th)) vs <> []) facts;;

(* Then, if that fails, also the facts with DIV or MOD that share an atom    *)
(* with the goal.                                                            *)

let S4_ARITH_TAC : tactic = fun (asl,w) ->
  let ths = s4_relevant_facts asl w in
  try (MAP_EVERY MP_TAC ths THEN ARITH_TAC) ([],w) with Failure _ ->
  let ga = s4_atoms w in
  let ths2 = filter (fun th -> let c = concl th in
      is_num_fact c && s4_divmods c <> [] && not(mem th ths) &&
      intersect (s4_atoms c) ga <> []) (map snd asl) in
  if ths2 = [] then failwith "S4_ARITH_TAC" else
  (MAP_EVERY MP_TAC (ths @ ths2) THEN ARITH_TAC) ([],w);;

(* The MOD/DIV elimination of the lib with the same choice of facts.         *)

let S4_MOD_ELIM_CONV (ths:thm list) : conv =
  let is_md op t = is_binary op t && is_numeral(rand t) in
  let asl = map (fun th -> ("",th)) ths in
  let prove_lt tm = TAC_PROOF((asl,tm), S4_ARITH_TAC) in
  let rec go tm =
    let cands = setify(find_terms (fun t -> is_md "MOD" t || is_md "DIV" t) tm) in
    let cands = sort (fun a b -> snappy_term_size a < snappy_term_size b) cands in
    let rec first l = match l with
        [] -> REFL tm
      | t::r ->
          (try let lth = prove_lt (mk_binary "<" (lhand t,rand t)) in
               let eq = if is_md "MOD" t then MATCH_MP MOD_LT lth
                        else MATCH_MP DIV_LT lth in
               let th1 = GEN_REWRITE_CONV ONCE_DEPTH_CONV [eq] tm in
               TRANS th1 (go (rand(concl th1)))
           with Failure _ -> first r) in
    first cands in
  go;;

(* ------------------------------------------------------------------------- *)
(* Facts about match lengths and 64-bit loads.                              *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_MLEN_UNIQUE = prove
 (`!k (src:byte list) a b L.
        L <= k /\ (!t. t < L ==> EL (a + t) src = EL (b + t) src) /\
        (L < k ==> ~(EL (a + L) src = EL (b + L) src))
        ==> snappy_mlen k src a b = L`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_mlen] THENL [ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `L:num` num_CASES) THEN
  REWRITE_TAC[LT_0] THEN STRIP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "t" with Failure _ -> false)) THEN
  REWRITE_TAC[LT_0; ADD_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUC_INJ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC t`) THEN
    ASM_REWRITE_TAC[LT_SUC; ARITH_RULE `(a + 1) + t = a + SUC t`];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
                                   is_binary "<" (lhand(concl th)))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(a + 1) + n = a + SUC n`]]);;

let SNAPPY_MATCH_LENGTH_UNIQUE = prove
 (`!(src:byte list) a b L.
        b + L <= LENGTH src /\
        (!t. t < L ==> EL (a + t) src = EL (b + t) src) /\
        (b + L < LENGTH src ==> ~(EL (a + L) src = EL (b + L) src))
        ==> snappy_match_length src a b = L`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_match_length] THEN
  MATCH_MP_TAC SNAPPY_MLEN_UNIQUE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_ARITH_TAC]);;

let SNAPPY_CTZ_XOR_BYTES = prove
 (`!(x:int64) y.
     (!i. 8 * i + 8 <= word_ctz(word_xor x y)
          ==> word_subword x (8 * i,8):byte = word_subword y (8 * i,8)) /\
     (word_ctz(word_xor x y) < 64
      ==> ~(word_subword x (8 * (word_ctz(word_xor x y) DIV 8),8):byte =
            word_subword y (8 * (word_ctz(word_xor x y) DIV 8),8)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`word_xor x y:int64`; `word_ctz(word_xor x y:int64)`]
    WORD_CTZ_UNIQUE_GEN) THEN
  REWRITE_TAC[DIMINDEX_64; BIT_WORD_XOR] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; DIMINDEX_8] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `8 * i + j`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `MIN 8 8 = 8`] THEN
    ASM_SIMP_TAC[ARITH_RULE `j < 8 /\ 8 * i + 8 <= t /\ t <= 64 ==> 8 * i + j < 64`] THEN
    MESON_TAC[];
    DISCH_TAC THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; DIMINDEX_8] THEN
    DISCH_THEN(MP_TAC o SPEC `word_ctz(word_xor x y:int64) MOD 8`) THEN
    REWRITE_TAC[ARITH_RULE `MIN 8 8 = 8`] THEN
    SIMP_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `8 * (t DIV 8) + t MOD 8 = t`] THEN
    UNDISCH_TAC `word_ctz (word_xor x y:int64) < 64 ==>
                 word_ctz (word_xor x y) < 64 /\
                 ~(bit (word_ctz (word_xor x y)) x <=>
                   bit (word_ctz (word_xor x y)) y)` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let S4_LOAD64_BYTE = prove
 (`!(l:byte list) a i.
        a + 8 <= LENGTH l /\ i < 8
        ==> word_subword (word (snappy_load64 l a):int64) (8 * i,8):byte =
            EL (a + i) l`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SNAPPY_EL_NUM_OF_BYTELIST; ARITH_RULE
   `a + 8 <= l /\ i < 8 ==> a + i < l`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  REWRITE_TAC[snappy_load64] THEN
  ASM_SIMP_TAC[SNAPPY_NUM_OF_SUB_LIST] THEN
  REWRITE_TAC[SNAPPY_EXP_256; MOD_MOD_EXP_MIN; DIV_MOD; DIV_DIV; GSYM EXP_ADD] THEN
  SUBGOAL_THEN
   `MIN (MIN (8 * (a + 8)) (8 * a + 64)) (8 * a + 8 * i + MIN 8 8) =
    8 * (a + i) + 8 /\
    8 * a + 8 * i = 8 * (a + i) /\
    2 EXP (8 * (a + i)) * 256 = 2 EXP (8 * (a + i) + 8)`
   (fun th -> REWRITE_TAC[th; MOD_MOD_REFL]) THEN
  REWRITE_TAC[EXP_ADD; MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;
let SNAPPY_MLEN_GE = prove
 (`!j k (src:byte list) a b.
        j <= k /\ (!t. t < j ==> EL (a + t) src = EL (b + t) src)
        ==> j <= snappy_mlen k src a b`,
  INDUCT_TAC THEN REWRITE_TAC[LE_0] THEN
  INDUCT_TAC THEN REWRITE_TAC[snappy_mlen] THENL [ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LT_0; ADD_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LE_SUC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC t`) THEN
  ASM_REWRITE_TAC[LT_SUC; ARITH_RULE `(a + 1) + t = a + SUC t`]);;

let SNAPPY_MATCH_LENGTH_GE = prove
 (`!(src:byte list) a b j.
        b + j <= LENGTH src /\ (!t. t < j ==> EL (a + t) src = EL (b + t) src)
        ==> j <= snappy_match_length src a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_match_length] THEN
  MATCH_MP_TAC SNAPPY_MLEN_GE THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SNAPPY_MATCH_LENGTH_LE_MISMATCH = prove
 (`!(src:byte list) a b t.
        ~(EL (a + t) src = EL (b + t) src) ==> snappy_match_length src a b <= t`,
  MESON_TAC[SNAPPY_MATCH_LENGTH_MATCH; NOT_LT]);;

let S4_LOAD64_EQ_BYTES = prove
 (`!(src:byte list) a b.
        a + 8 <= LENGTH src /\ b + 8 <= LENGTH src
        ==> (snappy_load64 src a = snappy_load64 src b <=>
             !t. t < 8 ==> EL (a + t) src = EL (b + t) src)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`src:byte list`; `a:num`; `t:num`] S4_LOAD64_BYTE) THEN
    MP_TAC(SPECL [`src:byte list`; `b:num`; `t:num`] S4_LOAD64_BYTE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    DISCH_TAC THEN REWRITE_TAC[snappy_load64] THEN AP_TERM_TAC THEN
    REWRITE_TAC[LIST_EQ] THEN
    ASM_SIMP_TAC[LENGTH_SUB_LIST; ARITH_RULE `a + 8 <= l ==> MIN 8 (l - a) = 8`] THEN
    X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[SNAPPY_EL_SUB_LIST; ARITH_RULE `t < 8 /\ a + 8 <= l ==> a + t < l`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The loops of FindMatchLength.                                             *)
(* ------------------------------------------------------------------------- *)

let s4_has_el th = can (find_term ((=) `EL:num->byte list->byte`)) (concl th);;

let SNAPPY_ELT_STEP_TAC =
  REWRITE_TAC[ARITH_RULE `t < j + 1 <=> t < j \/ t = j`] THEN
  X_GEN_TAC `t:num` THEN STRIP_TAC THENL
  [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
     is_forall(concl th) && s4_has_el th)) THEN ASM_REWRITE_TAC[];
   FIRST_X_ASSUM(MP_TAC o check (fun th ->
     is_neg(concl th) && is_neg(rand(concl th)) && s4_has_el th)) THEN
   ASM_REWRITE_TAC[]];;

let S4_ENSURES_EXISTS_PRE = prove
 (`!(step:A->A->bool) (P:B->A->bool) Q C.
        (!k. ensures step (P k) Q C) ==> ensures step (\s. ?k. P k s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let SNAPPY_WORD_ZX_BYTE_EQ = prove
 (`!x y:byte. val(word_sub (word_zx x:int32) (word_zx y)) = 0 <=> x = y`,
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ; VAL_WORD_ZX_GEN;
              DIMINDEX_8; DIMINDEX_32] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN MP_TAC(ISPEC `y:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN SIMP_TAC[MOD_LT; ARITH_RULE
    `x < 2 EXP 8 ==> x < 2 EXP 32`]);;

let SNAPPY_WORD_ADD_ASSOC_NUM_TAC =
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC; ADD_ASSOC];;

let S4_PC_TAC = SNAPPY_PC_NUM_TAC [VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ];;

(* loop8: the byte loop of FindMatchLength, from loop8 to loop8_exit2 (a     *)
(* mismatch) or join13 (the end of the input).                               *)

let SNAPPY_CF1_LOOP8 = prove
 (`!pc src (inp:byte list) a b k (e:uarch_event list).
     aligned 4096 (word pc:int64) /\ val src + LENGTH inp < 2 EXP 64 /\
     a < b /\ b + k < LENGTH inp /\
     (!t. t < k ==> EL (a + t) inp = EL (b + t) inp)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
               read PC s = word(pc + 14672) /\
               read (memory :> bytes(src,LENGTH inp)) s = num_of_bytelist inp /\
               read X14 s = word_add src (word a) /\
               read X8 s = word k /\
               read X6 s = word_add src (word (b + k)) /\
               read X2 s = word (LENGTH inp - b) /\
               read events s = e)
          (\s. read PC s =
               (if b + snappy_match_length inp a b < LENGTH inp
                then word(pc + 14972) else word(pc + 14704)) /\
               read X8 s = word(snappy_match_length inp a b) /\
               read X6 s = word_add src (word (b + snappy_match_length inp a b)) /\
               read X2 s = word (LENGTH inp - b) /\
               ?e2. read events s = APPEND e2 e /\
                    memaccess_inbounds e2 [src,LENGTH inp] [])
          (MAYCHANGE [PC; X6; X8; X15; X16] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
           MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`arm`;
    `\m s. ?k. m = (LENGTH(inp:byte list) - b) - k /\ b + k < LENGTH inp /\
               (!t. t < k ==> EL (a + t) inp = EL (b + t) inp) /\
               aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
               read PC s = word(pc + 14672) /\
               read (memory :> bytes(src,LENGTH inp)) s = num_of_bytelist inp /\
               read X14 s = word_add src (word a) /\
               read X8 s = word k /\
               read X6 s = word_add src (word (b + k)) /\
               read X2 s = word (LENGTH inp - b) /\
               ?e2. read events s = APPEND e2 e /\
                    memaccess_inbounds e2 [src,LENGTH inp] []`;
    `\s. read PC s =
         (if b + snappy_match_length inp a b < LENGTH inp
          then word(pc + 14972) else word(pc + 14704)) /\
         read X8 s = word(snappy_match_length inp a b) /\
         read X6 s = word_add src (word (b + snappy_match_length inp a b)) /\
         read X2 s = word (LENGTH (inp:byte list) - b) /\
         ?e2. read events s = APPEND e2 e /\
              memaccess_inbounds e2 [src,LENGTH inp] []`;
    `MAYCHANGE [PC; X6; X8; X15; X16] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
     MAYCHANGE [events]`] ENSURES_MEASURE_INDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC];
    DISCH_THEN(MP_TAC o SPEC `(LENGTH(inp:byte list) - b) - k`) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
    REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `k:num` THEN
    SNAPPY_EV_FIRST_TAC THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `arm` S4_ENSURES_EXISTS_PRE)) THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN SNAPPY_EV_CHOOSE_TAC THEN
  SNAPPY_LOAD_TAC [8,`a + j:num`; 8,`b + j:num`] THEN
  ARM_BSTEP_TAC S4_EXEC (1--4) THEN
  ARM_PC_REWRITE_TAC[SNAPPY_WORD_ZX_BYTE_EQ] THEN
  ARM_PC_CASES_TAC NO_TAC THENL
   [BSTEP_FINAL_TAC THEN SNAPPY_EV_FIRST_TAC THEN
    SUBGOAL_THEN `snappy_match_length inp a b = j` SUBST1_TAC THENL
     [MATCH_MP_TAC SNAPPY_MATCH_LENGTH_UNIQUE THEN
      REPEAT CONJ_TAC THENL
       [S4_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC;
        DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      DISJ1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ARM_BSTEP_TAC S4_EXEC (5--8) THEN
  S4_PC_TAC THEN ARM_PC_CASES_TAC NO_TAC THEN BSTEP_FINAL_TAC THEN
  SNAPPY_EV_FIRST_TAC THENL
   [DISJ2_TAC THEN EXISTS_TAC `LENGTH(inp:byte list) - b - (j + 1)` THEN
    CONJ_TAC THENL [S4_ARITH_TAC; EXISTS_TAC `j + 1`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [S4_ARITH_TAC; SNAPPY_ELT_STEP_TAC; REWRITE_TAC[WORD_ADD];
      SNAPPY_WORD_ADD_ASSOC_NUM_TAC];
    DISJ1_TAC THEN
    SUBGOAL_THEN `snappy_match_length inp a b = j + 1` SUBST1_TAC THENL
     [MATCH_MP_TAC SNAPPY_MATCH_LENGTH_UNIQUE THEN REPEAT CONJ_TAC THENL
       [S4_ARITH_TAC; SNAPPY_ELT_STEP_TAC; S4_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL [S4_ARITH_TAC; ALL_TAC] THEN
    SNAPPY_WORD_ADD_ASSOC_NUM_TAC]);;

let S4_SNAPPY_WORD_EQ_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN REPEAT AP_TERM_TAC THEN
  ARITH_TAC;;

let S7_EQ_TAC =
  SUBGOAL_THEN `!t. t < 8 * (j + 1) ==> EL (a + t) inp = EL (b + t) (inp:byte list)`
   ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
     can (find_term ((=) `snappy_load64`)) (concl th))) THEN
   REWRITE_TAC[] THEN
   MP_TAC(SPECL [`inp:byte list`; `a + 8 * j`; `b + 8 * j`] S4_LOAD64_EQ_BYTES) THEN
   ANTS_TAC THENL [S4_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
   DISCH_TAC THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
   ASM_CASES_TAC `t < 8 * j` THENL
    [FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN S4_ARITH_TAC);
     FIRST_X_ASSUM(MP_TAC o SPEC `t - 8 * j` o check (fun th ->
       is_forall(concl th) && s4_has_el th &&
       can (find_term ((=) `(a:num) + 8 * j`)) (concl th))) THEN
     ANTS_TAC THENL [S4_ARITH_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[ARITH_RULE `~(t < 8 * j) ==> (x + 8 * j) + t - 8 * j = x + t`]];
   ALL_TAC];;

let SNAPPY_CF1_LOOP7 = prove
 (`!pc src (inp:byte list) a b i (e:uarch_event list).
     aligned 4096 (word pc:int64) /\ val src + LENGTH inp < 2 EXP 64 /\
     a < b /\ b + 8 * i <= LENGTH inp - 16 /\ 16 <= LENGTH inp /\
     (!t. t < 8 * i ==> EL (a + t) inp = EL (b + t) inp)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
               read PC s = word(pc + 14624) /\
               read (memory :> bytes(src,LENGTH inp)) s = num_of_bytelist inp /\
               read X14 s = word_add src (word a) /\
               read X8 s = word (8 * i) /\
               read X6 s = word_add src (word (b + 8 * i)) /\
               read X10 s = word_add src (word (LENGTH inp - 16)) /\
               read events s = e)
          (\s. read PC s =
               (if snappy_match_length inp a b DIV 8 <
                   (LENGTH inp - 16 - b) DIV 8 + 1
                then word(pc + 14824) else word(pc + 14656)) /\
               read X8 s = word(8 * MIN (snappy_match_length inp a b DIV 8)
                                        ((LENGTH inp - 16 - b) DIV 8 + 1)) /\
               read X6 s = word_add src (word (b + 8 * MIN (snappy_match_length inp a b DIV 8)
                                        ((LENGTH inp - 16 - b) DIV 8 + 1))) /\
               read X2 s = word(snappy_load64 inp (a + 8 * MIN (snappy_match_length inp a b DIV 8)
                                        ((LENGTH inp - 16 - b) DIV 8))) /\
               read X15 s = word(snappy_load64 inp (b + 8 * MIN (snappy_match_length inp a b DIV 8)
                                        ((LENGTH inp - 16 - b) DIV 8))) /\
               read X10 s = word_add src (word (LENGTH inp - 16)) /\
               ?e2. read events s = APPEND e2 e /\
                    memaccess_inbounds e2 [src,LENGTH inp] [])
          (MAYCHANGE [PC; X2; X6; X8; X15] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
           MAYCHANGE [events])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`arm`;
    `\m s. ?i. m = ((LENGTH (inp:byte list) - 16 - b) DIV 8 + 1) - i /\
               b + 8 * i <= LENGTH inp - 16 /\
               (!t. t < 8 * i ==> EL (a + t) inp = EL (b + t) inp) /\
               aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
               read PC s = word(pc + 14624) /\
               read (memory :> bytes(src,LENGTH inp)) s = num_of_bytelist inp /\
               read X14 s = word_add src (word a) /\
               read X8 s = word (8 * i) /\
               read X6 s = word_add src (word (b + 8 * i)) /\
               read X10 s = word_add src (word (LENGTH inp - 16)) /\
               ?e2. read events s = APPEND e2 e /\
                    memaccess_inbounds e2 [src,LENGTH inp] []`;
    `(\s. read PC s =
               (if snappy_match_length inp a b DIV 8 <
                   (LENGTH inp - 16 - b) DIV 8 + 1
                then word(pc + 14824) else word(pc + 14656)) /\
               read X8 s = word(8 * MIN (snappy_match_length inp a b DIV 8)
                                        ((LENGTH inp - 16 - b) DIV 8 + 1)) /\
               read X6 s = word_add src (word (b + 8 * MIN (snappy_match_length inp a b DIV 8)
                                        ((LENGTH inp - 16 - b) DIV 8 + 1))) /\
               read X2 s = word(snappy_load64 inp (a + 8 * MIN (snappy_match_length inp a b DIV 8)
                                        ((LENGTH inp - 16 - b) DIV 8))) /\
               read X15 s = word(snappy_load64 inp (b + 8 * MIN (snappy_match_length inp a b DIV 8)
                                        ((LENGTH inp - 16 - b) DIV 8))) /\
               read X10 s = word_add src (word (LENGTH inp - 16)) /\
               ?e2. read events s = APPEND e2 e /\
                    memaccess_inbounds e2 [src,LENGTH inp] [])`;
    `MAYCHANGE [PC; X2; X6; X8; X15] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
           MAYCHANGE [events]`] ENSURES_MEASURE_INDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC];
    DISCH_THEN(MP_TAC o SPEC `((LENGTH (inp:byte list) - 16 - b) DIV 8 + 1) - i`) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
    REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `i:num` THEN
    SNAPPY_EV_FIRST_TAC THEN ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `arm` S4_ENSURES_EXISTS_PRE)) THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN SNAPPY_EV_CHOOSE_TAC THEN
  SNAPPY_LOAD_TAC [64,`a + 8 * j`; 64,`b + 8 * j`] THEN
  ARM_BSTEP_TAC S4_EXEC (1--4) THEN
  MAP_EVERY (ASSUME_TAC o C SPECL SNAPPY_LOAD64_BOUND)
   [[`inp:byte list`;`a + 8 * j`];[`inp:byte list`;`b + 8 * j`]] THEN
  S4_PC_TAC THEN
  ARM_PC_CASES_TAC NO_TAC THENL
   [BSTEP_FINAL_TAC THEN SNAPPY_EV_FIRST_TAC THEN DISJ1_TAC THEN
    SUBGOAL_THEN `snappy_match_length inp a b DIV 8 = j` SUBST1_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `8 * j <= l /\ l < 8 * j + 8 ==> l DIV 8 = j`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SNAPPY_MATCH_LENGTH_GE THEN ASM_REWRITE_TAC[] THEN
        S4_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
          can (find_term ((=) `snappy_load64`)) (concl th))) THEN
        MP_TAC(SPECL [`inp:byte list`; `a + 8 * j`; `b + 8 * j`]
          S4_LOAD64_EQ_BYTES) THEN
        ANTS_TAC THENL [S4_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
        DISCH_THEN(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC) THEN
        MP_TAC(SPECL [`inp:byte list`; `a:num`; `b:num`; `8 * j + t`]
          SNAPPY_MATCH_LENGTH_LE_MISMATCH) THEN
        ASM_REWRITE_TAC[ADD_ASSOC] THEN S4_ARITH_TAC];
      SUBGOAL_THEN
       `j < (LENGTH(inp:byte list) - 16 - b) DIV 8 + 1 /\
        MIN j ((LENGTH inp - 16 - b) DIV 8 + 1) = j /\
        MIN j ((LENGTH inp - 16 - b) DIV 8) = j`
       (fun th -> REWRITE_TAC[th]) THENL
       [S4_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ARM_BSTEP_TAC S4_EXEC (5--8) THEN
  S4_PC_TAC THEN ARM_PC_CASES_TAC NO_TAC THEN BSTEP_FINAL_TAC THEN
  SNAPPY_EV_FIRST_TAC THEN S7_EQ_TAC THENL
   [DISJ2_TAC THEN
    EXISTS_TAC `((LENGTH (inp:byte list) - 16 - b) DIV 8 + 1) - (j + 1)` THEN
    CONJ_TAC THENL [S4_ARITH_TAC; EXISTS_TAC `j + 1`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY S4_ARITH_TAC THEN S4_SNAPPY_WORD_EQ_TAC;
    DISJ1_TAC THEN
    SUBGOAL_THEN `8 * (j + 1) <= snappy_match_length inp a b` ASSUME_TAC THENL
     [MATCH_MP_TAC SNAPPY_MATCH_LENGTH_GE THEN ASM_REWRITE_TAC[] THEN
      S4_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(LENGTH(inp:byte list) - 16 - b) DIV 8 = j /\
                  j + 1 <= snappy_match_length inp a b DIV 8`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN
        EXISTS_TAC `(LENGTH(inp:byte list) - 16 - b) - 8 * j` THEN
        S4_ARITH_TAC;
        SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN S4_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(snappy_match_length inp a b DIV 8 <
        (LENGTH(inp:byte list) - 16 - b) DIV 8 + 1) /\
      MIN (snappy_match_length inp a b DIV 8)
          ((LENGTH inp - 16 - b) DIV 8 + 1) = j + 1 /\
      MIN (snappy_match_length inp a b DIV 8)
          ((LENGTH inp - 16 - b) DIV 8) = j`
     (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[] THEN S4_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN S4_SNAPPY_WORD_EQ_TAC]);;

(* ------------------------------------------------------------------------- *)
(* loop9 of EmitCopy and the output.                                         *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_READ_BYTES_EXTEND = prove
 (`!(m:(S,int64->byte)component) op d k (l1:byte list) l2 s.
        read (m :> bytes(word_add op (word d),k)) s = num_of_bytelist l1 /\
        LENGTH l1 = k /\
        read (m :> bytes(word_add op (word (d + k)),LENGTH l2)) s =
        num_of_bytelist l2
        ==> read (m :> bytes(word_add op (word d),k + LENGTH l2)) s =
            num_of_bytelist(APPEND l1 l2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(S,int64->byte)component`; `word_add op (word d):int64`;
                 `l1:byte list`; `l2:byte list`; `s:S`] SNAPPY_READ_BYTES_APPEND) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

(* A store of a 32-bit word w at a gives the first k <= 4 bytes.            *)

let SNAPPY_READ_BYTES32_PREFIX = prove
 (`!(m:(S,int64->byte)component) a (w:int32) k s.
        read (m :> bytes32 a) s = w /\ k <= 4
        ==> read (m :> bytes(a,k)) s =
            num_of_bytelist(bytelist_of_num k (val w))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SNAPPY_READ_BYTES_OF_WORD THEN
  ASM_REWRITE_TAC[GSYM BYTES32_WBYTES; DIMINDEX_32] THEN ASM_ARITH_TAC);;
let snappy_reps = new_recursive_definition num_RECURSION
 `(snappy_reps 0 (l:A list) = []) /\
  (snappy_reps (SUC q) l = APPEND (snappy_reps q l) l)`;;

let LENGTH_SNAPPY_REPS = prove
 (`!q (l:A list). LENGTH(snappy_reps q l) = q * LENGTH l`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[snappy_reps; LENGTH; LENGTH_APPEND] THEN
  ARITH_TAC);;

(* loop9 of EmitCopy: q copies of the 3 low bytes of w15 (a 4-byte store    *)
(* each, advancing by 3), from X0 = op + d to op + d + 3 q = X8.             *)

let SNAPPY_CF1_LOOP9 = prove
 (`!pc op d q (w:int64) M (e:uarch_event list).
     aligned 4096 (word pc:int64) /\ 1 <= q /\ val op + d + 3 * q + 1 < 2 EXP 64 /\
     nonoverlapping (op,M) (word pc,libsnappy_rw + libsnappy_rw_size) /\
     d + 3 * q + 1 <= M
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
               read PC s = word(pc + 14912) /\
               read X0 s = word_add op (word d) /\
               read X8 s = word_add op (word (d + 3 * q)) /\
               read X15 s = w /\
               read events s = e)
          (\s. read PC s = word(pc + 14924) /\
               read X0 s = word_add op (word (d + 3 * q)) /\
               read X8 s = word_add op (word (d + 3 * q)) /\
               read X15 s = w /\
               read (memory :> bytes(word_add op (word d),3 * q)) s =
               num_of_bytelist
                (snappy_reps q (bytelist_of_num 3 (val(word_zx w:int32)))) /\
               ?e2. read events s = APPEND e2 e /\
                    memaccess_inbounds e2 [] [op,M])
          (MAYCHANGE [PC; X0] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
           MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(word_add op (word d),3 * q + 1)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `l = bytelist_of_num 3 (val(word_zx (w:int64):int32))` THEN
  MP_TAC(ISPECL [`arm`;
    `\m s. ?i. m = q - i /\ i < q /\
         aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
         read PC s = word(pc + 14912) /\
         read X0 s = word_add op (word (d + 3 * i)) /\
         read X8 s = word_add op (word (d + 3 * q)) /\
         read X15 s = w /\
         read (memory :> bytes(word_add op (word d),3 * i)) s =
         num_of_bytelist(snappy_reps i (l:byte list)) /\
         ?e2. read events s = APPEND e2 e /\
              memaccess_inbounds e2 [] [op,M]`;
    `\s. read PC s = word(pc + 14924) /\
         read X0 s = word_add op (word (d + 3 * q)) /\
         read X8 s = word_add op (word (d + 3 * q)) /\
         read X15 s = w /\
         read (memory :> bytes(word_add op (word d),3 * q)) s =
         num_of_bytelist (snappy_reps q (l:byte list)) /\
         ?e2. read events s = APPEND e2 e /\
              memaccess_inbounds e2 [] [op,M]`;
    `MAYCHANGE [PC; X0] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
     MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(word_add op (word d),3 * q + 1)]`]
    ENSURES_MEASURE_INDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC];
    DISCH_THEN(MP_TAC o SPEC `q:num`) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_PRECONDITION_THM) THEN
    REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `0` THEN
    SNAPPY_EV_FIRST_TAC THEN ASM_REWRITE_TAC[snappy_reps; MULT_CLAUSES; ADD_CLAUSES; SUB_0;
                    READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
                    num_of_bytelist] THEN
    ASM_ARITH_TAC] THEN
  X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPEC `arm` S4_ENSURES_EXISTS_PRE)) THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN SNAPPY_EV_CHOOSE_TAC THEN
  ARM_BSTEP_TAC S4_EXEC (1--3) THEN
  S4_PC_TAC THEN ARM_PC_CASES_TAC NO_TAC THEN BSTEP_FINAL_TAC THEN
  SNAPPY_EV_FIRST_TAC THEN
  (MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `op:int64`; `d:num`; `3 * i`;
   `snappy_reps i (l:byte list)`; `l:byte list`; `s3:armstate`] SNAPPY_READ_BYTES_EXTEND) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[LENGTH_SNAPPY_REPS] THEN EXPAND_TAC "l" THEN
   REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC SNAPPY_READ_BYTES32_PREFIX THEN ASM_REWRITE_TAC[ARITH_RULE `3 <= 4`];
   ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(l:byte list) = 3` SUBST1_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 snappy_reps); ARITH_RULE `3 * i + 3 = 3 * SUC i`] THEN
  DISCH_TAC) THENL
   [DISJ2_TAC THEN EXISTS_TAC `q - SUC i` THEN
    CONJ_TAC THENL [S4_ARITH_TAC; EXISTS_TAC `SUC i`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY S4_ARITH_TAC THEN
    REWRITE_TAC[ADD1] THEN S4_SNAPPY_WORD_EQ_TAC;
    DISJ1_TAC THEN SUBGOAL_THEN `q = SUC i` SUBST_ALL_TAC THENL
     [S4_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD1] THEN S4_SNAPPY_WORD_EQ_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The tags of EmitCopy as the compiled code computes them, as byte lists.    *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CF1_S4_AND224 = prove
 (`!x:int64. val x < 2048
       ==> val(word_and (word_zx (word_ushr x 3):int32) (word 224)) =
           32 * (val x DIV 256)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[BITBLAST_RULE
   `word_and (word_zx (word_ushr (x:int64) 3):int32) (word 224) =
    word_shl (word_and (word_zx (word_ushr x 8)) (word 7)) 5`] THEN
  SUBGOAL_THEN `word 7:int32 = word(2 EXP 3 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[WORD_AND_MASK_WORD]] THEN
  REWRITE_TAC[VAL_WORD_SHL; VAL_WORD; VAL_WORD_ZX_GEN; VAL_WORD_USHR;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(x:int64) DIV 256 < 8` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
  DISCH_TAC THEN
  NUM_MOD_ELIM_TAC THEN REFL_TAC);;

let SNAPPY_CF1_S4_BYTES2 = prove
 (`!v. bytelist_of_num 2 v = [word(v MOD 256); word((v DIV 256) MOD 256)]`,
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; bytelist_of_num]);;

let SNAPPY_CF1_S4_BYTES3 = prove
 (`!v. bytelist_of_num 3 v =
       [word(v MOD 256); word((v DIV 256) MOD 256);
        word((v DIV 256 DIV 256) MOD 256)]`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; bytelist_of_num]);;

(* copy1: (off >> 3 & 0xe0) + (off << 8) + 4 len - 15, len < 12, off < 2048 *)

let SNAPPY_CF1_S4_COPY1 = prove
 (`!off len.
        0 < off /\ off < 2048 /\ 4 <= len /\ len < 12
        ==> bytelist_of_num 2
              (val(word_sub
                    (word_add
                      (word_and (word_zx (word_ushr (word off:int64) 3):int32)
                                (word 224))
                      (word_add (word_shl (word_zx (word off:int64)) 8)
                                (word_shl (word_zx (word len:int64)) 2)))
                    (word 15))) =
            snappy_emit_copy64 off len`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word off:int64) = off /\ val(word len:int64) = len`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `word off:int64` SNAPPY_CF1_S4_AND224) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `val(word_sub
         (word_add
           (word_and (word_zx (word_ushr (word off:int64) 3):int32) (word 224))
           (word_add (word_shl (word_zx (word off:int64)) 8)
                     (word_shl (word_zx (word len:int64)) 2)))
         (word 15)) =
    (32 * (off DIV 256) + 4 * len - 15) + 256 * off`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `off DIV 256 < 8` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_ADD; VAL_WORD_SHL; VAL_WORD_ZX_GEN;
                DIMINDEX_32; DIMINDEX_64; VAL_WORD] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    NUM_MOD_ELIM_TAC THEN COND_CASES_TAC THEN NUM_MOD_ELIM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SNAPPY_CF1_S4_BYTES2; snappy_emit_copy64] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN
  SUBGOAL_THEN `32 * off DIV 256 + 4 * len - 15 < 256` ASSUME_TAC THENL
   [SUBGOAL_THEN `off DIV 256 < 8` MP_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; DIV_LT; ADD_CLAUSES] THEN
  REWRITE_TAC[CONS_11] THEN REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let SNAPPY_CF1_S4_COPY1B = prove
 (`!off len.
        0 < off /\ off < 2048 /\ 4 <= len /\ len < 12
        ==> bytelist_of_num 2
              (val(word_add
                    (word_sub
                      (word_and (word_zx (word_ushr (word off:int64) 3):int32)
                                (word 224)) (word 15))
                    (word_add (word_shl (word_zx (word off:int64)) 8)
                              (word_shl (word_zx (word len:int64)) 2)))) =
            snappy_emit_copy64 off len`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`off:num`; `len:num`] SNAPPY_CF1_S4_COPY1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* The numeric value of the 3-byte tags, and their bytes.                    *)

let SNAPPY_CF1_S4_TAG3 = prove
 (`!off t. off < 65536 /\ t < 256
           ==> bytelist_of_num 3 (t + 256 * off) =
               [word t; word(off MOD 256); word(off DIV 256)]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SNAPPY_CF1_S4_BYTES3] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; MOD_LT; DIV_LT;
               ADD_CLAUSES] THEN
  REWRITE_TAC[CONS_11] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOD_LT THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
  ASM_ARITH_TAC);;

let SNAPPY_CF1_S4_SHL8_VAL = prove
 (`!off t. off < 65536 /\ t < 256
           ==> val(word_add (word_shl (word_zx (word off:int64):int32) 8)
                            (word t)) = t + 256 * off`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  NUM_MOD_ELIM_TAC THEN ARITH_TAC);;

let SNAPPY_CF1_S4_COPY2 = prove
 (`!off len.
        0 < off /\ off < 65536 /\ 1 <= len /\ len <= 64 /\
        ~(len < 12 /\ off < 2048)
        ==> bytelist_of_num 3
              (val(word_sub
                    (word_add (word_shl (word_zx (word off:int64)) 8)
                              (word_shl (word_zx (word len:int64)) 2))
                    (word 2):int32)) =
            snappy_emit_copy64 off len`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[snappy_emit_copy64] THEN
  SUBGOAL_THEN
   `word_sub (word_add (word_shl (word_zx (word off:int64)) 8)
                       (word_shl (word_zx (word len:int64)) 2)) (word 2):int32 =
    word_add (word_shl (word_zx (word off:int64)) 8) (word (2 + 4 * (len - 1)))`
   SUBST1_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (word_add a b) c = word_add a (word_sub b c)`] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUB_CASES; VAL_WORD_SHL; VAL_WORD_ZX_GEN;
                VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    NUM_MOD_ELIM_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SNAPPY_CF1_S4_SHL8_VAL; ARITH_RULE
   `1 <= len /\ len <= 64 ==> 2 + 4 * (len - 1) < 256`] THEN
  MATCH_MP_TAC SNAPPY_CF1_S4_TAG3 THEN ASM_ARITH_TAC);;

let SNAPPY_CF1_S4_COPYK = prove
 (`!off k. 0 < off /\ off < 65536 /\ (k = 60 \/ k = 64)
           ==> bytelist_of_num 3
                 (val(word_add (word_shl (word_zx (word off:int64)) 8)
                               (word (2 + 4 * (k - 1))):int32)) =
               snappy_emit_copy64 off k`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[snappy_emit_copy64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[SNAPPY_CF1_S4_SHL8_VAL; ARITH_RULE `238 < 256 /\ 254 < 256`] THEN
  MATCH_MP_TAC SNAPPY_CF1_S4_TAG3 THEN ASM_ARITH_TAC);;

let SNAPPY_CF1_S4_EC_SMALL = prove
 (`!off len. len <= 64 ==> snappy_emit_copy off len = snappy_emit_copy64 off len`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [snappy_emit_copy] THEN
  ASM_SIMP_TAC[ARITH_RULE `len <= 64 ==> ~(68 <= len) /\ ~(64 < len)`]);;

let SNAPPY_CF1_S4_EC_MID = prove
 (`!off len. 64 < len /\ len < 68
             ==> snappy_emit_copy off len =
                 APPEND (snappy_emit_copy64 off 60) (snappy_emit_copy64 off (len - 60))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [snappy_emit_copy] THEN
  ASM_SIMP_TAC[ARITH_RULE `len < 68 ==> ~(68 <= len)`]);;

let SNAPPY_CF1_S4_REPS_COMM = prove
 (`!q (l:A list). APPEND l (snappy_reps q l) = APPEND (snappy_reps q l) l`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[snappy_reps; APPEND; APPEND_NIL] THEN
  ASM_REWRITE_TAC[APPEND_ASSOC]);;

let SNAPPY_CF1_S4_EC_REPS = prove
 (`!off q len. 64 * q + 4 <= len
               ==> snappy_emit_copy off len =
                   APPEND (snappy_reps q (snappy_emit_copy64 off 64))
                          (snappy_emit_copy off (len - 64 * q))`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[snappy_reps; APPEND; MULT_CLAUSES; SUB_0] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [snappy_emit_copy] THEN
  SUBGOAL_THEN `68 <= len` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `len - 64`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[APPEND_ASSOC; SNAPPY_CF1_S4_REPS_COMM] THEN
  REWRITE_TAC[ARITH_RULE `len - 64 - 64 * q = len - (64 + 64 * q)`]);;

(* The same with the offset and the length as any words with those values.  *)

let SNAPPY_CF1_S4_COPY1_GEN = prove
 (`!x y off len.
        val x = off /\ val y = len /\
        0 < off /\ off < 2048 /\ 4 <= len /\ len < 12
        ==> bytelist_of_num 2
              (val(word_sub
                    (word_add
                      (word_and (word_zx (word_ushr (x:int64) 3):int32)
                                (word 224))
                      (word_add (word_shl (word_zx x) 8)
                                (word_shl (word_zx (y:int64)) 2)))
                    (word 15))) =
            snappy_emit_copy64 off len`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> SUBST1_TAC(SYM(ISPEC t WORD_VAL))) [`x:int64`; `y:int64`] THEN
  ASM_SIMP_TAC[SNAPPY_CF1_S4_COPY1]);;

let SNAPPY_CF1_S4_COPY1B_GEN = prove
 (`!x y off len.
        val x = off /\ val y = len /\
        0 < off /\ off < 2048 /\ 4 <= len /\ len < 12
        ==> bytelist_of_num 2
              (val(word_add
                    (word_sub
                      (word_and (word_zx (word_ushr (x:int64) 3):int32)
                                (word 224)) (word 15))
                    (word_add (word_shl (word_zx x) 8)
                              (word_shl (word_zx (y:int64)) 2)))) =
            snappy_emit_copy64 off len`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> SUBST1_TAC(SYM(ISPEC t WORD_VAL))) [`x:int64`; `y:int64`] THEN
  ASM_SIMP_TAC[SNAPPY_CF1_S4_COPY1B]);;

let SNAPPY_CF1_S4_COPY2_GEN = prove
 (`!x y off len.
        val x = off /\ val y = len /\
        0 < off /\ off < 65536 /\ 1 <= len /\ len <= 64 /\
        ~(len < 12 /\ off < 2048)
        ==> bytelist_of_num 3
              (val(word_sub
                    (word_add (word_shl (word_zx (x:int64)) 8)
                              (word_shl (word_zx (y:int64)) 2))
                    (word 2):int32)) =
            snappy_emit_copy64 off len`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> SUBST1_TAC(SYM(ISPEC t WORD_VAL))) [`x:int64`; `y:int64`] THEN
  ASM_SIMP_TAC[SNAPPY_CF1_S4_COPY2]);;

let SNAPPY_CF1_S4_COPY60_GEN = prove
 (`!x off. val x = off /\ 0 < off /\ off < 65536
           ==> bytelist_of_num 3
                 (val(word_add (word_shl (word_zx (x:int64)) 8)
                               (word 238):int32)) =
               snappy_emit_copy64 off 60`,
  REPEAT STRIP_TAC THEN SUBST1_TAC(SYM(ISPEC `x:int64` WORD_VAL)) THEN
  MP_TAC(SPECL [`off:num`; `60`] SNAPPY_CF1_S4_COPYK) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let SNAPPY_CF1_S4_COPY64_GEN = prove
 (`!x off. val x = off /\ 0 < off /\ off < 65536
           ==> bytelist_of_num 3
                 (val(word_add (word_shl (word_zx (x:int64)) 8)
                               (word 254):int32)) =
               snappy_emit_copy64 off 64`,
  REPEAT STRIP_TAC THEN SUBST1_TAC(SYM(ISPEC `x:int64` WORD_VAL)) THEN
  MP_TAC(SPECL [`off:num`; `64`] SNAPPY_CF1_S4_COPYK) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* Register facts in canonical forms.                                         *)

let S4_MOD_ELIM_TAC : tactic = fun (asl,w) ->
  let bs = snappy_load_bounds w in
  (MAP_EVERY ASSUME_TAC bs THEN
   CONV_TAC (S4_MOD_ELIM_CONV (bs @ map snd asl))) (asl,w);;

let SNAPPY_REG_NUM_TAC : tactic =
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC (VAL_WORD_SUB_CASES :: SNAPPY_VAL_THMS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN S4_MOD_ELIM_TAC THEN
  REPEAT(COND_CASES_TAC THEN S4_MOD_ELIM_TAC) THEN
  S4_ARITH_TAC;;

let SNAPPY_REG_EQ_TAC : tactic =
  FIRST [REFL_TAC; S4_SNAPPY_WORD_EQ_TAC; SNAPPY_REG_NUM_TAC];;

(* Replace the facts read c s = v0 by read c s = v, proving v0 = v.          *)
let S4_SNAPPY_SET_REGS_TAC (cvs:(term*term) list) : tactic =
  let one (c,v) (asl,w) =
    let n,th = find (fun (_,th) -> try lhand(lhs(concl th)) = c with Failure _ -> false) asl in
    let v0 = rand(concl th) in
    let eq = TAC_PROOF((asl,mk_eq(v0,v)), SNAPPY_REG_EQ_TAC) in
    (UNDISCH_THEN (concl th) (fun th -> ASSUME_TAC(TRANS th eq))) (asl,w) in
  MAP_EVERY one cvs;;

(* ------------------------------------------------------------------------- *)
(* A driver for the segment: steps one instruction at a time, splits at the  *)
(* branches (killing the cases that the arithmetic facts contradict), runs   *)
(* hooks at given PC offsets (Pre: before stepping the instruction; Call: in *)
(* place of stepping, e.g. through a loop lemma), and stops at the given PC  *)
(* offsets (absolute numerals k of word(pc + k)).                            *)
(* ------------------------------------------------------------------------- *)

(* The case condition of the split made last (the newest numeric fact)     *)
(* refuted with the facts that share atoms with it (S4_ARITH_TAC above): *)
(* with all the facts, the decision procedure, which numbers the atoms by    *)
(* genvar, took more than 40 GB in some orders of the atoms, i.e. depending  *)
(* on what the proof did before.                                             *)

let S4_SNAPPY_CONTR_TAC : tactic = fun (asl,w) ->
  match filter (fun (_,th) -> is_num_fact(concl th)) asl with
    (_,c)::_ -> (MATCH_MP_TAC(TAUT `F ==> p`) THEN MP_TAC c THEN
                 S4_ARITH_TAC) (asl,w)
  | [] -> failwith "S4_SNAPPY_CONTR_TAC";;

let S4_PC_NUM_TAC (extra:thm list) : tactic = fun (asl,w) ->
  let ths = map snd asl in
  let dec = TOP_DEPTH_CONV (fun t -> SNAPPY_DECIDE_CONV asl [] t) in
  RULE_ASSUM_TAC(fun th -> if is_pc_cond_fact th then
      let ths = snappy_load_bounds (concl th) @ ths in
      CONV_RULE(RAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV
        (REWRITE_CONV (extra @ VAL_WORD_SUB_CASES :: SNAPPY_VAL_THMS) THENC
         NUM_REDUCE_CONV THENC
         S4_MOD_ELIM_CONV ths THENC dec THENC
         REWRITE_CONV (VAL_WORD_SUB_CASES :: SNAPPY_VAL_THMS) THENC NUM_REDUCE_CONV THENC
         S4_MOD_ELIM_CONV ths THENC
         REWRITE_CONV[LT_ADD_LCANCEL; LE_ADD_LCANCEL; EQ_ADD_LCANCEL]))))) th
    else th) (asl,w);;

let S4_PC_TAC = S4_PC_NUM_TAC [VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ];;

(* A hook is (false,tac): tac then step; (true,tac): tac in place of the step. *)
let s4_pre (t:tactic) = (false,t) and s4_call (t:tactic) = (true,t);;

let s4_counter = par_local_ref (fun () -> 1000);;
let s4_rewrites = par_local_ref (fun () -> ([]:thm list));;

let s4_goal_state w =
  match w with
    Comb(Comb(Comb(Const("eventually",_),_),_),s) -> Some s
  | _ -> None;;

let s4_pc_value asl s =
  rand(concl(snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),_) ->
        s' = s
    | _ -> false) asl)));;

let s4_pc_offset v =
  match v with
    Comb(Const("word",_),Comb(Comb(Const("+",_),_),k)) when is_numeral k ->
      Some(dest_small_numeral k)
  | _ -> None;;

let S4_STEP_TAC : tactic = fun g ->
  incr (s4_counter ());
  let k = !(s4_counter ()) in
  ARM_BSTEP_TAC ~rewrites:(!(s4_rewrites ())) S4_EXEC (k--k) g;;

(* The case split on a branch condition c, in the form c1 with             *)
(* a <= b /\ ~(a = b) as a < b and negated comparisons turned around, so     *)
(* that the facts of the cases are atoms for the arithmetic (a negated       *)
(* conjunction is a disjunction, and the decision procedure splits them all, *)
(* which blows up after a few branches).                                     *)

let S4_CASES_TAC (dec:tactic) : tactic = fun (asl,w) ->
  let s = match s4_goal_state w with Some s -> s | None -> failwith "S4_CASES_TAC" in
  match (try Some(snd(find (fun (_,th) -> is_pc_cond_fact th &&
                                         rand(lhand(concl th)) = s) asl))
         with Failure _ -> None) with
    None -> ALL_TAC (asl,w)
  | Some th ->
  let r = rand(concl th) in
  let c0 = rand(rator(rator r)) in
  let eq1 = REWRITE_CONV[GSYM LT_LE; NOT_LT; NOT_LE;
    ARITH_RULE `!m n. m <= n /\ ~(n = m) <=> m < n`] c0 in
  let c = rand(concl eq1) in
  let fix b =
    let cth = if b then EQT_INTRO(EQ_MP (SYM eq1) (ASSUME c))
              else EQF_INTRO(EQ_MP (SYM(AP_TERM `(~)` eq1)) (ASSUME(mk_neg c))) in
    UNDISCH_THEN (concl th) (fun pth ->
       ASSUME_TAC(PURE_ONCE_REWRITE_RULE[COND_CLAUSES]
         (CONV_RULE(RAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV(K cth))))) pth))) in
  (ASM_CASES_TAC c THENL [fix true THEN TRY dec; fix false THEN TRY dec]) (asl,w);;

(* Run up to (not including) a step whose PC is not constant or is one of the *)
(* offsets ks.                                                                *)

let S4_BLOCK_TAC (ks:int list) : tactic = fun g ->
  incr (s4_counter ());
  let k = !(s4_counter ()) in
  s4_counter () := k + 1000;
  let stop pc = match s4_pc_offset pc with None -> true | Some n -> mem n ks in
  BSTEP_RUN_TAC arm_bstep_arch ~rewrites:(!(s4_rewrites ())) ~stop ~first:k S4_EXEC
    500 ("s" ^ string_of_int k) g;;

let rec S4_RUN_TAC (hooks:(int * (bool * tactic)) list) (stops:int list) : tactic =
  fun (asl,w) ->
  match s4_goal_state w with
    None -> ALL_TAC (asl,w)
  | Some s ->
  let v = s4_pc_value asl s in
  match s4_pc_offset v with
    None ->
      (S4_PC_TAC THEN S4_CASES_TAC S4_SNAPPY_CONTR_TAC THEN
       S4_RUN_TAC hooks stops) (asl,w)
  | Some n ->
      if mem n stops then ALL_TAC (asl,w) else
      match (try Some(assoc n hooks) with Failure _ -> None) with
        Some(false,h) -> (h THEN S4_STEP_TAC THEN S4_RUN_TAC hooks stops) (asl,w)
      | Some(true,h) -> (h THEN S4_RUN_TAC hooks stops) (asl,w)
      | None -> (S4_BLOCK_TAC (stops @ map fst hooks) THEN
                 S4_RUN_TAC hooks stops) (asl,w);;

(* The PC offset of the goal, for THENL-free dispatch on the stop points.    *)

let S4_AT_TAC (cases:(int * tactic) list) : tactic = fun (asl,w) ->
  match s4_goal_state w with
    None -> failwith "S4_AT_TAC: not at a state"
  | Some s ->
      match s4_pc_offset(s4_pc_value asl s) with
        Some n -> (try assoc n cases with Failure _ ->
                    failwith ("S4_AT_TAC: no case for " ^ string_of_int n)) (asl,w)
      | None -> failwith "S4_AT_TAC: PC not constant";;

(* Pointer facts read c s = word_add (word_add src (word a)) (word b) as     *)
(* word_add src (word (a + b)).                                              *)

let S4_CANON_TAC (cs:term list) =
  SNAPPY_REWRITE_FACTS_TAC cs [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];;

(* The address in register c as word_add src (word p): p.                    *)

let s4_reg_offset asl s c =
  let v = rand(concl(snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s')),_) ->
        c' = c && s' = s
    | _ -> false) asl))) in
  match v with
    Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),p)) -> p
  | _ -> failwith "s4_reg_offset";;

(* Load facts at the address in register c plus delta.                      *)

let S4_LOAD_REG_TAC (k:int) (c:term) (delta:int) : tactic = fun (asl,w) ->
  match s4_goal_state w with
    None -> failwith "S4_LOAD_REG_TAC" | Some s ->
  let p = s4_reg_offset asl s c in
  let p' = if delta = 0 then p else mk_binary "+" (p,mk_small_numeral delta) in
  SNAPPY_LOAD_TAC [k,p'] (asl,w);;

(* The register values of a state.                                           *)

let s4_reg_value asl s c =
  rand(concl(snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s')),_) ->
        c' = c && s' = s
    | _ -> false) asl)));;

let s4_state (asl,w) =
  match s4_goal_state w with Some s -> s | None -> failwith "s4_state";;

(* The hypotheses of a lemma about the match: facts, arithmetic, and the     *)
(* bytes below the match length.                                             *)

let S4_HYP_TAC : tactic =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; S4_ARITH_TAC;
         X_GEN_TAC `t:num` THEN DISCH_TAC THEN
         MATCH_MP_TAC SNAPPY_MATCH_LENGTH_MATCH THEN
         ASM_REWRITE_TAC[] THEN S4_ARITH_TAC];;

let S4_SNAPPY_LEMMA_CALL_TAC (lth:thm) (sname:string) : tactic = fun (asl,w) ->
  let lth = if is_forall(concl lth) then SPEC (snappy_current_events (asl,w)) lth
            else lth in
  let ant = lhand(concl lth) in
  let ath = TAC_PROOF((asl,ant), S4_HYP_TAC) in
  ARM_BSTEP_CALL_TAC S4_EXEC (MP lth ath) sname (asl,w);;

let S4_ML_TAC =
  SNAPPY_REWRITE_FACTS_TAC [`X2`;`X6`;`X8`;`X15`;`PC`]
    [ASSUME `snappy_match_length inp (c + 4) (ip + 4) = ML`];;

let S4_L8_HOOK : tactic = fun (asl,w) ->
  let s = s4_state (asl,w) in
  let k = rand(s4_reg_value asl s `X8`) in
  incr (s4_counter ());
  (S4_SNAPPY_SET_REGS_TAC
    [`X2`,`word(LENGTH(inp:byte list) - (ip + 4)):int64`;
     `X14`,`word_add src (word (c + 4)):int64`;
     `X6`,mk_comb(`word_add (src:int64)`,
                  mk_comb(`word:num->int64`,mk_binary "+" (`ip + 4`,k)))] THEN
   S4_SNAPPY_LEMMA_CALL_TAC
    (SPECL [`pc:num`;`src:int64`;`inp:byte list`;`c + 4`;`ip + 4`;k]
       SNAPPY_CF1_LOOP8) ("s" ^ string_of_int !(s4_counter ())) THEN
   S4_ML_TAC) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The tail from join8: the table updates and the check for the next match.  *)
(* ip2 = ip + 4 + ML is the new ip.                                           *)
(* ------------------------------------------------------------------------- *)

(* The data register X5 as word(load64 inp q DIV 2 EXP (8 * r)), r <= 3,     *)
(* q + r = ip2, and the rewrites of its low 32 bits as load32 inp ip2.        *)

let s4_data_parts v =
  match v with
    Comb(Const("word",_),Comb(Comb(Const("DIV",_),
      Comb(Comb(Const("snappy_load64",_),_),q)),
      Comb(Comb(Const("EXP",_),_),Comb(Comb(Const("*",_),_),r)))) -> q,r
  | Comb(Const("word",_),Comb(Comb(Const("snappy_load64",_),_),q)) -> q,`0`
  | _ -> failwith "s4_data_parts";;

let S4_DATA_TAC : tactic = fun (asl,w) ->
  let s = s4_state (asl,w) in
  let q,r = s4_data_parts (s4_reg_value asl s `X5`) in
  let v = `word(snappy_load64 inp q DIV 2 EXP (8 * r)):int64` in
  let v = subst [q,`q:num`; r,`r:num`]
           `word(snappy_load64 (inp:byte list) q DIV 2 EXP (8 * r)):int64` in
  let lth = SPECL [`inp:byte list`; q; r] SNAPPY_LOAD64_SHIFT_LOW32 in
  let ant = lhand(concl lth) in
  let ath = TAC_PROOF((asl,ant), CONJ_TAC THEN S4_ARITH_TAC) in
  let qr = mk_binary "+" (q,r) in
  let eq = TAC_PROOF((asl,mk_eq(qr,`ip2:num`)), S4_ARITH_TAC) in
  let th = REWRITE_RULE[eq] (MP lth ath) in
  let lth' = SPECL [`inp:byte list`; q; mk_binary "+" (r,`1`)]
               SNAPPY_LOAD64_SHIFT_LOW32 in
  let ath' = TAC_PROOF((asl,lhand(concl lth')), CONJ_TAC THEN S4_ARITH_TAC) in
  let eq' = TAC_PROOF((asl,mk_eq(mk_binary "+" (q,mk_binary "+" (r,`1`)),
                                 `ip2 + 1`)), S4_ARITH_TAC) in
  let th' = REWRITE_RULE[eq'] (MP lth' ath') in
  s4_rewrites () := [th; th'];
  (S4_SNAPPY_SET_REGS_TAC [`X5`,v] THEN ASSUME_TAC th THEN ASSUME_TAC th') (asl,w);;

let S4_TSPLIT_TAC h = SNAPPY_TABLE_SPLIT_TAC h
  (EXPAND_TAC (fst(dest_var h)) THEN MATCH_MP_TAC SNAPPY_HASH1_LT THEN
   S4_ARITH_TAC);;

(* At join8 + 8 (ldur w4, [x6, #-1]), after the check against ip_limit.      *)

let S4_HA : tactic =
  S4_SNAPPY_SET_REGS_TAC [`X6`,`word_add src (word (ip + 4 + ML)):int64`;
                       `X1`,`word_add src (word (ip + 4 + ML)):int64`] THEN
  SNAPPY_ABBREV_TAC `ip2 = ip + 4 + ML` THEN
  S4_DATA_TAC THEN
  SNAPPY_LOAD_TAC [32,`ip2 - 1`] THEN
  W(fun (asl,w) ->
    let ath = TAC_PROOF((asl,
      `word_add src (word (ip2 + 18446744073709551615)):int64 =
       word_add src (word (ip2 - 1))`),
      AP_TERM_TAC THEN
      SUBGOAL_THEN `ip2 + 18446744073709551615 = 1 * 2 EXP 64 + (ip2 - 1)`
       SUBST1_TAC THENL [S4_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_MULT_ADD]) in
    s4_rewrites () := ath :: !(s4_rewrites ()); ALL_TAC);;

(* word_zx (word_zx (word (2 * h))) = word (2 * h) for the index h < ts.     *)

let s4_zx_index asl h =
  let tm = subst [h,`h:num`]
    `word_zx (word_zx (word (2 * h):int64):int32):int64 = word (2 * h)` in
  TAC_PROOF((asl,tm),
    REWRITE_TAC[SNAPPY_WORD_ZX_WORD_64_32] THEN REWRITE_TAC[word_zx] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN
    S4_ARITH_TAC);;

(* At the strh of entry h1 (+0x288): the indices as words.                   *)

let S4_HB : tactic = fun (asl,w) ->
  let ths = [MATCH_MP SNAPPY_HASH1_WORD
              (ASSUME `snappy_table_size (LENGTH(inp:byte list)) = ts`);
             MATCH_MP SNAPPY_HASH1_WORD_ALT
              (ASSUME `snappy_table_size (LENGTH(inp:byte list)) = ts`);
             SNAPPY_VAL_WORD_LOAD32] in
  (SNAPPY_REWRITE_FACTS_TAC [`X2`;`X4`] ths THEN
   SNAPPY_ABBREV_TAC `h1 = snappy_hash1 ts (snappy_load32 inp (ip2 - 1))` THEN
   SNAPPY_ABBREV_TAC `h2 = snappy_hash1 ts (snappy_load32 inp ip2)` THEN
   S4_TSPLIT_TAC `h1:num` THEN
   W(fun (asl,w) -> s4_rewrites () := s4_zx_index asl `h1:num` :: !(s4_rewrites ());
                    ALL_TAC)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Merging a store of a tag (k bytes of a 32-bit store) into the fact        *)
(* read (memory :> bytes(op,LENGTH l)) s = num_of_bytelist l of the output.   *)
(* ------------------------------------------------------------------------- *)

let s4_is_out_fact s th =
  match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),
      Const("memory",_)),Comb(Const("bytes",_),Comb(Comb(Const(",",_),
      Var("op",_)),Comb(Const("LENGTH",_),_))))),s')),
      Comb(Const("num_of_bytelist",_),_)) -> s' = s
  | _ -> false;;

let s4_is_store32 s th =
  match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),
      Const("memory",_)),Comb(Const("bytes32",_),a))),s')),_) ->
        s' = s && can (find_term ((=) `op:int64`)) a
  | _ -> false;;

let S4_MERGE_TAC (k:int) : tactic = fun (asl,w) ->
  let s = s4_state (asl,w) in
  let pth = snd(find (fun (_,th) -> s4_is_out_fact s th) asl) in
  let l1 = rand(rand(concl pth)) in
  let d = mk_comb(`LENGTH:byte list->num`,l1) in
  let a' = mk_comb(`word_add (op:int64)`,mk_comb(`word:num->int64`,d)) in
  let one (_,sth) =
    if not(s4_is_store32 s sth) then failwith "S4_MERGE_TAC" else
    let a = rand(rand(lhand(lhs(concl sth)))) in
    let aeq = TAC_PROOF((asl,mk_eq(a,a')),
       REWRITE_TAC[LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM; LENGTH_SNAPPY_REPS] THEN
       REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
       TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC)) in
    let sth' = GEN_REWRITE_RULE
                 (LAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV)
                 [aeq] sth in
    let v = rand(concl sth) in
    let kt = mk_small_numeral k in
    let bth = MP (ISPECL [`memory:(armstate,int64->byte)component`; a'; v; kt; s]
                    SNAPPY_READ_BYTES32_PREFIX)
                 (CONJ sth' (ARITH_RULE(mk_binary "<=" (kt,`4`)))) in
    let l2 = rand(rand(concl bth)) in
    let lth = ISPECL [`memory:(armstate,int64->byte)component`; `op:int64`;
                      l1; l2; s] SNAPPY_READ_BYTES_APPEND in
    let bth' = CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV
                 (K(SYM(ISPECL [kt; rand l2] LENGTH_BYTELIST_OF_NUM))))))))) bth in
    MP lth (CONJ pth bth') in
  (try ASSUME_TAC(tryfind one asl) with Failure _ -> ALL_TAC) (asl,w);;

(* The loop9 output (q copies) into the output fact.                         *)

let S4_MERGE_REPS_TAC : tactic = fun (asl,w) ->
  let s = s4_state (asl,w) in
  let rth = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),
        Const("memory",_)),Comb(Const("bytes",_),_))),s')),
        Comb(Const("num_of_bytelist",_),Comb(Comb(Const("snappy_reps",_),_),_)))
        -> s' = s
    | _ -> false) asl) in
  let pth = snd(find (fun (_,th) -> s4_is_out_fact s th) asl) in
  let l1 = rand(rand(concl pth)) and l2 = rand(rand(concl rth)) in
  let lth = ISPECL [`memory:(armstate,int64->byte)component`; `op:int64`;
                    l1; l2; s] SNAPPY_READ_BYTES_APPEND in
  let need = rand(lhand(concl lth)) in
  let rth' = TAC_PROOF((asl,need),
    MP_TAC rth THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[LENGTH_SNAPPY_REPS; LENGTH_BYTELIST_OF_NUM; PAIR_EQ] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ARITH_TAC]) in
  ASSUME_TAC(MP lth (CONJ pth rth')) (asl,w);;

(* The hook of the 32-bit tag stores: k from X8 (join7) or 3.                *)

let S4_MERGE_X8_TAC : tactic = fun (asl,w) ->
  let s = s4_state (asl,w) in
  let k = dest_small_numeral(rand(s4_reg_value asl s `X8`)) in
  S4_MERGE_TAC k (asl,w);;

(* The emitted copy: l = APPEND out (snappy_emit_copy (ip - c) (4 + ML)) for *)
(* the list l of the latest output fact, with the tags recognised by the     *)
(* lemmas for the lengths in lens.                                           *)

let SNAPPY_CF1_S4_ZX_ZX = prove
 (`!x:int32. word_zx(word_zx x:int64):int32 = x`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64] THEN
  MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x < 2 EXP 32 ==> x < 2 EXP 64`]);;

let s4_gen_lemmas = [2,SNAPPY_CF1_S4_COPY1_GEN; 2,SNAPPY_CF1_S4_COPY1B_GEN;
                     3,SNAPPY_CF1_S4_COPY2_GEN];;

let S4_VAL_TAC : tactic =
  REWRITE_TAC(VAL_WORD_SUB_CASES :: SNAPPY_VAL_THMS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN S4_MOD_ELIM_TAC THEN
  REPEAT(COND_CASES_TAC THEN S4_MOD_ELIM_TAC) THEN S4_ARITH_TAC;;

let s4_tag_thm asl lens tm =
  (* tm = bytelist_of_num k (val w) *)
  let tryl lth =
    let pm = PART_MATCH (lhs o rand) lth tm in
    let vs = fst(strip_forall(concl pm)) in
    pm in
  let cands = [SNAPPY_CF1_S4_COPY60_GEN; SNAPPY_CF1_S4_COPY64_GEN] in
  let try2 th =
    let pm = PART_MATCH (lhs o rand) th tm in
    let pm = try SPEC `ip - c:num` pm with Failure _ ->
             INST [`ip - c:num`,`off:num`] pm in
    let ant = lhand(concl pm) in
    MP pm (TAC_PROOF((asl,ant), REPEAT CONJ_TAC THEN
             FIRST [S4_VAL_TAC; S4_ARITH_TAC])) in
  let try4 th len =
    let pm = PART_MATCH (lhs o rand) th tm in
    let pm = try SPECL [`ip - c:num`; len] pm with Failure _ ->
             INST [`ip - c:num`,`off:num`; len,`len:num`] pm in
    let ant = lhand(concl pm) in
    MP pm (TAC_PROOF((asl,ant), REPEAT CONJ_TAC THEN
             FIRST [S4_VAL_TAC; S4_ARITH_TAC])) in
  ignore tryl;
  try tryfind try2 cands with Failure _ ->
  tryfind (fun (_,th) -> tryfind (try4 th) lens) s4_gen_lemmas;;

let S4_OUT_TAC (lens:term list) (ecs:thm list) : tactic = fun (asl,w) ->
  let s = s4_state (asl,w) in
  let pth = snd(find (fun (_,th) -> s4_is_out_fact s th) asl) in
  let pth = REWRITE_RULE[SNAPPY_CF1_S4_ZX_ZX] pth in
  let l = rand(rand(concl pth)) in
  let tags = setify(find_terms (fun t -> match t with
      Comb(Comb(Const("bytelist_of_num",_),_),Comb(Const("val",_),_)) -> true
    | _ -> false) l) in
  let tths = map (s4_tag_thm asl lens) tags in
  let tgt = `APPEND out (snappy_emit_copy (ip - c) (4 + ML))` in
  let eq = TAC_PROOF((asl,mk_eq(l,tgt)),
    REWRITE_TAC tths THEN REWRITE_TAC ecs THEN
    REWRITE_TAC[APPEND_ASSOC; APPEND_NIL] THEN
    REWRITE_TAC[ARITH_RULE `(4 + ML) - 60 = ML - 56`]) in
  let lth = TRANS (AP_TERM `LENGTH:byte list->num` (SYM eq))
              (REWRITE_CONV[LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM;
                            LENGTH_SNAPPY_REPS; LENGTH] (mk_comb(`LENGTH:byte list->num`,l))) in
  (ASSUME_TAC(REWRITE_RULE[eq] pth) THEN ASSUME_TAC lth) (asl,w);;

let s4_ec_thm asl (len:term) =
  let off = `ip - c:num` in
  let ar t = TAC_PROOF((asl,t), S4_ARITH_TAC) in
  let small len =
    let th = SPECL [off;len] SNAPPY_CF1_S4_EC_SMALL in
    MP th (ar(lhand(concl th))) in
  let mid len =
    let th = SPECL [off;len] SNAPPY_CF1_S4_EC_MID in
    MP th (ar(lhand(concl th))) in
  try [small len] with Failure _ -> try [mid len] with Failure _ ->
  let q = mk_binary "+" (mk_binary "DIV" (mk_binary "-" (len,`68`),`64`),`1`) in
  let th = SPECL [off;q;len] SNAPPY_CF1_S4_EC_REPS in
  let th = MP th (ar(lhand(concl th))) in
  let rest = rand(rand(rand(concl th))) in
  th :: (try [small rest] with Failure _ -> [mid rest]);;

let S4_OUT2_TAC (lens:term list) : tactic = fun (asl,w) ->
  S4_OUT_TAC lens (s4_ec_thm asl `4 + ML`) (asl,w);;




(* ------------------------------------------------------------------------- *)
(* More facts about the match: the mismatch at the match length, and the     *)
(* first different byte of two 64-bit loads by the trailing zeros of their   *)
(* xor.                                                                       *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CF1_S4_MISMATCH = prove
 (`!(src:byte list) a b.
        b + snappy_match_length src a b < LENGTH src
        ==> ~(EL (a + snappy_match_length src a b) src =
              EL (b + snappy_match_length src a b) src)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`src:byte list`; `a:num`; `b:num`;
                `snappy_match_length src a b + 1`] SNAPPY_MATCH_LENGTH_GE) THEN
  ANTS_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `t = snappy_match_length src a b` THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC SNAPPY_MATCH_LENGTH_MATCH THEN ASM_ARITH_TAC]);;

let SNAPPY_CF1_S4_CTZ_DIV8 = prove
 (`!(src:byte list) a b t.
        a + 8 <= LENGTH src /\ b + 8 <= LENGTH src /\ t < 8 /\
        (!i. i < t ==> EL (a + i) src = EL (b + i) src) /\
        ~(EL (a + t) src = EL (b + t) src)
        ==> word_ctz(word_xor (word(snappy_load64 src a):int64)
                              (word(snappy_load64 src b))) DIV 8 = t`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "eq" o check (is_forall o concl)) THEN
  MP_TAC(ISPECL [`word(snappy_load64 src a):int64`;
                 `word(snappy_load64 src b):int64`] SNAPPY_CTZ_XOR_BYTES) THEN
  ABBREV_TAC `z = word_ctz(word_xor (word(snappy_load64 src a):int64)
                                   (word(snappy_load64 src b)))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lo") (LABEL_TAC "hi")) THEN
  SUBGOAL_THEN `!i. i < 8 ==> word_subword (word(snappy_load64 src a):int64) (8 * i,8):byte = EL (a + i) src /\
                              word_subword (word(snappy_load64 src b):int64) (8 * i,8):byte = EL (b + i) src`
   (LABEL_TAC "el") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC S4_LOAD64_BYTE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `z < 64` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    MP_TAC(ISPEC `word_xor (word(snappy_load64 src a):int64) (word(snappy_load64 src b))`
       WORD_CTZ_LT_DIMINDEX) THEN
    REWRITE_TAC[DIMINDEX_64; WORD_XOR_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_TAC THEN
    USE_THEN "el" (MP_TAC o SPEC `t:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_TAC(ARITH_RULE `z DIV 8 < t \/ t < z DIV 8 \/ z DIV 8 = t`) THENL
   [USE_THEN "hi" (MP_TAC o C MP (ASSUME `z < 64`)) THEN
    USE_THEN "el" (MP_TAC o SPEC `z DIV 8`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "eq" (MP_TAC o SPEC `z DIV 8`) THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "lo" (MP_TAC o SPEC `t:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "el" (MP_TAC o SPEC `t:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Table joins with the values of the stores computed in numbers.            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CF1_S4_AND65535 = prove
 (`!x:int32. word_and x (word 65535) = word(val x MOD 65536)`,
  GEN_TAC THEN
  SUBGOAL_THEN `word 65535:int32 = word(2 EXP 16 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[WORD_AND_MASK_WORD]] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let S4_JOIN_TAC (h:term) (v:term) : tactic = fun (asl,w) ->
  let gen = snd(find (fun (_,th) ->
     try let j,b = dest_forall(concl th) in
         let a,_ = dest_imp b in
         is_conj a && is_neg(rand a) && rand(rand(rand a)) = h
     with Failure _ -> false) asl) in
  let j,b = dest_forall(concl gen) in
  let a,c = dest_imp b in
  let r = lhs c and tj = rand(rand c) in
  let ts = rand(lhand a) in
  let rr = mk_abs(j,r) and t = rator tj in
  let rh = rand(concl(BETA_CONV(mk_comb(rr,h)))) in
  let spec = snd(find (fun (_,th) -> try lhs(concl th) = rh with Failure _ -> false) asl) in
  let lth = CONV_RULE(DEPTH_CONV BETA_CONV) (ISPECL [rr;t;h;v;ts] SNAPPY_CF1_TABLE_JOIN) in
  let need = lhand(lhand(concl lth)) in
  let vth = TAC_PROOF((asl,mk_eq(rand(concl spec), rand need)),
              REWRITE_TAC[GSYM VAL_EQ; SNAPPY_CF1_S4_AND65535] THEN S4_VAL_TAC) in
  (UNDISCH_THEN (concl gen) (fun gen ->
   ASSUME_TAC(MP lth (CONJ (TRANS spec vth) gen)))) (asl,w);;

(* The candidate read from entry h2 after the update of entry h1.            *)

let S4_HC : tactic = fun (asl,w) ->
  (S4_JOIN_TAC `h1:num` `ip2 - 1` THEN
   S4_TSPLIT_TAC `h2:num` THEN
   W(fun (asl,w) -> s4_rewrites () := s4_zx_index asl `h2:num` :: !(s4_rewrites ());
                    ALL_TAC) THEN
   SUBGOAL_THEN `snappy_tupd t1 h1 (ip2 - 1) h2 + 4 <= LENGTH(inp:byte list) /\
                 snappy_tupd t1 h1 (ip2 - 1) h2 < 65536` STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[snappy_tupd] THEN COND_CASES_TAC THENL
      [S4_ARITH_TAC; SNAPPY_TBOUND_TAC `h2:num`];
     ALL_TAC] THEN
   W(fun (asl,w) ->
     let zth = TAC_PROOF((asl,
       `word_zx (word (snappy_tupd t1 h1 (ip2 - 1) h2):int16):int64 =
        word (snappy_tupd t1 h1 (ip2 - 1) h2)`),
       REWRITE_TAC[word_zx] THEN AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
       REWRITE_TAC[DIMINDEX_16] THEN S4_ARITH_TAC) in
     s4_rewrites () := zth :: !(s4_rewrites ()); ALL_TAC)) (asl,w);;

let S4_HD : tactic = S4_JOIN_TAC `h2:num` `ip2:num`;;

let S4_HE : tactic = SNAPPY_LOAD_TAC [32,`snappy_tupd t1 h1 (ip2 - 1) h2`];;

(* ------------------------------------------------------------------------- *)
(* loop7, from the 8-byte equality of the first compare.                     *)
(* ------------------------------------------------------------------------- *)

(* At +0x310, in the case of equal 8-byte loads at c + 4 and ip + 4.         *)

let S4_EQ8_HOOK : tactic =
  SUBGOAL_THEN `8 <= ML` ASSUME_TAC THENL
   [EXPAND_TAC "ML" THEN MATCH_MP_TAC SNAPPY_MATCH_LENGTH_GE THEN
    CONJ_TAC THENL [S4_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
       (is_neg(concl th) && is_neg(rand(concl th)) ||
        is_eq(concl th) &&
        (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "snappy_load64"
         with Failure _ -> false)) &&
       can (find_term ((=) `snappy_load64`)) (concl th))) THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`inp:byte list`; `c + 4`; `ip + 4`] S4_LOAD64_EQ_BYTES) THEN
    ANTS_TAC THENL [S4_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC];;

let S4_L7_HOOK : tactic = fun (asl,w) ->
  incr (s4_counter ());
  (S4_SNAPPY_SET_REGS_TAC
    [`X14`,`word_add src (word (c + 4)):int64`;
     `X8`,`word (8 * 1):int64`;
     `X6`,`word_add src (word ((ip + 4) + 8 * 1)):int64`;
     `X10`,`word_add src (word (LENGTH(inp:byte list) - 16)):int64`] THEN
   S4_SNAPPY_LEMMA_CALL_TAC
    (SPECL [`pc:num`;`src:int64`;`inp:byte list`;`c + 4`;`ip + 4`;`1`]
       SNAPPY_CF1_LOOP7) ("s" ^ string_of_int !(s4_counter ())) THEN
   S4_ML_TAC) (asl,w);;

let SNAPPY_CF1_S4_AND24 = prove
 (`!x:int32. val(word_and x (word 24)) = 8 * ((val x DIV 8) MOD 4)`,
  GEN_TAC THEN
  REWRITE_TAC[BITBLAST_RULE
   `word_and (x:int32) (word 24) = word_shl (word_and (word_ushr x 3) (word 3)) 3`] THEN
  SUBGOAL_THEN `word 3:int32 = word(2 EXP 2 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[WORD_AND_MASK_WORD]] THEN
  REWRITE_TAC[VAL_WORD_SHL; VAL_WORD; VAL_WORD_USHR; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN NUM_MOD_ELIM_TAC THEN ARITH_TAC);;

let s4_pc_extra = par_local_ref (fun () -> ([]:thm list));;

(* The trailing zeros of the xor of the first compare: the match length.     *)
(* At +0x2c4, in the case of different 8-byte loads at c + 4 and ip + 4.     *)

let S4_NE8_HOOK : tactic =
  SUBGOAL_THEN `ML < 8` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      not(is_neg(rand(concl th))) &&
      can (find_term ((=) `snappy_load64`)) (concl th))) THEN
    MP_TAC(SPECL [`inp:byte list`; `c + 4`; `ip + 4`] S4_LOAD64_EQ_BYTES) THEN
    ANTS_TAC THENL [S4_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`inp:byte list`; `c + 4`; `ip + 4`; `t:num`]
      SNAPPY_MATCH_LENGTH_LE_MISMATCH) THEN
    ASM_REWRITE_TAC[] THEN S4_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_ctz(word_xor (word(snappy_load64 inp (c + 4)):int64)
                      (word(snappy_load64 inp (ip + 4)))) DIV 8 = ML`
   ASSUME_TAC THENL
   [MATCH_MP_TAC SNAPPY_CF1_S4_CTZ_DIV8 THEN
    REPEAT CONJ_TAC THEN TRY S4_ARITH_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC SNAPPY_MATCH_LENGTH_MATCH THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "ML" THEN MATCH_MP_TAC SNAPPY_CF1_S4_MISMATCH THEN
      ASM_REWRITE_TAC[] THEN S4_ARITH_TAC];
    ALL_TAC] THEN
  W(fun (asl,w) ->
    let d = `word_xor (word(snappy_load64 inp (c + 4)):int64)
                      (word(snappy_load64 inp (ip + 4)))` in
    let iff = TAC_PROOF((asl,
      subst [d,`d:int64`] `val(d:int64) MOD 4294967296 = 0 <=> 4 <= ML`),
      SUBGOAL_THEN (subst [d,`d:int64`] `4 <= ML <=> 32 <= word_ctz(d:int64)`)
       SUBST1_TAC THENL
       [FIRST_X_ASSUM(fun th ->
          if can (find_term ((=) `word_ctz:int64->num`)) (concl th) &&
             is_eq(concl th) then SUBST1_TAC(SYM th) else NO_TAC) THEN
        SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
        REWRITE_TAC[WORD_LE_CTZ_VAL_MOD; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV]) in
    s4_pc_extra () := [iff]; ASSUME_TAC iff);;

(* ------------------------------------------------------------------------- *)
(* The values computed from the trailing zeros z < 64 of the xor of two      *)
(* 64-bit loads: z >> 3 (the bytes that match) and z & 24 (the shift of the  *)
(* data register), and the sign extension of a small length.                 *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CF1_S4_CTZ_AND24 = prove
 (`!z. z < 64
       ==> word_and (word_zx (word z:int64):int32) (word 24) =
           word(8 * ((z DIV 8) MOD 4))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

let SNAPPY_CF1_S4_CTZ_USHR3 = prove
 (`!z. z < 64 ==> word_ushr (word z:int64) 3 = word(z DIV 8)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

let SNAPPY_CF1_S4_CTZ_ISHR3 = prove
 (`!z. z < 64 ==> word_ishr (word_zx (word z:int64):int32) 3 = word(z DIV 8)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

let SNAPPY_CF1_S4_SXFROM_SMALL = prove
 (`!x. x < 2 EXP 31
       ==> word_sxfrom 31 (word_subword (word x:int64) (0,32):int64):int64 = word x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SXFROM; BIT_WORD_SUBWORD;
              DIMINDEX_64; DIMINDEX_32; ADD_CLAUSES] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BIT_WORD; DIMINDEX_64] THEN
  ASM_CASES_TAC `i < 31` THENL
   [ASM_SIMP_TAC[ARITH_RULE `i < 31 ==> MIN 31 i = i`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC(TAUT `a ==> (a /\ b <=> b)`) THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `~(i < 31) ==> MIN 31 i = 31`] THEN
    SUBGOAL_THEN `x DIV 2 EXP 31 = 0 /\ x DIV 2 EXP i = 0`
     (fun th -> REWRITE_TAC[th; ODD]) THEN
    CONJ_TAC THEN MATCH_MP_TAC DIV_LT THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC LTE_TRANS `2 EXP 31` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC]);;

let SNAPPY_CF1_S4_SXFROM = prove
 (`!(x:int32) n. val x = n /\ n < 2 EXP 31
                 ==> word_sxfrom 31 (word_subword x (0,32):int64):int64 = word n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_subword (x:int32) (0,32):int64 =
                word_subword (word n:int64) (0,32)` SUBST1_TAC THENL
   [REWRITE_TAC[word_subword; VAL_WORD; DIMINDEX_64] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC SNAPPY_CF1_S4_SXFROM_SMALL THEN ASM_REWRITE_TAC[]]);;

let SNAPPY_CF1_S4_JUSHR = prove
 (`!L k. L < 2 EXP 64 /\ k < 64
         ==> word_jushr (word L:int64) (word_zx (word k:int32)) =
             word(L DIV 2 EXP k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `L DIV 2 EXP k < 2 EXP 64` ASSUME_TAC THENL
   [TRANS_TAC LET_TRANS `L:num` THEN ASM_REWRITE_TAC[DIV_LE]; ALL_TAC] THEN
  REWRITE_TAC[word_jushr; GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_64; DIMINDEX_32] THEN
  SUBGOAL_THEN `k < 2 EXP 32 /\ k < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let SNAPPY_CF1_S4_MOD84 = prove
 (`!n. (n MOD 8) MOD 4 = n MOD 4`,
  GEN_TAC THEN MP_TAC(SPECL [`n:num`; `4`; `2`] MOD_MOD) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* The facts about the trailing zeros of the xor d of the loads at a and b:  *)
(* word_ctz d DIV 8 = t, the first byte that differs, and                    *)
(* val d MOD 2 EXP 32 = 0 <=> 4 <= t (the test of the low 32 bits).          *)

let S4_CTZ_FACTS_TAC (a:term) (b:term) (t:term) : tactic =
  let d = subst [a,`a:num`; b,`b:num`]
    `word_xor (word(snappy_load64 inp a):int64) (word(snappy_load64 inp b))` in
  let fct = subst [d,`d:int64`; t,`t:num`] `word_ctz(d:int64) DIV 8 = t` in
  SUBGOAL_THEN fct ASSUME_TAC THENL
   [MATCH_MP_TAC SNAPPY_CF1_S4_CTZ_DIV8 THEN
    REPEAT CONJ_TAC THEN TRY S4_ARITH_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`inp:byte list`; `c + 4`; `ip + 4`;
                    mk_binary "+" (mk_binary "-" (a,`c + 4`),`i:num`)]
        SNAPPY_MATCH_LENGTH_MATCH) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [S4_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      S4_ARITH_TAC;
      MP_TAC(SPECL [`inp:byte list`; `c + 4`; `ip + 4`] SNAPPY_CF1_S4_MISMATCH) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [S4_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN BINOP_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN S4_ARITH_TAC];
    ALL_TAC] THEN
  W(fun (asl,w) ->
    let iff = TAC_PROOF((asl,
      subst [d,`d:int64`; t,`t:num`] `val(d:int64) MOD 4294967296 = 0 <=> 4 <= t`),
      SUBGOAL_THEN (subst [d,`d:int64`; t,`t:num`] `4 <= t <=> 32 <= word_ctz(d:int64)`)
       SUBST1_TAC THENL
       [FIRST_ASSUM(fun th -> if concl th = fct then SUBST1_TAC(SYM th) else NO_TAC) THEN
        SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
        REWRITE_TAC[WORD_LE_CTZ_VAL_MOD; DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV]) in
    ASSUME_TAC iff);;

(* At loop7_exit2 (+0x3f4): the loads at c + 4 + 8 j and ip + 4 + 8 j, j =   *)
(* ML DIV 8, differ at the byte ML MOD 8.                                    *)

let S4_NE8B_HOOK : tactic =
  S4_CTZ_FACTS_TAC `(c + 4) + 8 * ML DIV 8` `(ip + 4) + 8 * ML DIV 8`
    `ML - 8 * ML DIV 8`;;

(* The branch on the low 32 bits of the xor, by the facts above.             *)

let S4_IFF_PC_TAC : tactic = fun (asl,w) ->
  let iffs = mapfilter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",ty),Comb(Comb(Const("=",_),Comb(Comb(Const("MOD",_),
        Comb(Const("val",_),_)),_)),_)),_) when ty = `:bool->bool->bool` -> th
    | _ -> fail()) asl in
  ARM_PC_REWRITE_TAC iffs (asl,w);;

(* Canonical forms of the length, the new ip and the data register at the  *)
(* joins of EmitCopy: X2 = word(4 + ML) (or the rest after the copies of 64  *)
(* bytes), X6 = src + (ip + 4 + ML), X5 = word(load64 q DIV 2 EXP (8 *      *)
(* (ML MOD 4))).                                                             *)

let s4_ctz_facts asl =
  mapfilter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("DIV",_),
        Comb(Const("word_ctz",_),_)),_)),_) -> th
    | _ -> fail()) asl;;

let S4_CTZ_REWRITE_TAC : tactic = fun (asl,w) ->
  let fs = s4_ctz_facts asl in
  let one fth =
    let z = lhand(lhs(concl fth)) in
    let zlt = TAC_PROOF((asl,mk_binary "<" (z,`64`)), S4_ARITH_TAC) in
    [MP (SPEC z SNAPPY_CF1_S4_CTZ_AND24) zlt; MP (SPEC z SNAPPY_CF1_S4_CTZ_USHR3) zlt;
     MP (SPEC z SNAPPY_CF1_S4_CTZ_ISHR3) zlt; fth] in
  let ths = WORD_CLZ_REVERSEFIELDS :: List.concat (map one fs) in
  SNAPPY_REWRITE_FACTS_TAC [`X2`;`X5`;`X6`] ths (asl,w);;

let S4_CANON_EQ_TAC : tactic =
  FIRST [REFL_TAC;
         MATCH_MP_TAC SNAPPY_CF1_S4_SXFROM THEN CONJ_TAC THENL
          [S4_VAL_TAC; S4_ARITH_TAC];
         S4_SNAPPY_WORD_EQ_TAC; SNAPPY_REG_NUM_TAC];;

(* Replace the fact read c s = v0 by read c s = v if v0 = v is provable by   *)
(* tac; the facts about the components cs are rewritten with v0 = v too.    *)

let S4_TRY_SET_TAC (c:term) (v:term) (cs:term list) : tactic = fun (asl,w) ->
  let s = s4_state (asl,w) in
  try let v0 = s4_reg_value asl s c in
      if v0 = v then ALL_TAC (asl,w) else
      let eq = TAC_PROOF((asl,mk_eq(v0,v)), S4_CANON_EQ_TAC) in
      SNAPPY_REWRITE_FACTS_TAC (c::cs) [eq] (asl,w)
  with Failure _ -> ALL_TAC (asl,w);;

(* Arithmetic from the simple numeric facts only (no conjunctions or        *)
(* negations, which make the decision procedure split cases).               *)

let S4_LIGHT_ARITH_TAC : tactic = fun (asl,w) ->
  let simple tm = is_num_fact tm && not(is_conj tm) && not(is_neg tm) in
  let ths = filter (fun (_,th) -> simple(concl th)) asl in
  (MAP_EVERY (MP_TAC o snd) ths THEN ARITH_TAC) ([],w);;

let S4_X5_TAC : tactic = fun (asl,w) ->
  let s = s4_state (asl,w) in
  try let v0 = s4_reg_value asl s `X5` in
      match v0 with
        Comb(Comb(Const("word_jushr",_),Comb(Const("word",_),l)),
             Comb(Const("word_zx",_),Comb(Const("word",_),k))) ->
          let lth = TAC_PROOF((asl,mk_binary "<" (l,`2 EXP 64`)),
                      REWRITE_TAC[SNAPPY_LOAD64_BOUND]) in
          let kth = TAC_PROOF((asl,mk_binary "<" (k,`64`)), S4_ARITH_TAC) in
          let th = MP (SPECL [l;k] SNAPPY_CF1_S4_JUSHR) (CONJ lth kth) in
          (* the shift 8 * (t MOD 4) as 8 * ((ip + 4 + ML) - q) *)
          let t4 = rand k and q = rand l in
          let r = mk_binary "-" (`ip + 4 + ML`,q) in
          let meq = TAC_PROOF((asl,mk_eq(t4,r)),
            MATCH_MP_TAC MOD_UNIQ THEN
            FIRST [EXISTS_TAC `0` THEN S4_LIGHT_ARITH_TAC;
                   EXISTS_TAC `1` THEN S4_LIGHT_ARITH_TAC;
                   EXISTS_TAC `0` THEN S4_ARITH_TAC;
                   EXISTS_TAC `1` THEN S4_ARITH_TAC]) in
          SNAPPY_REWRITE_FACTS_TAC [`X5`] [th; meq] (asl,w)
      | _ -> ALL_TAC (asl,w)
  with Failure _ -> ALL_TAC (asl,w);;

let s4_rest = `(4 + ML) - 64 * (((4 + ML) - 68) DIV 64 + 1)`;;

let S4_CANON_TAC : tactic =
  S4_CTZ_REWRITE_TAC THEN S4_X5_TAC THEN
  S4_TRY_SET_TAC `X2` `word(4 + ML):int64` [`X6`] THEN
  S4_TRY_SET_TAC `X2` (mk_comb(`word:num->int64`,s4_rest)) [] THEN
  S4_TRY_SET_TAC `X6` `word_add src (word (ip + 4 + ML)):int64` [] THEN
  S4_TRY_SET_TAC `X4` `word(ip - c):int64` [];;

(* loop9 of EmitCopy, from join18: q = (4 + ML - 68) DIV 64 + 1 copies of    *)
(* the tag of 64 bytes.                                                       *)

let S4_L9_HOOK : tactic = fun (asl,w) ->
  incr (s4_counter ());
  let q = `((4 + ML) - 68) DIV 64 + 1` in
  let d = `LENGTH(out:byte list)` in
  (S4_SNAPPY_SET_REGS_TAC
     [`X8`,subst [d,`d:num`; q,`q:num`] `word_add op (word (d + 3 * q)):int64`] THEN
   W(fun (asl,w) ->
     let s = s4_state (asl,w) in
     let w15 = s4_reg_value asl s `X15` in
     let th = SPECL [`pc:num`; `op:int64`; d; q; w15; `mcl:num`;
                     snappy_current_events (asl,w)] SNAPPY_CF1_LOOP9 in
     let ath = TAC_PROOF((asl,lhand(concl th)),
       REPEAT CONJ_TAC THEN
       FIRST [FIRST_ASSUM ACCEPT_TAC; NONOVERLAPPING_TAC; S4_LIGHT_ARITH_TAC]) in
     ARM_BSTEP_CALL_TAC S4_EXEC (MP th ath) ("s" ^ string_of_int !(s4_counter ()))))
  (asl,w);;

(* The bits 8..39 of the data register (ubfx x16, x5, #8, #32).               *)

let SNAPPY_CF1_S4_SUBWORD8 = prove
 (`!(l:byte list) q r p.
        r <= 3 /\ q + 8 <= LENGTH l /\ q + r + 1 = p
        ==> word_subword (word (snappy_load64 l q DIV 2 EXP (8 * r)):int64) (8,32):int64 =
            word (snappy_load32 l p)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`l:byte list`; `q:num`; `r + 1`] SNAPPY_LOAD64_SHIFT_LOW32) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`l:byte list`; `q:num`] SNAPPY_LOAD64_BOUND) THEN
  ABBREV_TAC `L = snappy_load64 l q` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; word_subword;
              DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `!k. L DIV 2 EXP k < 2 EXP 64` ASSUME_TAC THENL
   [GEN_TAC THEN TRANS_TAC LET_TRANS `L:num` THEN ASM_REWRITE_TAC[DIV_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; DIV_DIV; GSYM EXP_ADD;
               ARITH_RULE `8 * r + 8 = 8 * (r + 1)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN MP_TAC(SPECL [`l:byte list`; `q + r + 1`] SNAPPY_LOAD32_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`]);;

(* The goal mach st' s at a cut point, with the length of the output from   *)
(* the facts LENGTH (APPEND out _) = n of S4_OUT_TAC.                        *)

let S4_MACH_TAC : tactic = fun (asl,w) ->
  let eqs = mapfilter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),l),Var(_,_)) when
        not(is_var l) && not(is_numeral l) &&
        not(can (find_term (fun t -> match t with
                  Const("read",_) -> true | _ -> false)) l) -> th
    | _ -> fail()) asl in
  let lens = mapfilter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),
        Comb(Comb(Const("APPEND",_),_),_))),_) -> th
    | _ -> fail()) asl in
  (REWRITE_TAC[snappy_cf1_mach; snappy_cf1_ctx; snappy_phase; snappy_ip;
     snappy_ne; snappy_skip; snappy_cand; snappy_aux; snappy_t1; snappy_t2;
     snappy_out] THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC eqs THEN
   REPEAT CONJ_TAC THEN
   TRY(SNAPPY_CF1_EV_TAC THEN NO_TAC) THEN
   TRY(FIRST_ASSUM ACCEPT_TAC) THEN
   TRY(SNAPPY_FACT_TAC (TRY REFL_TAC THEN REWRITE_TAC lens THEN
         REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_SUB_LIST;
                     LENGTH_BYTELIST_OF_NUM; LENGTH_SNAPPY_REPS] THEN
         REWRITE_TAC eqs THEN
         FIRST [S4_SNAPPY_WORD_EQ_TAC;
                MATCH_MP_TAC SNAPPY_CF1_S4_SUBWORD8 THEN S4_ARITH_TAC;
                SNAPPY_REG_NUM_TAC] THEN NO_TAC)) THEN
   TRY S4_ARITH_TAC) (asl,w);;

(* The output by pieces: a tag stored by a 32-bit store is kept as the fact *)
(* of its k bytes (a numeral length, adjacent to the next store, so that     *)
(* bstep keeps it), and the pieces are appended to the output fact at join8. *)

let S4_PIECE_TAC (k:int) : tactic = fun (asl,w) ->
  let s = s4_state (asl,w) in
  let one (_,sth) =
    if not(s4_is_store32 s sth) then failwith "S4_PIECE_TAC" else
    let sth' = CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV
                 (REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))))))
                 sth in
    let a = rand(rand(lhand(lhs(concl sth')))) in
    let v = rand(concl sth') in
    let kt = mk_small_numeral k in
    MP (ISPECL [`memory:(armstate,int64->byte)component`; a; v; kt; s]
          SNAPPY_READ_BYTES32_PREFIX)
       (CONJ sth' (ARITH_RULE(mk_binary "<=" (kt,`4`)))) in
  (try ASSUME_TAC(tryfind one asl) with Failure _ -> ALL_TAC) (asl,w);;

let S4_PIECE_X8_TAC : tactic = fun (asl,w) ->
  let s = s4_state (asl,w) in
  let k = dest_small_numeral(rand(s4_reg_value asl s `X8`)) in
  S4_PIECE_TAC k (asl,w);;

let s4_is_piece s th =
  match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),
      Const("memory",_)),Comb(Const("bytes",_),Comb(Comb(Const(",",_),a),_)))),s')),
      Comb(Const("num_of_bytelist",_),_)) ->
        s' = s && a <> `op:int64` && can (find_term ((=) `op:int64`)) a
  | _ -> false;;

let rec S4_MERGE_ALL_TAC : tactic = fun (asl,w) ->
  let s = s4_state (asl,w) in
  let pth = snd(find (fun (_,th) -> s4_is_out_fact s th) asl) in
  let l1 = rand(rand(concl pth)) in
  let one (_,rth) =
    if not(s4_is_piece s rth) then failwith "S4_MERGE_ALL_TAC" else
    try
    let l2 = rand(rand(concl rth)) in
    let lth = ISPECL [`memory:(armstate,int64->byte)component`; `op:int64`;
                      l1; l2; s] SNAPPY_READ_BYTES_APPEND in
    let need = rand(lhand(concl lth)) in
    let rth' = TAC_PROOF((asl,need),
      MP_TAC rth THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH_SNAPPY_REPS; LENGTH_BYTELIST_OF_NUM;
                  LENGTH; PAIR_EQ] THEN
      REPEAT CONJ_TAC THEN
      TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC) THEN
      ARITH_TAC) in
    MP lth (CONJ pth rth')
    with Failure m -> failwith m in
  (match (try Some(tryfind one asl) with Failure _ -> None) with
     Some th -> (ASSUME_TAC th THEN S4_MERGE_ALL_TAC)
   | None -> ALL_TAC) (asl,w);;

(* At join14 (after FindMatchLength's byte loop): X8 = (ML <= 7) as a word.  *)

let S4_J14_TAC : tactic =
  ASM_CASES_TAC `ML <= 7` THENL
   [TRY S4_SNAPPY_CONTR_TAC THEN S4_TRY_SET_TAC `X8` `word 1:int64` [];
    TRY S4_SNAPPY_CONTR_TAC THEN S4_TRY_SET_TAC `X8` `word 0:int64` []];;

(* SNAPPY_CF1_CUT_TAC with the conditions of the model decided by the        *)
(* assumptions first (both ways), then by the arithmetic of this segment.   *)

let S4_DECIDE_CONV (asl:(string*thm) list) (eqs:thm list) : conv =
  let acc c = TAC_PROOF((asl,c), FIRST_ASSUM ACCEPT_TAC) in
  let ari c = TAC_PROOF((asl,c), S4_ARITH_TAC) in
  let dec c =
    try EQT_INTRO(acc c) with Failure _ ->
    try EQF_INTRO(acc(mk_neg c)) with Failure _ ->
    try EQT_INTRO(ari c) with Failure _ ->
    try EQF_INTRO(ari(mk_neg c)) with Failure _ ->
    failwith "S4_DECIDE_CONV" in
  fun tm ->
    match tm with
      Comb(Comb(Comb(Const("COND",_),c),_),_) ->
        let cth = (REWRITE_CONV eqs THENC NUM_REDUCE_CONV) c in
        let c' = rand(concl cth) in
        let dth = if c' = `T` || c' = `F` then cth else TRANS cth (dec c') in
        (RATOR_CONV(RATOR_CONV(RAND_CONV(K dth))) THENC
         GEN_REWRITE_CONV I [COND_CLAUSES]) tm
    | _ -> failwith "S4_DECIDE_CONV";;

let S4_STEP_CONV (asl:(string*thm) list) (eqs:thm list) : conv =
  let step tm =
    match tm with
      Comb(Comb(Const("snappy_cf1_step",_),_),st) when
        (try fst(dest_const(fst(strip_comb st))) = "SnappyCState" with Failure _ -> false) ->
        (GEN_REWRITE_CONV I [snappy_cf1_step] THENC TOP_DEPTH_CONV let_CONV THENC
         TOP_DEPTH_CONV (S4_DECIDE_CONV asl eqs) THENC REWRITE_CONV eqs) tm
    | _ -> failwith "S4_STEP_CONV" in
  DEPTH_CONV step;;

let S4_CUT_TAC (j:int) : tactic =
  (DISJ2_TAC ORELSE ALL_TAC) THEN MATCH_MP_TAC SNAPPY_CF1_CUT_INTRO THEN
  W(fun (asl,w) ->
    let kth = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Comb(Const("snappy_crun",_),_),_),
             Comb(Const("snappy_cf1_init",_),_))),_) -> true
      | _ -> false) asl) in
    let k = rand(rator(lhand(concl kth))) and st = rand(concl kth) in
    let f = rand(rator(rator(lhand(concl kth)))) in
    let ith = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("snappy_cf1_inv",_),_),st') -> st' = st
      | _ -> false) asl) in
    let eqs = mapfilter (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),Var(_,_)) when
          not(is_var l) && not(is_numeral l) &&
          not(can (find_term (fun t -> match t with
                    Const("read",_) -> true | _ -> false)) l) -> th
      | _ -> fail()) asl in
    let run = list_mk_comb(`snappy_crun`,[f; mk_small_numeral j; st]) in
    let runth = (SNAPPY_CRUN_CONV THENC S4_STEP_CONV asl eqs) run in
    MAP_EVERY EXISTS_TAC [k; mk_small_numeral j; rand(concl runth)] THEN
    REPEAT CONJ_TAC THENL
     [ACCEPT_TAC kth; ACCEPT_TAC ith; ACCEPT_TAC runth; ARITH_TAC;
      REWRITE_TAC[snappy_phase] THEN ARITH_TAC; ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The segment: the driver from loop6 with the hooks above, to join4 (phase *)
(* 5, the end of the input), loop6 (phase 4, an immediate next match) or     *)
(* loop1 (phase 1), one step of the model in every case.                    *)
(* ------------------------------------------------------------------------- *)

let rec S4_RUN2_TAC (hooks:(int * (bool * tactic)) list) (stops:int list) : tactic =
  fun (asl,w) ->
  match s4_goal_state w with
    None -> ALL_TAC (asl,w)
  | Some s ->
  match s4_pc_offset (s4_pc_value asl s) with
    None ->
      (S4_PC_TAC THEN S4_IFF_PC_TAC THEN S4_CASES_TAC S4_SNAPPY_CONTR_TAC THEN
       S4_RUN2_TAC hooks stops) (asl,w)
  | Some n ->
      if mem n stops then ALL_TAC (asl,w) else
      match (try Some(assoc n hooks) with Failure _ -> None) with
        Some(false,h) -> (h THEN S4_STEP_TAC THEN TRY SNAPPY_EV_CHECKPOINT_TAC THEN
                          S4_RUN2_TAC hooks stops) (asl,w)
      | Some(true,h) -> (h THEN TRY SNAPPY_EV_CHECKPOINT_TAC THEN
                         S4_RUN2_TAC hooks stops) (asl,w)
      | None -> (S4_BLOCK_TAC (stops @ map fst hooks) THEN
                 TRY SNAPPY_EV_CHECKPOINT_TAC THEN
                 S4_RUN2_TAC hooks stops) (asl,w);;

(* After loop7: the case split on its exit, with MIN as one of its arguments. *)

let S4_L7_POST : tactic =
  let b = `(LENGTH(inp:byte list) - 16 - (ip + 4)) DIV 8` in
  let c = subst [b,`b:num`] `ML DIV 8 < b + 1` in
  let m1 = subst [b,`b:num`] `MIN (ML DIV 8) (b + 1)` and
      m0 = subst [b,`b:num`] `MIN (ML DIV 8) b` in
  let mk v1 v0 = mk_conj(mk_eq(m1,v1),mk_eq(m0,v0)) in
  let fix cth eq =
    SUBGOAL_THEN eq (fun th -> SNAPPY_REWRITE_FACTS_TAC [`X2`;`X6`;`X8`;`X15`;`PC`] [th; cth])
    THENL [REWRITE_TAC[MIN] THEN REPEAT COND_CASES_TAC THEN S4_ARITH_TAC; ALL_TAC] in
  ASM_CASES_TAC c THENL
   [fix (ASSUME c) (mk `ML DIV 8` `ML DIV 8`);
    fix (ASSUME (mk_neg c)) (mk (mk_binary "+" (b,`1`)) b)];;

let s4_lens = [`4 + ML`; `ML - 56`; s4_rest; mk_binary "-" (s4_rest,`60`)];;

let s4_hooks =
 [14500, s4_pre (S4_LOAD_REG_TAC 64 `X1` 4 THEN S4_LOAD_REG_TAC 64 `X4` 4);
  14520, s4_pre S4_NE8_HOOK;
  14540, s4_pre (S4_LOAD_REG_TAC 64 `X1` 8);
  14568, s4_pre S4_CANON_TAC;
  14596, s4_pre S4_EQ8_HOOK;
  14624, s4_call (S4_L7_HOOK THEN S4_L7_POST);
  14672, s4_call S4_L8_HOOK;
  14712, s4_pre S4_J14_TAC;
  14728, s4_pre S4_CANON_TAC;
  14740, s4_pre S4_CANON_TAC;
  14760, s4_pre (S4_PIECE_TAC 3);
  14820, s4_pre (S4_PIECE_TAC 3);
  14824, s4_pre S4_NE8B_HOOK;
  14844, s4_pre (S4_LOAD_REG_TAC 64 `X6` 4);
  14872, s4_pre S4_CANON_TAC;
  14900, s4_pre S4_CANON_TAC;
  14912, s4_call S4_L9_HOOK;
  14984, s4_pre (S4_LOAD_REG_TAC 64 `X6` 0);
  14416, s4_pre S4_PIECE_X8_TAC;
  14420, s4_pre (S4_MERGE_ALL_TAC THEN S4_OUT2_TAC s4_lens);
  14428, s4_pre S4_HA;
  14460, s4_pre S4_HB;
  14464, s4_pre S4_HC;
  14472, s4_pre S4_HD;
  14476, s4_pre S4_HE];;

let S4_FINAL_TAC : tactic =
  S4_AT_TAC
   [14228, BSTEP_FINAL_TAC THEN S4_CUT_TAC 1 THEN S4_MACH_TAC;
    14488, SUBGOAL_THEN `ip + (4 + ML) = ip2` ASSUME_TAC THENL
            [EXPAND_TAC "ip2" THEN ARITH_TAC; ALL_TAC] THEN
           BSTEP_FINAL_TAC THEN S4_CUT_TAC 1 THEN S4_MACH_TAC;
    13860, SUBGOAL_THEN `ip + (4 + ML) = ip2` ASSUME_TAC THENL
            [EXPAND_TAC "ip2" THEN ARITH_TAC; ALL_TAC] THEN
           BSTEP_FINAL_TAC THEN S4_CUT_TAC 1 THEN S4_MACH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The segment by the match length ML = snappy_match_length inp (c + 4)      *)
(* (ip + 4), the length of the copy being 4 + ML: ML below 8 (the first     *)
(* 8-byte compare differs, one copy tag), up to 60 (one copy of at most 64   *)
(* bytes), 61..63 (a copy of 60 bytes, then the rest), from 64 (loop9:       *)
(* copies of 64 bytes) with the rest s4_rest at most 64 or above it (a copy  *)
(* of 60 bytes before the last). The case is a conjunct of the antecedent.   *)
(* ------------------------------------------------------------------------- *)

let s4_ml = `snappy_match_length inp (c + 4) (ip + 4)`;;

let s4_cases =
  map (fun t -> subst [s4_ml,`x:num`] t)
   [`x < 8`;
    `8 <= x /\ x <= 60`;
    `60 < x /\ x < 64`;
    `64 <= x /\ (4 + x) - 64 * (((4 + x) - 68) DIV 64 + 1) <= 64`;
    `64 <= x /\ 64 < (4 + x) - 64 * (((4 + x) - 68) DIV 64 + 1)`];;

let s4_case_stmt (cond:term) =
  let vs,b = strip_forall SNAPPY_CF1_SEG4_STMT in
  let a,c = dest_imp b in
  list_mk_forall(vs,mk_imp(mk_conj(a,cond),c));;

let S4_CASES_SPLIT = prove
 (list_mk_disj s4_cases, ARITH_TAC);;

(* The segment, in each case (the case is then an assumption).              *)

let S4_SEG_TAC : tactic =
  SNAPPY_CF1_SEG_START_TAC THEN
  SNAPPY_ABBREV_TAC `mcl = 27 + LENGTH(inp:byte list) + LENGTH inp DIV 6` THEN
  SNAPPY_ABBREV_TAC `ML = snappy_match_length inp (c + 4) (ip + 4)` THEN
  SUBGOAL_THEN `(ip + 4) + ML <= LENGTH(inp:byte list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inp:byte list`; `c + 4`; `ip + 4`] SNAPPY_MATCH_LENGTH) THEN
    ASM_REWRITE_TAC[] THEN S4_LIGHT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(out:byte list) + 3 * ((4 + ML) DIV 64) + 12 <= mcl`
   ASSUME_TAC THENL [S4_LIGHT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(out:byte list) < 2 EXP 32 /\ ML < 65536`
   STRIP_ASSUME_TAC THENL [CONJ_TAC THEN S4_LIGHT_ARITH_TAC; ALL_TAC] THEN
  S4_STEP_TAC THEN S4_RUN2_TAC s4_hooks [14228; 14488; 13860] THEN
  S4_FINAL_TAC;;

(* The segment from its cases.                                               *)

let S4_FROM_CASES_TAC (ths:thm list) : tactic =
  let vs,b = strip_forall SNAPPY_CF1_SEG4_STMT in
  let a = lhand b in
  MAP_EVERY X_GEN_TAC vs THEN DISCH_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC S4_CASES_SPLIT THEN
  W(fun (asl,w) ->
    let cth = snd(hd asl) in
    ACCEPT_TAC(tryfind (fun th ->
      MP (SPECL vs th) (CONJ (ASSUME a) cth)) ths));;
