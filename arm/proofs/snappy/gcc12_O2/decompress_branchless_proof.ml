(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
(* ========================================================================= *)
(* DecompressBranchless<char*> (0x6050), the fast loop of the array writer:  *)
(* correctness and memory safety (decompress_branchless_spec.ml), with the   *)
(* lemmas and tactics of decompress_branchless_lib.ml; the pattern-copy      *)
(* leaves are proved in decompress_branchless_near{1,2a,2b}_proof.ml.        *)
(*                                                                           *)
(* First assembled by a development script, now maintained by hand.        *)
(*                                                                           *)
(* Three kinds of cut point, with a measure (ENSURES_MEASURE_INDUCT):        *)
(*   TAG (0x6140 for the first tag of an iteration, w = 2; 0x61f0 for the   *)
(*       second, w = 1) for the tag at position h of the input,             *)
(*       measure 2 (L - h) + 1;                                             *)
(*   J   (0x61e4, after a tag, the limit checks), measure 2 (L - h) + 2;    *)
(*   E   (0x6238, the exit: flush of the deferred copy and return), 0.      *)
(* At each: the output so far ob at base (op = LENGTH ob), the deferred copy *)
(* db at dsrc (dl = LENGTH db <= 64), and the model                          *)
(*   snappy_steps k m (inp,out) = SOME(SUB_LIST(h,L - h) inp, APPEND ob db). *)
(* The flushes are MemCopy64 by its contract (DB_FLUSH); the tag segment is  *)
(* split into leaves by the class of the tag and, for copies with an offset *)
(* below the length (Copy64BytesWithPatternExtension), by the offset: the   *)
(* pattern copies for each offset 1..16 (TBL with the pattern masks), the    *)
(* chunk copy for offsets 17..63.                                            *)
(* ========================================================================= *)


needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_lib.ml";;
needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_near1_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_near2a_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_near2b_spec.ml";;

let DB_TAG_LIT = prove(db_tag_leaf "val(EL h inp) MOD 4 = 0 /\\ val(EL h inp) DIV 4 < 60",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?d. val(EL h (inp:byte list)) DIV 4 = d` STRIP_ASSUME_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `d < 60` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC_ALL DB_STEP_LIT) THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE DB_ARITH_TAC); DISCH_TAC] THEN
  ABBREV_TAC `c = EL h (inp:byte list)` THEN
  SUBGOAL_THEN `val(c:byte) < 256` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sx(iword(&(d + 1) - &256):int16):int64 = word_sub (word (d + 1)) (word 256)` ASSUME_TAC THENL
   [MATCH_MP_TAC DB_SX_IWORD_SUB THEN DB_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (d + 1)) (word 256)) (word 255):int64 = word (d + 1)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`d + 1`; `1`] DB_AND255_SUB) THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN MATCH_MP_TAC THEN DB_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_zx (c:byte)) (word 3):int64 = word 0 /\ word_ushr (word_zx (c:byte)) 2:int64 = word d /\
                word_add (word d) (word 2):int64 = word (d + 2)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DB_AND3; DB_USHR2; WORD_ADD]; ALL_TAC] THEN
  ASM_CASES_TAC `op + dl < 256` THEN
  DB_WCASE_TAC (fun wv ->
   W(fun (asl,_) ->
    let rws = [DB_VAL_WORD_ZX_BYTE; DB_AND16_T0; DB_AND16_T1; DB_AND16_T2; WORD_SUB_0] @
      map (fun t -> snd(find (fun (_,th) -> concl th = t) asl))
       [`word_and (word_zx (c:byte)) (word 3):int64 = word 0`; `word_ushr (word_zx (c:byte)) 2:int64 = word d`;
        `word_add (word d) (word 2):int64 = word (d + 2)`;
        `word_sx(iword(&(d + 1) - &256):int16):int64 = word_sub (word (d + 1)) (word 256)`;
        `word_and (word_sub (word (d + 1)) (word 256)) (word 255):int64 = word (d + 1)`] in
    DB_INIT_TAC THEN
    MP_TAC(SPECL [`s0:armstate`; `pc:num`; `c:byte`] SNAPPY_LMO_TABLE) THEN
    ASM_REWRITE_TAC[snappy_lmo] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    DB_BYTE_TAC `((h + 1) + d) + 1` THEN
    DB_RUN_TAC ~rws [17936] THEN DB_FLUSH_NEXT_TAC THEN
    DB_RUN_TAC ~rws [25060] THEN
    DB_TO_TAC 1 `2 * (li - (h + d + 2)) + 2`
     [`h + d + 2`; `op + dl:num`; `d + 1`; `word_add ip (word (h + 1)):int64`; `APPEND ob db:byte list`;
      `SUB_LIST(h + 1,d + 1) inp:byte list`; `SUC k`; mk_small_numeral wv])));;
let DB_TAG_C2_FAR = db_far_leaf 2;;
let DB_TAG_C1_FAR = db_far_leaf 1;;
let DB_TAG_LONGLIT = db_break_leaf 0;;
let DB_TAG_COPY4 = db_break_leaf 3;;
let DB_TAG_CHUNK = db_chunk_leaf ();;
(* The pattern-copy leaves, from the jobs decompress_branchless_near*.     *)
let DB_TAG_NEAR1 = CONJUNCTS SNAPPY_DB_TAG_NEAR1;;
let DB_TAG_NEAR2 = CONJUNCTS SNAPPY_DB_TAG_NEAR2A @ CONJUNCTS SNAPPY_DB_TAG_NEAR2B;;
(* The tag segment from the leaves, by the class of the tag byte and the offset. *)
let DB_TAG_STMT = db_lemma db_tag_pre db_tag_bounds "2 * (li - h) + 1";;
let db_is_el_fact tm =
  type_of tm = bool_ty &&
  not(exists (fun v -> type_of v = `:armstate`) (frees tm)) &&
  forall (fun c -> mem (fst(dest_const c)) ("EL" :: db_arith_consts)) (find_terms is_const tm);;
let DB_EL_ARITH_TAC : tactic = fun (asl,w) ->
  (MAP_EVERY MP_TAC (filter (fun th -> db_is_el_fact (concl th) &&
      can (find_term (fun t -> match t with Const("EL",_) -> true | _ -> false)) (concl th)) (map snd asl)) THEN
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) (asl,w);;
let DB_LEAF_TAC (leaf:thm) : tactic =
  W(fun (asl,w) ->
    let lth = SPEC_ALL leaf in
    let hyp = lhand(concl lth) in
    let hth = TAC_PROOF((asl,hyp),
      REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; DB_ARITH_TAC; DB_EL_ARITH_TAC]) in
    ACCEPT_TAC (MP lth hth));;
let db_cases_tac (t:term) (n:int) (tacs:int -> tactic) : tactic =
  (* t < n known: split t = 0 \/ ... \/ t = n-1 *)
  let disj = list_mk_disj (map (fun i -> mk_eq(t,mk_small_numeral i)) (0--(n-1))) in
  SUBGOAL_THEN disj MP_TAC THENL [DB_EL_ARITH_TAC; ALL_TAC] THEN
  let rec go i = if i = n - 1 then DISCH_TAC THEN tacs i
                 else DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL [tacs i; go (i + 1)] in
  go 0;;
let db_tag_proof (lit,longlit,copy4,c1far,c2far,chunk,near1,near2) =
  prove(DB_TAG_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(EL h (inp:byte list)) MOD 4 < 4 /\ val(EL h (inp:byte list)) DIV 4 MOD 8 < 8` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun i -> ASSUME_TAC(REWRITE_RULE[DIMINDEX_8]
     (ISPEC (subst [i,`i:num`] `EL (h + i) (inp:byte list)`) VAL_BOUND))) [`1`; `2`] THEN
  ASSUME_TAC(REWRITE_RULE[DIMINDEX_8] (ISPEC `EL h (inp:byte list)` VAL_BOUND)) THEN
  db_cases_tac `val(EL h (inp:byte list)) MOD 4` 4 (fun t ->
    if t = 0 then
      ASM_CASES_TAC `val(EL h (inp:byte list)) DIV 4 < 60` THENL [DB_LEAF_TAC lit; DB_LEAF_TAC longlit]
    else if t = 3 then DB_LEAF_TAC copy4
    else if t = 1 then
      let off = parse_term (db_offt 1) and len = parse_term (db_lent 1) in
      ASM_CASES_TAC (mk_binop `(<=):num->num->bool` len off) THENL
       [DB_LEAF_TAC c1far;
        db_cases_tac off 11 (fun k -> DB_LEAF_TAC (near1 k))]
    else
      let off = parse_term (db_offt 2) and len = parse_term (db_lent 2) in
      ASM_CASES_TAC (mk_binop `(<=):num->num->bool` len off) THENL
       [DB_LEAF_TAC c2far;
        ASM_CASES_TAC (mk_binop `(<=):num->num->bool` `17` off) THENL
         [DB_LEAF_TAC chunk;
          db_cases_tac off 17 (fun k -> DB_LEAF_TAC (near2 k))]]));;
(* J: the join after a tag (0x194). *)
let DB_J_STMT = db_lemma db_j_pre db_j_bounds "2 * (li - h) + 2";;
let DB_OUT_LE_M_TAC : tactic =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `snappy_steps (k:num) (m:num) (inp,out) = SOME(a:byte list,b:byte list)`) (concl th)
    then MP_TAC(CONJUNCT2(CONJUNCT2(MATCH_MP SNAPPY_STEPS_SOME th))) else NO_TAC) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND] THEN DB_LEN_TAC THEN DISCH_TAC;;
let DB_J = prove(DB_J_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DB_OUT_LE_M_TAC THEN
  DB_WCASE_TAC (fun wv ->
    if wv = 2 then
      DB_INIT_TAC THEN DB_RUN_TAC [25072] THEN
      DB_TO_TAC 0 `2 * (li - h) + 1`
        [`h:num`; `op:num`; `dl:num`; `dsrc:int64`; `ob:byte list`; `db:byte list`; `k:num`; `1`]
    else
      ASM_CASES_TAC `h + 130 < li` THENL
       [ASM_CASES_TAC `op + dl + 64 < lim` THENL
         [DB_INIT_TAC THEN DB_RUN_TAC [24896] THEN
          DB_TO_TAC 0 `2 * (li - h) + 1`
            [`h:num`; `op:num`; `dl:num`; `dsrc:int64`; `ob:byte list`; `db:byte list`; `k:num`; `2`];
          DB_INIT_TAC THEN DB_RUN_TAC [25144] THEN
          DB_TO_TAC 2 `0` [`h:num`; `op:num`; `dl:num`; `dsrc:int64`; `ob:byte list`; `db:byte list`; `k:num`]];
        DB_INIT_TAC THEN DB_RUN_TAC [25144] THEN
        DB_TO_TAC 2 `0` [`h:num`; `op:num`; `dl:num`; `dsrc:int64`; `ob:byte list`; `db:byte list`; `k:num`]]));;
let DB_WORD_SUB_ADD_1 = prove
 (`!x:int64 h. word_sub (word_add x (word (h + 1))) (word 1) = word_add x (word h)`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let DB_TO_Q_TAC (kt:term) (inpt:term) (outt:term) : tactic =
  BSTEP_FINAL_TAC THEN
  (fun (asl,w) -> if is_conj w && not(is_conj(rand w)) && not(is_eq(rand w))
                  then (CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC]) (asl,w) else ALL_TAC (asl,w)) THEN
  (fun (asl,w) -> if is_disj w then DISJ1_TAC (asl,w) else ALL_TAC (asl,w)) THEN
  (fun (asl,w) -> REWRITE_TAC[db_find_asm asl `LENGTH (inp:byte list) = li`] (asl,w)) THEN
  REPEAT CONJ_TAC THEN
  db_conj_report (FIRST [FIRST_ASSUM ACCEPT_TAC;
         (fun (asl,w) -> match w with
            Comb(Const("?",_),Abs(v,_)) when fst(dest_var v) = "k" ->
              (EXISTS_TAC kt THEN EXISTS_TAC inpt THEN EXISTS_TAC outt THEN
               REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST; CONJUNCT1 snappy_steps] THEN ASM_REWRITE_TAC[SUB_REFL; WORD_ADD_0] THEN
               TRY(SUBGOAL_THEN `li - MIN (li - h) (li - h) = h` SUBST1_TAC THENL [DB_ARITH_TAC; ALL_TAC]) THEN
               REPEAT CONJ_TAC THEN db_conj_report (FIRST [FIRST_ASSUM ACCEPT_TAC; DB_REG_TAC])) (asl,w)
          | _ -> failwith "");
         DB_EVENTS_TAC;
         DB_REG_TAC]);;

let DB_E_STMT = db_lemma db_e_pre db_e_bounds "0";;
let DB_E = prove(DB_E_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `dl = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `db:byte list = []` SUBST_ALL_TAC THENL [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL; ADD_CLAUSES]) THEN
    DB_INIT_TAC THEN DB_RUN_TAC ~rws:[DB_WORD_SUB_ADD_1] [] THEN
    DB_TO_Q_TAC `k:num` `SUB_LIST(h,li - h) inp:byte list` `ob:byte list`;
    SUBGOAL_THEN `op + 64 <= m` ASSUME_TAC THENL [DB_ARITH_TAC; ALL_TAC] THEN
    DB_INIT_TAC THEN DB_RUN_TAC ~rws:[DB_WORD_SUB_ADD_1] [17936] THEN DB_FLUSH_NEXT_TAC THEN
    DB_RUN_TAC ~rws:[DB_WORD_SUB_ADD_1] [] THEN
    DB_TO_Q_TAC `k:num` `SUB_LIST(h,li - h) inp:byte list` `APPEND ob db:byte list`]);;
(* ------------------------------------------------------------------------- *)
(* The loop by the measure, from the three segment lemmas.                   *)
(* ------------------------------------------------------------------------- *)

let db_R_tm = parse_term db_R;;
let db_Q_tm = parse_term db_Q;;
let db_C_tm = parse_term db_C;;
let db_G_tm = parse_term db_G;;

let DB_LOOP_STMT =
  let body = mk_imp(db_G_tm, mk_forall(`n:num`,
    list_mk_icomb "ensures" [`arm`; mk_comb(db_R_tm,`n:num`); db_Q_tm; db_C_tm])) in
  list_mk_forall(filter (fun v -> fst(dest_var v) <> "imp") (frees body), body);;

(* One disjunct of R n s (an assumption, the last one), by a segment lemma. *)
let DB_USE_SEGMENT_TAC (lemma:thm) (gth:thm) (zero:bool) : tactic =
  fun (asl,w) ->
  let dth = snd(hd asl) in
  let neq0,dth = if zero then let a,b = CONJ_PAIR dth in Some a,b else None,dth in
  let rec strip th =
    if is_exists(concl th) then
      let v,_ = dest_exists(concl th) in
      CHOOSE_THEN (fun th' -> strip th') th
    else (fun (asl,w) ->
      let neq,rest = if zero then (match neq0 with Some a -> a | None -> failwith ""),th
                     else CONJ_PAIR th in
      let st,rest2 = CONJ_PAIR rest in
      let bd,pre = CONJ_PAIR rest2 in
      let lth = SPEC_ALL lemma in
      let lth = MP lth (CONJ gth (CONJ st bd)) in
      let lth = REWRITE_RULE[ensures] lth in
      let lth = BETA_RULE(SPEC (rand w) lth) in
      let lth = MP lth pre in
      (SUBST1_TAC neq THEN ACCEPT_TAC lth) (asl,w)) in
  (FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = concl (snd(hd asl)))) THEN strip dth) (asl,w);;

let DB_LOOP_TAC (tag,j,e) : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(fun gth ->
  MATCH_MP_TAC ENSURES_MEASURE_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[ensures] THEN BETA_TAC THEN X_GEN_TAC `s:armstate` THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
   [DB_USE_SEGMENT_TAC tag gth false;
    DB_USE_SEGMENT_TAC j gth false;
    DB_USE_SEGMENT_TAC e gth true]);;
let db_loop_proof (tag,j,e) = prove(DB_LOOP_STMT, DB_LOOP_TAC (tag,j,e));;

(* ------------------------------------------------------------------------- *)
(* The prologue and the main theorem.                                        *)
(* ------------------------------------------------------------------------- *)

let DB_SUB_LIST_ALL = prove
 (`!l:A list. SUB_LIST(0,LENGTH l - 0) l = l`,
  REWRITE_TAC[SUB_0; SUB_LIST_LENGTH]);;

let DB_MAIN_TAC (loop:thm) : tactic =
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; ALLPAIRS; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `li = LENGTH(inp:byte list)` THEN
  ABBREV_TAC `p = LENGTH(out:byte list)` THEN
  ABBREV_TAC `lim = m - MIN 63 m` THEN
  SUBGOAL_THEN `li < 2 EXP 64 /\ lim < 2 EXP 32 /\ p < 2 EXP 32 /\ lim <= m` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lim" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word_add ip (word li)) ip = word li:int64` ASSUME_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  W(fun (asl,_) ->
  let rws = [db_find_asm asl `word_sub (word_add ip (word li)) ip = word li:int64`] in
  ASM_CASES_TAC `130 < li /\ li < 2 EXP 63 /\ p + 64 < lim` THENL
   [FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
    SUBGOAL_THEN `lim + 63 = m /\ 64 < lim` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "lim" THEN UNDISCH_TAC `p + 64 < lim` THEN EXPAND_TAC "lim" THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC (mk_abs(`s:armstate`, mk_exists(`n:num`, list_mk_comb(db_R_tm,[`n:num`; `s:armstate`])))) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
      (* to the first tag *)
      MP_TAC(ISPEC `inp:byte list` DB_SUB_LIST_ALL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      DB_INIT_TAC THEN
      MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `ip:int64`; `li:num`; `0`; `s0:armstate`] EL_READ_BYTELIST) THEN
      ASM_REWRITE_TAC[WORD_ADD_0] THEN ANTS_TAC THENL [DB_ARITH_TAC; DISCH_THEN(ASSUME_TAC o SYM)] THEN
      DB_RUN_TAC ~rws [24896] THEN
      BSTEP_FINAL_TAC THEN
      (fun (asl,w) -> if is_conj w then (CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC]) (asl,w) else ALL_TAC (asl,w)) THEN
      BETA_TAC THEN EXISTS_TAC `2 * (li - 0) + 1` THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`0`; `p:num`; `0`; db_safe; `out:byte list`; `[]:byte list`; `0`; `2`] THEN
      REWRITE_TAC[snappy_steps; APPEND_NIL; LENGTH; LE_0; DB_SAFE_FACTS] THEN
      REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC; DB_ARITH_TAC;
             (fun (asl,w) -> REWRITE_TAC[db_find_asm asl `SUB_LIST(0,li - 0) (inp:byte list) = inp`] (asl,w)) THEN NO_TAC;
             MATCH_MP_TAC(SET_RULE `s SUBSET c ==> s SUBSET a UNION b UNION c UNION d`) THEN REWRITE_TAC[DB_SAFE_FACTS] THEN NO_TAC;
             DB_EVENTS_TAC; DB_REG_TAC];
      (* from the mid to the end *)
      REWRITE_TAC[ensures] THEN BETA_TAC THEN X_GEN_TAC `s:armstate` THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
      W(fun (asl,w) ->
        let gth = TAC_PROOF((asl,db_G_tm), REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; DB_ARITH_TAC]) in
        let lth = BETA_RULE(REWRITE_RULE[ensures] (SPEC `n:num` (MP (SPEC_ALL loop) gth))) in
        let lth = REWRITE_RULE[db_find_asm asl `LENGTH(inp:byte list) = li`] lth in
        MATCH_MP_TAC lth THEN FIRST_ASSUM ACCEPT_TAC)];
    (* no loop *)
    DB_INIT_TAC THEN DB_RUN_TAC ~rws [] THEN
    DB_TO_Q_TAC `0` `inp:byte list` `out:byte list`]);;
let DB_TAG = db_tag_proof (DB_TAG_LIT, DB_TAG_LONGLIT, DB_TAG_COPY4, DB_TAG_C1_FAR, DB_TAG_C2_FAR,
                           DB_TAG_CHUNK, (fun k -> el k DB_TAG_NEAR1), (fun k -> el k DB_TAG_NEAR2));;
let DB_LOOP = db_loop_proof (DB_TAG, DB_J, DB_E);;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  DB_MAIN_TAC DB_LOOP);;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
