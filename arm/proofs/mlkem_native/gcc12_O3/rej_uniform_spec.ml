(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform rejection sampling for ML-KEM, as inlined by gcc 12 with -O3.     *)
(* At -O2 the sampling is the function mlk_rej_uniform_c.constprop.0 (see    *)
(* mlkem_native/README.md), but at -O3 gcc inlines it into its callers,      *)
(* mlkem_poly_rej_uniform and mlkem_poly_rej_uniform_x4, which contain ten   *)
(* copies of its loop with different registers and slightly different       *)
(* control flow. This file has the lemmas about the samples, as at -O2, and  *)
(* a tool that proves, for one such copy in the image, the combined theorem  *)
(* of correctness and memory safety with its events, from the loop header to *)
(* its exit, and the correctness theorem without the events.                 *)
(*                                                                           *)
(* Each copy samples from a buffer buf of buflen bytes, with a pointer       *)
(* register that goes from buf to buf + buflen in steps of 3, compared with  *)
(* a register holding buf + buflen, and a counter register that starts at    *)
(* offset < 256 and is the index of the next coefficient stored at r. It     *)
(* stops as soon as the counter is 256 or the buffer is exhausted, at the    *)
(* two exits of the loop, which may be the same point. The theorems have the *)
(* same hypotheses and results as those for mlk_rej_uniform_c at -O2, except *)
(* that offset < 256, since the callers only enter the loop then, and that   *)
(* the result is in the counter register and the exit reached is given by    *)
(* whether there are 256 coefficients.                                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/base.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(* ------------------------------------------------------------------------- *)
(* The sampling as in the specification of the hand-written kernel, where    *)
(* the input buffer is a list of 12-bit words (two from each 3 bytes).       *)
(* ------------------------------------------------------------------------- *)

let REJ_SAMPLE = define
 `REJ_SAMPLE l = FILTER (\x. val x < 3329) (MAP (word_zx:12 word->int16) l)`;;

let REJ_SAMPLE_EMPTY_STMT =
  `REJ_SAMPLE [] = []`;;

let REJ_SAMPLE_EMPTY = assume_spec REJ_SAMPLE_EMPTY_STMT;;

let REJ_SAMPLE_APPEND_STMT =
  `!l1 l2. REJ_SAMPLE(APPEND l1 l2) =
           APPEND (REJ_SAMPLE l1) (REJ_SAMPLE l2)`;;

let REJ_SAMPLE_APPEND = assume_spec REJ_SAMPLE_APPEND_STMT;;

let VAL_WORD_ZX_12_16_STMT =
  `!x:12 word. val(word_zx x:int16) = val x`;;

let VAL_WORD_ZX_12_16 = assume_spec VAL_WORD_ZX_12_16_STMT;;

let REJ_SAMPLE_PAIR_STMT =
  `!v0 v1:12 word.
        REJ_SAMPLE [v0; v1] =
        APPEND (if val v0 < 3329 then [word_zx v0] else [])
               (if val v1 < 3329 then [word_zx v1] else [])`;;

let REJ_SAMPLE_PAIR = assume_spec REJ_SAMPLE_PAIR_STMT;;

(* ------------------------------------------------------------------------- *)
(* The bytes of the group of 3 bytes giving the 12-bit words 2 * i and       *)
(* 2 * i + 1 in the list.                                                    *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_12 = DIMINDEX_CONV `dimindex(:12)`;;
let DIMINDEX_24 = DIMINDEX_CONV `dimindex(:24)`;;

let REJ_GROUP_BYTES_STMT =
  `!buf n (l:(12 word)list) i s:armstate.
        read (memory :> bytes(buf,n)) s = num_of_wordlist l /\
        8 * n = 12 * LENGTH l /\ 3 * i + 3 <= n
        ==> !k. k < 3
                ==> read (memory :> bytes8(word_add buf (word(3 * i + k)))) s =
                    word_subword (word_join (EL (2 * i + 1) l) (EL (2 * i) l)
                                  :24 word) (8 * k,8)`;;

let REJ_GROUP_BYTES = assume_spec REJ_GROUP_BYTES_STMT;;

(* ------------------------------------------------------------------------- *)
(* The signed comparisons of small 32-bit numbers and the 16-bit values      *)
(* stored.                                                                   *)
(* ------------------------------------------------------------------------- *)

let WORD_CMP_32_SFLAGS_STMT =
  `!x y. x < 2147483648 /\ y < 2147483648
         ==> (ival(word_sub (word x) (word y):int32) < &0 <=> x < y) /\
             (ival(word x:int32) - &y =
              ival(word_sub (word x) (word y):int32)) /\
             (ival(word x:int32) - ival(word y:int32) =
              ival(word_sub (word x) (word y):int32))`;;

let WORD_CMP_32_SFLAGS = assume_spec WORD_CMP_32_SFLAGS_STMT;;

let WORD_ZX_32_64_SMALL_STMT =
  `!n. n < 4294967296 ==> word_zx(word n:int32):int64 = word n`;;

let WORD_ZX_32_64_SMALL = assume_spec WORD_ZX_32_64_SMALL_STMT;;

let WORD_ZX_STORED_STMT =
  `!n. n < 65536
       ==> word_zx(word n:int32):int16 = word n /\
           word_zx(word n:int64):int16 = word n /\
           word_zx(word_zx(word n:int64):int32):int16 = word n`;;

let WORD_ZX_STORED = assume_spec WORD_ZX_STORED_STMT;;

(* ------------------------------------------------------------------------- *)
(* Reading lists of 16-bit words, built up element by element.               *)
(* ------------------------------------------------------------------------- *)

let READ_BYTES16_APPEND_STMT =
  `!(a:int64) (l1:int16 list) (l2:int16 list) s:armstate.
     read (memory :> bytes(a,2 * LENGTH l1)) s = num_of_wordlist l1 /\
     read (memory :> bytes(word_add a (word(2 * LENGTH l1)),2 * LENGTH l2)) s =
     num_of_wordlist l2
     ==> read (memory :> bytes(a,2 * LENGTH(APPEND l1 l2))) s =
         num_of_wordlist(APPEND l1 l2)`;;

let READ_BYTES16_APPEND = assume_spec READ_BYTES16_APPEND_STMT;;

let READ_BYTES16_CONS_STMT =
  `!(a:int64) x (l:int16 list) s:armstate.
     read (memory :> bytes16 a) s = x /\
     read (memory :> bytes(word_add a (word 2),2 * LENGTH l)) s =
     num_of_wordlist l
     ==> read (memory :> bytes(a,2 * LENGTH(CONS x l))) s =
         num_of_wordlist(CONS x l)`;;

let READ_BYTES16_CONS = assume_spec READ_BYTES16_CONS_STMT;;

let READ_BYTES16_NIL_STMT =
  `!(a:int64) s:armstate.
     read (memory :> bytes(a,2 * LENGTH([]:int16 list))) s =
     num_of_wordlist([]:int16 list)`;;

let READ_BYTES16_NIL = assume_spec READ_BYTES16_NIL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Taking initial segments of the sampled list.                              *)
(* ------------------------------------------------------------------------- *)

let SUB_LIST_APPEND_RIGHT = prove
 (`!l1 l2:A list n.
        LENGTH l1 <= n
        ==> SUB_LIST(0,n) (APPEND l1 l2) =
            APPEND l1 (SUB_LIST(0,n - LENGTH l1) l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; LENGTH; SUB_0] THEN
  X_GEN_TAC `l2:A list` THEN INDUCT_TAC THEN
  REWRITE_TAC[LE; NOT_SUC; LE_SUC; SUB_LIST_CLAUSES; SUB_SUC; CONS_11] THEN
  ASM_SIMP_TAC[]);;

let SUB_LIST_REJ_SAMPLE_PREFIX_STMT =
  `!(l:(12 word)list) k m.
        m <= LENGTH(REJ_SAMPLE(SUB_LIST(0,k) l)) \/ LENGTH l <= k
        ==> SUB_LIST(0,m) (REJ_SAMPLE l) =
            SUB_LIST(0,m) (REJ_SAMPLE(SUB_LIST(0,k) l))`;;

let SUB_LIST_REJ_SAMPLE_PREFIX = assume_spec SUB_LIST_REJ_SAMPLE_PREFIX_STMT;;

(* ------------------------------------------------------------------------- *)
(* A copy of the loop in the image: the labels of its header and exits (the  *)
(* same label if there is one exit), the registers for the pointer, the end  *)
(* of the buffer, the counter and the output, the registers holding          *)
(* constants and their values, the registers holding the two 12-bit fields   *)
(* of a group after the seven instructions from the header that compute      *)
(* them, and the registers that the loop changes.                            *)
(* ------------------------------------------------------------------------- *)

type rej_loop =
  { rej_exec : thm * thm option array;
    rej_header : string;
    rej_full : string;
    rej_end : string;
    rej_ptr : string;
    rej_endreg : string;
    rej_ctr : string;
    rej_out : string;
    rej_consts : (string * int) list;
    rej_fields : string * string;
    rej_regs : string list };;

let rej_loop_pc_post l =
  if l.rej_full = l.rej_end then "pc + " ^ l.rej_full
  else "pc + (if offset + outlen = 256 then " ^ l.rej_full ^
       " else " ^ l.rej_end ^ ")";;

let rej_loop_consts l =
  String.concat " /\\ "
   (map (fun (r,v) -> "read " ^ r ^ " s = word " ^ string_of_int v)
        l.rej_consts);;

let rej_loop_hyps =
  "offset < 256 /\\ 3 <= buflen /\\ buflen <= 4096 /\\
   8 * buflen = 12 * LENGTH inlist /\\
   ALL (nonoverlapping (word_add r (word(2 * offset)),2 * (256 - offset)))
       [(word pc,libmlkem_size); (buf,buflen)]";;

let rej_loop_pre l events =
  "(\\s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O3_mc /\\
        read PC s = word(pc + " ^ l.rej_header ^ ") /\\
        read " ^ l.rej_out ^ " s = r /\\
        read " ^ l.rej_ctr ^ " s = word offset /\\
        read " ^ l.rej_ptr ^ " s = buf /\\
        read " ^ l.rej_endreg ^ " s = word_add buf (word buflen) /\\
        " ^ rej_loop_consts l ^ " /\\
        wordlist_from_memory(buf,LENGTH inlist) s = inlist" ^
  (if events then " /\\ read events s = e)" else ")");;

let rej_loop_result l =
  "(let inlist' = MAP (word_zx:12 word->16 word) inlist in
    let outlist =
      SUB_LIST (0,256 - offset) (FILTER (\\x. val x < 3329) inlist') in
    let outlen = LENGTH outlist in
    read PC s = word(" ^ rej_loop_pc_post l ^ ") /\\
    read " ^ l.rej_ctr ^ " s = word(offset + outlen) /\\
    wordlist_from_memory(word_add r (word(2 * offset)),outlen) s = outlist)";;

let rej_loop_frame l =
  "(MAYCHANGE [" ^ String.concat "; " ("PC" :: l.rej_regs) ^ "] ,,
    MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
    MAYCHANGE [memory :> bytes(word_add r (word(2 * offset)),
                               2 * (256 - offset))])";;

let rej_loop_full_goal l =
  parse_term
   ("exists f_events.
      forall e r offset buf buflen (inlist:(12 word)list) pc.
       " ^ rej_loop_hyps ^ "
       ==> ensures arm " ^ rej_loop_pre l true ^ "
            (\\s. " ^ rej_loop_result l ^ " /\\
                 (exists e2.
                    read events s = APPEND e2 e /\\
                    e2 = f_events r offset buf buflen inlist pc /\\
                    memaccess_inbounds e2 [buf,buflen]
                      [word_add r (word(2 * offset)),2 * (256 - offset)]))
            " ^ rej_loop_frame l);;

let rej_loop_correct_goal l =
  parse_term
   ("forall r offset buf buflen (inlist:(12 word)list) pc.
       " ^ rej_loop_hyps ^ "
       ==> ensures arm " ^ rej_loop_pre l false ^ "
            (\\s. " ^ rej_loop_result l ^ ")
            " ^ rej_loop_frame l);;

(* ------------------------------------------------------------------------- *)
(* Tactics for simulating the code for one group of 3 bytes, containing      *)
(* the two 12-bit values n0 and n1, where L is the list sampled so far.      *)
(* ------------------------------------------------------------------------- *)

(*** The PC in the current state ***)

let current_pc (asl,w) =
  let s = rand w in
  let th = snd(find (fun (_,th) -> try let l,_ = dest_eq(concl th) in
                                       l = mk_comb(`read PC`,s)
                                   with Failure _ -> false) asl) in
  rhs(concl th);;

(*** Whether the instruction at the current PC is a 16-bit store ***)

let rej_at_store exec g =
  try let p = rand(current_pc g) in
      let ofs = if is_var p then 0 else dest_small_numeral(rand p) in
      match (snd exec).(ofs) with
        Some th ->
          let i = rand(snd(dest_imp(snd(strip_forall(concl th))))) in
          fst(dest_const(fst(strip_comb i))) = "arm_STRH"
      | None -> false
  with Failure _ -> false;;

(*** Decide a condition by arithmetic, keeping it as an assumption ***)

let DECIDE_PROP_TAC c =
  (SUBGOAL_THEN c
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO th]) THEN
               ASSUME_TAC th) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg c)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO th]) THEN
               ASSUME_TAC th) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]);;

(*** Decide all the flags, including the signed ones, where possible ***)

let DECIDE_SFLAGS_TAC =
  W(fun (asl,w) ->
     let ps = mapfilter (fun (_,th) ->
       let l,r = dest_eq(concl th) in
       let f = rand(rator l) in
       if mem f [`CF`;`ZF`;`NF`;`VF`] && not(r = `T` || r = `F`) then r
       else failwith "") asl in
     MAP_EVERY (fun p -> TRY(DECIDE_PROP_TAC p)) ps);;

let CMP_SFLAGS_TAC pat th =
  W(fun (asl,w) ->
    let tms = setify (find_terms (can (term_match [] pat))
                                 (list_mk_conj(map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      let x = rand(lhand t) and y = rand(rand t) in
      MP_TAC(SPECL [x;y] th) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) tms);;

let W32S_DECIDE_FLAGS_TAC =
  W32_SMALL_TAC THEN
  CMP_SFLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS THEN
  CMP_SFLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_SFLAGS THEN
  DECIDE_SFLAGS_TAC;;

(*** The comparison of the pointer with the end of the buffer ***)

let REJ_PTR_FLAGS_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`]) THEN
  CMP_SFLAGS_TAC `word_sub (word x) (word y):int64` WORD_CMP_64_FLAGS THEN
  DECIDE_SFLAGS_TAC;;

(*** Decide the conditions in the flags set by the CCMP instructions ***)

let DECIDE_COND_TAC =
  W(fun (asl,w) ->
     let conds = setify(mapfilter (fun (_,th) ->
        let l,r = dest_eq(concl th) in
        if mem (rand(rator l)) [`CF`;`ZF`;`NF`;`VF`] && is_cond r
        then lhand(rator r) else failwith "") asl) in
     MAP_EVERY DECIDE_PROP_TAC conds);;

(*** Decide the condition of a conditional branch ***)

let DECIDE_BRANCH_TAC =
  FIRST_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if not (is_cond r) || not(can (term_match [] `read PC s`) l)
    then failwith "DECIDE_BRANCH_TAC" else
    DECIDE_PROP_TAC (lhand(rator r)));;

(*** Replace the value of a register by an equal one ***)

let REPLACE_REG_TAC r t =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && (try rand(rator(lhs c)) = r with Failure _ -> false)
    then ASSUME_TAC(REWRITE_RULE[word_zx]
                     (TRANS th (BITBLAST_RULE(mk_eq(rhs c,t)))))
    else failwith "REPLACE_REG_TAC");;

(*** Replace 64-bit views of small 32-bit numbers ***)

let W64_SMALL_TAC =
  W(fun (asl,w) ->
    let tms = setify (find_terms
      (can (term_match [] `word_zx(word n:int32):int64`))
      (list_mk_conj(w::map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      MP_TAC(SPEC (rand(rand t)) WORD_ZX_32_64_SMALL) THEN
      ANTS_TAC THENL
       [SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                             REWRITE_TAC[th])]) tms);;

let REJ_NORM_TAC =
  TRY W32_SMALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64; GSYM WORD_ADD]) THEN
  TRY W64_SMALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64; GSYM WORD_ADD;
                              GSYM WORD_ADD_ASSOC]);;

let REJ_STRIP_EXISTS_ASSUM_TAC =
  FIRST_X_ASSUM(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC));;

(*** The setup for group number idx, splitting into cases on n0 and n1 ***)

let REJ_GROUP_TAC idx =
  let ix t = subst [idx,`i:num`] t in
  let e0 = ix `EL (2 * i) inlist:12 word`
  and e1 = ix `EL (2 * i + 1) inlist:12 word` in
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_SAMPLE_APPEND; LENGTH_APPEND;
                              REJ_SAMPLE_PAIR]) THEN
  REWRITE_TAC[REJ_SAMPLE_APPEND; REJ_SAMPLE_PAIR] THEN
  ABBREV_TAC (ix `L = REJ_SAMPLE(SUB_LIST(0,2 * i) inlist)`) THEN
  ENSURES_INIT_TAC "s0" THEN REJ_STRIP_EXISTS_ASSUM_TAC THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`; `inlist:(12 word)list`; idx;
                `s0:armstate`] REJ_GROUP_BYTES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC e0 VAL_BOUND) THEN MP_TAC(ISPEC e1 VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC (mk_eq(`n0:num`,mk_comb(`val:12 word->num`,e0))) THEN
  ABBREV_TAC (mk_eq(`n1:num`,mk_comb(`val:12 word->num`,e1))) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   (mk_conj(mk_eq(mk_comb(`word_zx:12 word->int16`,e0),`word n0:int16`),
            mk_eq(mk_comb(`word_zx:12 word->int16`,e1),`word n1:int16`)))
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[word_zx] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `n0:num` (concl th) && free_in `L:int16 list` (concl th))) THEN
  ASM_CASES_TAC `n0 < 3329` THEN ASM_CASES_TAC `n1 < 3329` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE
   (REWRITE_CONV[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THENC
    NUM_REDUCE_CONV));;

(*** The indices of the two stores, which use UXTW register offsets ***)

let REJ_UXTW_TAC =
  MP_TAC(SPEC `offset + LENGTH(L:int16 list)` VAL_WORD_ZX_UXTW) THEN
  MP_TAC(SPEC `(offset + LENGTH(L:int16 list)) + 1` VAL_WORD_ZX_UXTW) THEN
  REPEAT(ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC]);;

(*** One step, recognizing the two values once they have been computed ***)

let REJ_STEP_TAC l idx n =
  (fun g -> if rej_at_store l.rej_exec g then REJ_UXTW_TAC g
            else ALL_TAC g) THEN
  ARM_STEPS_TAC l.rej_exec [n] THEN
  (if n = 7 then
     let e0 = subst [idx,`i:num`] `EL (2 * i) inlist:12 word`
     and e1 = subst [idx,`i:num`] `EL (2 * i + 1) inlist:12 word` in
     let r0 = mk_const(fst l.rej_fields,[])
     and r1 = mk_const(snd l.rej_fields,[]) in
     REPLACE_REG_TAC r0 (mk_comb(`word_zx:12 word->int64`,e0)) THEN
     REPLACE_REG_TAC r1 (mk_comb(`word_zx:12 word->int64`,e1)) THEN
     RULE_ASSUM_TAC(REWRITE_RULE
      [ASSUME(mk_eq(mk_comb(`val:12 word->num`,e0),`n0:num`));
       ASSUME(mk_eq(mk_comb(`val:12 word->num`,e1),`n1:num`))])
   else ALL_TAC) THEN
  REJ_NORM_TAC THEN TRY DECIDE_COND_TAC THEN
  TRY W32S_DECIDE_FLAGS_TAC THEN TRY REJ_PTR_FLAGS_TAC THEN
  TRY DECIDE_BRANCH_TAC;;

(*** Simulate from the head of the group until the PC is a target ***)

let rec REJ_RUN_TAC l idx n targets (asl,w) =
  (REJ_STEP_TAC l idx n THEN
   (fun g -> if mem (current_pc g) targets then ALL_TAC g
             else REJ_RUN_TAC l idx (n + 1) targets g)) (asl,w);;

let rej_target lab = parse_term("word(pc + " ^ lab ^ "):int64");;

(*** A stored coefficient, read at an address equal to the one written ***)

let READ16_TAC (asl,w) =
  let a = rand(rand(rand(rator(lhs w)))) and s = rand(lhs w) in
  let ths = filter (fun th ->
    try let l = lhs(concl th) in
        rand l = s && can (term_match [] `read (memory :> bytes16 a) s`) l
    with Failure _ -> false) (map snd asl) in
  let tac th =
    let a' = rand(rand(rand(rator(lhs(concl th))))) in
    SUBGOAL_THEN (mk_eq(a,a')) SUBST1_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
      REWRITE_TAC[th] THEN
      ASM_SIMP_TAC[WORD_ZX_STORED; ARITH_RULE `n < 4096 ==> n < 65536`]] in
  FIRST (map tac ths) (asl,w);;

(*** In the last group, derive that the buffer is exhausted if possible ***)

let RESOLVE_EXIT_TAC =
  FIRST_ASSUM(fun th ->
    if is_disj(concl th) && free_in `buflen:num` (concl th) then
      let a = lhand(concl th) in
      TRY(SUBGOAL_THEN a ASSUME_TAC THENL
           [MP_TAC th THEN SIMPLE_ARITH_TAC; ALL_TAC])
    else failwith "RESOLVE_EXIT_TAC");;

(*** If so, the number of fields, which gives the comparison of the ***)
(*** pointer with the end of the buffer                              ***)

let REJ_EXHAUST_TAC (asl,w) =
  let a = `buflen < 3 * (N + 2)` in
  if exists (fun (_,th) -> concl th = a) asl then
    FIRST_ASSUM(fun th ->
      if is_imp(concl th) && lhand(concl th) = a
      then ASSUME_TAC(MP th (ASSUME a)) else NO_TAC) (asl,w)
  else ALL_TAC (asl,w);;

(*** In the last group, the part of the group's values within the limit ***)

let SUBLIST_EVAL_TAC =
  REWRITE_TAC[APPEND] THEN
  W(fun (asl,w) ->
    let t = find_term (can (term_match [] `SUB_LIST (0,c) (l:int16 list)`))
                      w in
    let c = rand(rand(rator t)) and l = rand t in
    (SUBGOAL_THEN (mk_eq(t,l)) SUBST1_TAC THENL
      [MATCH_MP_TAC SUB_LIST_REFL THEN REWRITE_TAC[LENGTH] THEN
       SIMPLE_ARITH_TAC;
       ALL_TAC]) ORELSE
    (SUBGOAL_THEN (mk_eq(c,`1`)) SUBST1_TAC THENL
      [SIMPLE_ARITH_TAC;
       REWRITE_TAC[SUB_LIST_1; LENGTH; LT_0; LT_REFL; EL; HD]]));;

(*** In the last group, the exit, given by whether there are 256 samples ***)

let REJ_PC_COND_TAC =
  W(fun (asl,w) ->
    let cs = setify(map (lhand o rator)
               (find_terms (fun t -> is_cond t && type_of t = `:num` &&
                                     frees(lhand(rator t)) <> [] &&
                                     free_in `offset:num` (lhand(rator t)))
                           w)) in
    let tac c =
      let dtac = REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
                 SIMPLE_ARITH_TAC in
      (SUBGOAL_THEN c (fun th -> REWRITE_TAC[EQT_INTRO th]) THENL
        [dtac; ALL_TAC]) ORELSE
      (SUBGOAL_THEN (mk_neg c) (fun th -> REWRITE_TAC[EQF_INTRO th]) THENL
        [dtac; ALL_TAC]) in
    MAP_EVERY tac cs);;

(* ------------------------------------------------------------------------- *)
(* The combined proof of correctness and memory safety with the events,      *)
(* which are a function of the arguments and the list of fields inlist. They *)
(* are given by a template with the index of the last group of 3 bytes that  *)
(* is read, mlkem_native_rej_groups, and with the events of each group by    *)
(* cases on which of its two fields are accepted and, for the last group, on *)
(* whether the result is then full, as at -O2. The number N of groups before *)
(* the last one is the least such that the following group would go beyond  *)
(* the buffer or the coefficients from the group after N would reach 256.    *)
(* ------------------------------------------------------------------------- *)

let mlkem_native_rej_groups = new_definition
 `mlkem_native_rej_groups offset buflen (inlist:(12 word)list) =
    minimal n. buflen < 3 * (n + 2) \/
               256 <= offset +
                      LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * (n + 1)) inlist))`;;

let REJ_LOOP_TEMPLATE =
 `\(r:int64) (offset:num) (buf:int64) (buflen:num) (inlist:(12 word)list)
   (pc:num).
   APPEND (f_ev_ret r offset buf buflen inlist pc)
    (APPEND
      (ENUMERATEL (mlkem_native_rej_groups offset buflen inlist + 1)
        (\i. if i = mlkem_native_rej_groups offset buflen inlist
             then
              (if val(EL (2 * i) inlist) < 3329
               then
                (if offset + LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * i) inlist)) =
                    255
                 then f_ev_bx r offset buf buflen inlist pc i
                 else if val(EL (2 * i + 1) inlist) < 3329
                 then
                  (if offset + LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * i) inlist)) =
                      254
                   then f_ev_ax r offset buf buflen inlist pc i
                   else f_ev_ab r offset buf buflen inlist pc i)
                 else f_ev_bb r offset buf buflen inlist pc i)
               else
                (if val(EL (2 * i + 1) inlist) < 3329
                 then
                  (if offset + LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * i) inlist)) =
                      255
                   then f_ev_cx r offset buf buflen inlist pc i
                   else f_ev_cb r offset buf buflen inlist pc i)
                 else f_ev_db r offset buf buflen inlist pc i))
             else
              (if val(EL (2 * i) inlist) < 3329
               then
                (if val(EL (2 * i + 1) inlist) < 3329
                 then f_ev_a r offset buf buflen inlist pc i
                 else f_ev_b r offset buf buflen inlist pc i)
               else
                (if val(EL (2 * i + 1) inlist) < 3329
                 then f_ev_c r offset buf buflen inlist pc i
                 else f_ev_d r offset buf buflen inlist pc i))))
      (f_ev_prol r offset buf buflen inlist pc))
   :(uarch_event)list`;;

let REJ_LOOP_INTRO_TAC =
  CONCRETIZE_F_EVENTS_TAC REJ_LOOP_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `offset:num`; `buf:int64`; `buflen:num`;
    `inlist:(12 word)list`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`buf:int64`; `LENGTH(inlist:(12 word)list)`;
    `buflen:num`; `inlist:(12 word)list`]
   (INST_TYPE [`:12`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  ASM_REWRITE_TAC[DIMINDEX_12] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM REJ_SAMPLE] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM REJ_SAMPLE] THEN
  ABBREV_TAC `outlist = SUB_LIST (0,256 - offset) (REJ_SAMPLE inlist)` THEN
  MP_TAC(ISPECL
   [`word_add r (word(2 * offset)):int64`; `LENGTH(outlist:int16 list)`;
    `2 * LENGTH(outlist:int16 list)`; `outlist:int16 list`]
   (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * l = 8 * 2 * l`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]);;

let REJ_LOOP_N_TAC =
  SUBGOAL_THEN
   `?N. buflen < 3 * (N + 2) \/
        256 <= offset + LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * (N + 1)) inlist))`
  MP_TAC THENL
   [EXISTS_TAC `buflen:num` THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num`
   (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `mlkem_native_rej_groups offset buflen inlist = N`
  SUBST1_TAC THENL
   [REWRITE_TAC[mlkem_native_rej_groups] THEN
    MATCH_MP_TAC MINIMAL_UNIQUE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_LT; NOT_LE] THEN DISCH_TAC;;

let rej_loop_inv l =
  parse_term
   ("\\i s.
      read " ^ l.rej_out ^ " s = r /\\
      read " ^ l.rej_endreg ^ " s = word_add buf (word buflen) /\\
      " ^ rej_loop_consts l ^ " /\\
      read(memory :> bytes(buf,buflen)) s = num_of_wordlist inlist /\\
      (if i <= N then
        read " ^ l.rej_ctr ^ " s =
        word(offset + LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * i) inlist))) /\\
        read " ^ l.rej_ptr ^ " s = word_add buf (word(3 * i)) /\\
        read(memory :> bytes(word_add r (word(2 * offset)),
               2 * LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * i) inlist)))) s =
        num_of_wordlist(REJ_SAMPLE(SUB_LIST(0,2 * i) inlist))
       else
        read " ^ l.rej_ctr ^ " s =
        word(offset + LENGTH(outlist:int16 list)) /\\
        read(memory :> bytes(word_add r (word(2 * offset)),
                             2 * LENGTH outlist)) s =
        num_of_wordlist outlist)");;

let REJ_LOOP_PROL_TAC =
  REWRITE_TAC[LE_0] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY; LENGTH;
              ADD_CLAUSES; WORD_ADD_0; READ_COMPONENT_COMPOSE;
              READ_BYTES_TRIVIAL; num_of_wordlist] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The conditions in the template for group i, decided from the facts  ***)
(*** for it before the simulation, which loses the abbreviations n0, n1 ***)

let rej_free_conds tm =
  let rec go bound tm acc =
    match tm with
      Comb(Comb(Comb(Const("COND",_),p),a),b) ->
        let acc' = if intersect (frees p) bound = [] && not (mem p acc)
                   then p::acc else acc in
        go bound p (go bound a (go bound b acc'))
    | Comb(l,r) -> go bound l (go bound r acc)
    | Abs(v,b) -> go (v::bound) b acc
    | _ -> acc in
  go [] tm [];;

let REJ_DECIDE_ONE_TAC p =
  let tac = (ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE SIMPLE_ARITH_TAC ORELSE
            (ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC) in
  (SUBGOAL_THEN p (fun th -> REWRITE_TAC[EQT_INTRO th]) THENL
    [tac; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg p) (fun th -> REWRITE_TAC[EQF_INTRO th]) THENL
    [tac; ALL_TAC]);;

let REJ_DECIDE_CONDS_TAC =
  W(fun (asl,w) ->
    let ps = rej_free_conds w in
    EVERY (map (fun p -> TRY(REJ_DECIDE_ONE_TAC p)) ps));;

let REJ_PRESELECT_TAC =
  REWRITE_TAC[ENUMERATEL_ADD1] THEN REJ_DECIDE_CONDS_TAC THEN
  REJ_DECIDE_CONDS_TAC;;

let REJ_OLD_EVENTS_TAC =
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  W(fun (asl,w) ->
    let is_e2eq t =
      is_eq t && is_var(lhs t) && fst(dest_var(lhs t)) = "e2" in
    let is_macc t =
      match strip_comb t with
        Const("memaccess_inbounds",_),_ -> true | _ -> false in
    let eqths = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_e2eq c then th
      else if is_conj c && is_e2eq(lhand c) then CONJUNCT1 th
      else failwith "") asl
    and mths = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_conj c && is_e2eq(lhand c) then CONJUNCT2 th
      else if is_macc c then th else failwith "") asl in
    FIRST(map (fun eqth -> FIRST(map (fun mth ->
      ACCEPT_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV) (SUBS[eqth] mth)))
      mths)) eqths));;

let REJ_FULL_DISCHARGE_TAC =
  TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
        is_eq(concl th) && rhs(concl th) = `L:int16 list`))) THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ a ==> a /\ b`) THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[memaccess_inbounds; memaccess_inbounds_def;
                  ALL; EX; FST; SND] THEN
      REPEAT CONJ_TAC THEN
      TRY(REPEAT ((DISJ1_TAC THEN CONTAINED_ASM_TAC) ORELSE DISJ2_TAC ORELSE
                  CONTAINED_ASM_TAC) THEN NO_TAC);
      REJ_OLD_EVENTS_TAC];
    FULL_UNIFY_F_EVENTS_TAC ORELSE
    (CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC)];;

let REJ_FULL_CLOSE_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [REJ_FULL_DISCHARGE_TAC;
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN AP_TERM_TAC THEN
    SIMPLE_ARITH_TAC;
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
    MATCH_MP_TAC READ_BYTES16_APPEND THEN ASM_REWRITE_TAC[APPEND] THEN
    REPEAT(MATCH_MP_TAC READ_BYTES16_CONS THEN CONJ_TAC THENL
            [READ16_TAC; ALL_TAC]) THEN
    REWRITE_TAC[READ_BYTES16_NIL]];;

let REJ_LOOP_NORMAL_TAC l =
  SUBGOAL_THEN `i <= N /\ i + 1 <= N /\ i + 1 < N + 1 /\ ~(i = N)`
  STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `N:num` (concl th)
    then STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `i < N`))
    else failwith "") THEN
  SUBGOAL_THEN `2 * i + 2 <= LENGTH(inlist:(12 word)list)` ASSUME_TAC
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `SUB_LIST(0,2 * (i + 1)) inlist =
    APPEND (SUB_LIST(0,2 * i) inlist)
           [EL (2 * i) inlist:12 word; EL (2 * i + 1) inlist]`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`; SUB_LIST_0_SNOC2];
    ALL_TAC] THEN
  REJ_GROUP_TAC `i:num` THEN
  (SUBGOAL_THEN `offset + LENGTH(L:int16 list) < 256` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  REJ_PRESELECT_TAC THEN
  REJ_RUN_TAC l `i:num` 1 [rej_target l.rej_header] THEN REJ_FULL_CLOSE_TAC;;

let REJ_LOOP_LAST_TAC l =
  SUBGOAL_THEN `i:num = N` SUBST_ALL_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LE_REFL; LT_REFL; ARITH_RULE `~(N + 1 <= N)`] THEN
  SUBGOAL_THEN `?k. buflen = 3 * k /\ LENGTH(inlist:(12 word)list) = 2 * k`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `EVEN(LENGTH(inlist:(12 word)list))` MP_TAC THENL
     [SUBGOAL_THEN `3 * LENGTH(inlist:(12 word)list) = 2 * buflen` MP_TAC
      THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o AP_TERM `EVEN`)] THEN
      REWRITE_TAC[EVEN_MULT; ARITH];
      REWRITE_TAC[EVEN_EXISTS] THEN MATCH_MP_TAC MONO_EXISTS THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `3 * (N + 1) <= buflen /\
    offset + LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * N) inlist)) < 256`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `N = 0` THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES;
                      REJ_SAMPLE_EMPTY; LENGTH] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `N - 1` o check (is_forall o concl)) THEN
      ASM_SIMP_TAC[ARITH_RULE
       `~(N = 0) ==> N - 1 < N /\ N - 1 + 1 = N /\ N - 1 + 2 = N + 1`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * N + 2 <= LENGTH(inlist:(12 word)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `buflen < 3 * (N + 2) ==> LENGTH(inlist:(12 word)list) <= 2 * (N + 1)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `3 * k < 3 * (N + 2) ==> k <= N + 1`)) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `outlist =
    APPEND (REJ_SAMPLE(SUB_LIST(0,2 * N) inlist))
     (SUB_LIST(0,256 - offset - LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * N) inlist)))
       (REJ_SAMPLE [EL (2 * N) inlist; EL (2 * N + 1) inlist]))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rhs(concl th) = `outlist:int16 list`)) THEN
    MP_TAC(ISPECL [`inlist:(12 word)list`; `2 * (N + 1)`; `256 - offset`]
      SUB_LIST_REJ_SAMPLE_PREFIX) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[ARITH_RULE `2 * (N + 1) = 2 * N + 2`; SUB_LIST_0_SNOC2;
             ASSUME `2 * N + 2 <= LENGTH(inlist:(12 word)list)`] THEN
    REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
    MATCH_MP_TAC SUB_LIST_APPEND_RIGHT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCARD_MATCHING_ASSUMPTIONS
   [`buflen = 3 * k`; `LENGTH(inlist:(12 word)list) = 2 * k`] THEN
  SUBGOAL_THEN
   `SUB_LIST(0,2 * (N + 1)) inlist =
    APPEND (SUB_LIST(0,2 * N) inlist)
           [EL (2 * N) inlist:12 word; EL (2 * N + 1) inlist]`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [SIMP_TAC[ARITH_RULE `2 * (N + 1) = 2 * N + 2`; SUB_LIST_0_SNOC2;
             ASSUME `2 * N + 2 <= LENGTH(inlist:(12 word)list)`];
    ALL_TAC] THEN
  REJ_GROUP_TAC `N:num` THEN
  MP_TAC(MATCH_MP (ARITH_RULE
   `offset + LENGTH(L:int16 list) < 256
    ==> 255 <= offset + LENGTH L \/
        254 <= offset + LENGTH L /\ offset + LENGTH L < 255 \/
        offset + LENGTH L < 254`)
   (ASSUME `offset + LENGTH(L:int16 list) < 256`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  RESOLVE_EXIT_TAC THEN REJ_EXHAUST_TAC THEN SUBLIST_EVAL_TAC THEN
  REJ_PRESELECT_TAC THEN REJ_PC_COND_TAC THEN
  REJ_RUN_TAC l `N:num` 1 (setify [rej_target l.rej_full;
                                    rej_target l.rej_end]) THEN
  REJ_FULL_CLOSE_TAC;;

let REJ_LOOP_EPIL_TAC =
  REWRITE_TAC[ARITH_RULE `~(N + 1 <= N)`] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e1:(uarch_event)list` STRIP_ASSUME_TAC o
                check (is_exists o concl)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `e1:(uarch_event)list`)) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let REJ_LOOP_FULL_TAC l =
  let pc1 = parse_term("pc + " ^ l.rej_header)
  and pc2 = parse_term
    (if l.rej_full = l.rej_end then "pc + " ^ l.rej_full
     else "pc + (if offset + LENGTH(outlist:int16 list) = 256 then " ^
          l.rej_full ^ " else " ^ l.rej_end ^ ")") in
  REJ_LOOP_INTRO_TAC THEN REJ_LOOP_N_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `N + 1` pc1 pc2 (rej_loop_inv l) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REJ_LOOP_PROL_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `i < N` THENL [REJ_LOOP_NORMAL_TAC l; REJ_LOOP_LAST_TAC l];
    REJ_LOOP_EPIL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The theorems for a copy of the loop: the combined one, and the            *)
(* correctness theorem without the events, for the correctness proofs of the *)
(* callers.                                                                  *)
(* ------------------------------------------------------------------------- *)

let ENSURES_WEAKEN_RULE = prove
 (`!step P P' Q Q' C:A->A->bool.
        ensures step P Q C
        ==> (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s)
            ==> ensures step P' Q' C`,
  MESON_TAC[ENSURES_PREPOSTCONDITION_THM]);;

let REJ_LOOP_FULL l = prove(rej_loop_full_goal l, REJ_LOOP_FULL_TAC l);;

let REJ_LOOP_CORRECT l fullth =
  prove(rej_loop_correct_goal l,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
    CHOOSE_THEN
     (MP_TAC o SPECL [`e:(uarch_event)list`; `r:int64`; `offset:num`;
                      `buf:int64`; `buflen:num`; `inlist:(12 word)list`;
                      `pc:num`]) fullth THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
    SIMP_TAC[]);;
