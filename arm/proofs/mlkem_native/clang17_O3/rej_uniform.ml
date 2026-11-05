(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform rejection sampling for ML-KEM, as inlined by clang 17 with -O3.   *)
(* At gcc -O2 the sampling is the function mlk_rej_uniform_c.constprop.0     *)
(* (see mlkem_native/README.md), but clang -O3, like gcc -O3, inlines it     *)
(* into its callers, mlkem_poly_rej_uniform and mlkem_poly_rej_uniform_x4,  *)
(* which contain two and eight copies of its loop with different registers. *)
(* This file has the lemmas about the samples, as at gcc -O3, and a tool     *)
(* that proves, for one such copy in the image, the combined theorem of      *)
(* correctness and memory safety with its events, from the loop header to    *)
(* its exit, and the correctness theorem without the events.                 *)
(*                                                                           *)
(* Each copy samples from a buffer of buflen bytes, 504 for the first three  *)
(* blocks of SHAKE128 output and 168 for each further block, at buf + ofs    *)
(* for a register holding buf. Unlike at gcc -O3, the loop has an index      *)
(* register that goes from 0 in steps of 3 and is compared with the constant *)
(* buflen - 2, the stores use a 64-bit counter register shifted left by one, *)
(* and the second 12-bit field of a group of 3 bytes is only computed, and   *)
(* in some copies its third byte only read, if there are fewer than 256      *)
(* coefficients after the first. The counter starts at offset < 256 and is   *)
(* the index of the next coefficient stored at r. The loop stops as soon as  *)
(* the counter is 256 or the buffer is exhausted, at the two exits of the    *)
(* loop, which may be the same point. The theorems have the same hypotheses  *)
(* and results as those for gcc -O3, except that buflen is fixed, and that   *)
(* the copies in mlkem_poly_rej_uniform_x4 for the first three blocks also   *)
(* leave in a register whether the counter is below 256, which the caller    *)
(* uses later.                                                               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(* ------------------------------------------------------------------------- *)
(* The sampling as in the specification of the hand-written kernel, where    *)
(* the input buffer is a list of 12-bit words (two from each 3 bytes).       *)
(* ------------------------------------------------------------------------- *)

let REJ_SAMPLE = define
 `REJ_SAMPLE l = FILTER (\x. val x < 3329) (MAP (word_zx:12 word->int16) l)`;;

let REJ_SAMPLE_EMPTY = prove
 (`REJ_SAMPLE [] = []`,
  REWRITE_TAC[REJ_SAMPLE; FILTER; MAP]);;

let REJ_SAMPLE_APPEND = prove
 (`!l1 l2. REJ_SAMPLE(APPEND l1 l2) =
           APPEND (REJ_SAMPLE l1) (REJ_SAMPLE l2)`,
  REWRITE_TAC[REJ_SAMPLE; MAP_APPEND; FILTER_APPEND]);;

let VAL_WORD_ZX_12_16 = prove
 (`!x:12 word. val(word_zx x:int16) = val x`,
  GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ARITH_TAC);;

let REJ_SAMPLE_PAIR = prove
 (`!v0 v1:12 word.
        REJ_SAMPLE [v0; v1] =
        APPEND (if val v0 < 3329 then [word_zx v0] else [])
               (if val v1 < 3329 then [word_zx v1] else [])`,
  REWRITE_TAC[REJ_SAMPLE; MAP; FILTER; VAL_WORD_ZX_12_16] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `val(v0:12 word) < 3329` THEN
  ASM_CASES_TAC `val(v1:12 word) < 3329` THEN ASM_REWRITE_TAC[APPEND]);;

(* ------------------------------------------------------------------------- *)
(* The bytes of the group of 3 bytes giving the 12-bit words 2 * i and       *)
(* 2 * i + 1 in the list.                                                    *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_12 = DIMINDEX_CONV `dimindex(:12)`;;
let DIMINDEX_24 = DIMINDEX_CONV `dimindex(:24)`;;

let REJ_GROUP_BYTES = prove
 (`!buf n (l:(12 word)list) i s:armstate.
        read (memory :> bytes(buf,n)) s = num_of_wordlist l /\
        8 * n = 12 * LENGTH l /\ 3 * i + 3 <= n
        ==> !k. k < 3
                ==> read (memory :> bytes8(word_add buf (word(3 * i + k)))) s =
                    word_subword (word_join (EL (2 * i + 1) l) (EL (2 * i) l)
                                  :24 word) (8 * k,8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_12; DIMINDEX_24; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `4096 * val (EL (2 * i + 1) (l:(12 word)list)) + val (EL (2 * i) l) =
    (num_of_wordlist l DIV 2 EXP (24 * i)) MOD 2 EXP 24`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`l:(12 word)list`; `2 * i`; `2`]
           NUM_OF_WORDLIST_SUB_LIST) THEN
    REWRITE_TAC[DIMINDEX_12; ARITH_RULE `12 * 2 * i = 24 * i`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `2 * i + 2 <= LENGTH(l:(12 word)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; SUB_LIST_SPLIT] THEN
    REWRITE_TAC[SUB_LIST_1; ARITH_RULE `1 + 1 = 2`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 * i + 2 <= l ==> 2 * i < l /\ 2 * i + 1 < l`] THEN
    REWRITE_TAC[APPEND; num_of_wordlist; DIMINDEX_12] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val (read (memory :> bytes8 (word_add buf (word (3 * i + k)))) s) =
    (num_of_wordlist (l:(12 word)list) DIV 2 EXP (8 * (3 * i + k))) MOD
    2 EXP (8 * 1)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
      check (fun th -> free_in `num_of_wordlist (l:(12 word)list)`
                               (concl th))) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
    REWRITE_TAC[GSYM READ_BYTES_BYTES8] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_8; ARITH_RULE `8 * (3 * i + k) = 24 * i + 8 * k`] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `MIN 8 8 = 8`] THEN ASM_ARITH_TAC);;

(*** The same for a buffer at buf + ofs, with the addresses of the bytes ***)
(*** in the form that the simulation gives for the loads                 ***)

let REJ_GROUP_BYTES_OFS = prove
 (`!buf ofs n (l:(12 word)list) i s:armstate.
        read (memory :> bytes(word_add buf (word ofs),n)) s =
        num_of_wordlist l /\
        8 * n = 12 * LENGTH l /\ 3 * i + 3 <= n
        ==> !k. k < 3
                ==> read (memory :> bytes8(word_add buf
                                            (word(3 * i + (ofs + k))))) s =
                    word_subword (word_join (EL (2 * i + 1) l) (EL (2 * i) l)
                                  :24 word) (8 * k,8)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REJ_GROUP_BYTES) THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The 16-bit values stored, and their offsets from r, as a 64-bit counter   *)
(* shifted left by one.                                                      *)
(* ------------------------------------------------------------------------- *)

let WORD_SHL_WORD_1 = prove
 (`!n. word_shl (word n:int64) 1 = word(2 * n)`,
  REWRITE_TAC[word_shl; EXP_1; WORD_MUL; WORD_VAL; WORD_MUL_SYM]);;

let WORD_ZX_32_64_SMALL = prove
 (`!n. n < 4294967296 ==> word_zx(word n:int32):int64 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_32] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let WORD_ZX_STORED = prove
 (`!n. n < 65536
       ==> word_zx(word n:int32):int16 = word n /\
           word_zx(word n:int64):int16 = word n /\
           word_zx(word_zx(word n:int64):int32):int16 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `n < 65536 ==> n < 18446744073709551616 /\ n < 4294967296`]);;

(* ------------------------------------------------------------------------- *)
(* Reading lists of 16-bit words, built up element by element.               *)
(* ------------------------------------------------------------------------- *)

let READ_BYTES16_APPEND = prove
 (`!(a:int64) (l1:int16 list) (l2:int16 list) s:armstate.
     read (memory :> bytes(a,2 * LENGTH l1)) s = num_of_wordlist l1 /\
     read (memory :> bytes(word_add a (word(2 * LENGTH l1)),2 * LENGTH l2)) s =
     num_of_wordlist l2
     ==> read (memory :> bytes(a,2 * LENGTH(APPEND l1 l2))) s =
         num_of_wordlist(APPEND l1 l2)`,
  REWRITE_TAC[LENGTH_APPEND; NUM_OF_WORDLIST_APPEND; LEFT_ADD_DISTRIB;
              READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; DIMINDEX_16] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`]);;

let READ_BYTES16_CONS = prove
 (`!(a:int64) x (l:int16 list) s:armstate.
     read (memory :> bytes16 a) s = x /\
     read (memory :> bytes(word_add a (word 2),2 * LENGTH l)) s =
     num_of_wordlist l
     ==> read (memory :> bytes(a,2 * LENGTH(CONS x l))) s =
         num_of_wordlist(CONS x l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `2 * SUC n = 2 + 2 * n`; num_of_wordlist] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; DIMINDEX_16] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    can (term_match [] `read (bytes16 a) s = x`) (concl th))) THEN
  REWRITE_TAC[BYTES16_WBYTES; VAL_READ_WBYTES; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIMINDEX_16] THEN ARITH_TAC);;

let READ_BYTES16_NIL = prove
 (`!(a:int64) s:armstate.
     read (memory :> bytes(a,2 * LENGTH([]:int16 list))) s =
     num_of_wordlist([]:int16 list)`,
  REWRITE_TAC[LENGTH; MULT_CLAUSES; READ_COMPONENT_COMPOSE;
              READ_BYTES_TRIVIAL; num_of_wordlist]);;

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

let SUB_LIST_REJ_SAMPLE_PREFIX = prove
 (`!(l:(12 word)list) k m.
        m <= LENGTH(REJ_SAMPLE(SUB_LIST(0,k) l)) \/ LENGTH l <= k
        ==> SUB_LIST(0,m) (REJ_SAMPLE l) =
            SUB_LIST(0,m) (REJ_SAMPLE(SUB_LIST(0,k) l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
     [GSYM(ISPECL [`l:(12 word)list`; `k:num`] SUB_LIST_TOPSPLIT)] THEN
    REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
    MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SUB_LIST_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* A copy of the loop in the image: the labels of its header and exits (the  *)
(* same label if there is one exit), the register holding buf and the offset *)
(* of the buffer from it, the index register, the length of the buffer, the  *)
(* registers for the counter and the output, the registers holding the two   *)
(* 12-bit fields of a group once they are computed, the register, if any,    *)
(* that the loop sets to 1 or 0 according as the counter is below 256 or     *)
(* not, and the registers that the loop changes.                             *)
(* ------------------------------------------------------------------------- *)

type rej_loop =
  { rej_exec : thm * thm option array;
    rej_header : string;
    rej_full : string;
    rej_end : string;
    rej_base : string;
    rej_ofs : int;
    rej_idx : string;
    rej_buflen : int;
    rej_ctr : string;
    rej_out : string;
    rej_fields : string * string;
    rej_flag : string option;
    rej_regs : string list };;

let rej_loop_buf l =
  if l.rej_ofs = 0 then "buf"
  else "word_add buf (word " ^ string_of_int l.rej_ofs ^ ")";;

let rej_loop_pc_post l =
  if l.rej_full = l.rej_end then "pc + " ^ l.rej_full
  else "pc + (if offset + outlen = 256 then " ^ l.rej_full ^
       " else " ^ l.rej_end ^ ")";;

let rej_loop_flag l len =
  match l.rej_flag with
    None -> ""
  | Some f -> "read " ^ f ^ " s = (if offset + " ^ len ^
              " < 256 then word 1 else word 0) /\\ ";;

let rej_loop_hyps l =
  "offset < 256 /\\ buflen = " ^ string_of_int l.rej_buflen ^ " /\\
   8 * buflen = 12 * LENGTH inlist /\\
   ALL (nonoverlapping (word_add r (word(2 * offset)),2 * (256 - offset)))
       [(word pc,libmlkem_size); (" ^ rej_loop_buf l ^ ",buflen)]";;

let rej_loop_pre l events =
  "(\\s. aligned_bytes_loaded s (word pc)
          mlkem_native_libmlkem_clang17_O3_mc /\\
        read PC s = word(pc + " ^ l.rej_header ^ ") /\\
        read " ^ l.rej_out ^ " s = r /\\
        read " ^ l.rej_ctr ^ " s = word offset /\\
        read " ^ l.rej_base ^ " s = buf /\\
        read " ^ l.rej_idx ^ " s = word 0 /\\
        wordlist_from_memory(" ^ rej_loop_buf l ^ ",LENGTH inlist) s =
        inlist" ^
  (if events then " /\\ read events s = e)" else ")");;

let rej_loop_result l =
  "(let inlist' = MAP (word_zx:12 word->16 word) inlist in
    let outlist =
      SUB_LIST (0,256 - offset) (FILTER (\\x. val x < 3329) inlist') in
    let outlen = LENGTH outlist in
    read PC s = word(" ^ rej_loop_pc_post l ^ ") /\\
    read " ^ l.rej_ctr ^ " s = word(offset + outlen) /\\ " ^
    rej_loop_flag l "outlen" ^ "
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
       " ^ rej_loop_hyps l ^ "
       ==> ensures arm " ^ rej_loop_pre l true ^ "
            (\\s. " ^ rej_loop_result l ^ " /\\
                 (exists e2.
                    read events s = APPEND e2 e /\\
                    e2 = f_events r offset buf buflen inlist pc /\\
                    memaccess_inbounds e2 [" ^ rej_loop_buf l ^ ",buflen]
                      [word_add r (word(2 * offset)),2 * (256 - offset)]))
            " ^ rej_loop_frame l);;

let rej_loop_correct_goal l =
  parse_term
   ("forall r offset buf buflen (inlist:(12 word)list) pc.
       " ^ rej_loop_hyps l ^ "
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

(*** The assumptions about the registers, flags, PC and events of the     ***)
(*** state, the only ones that the tactics applied at each step look at  ***)
(*** and rewrite, since rewriting all the others at each step is slow    ***)

let rej_is_state_asm th =
  let c = concl th in
  is_eq c &&
  (match lhs c with
     Comb(Comb(Const("read",_),Const(_,_)),_) -> true
   | _ -> false);;

let REJ_STATE_RULE_TAC rule =
  RULE_ASSUM_TAC(fun th -> if rej_is_state_asm th then rule th else th);;

let rej_find_terms p tms =
  setify(itlist (fun t acc -> find_terms p t @ acc) tms []);;

let rej_state_terms p asl =
  rej_find_terms p (map (concl o snd) (filter (rej_is_state_asm o snd) asl));;

(*** Decide a condition by arithmetic, keeping it as an assumption ***)

let DECIDE_PROP_TAC c =
  (SUBGOAL_THEN c
    (fun th -> REJ_STATE_RULE_TAC(REWRITE_RULE[EQT_INTRO th]) THEN
               ASSUME_TAC th) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg c)
    (fun th -> REJ_STATE_RULE_TAC(REWRITE_RULE[EQF_INTRO th]) THEN
               ASSUME_TAC th) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]);;

(*** Rewrite with a lemma |- !n. n < b ==> l[n] = r[n] the instances of l ***)
(*** in the state, where the bound can be proved by arithmetic            ***)

let REJ_SMALL_TAC pat th =
  W(fun (asl,w) ->
    MAP_EVERY (fun n ->
      TRY(MP_TAC(SPEC n th) THEN ANTS_TAC THENL
           [SIMPLE_ARITH_TAC;
            DISCH_THEN(fun th -> REJ_STATE_RULE_TAC(REWRITE_RULE[th]))]))
     (map (rand o rand)
        (rej_state_terms (fun t -> can (term_match [] pat) t &&
                                   not(is_numeral(rand(rand t)))) asl)));;

let VAL_WORD64_EQ = prove
 (`!n. n < 18446744073709551616 ==> val(word n:int64) = n`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

(*** Express the carry and zero flags of the comparisons of small 32-bit ***)
(*** and 64-bit numbers in terms of the numbers, and decide them where   ***)
(*** possible, keeping the facts used (which DECIDE_FLAGS_TAC in         ***)
(*** utils/mlkem_native.ml does not, e.g. 255 <= c deciding a carry)     ***)

let rej_undecided_czflags asl =
  mapfilter (fun (_,th) ->
    let l,r = dest_eq(concl th) in
    let f = rand(rator l) in
    if mem f [`CF`;`ZF`] && not(r = `T` || r = `F`) then r
    else failwith "") asl;;

let DECIDE_CZFLAGS_TAC =
  W(fun (asl,w) ->
     MAP_EVERY (fun p -> TRY(DECIDE_PROP_TAC p)) (rej_undecided_czflags asl));;

let CMP_CZFLAGS_TAC pat th =
  W(fun (asl,w) ->
    let tms = rej_find_terms (can (term_match [] pat))
                (rej_undecided_czflags asl) in
    MAP_EVERY (fun t ->
      let x = rand(lhand t) and y = rand(rand t) in
      TRY(MP_TAC(SPECL [x;y] th) THEN
          ANTS_TAC THENL
           [CONJ_TAC THEN SIMPLE_ARITH_TAC;
            DISCH_THEN(fun th -> REJ_STATE_RULE_TAC(REWRITE_RULE[th]))]))
     tms);;

let REJ_FLAGS_TAC =
  CMP_CZFLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS THEN
  CMP_CZFLAGS_TAC `word_sub (word x) (word y):int64` WORD_CMP_64_FLAGS THEN
  DECIDE_CZFLAGS_TAC;;

(*** Decide the condition of a conditional branch ***)

let DECIDE_BRANCH_TAC =
  FIRST_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if not (is_cond r) || not(can (term_match [] `read PC s`) l)
    then failwith "DECIDE_BRANCH_TAC" else
    DECIDE_PROP_TAC (lhand(rator r)));;

(*** Once a field register holds a value that is the 12-bit field e, ***)
(*** replace it by word n, where val e = n                           ***)

let REJ_FIELD_TAC r e n =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && (try rand(rator(lhs c)) = r with Failure _ -> false) &&
       free_in e (rhs c)
    then let th' = TRANS th (BITBLAST_RULE
                     (mk_eq(rhs c,mk_comb(`word_zx:12 word->int64`,e)))) in
         let vth = ASSUME(mk_eq(mk_comb(`val:12 word->num`,e),n)) in
         ASSUME_TAC(REWRITE_RULE[vth] (REWRITE_RULE[word_zx] th'))
    else failwith "REJ_FIELD_TAC");;

let REJ_FIELDS_TAC l idx =
  let e0 = subst [idx,`i:num`] `EL (2 * i) inlist:12 word`
  and e1 = subst [idx,`i:num`] `EL (2 * i + 1) inlist:12 word` in
  let r0 = mk_const(fst l.rej_fields,[])
  and r1 = mk_const(snd l.rej_fields,[]) in
  TRY(REJ_FIELD_TAC r0 e0 `n0:num`) THEN TRY(REJ_FIELD_TAC r1 e1 `n1:num`);;

(*** The normal form of the values in the state at each step, and of all ***)
(*** the assumptions at the end of a group                               ***)

let REJ_NORM_TAC =
  REJ_STATE_RULE_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64; GSYM WORD_ADD;
                                  GSYM WORD_ADD_ASSOC; WORD_SHL_WORD_1]) THEN
  REJ_SMALL_TAC `word_zx(word n:int64):int32` WORD_ZX_64_32_SMALL THEN
  REJ_SMALL_TAC `word_zx(word n:int32):int64` WORD_ZX_32_64_SMALL THEN
  REJ_SMALL_TAC `val(word n:int64)` VAL_WORD64_EQ;;

let REJ_NORM_ALL_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64; GSYM WORD_ADD;
                              GSYM WORD_ADD_ASSOC; WORD_SHL_WORD_1]);;

(*** Before a store, the values of the two possible counters, so that the ***)
(*** address can be seen to be in the output                              ***)

let REJ_STORE_FACTS_TAC =
  MAP_EVERY (fun t ->
    MP_TAC(SPEC t VAL_WORD64_EQ) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC])
  [`offset + LENGTH(L:int16 list)`; `(offset + LENGTH(L:int16 list)) + 1`];;

let REJ_STRIP_EXISTS_ASSUM_TAC =
  FIRST_X_ASSUM(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC));;

(*** The setup for group number idx, splitting into cases on n0 and n1 ***)

let REJ_GROUP_TAC l idx =
  let ix t = subst [idx,`i:num`] t in
  let e0 = ix `EL (2 * i) inlist:12 word`
  and e1 = ix `EL (2 * i + 1) inlist:12 word` in
  let bytes_th =
    if l.rej_ofs = 0 then
      SPECL [`buf:int64`; `buflen:num`; `inlist:(12 word)list`; idx;
             `s0:armstate`] REJ_GROUP_BYTES
    else
      SPECL [`buf:int64`; mk_small_numeral l.rej_ofs; `buflen:num`;
             `inlist:(12 word)list`; idx; `s0:armstate`] REJ_GROUP_BYTES_OFS in
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_SAMPLE_APPEND; LENGTH_APPEND;
                              REJ_SAMPLE_PAIR]) THEN
  REWRITE_TAC[REJ_SAMPLE_APPEND; REJ_SAMPLE_PAIR] THEN
  ABBREV_TAC (ix `L = REJ_SAMPLE(SUB_LIST(0,2 * i) inlist)`) THEN
  ENSURES_INIT_TAC "s0" THEN REJ_STRIP_EXISTS_ASSUM_TAC THEN
  MP_TAC bytes_th THEN
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

(*** One step, recognizing the two values once they have been computed ***)

let REJ_STEP_TAC l idx n =
  (fun g -> if rej_at_store l.rej_exec g then REJ_STORE_FACTS_TAC g
            else ALL_TAC g) THEN
  ARM_STEPS_TAC l.rej_exec [n] THEN REJ_FIELDS_TAC l idx THEN
  REJ_NORM_TAC THEN REJ_FLAGS_TAC THEN TRY DECIDE_BRANCH_TAC;;

(*** Simulate from the head of the group until the PC is a target ***)

let rec REJ_RUN_TAC l idx n targets (asl,w) =
  (REJ_STEP_TAC l idx n THEN
   (fun g -> if mem (current_pc g) targets then REJ_NORM_ALL_TAC g
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

(*** If so, the number of fields ***)

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

(*** In the last group, the exit, given by whether there are 256 samples, ***)
(*** and the flag, given by whether there are fewer                       ***)

let REJ_PC_COND_TAC =
  W(fun (asl,w) ->
    let cs = setify(map (lhand o rator)
               (find_terms (fun t -> is_cond t &&
                                     mem (type_of t) [`:num`; `:int64`] &&
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
(* whether the result is then full, as at gcc -O3. The number N of groups    *)
(* before the last one is the least such that the following group would go  *)
(* beyond the buffer or the coefficients from the group after N would reach  *)
(* 256.                                                                      *)
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

let REJ_LOOP_INTRO_TAC l =
  CONCRETIZE_F_EVENTS_TAC REJ_LOOP_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `offset:num`; `buf:int64`; `buflen:num`;
    `inlist:(12 word)list`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[GSYM LE_ANTISYM] o
                check (fun th -> is_eq(concl th) &&
                                 lhs(concl th) = `buflen:num`)) THEN
  MP_TAC(ISPECL
   [parse_term("(" ^ rej_loop_buf l ^ "):int64");
    `LENGTH(inlist:(12 word)list)`;
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
      read " ^ l.rej_base ^ " s = buf /\\
      read(memory :> bytes(" ^ rej_loop_buf l ^ ",buflen)) s =
      num_of_wordlist inlist /\\
      (if i <= N then
        read " ^ l.rej_ctr ^ " s =
        word(offset + LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * i) inlist))) /\\
        read " ^ l.rej_idx ^ " s = word(3 * i) /\\
        read(memory :> bytes(word_add r (word(2 * offset)),
               2 * LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * i) inlist)))) s =
        num_of_wordlist(REJ_SAMPLE(SUB_LIST(0,2 * i) inlist))
       else
        read " ^ l.rej_ctr ^ " s =
        word(offset + LENGTH(outlist:int16 list)) /\\ " ^
        rej_loop_flag l "LENGTH(outlist:int16 list)" ^ "
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
  REJ_GROUP_TAC l `i:num` THEN
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
  REJ_GROUP_TAC l `N:num` THEN
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
  REJ_LOOP_INTRO_TAC l THEN REJ_LOOP_N_TAC THEN
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
    FIRST_X_ASSUM(fun hth -> CHOOSE_THEN (fun th ->
      MP_TAC(MP (SPECL [`e:(uarch_event)list`; `r:int64`; `offset:num`;
                        `buf:int64`; `buflen:num`; `inlist:(12 word)list`;
                        `pc:num`] th) hth)) fullth) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
    SIMP_TAC[]);;
