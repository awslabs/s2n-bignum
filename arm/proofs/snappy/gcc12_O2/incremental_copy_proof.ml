(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/incremental_copy_spec.ml";;
needs "common/snappy/snappy_memory.ml";;
needs "arm/proofs/snappy/bstep_decide.ml";;

(*** The proof is by the paths of the code (see the spec). The addresses    ***)
(*** are made relative to base, with LENGTH out = r + off: op is base +     ***)
(*** (r + off), src is base + r. The output is carried as                   ***)
(*** bytelist(base,(r + off) + c) = snappy_copy off c out for the c bytes   ***)
(*** done (common/snappy/snappy_memory.ml), extended by each chunk: a block ***)
(*** of bstep ends after each load that may read an earlier store (the     ***)
(*** 16-byte copies for off >= 16), so that the bytes loaded are those of  ***)
(*** the state at the end of the block. The 16-byte loops run at most 4    ***)
(*** times (b < n + 15 <= 79 there) and are unrolled by the range of b; the ***)
(*** byte loops are lemmas from their entry to the return.                 ***)

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_PATTERN_MASKS_LOADED = prove
 (`!s pc k. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\ k < 16
     ==> read (memory :> bytes128 (word_add (word_add (word pc) (word 31680)) (word (16 * k)))) s =
         snappy_pattern_mask k 0 /\
         read (memory :> bytes128 (word_add (word_add (word pc) (word 31936)) (word (16 * k)))) s =
         snappy_pattern_mask k 1`,
  let ths = map (fun d -> IMAGE_CONST_RULE_FOR snappy_libsnappy_gcc12_O2_mc d 128)
              (map (fun k -> 31680 + 16*k) (0--15) @ map (fun k -> 31936 + 16*k) (0--15)) in
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC (map (REWRITE_RULE[GSYM WORD_ADD]) ths) THEN
  REWRITE_TAC[snappy_pattern_mask] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let SNAPPY_TBL_EXPANDED = EXPAND_SIMD_RULE snappy_tbl;;

let SNAPPY_PATTERN_ITER_SMALL = prove
 (`!q off.
     snappy_pattern_iter q off 0 = snappy_tbl q (snappy_pattern_mask (off - 1) 0) /\
     snappy_pattern_iter q off 1 =
       snappy_tbl (snappy_pattern_iter q off 0) (snappy_pattern_mask (off - 1) 1) /\
     snappy_pattern_iter q off 2 =
       snappy_tbl (snappy_pattern_iter q off 1) (snappy_pattern_mask (off - 1) 1) /\
     snappy_pattern_iter q off 3 =
       snappy_tbl (snappy_pattern_iter q off 2) (snappy_pattern_mask (off - 1) 1)`,
  REWRITE_TAC[snappy_pattern_iter; ARITH_RULE `3 = SUC 2`; ARITH_RULE `2 = SUC 1`;
              ARITH_RULE `1 = SUC 0`]);;

(* Memory facts with base-relative addresses in one normal form.            *)

let IC_NORM_CONV =
  let rec conv tm =
    match tm with
      Comb(Comb(Const("word_add",_),Comb(Comb(Const("word_add",_),_),
           Comb(Const("word",_),_))),Comb(Const("word",_),_)) ->
        (REWR_CONV(GSYM WORD_ADD_ASSOC) THENC
         RAND_CONV(REWR_CONV(GSYM WORD_ADD)) THENC TRY_CONV conv) tm
    | Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),x))
        when not(is_numeral x) ->
        RAND_CONV(RAND_CONV(NUM_REDUCE_CONV THENC NUM_NORMALIZE_CONV)) tm
    | _ -> failwith "IC_NORM_CONV" in
  ONCE_DEPTH_CONV conv;;

let MEMFACT_TAC : tactic = fun (asl,w) ->
  let ismem th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),_)),_)),_) -> true
    | _ -> false in
  let ths = map (CONV_RULE IC_NORM_CONV) (filter ismem (map snd asl)) in
  (CONV_TAC IC_NORM_CONV THEN REWRITE_TAC ths) (asl,w);;

let IC_ARITH_TAC = BSTEP_ARITH_DECIDE_TAC ~rws:[];;

(* One 16-byte or k-byte chunk copied, at the state t of the stores.         *)

let CHUNK_TAC c k t =
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; t; t; `base:int64`;
                 `out:byte list`; mk_small_numeral c; mk_small_numeral k;
                 `off:num`] SNAPPY_COPY_CHUNK_STEP) THEN
  ASM_REWRITE_TAC[snappy_copy; ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `((r + off) + c) - off = r + c`;
              ARITH_RULE `(r + off) - off = r`] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; snappy_copy] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY IC_ARITH_TAC THEN
    (if k = 16 then MATCH_MP_TAC READ_BYTELIST_OF_BYTES64_PAIR THEN CONJ_TAC
     else if k = 8 then MATCH_MP_TAC READ_BYTELIST_OF_BYTES64
     else MATCH_MP_TAC READ_BYTELIST_OF_BYTES8) THEN
    MEMFACT_TAC;
    DISCH_TAC];;

let PATTERN_TAC j t =
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; t; `base:int64`;
                 `out:byte list`; mk_small_numeral j; `off:num`; `q:int128`]
         SNAPPY_COPY_PATTERN_STEP) THEN
  ASM_REWRITE_TAC[snappy_copy; ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; snappy_copy; ARITH_RULE `(r + off) - off = r`] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY IC_ARITH_TAC THEN
    REWRITE_TAC[SNAPPY_PATTERN_ITER_SMALL] THEN MEMFACT_TAC ;
    DISCH_TAC];;

let TRUNC_TAC c t =
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; t; `base:int64`;
                 `out:byte list`; mk_small_numeral c; `n:num`; `off:num`]
         SNAPPY_COPY_TRUNC) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [TRY CONJ_TAC THEN TRY IC_ARITH_TAC ; DISCH_THEN ACCEPT_TAC];;

(* ------------------------------------------------------------------------- *)
(* The main proof.                                                           *)
(* ------------------------------------------------------------------------- *)

let IC_SETUP_TAC =
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = v)))
    [`src:int64`; `op_limit:int64`; `buf_limit:int64`; `op:int64`] THEN
  SUBGOAL_THEN `?r. LENGTH(out:byte list) = r + off` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `LENGTH(out:byte list) - off` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if concl th = `LENGTH(out:byte list) = r + off` then
      RULE_ASSUM_TAC(fun a -> if concl a = concl th then a else REWRITE_RULE[th] a) THEN
      REWRITE_TAC[th]
    else NO_TAC) THEN
  SUBGOAL_THEN `word_sub (word_add base (word (r + off))) (word off) = word_add base (word r):int64`
   SUBST1_TAC THENL [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  SUBGOAL_THEN `word_sub (word_add base (word (r + off))) (word_add base (word r)) = word off:int64`
   ASSUME_TAC THENL [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `(r + off) + b < 2 EXP 64 /\ off < 2 EXP 64 /\ b < 2 EXP 64 /\ n < 2 EXP 64`
   STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC];;

let rw0 = `word_sub (word_add base (word (r + off))) (word_add base (word r)) = word off:int64`;;
let rw1 = `word_shl (word_sub (word off) (word 1)) 4 = word (16 * (off - 1)):int64`;;

let RW1_TAC =
  SUBGOAL_THEN rw1 ASSUME_TAC THENL
   [SUBGOAL_THEN `word_sub (word off) (word 1) = word(off - 1):int64` SUBST1_TAC THENL
     [ASM_SIMP_TAC[WORD_SUB]; ALL_TAC] THEN
    REWRITE_TAC[word_shl; VAL_WORD; DIMINDEX_64] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(off - 1) MOD 2 EXP 64 = off - 1` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN IC_ARITH_TAC; ARITH_TAC];
    ALL_TAC];;

let exec = SNAPPY_INCREMENTAL_COPY_GCC12_O2_EXEC;;

let BS blocks = W(fun (asl,w) ->
  let rws = map snd (filter (fun (_,a) -> concl a = rw0 || concl a = rw1) asl) in
  let dec = BSTEP_ARITH_DECIDE_TAC ~rws:rws in
  MAP_EVERY (fun (a,b) ->
    ARM_BSTEP_DECIDE_TAC ~rewrites:rws ~folds:[SNAPPY_TBL_EXPANDED] ~decide:dec exec (a--b))
   blocks);;

(* Run from step a until the return: the first block a..e that ends there. *)

let BS_RET a : tactic = fun g ->
  let rec go e =
    if e > a + 60 then failwith "BS_RET: no return" else
    match (try Some(BS [a,e] g) with Failure _ -> None) with
      Some((_,[asl,w],_) as r) when
        exists (fun (_,th) -> concl th = mk_eq(mk_comb(`read PC`,mk_var("s" ^ string_of_int e,`:armstate`)),`returnaddress:int64`)) asl ->
          r
    | _ -> go (e + 1) in
  go a;;

let sn k = mk_var("s" ^ string_of_int k,`:armstate`);;


(* ------------------------------------------------------------------------- *)
(* The byte loops, from their entry to the return.                           *)
(* ------------------------------------------------------------------------- *)

let TRUNC_TERM_TAC c t =
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; t; `base:int64`;
                 `out:byte list`; c; `n:num`; `off:num`]
         SNAPPY_COPY_TRUNC) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [TRY CONJ_TAC THEN TRY IC_ARITH_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN ACCEPT_TAC];;

let BYTE_CHUNK_TAC c t =
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; t; t; `base:int64`;
                 `out:byte list`; c; `1`; `off:num`] SNAPPY_COPY_CHUNK_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `((r + off) + c) - off = r + c`] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY IC_ARITH_TAC THEN
    MATCH_MP_TAC READ_BYTELIST_OF_BYTES8 THEN MEMFACT_TAC;
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[ADD_ASSOC])];;

(* A block that ends at a conditional branch leaves the PC as a COND: the    *)
(* condition decided by arithmetic.                                          *)

let PC_DECIDE_TAC : tactic = fun (asl,w) ->
  let _,th = find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),
           Comb(Comb(Comb(Const("COND",_),_),_),_)) -> true
    | _ -> false) asl in
  let c = lhand(rator(rhs(concl th))) in
  let dth =
    try TAC_PROOF((asl,c),BSTEP_ARITH_DECIDE_TAC ~rws:[]) with Failure _ ->
    TAC_PROOF((asl,mk_neg c),BSTEP_ARITH_DECIDE_TAC ~rws:[]) in
  (UNDISCH_THEN (concl th) (ASSUME_TAC o REWRITE_RULE[dth])) (asl,w);;

let BL_BS rws blocks = W(fun (asl,w) ->
  let dec = BSTEP_ARITH_DECIDE_TAC ~rws:rws in
  MAP_EVERY (fun (a,b) ->
    ARM_BSTEP_DECIDE_TAC ~rewrites:rws ~decide:dec exec (a--b))
   blocks);;

(* ------------------------------------------------------------------------- *)
(* Memory safety: the events of a path within the regions of the spec.       *)
(* ------------------------------------------------------------------------- *)

let IC_SUBSET_LEMMA = prove
 (`!(base:int64) x k y l.
        y <= x /\ x + k <= y + l
        ==> memrange(word_add base (word x),k) SUBSET
            memrange(word_add base (word y),l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_MEMRANGE] THEN
  X_GEN_TAC `a:int64` THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(x - y) + i` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `x = y + (x - y)` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;

let IC_SUBSET_LEMMA0 = prove
 (`!(base:int64) x k l.
        x + k <= l
        ==> memrange(word_add base (word x),k) SUBSET memrange(base,l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`base:int64`; `x:num`; `k:num`; `0`; `l:num`] IC_SUBSET_LEMMA) THEN
  ASM_REWRITE_TAC[LE_0; ADD_CLAUSES; WORD_ADD_0]);;

let IC_SUBSET_TAC : tactic =
  let one = (MATCH_MP_TAC IC_SUBSET_LEMMA ORELSE MATCH_MP_TAC IC_SUBSET_LEMMA0) THEN
            IC_ARITH_TAC in
  CONV_TAC IC_NORM_CONV THEN
  FIRST [one;
         MATCH_MP_TAC(SET_RULE `s SUBSET a ==> s SUBSET a UNION b`) THEN one;
         MATCH_MP_TAC(SET_RULE `s SUBSET b ==> s SUBSET a UNION b`) THEN one];;

let IC_INSET_TAC : tactic = fun (asl,w) ->
  let v,bod = dest_exists w in
  let eqt = lhand bod in
  let t = lhs eqt and e = rand(rhs eqt) in
  let tv,rw = try let _,th = find (fun (_,th) -> is_eq(concl th) &&
                                     lhs(concl th) = t) asl in
                  rhs(concl th),GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV) [th]
              with Failure _ -> t,ALL_TAC in
  (rw THEN EXISTS_TAC (events_prefix e tv) THEN CONJ_TAC THENL
    [REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
     REWRITE_TAC[MEMACCESS_INSET_CLAUSES; MEMACCESS_INSET_APPEND;
                 event_loads; event_stores; EMPTY_SUBSET] THEN
     REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE IC_SUBSET_TAC)]) (asl,w);;

let IC_FINISH_TAC = REPEAT CONJ_TAC THEN TRY IC_INSET_TAC;;

let INIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl)));;

(* Entry 0x322c (the pattern paths): x1 = op + c0, x5 = off.                 *)

let SNAPPY_INCREMENTAL_COPY_BYTE_LOOP_A = prove
 (`!e base out r off n b c0 pc returnaddress.
     LENGTH(out:byte list) = r + off /\ 1 <= off /\ c0 <= b /\ n <= b /\
     val base + (r + off) + b < 2 EXP 64 /\ (r + off) + b < 2 EXP 64 /\
     nonoverlapping (word_add base (word (r + off)),b) (word pc,32789)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + 12844) /\
           read X30 s = returnaddress /\
           read X0 s = word_add base (word ((r + off) + n)) /\
           read X1 s = word_add base (word ((r + off) + c0)) /\
           read X5 s = word off /\
           read (memory :> bytelist(base,(r + off) + c0)) s =
             snappy_copy off c0 out /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           read X0 s = word_add base (word ((r + off) + n)) /\
           read (memory :> bytelist(base,(r + off) + n)) s =
             snappy_copy off n out /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2 (memrange(word_add base (word r),off + b) UNION memrange(word pc,32789))
                 (memrange(word_add base (word (r + off)),b)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(word_add base (word (r + off)),b)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `b < 2 EXP 64 /\ n < 2 EXP 64 /\ c0 < 2 EXP 64 /\ off < 2 EXP 64`
   STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `n <= c0` THENL
   [INIT_TAC THEN BL_BS [] [1,4] THEN BSTEP_FINAL_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [TRUNC_TERM_TAC `c0:num` `s4:armstate`; IC_INSET_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word_add base (word ((r + off) + c0))) (word off) =
                word_add base (word (r + c0)):int64` ASSUME_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word_add base (word ((r + off) + n)))
                         (word_add base (word ((r + off) + c0))) =
                word (n - c0):int64` ASSUME_TAC THENL
   [SUBGOAL_THEN `n = c0 + (n - c0)` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    ALL_TAC] THEN
  (let rws = [ASSUME `word_sub (word_add base (word ((r + off) + c0))) (word off) =
                      word_add base (word (r + c0)):int64`;
              ASSUME `word_sub (word_add base (word ((r + off) + n)))
                         (word_add base (word ((r + off) + c0))) =
                      word (n - c0):int64`;
              GSYM WORD_ADD] in
  ENSURES_WHILE_UP_TAC `n - c0` `pc + 12864` `pc + 12876`
   `\i s. read X30 s = returnaddress /\
          read X0 s = word_add base (word ((r + off) + n)) /\
          read X1 s = word_add base (word ((r + off) + c0)) /\
          read X5 s = word_add base (word (r + c0)) /\
          read X4 s = word (n - c0) /\
          read X2 s = word i /\
          read (memory :> bytelist(base,(r + off) + c0 + i)) s =
            snappy_copy off (c0 + i) out /\
          ?e2. read events s = APPEND e2 e /\
               memaccess_inset e2 (memrange(word_add base (word r),off + b) UNION memrange(word pc,32789))
                (memrange(word_add base (word (r + off)),b))` THEN
  REPEAT CONJ_TAC THENL
   [IC_ARITH_TAC;
    INIT_TAC THEN BL_BS rws [1,5] THEN BSTEP_FINAL_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN IC_FINISH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    INIT_TAC THEN BL_BS rws [1,3] THEN
    BYTE_CHUNK_TAC `c0 + i:num` `s3:armstate` THEN
    BSTEP_FINAL_TAC THEN REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    IC_FINISH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    INIT_TAC THEN BL_BS rws [1,2] THEN PC_DECIDE_TAC THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN IC_FINISH_TAC;
    INIT_TAC THEN BL_BS rws [1,3] THEN BSTEP_FINAL_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c0 + n - c0 = n` (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [IC_ARITH_TAC; ASM_REWRITE_TAC[] THEN IC_FINISH_TAC]]));;

(* Entry 0x32ac (the paths for off >= 16): x1 = op + c0, x4 = src + c0, and *)
(* c0 < n.                                                                   *)

let SNAPPY_INCREMENTAL_COPY_BYTE_LOOP_B = prove
 (`!e base out r off n b c0 pc returnaddress.
     LENGTH(out:byte list) = r + off /\ 1 <= off /\ c0 < n /\ n <= b /\
     val base + (r + off) + b < 2 EXP 64 /\ (r + off) + b < 2 EXP 64 /\
     nonoverlapping (word_add base (word (r + off)),b) (word pc,32789)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + 12972) /\
           read X30 s = returnaddress /\
           read X0 s = word_add base (word ((r + off) + n)) /\
           read X1 s = word_add base (word ((r + off) + c0)) /\
           read X4 s = word_add base (word (r + c0)) /\
           read (memory :> bytelist(base,(r + off) + c0)) s =
             snappy_copy off c0 out /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           read X0 s = word_add base (word ((r + off) + n)) /\
           read (memory :> bytelist(base,(r + off) + n)) s =
             snappy_copy off n out /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2 (memrange(word_add base (word r),off + b) UNION memrange(word pc,32789))
                 (memrange(word_add base (word (r + off)),b)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(word_add base (word (r + off)),b)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `b < 2 EXP 64 /\ n < 2 EXP 64 /\ c0 < 2 EXP 64 /\ off < 2 EXP 64`
   STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word_add base (word ((r + off) + n)))
                         (word_add base (word ((r + off) + c0))) =
                word (n - c0):int64` ASSUME_TAC THENL
   [SUBGOAL_THEN `n = c0 + (n - c0)` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    ALL_TAC] THEN
  (let rws = [ASSUME `word_sub (word_add base (word ((r + off) + n)))
                         (word_add base (word ((r + off) + c0))) =
                      word (n - c0):int64`;
              GSYM WORD_ADD] in
  ENSURES_WHILE_UP_TAC `n - c0` `pc + 12984` `pc + 12996`
   `\i s. read X30 s = returnaddress /\
          read X0 s = word_add base (word ((r + off) + n)) /\
          read X1 s = word_add base (word ((r + off) + c0)) /\
          read X4 s = word_add base (word (r + c0)) /\
          read X5 s = word (n - c0) /\
          read X2 s = word i /\
          read (memory :> bytelist(base,(r + off) + c0 + i)) s =
            snappy_copy off (c0 + i) out /\
          ?e2. read events s = APPEND e2 e /\
               memaccess_inset e2 (memrange(word_add base (word r),off + b) UNION memrange(word pc,32789))
                (memrange(word_add base (word (r + off)),b))` THEN
  REPEAT CONJ_TAC THENL
   [IC_ARITH_TAC;
    INIT_TAC THEN BL_BS rws [1,3] THEN BSTEP_FINAL_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN IC_FINISH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    INIT_TAC THEN BL_BS rws [1,3] THEN
    BYTE_CHUNK_TAC `c0 + i:num` `s3:armstate` THEN
    BSTEP_FINAL_TAC THEN REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    IC_FINISH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    INIT_TAC THEN BL_BS rws [1,2] THEN PC_DECIDE_TAC THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN IC_FINISH_TAC;
    INIT_TAC THEN BL_BS rws [1,3] THEN BSTEP_FINAL_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c0 + n - c0 = n` (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [IC_ARITH_TAC; ASM_REWRITE_TAC[] THEN IC_FINISH_TAC]]));;


let cur_step (w:term) =
  let s = fst(dest_var(rand w)) in
  int_of_string(String.sub s 1 (String.length s - 1));;

(* k more steps from the current state.                                      *)

let BSN k = W(fun (_,w) -> let c = cur_step w in BS [c + 1,c + k]);;
let BSN_RET = W(fun (_,w) -> BS_RET (cur_step w + 1));;

(* The fact read reg s = v rewritten to read reg s = target, v = target     *)
(* proved by the rewrites rws and the normal form of addresses.             *)

let REG_FORM_TAC rws reg target : tactic = fun (asl,w) ->
  let _,th = find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) -> c = reg
    | _ -> false) asl in
  let v = rhs(concl th) in
  if v = target then ALL_TAC (asl,w) else
  let eq = TAC_PROOF((asl,mk_eq(v,target)),
     REWRITE_TAC rws THEN CONV_TAC(BINOP_CONV IC_NORM_CONV) THEN
     (REFL_TAC ORELSE (AP_TERM_TAC THEN AP_TERM_TAC THEN IC_ARITH_TAC))) in
  (UNDISCH_THEN (concl th) (fun th -> ASSUME_TAC(TRANS th eq))) (asl,w);;

(* Through a byte-loop lemma with c0 bytes done.                             *)

let CALL_LOOP_TAC lemma c0 regs : tactic = fun (asl,w) ->
  let sc = rand w in
  let ev = rhs(concl(snd(find (fun (_,th) -> is_eq(concl th) &&
             lhs(concl th) = mk_comb(`read events`,sc)) asl))) in
  let th0 = SPECL [ev; `base:int64`; `out:byte list`; `r:num`; `off:num`; `n:num`;
                   `b:num`; c0; `pc:num`; `returnaddress:int64`] lemma in
  let ants = lhand(concl th0) in
  let ath = TAC_PROOF((asl,ants),
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN IC_ARITH_TAC) in
  let th1 = CONV_RULE NUM_REDUCE_CONV (MP th0 ath) in
  let th1 = REWRITE_RULE[ADD_CLAUSES; snappy_copy] th1 in
  let pre = snd(dest_abs(rand(rator(rator(concl th1))))) in
  let targets = mapfilter (fun t -> match t with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),v)
        when mem c regs -> (c,v)
    | _ -> failwith "") (conjuncts pre) in
  (MAP_EVERY (fun (c,v) -> REG_FORM_TAC [] c v) targets THEN
   ARM_BSTEP_CALL_TAC exec th1 "s999" THEN
   BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN IC_FINISH_TAC) (asl,w);;

let PATTERN_PRELUDE_TAC =
  RW1_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`s0:armstate`; `pc:num`; `off - 1`] SNAPPY_PATTERN_MASKS_LOADED) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [IC_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `q = read (memory :> bytes128 (word_add base (word r))) s0` THEN
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `s0:armstate`; `base:int64`;
                 `out:byte list`; `off:num`; `q:int128`] SNAPPY_PATTERN_SOURCE) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(r + off) - off = r`] THEN
  ANTS_TAC THENL [IC_ARITH_TAC; DISCH_TAC];;

(* off <= 15, buf_limit - 15 < op_limit: b <= 15 (no 16-byte stores) or J   *)
(* stores of the pattern for 16 J <= b <= 16 J + 15, then the byte loop.     *)


let IC_SUB_LEMMA = prove
 (`!base:int64 l b k.
     k <= b
     ==> word_sub (word_sub (word_add base (word (l + b))) (word k))
                  (word_add base (word l)) = word (b - k)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `d = b - k` THEN
  SUBGOAL_THEN `b = d + k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;

let WORD_AND_NOT15 = prove
 (`!x. x < 2 EXP 64
       ==> word_and (word x) (word 18446744073709551600):int64 =
           word(16 * x DIV 16)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word 18446744073709551600:int64 = word_not(word(2 EXP 4 - 1))`
  SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

(* The pointer after J 16-byte blocks: op + (((buf_limit - k) - op) & ~15)  *)
(* + 16 = op + 16 J for 16 J + k - 16 <= b < 16 J + k (k = 16 or 17).       *)

let LOOP_END_RWS jj k : tactic = fun (asl,w) ->
  let jm = mk_small_numeral (jj - 1) and kt = mk_small_numeral k in
  let sub_th = TAC_PROOF((asl,
      vsubst [kt,`k:num`] `word_sub (word_sub (word_add base (word ((r + off) + b))) (word k))
                (word_add base (word (r + off))):int64 = word (b - k)`),
    MATCH_MP_TAC IC_SUB_LEMMA THEN IC_ARITH_TAC) in
  let div_th = TAC_PROOF((asl,
      vsubst [kt,`k:num`; jm,`j:num`] `(b - k) DIV 16 = j`),
    MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC (vsubst [kt,`k:num`; jm,`j:num`] `(b - k) - 16 * j`) THEN
    IC_ARITH_TAC) in
  let and_th = TAC_PROOF((asl,
      vsubst [kt,`k:num`] `b - k < 2 EXP 64`), IC_ARITH_TAC) in
  let and_th = REWRITE_RULE[div_th] (MP (SPEC (vsubst [kt,`k:num`] `b - k`) WORD_AND_NOT15) and_th) in
  let rws = [sub_th; and_th; GSYM WORD_ADD] in
  (REG_FORM_TAC rws `X1` (mk_comb(`word_add (base:int64)`, mk_comb(`word:num->int64`,
     mk_binop `(+):num->num->num` `r + off` (mk_small_numeral (16 * jj))))) THEN
   TRY(REG_FORM_TAC rws `X4` (mk_comb(`word_add (base:int64)`, mk_comb(`word:num->int64`,
     mk_binop `(+):num->num->num` `r:num` (mk_small_numeral (16 * jj))))))) (asl,w);;

(* off <= 15, buf_limit - 15 < op_limit: b <= 15 (no 16-byte stores) or J   *)
(* stores of the pattern for 16 J <= b <= 16 J + 15, then the byte loop.     *)

let P23_TAC jj =
  PATTERN_PRELUDE_TAC THEN
  (if jj = 0 then BS [1,10] else BS [1,20 + 4 * jj + 5] THEN LOOP_END_RWS jj 16) THEN
  W(fun (_,w) -> let t = rand w in
    MAP_EVERY (fun i -> PATTERN_TAC i t) (0--(jj-1))) THEN
  TRY PC_DECIDE_TAC THEN
  CALL_LOOP_TAC SNAPPY_INCREMENTAL_COPY_BYTE_LOOP_A (mk_small_numeral(16 * jj))
    [`X1`; `X5`];;

(* off >= 16, buf_limit - 15 < op_limit: J 16-byte chunks for 16 J + 1 <=   *)
(* b <= 16 J + 16 (J = 0 for b <= 16), then the 8-byte chunk and the byte    *)
(* loop from 0x3298 with x1 = op + c, x4 = src + c.                          *)

let TAIL56_TAC c =
  let ct = mk_small_numeral c and c8 = mk_small_numeral (c + 8) in
  let ret_tac cc = BSN_RET THEN W(fun (_,w) -> let t = rand w in
      BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [TRUNC_TAC cc t; IC_INSET_TAC]) in
  let rest =
    ASM_CASES_TAC (mk_binop `(<=):num->num->bool` (mk_binop `(+):num->num->num` ct `8`) `b:num`) THENL
     [BSN 5 THEN BSN 4 THEN W(fun (_,w) -> CHUNK_TAC c 8 (rand w)) THEN
      ASM_CASES_TAC (mk_binop `(<=):num->num->bool` `n:num` c8) THENL
       [ret_tac (c + 8);
        BSN 2 THEN TRY PC_DECIDE_TAC THEN
        CALL_LOOP_TAC SNAPPY_INCREMENTAL_COPY_BYTE_LOOP_B c8 [`X1`; `X4`]];
      BSN 5 THEN TRY PC_DECIDE_TAC THEN
      CALL_LOOP_TAC SNAPPY_INCREMENTAL_COPY_BYTE_LOOP_B ct [`X1`; `X4`]] in
  if c = 0 then rest else if c >= 64 then ret_tac c else
  ASM_CASES_TAC (mk_binop `(<=):num->num->bool` `n:num` ct) THENL [ret_tac c; rest];;

let P56_TAC jj =
  ENSURES_INIT_TAC "s0" THEN
  (if jj = 0 then BS [1,11] else
   BS [1,14] THEN
   MAP_EVERY (fun i -> BS [15 + 4 * i,18 + 4 * i] THEN
                       W(fun (_,w) -> CHUNK_TAC (16 * i) 16 (rand w))) (0--(jj-1)) THEN
   BS [15 + 4 * jj,20 + 4 * jj] THEN LOOP_END_RWS jj 17) THEN
  TAIL56_TAC (16 * jj);;


(* The pattern path with op_limit <= buf_limit - 15: J stores.               *)

let P1_TAC (j,steps) =
  RW1_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`s0:armstate`; `pc:num`; `off - 1`] SNAPPY_PATTERN_MASKS_LOADED) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [IC_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `q = read (memory :> bytes128 (word_add base (word r))) s0` THEN
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `s0:armstate`; `base:int64`;
                 `out:byte list`; `off:num`; `q:int128`] SNAPPY_PATTERN_SOURCE) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(r + off) - off = r`] THEN
  ANTS_TAC THENL [IC_ARITH_TAC; DISCH_TAC] THEN
  BS_RET 1 THEN W(fun (_,w) -> let t = rand w in
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY (fun i -> PATTERN_TAC i t) (0--(j-1)) THEN
    TRUNC_TAC (16 * j) t;
    IC_INSET_TAC]);;

(* The 16-byte chunks for off >= 16, op_limit <= buf_limit - 15.            *)

let P4_TAC blocks =
  ENSURES_INIT_TAC "s0" THEN
  BS [hd blocks] THEN
  MAP_EVERY (fun (i,(a,b)) ->
     (if i = length blocks - 2 then BS_RET a else BS [a,b]) THEN
     W(fun (_,w) -> CHUNK_TAC (16 * i) 16 (rand w)))
    (zip (0--(length blocks - 2)) (tl blocks)) THEN
  W(fun (_,w) -> let t = rand w in
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [TRUNC_TAC (16 * (length blocks - 1)) t; IC_INSET_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety.                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  IC_SETUP_TAC THEN
  ASM_CASES_TAC `off <= 15` THENL
   [ASM_CASES_TAC `n + 15 <= b` THENL
     [ASM_CASES_TAC `n <= 16` THENL [P1_TAC (1,28);
      ASM_CASES_TAC `n <= 32` THENL [P1_TAC (2,30);
      ASM_CASES_TAC `n <= 48` THENL [P1_TAC (3,32); P1_TAC (4,34)]]];
      ASM_CASES_TAC `b <= 15` THENL [P23_TAC 0;
      ASM_CASES_TAC `b <= 31` THENL [P23_TAC 1;
      ASM_CASES_TAC `b <= 47` THENL [P23_TAC 2;
      ASM_CASES_TAC `b <= 63` THENL [P23_TAC 3; P23_TAC 4]]]]];
    ASM_CASES_TAC `n + 15 <= b` THENL
     [ASM_CASES_TAC `n <= 16` THENL [P4_TAC [1,9; 10,20];
      ASM_CASES_TAC `n <= 32` THENL [P4_TAC [1,9; 10,13; 14,22];
      ASM_CASES_TAC `n <= 48` THENL [P4_TAC [1,9; 10,13; 14,18; 19,24];
                                     P4_TAC [1,9; 10,13; 14,18; 19,23; 24,26]]]];
      ASM_CASES_TAC `b <= 16` THENL [P56_TAC 0;
      ASM_CASES_TAC `b <= 32` THENL [P56_TAC 1;
      ASM_CASES_TAC `b <= 48` THENL [P56_TAC 2;
      ASM_CASES_TAC `b <= 64` THENL [P56_TAC 3; P56_TAC 4]]]]]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
