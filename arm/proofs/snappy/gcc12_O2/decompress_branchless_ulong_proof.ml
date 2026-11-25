(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* DecompressBranchless<size_t> (0x67a0), the fast loop of the validator:    *)
(* correctness and memory safety (decompress_branchless_ulong_spec.ml).      *)
(*                                                                           *)
(* Cut points 0x6890 (first tag of an iteration, w26 = 2) and 0x6940 (second *)
(* tag, w26 = 1), and the exit state at 0x6988 (x22 = the pointer past the  *)
(* tag to stop at). At a cut point for the tag at position h of the input:  *)
(* X19 = ip + h + 1, X27 = the tag byte, X28 = op = P - dl - 1, X8 = the     *)
(* deferred length dl (also at sp' + 152), P the output so far with the      *)
(* deferred copy, P + 22 (L - h) <= 2^63 - 128, and the model state          *)
(* snappy_fast_reach (2 EXP 63) inp out h P (common/snappy/snappy_validator.ml). *)
(* Measure 2 (L - h) + 2 at the first, 2 (L - h) + 1 at the second cut      *)
(* point, 0 at the exit (ENSURES_CUT_ENTRY, ENSURES_MEASURE_INDUCT).         *)
(*                                                                           *)
(* A segment from a cut point is split into five tag classes (literal of at  *)
(* most 60 bytes, longer literal, copy with 1-byte offset, with 2-byte      *)
(* offset, with 4-byte offset); per class the values that the code computes *)
(* from the tag (kLengthMinusOffset entry, ExtractOffset mask, length) are  *)
(* given to bstep as rewrites, the branches on data are split with the case *)
(* as an integer fact (DAT_PC_TAC), and the leaves are the exit or the next *)
(* cut point with witnesses (DBV_LEAF_TAC). The tools for the segments are   *)
(* those of the proof of DecompressAllTags<SnappyDecompressionValidator>     *)
(* (validator_segment_tools.ml).                                             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/decompress_branchless_ulong_spec.ml";;
needs "arm/proofs/snappy/validator_segment_tools.ml";;
needs "common/snappy/snappy_memory.ml";;
needs "common/ensures_measure.ml";;
needs "arm/proofs/snappy/gcc12_O2/length_minus_offset_lib.ml";;

let DBV_REACH_TAC : tactic =
  FIRST_ASSUM ACCEPT_TAC ORELSE
  (FIRST (map (fun th -> MATCH_MP_TAC th)
     [SNAPPY_FAST_REACH_LITERAL; SNAPPY_FAST_REACH_COPY1;
      SNAPPY_FAST_REACH_COPY2]) THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN DAT_ARITH_FACTS_TAC);;

let DBV_ONE_TAC : tactic = fun (asl,w as g) ->
  if is_exists w then DAT_INSET_TAC g else
  match w with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),_)),_) ->
      (FIRST_ASSUM ACCEPT_TAC ORELSE DAT_READ_EQ_TAC) g
  | _ ->
    (match strip_comb w with
       Const("snappy_fast_reach",_),_ -> DBV_REACH_TAC g
     | Const("aligned_bytes_loaded",_),_ -> FIRST_ASSUM ACCEPT_TAC g
     | _ -> (FIRST_ASSUM ACCEPT_TAC ORELSE DAT_ARITH_FACTS_TAC) g);;

let dbv_pc_is k (asl,w) =
  exists (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),pc),_)),v) ->
        pc = `PC` && v = mk_comb(`word:num->int64`,
                                 mk_binary "+" (`pc:num`,mk_small_numeral k))
    | _ -> false) asl;;

let DBV_LEAF_TAC (cands:(term*term*term) list) : tactic =
  BSTEP_FINAL_TAC THEN
  (fun g ->
    let side = if dbv_pc_is 27016 g then DISJ1_TAC else DISJ2_TAC in
    (side THEN
     FIRST (map (fun (h',p',d') ->
       MAP_EVERY EXISTS_TAC [h';p';d'] THEN REPEAT CONJ_TAC THEN DBV_ONE_TAC)
       cands)) g);;

(* The states of the proof of DecompressBranchless<size_t> (cut points and   *)
(* the exit), as terms in the variables of the spec.                         *)

let dbv_sp k = "(word_add (word_sub sp (word 224)) (word " ^ string_of_int k ^ "))";;
let dbv_slot k v =
  "read (memory :> bytes64 " ^
  (if k = 0 then "(word_sub sp (word 224))" else dbv_sp k) ^ ") s = " ^ v;;

let dbv_rd = "(memrange(ip,LENGTH inp) UNION memrange(word_sub sp (word 224),224) UNION memrange(word pc," ^ string_of_int(layout "libsnappy_size") ^ "))";;
let dbv_wr = "(memrange(word_sub sp (word 224),224))";;

let dbv_frame_str =
  String.concat " /\\ "
   (["aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc";
     "read SP s = word_sub sp (word 224)";
     "read X29 s = word_sub sp (word 224)";
     "read X20 s = word 1"; "read X21 s = word 9223372036854775680";
     "read X23 s = " ^ dbv_sp 144; "read X24 s = " ^ dbv_sp 152] @
    map (fun (k,v) -> dbv_slot k v)
     [0,"x29"; 8,"returnaddress"; 16,"x19"; 24,"x20"; 32,"x21"; 40,"x22";
      48,"x23"; 56,"x24"; 64,"x25"; 72,"x26"; 80,"x27"; 88,"x28";
      96,"word_add (word pc) (word 32256)"; 104,dbv_sp 160;
      112,"word_sub (word_add ip (word(LENGTH inp))) (word 129)"] @
    ["read (memory :> bytelist(ip,LENGTH inp)) s = inp";
     "(?e2. read events s = APPEND e2 e /\\ memaccess_inset e2 " ^ dbv_rd ^ " " ^ dbv_wr ^ ")"]);;

let dbv_val_str =
  "read X28 s = word_sub (word P) (word(dl + 1)) /\\ read X8 s = word dl /\\ " ^
  dbv_slot 152 "word dl" ^ " /\\ dl <= 64 /\\ snappy_fast_reach (2 EXP 63) inp out h P";;

(* A cut point at pc + pcoff for the tag at position h, with h + hb <= L.    *)

let dbv_cut_str pcoff hb =
  "read PC s = word (pc + " ^ string_of_int pcoff ^ ") /\\ " ^
  "read X19 s = word_add ip (word(h + 1)) /\\ read X27 s = word_zx (EL h inp) /\\ " ^
  dbv_val_str ^ " /\\ h + " ^ string_of_int hb ^ " <= LENGTH inp /\\ 131 <= LENGTH inp /\\ " ^
  "P + 22 * (LENGTH inp - h) <= 2 EXP 63 - 128 /\\ " ^ dbv_frame_str;;

let dbv_exit_str =
  "read PC s = word (pc + 27016) /\\ read X22 s = word_add ip (word(h + 1)) /\\ " ^
  dbv_val_str ^ " /\\ h <= LENGTH inp /\\ P <= 2 EXP 63 - 128 /\\ " ^ dbv_frame_str;;

(* The events clause exactly as in the spec (its regions as typed there).   *)

let dbv_is_mai t = match strip_comb t with
    Const("memaccess_inset",_),[_;_;_] -> true | _ -> false;;

let dbv_spec_mai =
  find_term dbv_is_mai
   (snd(strip_forall SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT));;

let dbv_parse s =
  let tm = parse_term s in
  try let mine = find_term dbv_is_mai tm in subst [dbv_spec_mai,mine] tm
  with Failure _ -> tm;;
let dbv_lam s = dbv_parse ("\\s:armstate. " ^ s);;

let dbv_cut1 = dbv_cut_str 0x6890 131 and dbv_cut2 = dbv_cut_str 0x6940 70;;

(* The postconditions of the segments: the exit or the next cut point.      *)

let dbv_seg_post next_str =
  let ex = dbv_parse dbv_exit_str and nx = dbv_parse next_str in
  let h' = `h':num` and p' = `P':num` and d' = `dl':num` in
  let sb t = subst [h',`h:num`; p',`P:num`; d',`dl:num`] t in
  let e1 = list_mk_exists([h';p';d'], sb ex) in
  let e2 = list_mk_exists([h';p';d'], mk_conj(`h < h':num`, sb nx)) in
  mk_abs(`s:armstate`, mk_disj(e1,e2));;

let dbv_frame_c =
 `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
  MAYCHANGE [SP; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
  MAYCHANGE [memory :> bytes(word_sub sp (word 224),224)]`;;

let dbv_global =
 `aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
  aligned 16 (sp:int64) /\ val (ip:int64) + LENGTH(inp:byte list) < 2 EXP 64 /\
  nonoverlapping (word_sub sp (word 224),224) (word pc,libsnappy_size) /\
  nonoverlapping (ip,LENGTH inp) (word_sub sp (word 224),224)`;;

let dbv_vars = `pc:num`,`ip:int64`,`inp:byte list`;;

let dbv_seg_stmt pre_str next_str =
  let tm = mk_imp(dbv_global,
    list_mk_icomb "ensures" [`arm`; dbv_lam pre_str; dbv_seg_post next_str; dbv_frame_c]) in
  list_mk_forall(frees tm, tm);;

(* The segments of DecompressBranchless<size_t> between the cut points.      *)

let dbv_exec = SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_EXEC;;

let dbv_x = `val(EL h (inp:byte list)) DIV 4`;;
let dbv_sx t = subst [dbv_x,`x:num`] t;;

(* class: name, type, x-bound fact, lmo, length lemma, (next tag, length)   *)

let dbv_classes =
  ["LIT", 0, dbv_sx `x < 60`, dbv_sx `&(x + 1) - &256:int`, DAT_LEN_LIT,
     Some(dbv_sx `h + x + 2`, dbv_sx `x + 1`);
   "LITLONG", 0, dbv_sx `~(x < 60)`, `&255:int`, DAT_LEN_255, None;
   "C1", 1, dbv_sx `x < 64`, dbv_sx `&(x MOD 8 + 4) - &256 * &(x DIV 8):int`,
     DAT_LEN_C1, Some(`h + 2`, dbv_sx `x MOD 8 + 4`);
   "C2", 2, dbv_sx `x < 64`, dbv_sx `&(x + 1):int`, DAT_LEN_C2,
     Some(`h + 3`, dbv_sx `x + 1`);
   "C4", 3, dbv_sx `x < 64`, `&255:int`, DAT_LEN_255, None];;

let DBV_CLASS_SPLIT = prove
 (`!c:byte.
     (val c MOD 4 = 0 /\ val c DIV 4 < 60) \/
     (val c MOD 4 = 0 /\ ~(val c DIV 4 < 60) /\ val c DIV 4 < 64) \/
     (val c MOD 4 = 1 /\ val c DIV 4 < 64) \/
     (val c MOD 4 = 2 /\ val c DIV 4 < 64) \/
     (val c MOD 4 = 3 /\ val c DIV 4 < 64)`,
  GEN_TAC THEN MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let dbv_verbose = ref false;;
let dbv_leaf_tac = ref DBV_LEAF_TAC;;
let dbv_only = ref ([]:string list);;

let dbv_stage name f = try f () with Failure m ->
  (Printf.printf "STAGE FAILED %s: %s\n%!" name m; failwith m);;

let DBV_CLASS_TAC (name,t,xb,lmo,lenth,nxt) (stops:term list) : tactic =
  fun (asl,w as g) -> dbv_stage name (fun () ->
  let x = dbv_x in
  let fact tm = snd(find (fun (_,th) -> concl th = tm) asl) in
  let facts = dat_facts asl in
  let arith tm = TAC_PROOF(([],tm),
    MAP_EVERY MP_TAC facts THEN ARITH_TAC) in
  let iarith0 tm = TAC_PROOF(([],tm), INT_FACTS_ARITH_TAC facts) in
  let tf = fact (mk_eq(`val(EL h (inp:byte list)) MOD 4`,mk_small_numeral t)) in
  let xbth = fact xb in
  let x64 = try fact (dbv_sx `x < 64`) with Failure _ -> arith (dbv_sx `x < 64`) in
  let dm = arith (dbv_sx `x DIV 8 < 8 /\ x MOD 8 < 8`) in
  let iarith tm = TAC_PROOF(([],tm), INT_FACTS_ARITH_TAC (dm :: x64 :: facts)) in
  let and3 = REWRITE_RULE[tf] (SPEC `EL h (inp:byte list)` DAT_ZX_AND3) in
  let lth = if is_imp(snd(strip_forall(concl lenth)))
            then CONJUNCTS(MP (SPEC x lenth) (if name = "LIT" then xbth else x64))
            else CONJUNCTS lenth in
  let lrw = filter (fun th -> is_eq(concl th)) lth @
            map EQF_INTRO (filter (fun th -> is_neg(concl th)) lth) @
            map EQT_INTRO (filter (fun th -> not(is_eq(concl th)) &&
                                              not(is_neg(concl th))) lth) in
  let sxth = let th = ISPEC lmo DAT_SX_IWORD in MP th (iarith (lhand(concl th))) in
  let ivth = let th = ISPEC lmo DAT_IVAL_IWORD64 in MP th (iarith (lhand(concl th))) in
  let lmoeq = TAC_PROOF(([],mk_eq(`snappy_lmo (EL h (inp:byte list))`,lmo)),
     REWRITE_TAC[snappy_lmo; tf] THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[if name = "LITLONG" then EQF_INTRO xbth else
                 if name = "LIT" then EQT_INTRO xbth else TRUTH]) in
  let nexts =
    if t = 0 then
      [`word_add (word_add (word_add (ip:int64) (word(h + 1))) (word(val(EL h (inp:byte list)) DIV 4))) (word 1)`,
       `((h + 1) + val(EL h (inp:byte list)) DIV 4) + 1`]
    else
      [subst [mk_small_numeral t,`t:num`] `word_add (word_add (ip:int64) (word(h + 1))) (word t)`,
       subst [mk_small_numeral t,`t:num`] `(h + 1) + t`] in
  let next_tac (a,k) =
    let tm = subst [a,`a:int64`; k,`k:num`]
      `read (memory :> bytes8 a) s0 = EL k (inp:byte list)` in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [CONV_TAC(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      MATCH_MP_TAC READ_MEMORY_BYTELIST_EL THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY MP_TAC facts THEN ARITH_TAC;
      ALL_TAC] in
  let x2th = prove(subst [x,`x:num`] `word_add (word x) (word 2):int64 = word(x + 2)`,
                   REWRITE_TAC[WORD_ADD]) in
  let rewrites =
    [and3; DAT_ZX_USHR2; WORD_AND_0; DAT_EXT; DAT_ZX_CHAINS; sxth; x2th] @
    DAT_MASKS @ DAT_EXT_UNRED @ lrw in
  let cands =
    [`h:num`,`P:num`,`dl:num`; `h:num`,`P:num`,`0`] @
    (match nxt with
       None -> []
     | Some(hn,len) -> [hn, mk_binary "+" (`P:num`,len), len;
                        hn, mk_binary "+" (`P:num`,len), `0`]) in
  (FIRST_X_ASSUM(fun th -> if can (find_term ((=) `snappy_lmo`)) (concl th)
                           then ASSUME_TAC(REWRITE_RULE[lmoeq] th) else NO_TAC) THEN
   MAP_EVERY ASSUME_TAC (ivth :: CONJUNCTS dm) THEN
   MAP_EVERY next_tac nexts THEN
   (fun g -> dbv_stage (name^" run") (fun () -> DAT_STEPS_TAC ~verbose:!dbv_verbose [] rewrites dbv_exec 1 stops g)) THEN
   (fun g -> dbv_stage (name^" leaf") (fun () -> !dbv_leaf_tac cands g))) g);;

let DBV_SEG_TAC (stops:term list) : tactic =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  MP_TAC(SPECL [`s0:armstate`; `pc:num`; `EL h (inp:byte list)`]
               SNAPPY_LMO_TABLE_ZX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ip:int64`; `inp:byte list`; `h + 1`; `s0:armstate`]
                DAT_READ_BYTES16) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(h + 1) + 1 = h + 2`] THEN DISCH_TAC THEN
  MAP_EVERY (fun i -> ASSUME_TAC(REWRITE_RULE[DIMINDEX_8]
     (ISPEC (subst [i,`i:num`] `EL (h + i) (inp:byte list)`) VAL_BOUND)))
     [`0`; `1`; `2`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  ASSUME_TAC(ISPECL [`EL (h + 1) (inp:byte list)`; `EL (h + 2) (inp:byte list)`]
                    DAT_VAL_JOIN) THEN
  ASSUME_TAC(ISPEC `EL h (inp:byte list)` DAT_VAL_ZX_BYTE) THEN
  SUBGOAL_THEN `P + 1540 <= 2 EXP 63 - 128` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `EL h (inp:byte list)` DBV_CLASS_SPLIT) THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) ORELSE DISCH_THEN STRIP_ASSUME_TAC)
  THENL (map (fun (n,_,_,_,_,_ as cl) ->
    if !dbv_only = [] || mem n !dbv_only then DBV_CLASS_TAC cl stops else ALL_TAC) dbv_classes);;

(* The exit (0x6988 to the return) and the entry (to the return or the first *)
(* cut point) of DecompressBranchless<size_t>.                               *)

let dbv_post_str =
  "read PC s = returnaddress /\\ read SP s = sp /\\ " ^
  "read X19 s = x19 /\\ read X20 s = x20 /\\ read X21 s = x21 /\\ " ^
  "read X22 s = x22 /\\ read X23 s = x23 /\\ read X24 s = x24 /\\ " ^
  "read X25 s = x25 /\\ read X26 s = x26 /\\ read X27 s = x27 /\\ " ^
  "read X28 s = x28 /\\ read X29 s = x29 /\\ " ^
  "(?k inp' out'. snappy_steps k (2 EXP 63) (inp,out) = SOME(inp',out') /\\ " ^
  "read X0 s = word_add ip (word(LENGTH inp - LENGTH inp')) /\\ " ^
  "read X1 s = word_sub (word(LENGTH out')) (word 1)) /\\ " ^
  "(?e2. read events s = APPEND e2 e /\\ memaccess_inset e2 " ^ dbv_rd ^ " " ^ dbv_wr ^ ")";;

let dbv_pre_str =
  "aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\\ " ^
  "read PC s = word (pc + " ^ string_of_int(layout "DecompressBranchless_ulong") ^ ") /\\ " ^
  "read SP s = sp /\\ read X30 s = returnaddress /\\ " ^
  "read X19 s = x19 /\\ read X20 s = x20 /\\ read X21 s = x21 /\\ " ^
  "read X22 s = x22 /\\ read X23 s = x23 /\\ read X24 s = x24 /\\ " ^
  "read X25 s = x25 /\\ read X26 s = x26 /\\ read X27 s = x27 /\\ " ^
  "read X28 s = x28 /\\ read X29 s = x29 /\\ " ^
  "C_ARGUMENTS [ip; word_add ip (word(LENGTH inp)); " ^
  "word_sub (word(LENGTH (out:byte list))) (word 1); word 1; word 9223372036854775744] s /\\ " ^
  "read (memory :> bytelist(ip,LENGTH inp)) s = inp /\\ read events s = e";;

let dbv_spec_parts =
  let body = snd(strip_forall SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT) in
  let _,ens = dest_imp body in
  match snd(strip_comb ens) with
    [_;pre;post;c] -> pre,post,c
  | _ -> failwith "dbv_spec_parts";;

let dbv_exit_stmt =
  let _,post,_ = dbv_spec_parts in
  let tm = mk_imp(dbv_global,
    list_mk_icomb "ensures" [`arm`; dbv_lam dbv_exit_str; post;
                             dbv_frame_c]) in
  list_mk_forall(frees tm, tm);;

let dbv_entry_stmt =
  let cut0 = subst [`0`,`h:num`; `LENGTH(out:byte list)`,`P:num`; `0`,`dl:num`]
               (dbv_parse dbv_cut1) in
  let pre,post,_ = dbv_spec_parts in
  let post = mk_abs(`s:armstate`,mk_disj(rhs(concl(BETA_CONV(mk_comb(post,`s:armstate`)))),cut0)) in
  let hyp = mk_conj(dbv_global,
    `LENGTH(out:byte list) + 22 * LENGTH(inp:byte list) <= 2 EXP 63 - 128`) in
  let tm = mk_imp(hyp,
    list_mk_icomb "ensures" [`arm`; pre; post; dbv_frame_c]) in
  list_mk_forall(frees tm, tm);;

(* After the run: the conjuncts of the postcondition.                        *)

let dbv_report (tac:tactic) : tactic = fun (asl,w as g) ->
  try tac g with Failure m ->
    (Printf.printf "POST CONJ FAILED (%s): %s\n%!" m (dat_short w); failwith m);;

let DBV_POST_CONJS_TAC (wits:term list) : tactic =
  REPEAT CONJ_TAC THEN
  dbv_report (fun (asl,w as g) ->
    if is_exists w && can (find_term ((=) `events`)) w then DAT_INSET_TAC g
    else if is_exists w then
      (MAP_EVERY EXISTS_TAC wits THEN
       REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
       TRY(REWRITE_TAC[snappy_steps] THEN NO_TAC) THEN
       TRY(FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
           lhs(concl th) = `LENGTH(inp:byte list) - LENGTH(inp':byte list)`
           then REWRITE_TAC[th] else NO_TAC)) THEN
       TRY(FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
           lhs(concl th) = `LENGTH(out':byte list)`
           then REWRITE_TAC[th] else NO_TAC)) THEN
       REWRITE_TAC[SUB_REFL] THEN
       dbv_report DBV_ONE_TAC) g
    else DBV_ONE_TAC g);;

let DBV_POST_TAC (wits:term list) : tactic =
  BSTEP_FINAL_TAC THEN DBV_POST_CONJS_TAC wits;;

let DBV_EXIT_TAC : tactic =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  MP_TAC(ISPECL [`2 EXP 63`; `inp:byte list`; `out:byte list`; `h:num`; `P:num`]
                SNAPPY_FAST_REACH_RESULT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `inp':byte list`
    (X_CHOOSE_THEN `out':byte list` STRIP_ASSUME_TAC))) THEN
  DAT_STEPS_TAC [] [] dbv_exec 1 [] THEN
  DBV_POST_TAC [`k:num`; `inp':byte list`; `out':byte list`];;

let DBV_ENTRY_TAC : tactic =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ASM_CASES_TAC `130 < LENGTH(inp:byte list)` THEN
  TRY(SUBGOAL_THEN `read (memory :> bytes8 ip) s0 = EL 0 (inp:byte list)`
   ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MESON[WORD_ADD_0] `ip:int64 = word_add ip (word 0)`] THEN
    MATCH_MP_TAC READ_MEMORY_BYTELIST_EL THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC; ALL_TAC]) THEN
  ASSUME_TAC(ISPECL [`2 EXP 63`; `inp:byte list`; `out:byte list`]
                    SNAPPY_FAST_REACH_0) THEN
  ASSUME_TAC(WORD_RULE
   `word_sub (word_add ip (word(LENGTH(inp:byte list)))) ip:int64 =
    word(LENGTH inp)`) THEN
  (fun (asl,w as g) ->
     let rw = snd(hd asl) in
     (DAT_STEPS_TAC [] [rw] dbv_exec 1 [`word(pc + 0x6890):int64`] THEN
      (fun g -> if dbv_pc_is 0x6890 g then
                  (BSTEP_FINAL_TAC THEN DISJ2_TAC THEN REPEAT CONJ_TAC THEN
                   DBV_ONE_TAC) g
                else (BSTEP_FINAL_TAC THEN DISJ1_TAC THEN
                      DBV_POST_CONJS_TAC [`0`; `inp:byte list`; `out:byte list`]) g)) g);;

(* The whole function: entry, the cut points with the measure, the exit.     *)

(* R n: the exit (n = 0) or a cut point with its measure.                    *)

let dbv_R =
  let ex = dbv_parse dbv_exit_str and c1 = dbv_parse dbv_cut1
  and c2 = dbv_parse dbv_cut2 in
  let hP = [`h:num`; `P:num`; `dl:num`] in
  let d1 = mk_conj(`n = 0`,list_mk_exists(hP,ex))
  and d2 = list_mk_exists(hP,mk_conj(`n = 2 * (LENGTH(inp:byte list) - h) + 2`,c1))
  and d3 = list_mk_exists(hP,mk_conj(`n = 2 * (LENGTH(inp:byte list) - h) + 1`,c2)) in
  list_mk_abs([`n:num`; `s:armstate`],list_mk_disj[d1;d2;d3]);;

let DBV_EV_MONO = prove
 (`!(step:A->A->bool) P Q s.
     (!s'. P s' ==> Q s') ==> eventually step P s ==> eventually step Q s`,
  MESON_TAC[EVENTUALLY_MONO]);;

(* Through a lemma at state s (its precondition the assumption th), to the   *)
(* goal eventually arm (\s'. G s' /\ C s s') s; tac proves Post s' ==> G s'. *)

let DBV_THROUGH_TAC (lemma:thm) (pre:thm) (tac:tactic) : tactic = fun (asl,w as g) ->
  let s = rand w in
  let lem = SPEC_ALL lemma in
  let gth = TAC_PROOF((asl,lhand(concl lem)),
                      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) in
  let th = SPEC s (REWRITE_RULE[ensures] (MP lem gth)) in
  (MP_TAC th THEN ANTS_TAC THENL
    [ACCEPT_TAC pre;
     MATCH_MP_TAC DBV_EV_MONO THEN X_GEN_TAC `s':armstate` THEN
     REWRITE_TAC[] THEN
     DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN DISCH_TAC THEN
     CONJ_TAC THENL [POP_ASSUM MP_TAC THEN tac; FIRST_ASSUM ACCEPT_TAC]]) g;;

let dbv_conj_of th tm = find (fun c -> concl c = tm) (CONJUNCTS th);;

(* From a segment post to Q s' \/ ?m. m < n /\ R m s', with the asm n = ...  *)
(* (neq) and the next cut point the k-th disjunct of R (k = 2 or 3).         *)

let DBV_SEG_POST_TAC (neq:thm) (k:int) (bound:term) : tactic =
  DISCH_THEN(DISJ_CASES_THEN2
   (fun th -> DISJ2_TAC THEN EXISTS_TAC `0` THEN REWRITE_TAC[] THEN
              CONJ_TAC THENL [MP_TAC neq THEN ARITH_TAC;
                              DISJ1_TAC THEN ACCEPT_TAC th])
   (X_CHOOSE_THEN `h':num` (X_CHOOSE_THEN `P':num` (X_CHOOSE_THEN `dl':num`
     (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  (fun (asl,w as g) ->
     let cut = snd(hd asl) and lt = snd(hd(tl asl)) in
     let bth = dbv_conj_of cut bound in
     let m = if k = 2 then `2 * (LENGTH(inp:byte list) - h') + 2`
             else `2 * (LENGTH(inp:byte list) - h') + 1` in
     (DISJ2_TAC THEN EXISTS_TAC m THEN REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY MP_TAC [neq; lt; bth] THEN ARITH_TAC;
        (if k = 2 then DISJ2_TAC THEN DISJ1_TAC else DISJ2_TAC THEN DISJ2_TAC) THEN
        MAP_EVERY EXISTS_TAC [`h':num`; `P':num`; `dl':num`] THEN
        CONJ_TAC THENL [REFL_TAC; ACCEPT_TAC cut]]) g);;

let DBV_MAIN_TAC (entry:thm) (exitl:thm) (seg1:thm) (seg2:thm) : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_CUT_ENTRY THEN EXISTS_TAC dbv_R THEN
  REPEAT CONJ_TAC THENL
   [(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC);
    REWRITE_TAC[ensures] THEN X_GEN_TAC `s:armstate` THEN DISCH_TAC THEN
    (fun (asl,w as g) -> DBV_THROUGH_TAC entry (snd(hd asl))
      (DISCH_THEN(DISJ_CASES_THEN2
        (fun th -> DISJ1_TAC THEN ACCEPT_TAC th)
        (fun th -> DISJ2_TAC THEN
                   EXISTS_TAC `2 * (LENGTH(inp:byte list) - 0) + 2` THEN
                   REWRITE_TAC[] THEN DISJ2_TAC THEN DISJ1_TAC THEN
                   MAP_EVERY EXISTS_TAC [`0`; `LENGTH(out:byte list)`; `0`] THEN
                   CONJ_TAC THENL [REFL_TAC; ACCEPT_TAC th]))) g);
    MATCH_MP_TAC ENSURES_MEASURE_INDUCT THEN CONJ_TAC THENL
     [(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC); ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[ensures] THEN
    X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h:num` (X_CHOOSE_THEN `P:num`
        (X_CHOOSE_THEN `dl:num` ASSUME_TAC))))
     (DISJ_CASES_THEN
       (X_CHOOSE_THEN `h:num` (X_CHOOSE_THEN `P:num` (X_CHOOSE_THEN `dl:num`
          (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THENL
     [(fun (asl,w as g) -> DBV_THROUGH_TAC exitl (snd(hd asl))
        (DISCH_THEN(fun th -> DISJ1_TAC THEN ACCEPT_TAC th)) g);
      (fun (asl,w as g) -> DBV_THROUGH_TAC seg1 (snd(hd asl))
        (DBV_SEG_POST_TAC (snd(hd(tl asl))) 3 `h' + 70 <= LENGTH(inp:byte list)`) g);
      (fun (asl,w as g) -> DBV_THROUGH_TAC seg2 (snd(hd asl))
        (DBV_SEG_POST_TAC (snd(hd(tl asl))) 2 `h' + 131 <= LENGTH(inp:byte list)`) g)]];;

(* ------------------------------------------------------------------------- *)
(* The segments, the exit, the entry and the function.                       *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DBV_SEG1 = prove
 (dbv_seg_stmt dbv_cut1 dbv_cut2,
  DBV_SEG_TAC [`word(pc + 0x6940):int64`; `word(pc + 0x6988):int64`]);;

let SNAPPY_DBV_SEG2 = prove
 (dbv_seg_stmt dbv_cut2 dbv_cut1,
  DBV_SEG_TAC [`word(pc + 0x6890):int64`; `word(pc + 0x6988):int64`]);;

let SNAPPY_DBV_EXIT = prove(dbv_exit_stmt, DBV_EXIT_TAC);;

let SNAPPY_DBV_ENTRY = prove(dbv_entry_stmt, DBV_ENTRY_TAC);;

let SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  DBV_MAIN_TAC SNAPPY_DBV_ENTRY SNAPPY_DBV_EXIT SNAPPY_DBV_SEG1 SNAPPY_DBV_SEG2);;

(* ------------------------------------------------------------------------- *)
(* Correctness alone.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC
    SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
