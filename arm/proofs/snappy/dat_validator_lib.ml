(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The library of the proof of DecompressAllTags<SnappyDecompressionValidator> *)
(* of the gcc12_O2 build (0x6a30): the states at the cut points, the model   *)
(* lemmas and the tactics of the segments. Loaded by the proof file of the   *)
(* function and by the spec and proof files of its pieces, the segment T    *)
(* restricted to one tag class (..._validator_t_{b,s}_{class}_*.ml), which   *)
(* are independent jobs. The tools of its segments, shared with the proof   *)
(* of DecompressBranchless<size_t>, are validator_segment_tools.ml's. First  *)
(* assembled by a development script, now maintained by hand.               *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/snappy_decompressor_decompress_all_tags_validator_spec.ml";;
needs "arm/proofs/snappy/validator_tactics.ml";;
needs "arm/proofs/snappy/array_writer.ml";;
needs "common/ensures_measure.ml";;
needs "arm/proofs/snappy/gcc12_O2/length_minus_offset_lib.ml";;
needs "common/snappy/snappy_slow_path.ml";;

needs "common/tactic_timing.ml";;
needs "common/arith_facts.ml";;
needs "arm/proofs/snappy/validator_segment_tools.ml";;

(* ------------------------------------------------------------------------- *)
(* The contract of DecompressBranchless<size_t> without X27 and X28, which   *)
(* it saves and restores (the frame of DecompressAllTags does not have them). *)
(* ------------------------------------------------------------------------- *)

let dat_drop_regs_stmt =
  let stmt = SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT in
  let vs,bod = strip_forall stmt in
  let hyp,ens = dest_imp bod in
  let step,pre,post,fr = match strip_comb ens with
      _,[a;b;c;d] -> a,b,c,d | _ -> failwith "dat_drop_regs_stmt" in
  let bad t = match t with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) ->
        c = `X27` || c = `X28`
    | _ -> false in
  let drop lam =
    let s,b = dest_abs lam in
    mk_abs(s,list_mk_conj(filter (not o bad) (conjuncts b))) in
  let fr' = subst [`[SP; X19; X20; X21; X22; X23; X24; X25; X26; X29; X30]`,
                   `[SP; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28;
                     X29; X30]`] fr in
  let vs' = filter (fun v -> name_of v <> "x27" && name_of v <> "x28") vs in
  list_mk_forall(vs',
    mk_imp(hyp,list_mk_icomb "ensures" [step; drop pre; drop post; fr']));;

let ENSURES_PREPOST_MONO = prove
 (`!(P:armstate->bool) P' Q Q' C.
        (!s. P s ==> P' s) /\ (!s. Q' s ==> Q s)
        ==> ensures arm P' Q' C ==> ensures arm P Q C`,
  MESON_TAC[ENSURES_PREPOSTCONDITION_THM]);;

let SNAPPY_DBU_NO_X27_X28 = prove
 (dat_drop_regs_stmt,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_PRESERVED_TAC "x27" `X27` THEN
  ENSURES_PRESERVED_TAC "x28" `X28` THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [SP; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28;
               X29; X30] ,,
    MAYCHANGE [memory :> bytes(word_sub sp (word 224),224)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
  MP_TAC(SPEC_ALL SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ENSURES_PREPOST_MONO THEN
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* The footprint of a union of sets (common/footprint.ml), for memory.       *)

needs "common/footprint.ml";;

let DAT_FOOTPRINT_UNION_SUBSUMED =
  MATCH_MP MAYCHANGE_FOOTPRINT_UNION_SUBSUMED
    (VALID_COMPONENT_CONV `valid_component (memory:(armstate,int64->byte)component)`);;

(* ------------------------------------------------------------------------- *)
(* The states of the proof (terms in the variables of the spec).             *)
(* ------------------------------------------------------------------------- *)

let dat_spec_parts =
  let body = snd(strip_forall SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT) in
  let hyp,ens = dest_imp body in
  match snd(strip_comb ens) with
    [_;pre;post;c] -> hyp,pre,post,c
  | _ -> failwith "dat_spec_parts";;

let dat_hyp,dat_pre,dat_post,dat_frame = dat_spec_parts;;

let dat_is_mai t = match strip_comb t with
    Const("memaccess_inset",_),[_;_;_] -> true | _ -> false;;

let dat_spec_mai = find_term dat_is_mai dat_post;;

let dat_parse s =
  let tm = parse_term s in
  try let mine = find_term dat_is_mai tm in subst [dat_spec_mai,mine] tm
  with Failure _ -> tm;;

let dat_sp k = "(word_add (word_sub sp (word 96)) (word " ^ string_of_int k ^ "))";;
let dat_ws = "(memrange(d,48) UNION memrange(src,24) UNION memrange(v,16) UNION memrange(word_sub sp (word 320),320))";;
let dat_rs = "(memrange(d,48) UNION memrange(src,24) UNION memrange(v,16) UNION memrange(q,LENGTH r) UNION memrange(word_sub sp (word 320),320) UNION memrange(word pc,libsnappy_size) UNION memrange(word(pc + libsnappy_rw),libsnappy_rw_size) UNION memrange(ea,el))";;

(* The facts at every cut point. *)

let dat_frame_str =
  String.concat " /\\ "
   (["aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc";
     "read SP s = word_sub sp (word 96)"; "read X29 s = word_sub sp (word 96)";
     "read X19 s = v"; "read X20 s = word_add (word pc) (word 32256)";
     "read X21 s = d"; "read X22 s = word(LENGTH(out:byte list))";
     "read X23 s = x23"; "read X24 s = x24"; "read X25 s = x25";
     "read X26 s = x26";
     "read (memory :> bytes64 (word_sub sp (word 96))) s = x29"] @
    map (fun (k,x) -> "read (memory :> bytes64 " ^ dat_sp k ^ ") s = " ^ x)
     [8,"returnaddress"; 16,"x19"; 24,"x20"; 32,"x21"; 40,"x22"] @
    ["read (memory :> bytes64 d) s = src";
     "read (memory :> bytes64 src) s = word_add (word pc) (word vtable_ByteArraySource)";
     "read (memory :> bytes64 v) s = word m";
     "read (memory :> bytes8 (word_add d (word 40))) s = word 0";
     "read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw";
     "read (memory :> bytes(ea,el)) s = ev";
     "(?e2. read events s = APPEND e2 e /\\ memaccess_inset e2 " ^ dat_rs ^ " " ^ dat_ws ^ ")";
     "LENGTH out + 22 * LENGTH (rest:byte list) <= 22 * LENGTH (r:byte list)";
     "(snappy_decode_tags m r [] = NONE <=> snappy_decode_tags m rest out = NONE)"]);;

(* The window: buffer (B, the input from q + i) or scratch (S). *)

let dat_win_b ip =
  "read (memory :> bytelist(" ^ ip ^ ",LENGTH rest)) s = rest /\\ " ^
  "i + LENGTH rest = LENGTH r /\\ 5 <= LENGTH rest /\\ " ^
  "read (memory :> bytes64 (word_add d (word 16))) s = word_add q (word(LENGTH r)) /\\ " ^
  "read (memory :> bytes64 (word_add d (word 24))) s = word_sub (word_add q (word(LENGTH r))) (word 4) /\\ " ^
  "read (memory :> bytes64 (word_add d (word 32))) s = word(LENGTH r) /\\ " ^
  "read (memory :> bytes64 (word_add src (word 8))) s = q /\\ " ^
  "read (memory :> bytes64 (word_add src (word 16))) s = word(LENGTH r)";;

let dat_win_s =
  "read (memory :> bytelist(word_add d (word 41),LENGTH rest)) s = rest /\\ " ^
  "~(rest = []) /\\ LENGTH rest < 5 /\\ " ^
  "read (memory :> bytes64 (word_add d (word 16))) s = word_add d (word(41 + LENGTH rest)) /\\ " ^
  "read (memory :> bytes64 (word_add d (word 24))) s = word_add d (word 41) /\\ " ^
  "read (memory :> bytes64 (word_add d (word 32))) s = word 0 /\\ " ^
  "read (memory :> bytes64 (word_add src (word 8))) s = word_add q (word(LENGTH r)) /\\ " ^
  "read (memory :> bytes64 (word_add src (word 16))) s = word 0";;

let dat_ipb = "word_add q (word i)" and dat_ips = "word_add d (word 41)";;

let dat_L_b = "read PC s = word (pc + 27264) /\\ read X3 s = " ^ dat_ipb ^
  " /\\ read X1 s = word_add q (word(LENGTH r)) /\\ " ^ dat_win_b dat_ipb ^ " /\\ " ^ dat_frame_str;;
let dat_L_s = "read PC s = word (pc + 27264) /\\ read X3 s = " ^ dat_ips ^
  " /\\ read X1 s = word_add d (word(41 + LENGTH rest)) /\\ " ^ dat_win_s ^ " /\\ " ^ dat_frame_str;;
let dat_T_b = "read PC s = word (pc + 27300) /\\ read X0 s = " ^ dat_ipb ^
  " /\\ " ^ dat_win_b dat_ipb ^ " /\\ " ^ dat_frame_str;;
let dat_T_s = "read PC s = word (pc + 27300) /\\ read X0 s = " ^ dat_ips ^
  " /\\ snappy_refill_ok rest /\\ " ^ dat_win_s ^ " /\\ " ^ dat_frame_str;;

let dat_lam s = dat_parse ("\\s:armstate. " ^ s);;
let dat_body s = body(dat_lam s);;

let dat_global = dat_hyp;;

(* ------------------------------------------------------------------------- *)
(* Model lemmas.                                                             *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECODE_TAGS_NIL = prove
 (`!m (out:byte list).
     snappy_decode_tags m [] out = if LENGTH out = m then SOME out else NONE`,
  REWRITE_TAC[snappy_decode_tags; LENGTH; snappy_decode_tags_fuel]);;

let DAT_WORD_EQ_NUM = prove
 (`!a b. a < 2 EXP 64 /\ b < 2 EXP 64 ==> (word a:int64 = word b <=> a = b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* The exit with eof_ set: the stream ends, the result is the count.         *)

let DAT_EXIT_EOF = prove
 (`!m r (out:byte list) pr.
     (snappy_decode_tags m r [] = NONE <=> snappy_decode_tags m [] out = NONE) /\
     LENGTH out < 2 EXP 64 /\ m < 2 EXP 64 /\ (pr:int64) = word(LENGTH out)
     ==> (T /\ pr = word m <=> ~(snappy_decode_tags m r [] = NONE))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SNAPPY_DECODE_TAGS_NIL] THEN
  ASM_SIMP_TAC[DAT_WORD_EQ_NUM] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT]);;

(* The exit without eof_: the stream fails from the current state.           *)

let DAT_EXIT_FAIL = prove
 (`!m r rest (out:byte list) pr.
     (snappy_decode_tags m r [] = NONE <=> snappy_decode_tags m rest out = NONE) /\
     snappy_decode_tags m rest out = NONE
     ==> (F /\ (pr:int64) = word m <=> ~(snappy_decode_tags m r [] = NONE))`,
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Running: as VAL_RUN_TAC, with stop PCs (a leaf at each) and the PC        *)
(* conditions also decided as integer facts (DAT_PC_TAC).                    *)
(* ------------------------------------------------------------------------- *)

let dat_verbose = ref false;;

(* word_sub of two addresses x + p and x + q with q <= p (the facts): word(p - q). *)

let DAT_WSUB_LEMMA = prove
 (`!(x:int64) p q. q <= p ==> word_sub (word_add x (word p)) (word_add x (word q)) = word(p - q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p = q + (p - q)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE]);;

let dat_wsub_eqs asl tm =
  let pats = find_terms (fun t -> match t with
      Comb(Comb(Const("word_sub",_),a),b) ->
        type_of t = `:int64` && not(is_comb b && is_const(rator b) &&
                                    fst(dest_const(rator b)) = "word")
    | _ -> false) tm in
  if pats = [] then [] else
  let facts = dat_num_facts (dat_facts asl) in
  let norm t = try dat_norm_addr_conv t with Failure _ -> REFL t in
  let split t = match t with
      Comb(Comb(Const("word_add",_),x),Comb(Const("word",_),p)) -> x,p
    | _ -> t,`0` in
  mapfilter (fun t ->
    match t with
      Comb(Comb(ws,a),b) ->
        let tha = norm a and thb = norm b in
        let x,p = split(rand(concl tha)) and y,q = split(rand(concl thb)) in
        if x <> y then fail() else
        let le = TAC_PROOF(([],mk_binary "<=" (q,p)), MAP_EVERY MP_TAC facts THEN ARITH_TAC) in
        let th0 = MP (ISPECL [x;p;q] DAT_WSUB_LEMMA) le in
        let fixa = if p = `0` then CONV_RULE(LAND_CONV(LAND_CONV(REWR_CONV WORD_ADD_0)) ORELSEC ALL_CONV) else I in
        let th0 = if p = `0` || q = `0` then REWRITE_RULE[WORD_ADD_0; SUB_0] th0 else th0 in
        let lhs_eq = MK_COMB(AP_TERM ws tha, thb) in
        TRANS lhs_eq th0
    | _ -> fail()) (setify pats);;

(* VAL_DECIDE_PC_TAC (validator_tactics.ml) with the facts of the decision   *)
(* by dat_arith_levels.                                                       *)

let DAT_VAL_DECIDE_PC_TAC (rws:thm list) : tactic =
  fun (asl,w as g) ->
    let r = bstep_pc_value g in
    let c,_ = dest_cond r in
    let free th = let c = concl th in
      type_of c = bool_ty &&
      not(exists (fun v -> type_of v = `:armstate`) (frees c)) &&
      not(can (find_term (fun t -> match t with
            Const("read",_) | Const("write",_) -> true | _ -> false)) c) in
    let ths = filter free (map snd asl) in
    let levels = dat_arith_levels rws ths c in
    let dec t = dat_try_levels (fun ths' ->
        TAC_PROOF((map (fun th -> "",th) ths',t),
                  BSTEP_ARITH_DECIDE_TAC ~rws)) levels in
    let t0 = Unix.gettimeofday() in
    let slow k = let dt = Unix.gettimeofday() -. t0 in
      if !tactic_timing && dt > 10.0 then
        Printf.printf "SLOWPC %.1f %s asl=%d facts=%d levels=%s: %s\n%!" dt k
          (length asl) (length ths)
          (String.concat "," (map (fun (n,l) -> n ^ ":" ^ string_of_int(length l)) levels))
          (dat_short c) in
    let th = try dec c with Failure _ ->
             try dec (mk_neg c) with Failure m -> (slow "undecided"; failwith m) in
    slow "decided";
    (FIRST_X_ASSUM(fun pth -> match concl pth with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),pc),_)),r')
          when pc = `PC` && r' = r -> ASSUME_TAC(REWRITE_RULE[th] pth)
      | _ -> NO_TAC) THEN
     ASSUME_TAC th) g;;

let rec DAT_RUN_TAC ?(rws=[]) ?(rewrites=[]) ?(kill=ALL_TAC) ?(norm=ALL_TAC)
                    ?(calls=[]) execth i (stops:term list) (leaf:tactic) : tactic = fun g ->
  let r = try bstep_pc_value g with Failure _ -> `T` in
  let again = DAT_RUN_TAC ~rws ~rewrites ~kill ~norm ~calls execth in
  let same k = k = r || can (fun () -> WORD_RULE(mk_eq(k,r))) () in
  (if !dat_verbose then Printf.printf "STEP %d PC %s\n%!" i (dat_short r));
  if r = `returnaddress:int64` then TIMED_TAC "leaf" leaf g
  else if is_cond r then
    let wsub (asl,_ as g) =
      let r = bstep_pc_value g in
      let eqs = dat_wsub_eqs asl r in
      if eqs = [] then failwith "wsub" else
      FIRST_X_ASSUM(fun pth -> match concl pth with
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),pc),_)),r')
            when pc = `PC` && r' = r -> ASSUME_TAC(REWRITE_RULE eqs pth)
        | _ -> NO_TAC) g in
    let rwpc (asl,_ as g) =
      if rws = [] then failwith "rwpc" else
      let rws' = filter (fun th -> is_eq(concl th)) rws in
      let eq = (REWRITE_CONV rws' THENC WORD_REDUCE_CONV THENC REWRITE_CONV rws') r in
      if rand(concl eq) = r then failwith "rwpc" else
      FIRST_X_ASSUM(fun pth -> match concl pth with
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),pc),_)),r')
            when pc = `PC` && r' = r -> ASSUME_TAC(TRANS pth eq)
        | _ -> NO_TAC) g in
    (TIMED_TAC "pc.rewrite" (TRY rwpc THEN TRY wsub) THEN fun g -> let r = try bstep_pc_value g with Failure _ -> r in
     if not(is_cond r) then again i stops leaf g else
     let exact g =
      let c = fst(dest_cond r) in
      let eq = REWRITE_CONV (filter (fun th -> let t = rand(concl th) in
                 t = `T` || t = `F`) rws) c in
      let v = rand(concl eq) in
      if v <> `T` && v <> `F` then failwith "exact" else
      FIRST_X_ASSUM(fun pth -> match concl pth with
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),pc),_)),r')
            when pc = `PC` && r' = r -> ASSUME_TAC(REWRITE_RULE[eq] pth)
        | _ -> NO_TAC) g in
    ((TIMED_TAC "pc.exact" exact ORELSE TIMED_TAC "pc.valdecide" (DAT_VAL_DECIDE_PC_TAC rws) ORELSE
      TIMED_TAC "pc.datpc" (fun g -> (if !dat_verbose then
                   (print_string "SPLIT: "; print_term (fst(dest_cond r));
                    print_newline()));
                DAT_PC_TAC ~verbose:!dat_verbose rws g) ORELSE
      (TIMED_TAC "pc.split" BSTEP_SPLIT_PC_TAC THEN TIMED_TAC "pc.kill" (TRY kill))) THEN
     again i stops leaf) g) g
  else if i > 1 && exists same stops then TIMED_TAC "leaf" leaf g
  else
    match (try Some(snd(find (fun (k,_) -> same k) calls))
           with Failure _ -> None) with
      Some ctac -> let tac,used = ctac i in
                   (TIMED_TAC "run.call" tac THEN TIMED_TAC "run.norm" norm THEN
                    again (i+used) stops leaf) g
    | None -> (TIMED_TAC "run.bstep" (ARM_BSTEP_TAC ~rewrites execth (i--i)) THEN
               TIMED_TAC "run.norm" norm THEN
               again (i+1) stops leaf) g;;

(* ------------------------------------------------------------------------- *)
(* Calls of contracts: instantiate, rewrite with case facts, add the         *)
(* nonoverlapping facts of the hypothesis that the rule of subsets gives.    *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAPPING_SUBSETS = prove
 (`!(a:int64) n b k a' n' b' k'.
        nonoverlapping (a',n') (b',k') /\
        memrange(a,n) SUBSET memrange(a',n') /\
        memrange(b,k) SUBSET memrange(b',k')
        ==> nonoverlapping (a,n) (b,k)`,
  REWRITE_TAC[NONOVERLAPPING_MEMRANGE] THEN SET_TAC[]);;

let NONOVERLAPPING_ZERO = prove
 (`!(a:int64) b k. nonoverlapping (a,0) (b,k) /\ nonoverlapping (b,k) (a,0)`,
  REWRITE_TAC[NONOVERLAPPING_MEMRANGE; MEMRANGE_0; DISJOINT_EMPTY]);;

let dat_nonoverlap_facts (subs:thm list) (ths:thm list) (hyp:term) =
  let rm (a,k) = mk_comb(`memrange:int64#num->int64->bool`,mk_pair(a,k)) in
  let sub r r' =
    try memrange_subset_rule r r' with Failure _ ->
    find (fun th -> concl th = mk_comb(mk_comb(`(SUBSET):(int64->bool)->(int64->bool)->bool`,rm r),rm r')) subs in
  let one c =
    match c with
      Comb(Comb(Const("nonoverlapping",_),p),q) ->
        let r1 = dest_pair p and r2 = dest_pair q in
        if snd r1 = `0` || snd r2 = `0` then
          (if snd r1 = `0` then CONJUNCT1 else CONJUNCT2)
           (ISPECL (if snd r1 = `0` then [fst r1; fst r2; snd r2]
                    else [fst r2; fst r1; snd r1]) NONOVERLAPPING_ZERO) else
        tryfind (fun th ->
          match concl th with
            Comb(Comb(Const("nonoverlapping",_),p'),q') ->
              let r1' = dest_pair p' and r2' = dest_pair q' in
              (try MATCH_MP NONOVERLAPPING_SUBSETS
                     (CONJ th (CONJ (sub r1 r1') (sub r2 r2')))
               with Failure _ ->
                 let th' = ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] th in
                 MATCH_MP NONOVERLAPPING_SUBSETS
                   (CONJ th' (CONJ (sub r1 r2') (sub r2 r1'))))
          | _ -> fail()) ths
    | _ -> fail() in
  mapfilter one (conjuncts hyp);;

let WORD_SUB_SUB_NUM_CONV tm =
  match tm with
    Comb(Comb(Const("word_sub",_),
              Comb(Comb(Const("word_sub",_),x),Comb(Const("word",_),a))),
         Comb(Const("word",_),b))
      when is_numeral a && is_numeral b ->
      let c = mk_numeral(dest_numeral a +/ dest_numeral b) in
      let r = mk_comb(mk_comb(rator(rator tm),x),
                      mk_comb(rator(rand tm),c)) in
      WORD_RULE(mk_eq(tm,r))
  | _ -> failwith "WORD_SUB_SUB_NUM_CONV";;

(* th instantiated by args (terms, evaluated in the state of the goal),      *)
(* rewritten by rws (case facts), then called.                               *)

let DAT_CONTRACT_TAC exec (th:thm) (args:term list) (rws:thm list) (subs:thm list) sname : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    let args = map (arm_bstep_eval asl s) args in
    let dth = CONV_RULE (REWRITE_CONV([C_ARGUMENTS; C_RETURN; ALLPAIRS; ALL; PAIRWISE;
                                       WORD_ADD_0; SUB_0] @ rws) THENC
                         DEPTH_CONV WORD_ADD_ADD_NUM_CONV THENC
                         DEPTH_CONV WORD_SUB_SUB_NUM_CONV)
                (SPECL args th) in
    let novths = map snd (filter (fun (_,th) -> match concl th with
        Comb(Comb(Const("nonoverlapping",_),_),_) -> true | _ -> false) asl) in
    let extra = if is_imp(concl dth)
                then dat_nonoverlap_facts subs novths (lhand(concl dth)) else [] in
    MAP_EVERY ASSUME_TAC extra THEN
    ARM_BSTEP_CONTRACT_TAC exec dth [] sname);;

let DAT_ENTRY_FAIL = prove
 (`!m (r:byte list).
     ~snappy_refill_ok r /\ m < 2 EXP 64
     ==> ((r = [] /\ word 0:int64 = word m) <=>
          ~(snappy_decode_tags m r [] = NONE))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r:byte list = []` THEN
  ASM_REWRITE_TAC[SNAPPY_DECODE_TAGS_NIL; LENGTH] THENL
   [ASM_SIMP_TAC[DAT_WORD_EQ_NUM; ARITH_RULE `0 < 2 EXP 64`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN ASM_ARITH_TAC;
    ASM_MESON_TAC[SNAPPY_DECODE_TAGS_SHORT]]);;

(* ------------------------------------------------------------------------- *)
(* The leaves.                                                               *)
(* ------------------------------------------------------------------------- *)

let DAT_SP_RULE =
  WORD_RULE `word_add (word_sub sp (word 96)) (word 96):int64 = sp`;;

let dat_state_free asl =
  filter (fun (_,th) -> let c = concl th in
    type_of c = bool_ty &&
    not(exists (fun v -> type_of v = `:armstate`) (frees c)) &&
    not(can (find_term (fun t -> match t with
          Const("read",_) | Const("ensures",_) | Const("eventually",_) -> true
        | _ -> false)) c)) asl;;

let REFILL_OK_NONNIL = prove
 (`!r:byte list. snappy_refill_ok r ==> ~(r = [])`,
  SIMP_TAC[snappy_refill_ok]);;

let dat_model_lemmas = ref [REFILL_OK_NONNIL; DAT_ENTRY_FAIL; DAT_EXIT_EOF; DAT_EXIT_FAIL;
                            SNAPPY_DECODE_TAGS_SHORT];;

(* The model facts only (decode_tags, refill_ok, nil, bounds), with the      *)
(* variables equal to [] substituted: MESON over all the state-free facts    *)
(* (and with the equations x = []) did not terminate.                        *)

let dat_model_facts asl =
  let ths = map snd (dat_state_free asl) in
  let nils = mapfilter (fun th -> match concl th with
      Comb(Comb(Const("=",_),x),Const("NIL",_)) when is_var x -> th
    | _ -> fail()) ths in
  let relevant th =
    let c = concl th in
    can (find_term (fun t -> match t with
        Const("snappy_decode_tags",_) | Const("snappy_refill_ok",_) -> true
      | _ -> false)) c ||
    (match c with
       Comb(Const("~",_),Comb(Comb(Const("=",_),_),Const("NIL",_))) -> true
     | Comb(Comb(Const("<",_),_),r) -> r = `2 EXP 64`
     | Comb(Comb(Const("=",_),_),Comb(Const("word",_),Comb(Const("LENGTH",_),x))) -> is_var x
     | _ -> false) in
  nils, map (fun th -> if nils = [] then th else
                       try SUBS nils th with Failure _ -> th) (filter relevant ths);;

let DAT_ADD1_RULE = WORD_RULE
 `!x:int64. word_add (word_sub x (word 1)) (word 1) = x`;;

let DAT_MODEL_TAC : tactic = fun (asl,w) ->
  let nils,facts = dat_model_facts asl in
  let weq = try SUBS_CONV nils w with Failure _ -> REFL w in
  let w' = rhs(concl weq) in
  let wordeqs = filter (fun th -> match concl th with
      Comb(Comb(Const("=",_),l),Comb(Const("word",_),Comb(Const("LENGTH",_),_))) ->
        not(is_comb l && is_const(rator l) && fst(dest_const(rator l)) = "word")
    | _ -> false) facts in
  let try_conv c t = try c t with Failure _ -> REFL t in
  let weq2 = try_conv (GEN_REWRITE_CONV ONCE_DEPTH_CONV [DAT_ADD1_RULE]) w' in
  let weq3 = try_conv (GEN_REWRITE_CONV ONCE_DEPTH_CONV wordeqs) (rhs(concl weq2)) in
  let w3 = rhs(concl weq3) in
  let models = mapfilter (fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("=",_),
        Comb(Comb(Comb(Const("snappy_decode_tags",_),_),r0),Const("NIL",_))),_)),
        Comb(Comb(Const("=",_),Comb(Comb(Comb(Const("snappy_decode_tags",_),_),x),y)),_))
        when r0 = `r:byte list` -> (x,y,th)
    | _ -> fail()) facts in
  let decs = filter (fun th -> can (find_term (fun t -> match t with
      Const("snappy_decode_tags",_) -> true | _ -> false)) (concl th)) facts in
  let fact t = find (fun th -> concl th = t) facts in
  let mlt = fact `m < 2 EXP 64` in
  let shorts = mapfilter (fun (x,y,_) ->
      MP (ISPECL [`m:num`; x; y] SNAPPY_DECODE_TAGS_SHORT)
         (CONJ (fact (mk_neg(mk_eq(x,`[]:byte list`))))
               (fact (mk_neg(mk_comb(`snappy_refill_ok`,x)))))) models in
  let eofs = mapfilter (fun (x,y,th) ->
      if x <> `[]:byte list` then fail() else
      let pr = mk_comb(`word:num->int64`,mk_comb(`LENGTH:byte list->num`,y)) in
      MP (ISPECL [`m:num`; `r:byte list`; y; pr] DAT_EXIT_EOF)
         (CONJ th (CONJ (fact (mk_binary "<" (mk_comb(`LENGTH:byte list->num`,y),`2 EXP 64`)))
                        (CONJ mlt (REFL pr))))) models in
  let entry = try [MP (ISPECL [`m:num`; `r:byte list`] DAT_ENTRY_FAIL)
                      (CONJ (fact `~snappy_refill_ok r`) mlt)] with Failure _ -> [] in
  let nonnils = mapfilter (fun th -> match concl th with
      Comb(Const("~",_),Comb(Comb(Const("=",_),_),Const("NIL",_))) -> th
    | Comb(Const("snappy_refill_ok",_),_) -> MATCH_MP REFILL_OK_NONNIL th
    | _ -> fail()) facts in
  let props = decs @ shorts @ eofs @ entry @ nonnils in
  let th = try TAC_PROOF(([],w3), MAP_EVERY MP_TAC props THEN CONV_TAC TAUT)
    with Failure _ ->
      ((if !dat_verbose then
         (Printf.printf "MODEL FAILED on %s\n%!" (dat_short w3);
          List.iter (fun th -> Printf.printf "  PROP %s\n%!" (dat_short(concl th))) props));
       failwith "DAT_MODEL_TAC") in
  ACCEPT_TAC (EQ_MP (SYM weq) (EQ_MP (SYM weq2) (EQ_MP (SYM weq3) th))) (asl,w);;

let DAT_MODEL_TAC = TIMED_TAC "model" DAT_MODEL_TAC;;

(* ?eofv pr. eof_ = word(bitval eofv) /\ produced_ = pr /\ iff             *)

let DAT_EOF_EXISTS_TAC : tactic = fun (asl,w) ->
  let s = rand(lhand(lhand(snd(strip_exists w)))) in
  let rd c = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s')),_) ->
        c' = c && s' = s
    | _ -> false) asl) in
  let ev = rand(concl(rd `memory :> bytes8 (word_add d (word 40))`)) in
  let b = match ev with
      Comb(Const("word",_),Comb(Const("bitval",_),b)) -> b
    | _ -> if ev = `word 1:byte` then `T` else `F` in
  let pr = rand(concl(rd `memory :> bytes64 (word_add v (word 8))`)) in
  (MAP_EVERY EXISTS_TAC [b; pr] THEN REPEAT CONJ_TAC THENL
    [ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV;
     FIRST_ASSUM ACCEPT_TAC;
     DAT_MODEL_TAC]) (asl,w);;

(* MEMACCESS_INSET_TAC with the subsets that need arithmetic (the loads at  *)
(* ip + k, the table entry) proved by DAT_SUBSET_TAC.                         *)

let DAT_UNION_SUBSET_L = SET_RULE
 `!(a:int64->bool) b u. a SUBSET u /\ b SUBSET u ==> (a UNION b) SUBSET u`;;

let rec DAT_SUB_TAC : tactic = fun (asl,w as g) ->
  let s,t = dest_binary "SUBSET" w in
  match s with
    Comb(Comb(Const("UNION",_),_),_) ->
      (MATCH_MP_TAC DAT_UNION_SUBSET_L THEN CONJ_TAC THEN DAT_SUB_TAC) g
  | Comb(Const("memrange",_),p) when rand p = `0` ->
      REWRITE_TAC[MEMRANGE_0; EMPTY_SUBSET] g
  | _ -> (try ACCEPT_TAC (footprint_subset_rule s t) g
          with Failure _ -> DAT_SUBSET_TAC g);;

let DAT_MEMACCESS_TAC : tactic =
  fun (asl,w) ->
    let v,bod = dest_exists w in
    let eqt = lhand bod in
    let t = lhs eqt and e = rand(rhs eqt) in
    let x = events_prefix e t in
    set_component_assumptions (map snd asl);
    let one (asl,w as g) =
      match w with
        Comb(Comb(Const("SUBSET",_),s),t) -> DAT_SUB_TAC g
      | Comb(Comb(Comb(Const("memaccess_inset",_),l),rs),ws) ->
          let th = snd(find (fun (_,th) -> match concl th with
              Comb(Comb(Comb(Const("memaccess_inset",_),l'),_),_) ->
                compare l l' = 0
            | _ -> false) asl) in
          let rs',ws' = rand(rator(concl th)),rand(concl th) in
          let sub a b = TAC_PROOF((asl,mk_icomb(mk_icomb(`(SUBSET):(A->bool)->(A->bool)->bool`,a),b)), DAT_SUB_TAC) in
          ACCEPT_TAC (MATCH_MP MEMACCESS_INSET_MONO
            (CONJ (sub rs' rs) (CONJ (sub ws' ws) th))) g
      | _ -> failwith "DAT_MEMACCESS_TAC" in
    (EXISTS_TAC x THEN CONJ_TAC THENL
      [REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
       REWRITE_TAC[MEMACCESS_INSET_CLAUSES; MEMACCESS_INSET_APPEND;
                   event_loads; event_stores; EMPTY_SUBSET] THEN
       REPEAT CONJ_TAC THEN one]) (asl,w);;

let DAT_MEMACCESS_TAC = TIMED_TAC "memaccess" DAT_MEMACCESS_TAC;;

let dat_read_extra = ref (NO_TAC:tactic);;

let DAT_READ_TAC = TIMED_TAC "read" DAT_READ_EQ_TAC;;
let DAT_ARITH_TAC = TIMED_TAC "arith" DAT_ARITH_FACTS_TAC;;

let DAT_POST_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[DAT_SP_RULE]) THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w as g) ->
    (if !dat_verbose then Printf.printf "POST GOAL %s\n%!" (dat_short w));
    if is_exists w && can (find_term ((=) `events:(armstate,(uarch_event)list)component`)) w
    then (TRY(W(fun (asl,w) ->
            let evth = snd(find (fun (_,th) -> is_eq(concl th) &&
              lhand(concl th) = lhand(lhand(snd(dest_exists w)))) asl) in
            REWRITE_TAC[evth])) THEN DAT_MEMACCESS_TAC) g
    else if is_exists w then DAT_EOF_EXISTS_TAC g
    else (FIRST_ASSUM ACCEPT_TAC ORELSE DAT_READ_TAC ORELSE (fun g -> !dat_read_extra g) ORELSE
          (ASM_REWRITE_TAC[] THEN NO_TAC)) g);;

(* A conjunct of a cut point. *)

let DAT_CUT_ONE_TAC : tactic = fun (asl,w as g) ->
  (if !dat_verbose then Printf.printf "CUT GOAL %s\n%!" (dat_short w));
  if is_exists w then
    (TRY(W(fun (asl,w) ->
       let evth = snd(find (fun (_,th) -> is_eq(concl th) &&
         lhand(concl th) = lhand(lhand(snd(dest_exists w)))) asl) in
       REWRITE_TAC[evth])) THEN DAT_MEMACCESS_TAC) g
  else match w with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),_)),_) ->
      (FIRST_ASSUM ACCEPT_TAC ORELSE DAT_READ_TAC ORELSE (fun g -> !dat_read_extra g)) g
  | _ -> (FIRST_ASSUM ACCEPT_TAC ORELSE (ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
          DAT_ARITH_TAC ORELSE DAT_MODEL_TAC) g;;

let dat_pc_is k (asl,w) =
  exists (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),pc),_)),v) ->
        pc = `PC` && v = mk_comb(`word:num->int64`,
                                 mk_binary "+" (`pc:num`,mk_small_numeral k))
    | _ -> false) asl;;

(* The leaf: the postcondition is Post \/ D1 \/ ... \/ Dn, each Di an         *)
(* existential of a cut point; cands: for each Di (index from 1) the list of *)
(* witness lists to try.                                                      *)

let dat_leaf_debug = ref false;;

let rec dat_disj_tac k tac =
  if k = 0 then DISJ1_TAC THEN tac else DISJ2_TAC THEN dat_disj_tac (k-1) tac;;

let DAT_SUB_RULES = map (fun t -> prove(t, REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE))
 [`!(x:int64) a b. word_sub (word_add x (word (a + b))) (word_add x (word a)) = word b`;
  `!(x:int64) a. word_sub (word_add x (word a)) x = word a`];;

(* Decide the conditions in the values of the read facts of the state by    *)
(* integer arithmetic (DAT_INT_PROVE), and rewrite the facts.                *)

let DAT_NORM_COND_TAC : tactic = fun (asl,w) ->
  let s = try rand w with Failure _ -> failwith "DAT_NORM_COND_TAC" in
  let memo = ref [] in
  let decide b =
    try assoc b !memo with Failure _ ->
    let t0 = Unix.gettimeofday() in
    let d =
      try Some(EQT_INTRO(DAT_INT_PROVE [] asl b)) with Failure _ ->
      try Some(EQF_INTRO(DAT_INT_PROVE [] asl (mk_neg b))) with Failure _ -> None in
    let dt = Unix.gettimeofday() -. t0 in
    (if !tactic_timing && dt > 10.0 then
       (let fs = dat_facts asl in
        let lv = dat_arith_levels [] fs b in
        Printf.printf "SLOWCOND %.1f %s asl=%d facts=%d levels=%s termsize=%d: %s\n%!" dt
         (match d with Some _ -> "decided" | None -> "undecided")
         (length asl) (length fs)
         (String.concat "," (map (fun (n,l) -> n ^ ":" ^ string_of_int(length l)) lv))
         (String.length(string_of_term b)) (dat_short b)));
    memo := (b,d) :: !memo; d in
  let fix (_,th) =
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s1)),v)
        when s1 = s && can (find_term is_cond) v ->
        let conds = setify(map (fun t -> fst(dest_cond t)) (find_terms is_cond v)) in
        let ds = mapfilter (fun b -> match decide b with
                                       Some d -> d | None -> fail()) conds in
        if ds = [] then fail() else
        (concl th,CONV_RULE(RAND_CONV(REWRITE_CONV ds)) th)
    | _ -> fail() in
  let fixes = mapfilter fix asl in
  MAP_EVERY (fun (oc,nth) -> UNDISCH_THEN oc (K(ASSUME_TAC nth))) fixes (asl,w);;

let DAT_LIST_FACTS_TAC : tactic = fun (asl,w) ->
  let ths = mapfilter (fun (_,th) -> match concl th with
      Comb(Const("~",_),Comb(Comb(Const("=",_),_),Const("NIL",_))) -> EQF_INTRO th
    | Comb(Const("snappy_refill_ok",_),_) -> EQF_INTRO(MATCH_MP REFILL_OK_NONNIL th)
    | _ -> fail()) asl in
  let isread th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),_)),_) -> true
    | _ -> false in
  if ths = [] then ALL_TAC (asl,w) else
  RULE_ASSUM_TAC(fun th -> if isread th then REWRITE_RULE(BITVAL_CLAUSES :: ths) th
                           else th) (asl,w);;

let DAT_LEAF_TAC (cands:(int * term list) list) : tactic =
  TIMED_TAC "leaf.listfacts" DAT_LIST_FACTS_TAC THEN
  TIMED_TAC "leaf.subrules" (RULE_ASSUM_TAC(REWRITE_RULE DAT_SUB_RULES)) THEN
  TIMED_TAC "leaf.normcond" (TRY DAT_NORM_COND_TAC) THEN
  TIMED_TAC "leaf.final" BSTEP_FINAL_TAC THEN
  (fun g ->
    if !dat_leaf_debug then
      (let pcs = mapfilter (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),pc),_)),v)
            when pc = `PC` -> v | _ -> fail()) (fst g) in
       Printf.printf "LEAF at PC %s\n%!" (String.concat "," (map string_of_term pcs));
       ALL_TAC g) else
    let w = snd g in
    let n = length(disjuncts w) - 1 in
    let pick k tac = if k = n then funpow n (fun t -> DISJ2_TAC THEN t) tac
                     else dat_disj_tac k tac in
    if dat_pc_is 0 g || can (fun (asl,_) -> find (fun (_,th) ->
         concl th = `read PC s = returnaddress`) asl) g ||
       exists (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),pc),_)),v) ->
            pc = `PC` && v = `returnaddress:int64`
        | _ -> false) (fst g)
    then pick 0 (TIMED_TAC "leaf.post" DAT_POST_TAC) g
    else
      FIRST (map (fun (k,ws) ->
        pick k ((fun g -> let nv = length(fst(strip_exists(snd g))) in
                          let rec lastn l = if length l <= nv then l else lastn (tl l) in
                          MAP_EVERY EXISTS_TAC (lastn ws) g) THEN
                TIMED_TAC "leaf.cut" (REPEAT CONJ_TAC THEN DAT_CUT_ONE_TAC))) cands) g);;

(* ------------------------------------------------------------------------- *)
(* The entry: to the exit or the loop (L) with the whole stream.             *)
(* ------------------------------------------------------------------------- *)

let DAT_EXEC = SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_VALIDATOR_GCC12_O2_EXEC;;
let DAT_REFILL_EMPTY = SNAPPY_DECOMPRESSOR_REFILL_TAG_EMPTY_GCC12_O2_IMAGE_SUBROUTINE_SAFE;;
let DAT_REFILL_WINDOW = SNAPPY_DECOMPRESSOR_REFILL_TAG_WINDOW_GCC12_O2_IMAGE_SUBROUTINE_SAFE;;

let dat_mk_stmt pre post =
  let tm = mk_imp(dat_global, list_mk_icomb "ensures" [`arm`; pre; post; dat_frame]) in
  list_mk_forall(frees tm, tm);;

let dat_entry_stmt =
  let sb t = subst [`0`,`i:num`; `r:byte list`,`rest:byte list`;
                    `[]:byte list`,`out:byte list`] t in
  let norm t = rhs(concl((REWRITE_CONV[LENGTH; ADD_CLAUSES; WORD_ADD_0]) t)) in
  let lb = norm(sb(dat_body dat_L_b)) and ls = norm(sb(dat_body dat_L_s)) in
  let post = mk_abs(`s:armstate`,
    list_mk_disj[rhs(concl(BETA_CONV(mk_comb(dat_post,`s:armstate`)))); lb; ls]) in
  dat_mk_stmt dat_pre post;;

let dat_refill_args kind p n k ip rest =
  [`read events s`; `read X0 s`; `src:int64`; p; n] @
  (if kind = "EMPTY" then [k] else []) @
  [ip; rest; `pc:num`; `rw:num`; `read SP s`; `read X30 s`;
   `read X19 s`; `read X20 s`; `read X21 s`; `read X22 s`; `read X23 s`;
   `read X24 s`; `read X29 s`; `ea:int64`; `el:num`; `ev:num`];;

let DAT_ENTRY_TAC : tactic =
  REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(r:byte list) < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `snappy_refill_ok r` THEN
  ASM_CASES_TAC `LENGTH(r:byte list) < 5` THEN
  ENSURES_INIT_TAC "s0" THEN
  W(fun (asl,w) ->
    let cs = map (fun t -> let th = snd(find (fun (_,th) -> concl th = t ||
                                                  concl th = mk_neg t) asl) in
                  if is_neg(concl th) then EQF_INTRO th else EQT_INTRO th)
               [`snappy_refill_ok r`; `LENGTH(r:byte list) < 5`] in
    let call i = DAT_CONTRACT_TAC DAT_EXEC DAT_REFILL_EMPTY
      (dat_refill_args "EMPTY" `q:int64` `LENGTH(r:byte list)` `0` `ip:int64` `r:byte list`)
      cs [] ("s" ^ string_of_int i), 1 in
    DAT_RUN_TAC ~calls:[`word(pc + 18064):int64`, call]
      ~norm:(TRY(VAL_NORM_COND_TAC ~rws:[]))
      DAT_EXEC 1 [`word(pc + 27264):int64`]
      (DAT_LEAF_TAC [1,[]; 2,[]]));;

(* ------------------------------------------------------------------------- *)
(* The segments from the cut points.                                         *)
(* ------------------------------------------------------------------------- *)

(* Post \/ ?i' rest' out'. LENGTH rest' REL LENGTH rest /\ next ...          *)

let dat_seg_stmt (pre:string) (nexts:(string*string) list) =
  let sb t = subst [`i':num`,`i:num`; `rest':byte list`,`rest:byte list`;
                    `out':byte list`,`out:byte list`] t in
  let nx (str,rel) =
    let c = mk_binary rel (`LENGTH(rest':byte list)`,`LENGTH(rest:byte list)`) in
    list_mk_exists([`i':num`; `rest':byte list`; `out':byte list`],
                   mk_conj(c, sb(dat_body str))) in
  let post = mk_abs(`s:armstate`,
    list_mk_disj(rhs(concl(BETA_CONV(mk_comb(dat_post,`s:armstate`)))) ::
                 map nx nexts)) in
  dat_mk_stmt (dat_lam pre) post;;

let READ_BYTELIST_ZERO = prove
 (`!(a:int64) s. read (memory :> bytelist(a,0)) s = []`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `a:int64`; `0`;
                 `s:armstate`; `[]:byte list`] READ_BYTELIST_EQ_EL) THEN
  REWRITE_TAC[LENGTH; LT]);;

let DAT_SUB_LIST_APPEND_RIGHT = prove
 (`!(x:A list) r n. SUB_LIST(LENGTH x,n) (APPEND x r) = SUB_LIST(0,n) r`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; LENGTH; SUB_LIST_CLAUSES]);;

let DAT_READ_SUFFIX = prove
 (`!(a:int64) (inp:byte list) inp' s.
     read (memory :> bytelist(a,LENGTH inp)) s = inp /\ (?h. inp = APPEND h inp')
     ==> read (memory :> bytelist(word_add a (word(LENGTH inp - LENGTH inp')),
                                  LENGTH inp')) s = inp'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `h:byte list` SUBST1_TAC)) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `a:int64`;
                 `APPEND (h:byte list) inp'`; `LENGTH(h:byte list)`; `s:armstate`]
         READ_BYTELIST_SUFFIX) THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; ARITH_RULE `(a + b) - b:num = a`;
                  ARITH_RULE `(a + b) - a:num = b`; LE_ADD] THEN
  REWRITE_TAC[DAT_SUB_LIST_APPEND_RIGHT; SUB_LIST_LENGTH]);;

let DAT_STEPS_MODEL = prove
 (`!k m r (inp:byte list) out inp' out'.
     snappy_steps k (2 EXP 63) (inp,out) = SOME(inp',out') /\ m < 2 EXP 32 /\
     LENGTH out + 22 * LENGTH inp <= 22 * LENGTH r /\
     (snappy_decode_tags m r [] = NONE <=> snappy_decode_tags m inp out = NONE)
     ==> (?h. inp = APPEND h inp') /\ LENGTH inp' <= LENGTH inp /\
         LENGTH out' + 22 * LENGTH inp' <= 22 * LENGTH r /\
         (snappy_decode_tags m r [] = NONE <=>
          snappy_decode_tags m inp' out' = NONE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SNAPPY_STEPS_SOME) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SNAPPY_STEPS_RATIO) THEN
  MP_TAC(SPECL [`k:num`; `m:num`; `2 EXP 63`; `inp:byte list`; `out:byte list`;
                `inp':byte list`; `out':byte list`] SNAPPY_STEPS_BOUND_NONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `h:byte list` THEN FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `inp:byte list = APPEND h inp'` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_MESON_TAC[]]);;

(* Replace the value of the fact read c s = v by v', proved equal.          *)

let dat_word_eq asl l r =
  let facts = dat_facts asl in
  let tm = mk_eq(l,r) in
  try WORD_RULE tm with Failure _ ->
  TAC_PROOF(([],tm),
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    REPEAT AP_TERM_TAC THEN MAP_EVERY MP_TAC (dat_num_facts facts) THEN ARITH_TAC);;

let DAT_REPLACE_TAC (c:term) (v':term) : tactic = fun (asl,w) ->
  let s = rand w in
  let th = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s')),_) -> c' = c && s' = s
    | _ -> false) asl) in
  let v = rand(concl th) in
  if v = v' then ALL_TAC (asl,w) else
  let eq = dat_word_eq asl v v' in
  (UNDISCH_THEN (concl th) (fun th -> ASSUME_TAC(TRANS th eq))) (asl,w);;

let dat_read_value c (asl,w) =
  let s = rand w in
  rand(concl(snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s')),_) -> c' = c && s' = s
    | _ -> false) asl)));;

let DAT_VAL_ADD_LT = prove
 (`!(a:int64) i n. val a + i + n < 2 EXP 64 ==> val(word_add a (word i)) + n < 2 EXP 64`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `i MOD 2 EXP 64 = i` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(val(a:int64) + i) MOD 2 EXP 64 = val a + i` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;



let NOT_REFILL_OK_NIL = prove
 (`~snappy_refill_ok []`, REWRITE_TAC[snappy_refill_ok]);;

let dat_find_fact pat vars asl =
  let lcs = subtract (frees pat) vars in
  snd(find (fun (_,th) -> can (term_match lcs pat) (concl th)) asl);;

let dat_bool_fact asl t =
  try let th = snd(find (fun (_,th) -> concl th = t) asl) in EQT_INTRO th
  with Failure _ ->
  let th = snd(find (fun (_,th) -> concl th = mk_neg t) asl) in EQF_INTRO th;;

let dat_num_of_word t =
  match t with Comb(Const("word",_),n) -> n | _ -> failwith "dat_num_of_word";;

(* The facts that a contract needs that are proved before the call: the     *)
(* subsets of the windows (for the nonoverlapping hypotheses).               *)

let dat_subs = par_local_ref (fun () -> ([]:thm list));;

let DAT_ADD_SUBSET_TAC (tm:term) : tactic = fun (asl,w) ->
  let facts = dat_facts asl in
  let th = TAC_PROOF(([],tm),
    TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
    FIRST [MATCH_MP_TAC MEMRANGE_OFFSET_SUBSET THEN
           MAP_EVERY MP_TAC (dat_num_facts facts) THEN ARITH_TAC;
           MATCH_MP_TAC MEMRANGE_PREFIX_SUBSET THEN
           MAP_EVERY MP_TAC (dat_num_facts facts) THEN ARITH_TAC]) in
  dat_subs () := th :: !(dat_subs ()); ASSUME_TAC th (asl,w);;

(* RefillTag at the current state: EMPTY if the window w at ip_ is [] (a     *)
(* fact w = [] or the window of length 0), WINDOW otherwise.                 *)

let rec DAT_REFILL_TAC i : tactic = fun (asl,w as g) ->
  let v80 = dat_read_value `memory :> bytes64 (word_add d (word 8))` g in
  let v8n = rhs(concl((DEPTH_CONV WORD_ADD_ADD_NUM_CONV) v80)) in
  if v8n <> v80 then
    (DAT_REPLACE_TAC `memory :> bytes64 (word_add d (word 8))` v8n THEN
     DAT_REFILL_TAC i) g else
  let s = rand w in
  let rv c = dat_read_value c g in
  let v8 = rv `memory :> bytes64 (word_add d (word 8))`
  and lim = rv `memory :> bytes64 (word_add d (word 16))`
  and n32 = rv `memory :> bytes64 (word_add d (word 32))`
  and p = rv `memory :> bytes64 (word_add src (word 8))`
  and n16 = rv `memory :> bytes64 (word_add src (word 16))` in
  let wth = try Some(snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),_),Comb(Const("bytelist",_),pr))),s')),_) ->
         s' = s && (fst(dest_pair pr) = v8 ||
                    can (dat_word_eq asl (fst(dest_pair pr))) v8)
    | _ -> false) asl)) with Failure _ -> None in
  let wth = match wth with
      None -> None
    | Some th ->
        let a = fst(dest_pair(rand(rand(rand(rator(lhand(concl th))))))) in
        if a = v8 then Some th else
        let eq = dat_word_eq asl a v8 in
        Some(SUBS [eq] th) in
  let win = match wth with Some th -> rand(concl th) | None -> `[]:byte list` in
  let empty = wth = None ||
              exists (fun (_,th) -> concl th = mk_eq(win,`[]:byte list`)) asl in
  let sname = "s" ^ string_of_int i in
  let addw = match wth with Some th when not(empty) -> ASSUME_TAC th | _ -> ALL_TAC in
  (if !dat_verbose then
     Printf.printf "REFILL %s ip_ = %s limit = %s\n%!" (if empty then "EMPTY" else "WINDOW")
       (dat_short v8) (dat_short lim));
  if empty then
    let k = dat_num_of_word n32 and n = dat_num_of_word n16 in
    let addr = rhs(concl(REWRITE_CONV[WORD_ADD_0]
                 (mk_comb(mk_comb(`word_add:int64->int64->int64`,p),
                          mk_comb(`word:num->int64`,k))))) in
    let zth = ISPECL [addr; s] READ_BYTELIST_ZERO in
    let rws = [NOT_REFILL_OK_NIL; SUB_REFL; LENGTH; ARITH_RULE `0 < 5`] in
    (DAT_REPLACE_TAC `memory :> bytes64 (word_add d (word 8))` lim THEN
     ASSUME_TAC zth THEN
     DAT_CONTRACT_TAC DAT_EXEC DAT_REFILL_EMPTY
       (dat_refill_args "EMPTY" p n k lim `[]:byte list`) rws !(dat_subs ()) sname) g
  else
    let lw = mk_comb(`LENGTH:byte list->num`,win) in
    let lim' = mk_comb(mk_comb(`word_add:int64->int64->int64`,v8),
                       mk_comb(`word:num->int64`,lw)) in
    let rws = [EQF_INTRO(snd(find (fun (_,th) -> concl th = mk_neg(mk_eq(win,`[]:byte list`))) asl));
               dat_bool_fact asl (mk_binary "<" (lw,`5`));
               dat_bool_fact asl (mk_comb(`snappy_refill_ok`,win))] in
    (addw THEN DAT_REPLACE_TAC `memory :> bytes64 (word_add d (word 16))` lim' THEN
     DAT_CONTRACT_TAC DAT_EXEC DAT_REFILL_WINDOW
       (dat_refill_args "WINDOW" p n32 `0` v8 win) rws !(dat_subs ()) sname) g;;

(* ------------------------------------------------------------------------- *)
(* The segment from L: DecompressBranchless, then T directly or a refill.    *)
(* ------------------------------------------------------------------------- *)

let dat_ip st = if st = "B" then `word_add (q:int64) (word i)` else `word_add (d:int64) (word 41)`;;
let dat_region st = if st = "B" then `q:int64,LENGTH(r:byte list)` else `d:int64,48`;;

let dat_mk_sub (a,k) (b,l) =
  mk_comb(mk_comb(`(SUBSET):(int64->bool)->(int64->bool)->bool`,
                   mk_comb(`memrange:int64#num->int64->bool`,mk_pair(a,k))),
          mk_comb(`memrange:int64#num->int64->bool`,mk_pair(b,l)));;

let DAT_SETUP_TAC st : tactic =
  REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(r:byte list) < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  SUBGOAL_THEN `LENGTH(out:byte list) < 2 EXP 63` ASSUME_TAC THENL
   [MP_TAC(ASSUME `LENGTH(r:byte list) < 2 EXP 58`) THEN
    MP_TAC(ASSUME `LENGTH(out:byte list) + 22 * LENGTH (rest:byte list) <= 22 * LENGTH (r:byte list)`) THEN
    ARITH_TAC; ALL_TAC] THEN
  (fun g -> dat_subs () := []; ALL_TAC g) THEN
  (if st = "B" then
     SUBGOAL_THEN `val(word_add (q:int64) (word i)) + LENGTH(rest:byte list) < 2 EXP 64`
       ASSUME_TAC THENL
      [MATCH_MP_TAC DAT_VAL_ADD_LT THEN ASM_ARITH_TAC; ALL_TAC]
   else
     SUBGOAL_THEN `val(word_add (d:int64) (word 41)) + LENGTH(rest:byte list) < 2 EXP 64`
       ASSUME_TAC THENL
      [MATCH_MP_TAC DAT_VAL_ADD_LT THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  DAT_ADD_SUBSET_TAC (dat_mk_sub (dat_ip st,`LENGTH(rest:byte list)`)
                                 (dest_pair(dat_region st)));;

let DAT_AFTER_DBU_TAC st : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[DAT_ADD1_RULE]) THEN
  W(fun (asl,w) ->
    let s = rand w in
    let sth = dat_find_fact
      `snappy_steps k (2 EXP 63) (rest,out) = SOME(a:byte list,b:byte list)`
      [`k:num`; `a:byte list`; `b:byte list`] asl in
    let inp',out' = dest_pair(rand(rand(concl sth))) in
    let model = snd(find (fun (_,th) -> is_iff(concl th) &&
      rhs(concl th) = `snappy_decode_tags m rest out = NONE`) asl) in
    let ratio = snd(find (fun (_,th) -> concl th =
      `LENGTH(out:byte list) + 22 * LENGTH (rest:byte list) <= 22 * LENGTH (r:byte list)`) asl) in
    let mlt = snd(find (fun (_,th) -> concl th = `m < 2 EXP 32`) asl) in
    let mth = MATCH_MP DAT_STEPS_MODEL (CONJ sth (CONJ mlt (CONJ ratio model))) in
    let ex,rest = CONJ_PAIR mth in
    let bl = dat_find_fact (vsubst [s,`s:armstate`]
      `read (memory :> bytelist(a:int64,LENGTH(rest:byte list))) s = rest`) [`a:int64`] asl in
    let bth = MATCH_MP DAT_READ_SUFFIX (CONJ bl ex) in
    let ip' = fst(dest_pair(rand(rand(rand(rator(lhand(concl bth))))))) in
    let lw = mk_comb(`LENGTH:byte list->num`,inp') in
    let sub = dat_mk_sub (ip',lw) (dest_pair(dat_region st)) in
    MAP_EVERY ASSUME_TAC (CONJUNCTS rest) THEN ASSUME_TAC bth THEN
    SUBGOAL_THEN (mk_binary "<" (lw,`2 EXP 64`)) ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (mk_binary "<" (mk_comb(`LENGTH:byte list->num`,out'),`2 EXP 64`))
      ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DAT_ADD_SUBSET_TAC sub THEN
    (if st = "B" then
       ASM_CASES_TAC (mk_binary "<=" (`5`,lw)) THENL
        [ALL_TAC;
         SUBGOAL_THEN (mk_binary "<" (lw,`5`)) ASSUME_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         ASM_CASES_TAC (mk_eq(inp',`[]:byte list`)) THENL
          [SUBGOAL_THEN (mk_eq(lw,`0`)) ASSUME_TAC THENL
            [REWRITE_TAC[LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[]; ALL_TAC];
           ASM_CASES_TAC (mk_comb(`snappy_refill_ok`,inp'))]]
     else
       SUBGOAL_THEN (mk_binary "<" (lw,`5`)) ASSUME_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
       ASM_CASES_TAC (mk_eq(inp',`[]:byte list`)) THENL
        [SUBGOAL_THEN (mk_eq(lw,`0`)) ASSUME_TAC THENL
          [REWRITE_TAC[LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[]; ALL_TAC];
         ASM_CASES_TAC (mk_comb(`snappy_refill_ok`,inp'))]));;

let dat_L_cands st = fun (asl,w) ->
  let sth = dat_find_fact
      `snappy_steps k (2 EXP 63) (rest,out) = SOME(a:byte list,b:byte list)`
      [`k:num`; `a:byte list`; `b:byte list`] asl in
  let inp',out' = dest_pair(rand(rand(concl sth))) in
  let lw = mk_comb(`LENGTH:byte list->num`,inp') in
  [1,[mk_binary "+" (`i:num`,mk_binary "-" (`LENGTH(rest:byte list)`,lw)); inp'; out'];
   2,[`i:num`; inp'; out']];;

let DAT_L_TAC st : tactic =
  DAT_SETUP_TAC st THEN
  DAT_REPLACE_TAC `X1` (mk_comb(mk_comb(`word_add:int64->int64->int64`,dat_ip st),
                                `word(LENGTH(rest:byte list)):int64`)) THEN
  let dbu i =
    (fun g -> DAT_CONTRACT_TAC DAT_EXEC SNAPPY_DBU_NO_X27_X28
       [`read events s`; dat_ip st; `rest:byte list`; `out:byte list`; `pc:num`;
        `read SP s`; `read X30 s`; `read X19 s`; `read X20 s`; `read X21 s`;
        `read X22 s`; `read X23 s`; `read X24 s`; `read X25 s`; `read X26 s`;
        `read X29 s`] [] !(dat_subs ()) ("s" ^ string_of_int i) g) THEN
    DAT_AFTER_DBU_TAC st, 1 in
  DAT_RUN_TAC ~calls:[`word(pc + 26528):int64`, dbu;
                      `word(pc + 18064):int64`, (fun i -> DAT_REFILL_TAC i, 1)]
    DAT_EXEC 1 [`word(pc + 27300):int64`]
    (fun g -> DAT_LEAF_TAC (dat_L_cands st g) g);;

(* ------------------------------------------------------------------------- *)
(* The segment from T: one tag of the slow path.                             *)
(* ------------------------------------------------------------------------- *)

let DAT_CLASS_SPLIT = prove
 (`!c:byte.
     (val c MOD 4 = 0 /\ val c DIV 4 < 60) \/
     (val c MOD 4 = 0 /\ ~(val c DIV 4 < 60) /\ val c DIV 4 < 64) \/
     (val c MOD 4 = 1 /\ val c DIV 4 < 64) \/
     (val c MOD 4 = 2 /\ val c DIV 4 < 64) \/
     (val c MOD 4 = 3 /\ val c DIV 4 < 64)`,
  GEN_TAC THEN MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let DAT_ZX32_AND3 = prove
 (`!c:byte. word_and (word_zx c:int32) (word 3) = word(val c MOD 4)`,
  DAT_BYTE_ENUM_TAC);;

let DAT_ZX32_USHR2 = prove
 (`!c:byte. word_ushr (word_zx c:int32) 2 = word(val c DIV 4)`,
  DAT_BYTE_ENUM_TAC);;

let DAT_BYTES32_LOW = prove
 (`!(a:int64) (l:byte list) k s.
     read (memory :> bytelist(a,LENGTH l)) s = l /\ 1 + k <= LENGTH l /\ k <= 4
     ==> val(read (memory :> bytes32 (word_add a (word 1))) s) MOD 2 EXP (8 * k) =
         num_of_bytelist(SUB_LIST(1,k) l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `a:int64`; `1`; `k:num`;
                 `LENGTH(l:byte list)`; `s:armstate`] READ_BYTELIST_SUB_LIST) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN
  STRIP_TAC THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN 4 k = k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[]);;

let dat_classes = ["LIT"; "LITLONG"; "C1"; "C2"; "C4"];;
let dat_only = ref ([]:string list);;

let dat_copy_tac = ref (fun (st:string) (t:int) -> (ALL_TAC:tactic));;

let dat_lit_tac = ref (fun (st:string) (b:bool) -> (ALL_TAC:tactic));;

let DAT_T_PREP_TAC st : tactic =
  TIMED_TAC "setup" (DAT_SETUP_TAC st) THEN
  SUBGOAL_THEN `~(rest:byte list = [])` ASSUME_TAC THENL
   [(if st = "B" then REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC
     else ASM_REWRITE_TAC[]); ALL_TAC] THEN
  (if st = "B" then ALL_TAC else
   SUBGOAL_THEN `1 <= LENGTH(rest:byte list)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; LENGTH_EQ_NIL]; ALL_TAC]) THEN
  SUBGOAL_THEN (subst [dat_ip st,`ip:int64`]
    `read (memory :> bytes8 (ip:int64)) s0 = EL 0 (rest:byte list)`) ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MESON[WORD_ADD_0] `x:int64 = word_add x (word 0)`] THEN
    MATCH_MP_TAC READ_MEMORY_BYTELIST_EL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; LENGTH_EQ_NIL] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`s0:armstate`; `pc:num`; `EL 0 (rest:byte list)`]
               SNAPPY_LMO_TABLE_ZX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
    ~select:(elf_slots_at [0x1fc98; 0x1fca0]) THEN
  ASSUME_TAC(REWRITE_RULE[DIMINDEX_8] (ISPEC `EL 0 (rest:byte list)` VAL_BOUND));;

(* The tactic of one class, after DAT_T_PREP_TAC and the class facts. *)

let DAT_CLASS_TAC st name : tactic = fun g ->
  (if !dat_verbose then Printf.printf "CLASS %s\n%!" name);
  TIMED_TAC ("class." ^ st ^ "." ^ name)
   (if name = "LIT" then !dat_lit_tac st false else
    if String.length name >= 7 && String.sub name 0 7 = "LITLONG" then !dat_lit_tac st true else
    if name = "C1" || name = "C2" || name = "C4" then
      let t = if name = "C1" then 1 else if name = "C2" then 2 else 3 in
      !dat_copy_tac st t
    else failwith ("DAT_CLASS_TAC: " ^ name)) g;;

let DAT_T_TAC st : tactic =
  DAT_T_PREP_TAC st THEN
  MP_TAC(ISPEC `EL 0 (rest:byte list)` DAT_CLASS_SPLIT) THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) ORELSE
         DISCH_THEN STRIP_ASSUME_TAC) THENL
  (map (fun name ->
    if !dat_only <> [] && not(mem name !dat_only) then ALL_TAC else
    DAT_CLASS_TAC st name) dat_classes);;

(* A segment T restricted to one class: the class (a disjunct of            *)
(* DAT_CLASS_SPLIT for the tag byte EL 0 rest) as an antecedent.            *)

(* LITLONG6x: the long literal with the header width x - 59 (x = 60..63). *)

let dat_class_conds =
  let c = `EL 0 (rest:byte list)` in
  let ds = disjuncts(snd(dest_forall(concl DAT_CLASS_SPLIT))) in
  let cs = zip dat_classes (map (fun d -> subst [c,`c:byte`] d) ds) in
  cs @ map (fun x -> "LITLONG" ^ string_of_int x,
                     mk_conj(assoc "LITLONG" cs,
                             subst [mk_small_numeral x,`x:num`]
                               `val(EL 0 (rest:byte list)) DIV 4 = x`))
           [60;61;62;63];;

(* The split of the tag byte by classes (names), as a theorem for          *)
(* DAT_T_FROM_CLASSES_TAC.                                                  *)

let dat_class_split names =
  let tm = list_mk_disj(map (fun n -> assoc n dat_class_conds) names) in
  prove(tm, MP_TAC(ISPEC `EL 0 (rest:byte list)` VAL_BOUND) THEN
            REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let dat_class_stmt (pre:string) (nexts:(string*string) list) name =
  let stmt = dat_seg_stmt pre nexts in
  let vs,bod = strip_forall stmt in
  list_mk_forall(vs,mk_imp(assoc name dat_class_conds,bod));;

let DAT_T_CLASS_TAC st name : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun cth -> DAT_T_PREP_TAC st THEN STRIP_ASSUME_TAC cth) THEN
  DAT_CLASS_TAC st name;;

(* The segment from its classes (the theorems of dat_class_stmt). *)

let DAT_T_FROM_CLASSES_TAC (split:thm) (ths:thm list) : tactic =
  REPEAT GEN_TAC THEN
  MP_TAC split THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  FIRST(map (fun th -> MATCH_MP_TAC th THEN REPEAT CONJ_TAC THEN
                       FIRST_ASSUM ACCEPT_TAC) ths);;

(* ------------------------------------------------------------------------- *)
(* The tag at the head of rest, in terms of rest.                            *)
(* ------------------------------------------------------------------------- *)

let DAT_SUB_LIST_TL = prove
 (`!(l:byte list) j n. ~(l = []) ==> SUB_LIST(j,n) (TL l) = SUB_LIST(j + 1,n) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; TL] THEN
  REWRITE_TAC[GSYM ADD1; SUB_LIST_CLAUSES]);;

let DAT_TL_SUB_LIST = prove
 (`!(l:byte list). ~(l = []) ==> TL l = SUB_LIST(1,LENGTH l - 1) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; TL; LENGTH] THEN
  REWRITE_TAC[ONE; SUB_LIST_CLAUSES; SUC_SUB1; SUB_LIST_LENGTH]);;

let DAT_TAG_STEP_REST = prove
 (`!m (rest:byte list) out.
     ~(rest = [])
     ==> snappy_tag_step m rest out =
         snappy_tag_step m (CONS (EL 0 rest) (TL rest)) out`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EL; HD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CONS_HD_TL THEN
  ASM_REWRITE_TAC[]);;

let DAT_TAG_C1 = prove
 (`!m (rest:byte list) out.
     ~(rest = []) /\ val(EL 0 rest) MOD 4 = 1 /\ 2 <= LENGTH rest
     ==> snappy_tag_step m rest out =
         snappy_copy_tag m (256 * (val(EL 0 rest) DIV 4 DIV 8) + val(EL 1 rest))
           (val(EL 0 rest) DIV 4 MOD 8 + 4) (SUB_LIST(2,LENGTH rest - 2) rest) out`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DAT_TAG_STEP_REST] THEN
  MP_TAC(SPECL [`m:num`; `EL 0 (rest:byte list)`; `TL(rest:byte list)`; `out:byte list`]
    SNAPPY_TAG_STEP_COPY1) THEN
  ASM_SIMP_TAC[LENGTH_TL] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EL; ONE] THEN
  SUBGOAL_THEN `TL(TL(rest:byte list)) = SUB_LIST(2,LENGTH rest - 2) rest` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(TL(rest:byte list) = [])` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_SIMP_TAC[LENGTH_TL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[DAT_TL_SUB_LIST; DAT_SUB_LIST_TL; LENGTH_TL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC;
    REFL_TAC]);;

let DAT_TAG_CK = prove
 (`!m (rest:byte list) out k.
     ~(rest = []) /\
     ((val(EL 0 rest) MOD 4 = 2 /\ k = 2) \/ (val(EL 0 rest) MOD 4 = 3 /\ k = 4)) /\
     k + 1 <= LENGTH rest
     ==> snappy_tag_step m rest out =
         snappy_copy_tag m (num_of_bytelist(SUB_LIST(1,k) rest))
           (val(EL 0 rest) DIV 4 + 1) (SUB_LIST(k + 1,LENGTH rest - (k + 1)) rest) out`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[DAT_TAG_STEP_REST] THENL
   [MP_TAC(SPECL [`m:num`; `EL 0 (rest:byte list)`; `TL(rest:byte list)`; `out:byte list`]
      SNAPPY_TAG_STEP_COPY2);
    MP_TAC(SPECL [`m:num`; `EL 0 (rest:byte list)`; `TL(rest:byte list)`; `out:byte list`]
      SNAPPY_TAG_STEP_COPY4)] THEN
  ASM_SIMP_TAC[LENGTH_TL] THEN (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  ASM_SIMP_TAC[DAT_SUB_LIST_TL; LENGTH_TL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `(n - 1) - 2 = n - 3 /\ (n - 1) - 4 = n - 5`]);;

(* Masks of the 32-bit word at ip + 1.                                        *)

let DAT_WORD_AND_MASK = prove
 (`!(w:int32) k. word_and w (word(2 EXP k - 1)) = word(val w MOD 2 EXP k)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  MP_TAC(ISPEC `w:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  DISCH_TAC THEN MATCH_MP_TAC(GSYM MOD_LT) THEN
  TRANS_TAC LET_TRANS `val(w:int32)` THEN ASM_REWRITE_TAC[MOD_LE]);;

let DAT_NUM_OF_BYTELIST_1 = prove
 (`!(l:byte list). 2 <= LENGTH l ==> num_of_bytelist(SUB_LIST(1,1) l) = val(EL 1 l)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:byte list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(2 <= 0)`] THEN
  STRUCT_CASES_TAC(ISPEC `t:byte list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(2 <= SUC 0)`] THEN
  REWRITE_TAC[ONE; SUB_LIST_CLAUSES; EL; HD; TL; num_of_bytelist] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A read goal from a fact of a component equal up to the address and the   *)
(* length, the values equal up to the LENGTH equations among the facts.      *)
(* ------------------------------------------------------------------------- *)

let dat_len_eqs asl =
  mapfilter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),x)),_) when is_var x -> th
    | _ -> fail()) asl;;

let dat_num_eq asl l r =
  if l = r then REFL l else
  let facts = dat_facts asl in
  TAC_PROOF(([],mk_eq(l,r)),
    REWRITE_TAC(dat_len_eqs asl) THEN
    MAP_EVERY MP_TAC (dat_num_facts facts) THEN ARITH_TAC);;

let dat_val_eq asl l r =
  if l = r then REFL l else
  try WORD_RULE(mk_eq(l,r)) with Failure _ ->
  try dat_word_eq asl l r with Failure _ ->
  let tm = mk_eq(l,r) in
  TAC_PROOF((dat_state_free asl,tm),
    REWRITE_TAC(dat_len_eqs asl) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    (CONV_TAC WORD_RULE ORELSE
     (REPEAT AP_TERM_TAC THEN ASM_ARITH_TAC) ORELSE
     ASM_REWRITE_TAC[]));;

let rec dat_comp_eq asl c c' =
  if c = c' then REFL c else
  match c,c' with
    Comb(Comb(Const(":>",_) as cop,m),Comb(k,a)),
    Comb(Comb(Const(":>",_),m'),Comb(k',a')) when m = m' ->
      let eqk = if k = k' then REFL k else failwith "dat_comp_eq" in
      let eqa = match a,a' with
          Comb(Comb(Const(",",_),x),n),Comb(Comb(Const(",",_),x'),n') ->
            let ex = dat_val_eq asl x x' and en = dat_num_eq asl n n' in
            MK_COMB(AP_TERM (rator(rator a)) ex,en)
        | _ -> dat_val_eq asl a a' in
      AP_TERM (mk_comb(cop,m)) (MK_COMB(eqk,eqa))
  | _ -> failwith "dat_comp_eq";;

let DAT_READ2_TAC : tactic = fun (asl,w) ->
  let lw,v = dest_eq w in
  let rc,s = dest_comb lw in
  let rd,c = dest_comb rc in
  let cands = filter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s')),_) ->
        s' = s && (match c,c' with
          Comb(Comb(Const(":>",_),_),Comb(k,_)),Comb(Comb(Const(":>",_),_),Comb(k',_)) -> k = k'
        | _ -> c = c')
    | _ -> false) asl in
  let try1 (_,th) =
    let c' = rand(rator(lhs(concl th))) in
    let ceq = dat_comp_eq asl c c' in
    let th1 = TRANS (AP_THM (AP_TERM rd ceq) s) th in
    let veq = if rhs(concl th1) = v then REFL v
              else try dat_val_eq asl (rhs(concl th1)) v
                   with Failure _ -> dat_num_eq asl (rhs(concl th1)) v in
    TRANS th1 veq in
  ACCEPT_TAC (tryfind try1 cands) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* 32-bit forms of the table entries (kLengthMinusOffset), by cases.         *)
(* ------------------------------------------------------------------------- *)

let DAT_LEN32_C1 = prove
 (`!x. x < 64
       ==> word_and (iword(&(x MOD 8 + 4) - &256 * &(x DIV 8)):int32) (word 255) =
           word(x MOD 8 + 4) /\
           word_sub (word(x MOD 8 + 4)) (iword(&(x MOD 8 + 4) - &256 * &(x DIV 8)):int32) =
           word(256 * (x DIV 8)) /\
           word_sx (word(x MOD 8 + 4):int32):int64 = word(x MOD 8 + 4)`,
  DAT_X_CASES_TAC 64);;

let DAT_LEN32_C2 = prove
 (`!x. x < 64
       ==> word_and (iword(&(x + 1)):int32) (word 255) = word(x + 1) /\
           word_sub (word(x + 1)) (iword(&(x + 1)):int32) = word 0 /\
           word_sx (word(x + 1):int32):int64 = word(x + 1) /\
           word_zx (word(x + 1):int32):int64 = word(x + 1) /\
           word_and (word(x + 1):int64) (word 255) = word(x + 1)`,
  DAT_X_CASES_TAC 64);;

let DAT_SX_IWORD32 = prove
 (`!i. --(&32768) <= i /\ i < &32768 ==> word_sx(iword i:int16):int32 = iword i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_sx] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC IVAL_IWORD_16 THEN ASM_REWRITE_TAC[]);;

let DAT_ZX_32_64 = prove
 (`!n. n < 2 EXP 32 ==> word_zx(word n:int32):int64 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `m < 2 EXP 32 ==> m < 2 EXP 64`]);;

(* ------------------------------------------------------------------------- *)
(* The copy classes (C1, C2, C4).                                            *)
(* ------------------------------------------------------------------------- *)

let dat_c = `EL 0 (rest:byte list)`;;
let dat_x = `val(EL 0 (rest:byte list)) DIV 4`;;

let dat_tm s = subst [dat_x,`x:num`] (parse_term s);;

let dat_add_fact (tm:term) (tac:tactic) : tactic =
  SUBGOAL_THEN tm ASSUME_TAC THENL [tac; ALL_TAC];;

let dat_copy_rws = par_local_ref (fun () -> ([]:thm list));;

(* The facts after a tag that consumed kk bytes (a numeral term) and that   *)
(* appends to out the list o2: the abbreviations rest2, out2, their lengths, *)
(* the bytes of rest2 at ip + kk, the model.                                 *)

let DAT_STEP_FACTS_TAC st (kk:term) (o2:term) (sth:thm) : tactic =
  fun (asl,w) ->
    let ip = dat_ip st in
    let r2 = subst [kk,`k:num`] `SUB_LIST(k,LENGTH(rest:byte list) - k) rest` in
    (ABBREV_TAC (mk_eq(`rest2:byte list`,r2)) THEN
     ABBREV_TAC (mk_eq(`out2:byte list`,o2)) THEN
     W(fun (asl,w) ->
       let sth' = snd(find (fun (_,th) -> concl th = subst [`rest2:byte list`,r2;
                     `out2:byte list`,o2] (concl sth) || 
                     (is_eq(concl th) && lhand(concl th) = lhand(concl sth))) asl) in
       let model = snd(find (fun (_,th) -> is_iff(concl th) &&
         rhs(concl th) = `snappy_decode_tags m rest out = NONE`) asl) in
       let iff' = TRANS model (AP_THM (AP_TERM `(=):(byte list)option->(byte list)option->bool`
                    (MATCH_MP SNAPPY_DECODE_TAGS_STEP sth')) `NONE:(byte list)option`) in
       let ratio' = MATCH_MP SNAPPY_TAG_STEP_RATIO sth' in
       ASSUME_TAC iff' THEN ASSUME_TAC ratio') THEN
     dat_add_fact (subst [kk,`k:num`] `LENGTH(rest2:byte list) = LENGTH(rest:byte list) - k`)
       (EXPAND_TAC "rest2" THEN REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC) THEN
     dat_add_fact (subst [ip,`ip:int64`; kk,`k:num`]
        `read (memory :> bytelist(word_add ip (word k),LENGTH(rest2:byte list))) s0 = rest2`)
       (EXPAND_TAC "rest2" THEN REWRITE_TAC[LENGTH_SUB_LIST] THEN
        REWRITE_TAC[ARITH_RULE `MIN (n - k) (n - k) = n - k`] THEN
        MATCH_MP_TAC READ_BYTELIST_SUFFIX THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC))
    (asl,w);;

let dat_w32_addr st = if st = "B" then `word_add (q:int64) (word (i + 1))`
                      else `word_add (d:int64) (word 42)`;;

let dat_find_eq lhs_tm asl =
  snd(find (fun (_,th) -> is_eq(concl th) && lhand(concl th) = lhs_tm) asl);;

(* Cases for a tag that consumed kk bytes: B: no refill (5 <= LENGTH rest2), *)
(* or EMPTY (rest2 = []), or WINDOW with refill_ok rest2 or not; S: the last  *)
(* two.                                                                      *)

(* Close a case whose LENGTH facts are contradictory (rest2 = [] after a tag  *)
(* of a few bytes in B, where 5 <= LENGTH rest).                             *)

let DAT_LEN_KILL_TAC : tactic = fun (asl,w) ->
  let isnum t = type_of t = `:num` in
  let ok c =
    c = `1 <= len` ||
    can (find_term (fun t -> match t with Const("LENGTH",_) -> true | _ -> false)) c &&
    not(can (find_term (fun t -> type_of t = `:int`)) c) &&
    (match c with
       Comb(Comb(Const(("<="|"<"),_),_),_) -> true
     | Comb(Comb(Const("=",_),l),_) -> isnum l
     | Comb(Const("~",_),Comb(Comb(Const(("<="|"<"),_),_),_)) -> true
     | Comb(Const("~",_),Comb(Comb(Const("=",_),l),_)) -> isnum l
     | _ -> false) in
  let ths = filter (fun th -> ok(concl th)) (map snd (dat_state_free asl)) in
  (MATCH_MP_TAC(TAUT `F ==> p`) THEN MAP_EVERY MP_TAC ths THEN ARITH_TAC) (asl,w);;

let DAT_LEN_KILL_TAC = TIMED_TAC "lenkill" DAT_LEN_KILL_TAC;;

let DAT_POS_CASES_TAC st : tactic =
  let win =
    ASM_CASES_TAC `rest2:byte list = []` THENL
     [SUBGOAL_THEN `LENGTH(rest2:byte list) = 0` ASSUME_TAC THENL
       [REWRITE_TAC[LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[]; ALL_TAC];
      SUBGOAL_THEN `~(LENGTH(rest2:byte list) = 0)` ASSUME_TAC THENL
       [REWRITE_TAC[LENGTH_EQ_NIL] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `snappy_refill_ok rest2`] in
  if st = "B" then
    ASM_CASES_TAC `5 <= LENGTH(rest2:byte list)` THENL
     [ALL_TAC;
      SUBGOAL_THEN `LENGTH(rest2:byte list) < 5` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN win]
  else
    SUBGOAL_THEN `LENGTH(rest2:byte list) < 5` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN win;;

let dat_ck_disj t tf =
  let d1 = `val(EL 0 (rest:byte list)) MOD 4 = 2 /\ 4 = 2`
  and d2 = `val(EL 0 (rest:byte list)) MOD 4 = 3 /\ 2 = 4` in
  if t = 2 then DISJ1 (CONJ tf (REFL `2`)) d2 else DISJ2 d1 (CONJ tf (REFL `4`));;

let DAT_COPY_SETUP_TAC st (t:int) : tactic =
  let k = if t = 1 then 1 else if t = 2 then 2 else 4 in
  let kn = mk_small_numeral k and k1 = mk_small_numeral (k + 1) in
  let ip = dat_ip st in
  fun (asl,w as g) ->
    let tf = dat_find_eq `val(EL 0 (rest:byte list)) MOD 4` asl in
    let x64 = snd(find (fun (_,th) -> concl th = dat_tm "x < 64") asl) in
    (* the bytes of the tag are there *)
    (dat_add_fact (subst [k1,`k:num`] `k <= LENGTH(rest:byte list)`)
      (if st = "B" then ASM_ARITH_TAC else
       FIRST_ASSUM(fun th -> if concl th = `snappy_refill_ok rest` then
         MP_TAC th else NO_TAC) THEN
       REWRITE_TAC[snappy_refill_ok; snappy_tag_needed; GSYM(CONJUNCT1 EL)] THEN
       ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) THEN
     TRY DAT_LEN_KILL_TAC THEN
     (* the model of the tag *)
     W(fun (asl,w) ->
       let kth = snd(find (fun (_,th) -> concl th = subst [k1,`k:num`]
                   `k <= LENGTH(rest:byte list)`) asl) in
       let ne = snd(find (fun (_,th) -> concl th = `~(rest:byte list = [])`) asl) in
       let tagth =
         if t = 1 then MP (SPECL [`m:num`; `rest:byte list`; `out:byte list`] DAT_TAG_C1)
                          (CONJ ne (CONJ tf kth))
         else
           let kt = mk_binary "<=" (mk_binary "+" (kn,`1`),`LENGTH(rest:byte list)`) in
           let kth' = EQ_MP (SYM(LAND_CONV NUM_ADD_CONV kt)) kth in
           CONV_RULE (DEPTH_CONV NUM_ADD_CONV)
            (MP (SPECL [`m:num`; `rest:byte list`; `out:byte list`; kn] DAT_TAG_CK)
                 (CONJ ne (CONJ (dat_ck_disj t tf) kth'))) in
       ASSUME_TAC tagth) THEN
     (* the 32-bit word at ip + 1 *)
     W(fun (asl,w) ->
       let a = dat_w32_addr st in
       let ex = prove(mk_exists(`w32:int32`,
         mk_eq(subst [a,`a:int64`] `read (memory :> bytes32 a) s0`,`w32:int32`)),
         MESON_TAC[]) in
       X_CHOOSE_TAC `w32:int32` ex) THEN
     dat_add_fact (subst [kn,`k:num`]
         `val(w32:int32) MOD 2 EXP (8 * k) = num_of_bytelist(SUB_LIST(1,k) rest)`)
       (FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `w32:int32`
                              then SUBST1_TAC(SYM th) else NO_TAC) THEN
        SUBST1_TAC(WORD_RULE(mk_eq(dat_w32_addr st,
          mk_comb(mk_comb(`word_add:int64->int64->int64`,ip),`word 1:int64`)))) THEN
        MATCH_MP_TAC DAT_BYTES32_LOW THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC) THEN
     ALL_TAC) g;;

(* The rewrites for the run of a copy class, after the setup, with off       *)
(* abbreviated; and the case splits.                                         *)

let dat_mod_rule th = CONV_RULE NUM_REDUCE_CONV th;;

let DAT_COPY_TAC st (t:int) : tactic =
  let k = if t = 1 then 1 else if t = 2 then 2 else 4 in
  let k1 = mk_small_numeral (k + 1) in
  let len = if t = 1 then dat_tm "x MOD 8 + 4" else dat_tm "x + 1" in
  DAT_COPY_SETUP_TAC st t THEN
  fun (asl,w as g) ->
    let tf = dat_find_eq `val(EL 0 (rest:byte list)) MOD 4` asl in
    let x64 = snd(find (fun (_,th) -> concl th = dat_tm "x < 64") asl) in
    let mk = dat_mod_rule(snd(find (fun (_,th) -> is_eq(concl th) &&
               can (find_term ((=) `w32:int32`)) (lhand(concl th)) &&
               can (find_term ((=) `MOD`)) (lhand(concl th))) asl)) in
    let and3 = REWRITE_RULE[tf] (SPEC dat_c DAT_ZX32_AND3) in
    let facts = dat_facts asl in
    let arith tm = TAC_PROOF(([],tm), MAP_EVERY MP_TAC facts THEN ARITH_TAC) in
    let offx, mrw =
      if t = 1 then
        let r2 = MP (SPEC `rest:byte list` DAT_NUM_OF_BYTELIST_1)
                    (arith `2 <= LENGTH(rest:byte list)`) in
        let m8 = dat_mod_rule (SPECL [`w32:int32`; `8`] DAT_WORD_AND_MASK) in
        dat_tm "256 * (x DIV 8) + val(EL 1 (rest:byte list))",
        [REWRITE_RULE[mk; r2] m8]
      else if t = 2 then
        let m16 = dat_mod_rule (SPECL [`w32:int32`; `16`] DAT_WORD_AND_MASK) in
        `num_of_bytelist(SUB_LIST(1,2) (rest:byte list))`, [REWRITE_RULE[mk] m16]
      else
        let vlt = CONV_RULE NUM_REDUCE_CONV (MATCH_MP MOD_LT (REWRITE_RULE[DIMINDEX_32]
                    (ISPEC `w32:int32` VAL_BOUND))) in
        let zx = prove(`word_zx (w32:int32):int64 = word(val w32)`,
                       REWRITE_TAC[word_zx]) in
        `num_of_bytelist(SUB_LIST(1,4) (rest:byte list))`,
        [REWRITE_RULE[REWRITE_RULE[vlt] mk] zx] in
    let lmo_rws =
      if t = 3 then [] else
      let I = if t = 1 then dat_tm "&(x MOD 8 + 4) - &256 * &(x DIV 8):int"
              else dat_tm "&(x + 1):int" in
      let lmoeq = TAC_PROOF(([],mk_eq(`snappy_lmo (EL 0 (rest:byte list))`,I)),
         REWRITE_TAC[snappy_lmo; tf] THEN CONV_TAC NUM_REDUCE_CONV) in
      let iarith tm = TAC_PROOF(([],tm), INT_FACTS_ARITH_TAC
         (arith (dat_tm "x DIV 8 < 8 /\\ x MOD 8 < 8") :: x64 :: facts)) in
      let sxth = let th = ISPEC I DAT_SX_IWORD32 in MP th (iarith (lhand(concl th))) in
      [lmoeq; sxth] in
    let lenths = CONJUNCTS(MP (SPEC dat_x (if t = 1 then DAT_LEN32_C1 else DAT_LEN32_C2)) x64) in
    let offlt =
      if t = 1 then
        TAC_PROOF(([],mk_binary "<" (offx,`2 EXP 32`)),
          MP_TAC(REWRITE_RULE[DIMINDEX_8] (ISPEC `EL 1 (rest:byte list)` VAL_BOUND)) THEN
          MP_TAC x64 THEN ARITH_TAC)
      else
        TAC_PROOF(([],mk_binary "<" (offx,`2 EXP 32`)),
          REWRITE_TAC[GSYM mk] THEN
          W(fun (_,w) -> MP_TAC(SPECL [lhand(lhand w); rand(lhand w)] MOD_LT_EQ)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) in
    ((FIRST_X_ASSUM(fun th -> if can (find_term ((=) `snappy_lmo`)) (concl th) &&
                                lmo_rws <> []
                             then ASSUME_TAC(REWRITE_RULE[hd lmo_rws] th) else NO_TAC) ORELSE ALL_TAC) THEN
    ASSUME_TAC offlt THEN
    ABBREV_TAC (mk_eq(`off:num`,offx)) THEN
    ABBREV_TAC (mk_eq(`len:num`,len)) THEN
    W(fun (asl,w) ->
      let ab = map (fun v -> SYM(dat_find_eq v asl)) [] in
      let offeq = snd(find (fun (_,th) -> concl th = mk_eq(offx,`off:num`)) asl) in
      let leneq = snd(find (fun (_,th) -> concl th = mk_eq(len,`len:num`)) asl) in
      let fixr th = REWRITE_RULE[offeq; leneq] th in
      let offadd = if t = 1 then
          fixr(prove(mk_eq(subst [dat_x,`x:num`]
            `word_add (word(val(EL 1 (rest:byte list)))) (word(256 * (x DIV 8))):int32`,
            mk_comb(`word:num->int32`,offx)),
            REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC))
        else let wo = mk_comb(`word:num->int32`,offx) in
             fixr(CONJ (ISPEC wo (CONJUNCT1 WORD_ADD_0)) (ISPEC wo (CONJUNCT2 WORD_ADD_0))) in
      let offlt' = snd(find (fun (_,th) -> concl th = `off < 2 EXP 32`) asl) in
      let zx = MP (SPEC `off:num` DAT_ZX_32_64) offlt' in
      let rws = [and3; DAT_ZX32_USHR2; offadd; zx] @ map fixr (mrw @ lmo_rws @ lenths) @
                (if t = 3 then
                   let vlt = CONV_RULE NUM_REDUCE_CONV (MATCH_MP MOD_LT (REWRITE_RULE[DIMINDEX_32]
                               (ISPEC `w32:int32` VAL_BOUND))) in
                   [fixr(INST_TYPE [`:32`,`:N`] (ISPECL [dat_x; `1`] (GSYM WORD_ADD)));
                    fixr(REWRITE_RULE[vlt] mk)] else []) in
      (if !dat_verbose then Printf.printf "COPY rewrites: %d\n%!" (length rws));
      dat_copy_rws () := rws;
      ALL_TAC)) g;;

(* State-free equations among the assumptions with a variable on the left  *)
(* (off = 0, the cases), for the rewrites of a run.                          *)

let dat_state_eqs asl =
  mapfilter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),l),Comb(Const("NUMERAL",_),_)) when is_var l -> th
    | _ -> fail()) asl;;

(* val of the length len in its word forms (32 and 64 bits, zero-extended),  *)
(* given len < 2 EXP 32 from the facts: for the PC conditions on len.        *)

let DAT_VAL_LEN_FORMS = prove
 (`!n. n < 2 EXP 32
       ==> val(word n:int32) = n /\ val(word n:int64) = n /\
           val(word_zx(word n:int32):int64) = n /\
           val(word_zx(word n:int64):int32) = n /\
           val(word_zx(word n:int64):int64) = n /\
           val(word_zx(word n:int32):int32) = n`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n MOD 2 EXP 32 = n /\ n MOD 2 EXP 64 = n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  ASM_REWRITE_TAC[]);;

let DAT_ZX_LEN_FORMS = prove
 (`!n. n < 2 EXP 32
       ==> word_zx(word n:int64):int32 = word n /\
           word_zx(word n:int32):int64 = word n /\
           word_zx(word n:int64):int64 = word n /\
           word_zx(word n:int32):int32 = word n`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n MOD 2 EXP 32 = n /\ n MOD 2 EXP 64 = n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  ASM_REWRITE_TAC[]);;

let dat_len_forms asl =
  if not(exists (fun (_,th) -> can (find_term ((=) `len:num`)) (concl th)) asl) then [] else
  try let facts = dat_num_facts (dat_facts asl) in
      let b = TAC_PROOF(([],`len < 2 EXP 32`), MAP_EVERY MP_TAC facts THEN ARITH_TAC) in
      CONJUNCTS(MP (SPEC `len:num` DAT_VAL_LEN_FORMS) b) @
      CONJUNCTS(MP (SPEC `len:num` DAT_ZX_LEN_FORMS) b)
  with Failure _ -> [];;

(* The read facts of the current state rewritten by the rewrites of the     *)
(* class with numerals reduced (the address ip_ after a long literal, which  *)
(* the rewrites of the run left with the tag byte and the mask unreduced).   *)

let DAT_NORM_READS_TAC (rws:thm list) : tactic = fun (asl,w) ->
  let s = rand w in
  let conv = REWRITE_CONV rws THENC WORD_REDUCE_CONV THENC REWRITE_CONV rws THENC
             WORD_REDUCE_CONV THENC REWRITE_CONV rws in
  let fix (_,th) = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s1)),v)
        when s1 = s && (match c with Const(("PC"|"events"),_) -> false | _ -> true) ->
        let eq = conv v in
        if rand(concl eq) = v then fail() else
        (concl th, CONV_RULE(RAND_CONV(K eq)) th)
    | _ -> fail() in
  let fixes = mapfilter fix asl in
  MAP_EVERY (fun (oc,nth) -> UNDISCH_THEN oc (K(ASSUME_TAC nth))) fixes (asl,w);;

(* The 4-byte header: the load of w32 is zero-extended to 64 bits and        *)
(* rewritten to word nb (zxw); the 32-bit mask then meets word_zx (word nb).  *)

let DAT_ZX_64_32_WORD = prove
 (`!n. word_zx(word n:int64):int32 = word n`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let DAT_AND32_FULL = prove
 (`!x:int32. word_and x (word 4294967295) = x`,
  CONV_TAC WORD_BLAST);;

let DAT_AND64_32 = prove
 (`!n. n < 2 EXP 32 ==> word_and (word n:int64) (word 4294967295) = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `4294967295 = 2 EXP 32 - 1` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 2 EXP 32 ==> n < 2 EXP 64`]);;

let dat_run st k1 rws0 : tactic = fun g ->
  let rws = rws0 @ dat_len_forms (fst g) in
  DAT_RUN_TAC ~rws ~rewrites:rws
    ~calls:[`word(pc + 18064):int64`, (fun i -> TRY(DAT_NORM_READS_TAC rws) THEN DAT_REFILL_TAC i, 1)]
    DAT_EXEC 1 [`word(pc + 27264):int64`]
    (TRY(DAT_NORM_READS_TAC rws) THEN
     DAT_LEAF_TAC [1,[mk_binary "+" (`i:num`,k1); `rest2:byte list`; `out2:byte list`];
                   2,[`0`; `rest2:byte list`; `out2:byte list`]]) g;;

let DAT_VAL_SUB1 = prove
 (`!n. ~(n = 0) /\ n < 2 EXP 64 ==> val(word_sub (word n) (word 1):int64) = n - 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word n) (word 1):int64 = word(n - 1)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `~(n = 0) ==> 1 <= n`];
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

(* The offset test of AppendFromSelf (produced <= off - 1) as arithmetic.    *)

let dat_off_rws asl =
  try let lt = snd(find (fun (_,th) -> concl th = `off < 2 EXP 32`) asl) in
      let lt64 = MP (ARITH_RULE `off < 2 EXP 32 ==> off < 2 EXP 64`) lt in
      (try let nz = snd(find (fun (_,th) -> concl th = `~(off = 0)`) asl) in
           [MP (SPEC `off:num` DAT_VAL_SUB1) (CONJ nz lt64)]
       with Failure _ -> []) @
      CONJUNCTS(MP (SPEC `off:num` DAT_VAL_LEN_FORMS) lt) @
      CONJUNCTS(MP (SPEC `off:num` DAT_ZX_LEN_FORMS) lt)
  with Failure _ -> [];;

let DAT_COPY_CASES_TAC st (t:int) : tactic =
  let k = if t = 1 then 1 else if t = 2 then 2 else 4 in
  let k1 = mk_small_numeral (k + 1) in
  let r2 = subst [k1,`k:num`] `SUB_LIST(k,LENGTH(rest:byte list) - k) rest` in
  let fail_tac =
    W(fun (asl,w) ->
      let tagth = snd(find (fun (_,th) -> is_eq(concl th) &&
                    lhand(concl th) = `snappy_tag_step m rest out`) asl) in
      let nth = TAC_PROOF((dat_state_free asl,
                  `snappy_decode_tags m rest out = NONE`),
        MATCH_MP_TAC SNAPPY_DECODE_TAGS_FAIL THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[tagth; snappy_copy_tag] THEN ASM_REWRITE_TAC[] THEN
        TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC)) in
      ASSUME_TAC nth) THEN
    (fun g -> dat_run st k1 (!(dat_copy_rws ()) @ dat_state_eqs (fst g) @ dat_off_rws (fst g)) g) in
  let ok_tac =
    W(fun (asl,w) ->
      let tagth = snd(find (fun (_,th) -> is_eq(concl th) &&
                    lhand(concl th) = `snappy_tag_step m rest out`) asl) in
      let sth = TAC_PROOF((dat_state_free asl,
         mk_eq(`snappy_tag_step m rest out`,
               mk_comb(`SOME:byte list#byte list->(byte list#byte list)option`,
                       mk_pair(r2,`snappy_copy off len out`)))),
        REWRITE_TAC[tagth; snappy_copy_tag] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC) in
      ASSUME_TAC sth) THEN
    W(fun (asl,w) ->
      let sth = snd(find (fun (_,th) -> is_eq(concl th) &&
                  lhand(concl th) = `snappy_tag_step m rest out` &&
                  can (find_term ((=) `SOME:byte list#byte list->(byte list#byte list)option`)) (concl th)) asl) in
      DAT_STEP_FACTS_TAC st k1 `snappy_copy off len out` sth) THEN
    dat_add_fact `LENGTH(out2:byte list) = LENGTH(out:byte list) + len`
      (EXPAND_TAC "out2" THEN REWRITE_TAC[LENGTH_SNAPPY_COPY]) THEN
    dat_add_fact `LENGTH(out2:byte list) < 2 EXP 64` ASM_ARITH_TAC THEN
    dat_add_fact `word_add (word(LENGTH(out:byte list))) (word len):int64 = word(LENGTH(out2:byte list))`
      (ASM_REWRITE_TAC[WORD_ADD]) THEN
    DAT_POS_CASES_TAC st THEN TRY DAT_LEN_KILL_TAC THEN
    (fun g -> dat_run st k1 (!(dat_copy_rws ()) @ dat_state_eqs (fst g) @ dat_off_rws (fst g)) g) in
  ASM_CASES_TAC `off = 0` THENL
   [fail_tac;
    ASM_CASES_TAC `off <= LENGTH(out:byte list)` THENL
     [ASM_CASES_TAC `LENGTH(out:byte list) + len <= m` THENL [ok_tac; fail_tac];
      fail_tac]];;


(* ------------------------------------------------------------------------- *)
(* The literal classes.                                                      *)
(* ------------------------------------------------------------------------- *)

let DAT_SUB_LIST_SUB_LIST1 = prove
 (`!(l:byte list) j n.
     ~(l = []) ==> SUB_LIST(j,n) (SUB_LIST(1,LENGTH l - 1) l) = SUB_LIST(j + 1,n) l`,
  SIMP_TAC[GSYM DAT_TL_SUB_LIST; DAT_SUB_LIST_TL]);;

let DAT_TAG_LIT = prove
 (`!m (rest:byte list) out.
     ~(rest = []) /\ val(EL 0 rest) MOD 4 = 0 /\ val(EL 0 rest) DIV 4 < 60
     ==> snappy_tag_step m rest out =
         snappy_literal m (val(EL 0 rest) DIV 4 + 1) (SUB_LIST(1,LENGTH rest - 1) rest) out`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DAT_TAG_STEP_REST] THEN
  ASM_SIMP_TAC[SNAPPY_TAG_STEP_LITERAL; DAT_TL_SUB_LIST]);;

let DAT_TAG_LITLONG = prove
 (`!m (rest:byte list) out.
     ~(rest = []) /\ val(EL 0 rest) MOD 4 = 0 /\ ~(val(EL 0 rest) DIV 4 < 60) /\
     val(EL 0 rest) DIV 4 - 58 <= LENGTH rest
     ==> snappy_tag_step m rest out =
         snappy_literal m
           (num_of_bytelist(SUB_LIST(1,val(EL 0 rest) DIV 4 - 59) rest) + 1)
           (SUB_LIST(val(EL 0 rest) DIV 4 - 58,
                     LENGTH rest - (val(EL 0 rest) DIV 4 - 58)) rest) out`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DAT_TAG_STEP_REST] THEN
  MP_TAC(SPECL [`m:num`; `EL 0 (rest:byte list)`; `TL(rest:byte list)`; `out:byte list`]
    SNAPPY_TAG_STEP_LONG_LITERAL) THEN
  ASM_SIMP_TAC[LENGTH_TL] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[DAT_SUB_LIST_TL; LENGTH_TL] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let DAT_SUB_LIST_SUB_LIST = prove
 (`!(l:byte list) a b c d.
     a + b <= d /\ c + d <= LENGTH l
     ==> SUB_LIST(a,b) (SUB_LIST(c,d) l) = SUB_LIST(a + c,b) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MIN] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < b` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[MIN] THEN REPEAT COND_CASES_TAC THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o lhand o snd) THEN
  ANTS_TAC THENL [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o rand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* The literal of len bytes from the bytes after h header bytes.             *)

let DAT_LITERAL_STEP = prove
 (`!m (rest:byte list) out h len.
     ~(rest = []) /\ 1 <= h /\ h + len <= LENGTH rest /\ LENGTH out + len <= m
     ==> snappy_literal m len (SUB_LIST(h,LENGTH rest - h) rest) out =
         SOME(SUB_LIST(h + len,LENGTH rest - (h + len)) rest,
              APPEND out (SUB_LIST(0,len) (SUB_LIST(h,LENGTH rest - h) rest)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[snappy_literal; LENGTH_SUB_LIST; ARITH_RULE `MIN (a:num) a = a`] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DAT_SUB_LIST_SUB_LIST o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let DAT_LITERAL_FAIL = prove
 (`!m (rest:byte list) out h len.
     ~(h + len <= LENGTH rest /\ LENGTH out + len <= m) /\ h <= LENGTH rest
     ==> snappy_literal m len (SUB_LIST(h,LENGTH rest - h) rest) out = NONE`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[snappy_literal; LENGTH_SUB_LIST; ARITH_RULE `MIN (a:num) a = a`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* A literal of len bytes after h tag bytes (h a numeral term): the cases.   *)
(* rws0: the rewrites of the class for the run.                              *)

let DAT_LIT_CASES_TAC st (h:term) (tagth:thm) (rws0:thm list) : tactic =
  let kk = mk_binary "+" (h,`len:num`) in
  let fail_tac =
    W(fun (asl,w) ->
      let nth = TAC_PROOF((dat_state_free asl,
                  `snappy_decode_tags m rest out = NONE`),
        MATCH_MP_TAC SNAPPY_DECODE_TAGS_FAIL THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[tagth] THEN MATCH_MP_TAC DAT_LITERAL_FAIL THEN
        ASM_ARITH_TAC) in
      ASSUME_TAC nth) THEN
    (fun g -> dat_run st kk (rws0 @ dat_state_eqs (fst g)) g) in
  let ok_tac =
    W(fun (asl,w) ->
      let sth = TAC_PROOF((dat_state_free asl,
         mk_eq(`snappy_tag_step m rest out`,
          rhs(snd(dest_imp(concl(SPECL [`m:num`; `rest:byte list`; `out:byte list`; h; `len:num`]
                     DAT_LITERAL_STEP)))))),
        REWRITE_TAC[tagth] THEN MATCH_MP_TAC DAT_LITERAL_STEP THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC) in
      ASSUME_TAC sth THEN
      DAT_STEP_FACTS_TAC st kk (rand(rand(rand(concl sth)))) sth) THEN
    dat_add_fact `LENGTH(out2:byte list) = LENGTH(out:byte list) + len`
      (EXPAND_TAC "out2" THEN REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST] THEN
       ASM_ARITH_TAC) THEN
    dat_add_fact `LENGTH(out2:byte list) < 2 EXP 64` ASM_ARITH_TAC THEN
    dat_add_fact `word_add (word(LENGTH(out:byte list))) (word len):int64 = word(LENGTH(out2:byte list))`
      (ASM_REWRITE_TAC[WORD_ADD]) THEN
    DAT_POS_CASES_TAC st THEN TRY DAT_LEN_KILL_TAC THEN
    (fun g -> dat_run st kk (rws0 @ dat_state_eqs (fst g)) g) in
  ASM_CASES_TAC (mk_binary "<=" (kk,`LENGTH(rest:byte list)`)) THENL
   [ASM_CASES_TAC `LENGTH(out:byte list) + len <= m` THENL [ok_tac; fail_tac];
    fail_tac];;

(* The test literal_length >= 61 of a short literal (len <= 60) is false,   *)
(* in the forms of the run (len zero-extended or not).                        *)

let DAT_LIT_SHORT_COND = prove
 (`!n (x:int64). n <= 60 /\ val x = n
       ==> ~(&n - &60:int = &(val(word_sub x (word 60))) /\
             ~(val(word_sub x (word 60)) = 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `n = 60` THENL
   [SUBGOAL_THEN `x:int64 = word 60` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0]];
    MATCH_MP_TAC(TAUT `~a ==> ~(a /\ b)`) THEN
    MATCH_MP_TAC(INT_ARITH `x < &0 /\ &0 <= y ==> ~(x:int = y)`) THEN
    REWRITE_TAC[INT_POS; INT_LT_SUB_RADD; INT_ADD_LID; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC]);;

let DAT_LIT_SHORT_COND32 = prove
 (`!n (x:int32). n <= 60 /\ val x = n
       ==> ~(&n - &60:int = &(val(word_sub x (word 60))) /\
             ~(val(word_sub x (word 60)) = 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `n = 60` THENL
   [SUBGOAL_THEN `x:int32 = word 60` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0]];
    MATCH_MP_TAC(TAUT `~a ==> ~(a /\ b)`) THEN
    MATCH_MP_TAC(INT_ARITH `x < &0 /\ &0 <= y ==> ~(x:int = y)`) THEN
    REWRITE_TAC[INT_POS; INT_LT_SUB_RADD; INT_ADD_LID; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC]);;

let dat_lit_short_rws (lenle:thm) =
  let forms = [`word_zx(word len:int32):int64`; `word_zx(word len:int64):int64`;
               `word len:int64`] in
  let vth = CONJUNCTS(MP (SPEC `len:num` DAT_VAL_LEN_FORMS)
                         (MP (ARITH_RULE `len <= 60 ==> len < 2 EXP 32`) lenle)) in
  let forms32 = [`word_zx(word len:int64):int32`; `word_zx(word len:int32):int32`;
                 `word len:int32`] in
  mapfilter (fun x ->
    let vx = find (fun th -> lhand(concl th) = mk_comb(`val:int64->num`,x)) vth in
    EQF_INTRO(MP (ISPECL [`len:num`; x] DAT_LIT_SHORT_COND) (CONJ lenle vx))) forms @
  mapfilter (fun x ->
    let vx = find (fun th -> lhand(concl th) = mk_comb(`val:int32->num`,x)) vth in
    EQF_INTRO(MP (ISPECL [`len:num`; x] DAT_LIT_SHORT_COND32) (CONJ lenle vx))) forms32;;

let DAT_LIT_TAC st : tactic = fun (asl,w as g) ->
  let tf = dat_find_eq `val(EL 0 (rest:byte list)) MOD 4` asl in
  let xb = snd(find (fun (_,th) -> concl th = dat_tm "x < 60") asl) in
  let ne = snd(find (fun (_,th) -> concl th = `~(rest:byte list = [])`) asl) in
  let tagth = MP (SPECL [`m:num`; `rest:byte list`; `out:byte list`] DAT_TAG_LIT)
                 (CONJ ne (CONJ tf xb)) in
  let and3 = REWRITE_RULE[tf] (SPEC dat_c DAT_ZX32_AND3) in
  let add1 = INST_TYPE [`:32`,`:N`] (ISPECL [dat_x; `1`] (GSYM WORD_ADD)) in
  let zx = MP (SPEC (dat_tm "x + 1") DAT_ZX_32_64)
              (TAC_PROOF(([],dat_tm "x + 1 < 2 EXP 32"), MP_TAC xb THEN ARITH_TAC)) in
  (ABBREV_TAC (mk_eq(`len:num`,dat_tm "x + 1")) THEN
   W(fun (asl,w) ->
     let leneq = snd(find (fun (_,th) -> concl th = mk_eq(dat_tm "x + 1",`len:num`)) asl) in
     let fixr = REWRITE_RULE[leneq] in
     let lenle = TAC_PROOF(([],`len <= 60`), MP_TAC xb THEN MP_TAC leneq THEN ARITH_TAC) in
     DAT_LIT_CASES_TAC st `1` (fixr tagth)
       (map fixr [and3; DAT_ZX32_USHR2; add1; zx] @ dat_lit_short_rws lenle))) g;;

(* Dev only: the header values of LITLONG to run (others left open). *)
let dat_litlong_xs = ref [60;61;62;63];;

(* Close a goal whose arithmetic facts connected to tm are contradictory    *)
(* (a header width other than that of the piece LITLONG6x).                  *)

let dat_kill_by tm : tactic = fun (asl,w) ->
  let fs = dat_facts asl in
  ACCEPT_TAC (CONTR w (TAC_PROOF(([],`F`),
    MAP_EVERY MP_TAC (relevant_arith_facts fs tm) THEN ARITH_TAC))) (asl,w);;

let DAT_LITLONG_TAC st : tactic = fun (asl,w as g) ->
  let tf = dat_find_eq `val(EL 0 (rest:byte list)) MOD 4` asl in
  let nxb = snd(find (fun (_,th) -> concl th = mk_neg(dat_tm "x < 60")) asl) in
  let x64 = snd(find (fun (_,th) -> concl th = dat_tm "x < 64") asl) in
  let ne = snd(find (fun (_,th) -> concl th = `~(rest:byte list = [])`) asl) in
  let one xv =
    let ll = xv - 59 in
    let lln = mk_small_numeral ll and xn = mk_small_numeral xv in
    let xeq = mk_eq(dat_x,xn) in
    W(fun (asl,w) ->
      let xth = snd(find (fun (_,th) -> concl th = xeq) asl) in
      (* the bytes of the header are there *)
      dat_add_fact (subst [mk_small_numeral (ll+1),`k:num`] `k <= LENGTH(rest:byte list)`)
        (if st = "B" then ASM_ARITH_TAC else
         FIRST_ASSUM(fun th -> if concl th = `snappy_refill_ok rest` then
           MP_TAC th else NO_TAC) THEN
         REWRITE_TAC[snappy_refill_ok; snappy_tag_needed; GSYM(CONJUNCT1 EL)] THEN
         ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN (subst [xn,`x:num`] `240 <= val(EL 0 (rest:byte list))`)
           (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
         CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) THEN
      TRY DAT_LEN_KILL_TAC THEN
      W(fun (asl,w) ->
        let kth = snd(find (fun (_,th) -> concl th =
                    subst [mk_small_numeral (ll+1),`k:num`] `k <= LENGTH(rest:byte list)`) asl) in
        let tagth = REWRITE_RULE[xth] (MP (SPECL [`m:num`; `rest:byte list`; `out:byte list`]
                       DAT_TAG_LITLONG)
                     (CONJ ne (CONJ tf (CONJ nxb
                       (EQ_MP (SYM((REWRITE_CONV[xth] THENC NUM_REDUCE_CONV) (mk_binary "<=" (mk_binary "-" (dat_x,`58`),
                          `LENGTH(rest:byte list)`))))
                         (CONV_RULE NUM_REDUCE_CONV kth)))))) in
        let tagth = CONV_RULE NUM_REDUCE_CONV tagth in
        (* the 32-bit word at ip + 1 *)
        let a = dat_w32_addr st in
        let ex = prove(mk_exists(`w32:int32`,
          mk_eq(subst [a,`a:int64`] `read (memory :> bytes32 a) s0`,`w32:int32`)),
          MESON_TAC[]) in
        X_CHOOSE_TAC `w32:int32` ex THEN
        dat_add_fact (subst [lln,`k:num`]
            `val(w32:int32) MOD 2 EXP (8 * k) = num_of_bytelist(SUB_LIST(1,k) rest)`)
          (FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `w32:int32`
                                 then SUBST1_TAC(SYM th) else NO_TAC) THEN
           SUBST1_TAC(WORD_RULE(mk_eq(dat_w32_addr st,
             mk_comb(mk_comb(`word_add:int64->int64->int64`,dat_ip st),`word 1:int64`)))) THEN
           MATCH_MP_TAC DAT_BYTES32_LOW THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC) THEN
        W(fun (asl,w) ->
          let mk = dat_mod_rule(snd(find (fun (_,th) -> is_eq(concl th) &&
                     can (find_term ((=) `w32:int32`)) (lhand(concl th)) &&
                     can (find_term ((=) `MOD`)) (lhand(concl th))) asl)) in
          let nb = rand(concl mk) in
          let mth = dat_mod_rule (SPECL [`w32:int32`; mk_small_numeral (8*ll)] DAT_WORD_AND_MASK) in
          let mth = REWRITE_RULE[mk] mth in
          let nblt = TAC_PROOF(([],mk_binary "<" (nb,`2 EXP 32`)),
            REWRITE_TAC[GSYM mk] THEN
            MP_TAC(ISPEC `w32:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
            MP_TAC(SPECL [`val(w32:int32)`; mk_small_numeral (1 lsl (8*ll))] MOD_LT_EQ) THEN
            CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) in
          let zx = MP (SPEC nb DAT_ZX_32_64) nblt in
          let zxw = if ll = 4 then
              let vlt = CONV_RULE NUM_REDUCE_CONV (MATCH_MP MOD_LT (REWRITE_RULE[DIMINDEX_32] (ISPEC `w32:int32` VAL_BOUND))) in
              [REWRITE_RULE[REWRITE_RULE[vlt] mk]
                (prove(`word_zx (w32:int32):int64 = word(val w32)`, REWRITE_TAC[word_zx]));
               DAT_ZX_64_32_WORD; DAT_AND32_FULL; MP (SPEC nb DAT_AND64_32) nblt]
            else [] in
          let add1 = INST_TYPE [`:64`,`:N`] (ISPECL [nb; `1`] (GSYM WORD_ADD)) in
          let and3 = REWRITE_RULE[tf] (SPEC dat_c DAT_ZX32_AND3) in
          ABBREV_TAC (mk_eq(`len:num`,mk_binary "+" (nb,`1`))) THEN
          W(fun (asl,w) ->
            let leneq = snd(find (fun (_,th) -> concl th =
                          mk_eq(mk_binary "+" (nb,`1`),`len:num`)) asl) in
            let fixr = REWRITE_RULE[leneq] in
            (* 1 <= len for the kill of impossible positions: leneq has no LENGTH *)
            dat_add_fact `1 <= len` (MP_TAC leneq THEN ARITH_TAC) THEN
            DAT_LIT_CASES_TAC st (mk_small_numeral (ll+1)) (fixr tagth)
              (map fixr ([xth; and3; DAT_ZX32_USHR2; mth; zx; add1] @ zxw)))))) in
  let cases = TAC_PROOF(([],mk_imp(mk_conj(mk_neg(dat_tm "x < 60"),dat_tm "x < 64"),
     list_mk_disj(map (fun v -> mk_eq(dat_x,mk_small_numeral v)) [60;61;62;63]))),
     ARITH_TAC) in
  (MP_TAC(MP cases (CONJ nxb x64)) THEN
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   map (fun v -> if mem v !dat_litlong_xs then
                   dat_kill_by (mk_eq(dat_x,mk_small_numeral v)) ORELSE one v
                 else ALL_TAC) [60;61;62;63]) g;;

dat_read_extra := DAT_READ2_TAC;;
dat_copy_tac := (fun st t -> DAT_COPY_TAC st t THEN DAT_COPY_CASES_TAC st t);;
dat_lit_tac := (fun st long -> if long then DAT_LITLONG_TAC st else DAT_LIT_TAC st);;

(* The pieces: the segment T (B or S) restricted to a tag class. *)

let dat_class_nexts = [dat_L_b,"<"; dat_L_s,"<"];;

let dat_class_pre st = if st = "B" then dat_T_b else dat_T_s;;
