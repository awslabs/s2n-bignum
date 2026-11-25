(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the segments of the validator path of snappy's decompressor,    *)
(* shared by the proofs of DecompressBranchless<size_t>                      *)
(* (gcc12_O2/decompress_branchless_ulong_proof.ml) and of                    *)
(* DecompressAllTags<SnappyDecompressionValidator> (dat_validator_lib.ml):   *)
(*                                                                           *)
(*  - the values that the code computes from a tag byte (its class and       *)
(*    length, the masks of ExtractOffset, the length bytes of the            *)
(*    kLengthMinusOffset entries as words);                                  *)
(*  - conditions of branches as integer and number facts: DAT_PC_TAC decides *)
(*    the condition of a PC if c then a else b by arithmetic (from the facts *)
(*    connected to it, relevant_arith_facts of common/arith_facts.ml), or    *)
(*    splits on it with the case as an integer fact; DAT_STEPS_TAC steps a   *)
(*    block with it up to given PCs;                                         *)
(*  - memory events within regions at offsets from a base (DAT_INSET_TAC);   *)
(*  - the leaves: reads of the state (DAT_READ_EQ_TAC) and arithmetic        *)
(*    (DAT_ARITH_FACTS_TAC) from the facts of the goal.                      *)
(*                                                                           *)
(* The state of a proof that these keep (dat_eq_facts) is per domain         *)
(* (par_local_ref, common/par.ml): the proofs run at the same time on        *)
(* several domains of the link.                                              *)
(* ========================================================================= *)

needs "arm/proofs/snappy/validator_tactics.ml";;
needs "common/snappy/snappy_memory.ml";;
needs "common/tactic_timing.ml";;
needs "common/arith_facts.ml";;

let DAT_BYTE_ENUM_TAC : tactic =
  GEN_TAC THEN
  SUBGOAL_THEN `c:byte = word(val c)` (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SPEC_TAC(`val(c:byte)`,`v:num`) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)) THEN REWRITE_TAC[];;

let DAT_ZX_AND3 = prove
 (`!c:byte. word_and (word_zx c:int64) (word 3) = word(val c MOD 4)`,
  DAT_BYTE_ENUM_TAC);;

let DAT_ZX_USHR2 = prove
 (`!c:byte. word_ushr (word_zx c:int64) 2 = word(val c DIV 4)`,
  DAT_BYTE_ENUM_TAC);;

let DAT_VAL_ZX_BYTE = prove
 (`!c:byte. val(word_zx c:int64) = val c`,
  GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_64] THEN ARITH_TAC);;

(* The masks of ExtractOffset (lsr of 0xffff00ff0000 by 16 * type).          *)

let DAT_MASKS = map (fun t ->
  WORD_REDUCE_CONV (subst [mk_small_numeral t,`t:num`]
   `word_zx (word_jushr (word 281470698455040:int64)
                        (word_shl (word t:int64) 4)):int32`)) (0--3);;

let DAT_EXT = prove
 (`(!(b1:byte) (b2:byte). word_and (word_zx (word_join b2 b1:int16):int32)
                          (word 16711680) = word 0) /\
   (!(b1:byte) (b2:byte). word_and (word_zx (word_join b2 b1:int16):int32)
                          (word 4294902015) = word_zx b1) /\
   (!(b1:byte) (b2:byte). word_and (word_zx (word_join b2 b1:int16):int32)
                          (word 65535) = word_zx (word_join b2 b1:int16)) /\
   (!(b1:byte) (b2:byte). word_and (word_zx (word_join b2 b1:int16):int32)
                          (word 0) = word 0)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN BITBLAST_TAC);;

let DAT_EXT_UNRED = map (fun mth ->
  let l = lhs(concl mth) in
  let gen = `word_and (word_zx (word_join (b2:byte) (b1:byte):int16):int32) m` in
  let tm = subst [l,`m:int32`] gen in
  let th = (REWRITE_CONV[mth] THENC REWRITE_CONV[DAT_EXT]) tm in
  GEN_ALL th) DAT_MASKS;;

let DAT_ZX_CHAINS = prove
 (`(!b:byte. word_zx (word_zx (word_zx b:int32):int16):int64 = word_zx b) /\
   (!j:int16. word_zx (word_zx (word_zx j:int32):int16):int64 = word_zx j) /\
   (!b:byte. word_zx (word_zx b:int32):int64 = word_zx b) /\
   (!j:int16. word_zx (word_zx j:int32):int64 = word_zx j) /\
   (!b:byte. word_zx (word_zx b:int32):int16 = word_zx b) /\
   (!j:int16. word_zx (word_zx j:int32):int16 = j)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN BITBLAST_TAC);;

let DAT_VAL_JOIN = prove
 (`!(b1:byte) (b2:byte). val(word_join b2 b1:int16) = val b1 + 256 * val b2`,
  REPEAT GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_JOIN_SIMPLE o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_16] THEN ARITH_TAC);;

let DAT_SX_IWORD = prove
 (`!i. --(&32768) <= i /\ i < &32768 ==> word_sx(iword i:int16):int64 = iword i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_sx] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC IVAL_IWORD_16 THEN ASM_REWRITE_TAC[]);;

let DAT_IVAL_IWORD64 = prove
 (`!i. --(&2 pow 63) <= i /\ i < &2 pow 63 ==> ival(iword i:int64) = i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

let DAT_VAL_EQ_IVAL = prove
 (`!(x:int64) (y:int64). val x = val y <=> ival x = ival y`,
  REWRITE_TAC[VAL_EQ; IVAL_EQ]);;

(* The lengths (low byte of the kLengthMinusOffset entry) and bit 7.         *)

let DAT_X_CASES_TAC (n:int) =
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV)) THEN
  CONV_TAC WORD_REDUCE_CONV;;

let DAT_LEN_LIT = prove
 (`!x. x < 60
       ==> word_and (iword(&(x + 1) - &256):int64) (word 255) = word(x + 1) /\
           ~bit 7 (word_zx (iword(&(x + 1) - &256):int64):int32)`,
  DAT_X_CASES_TAC 60);;

let DAT_LEN_C1 = prove
 (`!x. x < 64
       ==> word_and (iword(&(x MOD 8 + 4) - &256 * &(x DIV 8)):int64) (word 255) =
           word(x MOD 8 + 4) /\
           ~bit 7 (word_zx (iword(&(x MOD 8 + 4) - &256 * &(x DIV 8)):int64):int32)`,
  DAT_X_CASES_TAC 64);;

let DAT_LEN_C2 = prove
 (`!x. x < 64
       ==> word_and (iword(&(x + 1)):int64) (word 255) = word(x + 1) /\
           ~bit 7 (word_zx (iword(&(x + 1)):int64):int32)`,
  DAT_X_CASES_TAC 64);;

let DAT_LEN_255 = prove
 (`word_and (iword(&255):int64) (word 255) = word 255 /\
   bit 7 (word_zx (iword(&255):int64):int32)`,
  CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Conditions as integer and number facts.                                   *)
(* ------------------------------------------------------------------------- *)

let dat_short t = let s = string_of_term t in
  if String.length s > 400 then String.sub s 0 400 ^ "..." else s;;

let dat_side ths t = TAC_PROOF(([],t),INT_FACTS_ARITH_TAC ths);;

let DAT_IWORD64_CONV ths tm =
  match tm with
    Comb(Const("ival",_),(Comb(Const("iword",_),i) as t))
      when type_of t = `:int64` ->
      let th = ISPEC i DAT_IVAL_IWORD64 in
      MP th (dat_side ths (lhand(concl th)))
  | _ -> failwith "DAT_IWORD64_CONV";;

let DAT_BOOL_COND = TAUT
 `((if a then b else T) <=> ~a \/ b) /\ ((if a then T else b) <=> a \/ b) /\
  ((if a then b else F) <=> a /\ b) /\ ((if a then F else b) <=> ~a /\ b)`;;

let DAT_VALEQ_IWORD_CONV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Const("val",_),a)),Comb(Const("val",_),b))
      when type_of a = `:int64` &&
           (can (find_term (fun t -> match t with Const("iword",_) -> true | _ -> false)) a ||
            can (find_term (fun t -> match t with Const("iword",_) -> true | _ -> false)) b) ->
      REWR_CONV DAT_VAL_EQ_IVAL tm
  | _ -> failwith "DAT_VALEQ_IWORD_CONV";;

let dat_cond_conv rws ths =
  REWRITE_CONV(DAT_BOOL_COND :: VAL_WORD_SUB_EQ_0 ::
               INST_TYPE [`:64`,`:N`] (GSYM VAL_EQ) :: rws) THENC
  TOP_DEPTH_CONV DAT_VALEQ_IWORD_CONV THENC
  TOP_DEPTH_CONV (VAL_NOWRAP_CONV ths) THENC
  REWRITE_CONV[DAT_VAL_EQ_IVAL] THENC
  ONCE_DEPTH_CONV (IVAL_NW_CONV ths) THENC
  ONCE_DEPTH_CONV (DAT_IWORD64_CONV ths) THENC
  REWRITE_CONV[NOT_CLAUSES];;

let dat_facts asl =
  let ok th = let c = concl th in
    type_of c = bool_ty &&
    not(exists (fun v -> type_of v = `:armstate`) (frees c)) &&
    (try let _ = find_term (fun t -> match t with
           Const("read",_) | Const("write",_) | Const("ensures",_)
         | Const("eventually",_) -> true | _ -> false) c in false
     with Failure _ -> true) in
  map (CONV_RULE NUM_REDUCE_CONV) (filter ok (map snd asl));;

let dat_num_facts ths =
  filter (fun th -> let c = concl th in
     not(can (find_term (fun t -> type_of t = `:int`)) c) &&
     can (find_term (fun t -> type_of t = `:num`)) c) ths;;

let dat_int_prove_with rws ths tm =
  let th = dat_cond_conv rws ths tm in
  EQ_MP (SYM th) (TAC_PROOF(([],rhs(concl th)),
    REPEAT(COND_CASES_TAC THEN POP_ASSUM MP_TAC) THEN
    ((MAP_EVERY MP_TAC (dat_num_facts ths) THEN ARITH_TAC) ORELSE
     INT_FACTS_ARITH_TAC ths)));;

(* The facts for an arithmetic decision of tm, in the order tried: those of  *)
(* arithmetic connected to tm (also after the rewrites rws), then (if        *)
(* dat_arith_all) all those of arithmetic, then (if dat_arith_full) all the  *)
(* facts. The fallbacks are off: in the runs measured                       *)
(* (arm/snappy/doc/PERF.md) they never succeeded where the connected facts   *)
(* failed, and failed slowly (the failing attempts are the conditions that   *)
(* are not decided, then split).                                             *)

let dat_arith_full = ref false;;
let dat_arith_all = ref false;;

let dat_arith_levels rws ths tm =
  let ar = arith_facts ths in
  let tm' = try rhs(concl(REWRITE_CONV rws tm)) with Failure _ -> tm in
  let rel = relevant_arith_facts ar (mk_conj(tm,tm')) in
  ["arith.rel",rel] @
  (if !dat_arith_all && length rel < length ar then ["arith.all",ar] else []) @
  (if !dat_arith_full && length ar < length ths then ["arith.full",ths] else []);;

let dat_try_levels f levels =
  let rec go l = match l with
      [] -> failwith "dat_try_levels"
    | (name,ths)::l' -> try timed_outcome name f ths with Failure _ -> go l' in
  go levels;;

let DAT_INT_PROVE rws asl tm =
  let ths = dat_facts asl in
  dat_try_levels (fun ths -> dat_int_prove_with rws ths tm)
                 (dat_arith_levels rws ths tm);;

(* At a PC of the form if c then a else b: decide c by arithmetic, or split  *)
(* and add the case as an integer fact.                                       *)

let DAT_PC_TAC ?(verbose=false) rws : tactic = fun (asl,w as g) ->
  let r = bstep_pc_value g in
  let c,_ = dest_cond r in
  let fix th =
    FIRST_X_ASSUM(fun pth -> match concl pth with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),pc),_)),r')
          when pc = `PC` && r' = r -> ASSUME_TAC(REWRITE_RULE[th] pth)
      | _ -> NO_TAC) in
  try let th = DAT_INT_PROVE rws asl c in (fix (EQT_INTRO th)) g with Failure _ ->
  try let th = DAT_INT_PROVE rws asl (mk_neg c) in
      (fix (EQF_INTRO th)) g with Failure _ ->
  (if verbose then (print_string "SPLIT on: "; print_term c; print_newline()));
  (ASM_CASES_TAC c THEN
   POP_ASSUM(fun cth ->
     let cth' = try CONV_RULE (dat_cond_conv rws (dat_facts asl)) cth
                with Failure m -> (if verbose then Printf.printf "CASE CONV FAILED: %s\n%!" m); cth in
     (if verbose then (print_string "CASE FACT: "; print_term (concl cth'); print_newline()));
     fix cth THEN ASSUME_TAC cth')) g;;

let rec DAT_STEPS_TAC ?(verbose=false) rws rewrites execth i (stop:term list) : tactic = fun g ->
  let r = try bstep_pc_value g with Failure _ -> `T` in
  let again = DAT_STEPS_TAC ~verbose rws rewrites execth in
  if r = `returnaddress:int64` then ALL_TAC g
  else if is_cond r then (DAT_PC_TAC ~verbose rws THEN again i stop) g
  else
    let same k = k = r || can (fun () -> WORD_RULE(mk_eq(k,r))) () in
    if i > 1 && exists same stop then ALL_TAC g else
    (ARM_BSTEP_TAC ~rewrites execth (i--i) THEN again (i+1) stop) g;;

(* ------------------------------------------------------------------------- *)
(* Memory events within the regions: memrange(a,k) SUBSET memrange(b,l) by   *)
(* word_sub a b = word n and n + k <= l.                                      *)
(* ------------------------------------------------------------------------- *)

let DAT_MEMRANGE_SUBSET = prove
 (`!(a:int64) b k l n.
        word_sub a b = word n /\ n + k <= l
        ==> memrange(a,k) SUBSET memrange(b,l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a:int64 = word_add b (word n)` SUBST1_TAC THENL
   [UNDISCH_TAC `word_sub a b:int64 = word n` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_MEMRANGE] THEN X_GEN_TAC `x:int64` THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `n + i:num` THEN ASM_REWRITE_TAC[WORD_ADD] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; CONV_TAC WORD_RULE])

let dat_split_addr a =
  let th = try DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV a with Failure _ -> REFL a in
  let a' = rhs(concl th) in
  match a' with
    Comb(Comb(Const("word_add",_),b),Comb(Const("word",_),n)) -> b,n
  | _ -> a',`0`;;

let DAT_SUBSET_ONE_TAC : tactic = fun (asl,w as g) ->
  let s,t = dest_binary "SUBSET" w in
  let a,k = dest_pair(rand s) and b,l = dest_pair(rand t) in
  let ba,na = dat_split_addr a and bb,nb = dat_split_addr b in
  if ba <> bb then failwith "DAT_SUBSET_ONE_TAC: bases" else
  let n = if nb = `0` then na else mk_binary "-" (na,nb) in
  let facts = dat_facts asl in
  let rel (_,w as g) =
    MAP_EVERY MP_TAC (relevant_arith_facts facts w) g in
  (MATCH_MP_TAC DAT_MEMRANGE_SUBSET THEN EXISTS_TAC n THEN CONJ_TAC THENL
    [REWRITE_TAC[WORD_ADD; WORD_SUB] THEN
     (CONV_TAC WORD_RULE ORELSE
      (SUBGOAL_THEN (mk_binary "<=" (nb,na)) MP_TAC THENL
        [rel THEN ARITH_TAC;
         SIMP_TAC[GSYM WORD_SUB] THEN CONV_TAC WORD_RULE]));
     rel THEN REWRITE_TAC[DAT_VAL_ZX_BYTE] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]) g;;

let rec DAT_SUBSET_TAC : tactic = fun (asl,w as g) ->
  let s,t = dest_binary "SUBSET" w in
  match t with
    Comb(Comb(Const("UNION",_),t1),t2) ->
      (FIRST [MATCH_MP_TAC(SET_RULE `s SUBSET a ==> s SUBSET a UNION b`) THEN
              DAT_SUBSET_TAC;
              MATCH_MP_TAC(SET_RULE `s SUBSET b ==> s SUBSET a UNION b`) THEN
              DAT_SUBSET_TAC]) g
  | _ -> DAT_SUBSET_ONE_TAC g;;

let DAT_INSET_TAC : tactic = fun (asl,w) ->
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
     REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE DAT_SUBSET_TAC)]) (asl,w);;
let DAT_READ_BYTES16 = prove
 (`!(a:int64) (l:byte list) k s.
     read (memory :> bytelist(a,LENGTH l)) s = l /\ k + 2 <= LENGTH l
     ==> read (memory :> bytes16 (word_add a (word k))) s =
         word_join (EL (k + 1) l) (EL k l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `a:int64`; `k:num`;
                 `2`; `LENGTH(l:byte list)`; `s:armstate`]
         READ_BYTELIST_SUB_LIST) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[SNAPPY_SUB_LIST_2] THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES; LENGTH; num_of_bytelist] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[DAT_VAL_JOIN] THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The leaves of a segment: the exit or the next cut point, with witnesses. *)
(* ------------------------------------------------------------------------- *)

let dat_norm_addr_conv = DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV;;

(* State of a proof, per domain (par_local_ref, common/par.ml): the pieces  *)
(* run at the same time on several domains of the link.                     *)

let dat_eq_facts = par_local_ref (fun () -> ([]:thm list));;

let rec dat_eq l r =
  if l = r then REFL l else
  try let tm = mk_eq(l,r) in
      if type_of l = `:num` then
        (try ARITH_RULE tm with Failure _ ->
         dat_try_levels (fun ths ->
           try TAC_PROOF(([],tm),MAP_EVERY MP_TAC (dat_num_facts ths) THEN ARITH_TAC)
           with Failure _ -> TAC_PROOF(([],tm),INT_FACTS_ARITH_TAC ths))
          (dat_arith_levels [] !(dat_eq_facts ()) tm))
      else if type_of l = `:int` then INT_ARITH tm
      else
      let th = (REWRITE_CONV[WORD_ADD] THENC
                (fun t -> EQT_INTRO(WORD_RULE t))) tm in
      EQT_ELIM th
  with Failure _ ->
  match l,r with
    Comb(f,x),Comb(g,y) when type_of f = type_of g -> MK_COMB(dat_eq f g,dat_eq x y)
  | _ -> failwith "dat_eq"

let DAT_READ_EQ_TAC : tactic = fun (asl,w) ->
  let lw,v = dest_eq w in
  let rc,s = dest_comb lw in
  let rd,c = dest_comb rc in
  let nth = match c with
      Comb(Comb(Const(":>",_) as op,m),Comb(k,a)) ->
        AP_TERM (mk_comb(op,m)) (AP_TERM k (dat_norm_addr_conv a))
    | _ -> REFL c in
  let cn = rand(concl nth) in
  let fact = find (fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s')),_) ->
        s' = s && (c' = cn || c' = c)
    | _ -> false) (map snd asl) in
  let c' = rand(rator(lhs(concl fact))) in
  let th1 = if c' = c then fact else
            TRANS (AP_THM (AP_TERM rd nth) s) fact in
  dat_eq_facts () := dat_facts asl;
  ACCEPT_TAC (TRANS th1 (dat_eq (rhs(concl th1)) v)) (asl,w);;

let DAT_ARITH_FACTS_TAC : tactic = fun (asl,w) ->
  let facts = dat_facts asl in
  let th = dat_try_levels (fun ths -> TAC_PROOF(([],w),
             (MAP_EVERY MP_TAC (dat_num_facts ths) THEN ARITH_TAC) ORELSE
             INT_FACTS_ARITH_TAC ths)) (dat_arith_levels [] facts w) in
  ACCEPT_TAC th (asl,w);;

