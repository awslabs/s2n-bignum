(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shared objects as the dynamic loader leaves them: the data that the       *)
(* loader relocates.                                                         *)
(*                                                                           *)
(* A shared object linked with -z now -z relro is mapped at one base pc (a   *)
(* multiple of the page size), every segment at pc + its virtual address.    *)
(* Before any of its code runs, the loader applies the dynamic relocations,  *)
(* which write 64-bit slots of the writable segment (the GOT and the         *)
(* relocated data such as vtables), and then makes those pages read-only     *)
(* (RELRO). The code and read-only data are "the image" of the proofs        *)
(* (aligned_bytes_loaded s (word pc) <lib>_mc); this file describes the      *)
(* relocated slots. For each library, a generated definition lists them as   *)
(* (address, value) pairs as functions of pc and of the addresses of the     *)
(* imported symbols, imp:string->int64:                                      *)
(*                                                                           *)
(*   <lib>_relocated pc imp =                                                *)
(*    [word(pc + 0x1fe48), word(pc + 0x370);         (RELATIVE, addend)      *)
(*     word(pc + 0x1fe50), word_add (imp "memmove") (word 8);  (ABS64)       *)
(*     word(pc + 0x1ffe0), imp "memmove"; ...]   (GLOB_DAT, JUMP_SLOT)       *)
(*                                                                           *)
(* Nothing here depends on the instruction set or on the relocation kinds:   *)
(* the memory component m is a parameter (memory for both AArch64 and        *)
(* x86-64), and the list is all that the generator produces.                 *)
(*                                                                           *)
(* TWO FORMS OF THE HYPOTHESIS                                               *)
(*                                                                           *)
(*  - elf_relocated m s l: in the state s, each slot of l holds its value.   *)
(*    This is the plain statement, for the theorems of the entry points.     *)
(*                                                                           *)
(*  - elf_relocated_data b d l: the number d, the contents of a region of    *)
(*    memory at address b (such as the RELRO part of the writable segment),  *)
(*    has each slot of l at its offset from b. A theorem then has            *)
(*    elf_relocated_data b d l as a hypothesis and                           *)
(*    read (memory :> bytes(b,n)) s = d in its precondition, the same        *)
(*    pattern as the region (ea,el) with contents ev of the contracts of the *)
(*    external functions. The precondition is one fact, which the step       *)
(*    tactics carry across the code (it is not written: see below), and      *)
(*    which a caller's precondition gives unchanged to a callee whose        *)
(*    theorem has the same hypothesis; with elf_relocated in the             *)
(*    preconditions, every call would have to prove it again in the state of *)
(*    the call, slot by slot.                                                *)
(*                                                                           *)
(* ELF_RELOCATED_OF_DATA goes from the second to the first, and              *)
(* ENSURES_ELF_RELOCATED (with ENSURES_ELF_RELOCATED_TAC) turns a theorem in *)
(* the second form into one in the first, so a function proved with the      *)
(* second form has a theorem in the first; both need elf_slots_within b n l, *)
(* the slots in the region, which ELF_SLOTS_WITHIN_CONV proves for a         *)
(* concrete list. ELF_RELOCATED_SLOTS and ELF_RELOCATED_DATA_SLOTS give the  *)
(* slots as theorems read (m :> bytes64 (word_add (word pc) (word off))) s = *)
(* v, in the form in which the step tactics look memory facts up, and        *)
(* ELF_RELOCATED_TAC and ELF_RELOCATED_DATA_TAC add them to the assumptions  *)
(* (only those selected, as every fact costs at each step of ARM_STEPS_TAC). *)
(*                                                                           *)
(* DISJOINTNESS                                                              *)
(*                                                                           *)
(* The slots are only read: RELRO makes them read-only, so a region that the *)
(* code writes is disjoint from them (the trusted base states this). The     *)
(* theorems state it as disjointness from the whole extent of the library,   *)
(* (word pc, <lib>_extent) from pc to the end of the RELRO part, which also  *)
(* covers the image and the gap between the segments (reserved by the       *)
(* loader). The facts about the slots then cross every write by the          *)
(* nonoverlapping facts that the step tactics derive for a subregion of an   *)
(* assumption with the same base: word_add (word pc) (word off) for an       *)
(* offset off within the extent.                                             *)
(* ========================================================================= *)

let elf_relocated = new_definition
 `elf_relocated (m:(S,int64->byte)component) (s:S) (l:(int64#int64)list) <=>
    ALL (\(a,v). read (m :> bytes64 a) s = v) l`;;

let elf_relocated_data = new_definition
 `elf_relocated_data (b:int64) (d:num) (l:(int64#int64)list) <=>
    ALL (\(a,v). word(d DIV 2 EXP (8 * val(word_sub a b))) = v) l`;;

(* The slots that a region of n bytes at b contains.                         *)

let elf_slots_within = new_definition
 `elf_slots_within (b:int64) (n:num) (l:(int64#int64)list) <=>
    ALL (\(a,v). val(word_sub a b) + 8 <= n) l`;;

(* ------------------------------------------------------------------------- *)
(* A slot read from the contents of a region that contains it.               *)
(* ------------------------------------------------------------------------- *)

let ELF_SLOT_OF_DATA = prove
 (`!(m:(S,int64->byte)component) b n d a v s.
        read (m :> bytes(b,n)) s = d /\
        val(word_sub a b) + 8 <= n /\
        word(d DIV 2 EXP (8 * val(word_sub a b))) = v
        ==> read (m :> bytes64 a) s = v`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `k = val(word_sub (a:int64) b)` THEN
  SUBGOAL_THEN `a:int64 = word_add b (word k)` SUBST1_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[WORD_VAL] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES64_WBYTES; VAL_READ_WBYTES;
              DIMINDEX_64; READ_BYTES_DIV] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 = 8 * 8`; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (n - k) 8 = MIN 8 8` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

let ELF_RELOCATED_OF_DATA = prove
 (`!(m:(S,int64->byte)component) b n d l s.
        read (m :> bytes(b,n)) s = d /\
        elf_slots_within b n l /\ elf_relocated_data b d l
        ==> elf_relocated m s l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[elf_relocated; elf_relocated_data; elf_slots_within] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[AND_ALL] THEN MATCH_MP_TAC MONO_ALL THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ELF_SLOT_OF_DATA THEN
  MAP_EVERY EXISTS_TAC [`b:int64`; `n:num`; `d:num`] THEN
  ASM_REWRITE_TAC[]);;

let ELF_RELOCATED_DATA_OF_STATE = prove
 (`!(m:(S,int64->byte)component) b n l s.
        elf_slots_within b n l /\ elf_relocated m s l
        ==> elf_relocated_data b (read (m :> bytes(b,n)) s) l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[elf_relocated; elf_relocated_data; elf_slots_within] THEN
  REWRITE_TAC[AND_ALL] THEN MATCH_MP_TAC MONO_ALL THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `v:int64`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC ELF_SLOT_OF_DATA THEN
  MAP_EVERY EXISTS_TAC [`b:int64`; `n:num`;
                        `read ((m:(S,int64->byte)component) :> bytes(b,n)) s`]
  THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A theorem with elf_relocated_data b d l as a hypothesis and the contents  *)
(* d of the region (b,n) in its precondition, for all d, gives the theorem   *)
(* with elf_relocated in the precondition instead. The hypotheses that do    *)
(* not mention d stay hypotheses.                                            *)
(* ------------------------------------------------------------------------- *)

let ENSURES_ELF_RELOCATED = prove
 (`!(step:S->S->bool) (m:(S,int64->byte)component) b n l P Q C.
        elf_slots_within b n l /\
        (!d. elf_relocated_data b d l
             ==> ensures step (\s. read (m :> bytes(b,n)) s = d /\ P s) Q C)
        ==> ensures step (\s. elf_relocated m s l /\ P s) Q C`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ensures] THEN
  X_GEN_TAC `s:S` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `read ((m:(S,int64->byte)component) :>
                                     bytes(b,n)) (s:S)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ELF_RELOCATED_DATA_OF_STATE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ensures] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Conversions and rules.                                                    *)
(* ------------------------------------------------------------------------- *)

(* The address of a slot, word(pc + off), as word_add (word pc) (word off):  *)
(* the form of NORMALIZE_RELATIVE_ADDRESS_CONV, in which the step tactics    *)
(* find memory facts.                                                        *)

let ELF_SLOT_ADDRESS_CONV tm =
  match tm with
    Comb(Const("word",_),Comb(Comb(Const("+",_),_),k)) when is_numeral k ->
      GEN_REWRITE_CONV I [WORD_ADD] tm
  | _ -> REFL tm;;

let ELF_SLOT_CANON_RULE =
  CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV
    ELF_SLOT_ADDRESS_CONV)))));;

(* elf_relocated m s [a1,v1; ...] as the conjunction of the slots. The list  *)
(* may be given by a definition, which ~defs unfolds (as the theorem of a    *)
(* generated <lib>_relocated).                                               *)

let ELF_UNFOLD_LIST_CONV defs tm =
  if is_list tm then REFL tm
  else (REWRITE_CONV defs THENC TRY_CONV(DEPTH_CONV let_CONV)) tm;;

let ELF_RELOCATED_CONV ?(defs=[]) =
  RAND_CONV(ELF_UNFOLD_LIST_CONV defs) THENC
  GEN_REWRITE_CONV I [elf_relocated] THENC
  PURE_REWRITE_CONV[ALL; AND_CLAUSES] THENC
  DEPTH_CONV GEN_BETA_CONV;;

(* Selecting slots: by the addresses (offsets from pc), by the names of the  *)
(* imports their values mention, or all.                                     *)

type elf_slot_select = term -> term -> bool;;     (* address, value *)

let elf_all_slots : elf_slot_select = fun _ _ -> true;;

let elf_slot_offset a =
  match a with
    Comb(Const("word",_),Comb(Comb(Const("+",_),_),k)) when is_numeral k ->
      Some(dest_small_numeral k)
  | Comb(Const("word",_),Var(_,_)) -> Some 0
  | _ -> None;;

let elf_slots_at (offs:int list) : elf_slot_select = fun a _ ->
  match elf_slot_offset a with Some k -> mem k offs | None -> false;;

let elf_slots_importing (names:string list) : elf_slot_select = fun _ v ->
  can (find_term (fun t -> match t with
      Comb(Var(_,_),s) ->
        (try mem (dest_string s) names with Failure _ -> false)
    | _ -> false)) v;;

(* The slot facts of |- elf_relocated m s l, selected.                       *)

let ELF_RELOCATED_SLOTS ?(defs=[]) ?(select=elf_all_slots) th =
  let th' = CONV_RULE (ELF_RELOCATED_CONV ~defs) th in
  if concl th' = `T` then [] else
  let ths = CONJUNCTS th' in
  map ELF_SLOT_CANON_RULE
   (filter (fun th -> let l,v = dest_eq(concl th) in
                      select (rand(rand(rand(rator l)))) v) ths);;

(* The slot facts from |- read (m :> bytes(b,n)) s = d and                   *)
(* |- elf_relocated_data b d l, checking that each selected slot is in       *)
(* (b,n): val(word_sub a b) is computed for a = word(pc + k) and             *)
(* b = word(pc + j) (or word pc), with j <= k.                               *)

let ELF_SLOT_OFFSET_CONV =
  let pth = prove
   (`!p j k. j <= k
             ==> val(word_sub (word(p + k)) (word(p + j)):int64) =
                 (k - j) MOD 2 EXP 64`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DIMINDEX_64; GSYM VAL_WORD] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE) in
  fun tm ->
    let th = PART_MATCH (lhand o rand) pth tm in
    let ath = EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))) in
    CONV_RULE(RAND_CONV NUM_REDUCE_CONV) (MP th ath);;

let ELF_RELOCATED_DATA_SLOTS ?(defs=[]) ?(select=elf_all_slots) bth dth =
  let m,b,n,s,d =
    match concl bth with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
           Comb(Comb(Const(":>",_),m),Comb(Const("bytes",_),bn))),s)),d) ->
        let b,n = dest_pair bn in m,b,n,s,d
    | _ -> failwith "ELF_RELOCATED_DATA_SLOTS: not read (m :> bytes(b,n)) s" in
  let dth' = CONV_RULE(RAND_CONV(ELF_UNFOLD_LIST_CONV defs) THENC
                       GEN_REWRITE_CONV I [elf_relocated_data] THENC
                       PURE_REWRITE_CONV[ALL; AND_CLAUSES] THENC
                       DEPTH_CONV GEN_BETA_CONV) dth in
  if concl dth' = `T` then [] else
  let ths = CONJUNCTS dth' in
  let lemma = ISPECL [m;b;n;d] ELF_SLOT_OF_DATA in
  let slot th =
    let l,v = dest_eq(concl th) in
    let vtm = rand(rand(rand(rand l))) in
    let a = lhand(rand vtm) in
    if not(select a v) then None else
    let oth = ELF_SLOT_OFFSET_CONV vtm in
    let bound =
      try EQT_ELIM ((LAND_CONV(LAND_CONV(K oth)) THENC NUM_REDUCE_CONV)
                    (mk_binary "<=" (mk_binary "+" (vtm,`8`),n)))
      with Failure _ -> failwith ("ELF_RELOCATED_DATA_SLOTS: the slot at `" ^
                          string_of_term a ^ "` is not in the region") in
    let ith = SPECL [a;v;s] lemma in
    Some(ELF_SLOT_CANON_RULE(MP ith (CONJ bth (CONJ bound th)))) in
  mapfilter (fun th -> match slot th with Some t -> t | None -> fail()) ths;;

(* ELF_RELOCATED_TAC replaces each assumption elf_relocated m s l by the     *)
(* selected slot facts. ELF_RELOCATED_DATA_TAC adds the selected slot facts  *)
(* from each pair of assumptions read (m :> bytes(b,n)) s = d and            *)
(* elf_relocated_data b d l, which stay.                                     *)

let ELF_RELOCATED_TAC ?(defs=[]) ?(select=elf_all_slots) =
  let is_rel tm = match tm with
      Comb(Comb(Comb(Const("elf_relocated",_),_),_),_) -> true
    | _ -> false in
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_rel(concl th) then
      MAP_EVERY ASSUME_TAC (ELF_RELOCATED_SLOTS ~defs ~select th)
    else failwith "ELF_RELOCATED_TAC"));;

let ELF_RELOCATED_DATA_TAC ?(defs=[]) ?(select=elf_all_slots) =
  W(fun (asl,_) ->
    let ths = map snd asl in
    let datas = filter (fun th -> match concl th with
        Comb(Comb(Comb(Const("elf_relocated_data",_),_),_),_) -> true
      | _ -> false) ths in
    let bytes_for b d = filter (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
             Comb(Comb(Const(":>",_),_),Comb(Const("bytes",_),bn))),_)),d')
          -> d' = d && fst(dest_pair bn) = b
      | _ -> false) ths in
    let news = List.concat (map (fun dth ->
        match concl dth with
          Comb(Comb(Comb(_,b),d),_) ->
            List.concat (map (fun bth ->
              ELF_RELOCATED_DATA_SLOTS ~defs ~select bth dth) (bytes_for b d))
        | _ -> []) datas) in
    MAP_EVERY ASSUME_TAC news);;

(* ELF_SLOTS_WITHIN_CONV defs proves elf_slots_within b n l (to T) for a     *)
(* concrete list, given by the definitions defs, of slots word(pc + k) with  *)
(* b = word(pc + j).                                                         *)

let ELF_SLOTS_WITHIN_CONV ?(defs=[]) =
  RAND_CONV(ELF_UNFOLD_LIST_CONV defs) THENC
  GEN_REWRITE_CONV I [elf_slots_within] THENC
  PURE_REWRITE_CONV[ALL; AND_CLAUSES] THENC
  DEPTH_CONV GEN_BETA_CONV THENC
  DEPTH_CONV ELF_SLOT_OFFSET_CONV THENC NUM_REDUCE_CONV;;

(* ENSURES_ELF_RELOCATED_TAC b n, on a goal                                  *)
(* ensures step (\s. elf_relocated m s l /\ P s) Q C, leaves                 *)
(* elf_slots_within b n l /\                                                 *)
(* !d. elf_relocated_data b d l                                              *)
(*     ==> ensures step (\s. read (m :> bytes(b,n)) s = d /\ P s) Q C,       *)
(* by ENSURES_ELF_RELOCATED.                                                 *)

let ENSURES_ELF_RELOCATED_TAC (b:term) (n:term) : tactic =
  fun (asl,w) ->
    match w with
      Comb(Comb(Comb(Comb(Const("ensures",_),step),pre),post),frame) ->
        let s,body = dest_abs pre in
        let rel,rest = dest_conj body in
        let m,l = match rel with
            Comb(Comb(Comb(Const("elf_relocated",_),m),s'),l) when s' = s ->
              m,l
          | _ -> failwith "ENSURES_ELF_RELOCATED_TAC: no elf_relocated" in
        let th = ISPECL [step;m;b;n;l;mk_abs(s,rest);post;frame]
                   ENSURES_ELF_RELOCATED in
        MATCH_MP_TAC (BETA_RULE th) (asl,w)
    | _ -> failwith "ENSURES_ELF_RELOCATED_TAC: not ensures";;
