(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The objects of snappy's decompressor in memory, as the AArch64 Linux C++  *)
(* ABI (LP64, Itanium C++ ABI) lays them out (offsets checked against the    *)
(* code of gcc 12 -O2, see arm/snappy/DESIGN.md section 7).                  *)
(*                                                                           *)
(* snappy::ByteArraySource (snappy-sinksource.h), 24 bytes, 8-aligned:       *)
(*                                                                           *)
(*    +0   vptr               vtable_ByteArraySource of the build            *)
(*    +8   const char* ptr_   the next unread byte                          *)
(*    +16  size_t left_       the number of unread bytes                     *)
(*                                                                           *)
(* Its vtable slots (8 bytes each, from the vptr): +0 the destructor, +8 the *)
(* deleting destructor, +16 Available, +24 Peek, +32 Skip.                  *)
(*                                                                           *)
(* snappy::SnappyDecompressor (snappy.cc), 48 bytes, 8-aligned:              *)
(*                                                                           *)
(*    +0   Source* reader_                                                   *)
(*    +8   const char* ip_                    next buffered byte             *)
(*    +16  const char* ip_limit_              just past the buffered bytes   *)
(*    +24  const char* ip_limit_min_maxtaglen_                               *)
(*    +32  uint64_t peeked_                   bytes peeked, not yet skipped  *)
(*    +40  bool eof_                                                         *)
(*    +41  char scratch_[5]                                                  *)
(*                                                                           *)
(* (bytes 46 and 47 are padding). The predicates give only the fields that  *)
(* the code reads; vptr is the value of the vptr, word(pc + vtable_<C>) for  *)
(* the image loaded at pc.                                                   *)
(* ========================================================================= *)

needs "common/snappy/snappy_decompressor.ml";;
needs "arm/proofs/utils/compare_branch.ml";;

let snappy_byte_array_source = new_definition
 `snappy_byte_array_source (src:int64) (vptr:int64) (p:int64) (l:int64)
                           (s:armstate) <=>
    read (memory :> bytes64 src) s = vptr /\
    read (memory :> bytes64 (word_add src (word 8))) s = p /\
    read (memory :> bytes64 (word_add src (word 16))) s = l`;;

let snappy_decompressor = new_definition
 `snappy_decompressor (d:int64) (reader:int64) (ip:int64) (lim:int64)
                      (peeked:int64) (eof:bool) (s:armstate) <=>
    read (memory :> bytes64 d) s = reader /\
    read (memory :> bytes64 (word_add d (word 8))) s = ip /\
    read (memory :> bytes64 (word_add d (word 16))) s = lim /\
    read (memory :> bytes64 (word_add d (word 32))) s = peeked /\
    read (memory :> bytes8 (word_add d (word 40))) s = word(bitval eof)`;;

let SNAPPY_DECOMPRESSOR_OBJECTS_EXPAND_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[snappy_byte_array_source;
                              snappy_decompressor]) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC));;

(* ------------------------------------------------------------------------- *)
(* The bytes of an input given as a byte list.                               *)
(* ------------------------------------------------------------------------- *)

let READ_BYTELIST_EL = prove
 (`!l (a:int64) k (m:int64->byte).
     read (bytelist(a,LENGTH l)) m = l /\ k < LENGTH l
     ==> read (bytes8 (word_add a (word k))) m = EL k l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  REWRITE_TAC[bytelist_clauses; CONS_11; BYTES8_ELEMENT; READ_ELEMENT] THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `k:num`; `m:int64->byte`] THEN
  STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; WORD_ADD_0; LT_SUC] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`word_add a (word 1):int64`; `n:num`; `m:int64->byte`]) THEN
  ASM_REWRITE_TAC[BYTES8_ELEMENT; READ_ELEMENT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ADD1] THEN CONV_TAC WORD_RULE);;

let READ_MEMORY_BYTELIST_EL = prove
 (`!(a:int64) l k s.
     read (memory :> bytelist(a,LENGTH l)) s = l /\ k < LENGTH l
     ==> read (memory :> bytes8 (word_add a (word k))) s = EL k l`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTELIST_EL]);;

(* ------------------------------------------------------------------------- *)
(* The tests of a byte as the step tactics leave them (tbz on bit 7 of the   *)
(* zero-extended byte, cmp w, #imm with b.hi/b.ls), as comparisons of its    *)
(* value.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BIT7_WORD_ZX_BYTE = prove
 (`(!b:byte. bit 7 (word_zx b:int32) <=> ~(val b < 128)) /\
   (!b:byte. bit 7 (word_zx b:int64) <=> ~(val b < 128))`,
  REWRITE_TAC[VAL_BYTE_LT_128] THEN CONJ_TAC THEN BITBLAST_TAC);;

let CMP_HI_WORD_ZX_BYTE = prove
 (`!(b:byte) k.
     k < 256
     ==> ((&(val(word_zx b:int32)) - &k:int =
           &(val(word_sub (word_zx b:int32) (word k))) /\
           ~(val(word_sub (word_zx b:int32) (word k)) = 0)) <=>
          ~(val b < k + 1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_zx (b:byte):int32`; `k:num`] WORD_CMP_HI_INT) THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  DISCH_TAC THEN SUBGOAL_THEN `val(b:byte) MOD 2 EXP 32 = val b` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Driving bstep through code with branches on data: BSTEP_SPLIT_PC_TAC      *)
(* splits on the condition of a PC of the form if c then a else b (left by   *)
(* a conditional branch that the assumptions do not decide) and rewrites the *)
(* assumptions with the case; ARM_BSTEP_RUN_TAC execth i leaf steps one      *)
(* instruction at a time (from step number i), splitting at such branches,   *)
(* and applies leaf at the return (PC = returnaddress).                      *)
(* ------------------------------------------------------------------------- *)

let BSTEP_SPLIT_PC_TAC =
  FIRST_ASSUM(fun th -> match concl th with
     Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),r)
       when c = `PC` && is_cond r ->
       let b,_ = dest_cond r in
       ASM_CASES_TAC b THEN
       POP_ASSUM(fun c -> RULE_ASSUM_TAC(REWRITE_RULE[c]) THEN ASSUME_TAC c)
   | _ -> NO_TAC);;

let bstep_pc_value (asl,w) =
  let _,th = find (fun (_,th) -> match concl th with
     Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) -> c = `PC`
   | _ -> false) asl in
  rand(concl th);;

let rec ARM_BSTEP_RUN_TAC execth i (leaf:tactic) : tactic = fun g ->
  let r = try bstep_pc_value g with Failure _ -> `T` in
  if r = `returnaddress:int64` then leaf g
  else if is_cond r then
    (BSTEP_SPLIT_PC_TAC THEN ARM_BSTEP_RUN_TAC execth i leaf) g
  else (ARM_BSTEP_TAC execth (i--i) THEN ARM_BSTEP_RUN_TAC execth (i+1) leaf) g;;

(* A memory-safety goal with a larger read set.                              *)

let MEMACCESS_INSET_EXISTS_MONO = prove
 (`!(t:(uarch_event)list) e rs ws rs'.
        rs' SUBSET rs /\ (?e2. t = APPEND e2 e /\ memaccess_inset e2 rs' ws)
        ==> (?e2. t = APPEND e2 e /\ memaccess_inset e2 rs ws)`,
  MESON_TAC[MEMACCESS_INSET_MONO; SUBSET_REFL]);;

(* ARM_BSTEP_RUN_GEN_TAC: ARM_BSTEP_RUN_TAC with ~kill applied after each    *)
(* split (to close the cases that the facts contradict), ~norm after each    *)
(* step (to normalize values), and ~calls, a list of PC values with a tactic *)
(* (given the step number) that goes through the call at that PC; it         *)
(* returns the number of steps used, the run continuing after them.          *)

let rec ARM_BSTEP_RUN_GEN_TAC ?(kill=ALL_TAC) ?(norm=ALL_TAC) ?(calls=[])
                              execth i (leaf:tactic) : tactic = fun g ->
  let r = try bstep_pc_value g with Failure _ -> `T` in
  let again = ARM_BSTEP_RUN_GEN_TAC ~kill ~norm ~calls execth in
  if r = `returnaddress:int64` then leaf g
  else if is_cond r then
    (BSTEP_SPLIT_PC_TAC THEN TRY kill THEN again i leaf) g
  else
    let same k = k = r || can (fun () -> WORD_RULE(mk_eq(k,r))) () in
    match (try Some(snd(find (fun (k,_) -> same k) calls))
           with Failure _ -> None) with
      Some ctac -> let tac,used = ctac i in
                   (tac THEN norm THEN again (i+used) leaf) g
    | None -> (ARM_BSTEP_TAC execth (i--i) THEN norm THEN again (i+1) leaf) g;;

(* Close a case whose last assumption contradicts the arithmetic facts      *)
(* among the assumptions, after rewriting it with rws (and val of words).    *)

let rec bstep_arith_fact t =
  match t with
    Comb(Const("~",_),a) -> bstep_arith_fact a
  | Comb(Comb(Const("/\\",_),a),b) -> bstep_arith_fact a && bstep_arith_fact b
  | Comb(Comb(Const(("<"|"<="),_),_),_) -> true
  | Comb(Comb(Const("=",_),a),_) -> type_of a = `:num`
  | _ -> false;;

let BSTEP_ARITH_KILL_TAC (rws:thm list) : tactic = fun (asl,w) ->
  match asl with
    [] -> failwith "BSTEP_ARITH_KILL_TAC"
  | (_,cth)::rest ->
      let ar = filter (fun (_,th) -> bstep_arith_fact (concl th) &&
                 not(exists (fun v -> type_of v = `:armstate`)
                            (frees(concl th)))) rest in
      let tm = itlist (curry mk_imp) (map (concl o snd) ar) (mk_neg(concl cth)) in
      let hs = map (fun h -> ("",ASSUME h)) (itlist (union o hyp) rws []) in
      let th = TAC_PROOF((hs,tm),
        REWRITE_TAC(rws @ [VAL_EQ_0; WORD_SUB_EQ_0]) THEN
        REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC rws THEN
        CONV_TAC(DEPTH_CONV VAL_WORD_NUMERAL_CONV) THEN
        REPEAT DISCH_TAC THEN ASM_ARITH_TAC) in
      let nth = rev_itlist (fun (_,a) th -> MP th a) ar th in
      CONTR_TAC(MP (NOT_ELIM nth) cth) (asl,w);;
