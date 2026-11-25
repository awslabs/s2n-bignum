(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sets of addresses in frames and in memory-safety statements.              *)
(*                                                                           *)
(* A frame such as MAYCHANGE [memory :> bytes(a,n)] names a region by its    *)
(* base and length. The memory that an external allocator owns is not such   *)
(* a region: it is a set of addresses that the proof does not know, only     *)
(* facts about it (for example that a block it returned is inside it and     *)
(* that the stack is outside it). This file gives                            *)
(*                                                                           *)
(*  - memrange (a,k), the set of the k addresses from a (modulo the word     *)
(*    size), with the link to nonoverlapping and contained;                  *)
(*                                                                           *)
(*  - footprint t, the component of a memory (a function from addresses) of  *)
(*    the addresses in the set t: MAYCHANGE [memory :> footprint t] is "the  *)
(*    memory may change at the addresses in t", and the value read,          *)
(*    read (memory :> footprint t) s, is the memory at t (and a fixed value  *)
(*    elsewhere), so a predicate of it depends only on the memory at t;      *)
(*                                                                           *)
(*  - memaccess_inset e rs ws, the memory safety of a list of events in      *)
(*    terms of sets: every load is in rs and every store in ws, with the     *)
(*    link to the list form memaccess_inbounds;                              *)
(*                                                                           *)
(*  - the proofs that the frame machinery needs for these components, from   *)
(*    the facts among the component assumptions (set_component_assumptions) *)
(*    of the forms                                                           *)
(*                                                                           *)
(*      memrange(a,k) SUBSET t,  s SUBSET t,  DISJOINT (memrange(a,k)) t,    *)
(*      DISJOINT t (memrange(a,k)),  DISJOINT s t:                           *)
(*                                                                           *)
(*      orthogonality of memory :> footprint t and memory :> bytes(a,k) (or  *)
(*      bytes64 a, ...) when the region is outside t, of two footprints of   *)
(*      disjoint sets, and of two byte regions that are on different sides   *)
(*      of a set (one inside, one outside); and the absorption of a write    *)
(*      to a region or a footprint inside t into a clause                    *)
(*      MAYCHANGE [memory :> footprint t] of a frame. They are installed as  *)
(*      orthogonality_extensions (common/components.ml) and                  *)
(*      maychange_absorb_extensions (common/relational.ml), so that          *)
(*      frame_keeps, maychange_absorb, the step tactics of bstep and         *)
(*      GEN_BSTEP_CALL_TAC use them.                                         *)
(*                                                                           *)
(* A region is inside or outside a set if it is part of a region named in    *)
(* such a fact: the same base and length, or the same base (in the forms     *)
(* word_add b (word n), word_sub b (word n) and word (x + n) with numerals   *)
(* n) and numeral offsets and lengths with the region within the other, or   *)
(* the k bytes below an address with k <= K a fact for a numeral K. A set is *)
(* within another by a chain of SUBSET facts, and A UNION B is within t if A *)
(* and B are. Nothing else is searched for: the proofs that need other facts *)
(* derive them first.                                                        *)
(*                                                                           *)
(*  - MEMACCESS_INSET_TAC, for the final goal of a safety proof              *)
(*    ?e2. t = APPEND e2 e /\ memaccess_inset e2 rs ws, by the same facts.   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Ranges of addresses as sets.                                              *)
(* ------------------------------------------------------------------------- *)

let memrange = new_definition
 `memrange (a:N word,k) = {word_add a (word i) | i < k}`;;

let IN_MEMRANGE = prove
 (`!(a:N word) k x. x IN memrange(a,k) <=> ?i. i < k /\ x = word_add a (word i)`,
  REWRITE_TAC[memrange; IN_ELIM_THM] THEN MESON_TAC[]);;

let MEMRANGE_0 = prove
 (`!a:N word. memrange(a,0) = {}`,
  REWRITE_TAC[EXTENSION; IN_MEMRANGE; NOT_IN_EMPTY; LT]);;

let MEMRANGE_REFL = prove
 (`!(a:N word) k. 0 < k ==> a IN memrange(a,k)`,
  REWRITE_TAC[IN_MEMRANGE] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN
  ASM_REWRITE_TAC[WORD_ADD_0]);;

let FINITE_MEMRANGE = prove
 (`!(a:N word) k. FINITE(memrange(a,k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memrange] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT]);;

(* A part at an offset: the offset and the length within the length.         *)

let MEMRANGE_OFFSET_SUBSET = prove
 (`!(a:N word) m k l.
        m + k <= l ==> memrange(word_add a (word m),k) SUBSET memrange(a,l)`,
  REWRITE_TAC[SUBSET; IN_MEMRANGE] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `m + i:num` THEN
  ASM_REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC] THEN ASM_ARITH_TAC);;

let MEMRANGE_PREFIX_SUBSET = prove
 (`!(a:N word) k l. k <= l ==> memrange(a,k) SUBSET memrange(a,l)`,
  MESON_TAC[MEMRANGE_OFFSET_SUBSET; WORD_ADD_0; ADD_CLAUSES]);;

(* The last k of the l bytes below an address, k <= l.                       *)

let MEMRANGE_BELOW_SUBSET = prove
 (`!(a:N word) k l.
        k <= l
        ==> memrange(word_sub a (word k),k) SUBSET
            memrange(word_sub a (word l),l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub a (word k):N word =
                word_add (word_sub a (word l)) (word(l - k))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE;
    MATCH_MP_TAC MEMRANGE_OFFSET_SUBSET THEN ASM_ARITH_TAC]);;

let NONOVERLAPPING_MEMRANGE = prove
 (`!(a:N word) k b l.
        nonoverlapping (a,k) (b,l) <=>
        DISJOINT (memrange(a,k)) (memrange(b,l))`,
  REWRITE_TAC[NONOVERLAPPING; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
              IN_MEMRANGE] THEN
  MESON_TAC[]);;

let CONTAINED_MEMRANGE = prove
 (`!(a:N word) k b l.
        contained (a,k) (b,l) <=> memrange(a,k) SUBSET memrange(b,l)`,
  REWRITE_TAC[CONTAINED; SUBSET; IN_MEMRANGE] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The component of a memory at a set of addresses.                          *)
(* ------------------------------------------------------------------------- *)

let footprint = new_definition
 `(footprint:(A->bool)->((A->B),(A->B))component) t =
    component((\m a. if a IN t then m a else @x. T),
              (\y m a. if a IN t then y a else m a))`;;

let READ_FOOTPRINT = prove
 (`!(t:A->bool) (m:A->B).
        read (footprint t) m = \a. if a IN t then m a else @x. T`,
  REWRITE_TAC[footprint; read]);;

let WRITE_FOOTPRINT = prove
 (`!(t:A->bool) (y:A->B) m.
        write (footprint t) y m = \a. if a IN t then y a else m a`,
  REWRITE_TAC[footprint; write]);;

let EXTENSIONALLY_VALID_COMPONENT_FOOTPRINT = prove
 (`!t:A->bool. extensionally_valid_component
                 (footprint t:((A->B),(A->B))component)`,
  GEN_TAC THEN REWRITE_TAC[extensionally_valid_component] THEN
  REWRITE_TAC[READ_FOOTPRINT; WRITE_FOOTPRINT; FUN_EQ_THM] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `\(y:A->B) a. if a IN t then y a else @x:B. T` THEN
    REWRITE_TAC[] THEN MESON_TAC[];
    MESON_TAC[];
    MESON_TAC[]]);;

let WEAKLY_VALID_COMPONENT_FOOTPRINT = prove
 (`!t:A->bool. weakly_valid_component
                 (footprint t:((A->B),(A->B))component)`,
  SIMP_TAC[EXTENSIONALLY_VALID_IMP_WEAKLY_VALID_COMPONENT;
           EXTENSIONALLY_VALID_COMPONENT_FOOTPRINT]);;

add_extensionally_valid_component_thms
  [EXTENSIONALLY_VALID_COMPONENT_FOOTPRINT];;
add_weakly_valid_component_thms [WEAKLY_VALID_COMPONENT_FOOTPRINT];;

(* Two states have the same footprint at t iff they agree at t.              *)

let READ_FOOTPRINT_EQ = prove
 (`!(c:(S,A->B)component) t s s'.
        read (c :> footprint t) s = read (c :> footprint t) s' <=>
        !a. a IN t ==> read c s a = read c s' a`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_FOOTPRINT; FUN_EQ_THM] THEN
  MESON_TAC[]);;

(* What a part of the memory inside t reads from the footprint.              *)

let READ_ELEMENT_FOOTPRINT = prove
 (`!(t:A->bool) a (m:A->B).
        a IN t ==> read (element a) (read (footprint t) m) = read (element a) m`,
  SIMP_TAC[READ_ELEMENT; READ_FOOTPRINT]);;

let READ_BYTES_FOOTPRINT = prove
 (`!(t:N word->bool) a k m.
        memrange(a,k) SUBSET t
        ==> read (bytes(a,k)) (read (footprint t) m) = read (bytes(a,k)) m`,
  REWRITE_TAC[SUBSET; IN_MEMRANGE; READ_BYTES; READ_FOOTPRINT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let READ_BYTES_SUB_FOOTPRINT = prove
 (`!(t:N word->bool) a k (c:(num,V)component) m.
        memrange(a,k) SUBSET t
        ==> read (bytes(a,k) :> c) (read (footprint t) m) =
            read (bytes(a,k) :> c) m`,
  SIMP_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_FOOTPRINT]);;

let READ_MEMORY_BYTES_FOOTPRINT = prove
 (`!(mem:(S,N word->byte)component) t a k s.
        memrange(a,k) SUBSET t
        ==> read (bytes(a,k)) (read (mem :> footprint t) s) =
            read (mem :> bytes(a,k)) s`,
  SIMP_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_FOOTPRINT]);;

let READ_MEMORY_BYTES_SUB_FOOTPRINT = prove
 (`!(mem:(S,N word->byte)component) t a k (c:(num,V)component) s.
        memrange(a,k) SUBSET t
        ==> read (bytes(a,k) :> c) (read (mem :> footprint t) s) =
            read (mem :> bytes(a,k) :> c) s`,
  SIMP_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_FOOTPRINT]);;

(* A smaller footprint is a function of a larger one.                        *)

let READ_FOOTPRINT_SUBSET = prove
 (`!(c:(S,A->B)component) s t st.
        s SUBSET t
        ==> read (c :> footprint s) st =
            read (footprint s) (read (c :> footprint t) st)`,
  REWRITE_TAC[SUBSET; READ_COMPONENT_COMPOSE; READ_FOOTPRINT; FUN_EQ_THM] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Orthogonality and subsumption.                                            *)
(* ------------------------------------------------------------------------- *)

let ORTHOGONAL_COMPONENTS_FOOTPRINT = prove
 (`!(s:A->bool) t.
        DISJOINT s t
        ==> orthogonal_components (footprint s:((A->B),(A->B))component)
                                  (footprint t)`,
  REWRITE_TAC[orthogonal_components; READ_FOOTPRINT; WRITE_FOOTPRINT;
              FUN_EQ_THM; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let ORTHOGONAL_COMPONENTS_ELEMENT_FOOTPRINT = prove
 (`!(a:A) t.
        ~(a IN t)
        ==> orthogonal_components (element a:((A->B),B)component)
                                  (footprint t)`,
  REWRITE_TAC[orthogonal_components; READ_FOOTPRINT; WRITE_FOOTPRINT;
              element; read; write; FUN_EQ_THM] THEN
  MESON_TAC[]);;

let ORTHOGONAL_COMPONENTS_BYTES_FOOTPRINT = prove
 (`!(a:N word) k t.
        DISJOINT (memrange(a,k)) t
        ==> orthogonal_components (bytes(a,k)) (footprint t)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[ORTHOGONAL_WEAK_COMPONENTS; EXTENSIONALLY_VALID_COMPONENT_BYTES;
           EXTENSIONALLY_VALID_COMPONENT_FOOTPRINT] THEN
  REWRITE_TAC[ELEMENT_EXTENSIONALITY; READ_ELEMENT_WRITE_BYTES] THEN
  REWRITE_TAC[WRITE_FOOTPRINT; READ_ELEMENT;
              REWRITE_RULE[READ_ELEMENT] READ_ELEMENT_WRITE_BYTES] THEN
  MAP_EVERY X_GEN_TAC [`y:num`; `z:N word->byte`; `s:N word->byte`;
                       `x:N word`] THEN
  ASM_CASES_TAC `(x:N word) IN t` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DISJOINT]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_MEMRANGE] THEN
  DISCH_THEN(MP_TAC o SPEC `x:N word`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  EXISTS_TAC `val(word_sub (x:N word) a)` THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN CONV_TAC WORD_RULE);;

(* With the memory component m (memory in the instances) and a part c of a   *)
(* region, as asword in bytes64 a = bytes(a,8) :> asword.                    *)

let ORTHOGONAL_MEMORY_BYTES_FOOTPRINT = prove
 (`!(m:(S,N word->byte)component) a k t.
        valid_component m /\ DISJOINT (memrange(a,k)) t
        ==> orthogonal_components (m :> bytes(a,k)) (m :> footprint t)`,
  SIMP_TAC[ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT;
           ORTHOGONAL_COMPONENTS_BYTES_FOOTPRINT]);;

let ORTHOGONAL_MEMORY_BYTES_SUB_FOOTPRINT = prove
 (`!(m:(S,N word->byte)component) a k t (c:(num,V)component).
        valid_component m /\ DISJOINT (memrange(a,k)) t
        ==> orthogonal_components (m :> bytes(a,k) :> c) (m :> footprint t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPONENT_COMPOSE_ASSOC] THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN
  ASM_SIMP_TAC[ORTHOGONAL_MEMORY_BYTES_FOOTPRINT]);;

let ORTHOGONAL_MEMORY_FOOTPRINT_FOOTPRINT = prove
 (`!(m:(S,A->B)component) s t.
        valid_component m /\ DISJOINT s t
        ==> orthogonal_components (m :> footprint s) (m :> footprint t)`,
  SIMP_TAC[ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT;
           ORTHOGONAL_COMPONENTS_FOOTPRINT]);;

(* Two regions on different sides of a set are disjoint.                     *)

let DISJOINT_MEMRANGE_SIDES = prove
 (`!(a:N word) k b l t.
        memrange(a,k) SUBSET t /\ DISJOINT (memrange(b,l)) t
        ==> nonoverlapping (a,k) (b,l)`,
  REWRITE_TAC[NONOVERLAPPING_MEMRANGE] THEN SET_TAC[]);;

let SUBSUMED_ASSIGNS_FOOTPRINT = prove
 (`!(s:A->bool) t.
        s SUBSET t
        ==> ASSIGNS (footprint s:((A->B),(A->B))component) subsumed
            ASSIGNS (footprint t)`,
  REWRITE_TAC[subsumed; ASSIGNS_THM; WRITE_FOOTPRINT; SUBSET; FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\a:A. if a IN s then (y:A->B) a else x a` THEN
  ASM_MESON_TAC[]);;

let SUBSUMED_ASSIGNS_BYTES_FOOTPRINT = prove
 (`!(a:N word) k t.
        memrange(a,k) SUBSET t
        ==> ASSIGNS (bytes(a,k)) subsumed ASSIGNS (footprint t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[subsumed; ASSIGNS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:N word->byte`; `m':N word->byte`] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num` (SUBST1_TAC o SYM)) THEN
  EXISTS_TAC `write (bytes(a:N word,k)) y m` THEN
  REWRITE_TAC[WRITE_FOOTPRINT; FUN_EQ_THM] THEN X_GEN_TAC `x:N word` THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`a:N word`; `x:N word`; `k:num`; `y:num`; `m:N word->byte`]
    READ_ELEMENT_WRITE_BYTES) THEN
  REWRITE_TAC[READ_ELEMENT] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:N word) IN t` (fun th -> ASM_MESON_TAC[th]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[IN_MEMRANGE] THEN EXISTS_TAC `val(word_sub (x:N word) a)` THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN CONV_TAC WORD_RULE);;

let MAYCHANGE_MEMORY_FOOTPRINT_SUBSUMED = prove
 (`!(m:(S,A->B)component) s t.
        s SUBSET t
        ==> MAYCHANGE [m :> footprint s] subsumed ASSIGNS (m :> footprint t)`,
  SIMP_TAC[MAYCHANGE_SING; SUBSUMED_ASSIGNS_SUBCOMPONENTS;
           SUBSUMED_ASSIGNS_FOOTPRINT]);;

let MAYCHANGE_MEMORY_BYTES_FOOTPRINT_SUBSUMED = prove
 (`!(m:(S,N word->byte)component) a k t.
        memrange(a,k) SUBSET t
        ==> MAYCHANGE [m :> bytes(a,k)] subsumed ASSIGNS (m :> footprint t)`,
  SIMP_TAC[MAYCHANGE_SING; SUBSUMED_ASSIGNS_SUBCOMPONENTS;
           SUBSUMED_ASSIGNS_BYTES_FOOTPRINT]);;

let MAYCHANGE_MEMORY_BYTES_SUB_FOOTPRINT_SUBSUMED = prove
 (`!(m:(S,N word->byte)component) a k t (c:(num,V)component).
        memrange(a,k) SUBSET t
        ==> MAYCHANGE [m :> bytes(a,k) :> c] subsumed
            ASSIGNS (m :> footprint t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_SING; COMPONENT_COMPOSE_ASSOC] THEN
  MP_TAC(ISPECL [`m:(S,N word->byte)component :> bytes(a,k)`;
                 `c:(num,V)component`] SUBSUMED_ASSIGNS_SUBCOMPONENT) THEN
  MP_TAC(ISPECL [`m:(S,N word->byte)component`; `bytes(a:N word,k)`;
                 `footprint(t:N word->bool):((N word->byte),(N word->byte))component`]
         SUBSUMED_ASSIGNS_SUBCOMPONENTS) THEN
  ASM_SIMP_TAC[SUBSUMED_ASSIGNS_BYTES_FOOTPRINT] THEN
  REWRITE_TAC[subsumed] THEN MESON_TAC[]);;

(* A footprint of a union as the footprints in sequence: with a frame       *)
(* MAYCHANGE [m :> footprint (s1 UNION ... UNION sn)] (one clause, so that   *)
(* MAYCHANGE_IDEMPOT_TAC proves C ,, C = C for loop rules such as           *)
(* ENSURES_MEASURE_INDUCT), the frame of the separate regions follows.       *)

let MAYCHANGE_FOOTPRINT_UNION_SUBSUMED = prove
 (`!(m:(S,A->B)component) s t.
        valid_component m
        ==> MAYCHANGE [m :> footprint (s UNION t)] subsumed
            MAYCHANGE [m :> footprint s] ,, MAYCHANGE [m :> footprint t]`,
  REWRITE_TAC[MAYCHANGE_SING; subsumed; seq; ASSIGNS_THM] THEN
  REWRITE_TAC[valid_component] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`s0:S`; `s2:S`] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->B` (SUBST1_TAC o SYM)) THEN
  EXISTS_TAC `write ((m:(S,A->B)component) :> footprint (s:A->bool))
                    (f:A->B) (s0:S)` THEN
  CONJ_TAC THENL [MESON_TAC[]; EXISTS_TAC `f:A->B`] THEN
  ASM_REWRITE_TAC[WRITE_COMPONENT_COMPOSE; READ_COMPONENT_COMPOSE;
                  WRITE_FOOTPRINT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; IN_UNION] THEN
  MESON_TAC[]);;

let FOOTPRINT_UNION_SUBSUMED_SEQ = prove
 (`!(m:(S,A->B)component) s t (X:S->S->bool) (Y:S->S->bool).
        valid_component m /\
        MAYCHANGE [m :> footprint s] subsumed X /\
        MAYCHANGE [m :> footprint t] subsumed Y
        ==> MAYCHANGE [m :> footprint (s UNION t)] subsumed X ,, Y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`s:A->bool`; `t:A->bool`] o
    MATCH_MP MAYCHANGE_FOOTPRINT_UNION_SUBSUMED) MP_TAC) THEN
  REWRITE_TAC[subsumed; seq] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Memory safety with sets.                                                  *)
(* ------------------------------------------------------------------------- *)

let event_loads = define
 `(event_loads (EventLoad (a,k):(A)address_uarch_event) = memrange(a,k)) /\
  (event_loads (EventStore (a,k):(A)address_uarch_event) = {}) /\
  (event_loads (EventJump (x,y):(A)address_uarch_event) = {}) /\
  (event_loads (EventX86PEXT p:(A)address_uarch_event) = {}) /\
  (event_loads (EventX86POPCNT q:(A)address_uarch_event) = {}) /\
  (event_loads (EventX86Opmask r:(A)address_uarch_event) = {})`;;

let event_stores = define
 `(event_stores (EventLoad (a,k):(A)address_uarch_event) = {}) /\
  (event_stores (EventStore (a,k):(A)address_uarch_event) = memrange(a,k)) /\
  (event_stores (EventJump (x,y):(A)address_uarch_event) = {}) /\
  (event_stores (EventX86PEXT p:(A)address_uarch_event) = {}) /\
  (event_stores (EventX86POPCNT q:(A)address_uarch_event) = {}) /\
  (event_stores (EventX86Opmask r:(A)address_uarch_event) = {})`;;

let memaccess_inset = new_definition
 `memaccess_inset (e:((A)address_uarch_event)list) rs ws <=>
    ALL (\x. event_loads x SUBSET rs /\ event_stores x SUBSET ws) e`;;

let MEMACCESS_INSET_CLAUSES = prove
 (`(!rs ws. memaccess_inset ([]:((A)address_uarch_event)list) rs ws) /\
   (!h t rs ws. memaccess_inset (CONS (h:(A)address_uarch_event) t) rs ws <=>
                event_loads h SUBSET rs /\ event_stores h SUBSET ws /\
                memaccess_inset t rs ws)`,
  REWRITE_TAC[memaccess_inset; ALL; CONJ_ASSOC]);;

let MEMACCESS_INSET_APPEND = prove
 (`!(e1:((A)address_uarch_event)list) e2 rs ws.
        memaccess_inset (APPEND e1 e2) rs ws <=>
        memaccess_inset e1 rs ws /\ memaccess_inset e2 rs ws`,
  REWRITE_TAC[memaccess_inset; ALL_APPEND]);;

let MEMACCESS_INSET_MONO = prove
 (`!(e:((A)address_uarch_event)list) rs ws rs' ws'.
        rs SUBSET rs' /\ ws SUBSET ws' /\ memaccess_inset e rs ws
        ==> memaccess_inset e rs' ws'`,
  REWRITE_TAC[memaccess_inset; GSYM ALL_MEM] THEN
  MESON_TAC[SUBSET_TRANS]);;

(* The list form: a region of the list is the set of its addresses.          *)

let memranges = new_definition
 `memranges (l:(A word#num)list) = {x | EX (\r. x IN memrange r) l}`;;

let MEMRANGES_CLAUSES = prove
 (`memranges ([]:(A word#num)list) = {} /\
   (!(r:A word#num) l. memranges (CONS r l) = memrange r UNION memranges l)`,
  REWRITE_TAC[memranges; EX; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNION]);;

let MEMACCESS_INBOUNDS_INSET = prove
 (`!(e:((A)address_uarch_event)list) rr wr.
        memaccess_inbounds e rr wr
        ==> memaccess_inset e (memranges rr) (memranges wr)`,
  let lemma = prove
   (`!(a:A word) k l.
        EX (\r. contained_modulo (2 EXP dimindex(:A)) (val a,k)
                                 (val (FST r),SND r)) l
        ==> memrange(a,k) SUBSET memranges l`,
    REWRITE_TAC[GSYM EX_MEM; EXISTS_PAIR_THM; FST; SND] THEN
    REWRITE_TAC[GSYM contained; CONTAINED_MEMRANGE; memranges] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM EX_MEM] THEN MESON_TAC[]) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[memaccess_inbounds_def; memaccess_inset; GSYM ALL_MEM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `ev:(A)address_uarch_event` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  SPEC_TAC(`ev:(A)address_uarch_event`,`ev:(A)address_uarch_event`) THEN
  MATCH_MP_TAC address_uarch_event_INDUCT THEN
  REWRITE_TAC[event_loads; event_stores; EMPTY_SUBSET; FORALL_PAIR_THM] THEN
  REWRITE_TAC[lemma]);;

(* ------------------------------------------------------------------------- *)
(* Set facts from the component assumptions.                                 *)
(*                                                                           *)
(* memrange_subset_rule (a,k) (b,l) proves |- memrange(a,k) SUBSET          *)
(* memrange(b,l): for the same region; for a part at a numeral offset from   *)
(* the same base, with numeral lengths (or sums and products of numerals,    *)
(* reduced first; addresses in the forms word_add b                          *)
(* (word n), word_sub b (word n) and word (x + n), nested); for the same     *)
(* base and lengths k <= l by ARITH_RULE; for the k bytes below an address   *)
(* with k <= K a component assumption (K a numeral), via the K bytes below   *)
(* it. footprint_subset_rule s t and footprint_disjoint_rule s t prove       *)
(* |- s SUBSET t and |- DISJOINT s t from the facts among the component     *)
(* assumptions, by the search described at the top of this file.            *)
(* All fail if they find no proof.                                           *)
(* ------------------------------------------------------------------------- *)

let footprint_word_size ty =
  match ty with
    Tyapp("word",[n]) -> dest_finty n
  | _ -> failwith "footprint_word_size";;

(* An address as a base and a numeral offset modulo the word size.           *)

let rec footprint_address_split a =
  match a with
    Comb(Comb(Const("word_add",_),b),Comb(Const("word",_),n))
      when is_numeral n ->
      let b1,n1 = footprint_address_split b in b1,n1 +/ dest_numeral n
  | Comb(Comb(Const("word_sub",_),b),Comb(Const("word",_),n))
      when is_numeral n ->
      let b1,n1 = footprint_address_split b in b1,n1 -/ dest_numeral n
  | Comb(Const("word",_) as w,Comb(Comb(Const("+",_),x),n))
      when is_numeral n && not(is_numeral x) ->
      let b1,n1 = footprint_address_split (mk_comb(w,x)) in
      b1,n1 +/ dest_numeral n
  | _ -> a,num_0;;

(* Addresses in one form, word_add base (word n) with a numeral n reduced    *)
(* modulo the word size (or the base alone), from the forms word_add a       *)
(* (word n), word_sub a (word n) and word (x + n): to prove two forms equal. *)

let WORD_SUB_AS_ADD_NEG = WORD_RULE
 `!x:N word y. word_sub x y = word_add x (word_neg y)`;;

let FOOTPRINT_ADDRESS_CONV =
  REWRITE_CONV[WORD_SUB_AS_ADD_NEG; WORD_ADD; GSYM WORD_ADD_ASSOC] THENC
  DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[WORD_ADD_0];;

let footprint_address_eq a b =
  if compare a b = 0 then REFL a else
  let tha = FOOTPRINT_ADDRESS_CONV a and thb = FOOTPRINT_ADDRESS_CONV b in
  if compare (rand(concl tha)) (rand(concl thb)) = 0 then TRANS tha (SYM thb)
  else failwith "footprint_address_eq";;

let memrange_subset_rule =
  let rm r = mk_icomb(`memrange:N word#num->N word->bool`,mk_pair r) in
  let sub x y = mk_icomb(mk_icomb(`(SUBSET):(A->bool)->(A->bool)->bool`,x),y) in
  let rec go (a,k) (b,l) =
    if compare a b = 0 && compare k l = 0 then ISPEC (rm(a,k)) SUBSET_REFL else
    if is_numeral k && is_numeral l then
      let pa,oa = footprint_address_split a
      and pb,ob = footprint_address_split b in
      if compare pa pb <> 0 then failwith "memrange_subset_rule" else
      let m = power_num num_2 (footprint_word_size(type_of a)) in
      let d = mod_num (oa -/ ob) m in
      if d +/ dest_numeral k >/ dest_numeral l then
        failwith "memrange_subset_rule" else
      let nty = hd(snd(dest_type(type_of a))) in
      let a' = mk_comb(mk_icomb(`word_add:N word->N word->N word`,b),
                       mk_comb(mk_const("word",[nty,`:N`]),mk_numeral d)) in
      let eq = footprint_address_eq a a' in
      let th = PART_MATCH rand MEMRANGE_OFFSET_SUBSET (sub (rm(a',k)) (rm(b,l))) in
      let th = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
      if compare a a' = 0 then th else SUBS [SYM eq] th
    else if compare a b = 0 &&
            can ARITH_RULE (mk_binary "<=" (k,l)) then
      let th = PART_MATCH rand MEMRANGE_PREFIX_SUBSET (sub (rm(a,k)) (rm(b,l))) in
      MP th (ARITH_RULE(lhand(concl th)))
    else
    (* the k bytes below c, k <= K a numeral by a component assumption *)
    match a with
      Comb(Comb(Const("word_sub",_) as ws,c),Comb(Const("word",_) as wd,k0))
        when compare k0 k = 0 && not(is_numeral k) ->
        let kth = find (fun th -> match concl th with
            Comb(Comb(Const("<=",_),x),kk) -> compare x k = 0 && is_numeral kk
          | _ -> false) (component_assumptions ()) in
        let kk = rand(concl kth) in
        let th1 = MP (ISPECL [c;k;kk] MEMRANGE_BELOW_SUBSET) kth in
        let th2 = go (mk_comb(mk_comb(ws,c),mk_comb(wd,kk)),kk) (b,l) in
        MATCH_MP SUBSET_TRANS (CONJ th1 th2)
    | _ -> failwith "memrange_subset_rule" in
  (* Lengths that are sums or products of numerals, such as the                *)
  (* libsnappy_rw + libsnappy_rw_size of a layout, are reduced to numerals     *)
  (* first, and the theorem is stated with the lengths as given.               *)
  let red t =
    if is_numeral t then None else
    try let th = NUM_REDUCE_CONV t in
        if is_numeral(rand(concl th)) then Some th else None
    with Failure _ -> None in
  let back kth lth th =
    let conv eo = match eo with
        Some eq -> RAND_CONV(RAND_CONV(K(SYM eq)))
      | None -> ALL_CONV in
    CONV_RULE(LAND_CONV(conv kth) THENC RAND_CONV(conv lth)) th in
  fun (a,k) (b,l) ->
    match red k,red l with
      None,None -> go (a,k) (b,l)
    | kth,lth ->
        let k' = match kth with Some eq -> rand(concl eq) | None -> k
        and l' = match lth with Some eq -> rand(concl eq) | None -> l in
        try go (a,k) (b,l) with Failure _ -> back kth lth (go (a,k') (b,l'));;

(* The SUBSET and DISJOINT facts among the component assumptions, the        *)
(* DISJOINT ones in both orders.                                             *)

let footprint_facts () =
  let subs = ref [] and disjs = ref [] in
  List.iter (fun th ->
      match concl th with
        Comb(Comb(Const("SUBSET",_),s),t) -> subs := (s,t,th) :: !subs
      | Comb(Comb(Const("DISJOINT",_),s),t) ->
          disjs := (s,t,th) :: (t,s,CONV_RULE (REWR_CONV DISJOINT_SYM) th) ::
                   !disjs
      | _ -> ()) (component_assumptions ());
  !subs,!disjs;;

let dest_memrange tm =
  match tm with
    Comb(Const("memrange",_),Comb(Comb(Const(",",_),a),k)) -> a,k
  | _ -> failwith "dest_memrange";;

let footprint_search_depth = ref 4;;

let footprint_subset_rule =
  let union_l = SPEC_ALL UNION_SUBSET
  and sub_ul = CONJUNCT1 SUBSET_UNION and sub_ur = CONJUNCT2 SUBSET_UNION in
  let trans2 th1 th2 = MATCH_MP SUBSET_TRANS (CONJ th1 th2) in
  fun s t ->
    let subs,_ = footprint_facts () in
    let rec go depth s t =
      if compare s t = 0 then ISPEC s SUBSET_REFL else
      match s with
        Const("EMPTY",_) -> ISPEC t EMPTY_SUBSET
      | Comb(Comb(Const("UNION",_),x),y) ->
          EQ_MP (SYM(PART_MATCH lhand union_l (mk_icomb(mk_icomb(
                    `(SUBSET):(A->bool)->(A->bool)->bool`,s),t))))
                (CONJ (go depth x t) (go depth y t))
      | _ ->
      try (match t with
             Comb(Comb(Const("UNION",_),x),y) ->
               (try trans2 (go depth s x) (ISPECL [x;y] sub_ul)
                with Failure _ -> trans2 (go depth s y) (ISPECL [y;x] sub_ur))
           | _ -> failwith "")
      with Failure _ ->
      try memrange_subset_rule (dest_memrange s) (dest_memrange t)
      with Failure _ ->
      if depth <= 0 then failwith "footprint_subset_rule" else
      tryfind (fun (x,u,th) ->
          let th1 =
            if compare x s = 0 then th else
            trans2 (memrange_subset_rule (dest_memrange s) (dest_memrange x))
                   th in
          if compare u t = 0 then th1 else trans2 th1 (go (depth - 1) u t))
        subs in
    try go !footprint_search_depth s t
    with Failure _ -> failwith "footprint_subset_rule";;

let DISJOINT_SUBSETS = prove
 (`!(s:A->bool) t x y.
        s SUBSET x /\ t SUBSET y /\ DISJOINT x y ==> DISJOINT s t`,
  SET_TAC[]);;

let DISJOINT_UNION_CLAUSES = prove
 (`(!(s:A->bool) t u. DISJOINT s t /\ DISJOINT s u ==> DISJOINT s (t UNION u)) /\
   (!(s:A->bool) t u. DISJOINT s u /\ DISJOINT t u ==> DISJOINT (s UNION t) u)`,
  SET_TAC[]);;

let footprint_disjoint_rule s t =
  let _,disjs = footprint_facts () in
  let rec go s t =
    match s,t with
      Comb(Comb(Const("UNION",_),x),y),_ ->
        MATCH_MP (CONJUNCT2 DISJOINT_UNION_CLAUSES) (CONJ (go x t) (go y t))
    | _,Comb(Comb(Const("UNION",_),x),y) ->
        MATCH_MP (CONJUNCT1 DISJOINT_UNION_CLAUSES) (CONJ (go s x) (go s y))
    | _ ->
        tryfind (fun (x,y,th) ->
            if compare x s = 0 && compare y t = 0 then th else
            let sx = footprint_subset_rule s x
            and ty = footprint_subset_rule t y in
            MATCH_MP DISJOINT_SUBSETS (CONJ sx (CONJ ty th))) disjs in
  try go s t with Failure _ -> failwith "footprint_disjoint_rule";;

(* ------------------------------------------------------------------------- *)
(* The extensions of the frame machinery.                                    *)
(* ------------------------------------------------------------------------- *)

(* m :> footprint t as (m,t).                                                *)

let dest_memory_footprint c =
  match c with
    Comb(Comb(Const(":>",_),m),Comb(Const("footprint",_),t)) -> m,t
  | _ -> failwith "dest_memory_footprint";;

(* A region of m: (m,a,k,|- c = m :> bytes(a,k) :> d), for c = m :> bytes   *)
(* (a,k) (d = entirety), m :> bytes8 a ... bytes256 a (d = asword) and       *)
(* m :> bytelist(a,k), the memory being the m of a footprint.               *)

let footprint_region =
  let sized = map (fun th -> fst(dest_const(fst(strip_comb(lhs(snd(strip_forall
                (concl th))))))),th)
    [bytes8; bytes16; bytes32; bytes64; bytes128; bytes256; bytelist] in
  fun c ->
    match c with
      Comb(Comb(Const(":>",_) as cop,m),
           (Comb(Const("bytes",_),Comb(Comb(Const(",",_),a),k)) as r)) ->
        m,a,k,AP_TERM (mk_comb(cop,m))
                (SYM(ISPEC r (CONJUNCT1 COMPOSE_ENTIRETY)))
    | Comb(Comb(Const(":>",_) as cop,m),(Comb(Const(n,_),x) as r))
        when List.mem_assoc n sized ->
        let eq = REWR_CONV (List.assoc n sized) r in
        let a,k = match rand(concl eq) with
            Comb(Comb(Const(":>",_),Comb(Const("bytes",_),
                  Comb(Comb(Const(",",_),a),k))),_) -> a,k
          | _ -> failwith "footprint_region" in
        m,a,k,AP_TERM (mk_comb(cop,m)) eq
    | _ -> failwith "footprint_region";;

let footprint_valid =
  let cache = par_local (fun () -> (Termtbl.create 4 : thm Termtbl.t)) in
  fun m ->
    let cache = cache () in
    try Termtbl.find cache m with Not_found ->
    let th = VALID_COMPONENT_CONV
               (mk_icomb(`valid_component:(S,V)component->bool`,m)) in
    let th = if is_eq(concl th) then EQT_ELIM th else th in
    Termtbl.replace cache m th; th;;

let ORTHOGONAL_MEMORY_BYTES_SUB_DISJOINT = prove
 (`!(m:(S,N word->byte)component) a k b l (c:(num,V)component)
    (d:(num,W)component).
        valid_component m /\ DISJOINT (memrange(a,k)) (memrange(b,l))
        ==> orthogonal_components (m :> bytes(a,k) :> c)
                                  (m :> bytes(b,l) :> d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPONENT_COMPOSE_ASSOC] THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_LEFT THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_SUB_RIGHT THEN
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN
  ASM_REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES] THEN
  REWRITE_TAC[GSYM nonoverlapping; NONOVERLAPPING_MEMRANGE] THEN
  ASM_REWRITE_TAC[]);;

(* |- orthogonal_components c d: a footprint and a region outside it, two     *)
(* footprints of disjoint sets, or two regions on two sides of a set of a     *)
(* DISJOINT fact (when the offset rule does not apply).                      *)

let footprint_orthogonality c d =
  let region_footprint c m t =
    let m',a,k,eq = footprint_region c in
    if compare m m' <> 0 then failwith "footprint_orthogonality" else
    let dth = footprint_disjoint_rule (mk_icomb(`memrange:N word#num->N word->bool`,
                                                mk_pair(a,k))) t in
    let sub = rand(rand(rand(concl eq))) in
    let th = MP (ISPECL [m;a;k;t;sub] ORTHOGONAL_MEMORY_BYTES_SUB_FOOTPRINT)
                (CONJ (footprint_valid m) dth) in
    SUBS [SYM eq] th in
  match (try Some(dest_memory_footprint c) with Failure _ -> None),
        (try Some(dest_memory_footprint d) with Failure _ -> None) with
    Some(m,s),Some(m',t) ->
      if compare m m' <> 0 then failwith "footprint_orthogonality" else
      MP (ISPECL [m;s;t] ORTHOGONAL_MEMORY_FOOTPRINT_FOOTPRINT)
         (CONJ (footprint_valid m) (footprint_disjoint_rule s t))
  | None,Some(m,t) -> region_footprint c m t
  | Some(m,t),None ->
      ONCE_REWRITE_RULE[ORTHOGONAL_COMPONENTS_SYM] (region_footprint d m t)
  | None,None ->
      if (match offset_orthogonality c d with Some _ -> true | None -> false)
      then failwith "footprint_orthogonality" else
      let m,a,k,eqc = footprint_region c and m',b,l,eqd = footprint_region d in
      if compare m m' <> 0 then failwith "footprint_orthogonality" else
      let _,disjs = footprint_facts () in
      if disjs = [] then failwith "footprint_orthogonality" else
      let rm a k = mk_icomb(`memrange:N word#num->N word->bool`,mk_pair(a,k)) in
      let dth = footprint_disjoint_rule (rm a k) (rm b l) in
      let th = MP (ISPECL [m;a;k;b;l;rand(rand(rand(concl eqc)));
                           rand(rand(rand(concl eqd)))]
                     ORTHOGONAL_MEMORY_BYTES_SUB_DISJOINT)
                  (CONJ (footprint_valid m) dth) in
      SUBS [SYM eqc; SYM eqd] th;;

(* |- MAYCHANGE [d] subsumed ASSIGNS e for e = m :> footprint t and d a      *)
(* footprint of a subset of t or a region inside t.                          *)

let footprint_absorb d e =
  let m,t = dest_memory_footprint e in
  match (try Some(dest_memory_footprint d) with Failure _ -> None) with
    Some(m',s) ->
      if compare m m' <> 0 then failwith "footprint_absorb" else
      MP (ISPECL [m;s;t] MAYCHANGE_MEMORY_FOOTPRINT_SUBSUMED)
         (footprint_subset_rule s t)
  | None ->
      let m',a,k,eq = footprint_region d in
      if compare m m' <> 0 then failwith "footprint_absorb" else
      let sth = footprint_subset_rule
        (mk_icomb(`memrange:N word#num->N word->bool`,mk_pair(a,k))) t in
      let th = MP (ISPECL [m;a;k;t;rand(rand(rand(concl eq)))]
                     MAYCHANGE_MEMORY_BYTES_SUB_FOOTPRINT_SUBSUMED) sth in
      SUBS [SYM eq] th;;

orthogonality_extensions := footprint_orthogonality :: !orthogonality_extensions;;
maychange_absorb_extensions := footprint_absorb :: !maychange_absorb_extensions;;

(* ------------------------------------------------------------------------- *)
(* MEMACCESS_INSET_TAC proves a goal                                         *)
(*                                                                           *)
(*   ?e2. t = APPEND e2 e /\ memaccess_inset e2 rs ws                        *)
(*                                                                           *)
(* where t is e with events and lists (the events of callees) put in front   *)
(* by CONS and APPEND: e2 is that prefix, and each event and list is shown   *)
(* within rs and ws: an event by footprint_subset_rule, a list by an          *)
(* assumption memaccess_inset l rs' ws' with rs' and ws' within rs and ws.   *)
(* ------------------------------------------------------------------------- *)

let rec events_prefix e t =
  if compare t e = 0 then mk_const("NIL",[hd(snd(dest_type(type_of e))),`:A`])
  else match t with
    Comb(Comb(Const(("CONS"|"APPEND"),_) as c,h),t') ->
      mk_comb(mk_comb(c,h),events_prefix e t')
  | _ -> failwith "events_prefix";;

let MEMACCESS_INSET_TAC : tactic =
  fun (asl,w) ->
    let v,bod = try dest_exists w with Failure _ ->
      failwith "MEMACCESS_INSET_TAC: not ?e2. t = APPEND e2 e /\\ ..." in
    let eqt = lhand bod in
    let t = lhs eqt and e = rand(rhs eqt) in
    let x = events_prefix e t in
    set_component_assumptions (map snd asl);
    let one (asl,w) =
      match w with
        Comb(Comb(Const("SUBSET",_),s),t) ->
          ACCEPT_TAC (footprint_subset_rule s t) (asl,w)
      | Comb(Comb(Comb(Const("memaccess_inset",_),l),rs),ws) ->
          let th = snd(find (fun (_,th) -> match concl th with
              Comb(Comb(Comb(Const("memaccess_inset",_),l'),_),_) ->
                compare l l' = 0
            | _ -> false) asl) in
          let rs',ws' = rand(rator(concl th)),rand(concl th) in
          ACCEPT_TAC (MATCH_MP MEMACCESS_INSET_MONO
            (CONJ (footprint_subset_rule rs' rs)
                  (CONJ (footprint_subset_rule ws' ws) th))) (asl,w)
      | _ -> failwith "MEMACCESS_INSET_TAC" in
    (EXISTS_TAC x THEN CONJ_TAC THENL
      [REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
       REWRITE_TAC[MEMACCESS_INSET_CLAUSES; MEMACCESS_INSET_APPEND;
                   event_loads; event_stores; EMPTY_SUBSET] THEN
       REPEAT CONJ_TAC THEN one]) (asl,w);;
