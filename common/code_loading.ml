(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Generic predicates and lemmas for loading byte lists into memory.         *)
(*                                                                           *)
(* This file is loaded after a backend defines its state and memory          *)
(* component. The address width is inferred from that component.             *)
(* ========================================================================= *)

(* Read exactly `LENGTH l` consecutive bytes at the backend native word
   address `pc`. Offset arithmetic in the lemmas below therefore wraps at the
   backend address width; this predicate does not embed addresses in int64. *)
let bytes_loaded = new_definition
 `bytes_loaded s pc l <=>
     read (memory :> bytelist(pc,LENGTH l)) s = l`;;

let bytes_loaded_nil = prove
 (`bytes_loaded s pc []`,
  REWRITE_TAC[bytes_loaded; READ_COMPONENT_COMPOSE;
              LENGTH; bytelist_clauses]);;

let bytes_loaded_append = prove
 (`bytes_loaded s pc (APPEND l1 l2) <=>
   bytes_loaded s pc l1 /\
   bytes_loaded s (word_add pc (word (LENGTH l1))) l2`,
  REWRITE_TAC[bytes_loaded; READ_COMPONENT_COMPOSE;
              read_bytelist_append]);;

let bytes_loaded_unique = METIS [bytes_loaded]
 `!s pc l1 l2.
    bytes_loaded s pc l1 ==> bytes_loaded s pc l2 ==>
    LENGTH l1 = LENGTH l2 ==> l1 = l2`;;

let bytes_loaded_update = METIS [bytes_loaded]
 `!l n. LENGTH l = n ==> !s pc. bytes_loaded s pc l ==>
  !s'. read(memory :> bytelist(pc,n)) s' =
       read(memory :> bytelist(pc,n)) s ==>
       bytes_loaded s' pc l`;;

let bytes_loaded_of_append3 = prove
 (`!l l1 l2 l3. l = APPEND l1 (APPEND l2 l3) ==>
   !s pc. bytes_loaded s (word pc) l ==>
          bytes_loaded s (word (pc + LENGTH l1)) l2`,
  REWRITE_TAC[WORD_ADD] THEN METIS_TAC[bytes_loaded_append]);;

let BYTES_LOADED_BUTLAST = prove
 (`!s pc l. bytes_loaded s pc l ==> bytes_loaded s pc (BUTLAST l)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `l:byte list = []` THEN ASM_REWRITE_TAC[BUTLAST] THEN
  FIRST_X_ASSUM(fun th ->
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [SYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  SIMP_TAC[bytes_loaded_append]);;

let BYTES_LOADED_SUB_LIST = prove
 (`!s pc l m n.
        bytes_loaded s pc l
        ==> bytes_loaded s (word_add pc (word m)) (SUB_LIST(m,n) l)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `m + n:num`] SUB_LIST_TOPSPLIT) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[bytes_loaded_append] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[SUB_LIST_SPLIT; ADD_CLAUSES; bytes_loaded_append] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[LENGTH_SUB_LIST; SUB_0; MIN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LE_CASES; SUB_LIST_TRIVIAL; bytes_loaded_nil]);;

let BYTES_LOADED_TRIM_LIST = prove
 (`!s pc l m n.
        bytes_loaded s pc l
        ==> bytes_loaded s (word_add pc (word m)) (TRIM_LIST(m,n) l)`,
  REWRITE_TAC[BYTES_LOADED_SUB_LIST; TRIM_LIST]);;
