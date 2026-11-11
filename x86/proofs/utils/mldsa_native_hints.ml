(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the FULL proofs of the packing glue of signatures and keys of   *)
(* mldsa-native (packing.c): the copies of byte strings that the compiler    *)
(* has inlined as 128-bit loads and stores (mld_pack_sig_c,                  *)
(* mld_pack_sk_rho_key_tr), the tail calls at offsets computed from an index *)
(* (mld_pack_sig_z, mld_unpack_pk_t1), and the packing and unpacking of the  *)
(* hints (mld_pack_sig_h, mld_sig_unpack_hints). These are the tools of      *)
(* arm/proofs/utils/mldsa_native_hints.ml for the x86 model and the x86      *)
(* code, where gcc inlines the memsets of the hints and of the coefficients, *)
(* as 128-bit stores or with REP STOSQ.                                      *)
(* ========================================================================= *)

needs "common/layout.ml";;
needs "x86/proofs/utils/mldsa_native.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_memset.ml";;
needs "common/mldsa_native_hints.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(* ------------------------------------------------------------------------- *)
(* Byte strings copied with 128-bit loads and stores. The inputs are facts   *)
(* !j. j < n ==> read (bytes8 (word_add a (word j))) s0 = b j: before the    *)
(* simulation, GLUE_LOAD128_TAC a offs adds the facts for the 128-bit words  *)
(* at a + off for each offset off in offs, with the bytes of b. After it,    *)
(* GLUE_STORE_TAC r splits each fact about a 32-, 64- or 128-bit word stored *)
(* at r or at word_add r e into the facts for its bytes, with the addresses  *)
(* normalized, and GLUE_BYTES_FINAL_TAC proves a goal                        *)
(* !j. j < n ==> read (bytes8 (word_add r (word(m + j)))) s = ... from them. *)
(* The legacy SSE loads keep the upper part of the YMM registers, whose      *)
(* initial values must be ghost variables (GHOST_INTRO_TAC before            *)
(* FULL_INIT_TAC), so that the simulation keeps the values of the XMM        *)
(* registers.                                                                *)
(* ------------------------------------------------------------------------- *)

let GLUE_LOAD128_TAC =
  let pat = `!j. j < n ==> read(memory :> bytes8(word_add a (word j)))
                             (s0:x86state) = (b:num->byte) j` in
  fun (a:term) (offs:int list) ->
    W(fun (asl,w) ->
      let th = snd(find (fun (_,th) ->
                 try let i = term_match [] pat (concl th) in
                     instantiate i `a:int64` = a
                 with Failure _ -> false) asl) in
      let lanes = CONJUNCTS(CONV_RULE(EXPAND_CASES_CONV THENC
                                      REWRITE_CONV[WORD_ADD_0]) th) in
      MAP_EVERY (fun off ->
        let addr = if off = 0 then a else
                   subst [a,`a:int64`; mk_small_numeral off,`n:num`]
                         `word_add (a:int64) (word n)` in
        ASSUME_TAC(REWRITE_RULE lanes (READ_MEMORY_MERGE_CONV 4
          (subst [addr,`A:int64`]
            `read (memory :> bytes128 A) (s0:x86state)`))))
       offs);;

let GLUE_STORE_TAC (r:term) =
  let ok a = (a = r) ||
             (try lhand a = r && fst(dest_const(rator(rator a))) = "word_add"
              with Failure _ -> false)
  and levels = ["bytes32",2; "bytes64",3; "bytes128",4] in
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    try let l,_ = dest_eq c in
        let comp = rand(rator l) and st = rand l in
        let bytesf,addr = dest_comb(rand comp) in
        let n = assoc (fst(dest_const bytesf)) levels in
        if ok addr && not(st = `s0:x86state`) then
          STRIP_ASSUME_TAC
           (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
             (CONV_RULE(SIMD_SIMPLIFY_CONV [])
               (CONV_RULE(READ_MEMORY_SPLIT_CONV n) th)))
        else NO_TAC
    with Failure _ -> NO_TAC));;

let GLUE_BYTES_FINAL_TAC =
  CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
           REWRITE_CONV[WORD_ADD_0]) THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Part of a byte string given by a fact !j. j < m ==> read (bytes8          *)
(* (word_add a (word j))) s = b j, e.g. for the precondition of a callee:    *)
(* GLUE_SLICE_TAC tm proves and assumes tm, of the form !j. j < n ==> read   *)
(* (bytes8 (word_add a (word(e + j)))) s = b(e' + j) with e + j and e' + j   *)
(* equal up to the association of the additions.                             *)
(* ------------------------------------------------------------------------- *)

let GLUE_SLICE_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN SIMPLE_ARITH_TAC);
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The address of a tail call, computed from an index i with 32-bit          *)
(* operations: GLUE_REG_TAC reg tm replaces the value v of the 64-bit        *)
(* register reg in the assumptions by tm, proving v = tm by cases on i, from *)
(* the bound i < n in the assumptions (GLUE_IDX_EQ_TAC), with the operations *)
(* evaluated in each case.                                                   *)
(* ------------------------------------------------------------------------- *)

let GLUE_IDX_EQ_TAC =
  W(fun (asl,w) ->
    let bth = snd(find (fun (_,th) ->
      can (term_match [] `i < n`) (concl th) &&
      lhand(concl th) = `i:num` && is_numeral(rand(concl th))) asl) in
    MP_TAC bth THEN SPEC_TAC(`i:num`,`i:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD; WORD_VAL] THEN
    CONV_TAC WORD_RULE);;

let GLUE_REG_TAC (reg:term) (tm:term) =
  let rd = `read:(x86state,int64)component->x86state->int64` in
  FIRST_ASSUM(fun th ->
    try let l,r = dest_eq(concl th) in
        if rator l = mk_comb(rd,reg) then
          SUBGOAL_THEN (mk_eq(r,tm)) SUBST_ALL_TAC THENL
           [GLUE_IDX_EQ_TAC; ALL_TAC]
        else NO_TAC
    with Failure _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Words formed from small numbers and bytes, as the code of the hints       *)
(* computes indices and counts: glue_small_val t is the number val t of such *)
(* a word t, GLUE_ARITH_TAC proves arithmetic from the facts in the context  *)
(* and the bounds of the bytes, and GLUE_WORD_SMALL2_TAC proves equations of *)
(* such words, as WORD_SMALL_TAC of utils/mldsa_native.ml does without       *)
(* bytes.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** The num value of a word built from small numbers and bytes ***)

let rec glue_small_val t =
  match t with
    Comb(Const("word",_),n) -> n
  | Comb(Const("word_zx",_),x) -> glue_small_val x
  | Comb(Comb(Const("word_add",_),x),y) ->
      mk_binary "+" (glue_small_val x,glue_small_val y)
  | _ -> if type_of t = `:byte` then mk_comb(`val:byte->num`,t)
         else failwith "glue_small_val";;

let GLUE_VAL_BYTE = prove
 (`!x:byte. val x < 256`,
  GEN_TAC THEN MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(*** Arithmetic with the small numbers, also using the bounds of bytes ***)

let GLUE_ARITH_TAC =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="] in
  let avoiderp tm =
    match tm with Const(n,_) -> mem n ["read"; "write"; "word"] | _ -> false in
  let filtered tm =
    (is_num_relop tm || (is_neg tm && is_num_relop (dest_neg tm))) &&
    not(can (find_term avoiderp) tm) in
  W(fun (asl,w) ->
    let vals = setify(find_terms (fun t ->
      try fst(dest_const(rator t)) = "val" && type_of(rand t) = `:byte`
      with Failure _ -> false) (list_mk_conj(w::map (concl o snd) asl))) in
    let asl' = filter (fun (_,th) -> filtered(concl th)) asl in
    MAP_EVERY (MP_TAC o snd) asl' THEN
    MAP_EVERY (fun t -> MP_TAC(SPEC (rand t) GLUE_VAL_BYTE)) vals THEN
    CONV_TAC ARITH_RULE);;

let GLUE_MOD_LT2_TAC =
  W(fun (asl,w) ->
    let tms = find_terms
     (fun t -> is_binary "MOD" t && is_numeral(rand t) &&
               not(is_numeral(lhand t))) w in
    FIRST(map (fun t ->
      MP_TAC(SPECL [lhand t; rand t] MOD_LT) THEN
      ANTS_TAC THENL [GLUE_ARITH_TAC; DISCH_THEN SUBST1_TAC])
     (sort free_in (setify tms))));;

let GLUE_WORD_SMALL2_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN;
              VAL_WORD; VAL_WORD_SHL; DIMINDEX_8; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT GLUE_MOD_LT2_TAC THEN GLUE_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loops of mld_sig_unpack_hints, for the omega + k bytes b of the       *)
(* hints and polynomial i, with the counts before it (mld_hints_start, s)    *)
(* and up to it (glue_suh_new, w): the code fails at once if                 *)
(* glue_suh_early, else sets the coefficients b j for j from s, in           *)
(* glue_suh_n1 iterations, up to w or up to the first that is not greater    *)
(* than the one before (glue_suh_ok1 says there is none), and then, for the  *)
(* last polynomial, if b w = 0 (w < omega), checks the bytes from w + 1 in   *)
(* glue_suh_n2 iterations, up to omega or the first that is not zero         *)
(* (glue_suh_zeros says the bytes from w are zero). glue_suh_h n gives the   *)
(* coefficients after n iterations of the first loop.                        *)
(* ------------------------------------------------------------------------- *)

let glue_suh_new = new_definition
 `glue_suh_new omega (b:num->byte) i = val(b(omega + i))`;;

let glue_suh_early = new_definition
 `glue_suh_early omega (b:num->byte) i <=>
    glue_suh_new omega b i < mld_hints_start omega b i \/
    omega < glue_suh_new omega b i`;;

let glue_suh_ok1 = new_definition
 `glue_suh_ok1 omega (b:num->byte) i <=>
    !j. mld_hints_start omega b i < j /\ j < glue_suh_new omega b i
        ==> val(b(j - 1)) < val(b j)`;;

let glue_suh_zeros = new_definition
 `glue_suh_zeros omega (b:num->byte) i <=>
    !j. glue_suh_new omega b i <= j /\ j < omega ==> b j = word 0`;;

let glue_suh_n1 = new_definition
 `glue_suh_n1 omega (b:num->byte) i =
    if glue_suh_early omega b i \/
       ~(mld_hints_start omega b i < glue_suh_new omega b i) then 0
    else (minimal j. mld_hints_start omega b i < j /\
                     (j = glue_suh_new omega b i \/
                      val(b j) <= val(b(j - 1)))) -
         mld_hints_start omega b i`;;

let glue_suh_loop2 = new_definition
 `glue_suh_loop2 omega k (b:num->byte) i <=>
    ~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ i = k - 1 /\
    glue_suh_new omega b i < omega /\ b(glue_suh_new omega b i) = word 0`;;

let glue_suh_n2 = new_definition
 `glue_suh_n2 omega k (b:num->byte) i =
    if glue_suh_loop2 omega k b i
    then (minimal m. glue_suh_new omega b i < m /\
                     (m = omega \/ ~(b m = word 0))) -
         glue_suh_new omega b i
    else 0`;;

let glue_suh_steps = new_definition
 `glue_suh_steps omega k (b:num->byte) i =
    glue_suh_n1 omega b i + glue_suh_n2 omega k b i`;;

let glue_suh_h = new_definition
 `glue_suh_h omega (b:num->byte) i n q:int32 =
    if ?j. mld_hints_start omega b i <= j /\
           j < mld_hints_start omega b i + n /\ val(b j) = q
    then word 1 else word 0`;;

(*** The return value, and the coefficients so far ***)

let GLUE_SUH_OK = prove
 (`!omega k (b:num->byte) i.
        mld_unpack_hints_ok omega k b i <=>
        ~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\
        (i = k - 1 ==> glue_suh_zeros omega b i)`,
  REWRITE_TAC[mld_unpack_hints_ok; glue_suh_early; glue_suh_ok1;
              glue_suh_zeros; glue_suh_new; NOT_LT; DE_MORGAN_THM] THEN
  MESON_TAC[]);;

let GLUE_SUH_H_0 = prove
 (`!omega (b:num->byte) i q. glue_suh_h omega b i 0 q = word 0`,
  REWRITE_TAC[glue_suh_h; ADD_CLAUSES] THEN ARITH_TAC);;

let GLUE_SUH_H_ADD1 = prove
 (`!omega (b:num->byte) i n q.
        glue_suh_h omega b i (n + 1) q =
        if val(b(mld_hints_start omega b i + n)) = q then word 1
        else glue_suh_h omega b i n q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_suh_h] THEN
  ABBREV_TAC `s = mld_hints_start omega (b:num->byte) i` THEN
  SUBGOAL_THEN
   `!P. (?j. s <= j /\ j < s + n + 1 /\ P j) <=>
        P(s + n) \/ (?j. s <= j /\ j < s + n /\ P j)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `j:num = s + n` THENL
       [DISJ1_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC];
      STRIP_TAC THENL
       [EXISTS_TAC `s + n:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
    ASM_CASES_TAC `val((b:num->byte)(s + n)) = q` THEN ASM_REWRITE_TAC[]]);;

let GLUE_SUH_H_FULL = prove
 (`!omega (b:num->byte) i n q.
        mld_hints_start omega b i + n = glue_suh_new omega b i
        ==> glue_suh_h omega b i n q = mld_unpack_hints omega b i q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_suh_h; mld_unpack_hints; glue_suh_new]
  THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(*** The number of iterations of the first loop, and the tests in them ***)

let GLUE_SUH_N1 = prove
 (`!omega (b:num->byte) i.
        ~glue_suh_early omega b i /\
        mld_hints_start omega b i < glue_suh_new omega b i
        ==> let s = mld_hints_start omega b i
            and w = glue_suh_new omega b i
            and n1 = glue_suh_n1 omega b i in
            0 < n1 /\ s + n1 <= w /\
            (!p. p + 1 < n1
                 ==> s + p + 1 < w /\ val(b(s + p)) < val(b(s + p + 1))) /\
            (glue_suh_ok1 omega b i <=> s + n1 = w) /\
            (~glue_suh_ok1 omega b i
             ==> s + n1 < w /\ val(b(s + n1)) <= val(b((s + n1) - 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[glue_suh_n1; glue_suh_ok1] THEN
  ABBREV_TAC `s = mld_hints_start omega (b:num->byte) i` THEN
  ABBREV_TAC `w = glue_suh_new omega (b:num->byte) i` THEN
  SUBGOAL_THEN
   `?j. s < j /\ (j = w \/ val((b:num->byte) j) <= val(b(j - 1)))`
  MP_TAC THENL [EXISTS_TAC `w:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN BETA_TAC THEN
  ABBREV_TAC
   `m = minimal j. s < j /\ (j = w \/ val((b:num->byte) j) <= val(b(j - 1)))`
  THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `m <= w` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. s < j /\ j < m ==> ~(j = w) /\ val((b:num->byte)(j - 1)) < val(b j)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s + p + 1`) THEN
    REWRITE_TAC[ARITH_RULE `(s + p + 1) - 1 = s + p`] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    EQ_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `m:num = w` THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (is_forall o concl) o
        check (fun th -> free_in `w:num` (concl th) &&
                         not(free_in `m:num` (concl th)))) THEN
      ASM_ARITH_TAC;
      DISCH_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        is_forall(concl th) && free_in `m:num` (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    DISCH_TAC THEN
    SUBGOAL_THEN `~(m:num = w)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC
       `~(!j. s < j /\ j < w ==> val((b:num->byte)(j - 1)) < val(b j))` THEN
      REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        is_forall(concl th) && free_in `m:num` (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `s + m - s = m` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [ASM_MESON_TAC[]; FIRST_ASSUM ACCEPT_TAC]]);;

(*** The number of iterations of the second loop, and the tests in them ***)

let GLUE_SUH_N2 = prove
 (`!omega k (b:num->byte) i.
        glue_suh_loop2 omega k b i
        ==> let w = glue_suh_new omega b i
            and n2 = glue_suh_n2 omega k b i in
            0 < n2 /\ w + n2 <= omega /\
            (!q. q + 1 < n2 ==> w + q + 1 < omega /\ b(w + q + 1) = word 0) /\
            (glue_suh_zeros omega b i <=> w + n2 = omega) /\
            (~glue_suh_zeros omega b i
             ==> w + n2 < omega /\ ~(b(w + n2) = word 0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[glue_suh_n2; glue_suh_zeros] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[glue_suh_loop2]) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `w = glue_suh_new omega (b:num->byte) i` THEN
  SUBGOAL_THEN `?m. w < m /\ (m = omega \/ ~((b:num->byte) m = word 0))`
  MP_TAC THENL [EXISTS_TAC `omega:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN BETA_TAC THEN
  ABBREV_TAC
   `m = minimal m. w < m /\ (m = omega \/ ~((b:num->byte) m = word 0))` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `m <= omega` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `omega:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. w < j /\ j < m ==> ~(j = omega) /\ (b:num->byte) j = word 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!j. w <= j /\ j < omega ==> (b:num->byte) j = word 0) <=> m = omega`
  ASSUME_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `m:num = omega` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
        is_forall(concl th) && not(free_in `m:num` (concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      DISCH_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `j:num = w` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        is_forall(concl th) && free_in `m:num` (concl th) &&
        not(is_neg(concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `w + m - w = m` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w + q + 1` o check (fun th ->
      is_forall(concl th) && free_in `m:num` (concl th) &&
      not(is_neg(concl th)))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [ASM_MESON_TAC[]; FIRST_ASSUM ACCEPT_TAC]]);;

let GLUE_SUH_LOOP2_OK = prove
 (`!omega k (b:num->byte) i.
        glue_suh_loop2 omega k b i
        ==> (mld_unpack_hints_ok omega k b i <=> glue_suh_zeros omega b i)`,
  REWRITE_TAC[glue_suh_loop2; GLUE_SUH_OK] THEN MESON_TAC[]);;

(*** The counts and the result in the cases of the tests of the code ***)

let GLUE_SUH_FACTS = prove
 (`!omega k (b:num->byte) i.
      (glue_suh_early omega b i
       ==> glue_suh_n1 omega b i = 0 /\ glue_suh_n2 omega k b i = 0 /\
           ~mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\
       ~(mld_hints_start omega b i < glue_suh_new omega b i)
       ==> glue_suh_n1 omega b i = 0 /\ glue_suh_ok1 omega b i) /\
      (~glue_suh_ok1 omega b i
       ==> glue_suh_n2 omega k b i = 0 /\ ~mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ ~(i = k - 1)
       ==> glue_suh_n2 omega k b i = 0 /\ mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ i = k - 1 /\
       glue_suh_new omega b i = omega
       ==> glue_suh_n2 omega k b i = 0 /\ mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ i = k - 1 /\
       ~(glue_suh_new omega b i = omega) /\
       ~(b(glue_suh_new omega b i) = word 0)
       ==> glue_suh_n2 omega k b i = 0 /\ ~mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ i = k - 1 /\
       ~(glue_suh_new omega b i = omega) /\
       b(glue_suh_new omega b i) = word 0
       ==> glue_suh_loop2 omega k b i /\
           (mld_unpack_hints_ok omega k b i <=> glue_suh_zeros omega b i))`,
  REPEAT GEN_TAC THEN
  MP_TAC(REWRITE_CONV[glue_suh_early] `glue_suh_early omega (b:num->byte) i`)
  THEN
  MP_TAC(REWRITE_CONV[glue_suh_ok1] `glue_suh_ok1 omega (b:num->byte) i`) THEN
  MP_TAC(REWRITE_CONV[glue_suh_zeros] `glue_suh_zeros omega (b:num->byte) i`)
  THEN
  MP_TAC(REWRITE_CONV[glue_suh_loop2]
          `glue_suh_loop2 omega k (b:num->byte) i`) THEN
  MP_TAC(REWRITE_CONV[glue_suh_n1] `glue_suh_n1 omega (b:num->byte) i`) THEN
  MP_TAC(REWRITE_CONV[glue_suh_n2] `glue_suh_n2 omega k (b:num->byte) i`) THEN
  MP_TAC(REWRITE_CONV[GLUE_SUH_OK]
          `mld_unpack_hints_ok omega k (b:num->byte) i`) THEN
  SPEC_TAC(`mld_unpack_hints_ok omega k (b:num->byte) i`,`ok:bool`) THEN
  SPEC_TAC(`glue_suh_n2 omega k (b:num->byte) i`,`n2:num`) THEN
  SPEC_TAC(`glue_suh_n1 omega (b:num->byte) i`,`n1:num`) THEN
  SPEC_TAC(`glue_suh_loop2 omega k (b:num->byte) i`,`l2:bool`) THEN
  SPEC_TAC(`glue_suh_zeros omega (b:num->byte) i`,`zs:bool`) THEN
  SPEC_TAC(`glue_suh_ok1 omega (b:num->byte) i`,`o1:bool`) THEN
  SPEC_TAC(`glue_suh_early omega (b:num->byte) i`,`ea:bool`) THEN
  SPEC_TAC(`mld_hints_start omega (b:num->byte) i`,`s:num`) THEN
  SPEC_TAC(`glue_suh_new omega (b:num->byte) i`,`w:num`) THEN
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  TRY(X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_ARITH_TAC) THEN
  TRY(EXISTS_TAC `w:num` THEN ASM_REWRITE_TAC[LE_REFL] THEN ASM_ARITH_TAC)
  THEN ASM_ARITH_TAC);;

let GLUE_SUH_BOUNDS = prove
 (`!omega (b:num->byte) i.
        mld_hints_start omega b i < 256 /\ glue_suh_new omega b i < 256`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_hints_start; glue_suh_new] THEN
  COND_CASES_TAC THEN REWRITE_TAC[GLUE_VAL_BYTE] THEN ARITH_TAC);;

(*** Arithmetic with the counts, with the number of iterations as a sum ***)

let GLUE_STEPS_ARITH_TAC =
  let isst t =
    try let f,args = strip_comb t in
        fst(dest_const f) = "glue_suh_steps" && length args = 4
    with Failure _ -> false in
  W(fun (asl,w) ->
    let ts = setify(find_terms isst (list_mk_conj(w::map (concl o snd) asl))) in
    MAP_EVERY (fun t -> MP_TAC(REWRITE_CONV[glue_suh_steps] t)) ts THEN
    GLUE_ARITH_TAC);;

(*** A loop with any invariant (whose PC may depend on the iteration):    ***)
(*** the invariant iv i for the iterations i <= k, with the events of the ***)
(*** iterations so far, from the template in the postcondition            ***)

let GLUE_ENSURES_WHILE = prove
 (`!k (iv:num->A->bool) P Q C.
        C ,, C = C /\
        ensures step P (iv 0) C /\
        (!i. i < k ==> ensures step (iv i) (iv(i + 1)) C) /\
        ensures step (iv k) Q C
        ==> ensures step P Q C`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `(iv:num->A->bool) k` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n. n <= k ==> ensures step P ((iv:num->A->bool) n) C`
   (fun th -> MATCH_MP_TAC th THEN REWRITE_TAC[LE_REFL]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `(iv:num->A->bool) n` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let GLUE_EVENTS_WHILE_TAC (k:term) (iv:term) (asl,w) =
  let _,args = strip_comb w in
  let postcond = el 2 args in
  let sv,_ = dest_abs postcond in
  let ex = find_term (fun t -> is_exists t &&
             fst(dest_var(fst(dest_exists t))) = "e2") postcond in
  let v,bd = dest_exists ex in
  let c1,eqn,c3 = match conjuncts bd with
                    [a;b;c] -> a,b,c | _ -> failwith "GLUE_EVENTS_WHILE_TAC" in
  let _,mid = dest_binary "APPEND" (rhs eqn) in
  let enum,pro = dest_binary "APPEND" mid in
  let fn = rand enum in
  let i = fst(dest_abs iv) in
  let bv,body = dest_abs(snd(dest_abs iv)) in
  let ev_conj = mk_exists(v,list_mk_conj
    [c1; mk_eq(v,list_mk_icomb "APPEND"
              [list_mk_icomb "ENUMERATEL" [i;fn]; pro]); c3]) in
  let new_iv = mk_abs(i,mk_abs(bv,mk_conj(body,vsubst [bv,sv] ev_conj))) in
  (MATCH_MP_TAC GLUE_ENSURES_WHILE THEN
   MAP_EVERY EXISTS_TAC [k; new_iv] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Zero 32-bit words from zero bytes, as the memset of the coefficients in   *)
(* mld_sig_unpack_hints, which gcc inlines with REP STOSQ (see               *)
(* x86/proofs/utils/mldsa_native_memset.ml), leaves them.                    *)
(* ------------------------------------------------------------------------- *)

let GLUE_ZERO32_BYTES = prove
 (`!a:int64 n s:x86state.
     read (memory :> bytes(a,4 * n)) s = 0
     ==> !q. q < n
             ==> read(memory :> bytes32(word_add a (word(4 * q)))) s = word 0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; BYTES32_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  MP_TAC(SPECL [`a:int64`; `4 * n`; `0`; `4 * q`; `4`; `s:x86state`]
    READ_MEMORY_BYTES_SUB) THEN
  ASM_REWRITE_TAC[DIV_0; MOD_0] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMPLE_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The proof of a FULL theorem for mld_sig_unpack_hints. The two loops of    *)
(* the code are one loop over the glue_suh_steps = n1 + n2 iterations p      *)
(* (GLUE_ENSURES_WHILE), with the invariant glue_suh_inv whose PC is the     *)
(* head of the first loop for p < n1, that of the second for n1 <= p and one *)
(* of the two paths to the return at the end. The record gives the parameter *)
(* set, and suh_stos the offset of the REP STOSQ of the memset of the        *)
(* coefficients, which gcc inlines on x86 (MEMSET_PREP_TAC and the tools     *)
(* after it in utils/mldsa_native_memset.ml). An iteration is proved in the  *)
(* cases of the paths of the code (GLUE_SUH_BODY_TAC), each with its own     *)
(* function in the events template glue_suh_template.                        *)
(* ------------------------------------------------------------------------- *)

type glue_suh =
 { suh_exec : thm * thm option array;
   suh_fn : string;
   suh_omega : int;
   suh_k : int;
   suh_sigh : int;
   suh_stos : int };;

let glue_suh_inst prm tm =
  let n = mk_small_numeral in
  let lbl l = n(layout(prm.suh_fn ^ "_" ^ l)) in
  vsubst [n prm.suh_omega,`OM:num`; n (prm.suh_omega - 1),`OM1:num`;
          n prm.suh_k,`KK:num`; n (prm.suh_k - 1),`KM1:num`;
          n prm.suh_sigh,`SH:num`; n (prm.suh_omega + prm.suh_k),`HB:num`;
          lbl "loop1",`L1:num`; lbl "loop2",`L2:num`;
          lbl "join2",`J2:num`; lbl "join4",`J4:num`] tm;;

let glue_suh_template prm = glue_suh_inst prm
 `\(b:num->byte) (i:num) (h:int64) (sig:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   APPEND
    (if mld_unpack_hints_ok OM KK b i
     then f_ev_ok b i h sig pc stackpointer returnaddress
     else f_ev_bad b i h sig pc stackpointer returnaddress)
    (APPEND
      (ENUMERATEL (glue_suh_steps OM KK b i)
        (\p. if p < glue_suh_n1 OM b i
             then if p + 1 < glue_suh_n1 OM b i
                  then f_ev_a b i h sig pc stackpointer returnaddress p
                  else if glue_suh_ok1 OM b i
                  then if i < KM1
                       then f_ev_ar b i h sig pc stackpointer returnaddress p
                       else if OM <= glue_suh_new OM b i
                       then f_ev_ar2 b i h sig pc stackpointer
                                     returnaddress p
                       else if b(glue_suh_new OM b i) = word 0
                       then f_ev_at b i h sig pc stackpointer returnaddress p
                       else f_ev_az b i h sig pc stackpointer returnaddress p
                  else f_ev_af b i h sig pc stackpointer returnaddress p
             else if p + 1 < glue_suh_steps OM KK b i
             then f_ev_b b i h sig pc stackpointer returnaddress p
             else if glue_suh_zeros OM b i
             then f_ev_be b i h sig pc stackpointer returnaddress p
             else f_ev_bf b i h sig pc stackpointer returnaddress p))
      (if glue_suh_early OM b i
       then if glue_suh_new OM b i < mld_hints_start OM b i
            then f_ev_e1 b i h sig pc stackpointer returnaddress
            else if 0 < i
            then f_ev_e3 b i h sig pc stackpointer returnaddress
            else f_ev_e2 b i h sig pc stackpointer returnaddress
       else if mld_hints_start OM b i < glue_suh_new OM b i
       then if 0 < i then f_ev_p1 b i h sig pc stackpointer returnaddress
            else f_ev_p0 b i h sig pc stackpointer returnaddress
       else if i < KM1
       then if 0 < i then f_ev_r1 b i h sig pc stackpointer returnaddress
            else f_ev_r0 b i h sig pc stackpointer returnaddress
       else if OM <= glue_suh_new OM b i
       then f_ev_r2 b i h sig pc stackpointer returnaddress
       else if b(glue_suh_new OM b i) = word 0
       then f_ev_t b i h sig pc stackpointer returnaddress
       else f_ev_z b i h sig pc stackpointer returnaddress))
   :(uarch_event)list`;;

let glue_suh_inv prm = glue_suh_inst prm
 `\p (s:x86state).
   bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
   read RSP s = stackpointer /\
   read (memory :> bytes64 stackpointer) s = rbx_init /\
   read (memory :> bytes64 (word_add stackpointer (word 8))) s = rbp_init /\
   read (memory :> bytes64 (word_add stackpointer (word 16))) s =
     returnaddress /\
   read R8 s = h /\ read R11 s = sig /\ read RBX s = word_add sig (word SH) /\
   read RBP s = word i /\ read RSI s = word(mld_hints_start OM b i) /\
   read R9 s = word(glue_suh_new OM b i) /\
   (!j. j < HB
        ==> read(memory :> bytes8(word_add sig (word(SH + j)))) s = b j) /\
   read RIP s =
     word(if p < glue_suh_steps OM KK b i
          then if p < glue_suh_n1 OM b i then pc + L1 else pc + L2
          else if mld_unpack_hints_ok OM KK b i then pc + J4 else pc + J2) /\
   (p < glue_suh_n1 OM b i
    ==> read RAX s = word(mld_hints_start OM b i + p) /\
        read RDX s = word_add sig (word(SH + mld_hints_start OM b i + p))) /\
   (p < glue_suh_steps OM KK b i
    ==> read R10 s = word(glue_suh_new OM b i + (p - glue_suh_n1 OM b i))) /\
   (p < glue_suh_steps OM KK b i \/ mld_unpack_hints_ok OM KK b i
    ==> !q. q < 256
            ==> read(memory :> bytes32(word_add h (word(4 * q)))) s =
                glue_suh_h OM b i (MIN p (glue_suh_n1 OM b i)) q)`;;

let GLUE_SUH_SETUP_TAC prm =
  let inst = glue_suh_inst prm in
  CONCRETIZE_F_EVENTS_TAC (glue_suh_template prm) THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst prm.suh_exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  GLUE_EVENTS_WHILE_TAC (inst `glue_suh_steps OM KK (b:num->byte) i`)
    (glue_suh_inv prm);;

(*** The PC in the current state and its offset in the function, the facts ***)
(*** about the current state (glue_pcev), and a word base + word e with e  ***)
(*** formed from small numbers and bytes (glue_base_off)                   ***)

let glue_current_pc (asl,w) =
  let s = rand w in
  rhs(concl(snd(find (fun (_,th) ->
    try lhs(concl th) = mk_comb(`read RIP`,s) with Failure _ -> false) asl)));;

let glue_pc_offset base t =
  try dest_small_numeral(rand(rand t)) - base with Failure _ -> -1;;

let glue_pcev =
  let pat = `read (c:(x86state,A)component) (s:x86state)` in
  fun th ->
    let c = concl th in
    is_eq c && can (term_match [] pat) (lhs c);;

let glue_rassoc e = rand(concl(REWRITE_CONV[GSYM ADD_ASSOC] e));;

let rec glue_base_off t =
  match t with
    Comb(Comb(Const("word_add",_),x),y) ->
      (try let e = glue_small_val y in
           let b,off = glue_base_off x in
           b,Some(match off with
                    None -> e
                  | Some e' -> glue_rassoc(mk_binary "+" (e',e)))
       with Failure _ ->
       try let e = glue_small_val x in
           let b,off = glue_base_off y in
           b,Some(match off with
                    None -> e
                  | Some e' -> glue_rassoc(mk_binary "+" (e',e)))
       with Failure _ -> t,None)
  | _ -> t,None;;

(*** Register values that are small words, as word n, or base + word n,    ***)
(*** after the truncations of the 32-bit LEA written as zero extensions    ***)

let WORD_SX_ZX_64_32 = prove
 (`!x:int64. (word_sx x:int32) = word_zx x`,
  GEN_TAC THEN MATCH_MP_TAC WORD_SX_ZX THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN ARITH_TAC);;

let GLUE_SMALL_REGS_TAC =
  let rd = `read:(x86state,int64)component->x86state->int64` in
  let regs = [`RAX`;`RCX`;`RDX`;`RSI`;`RDI`;`R8`;`R9`;`R10`;`R11`;
              `RBP`;`RBX`] in
  let is_word t = is_comb t && is_const(rator t) &&
                  fst(dest_const(rator t)) = "word" in
  let one reg =
    TRY(FIRST_ASSUM(fun th ->
      let l,r = dest_eq(concl th) in
      if rator l <> mk_comb(rd,reg) || is_word r then NO_TAC else
      try let e = glue_rassoc(glue_small_val r) in
          let tm = mk_comb(`word:num->int64`,e) in
          SUBGOAL_THEN (mk_eq(r,tm)) SUBST_ALL_TAC THENL
           [GLUE_WORD_SMALL2_TAC; ALL_TAC]
      with Failure _ ->
        match glue_base_off r with
          b,Some e ->
            let tm = list_mk_icomb "word_add"
                       [b; mk_comb(`word:num->int64`,e)] in
            if tm = r then NO_TAC else
            SUBGOAL_THEN (mk_eq(r,tm)) SUBST_ALL_TAC THENL
             [GLUE_WORD_SMALL2_TAC ORELSE
              (GEN_REWRITE_TAC LAND_CONV [WORD_ADD_SYM] THEN
               GLUE_WORD_SMALL2_TAC);
              ALL_TAC]
        | _ -> NO_TAC)) in
  RULE_ASSUM_TAC(fun th ->
    if glue_pcev th then REWRITE_RULE[WORD_SX_ZX_64_32] th else th) THEN
  MAP_EVERY one regs;;

(*** The flags of comparisons, as arithmetic on the values compared ***)

let GLUE_CF_LEMMA = prove
 (`!x y:N word. (&(val x) - &(val y):int = &(val(word_sub x y))) <=>
                val y <= val x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[INT_ARITH `x - y:int = z <=> x = y + z`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  MP_TAC(ISPEC `x:N word` VAL_BOUND) THEN ASM_ARITH_TAC);;

let GLUE_ZF_LEMMA = prove
 (`!x y:N word. val(word_sub x y) = 0 <=> val x = val y`,
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; VAL_EQ]);;

(*** val t as a number for the small words t in the facts ***)

let GLUE_VALS_TAC =
  let isval t = try fst(dest_const(rator t)) = "val" with Failure _ -> false in
  W(fun (asl,w) ->
    let tms = setify(find_terms (fun t ->
      isval t && not(is_var(rand t)) &&
      not(type_of(rand t) = `:byte` && is_comb(rand t) &&
          not(is_const(rator(rand t)))))
      (list_mk_conj(`T`::map (concl o snd) (filter (glue_pcev o snd) asl))))
    in
    MAP_EVERY (fun t ->
      try let e = glue_rassoc(glue_small_val(rand t)) in
          if e = t then ALL_TAC else
          TRY(SUBGOAL_THEN (mk_eq(t,e))
               (fun th -> RULE_ASSUM_TAC(fun th' ->
                  if glue_pcev th' then REWRITE_RULE[th] th' else th')) THENL
               [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_ADD;
                            DIMINDEX_8; DIMINDEX_16; DIMINDEX_32;
                            DIMINDEX_64] THEN
                CONV_TAC NUM_REDUCE_CONV THEN
                REPEAT GLUE_MOD_LT2_TAC THEN GLUE_ARITH_TAC;
                ALL_TAC])
      with Failure _ -> ALL_TAC) tms);;

(*** The carry flag of a comparison with an immediate n, whose value the   ***)
(*** simulation has already reduced from val(word n) to n                  ***)

let GLUE_CF_NUM_CONV tm =
  let l,r = dest_eq tm in
  let _ = dest_binop `(-):int->int->int` l in
  let x,y = dest_binary "word_sub" (rand(rand r)) in
  let th0 = ISPECL [x; y] GLUE_CF_LEMMA in
  let th = CONV_RULE(LAND_CONV(LAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) THENC
                     RAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) th0 in
  if lhs(concl th) = tm then th else failwith "GLUE_CF_NUM_CONV";;

let GLUE_VAL_BYTE_MOD = prove
 (`!x:byte. val x MOD 256 = val x /\ val x MOD 4294967296 = val x /\
            val x MOD 18446744073709551616 = val x`,
  GEN_TAC THEN MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x < 256 ==> x < 4294967296`;
           ARITH_RULE `x < 256 ==> x < 18446744073709551616`]);;

let GLUE_FLAGS_TAC =
  RULE_ASSUM_TAC(fun th ->
    if glue_pcev th then
      CONV_RULE(ONCE_DEPTH_CONV GLUE_CF_NUM_CONV)
       (REWRITE_RULE[GLUE_CF_LEMMA; GLUE_ZF_LEMMA] th)
    else th) THEN
  GLUE_VALS_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if glue_pcev th then REWRITE_RULE[GLUE_VAL_BYTE_MOD] th else th);;

(*** Split on p, deciding the branch and the events in each case ***)

let GLUE_CASES_TAC (p:term) =
  ASM_CASES_TAC p THEN
  POP_ASSUM(fun cth ->
    let eq = if is_neg(concl cth) then EQF_INTRO cth else EQT_INTRO cth in
    RULE_ASSUM_TAC(fun th -> if glue_pcev th then REWRITE_RULE[eq] th else th)
    THEN ASSUME_TAC cth);;

(*** The byte of the hints at index t, in the canonical form of the input  ***)
(*** and in the forms in which the simulation may address it               ***)

let GLUE_INPUT_AT_TAC prm t =
  let inst = glue_suh_inst prm in
  let pat = inst `!j. j < HB ==> read(memory :> bytes8
                         (word_add sig (word(SH + j)))) s = (b:num->byte) j` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pat) (concl th) then
      MP_TAC(SPEC t th) THEN ANTS_TAC THENL [GLUE_STEPS_ARITH_TAC; DISCH_TAC]
    else NO_TAC);;

let GLUE_INPUT_FORMS_TAC prm extra t =
  let inst = glue_suh_inst prm in
  let canon = inst (vsubst [t,`t:num`] `word_add sig (word(SH + t)):int64`) in
  let cands =
    [inst (vsubst [t,`t:num`] `word_add sig (word(t + SH)):int64`);
     inst (vsubst [t,`t:num`] `word_add sig (word(1 * t + SH)):int64`)] @
    map (fun e -> list_mk_icomb "word_add"
                    [`sig:int64`; mk_comb(`word:num->int64`,inst e)]) extra in
  let forms = setify(map (fun a ->
    try rhs(concl(NUM_REDUCE_CONV a)) with Failure _ -> a) cands) in
  GLUE_INPUT_AT_TAC prm t THEN
  MAP_EVERY (fun a ->
    if a = canon then ALL_TAC else
    TRY(FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && can (term_match [] `read (memory :> bytes8 a) s`) (lhs c)
         && rand(rand(rand(rator(lhs c)))) = canon
      then
        SUBGOAL_THEN (mk_eq(a,canon)) (fun eq -> ASSUME_TAC
          (CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV(REWR_CONV(SYM eq)))) th))
        THENL
         [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
          ALL_TAC]
      else NO_TAC))) forms;;

(*** val(word n) = n and 1 * n = n for the index n in a register, which    ***)
(*** the simulation uses in the address base + index * 1 + disp            ***)

let GLUE_INDEX_FACTS_TAC (n:term) =
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,n)),n))
   ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    GLUE_ARITH_TAC;
    ALL_TAC] THEN
  ASSUME_TAC(ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `1` n,n)));;

(*** Byte values named by equations in the context, in the facts ***)

let GLUE_SUH_ATOMS_TAC =
  W(fun (asl,w) ->
    let eqs = filter (fun th ->
      let c = concl th in
      is_eq c &&
      (try fst(dest_const(rator(lhs c))) = "val" &&
           type_of(rand(lhs c)) = `:byte` && not(is_var(rand(lhs c)))
       with Failure _ -> false)) (map snd asl) in
    if eqs = [] then ALL_TAC else
    RULE_ASSUM_TAC(fun th ->
      if glue_pcev th then REWRITE_RULE eqs th else th));;

let GLUE_SUH_NORM_TAC =
  GLUE_SMALL_REGS_TAC THEN GLUE_FLAGS_TAC THEN GLUE_SUH_ATOMS_TAC THEN
  GLUE_SMALL_REGS_TAC;;

(*** Decide a branch from the facts, or split on one of the predicates of  ***)
(*** the events template that it is equivalent to                          ***)

let GLUE_SUH_DECIDE_TAC prm =
  let inst = glue_suh_inst prm in
  let canon eq =
    RULE_ASSUM_TAC(fun th ->
      if glue_pcev th then REWRITE_RULE[eq; NOT_CLAUSES] th else th) in
  let cands =
   [`0 < i`;
    inst `glue_suh_new OM (b:num->byte) i < mld_hints_start OM b i`;
    inst `glue_suh_early OM (b:num->byte) i`;
    inst `mld_hints_start OM (b:num->byte) i < glue_suh_new OM b i`;
    inst `i < KM1`; inst `OM <= glue_suh_new OM (b:num->byte) i`;
    inst `(b:num->byte)(glue_suh_new OM b i) = word 0`] in
  let hook p =
    if p = `0 < i` then
      W(fun (asl,w) ->
        if exists (fun (_,th) -> concl th = `0 < i`) asl then
          SUBGOAL_THEN
           (inst `val((b:num->byte)(i + OM1)) = mld_hints_start OM b i`)
          ASSUME_TAC THENL
           [REWRITE_TAC[mld_hints_start] THEN
            COND_CASES_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
            AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
            ALL_TAC] THEN
          GLUE_INDEX_FACTS_TAC (inst `i + OM1`) THEN
          GLUE_INPUT_FORMS_TAC prm [] (inst `i + OM1`)
        else
          SUBGOAL_THEN (inst `mld_hints_start OM (b:num->byte) i <= 0`)
          ASSUME_TAC THENL
           [REWRITE_TAC[mld_hints_start] THEN
            COND_CASES_TAC THENL [REWRITE_TAC[LE_REFL]; SIMPLE_ARITH_TAC];
            ALL_TAC] THEN
          SUBGOAL_THEN (inst `word 0:int64 = word(mld_hints_start OM b i)`)
           (fun eq -> FIRST_X_ASSUM(fun th ->
              if concl th = mk_eq(mk_comb(`read RSI`,rand w),`word 0:int64`)
              then ASSUME_TAC(TRANS th eq) else NO_TAC)) THENL
           [REWRITE_TAC[mld_hints_start] THEN
            COND_CASES_TAC THENL [REFL_TAC; SIMPLE_ARITH_TAC];
            ALL_TAC])
    else if p = el 2 cands then
      W(fun (asl,w) ->
        if exists (fun (_,th) -> concl th = mk_neg p) asl then
          SUBGOAL_THEN
           (inst `mld_hints_start OM (b:num->byte) i <= glue_suh_new OM b i /\
                  glue_suh_new OM b i <= OM`) STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC (mk_neg p) THEN REWRITE_TAC[glue_suh_early] THEN
            ARITH_TAC;
            ALL_TAC] THEN
          GLUE_INDEX_FACTS_TAC (inst `glue_suh_new OM (b:num->byte) i`) THEN
          GLUE_INPUT_FORMS_TAC prm [] (inst `glue_suh_new OM (b:num->byte) i`)
        else ALL_TAC)
    else ALL_TAC in
  let equiv =
    REWRITE_TAC[glue_suh_early; COND_EXPAND; GSYM VAL_EQ_0] THEN
    GLUE_ARITH_TAC in
  let decide =
    (ASM_REWRITE_TAC[COND_EXPAND; VAL_EQ_0] THEN NO_TAC) ORELSE
    (REWRITE_TAC[COND_EXPAND] THEN GLUE_ARITH_TAC) in
  W(fun (asl,w) ->
    let c0,_ = dest_cond(glue_current_pc (asl,w)) in
    let addcands =
      MAP_EVERY (fun p ->
        W(fun (asl,w) ->
          if exists (fun (_,th) -> concl th = p || concl th = mk_neg p) asl
          then ALL_TAC else
          TRY(SUBGOAL_THEN p ASSUME_TAC THENL [equiv; ALL_TAC]) THEN
          TRY(SUBGOAL_THEN (mk_neg p) ASSUME_TAC THENL [equiv; ALL_TAC])))
       cands in
    let split p =
      ((SUBGOAL_THEN (mk_iff(c0,p)) canon THENL [equiv; ALL_TAC]) ORELSE
       (SUBGOAL_THEN (mk_iff(c0,mk_neg p)) canon THENL [equiv; ALL_TAC])) THEN
      GLUE_CASES_TAC p THEN hook p THEN addcands in
    ((((SUBGOAL_THEN c0 (canon o EQT_INTRO) THENL [decide; ALL_TAC]) ORELSE
       (SUBGOAL_THEN (mk_neg c0) (canon o EQF_INTRO) THENL [decide; ALL_TAC]))
      THEN addcands) ORELSE
     FIRST (map split cands)));;

(*** The simulation from step n to the next checkpoint (the heads of the   ***)
(*** loops and the two paths to the returns), with the REP STOSQ of the    ***)
(*** inlined memset                                                        ***)

let rec GLUE_SUH_RUN_TAC prm final n (asl,w) =
  let base = layout prm.suh_fn in
  let lbl l = layout(prm.suh_fn ^ "_" ^ l) - base in
  let off = glue_pc_offset base (glue_current_pc (asl,w)) in
  if n > 1 &&
     mem off [lbl "loop1"; lbl "loop2"; lbl "join2"; lbl "join4"] then
    final (asl,w)
  else if off = prm.suh_stos then
    let sname = "s" ^ string_of_int n in
    (MEMSET_PREP_TAC THEN MEMSET_STEP_TAC prm.suh_exec n THEN
     MEMSET_DONE_TAC `h:int64` 1024 sname THEN
     MP_TAC(SPECL [`h:int64`; `256`; mk_var(sname,`:x86state`)]
             GLUE_ZERO32_BYTES) THEN
     CONV_TAC(LAND_CONV(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV))) THEN
     ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
     GLUE_SUH_NORM_TAC THEN
     GLUE_SUH_RUN_TAC prm final (n + 1)) (asl,w)
  else
    (X86_STEPS_TAC prm.suh_exec [n] THEN GLUE_SUH_NORM_TAC THEN
     (fun g -> if is_cond(glue_current_pc g) then GLUE_SUH_DECIDE_TAC prm g
               else ALL_TAC g) THEN
     GLUE_SUH_RUN_TAC prm final (n + 1)) (asl,w);;

let GLUE_SUH_INIT_PREP_TAC prm =
  let inst = glue_suh_inst prm in
  STRIP_ASSUME_TAC(SPECL [mk_small_numeral prm.suh_omega; `b:num->byte`;
                          `i:num`] GLUE_SUH_BOUNDS) THEN
  SUBGOAL_THEN (inst `val((b:num->byte)(i + OM)) = glue_suh_new OM b i`)
  ASSUME_TAC THENL
   [REWRITE_TAC[glue_suh_new] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  GLUE_INDEX_FACTS_TAC (inst `i + OM`) THEN
  GLUE_INPUT_FORMS_TAC prm [] (inst `i + OM`);;

(*** Decide the conditions and antecedents in the goal from the facts ***)

let GLUE_DECIDE_CONDS_TAC prover =
  W(fun (asl,w) ->
    let ts = find_terms (fun t -> is_cond t || is_imp t) w in
    let cs = setify(map (fun t -> if is_cond t then rand(rator(rator t))
                                  else lhand t) ts) in
    MAP_EVERY (fun c ->
      TRY((SUBGOAL_THEN c MP_TAC THENL
            [prover; DISCH_THEN(fun th -> REWRITE_TAC[EQT_INTRO th])]) ORELSE
          (SUBGOAL_THEN (mk_neg c) MP_TAC THENL
            [prover; DISCH_THEN(fun th -> REWRITE_TAC[EQF_INTRO th])]))) cs);;

let GLUE_SELECT_TAC =
  W(fun (asl,w) ->
    let conds = map (fun t -> rand(rator(rator t))) (find_terms is_cond w) in
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if mem c conds then EQT_INTRO th
      else if is_neg c && mem (rand c) conds then EQF_INTRO th
      else failwith "") asl in
    REWRITE_TAC ths);;

(*** The facts about the counts and the result in the cases of the tests ***)

let GLUE_SUH_COUNTS_TAC prm =
  let om = mk_small_numeral prm.suh_omega
  and kk = mk_small_numeral prm.suh_k in
  let facts = CONV_RULE NUM_REDUCE_CONV
                (SPECL [om; kk; `b:num->byte`; `i:num`] GLUE_SUH_FACTS) in
  let ante = REPEAT CONJ_TAC THEN
             (FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_ARITH_TAC) in
  MAP_EVERY (fun th ->
    TRY(MP_TAC th THEN ANTS_TAC THENL [ante; STRIP_TAC])) (CONJUNCTS facts)
  THEN
  TRY(MP_TAC(SPECL [om; `b:num->byte`; `i:num`] GLUE_SUH_N1) THEN
      ANTS_TAC THENL [ante; ALL_TAC] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC) THEN
  TRY(FIRST_ASSUM(fun th ->
        if can (term_match [] `glue_suh_loop2 omega k (b:num->byte) i`)
               (concl th)
        then MP_TAC(MATCH_MP GLUE_SUH_N2 th) THEN
             CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC
        else NO_TAC));;

(*** The events so far in the goal, from the fact for them ***)

let GLUE_EVENTS_REWRITE_TAC =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read events s`) (lhs c)
    then REWRITE_TAC[th] else NO_TAC);;

(*** A conjunct of the invariant at a checkpoint ***)

let GLUE_SUH_CONJ_TAC =
  let prover = FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_STEPS_ARITH_TAC in
  GLUE_DECIDE_CONDS_TAC prover THEN
  ASM_REWRITE_TAC[glue_suh_steps; mld_unpack_hints_ret; GLUE_SUH_H_0;
                  ARITH_RULE `MIN 0 n = 0`; VAL_WORD_0; ADD_CLAUSES] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN TRY GLUE_WORD_SMALL2_TAC;;

let GLUE_SUH_INIT_FINAL_TAC prm =
  GLUE_SUH_COUNTS_TAC prm THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  W(fun (asl,w) ->
    if is_exists w then
      GLUE_EVENTS_REWRITE_TAC THEN
      REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN GLUE_SELECT_TAC THEN
      DISCHARGE_SAFETY_PROPERTY_TAC
    else GLUE_SUH_CONJ_TAC);;

(*** The counts of iterations are positive only for the cases of the loops ***)

let GLUE_SUH_N1_POS = prove
 (`!omega (b:num->byte) i.
        0 < glue_suh_n1 omega b i
        ==> ~glue_suh_early omega b i /\
            mld_hints_start omega b i < glue_suh_new omega b i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_suh_n1] THEN
  COND_CASES_TAC THENL [ARITH_TAC; ASM_MESON_TAC[]]);;

let GLUE_SUH_N2_POS = prove
 (`!omega k (b:num->byte) i.
        0 < glue_suh_n2 omega k b i ==> glue_suh_loop2 omega k b i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_suh_n2] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let GLUE_SUH_STEPS_POS = prove
 (`!omega k (b:num->byte) i.
        0 < glue_suh_steps omega k b i
        ==> mld_hints_start omega b i <= glue_suh_new omega b i /\
            glue_suh_new omega b i <= omega`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_suh_steps] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~glue_suh_early omega (b:num->byte) i` MP_TAC THENL
   [ASM_CASES_TAC `0 < glue_suh_n1 omega (b:num->byte) i` THENL
     [ASM_MESON_TAC[GLUE_SUH_N1_POS];
      SUBGOAL_THEN `0 < glue_suh_n2 omega k (b:num->byte) i` MP_TAC THENL
       [ASM_ARITH_TAC;
        DISCH_THEN(MP_TAC o MATCH_MP GLUE_SUH_N2_POS) THEN
        SIMP_TAC[glue_suh_loop2]]];
    REWRITE_TAC[glue_suh_early] THEN ARITH_TAC]);;

(*** The facts at the head of an iteration p of the first loop, for the    ***)
(*** position j = s + p: the bytes it loads, and the coefficients other    ***)
(*** than the one it sets                                                  ***)

let GLUE_SUH_PREP1_TAC prm =
  let inst = glue_suh_inst prm in
  let j = inst `mld_hints_start OM (b:num->byte) i + p` in
  SUBGOAL_THEN (inst `p - glue_suh_n1 OM (b:num->byte) i = 0`)
   (fun th -> RULE_ASSUM_TAC(fun t ->
      if can (term_match [] `read R10 s = x`) (concl t)
      then REWRITE_RULE[th; ADD_CLAUSES] t else t)) THENL
   [GLUE_ARITH_TAC; ALL_TAC] THEN
  GLUE_INPUT_FORMS_TAC prm [] j THEN
  GLUE_INPUT_FORMS_TAC prm
   [inst `(SH + mld_hints_start OM (b:num->byte) i + p) + 1`]
   (inst `mld_hints_start OM (b:num->byte) i + p + 1`) THEN
  GLUE_INDEX_FACTS_TAC j THEN
  GLUE_INDEX_FACTS_TAC (inst `glue_suh_new OM (b:num->byte) i`) THEN
  GLUE_INPUT_FORMS_TAC prm [] (inst `glue_suh_new OM (b:num->byte) i`) THEN
  ASSUME_TAC(SPEC (mk_comb(`b:num->byte`,j)) GLUE_VAL_BYTE) THEN
  SUBGOAL_THEN (subst [j,`j:num`] `val(word(val((b:num->byte) j)):int64) =
                                   val(b j)`) ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPEC (mk_comb(`b:num->byte`,j)) GLUE_VAL_BYTE) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (inst `MIN p (glue_suh_n1 OM (b:num->byte) i) = p`)
  ASSUME_TAC THENL
   [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN GLUE_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!q. q < 256 ==> read(memory :> bytes32(word_add h (word(4 * q)))) s =
                          glue_suh_h omega b i n q`) (concl th)
    then
      SUBGOAL_THEN
       (subst [j,`j:num`]
         (inst `!q. q < 256 /\ ~(q = val((b:num->byte) j))
                    ==> read(memory :> bytes32
                          (word_add h (word(4 * q)))) s0 =
                        glue_suh_h OM b i p q`))
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MP_TAC(SPEC `q:num` th) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC]
    else NO_TAC);;

(*** The facts at the head of an iteration p of the second loop, for the   ***)
(*** position m = w + (p - n1) + 1                                         ***)

let GLUE_SUH_PREP2_TAC prm =
  let inst = glue_suh_inst prm in
  let m = inst `glue_suh_new OM (b:num->byte) i +
                 (p - glue_suh_n1 OM b i) + 1` in
  GLUE_INDEX_FACTS_TAC m THEN
  GLUE_INPUT_FORMS_TAC prm [] m;;
(*** The end of an iteration: the invariant for p + 1 ***)

(*** The frame, with the bytes in the addresses of the stores replaced by  ***)
(*** variables, so that their bounds are available to the arithmetic       ***)

let GLUE_FRAME_TAC =
  let isv t =
    try fst(dest_const(rator t)) = "val" && type_of(rand t) = `:byte`
    with Failure _ -> false in
  W(fun (asl,w) ->
    let s0,s1 = rand(rator w),rand w in
    let ok c =
      maychange_term c &&
      (try rand(rator c) = s0 && rand c = s1 with Failure _ -> false) in
    let th = snd(find (fun (_,th) -> ok(concl th)) asl) in
    let vs = setify(find_terms isv (concl th)) in
    MP_TAC th THEN
    MAP_EVERY (fun t -> MP_TAC(SPEC (rand t) GLUE_VAL_BYTE)) vs THEN
    MAP_EVERY (fun t -> SPEC_TAC(t,genvar `:num`)) vs THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(*** PATH_DISCHARGE_TAC, with the byte values in the addresses of the      ***)
(*** events replaced by variables, so that their bounds are available to   ***)
(*** the arithmetic                                                        ***)

let GLUE_GEN_BYTES_TAC =
  let isv t =
    try fst(dest_const(rator t)) = "val" && type_of(rand t) = `:byte` &&
        not(is_var(rand t))
    with Failure _ -> false in
  W(fun (asl,w) ->
    let vs = setify(find_terms isv w) in
    MAP_EVERY (fun t -> MP_TAC(SPEC (rand t) GLUE_VAL_BYTE)) vs THEN
    MAP_EVERY (fun t -> SPEC_TAC(t,genvar `:num`)) vs THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC);;

let GLUE_SELECT_E2_TAC =
  let ise2 th =
    let c = concl th in
    is_eq c && is_var(lhs c) && fst(dest_var(lhs c)) = "e2" in
  W(fun (asl,w) ->
    match filter (ise2 o snd) asl with
      [] -> ALL_TAC
    | (_,th)::_ ->
        let conds = map (fun t -> rand(rator(rator t)))
                        (find_terms is_cond (rhs(concl th))) in
        let ths = mapfilter (fun (_,th) ->
          let c = concl th in
          if mem c conds then EQT_INTRO th
          else if is_neg c && mem (rand c) conds then EQF_INTRO th
          else failwith "") asl in
        RULE_ASSUM_TAC(fun th -> if ise2 th then REWRITE_RULE ths th else th));;

let GLUE_PATH_DISCHARGE_TAC =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN GLUE_SELECT_TAC THEN
  GLUE_SELECT_E2_TAC THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
    else ALL_TAC) THEN
  beta_all THEN
  REWRITE_TAC[NOT_LT] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  GLUE_GEN_BYTES_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(*** The coefficients after an iteration: one more set in the first loop ***)

let GLUE_SUH_H_TAC =
  let prover = FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_STEPS_ARITH_TAC ORELSE
               (ASM_REWRITE_TAC[] THEN GLUE_STEPS_ARITH_TAC) in
  GLUE_DECIDE_CONDS_TAC prover THEN REWRITE_TAC[] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  REWRITE_TAC[MIN] THEN GLUE_DECIDE_CONDS_TAC prover THEN
  REWRITE_TAC[GLUE_SUH_H_ADD1] THEN
  FIRST
   [COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN FIRST_ASSUM ACCEPT_TAC]];
    FIRST_ASSUM(fun th ->
      if is_forall(concl th) && free_in `glue_suh_h` (concl th) then
        MP_TAC(SPEC `q:num` th) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MIN] THEN
        COND_CASES_TAC THEN GLUE_ARITH_TAC
      else NO_TAC)];;

let GLUE_SUH_BODY_CONJ_TAC =
  W(fun (asl,w) ->
    if is_exists w then GLUE_EVENTS_REWRITE_TAC THEN GLUE_PATH_DISCHARGE_TAC
    else if maychange_term w then GLUE_FRAME_TAC
    else if free_in `glue_suh_h` w then GLUE_SUH_H_TAC
    else GLUE_SUH_CONJ_TAC);;

let GLUE_SUH_BODY_FINAL_TAC prm =
  GLUE_SUH_COUNTS_TAC prm THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN GLUE_SUH_BODY_CONJ_TAC;;

(*** The iterations of the loops, in the cases of the paths of the code ***)

let GLUE_DECIDE_ASMS_TAC prover =
  let bad t = can (find_term (fun u -> is_const u &&
                                       fst(dest_const u) = "ENUMERATEL")) t in
  let ok th = let c = concl th in
              not(bad c) &&
              can (find_term (fun t -> is_cond t || is_imp t)) c in
  W(fun (asl,w) ->
    let conds = setify(flat(map (fun (_,th) ->
      map (fun t -> if is_cond t then rand(rator(rator t)) else lhand t)
          (find_terms (fun t -> is_cond t || is_imp t) (concl th)))
      (filter (fun (_,th) -> ok th) asl))) in
    let known c = exists (fun (_,th) -> concl th = c || concl th = mk_neg c) in
    MAP_EVERY (fun c ->
      W(fun (asl,w) ->
        if known c asl then ALL_TAC else
        TRY(SUBGOAL_THEN c ASSUME_TAC THENL [prover; ALL_TAC]) THEN
        TRY(SUBGOAL_THEN (mk_neg c) ASSUME_TAC THENL [prover; ALL_TAC])))
     conds THEN
    W(fun (asl,w) ->
      let eqs = mapfilter (fun (_,th) ->
        let c = concl th in
        if mem c conds then EQT_INTRO th
        else if is_neg c && mem (rand c) conds then EQF_INTRO th
        else failwith "") asl in
      RULE_ASSUM_TAC(fun th -> if ok th then REWRITE_RULE eqs th else th) THEN
      REPEAT(FIRST_X_ASSUM(fun th ->
        let c = concl th in
        if is_conj c && can (find_term (fun t ->
             try fst(dest_const(rator(rator t))) = "read" with Failure _ ->
             false)) c && not(bad c)
        then STRIP_ASSUME_TAC th else NO_TAC))));;

(*** The equation for the events so far, e2 = X, is kept as X = e2 during  ***)
(*** the simulation, so that its rewriting does not expand e2 into X in    ***)
(*** the facts at each step                                                ***)

let GLUE_E2_HIDE_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var(lhs c) && fst(dest_var(lhs c)) = "e2"
    then ASSUME_TAC(SYM th) else NO_TAC);;

let GLUE_E2_SHOW_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var(rhs c) && fst(dest_var(rhs c)) = "e2"
    then
      let eq = SYM th in
      RULE_ASSUM_TAC(fun th' ->
        let c' = concl th' in
        if is_eq c' && can (term_match [] `read events s`) (lhs c')
        then REWRITE_RULE[eq] th' else th') THEN
      REWRITE_TAC[eq] THEN ASSUME_TAC eq
    else NO_TAC);;

(*** The events template in the goal (its function of the iteration and    ***)
(*** its prologue) is abbreviated by variables during the simulation, so   ***)
(*** that its rewriting with the facts at each step does not change it     ***)

let GLUE_TEMPLATE_HIDE_TAC =
  let isapp2 c t =
    is_comb t && is_comb(rator t) &&
    (try fst(dest_const(rator(rator t))) = c with Failure _ -> false) in
  W(fun (asl,w) ->
    let en = find_term (isapp2 "ENUMERATEL") w in
    let f = rand en in
    let ap = find_term (fun t -> isapp2 "APPEND" t && lhand t = en) w in
    let pr = rand ap in
    ABBREV_TAC (mk_eq(mk_var("evf",type_of f),f)) THEN
    ABBREV_TAC (mk_eq(mk_var("evp",type_of pr),pr)));;

let GLUE_TEMPLATE_SHOW_TAC =
  let expand s =
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && is_var(rhs c) &&
         (let v = fst(dest_var(rhs c)) in
          String.length v >= 3 && String.sub v 0 3 = s) then
        RULE_ASSUM_TAC(REWRITE_RULE[SYM th]) THEN REWRITE_TAC[SYM th]
      else NO_TAC) in
  expand "evp" THEN expand "evf";;

let GLUE_SUH_ITER_TAC prm prep =
  let prover = FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_STEPS_ARITH_TAC in
  GLUE_SUH_COUNTS_TAC prm THEN FULL_INIT_TAC THEN
  GLUE_DECIDE_ASMS_TAC prover THEN prep THEN
  GLUE_TEMPLATE_HIDE_TAC THEN GLUE_E2_HIDE_TAC THEN
  GLUE_SUH_RUN_TAC prm
   (GLUE_E2_SHOW_TAC THEN GLUE_TEMPLATE_SHOW_TAC THEN
    GLUE_SUH_BODY_FINAL_TAC prm) 1;;

let GLUE_SUH_BODY_GEN_TAC prm it1 it2 =
  let inst = glue_suh_inst prm in
  let om = mk_small_numeral prm.suh_omega and kk = mk_small_numeral prm.suh_k in
  let n1 = inst `glue_suh_n1 OM (b:num->byte) i`
  and ok1 = inst `glue_suh_ok1 OM (b:num->byte) i`
  and zs = inst `glue_suh_zeros OM (b:num->byte) i`
  and ok = inst `mld_unpack_hints_ok OM KK (b:num->byte) i` in
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC(SPECL [om; `b:num->byte`; `i:num`] GLUE_SUH_BOUNDS) THEN
  MP_TAC(SPECL [om; kk; `b:num->byte`; `i:num`] GLUE_SUH_STEPS_POS) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC (mk_binary "<" (`p:num`,n1)) THENL
   [MP_TAC(SPECL [om; `b:num->byte`; `i:num`] GLUE_SUH_N1_POS) THEN
    ANTS_TAC THENL [GLUE_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(SPECL [om; `b:num->byte`; `i:num`] GLUE_SUH_N1) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    ASM_CASES_TAC (mk_binary "<" (`p + 1`,n1)) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
        is_forall(concl th) && free_in n1 (concl th))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN it1;
      ASM_CASES_TAC ok1 THENL
       [FIRST_ASSUM(fun th ->
          if is_iff(concl th) && lhand(concl th) = ok1 then
            FIRST_ASSUM(fun th1 ->
              if concl th1 = ok1 then ASSUME_TAC(EQ_MP th th1) else NO_TAC)
          else NO_TAC) THEN
        ASM_CASES_TAC (inst `i < KM1`) THENL
         [it1;
          ASM_CASES_TAC (inst `OM <= glue_suh_new OM (b:num->byte) i`) THENL
           [it1;
            ASM_CASES_TAC
             (inst `(b:num->byte)(glue_suh_new OM b i) = word 0`) THEN it1]];
        FIRST_X_ASSUM(MP_TAC o check (fun th ->
          is_imp(concl th) && is_neg(lhand(concl th)))) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
        SUBGOAL_THEN (inst `mld_hints_start OM (b:num->byte) i +
                            glue_suh_n1 OM b i =
                            mld_hints_start OM b i + p + 1 /\
                            (mld_hints_start OM b i + glue_suh_n1 OM b i) - 1 =
                            mld_hints_start OM b i + p`)
         (fun th -> RULE_ASSUM_TAC(fun t ->
            if free_in `val:byte->num` (concl t) then REWRITE_RULE[th] t
            else t)) THENL
         [GLUE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN (inst `~(mld_hints_start OM (b:num->byte) i +
                              glue_suh_n1 OM b i = glue_suh_new OM b i)`)
        ASSUME_TAC THENL [GLUE_ARITH_TAC; ALL_TAC] THEN it1]];
    SUBGOAL_THEN (inst `0 < glue_suh_n2 OM KK (b:num->byte) i`) ASSUME_TAC THENL
     [GLUE_STEPS_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GLUE_SUH_N2_POS) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GLUE_SUH_N2) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    ASM_CASES_TAC (inst `p + 1 < glue_suh_steps OM KK (b:num->byte) i`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC (inst `p - glue_suh_n1 OM (b:num->byte) i`) o
        check (fun th -> is_forall(concl th) &&
                         free_in `glue_suh_n2` (concl th))) THEN
      ANTS_TAC THENL [GLUE_STEPS_ARITH_TAC; STRIP_TAC] THEN it2;
      SUBGOAL_THEN (inst `p - glue_suh_n1 OM (b:num->byte) i + 1 <=
                          glue_suh_n2 OM KK b i /\
                          glue_suh_n2 OM KK b i <=
                          p - glue_suh_n1 OM (b:num->byte) i + 1`)
      STRIP_ASSUME_TAC THENL [GLUE_STEPS_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th ->
        if can (term_match [] `glue_suh_loop2 omega k (b:num->byte) i`)
               (concl th)
        then ASSUME_TAC(MATCH_MP GLUE_SUH_LOOP2_OK th) else NO_TAC) THEN
      ASM_CASES_TAC zs THENL
       [FIRST_ASSUM(fun th ->
          if is_iff(concl th) && lhand(concl th) = zs then
            FIRST_ASSUM(fun th1 ->
              if concl th1 = zs then ASSUME_TAC(EQ_MP th th1) else NO_TAC)
          else NO_TAC) THEN
        FIRST_X_ASSUM(fun th ->
          if is_iff(concl th) && lhand(concl th) = ok then
            FIRST_ASSUM(fun th1 ->
              if concl th1 = zs then ASSUME_TAC(EQ_MP (SYM th) th1)
              else NO_TAC)
          else NO_TAC) THEN
        it2;
        FIRST_X_ASSUM(fun th ->
          if is_iff(concl th) && lhand(concl th) = ok then
            FIRST_ASSUM(fun th1 ->
              if concl th1 = mk_neg zs then
                ASSUME_TAC(REWRITE_RULE[GSYM th] th1)
              else NO_TAC)
          else NO_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th ->
          is_imp(concl th) && is_neg(lhand(concl th)) &&
          free_in `glue_suh_zeros` (concl th))) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
        SUBGOAL_THEN (inst `~(glue_suh_new OM (b:num->byte) i +
                              glue_suh_n2 OM KK b i = OM)`)
        ASSUME_TAC THENL [GLUE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN (inst `glue_suh_new OM (b:num->byte) i +
                            glue_suh_n2 OM KK b i =
                            glue_suh_new OM b i + (p - glue_suh_n1 OM b i) + 1`)
         (fun th -> RULE_ASSUM_TAC(fun t ->
            if is_neg(concl t) && free_in `word 0:byte` (concl t)
            then REWRITE_RULE[th] t else t)) THENL
         [GLUE_STEPS_ARITH_TAC; ALL_TAC] THEN it2]]];;

let GLUE_SUH_BODY_TAC prm =
  GLUE_SUH_BODY_GEN_TAC prm
   (GLUE_SUH_ITER_TAC prm (GLUE_SUH_PREP1_TAC prm))
   (GLUE_SUH_ITER_TAC prm (GLUE_SUH_PREP2_TAC prm));;


(*** The coefficients at the end, when the hints are well formed ***)

let GLUE_SUH_OK_N1 = prove
 (`!omega k (b:num->byte) i.
        mld_unpack_hints_ok omega k b i
        ==> mld_hints_start omega b i + glue_suh_n1 omega b i =
            glue_suh_new omega b i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GLUE_SUH_OK] THEN STRIP_TAC THEN
  ASM_CASES_TAC `mld_hints_start omega (b:num->byte) i <
                 glue_suh_new omega b i` THENL
   [MP_TAC(SPECL [`omega:num`; `b:num->byte`; `i:num`] GLUE_SUH_N1) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    UNDISCH_TAC `~glue_suh_early omega (b:num->byte) i` THEN
    ASM_REWRITE_TAC[glue_suh_n1; glue_suh_early] THEN ASM_ARITH_TAC]);;

(*** The return from the checkpoint at the end ***)

let GLUE_SUH_EXIT_TAC prm =
  let inst = glue_suh_inst prm in
  let om = mk_small_numeral prm.suh_omega and kk = mk_small_numeral prm.suh_k in
  let ok = inst `mld_unpack_hints_ok OM KK (b:num->byte) i` in
  ASM_CASES_TAC ok THEN
  ASM_REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  GLUE_TEMPLATE_HIDE_TAC THEN GLUE_E2_HIDE_TAC THEN
  X86_STEPS_TAC prm.suh_exec (1--4) THEN
  GLUE_E2_SHOW_TAC THEN GLUE_TEMPLATE_SHOW_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  W(fun (asl,w) ->
    if is_exists w then
      GLUE_EVENTS_REWRITE_TAC THEN GLUE_SELECT_TAC THEN
      DISCHARGE_SAFETY_PROPERTY_TAC
    else
      ASM_REWRITE_TAC[mld_unpack_hints_ret] THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      TRY(X_GEN_TAC `q:num` THEN DISCH_TAC THEN
          FIRST_ASSUM(fun th ->
            if is_forall(concl th) && free_in `glue_suh_h` (concl th)
            then MP_TAC(SPEC `q:num` th) THEN
                 ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]
            else NO_TAC) THEN
          SUBGOAL_THEN
           (inst `MIN (glue_suh_steps OM KK (b:num->byte) i)
                      (glue_suh_n1 OM b i) = glue_suh_n1 OM b i`)
          SUBST1_TAC THENL
           [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN GLUE_STEPS_ARITH_TAC;
            ALL_TAC] THEN
          MATCH_MP_TAC GLUE_SUH_H_FULL THEN
          MATCH_MP_TAC(SPECL [om; kk] GLUE_SUH_OK_N1) THEN
          FIRST_ASSUM ACCEPT_TAC));;

(*** The whole proof ***)

let GLUE_SUH_FULL_TAC prm =
  GLUE_SUH_SETUP_TAC prm THEN
  REPEAT CONJ_TAC THENL
   [FULL_INIT_TAC THEN GLUE_SUH_INIT_PREP_TAC prm THEN
    GLUE_SUH_RUN_TAC prm (GLUE_SUH_INIT_FINAL_TAC prm) 1;
    GLUE_SUH_BODY_TAC prm;
    GLUE_SUH_EXIT_TAC prm];;

(* ------------------------------------------------------------------------- *)
(* The loop of mld_pack_sig_h, as one loop over the positions p of the       *)
(* vector (coefficient p MOD 256 of polynomial p DIV 256). With hint bits h, *)
(* the code goes through glue_hint_steps omega n h of the n positions: all   *)
(* of them if there are at most omega hints, else up to the first that does  *)
(* not fit (glue_hint_fail omega h p), where it returns.                     *)
(* ------------------------------------------------------------------------- *)

let glue_hint_fail = new_definition
 `glue_hint_fail omega (h:num->bool) p <=>
    h p /\ mld_hint_count h p = omega`;;

let glue_hint_steps = new_definition
 `glue_hint_steps omega n (h:num->bool) =
    if mld_hint_count h n <= omega then n
    else (minimal p. glue_hint_fail omega h p) + 1`;;

let GLUE_HINT_FAIL_EXISTS = prove
 (`!h omega n. ~(mld_hint_count h n <= omega)
               ==> ?p. p < n /\ glue_hint_fail omega h p`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[mld_hint_count; LE_0; glue_hint_fail] THEN
  ASM_CASES_TAC `mld_hint_count h n <= omega` THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[LT] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[glue_hint_fail] THEN MESON_TAC[LT]]);;

let GLUE_HINT_STEPS = prove
 (`!h omega n.
        let np = glue_hint_steps omega n h in
        np <= n /\
        (0 < n ==> 0 < np) /\
        (mld_hint_count h n <= omega ==> np = n) /\
        (!p. p < np ==> mld_hint_count h p <= omega) /\
        (!p. p < np
             ==> (glue_hint_fail omega h p <=>
                  p + 1 = np /\ ~(mld_hint_count h n <= omega)))`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[glue_hint_steps] THEN
  ASM_CASES_TAC `mld_hint_count h n <= omega` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[LE_REFL; glue_hint_fail] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MLD_HINT_COUNT_MONO; LT_IMP_LE; LE_TRANS]; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`h:num->bool`; `p + 1`; `n:num`] MLD_HINT_COUNT_MONO) THEN
    ASM_REWRITE_TAC[MLD_HINT_COUNT_ADD1] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:num->bool`; `omega:num`; `n:num`] GLUE_HINT_FAIL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?p. glue_hint_fail omega (h:num->bool) p` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN BETA_TAC THEN
  ABBREV_TAC `m = minimal p. glue_hint_fail omega (h:num->bool) p` THEN
  REWRITE_TAC[glue_hint_fail] THEN STRIP_TAC THEN
  SUBGOAL_THEN `m < n` ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM NOT_LT] THEN ASM_MESON_TAC[glue_hint_fail];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p <= m ==> mld_hint_count h p <= omega` ASSUME_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[mld_hint_count; LE_0] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[glue_hint_fail]] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ARITH_TAC;
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[EQ_ADD_RCANCEL] THEN EQ_TAC THENL
     [STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM NOT_LT] THEN ASM_MESON_TAC[glue_hint_fail];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The tests of the code for the hint of a coefficient a0 with high part a1: *)
(* a0 + gamma2 <= 2 * gamma2 as unsigned 32-bit numbers (a0 is within        *)
(* [-gamma2, gamma2], glue_hint_inr_88/32, GLUE_INR_VAL), and then, on x86,  *)
(* a0 = -gamma2 and a1 <> 0 with two comparisons and branches.               *)
(* ------------------------------------------------------------------------- *)

let glue_hint_inr_88 = new_definition
 `glue_hint_inr_88 (a:int32) <=> -- &95232 <= ival a /\ ival a <= &95232`;;

let glue_hint_inr_32 = new_definition
 `glue_hint_inr_32 (a:int32) <=> -- &261888 <= ival a /\ ival a <= &261888`;;

let GLUE_INR_VAL = prove
 (`!a:int32 g.
        2 * g < 2 EXP 31
        ==> (val(word_add a (word g)) <= 2 * g <=>
             -- &g <= ival a /\ ival a <= &g)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD_CASES; INT_IVAL; DIMINDEX_32; VAL_WORD] THEN
  MP_TAC(ISPEC `a:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `g MOD 4294967296 = g` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[INT_ARITH `-- &g:int <= &x - &n <=> &n:int <= &x + &g`;
              INT_ARITH `&x - &n:int <= &g <=> &x:int <= &g + &n`;
              INT_ARITH `-- &g:int <= &x`; INT_OF_NUM_ADD; INT_OF_NUM_LE] THEN
  ASM_ARITH_TAC);;

let GLUE_INR_88 = prove
 (`!a:int32. val(word_add a (word 95232)) <= 190464 <=> glue_hint_inr_88 a`,
  GEN_TAC THEN REWRITE_TAC[glue_hint_inr_88] THEN
  MP_TAC(SPECL [`a:int32`; `95232`] GLUE_INR_VAL) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let GLUE_INR_32 = prove
 (`!a:int32. val(word_add a (word 261888)) <= 523776 <=> glue_hint_inr_32 a`,
  GEN_TAC THEN REWRITE_TAC[glue_hint_inr_32] THEN
  MP_TAC(SPECL [`a:int32`; `261888`] GLUE_INR_VAL) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(*** The hint bit when a0 is out of range, and when it is within it ***)

let GLUE_HINT_OUT_88 = prove
 (`!a0 a1. ~glue_hint_inr_88 a0 ==> mld_make_hint_88 a0 a1`,
  REWRITE_TAC[glue_hint_inr_88; mld_make_hint_88] THEN INT_ARITH_TAC);;

let GLUE_HINT_OUT_32 = prove
 (`!a0 a1. ~glue_hint_inr_32 a0 ==> mld_make_hint_32 a0 a1`,
  REWRITE_TAC[glue_hint_inr_32; mld_make_hint_32] THEN INT_ARITH_TAC);;

let GLUE_HINT_INR_88 = prove
 (`!a0 a1. glue_hint_inr_88 a0
           ==> (mld_make_hint_88 a0 a1 <=>
                ~(a1 = word 0) /\ a0 = word 4294872064)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_hint_inr_88; mld_make_hint_88] THEN
  SUBGOAL_THEN `(a0:int32) = word 4294872064 <=> ival a0 = -- &95232`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IVAL_EQ] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a1:int32 = word 0` THEN ASM_REWRITE_TAC[] THEN
  INT_ARITH_TAC);;

let GLUE_HINT_INR_32 = prove
 (`!a0 a1. glue_hint_inr_32 a0
           ==> (mld_make_hint_32 a0 a1 <=>
                ~(a1 = word 0) /\ a0 = word 4294705408)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_hint_inr_32; mld_make_hint_32] THEN
  SUBGOAL_THEN `(a0:int32) = word 4294705408 <=> ival a0 = -- &261888`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IVAL_EQ] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a1:int32 = word 0` THEN ASM_REWRITE_TAC[] THEN
  INT_ARITH_TAC);;

(*** The hint bit of position i, from the coefficient of w0 and the one of ***)
(*** w1 that the code unpacks into the scratch polynomial ***)

let GLUE_POLYVEC_HINT_88 = prove
 (`!x b i. mld_polyvec_make_hint_88 x b i <=>
           mld_make_hint_88 (x i)
            (mld_polyw1_unpack_88 (\t. b(192 * i DIV 256 + t)) (i MOD 256))`,
  REWRITE_TAC[mld_polyvec_make_hint_88; mld_polyvec_unpack; mld_polyvec]);;

let GLUE_POLYVEC_HINT_32 = prove
 (`!x b i. mld_polyvec_make_hint_32 x b i <=>
           mld_make_hint_32 (x i)
            (mld_polyw1_unpack_32 (\t. b(128 * i DIV 256 + t)) (i MOD 256))`,
  REWRITE_TAC[mld_polyvec_make_hint_32; mld_polyvec_unpack; mld_polyvec]);;

(*** The position after i, in the same polynomial or the next one ***)

let GLUE_MOD_NEXT = prove
 (`!i. (i MOD 256 < 255
        ==> (i + 1) MOD 256 = i MOD 256 + 1 /\ (i + 1) DIV 256 = i DIV 256) /\
       (~(i MOD 256 < 255)
        ==> (i + 1) MOD 256 = 0 /\ (i + 1) DIV 256 = i DIV 256 + 1 /\
            256 * (i DIV 256 + 1) = i + 1)`,
  GEN_TAC THEN MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  ABBREV_TAC `q = i DIV 256` THEN ABBREV_TAC `r = i MOD 256` THEN
  STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r + 1` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q + 1` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(*** The number of positions after the step for position i ***)

let GLUE_HINT_NEXT = prove
 (`!h omega n i.
        i < glue_hint_steps omega n h
        ==> (glue_hint_fail omega h i
             ==> glue_hint_steps omega n h = i + 1 /\
                 ~(mld_hint_count h n <= omega)) /\
            (~glue_hint_fail omega h i /\ i + 1 < n
             ==> i + 1 < glue_hint_steps omega n h /\
                 ~(i + 1 = glue_hint_steps omega n h)) /\
            (~glue_hint_fail omega h i /\ i + 1 = n
             ==> glue_hint_steps omega n h = i + 1 /\
                 mld_hint_count h n <= omega)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`h:num->bool`; `omega:num`; `n:num`] GLUE_HINT_STEPS) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `np = glue_hint_steps omega n h` THEN STRIP_TAC THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `mld_hint_count h n <= omega` THEN
  ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The proof of a FULL theorem for mld_pack_sig_h. Its loop over the         *)
(* polynomials, with the unpacking of w1 into the scratch polynomial, and    *)
(* the loop over their coefficients are one loop over the positions i, from  *)
(* the head of the inner loop (label join4) to the next head or to the       *)
(* epilogue (join6), whose iteration for i goes through one of the paths of  *)
(* the code: the range test of the coefficient a0 of w0                      *)
(* (glue_hint_inr_88/32), for those within the range the tests of            *)
(* a0 = -gamma2 and of the hint bit, the test of the count of the hints so   *)
(* far against omega (glue_hint_fail) and the tests of the index             *)
(* (i MOD 256 < 255) and of the polynomial (i DIV 256 < k - 1). The events   *)
(* template has one function for each path, with two for the coefficients    *)
(* within the range without a hint (as the test of a0 = -gamma2 comes        *)
(* first). GLUE_PSH_RUN_TAC simulates the iteration from the head, splitting *)
(* the goal at each branch on these predicates (GLUE_PSH_DECIDE_TAC), and    *)
(* proves the invariant for i + 1 at the end of each path                    *)
(* (GLUE_PSH_FINAL_TAC). The parameters prm give the code, the hint bits and *)
(* the constants of the parameter set, and psh_stos the offset of the REP    *)
(* STOSQ of the memset of the hints, or 0 for mldsa65, where gcc inlines it  *)
(* as 128-bit stores.                                                        *)
(* ------------------------------------------------------------------------- *)

type glue_psh =
 { psh_exec : thm * thm option array;
   psh_fn : string;
   psh_callee : string;
   psh_hintf : term;
   psh_inrf : term;
   psh_unpackf : term;
   psh_inr_val : thm;
   psh_inr : thm;
   psh_out : thm;
   psh_unfold : thm;
   psh_omega : int;
   psh_k : int;
   psh_wbytes : int;
   psh_sigh : int;
   psh_gamma : int;
   psh_stos : int };;

let glue_psh_hint prm =
  list_mk_comb(prm.psh_hintf,[`x:num->int32`; `b:num->byte`]);;

let glue_psh_vars =
  [`x:num->int32`; `b:num->byte`; `sig:int64`; `w0:int64`; `w1p:int64`;
   `scratch:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`;
   `i:num`];;

let glue_psh_inst prm tm =
  let n = mk_small_numeral in
  vsubst [glue_psh_hint prm,`H:num->bool`;
          prm.psh_hintf,`HF:(num->int32)->(num->byte)->num->bool`;
          prm.psh_inrf,`IF:int32->bool`;
          prm.psh_unpackf,`UNPACK:(num->byte)->num->int32`;
          n prm.psh_omega,`OM:num`;
          n (256 * prm.psh_k),`NN:num`; n prm.psh_k,`KK:num`;
          n (prm.psh_k - 1),`KM1:num`; n prm.psh_wbytes,`WB:num`;
          n (prm.psh_wbytes * prm.psh_k),`WK:num`;
          n (1024 * prm.psh_k),`XK:num`;
          n prm.psh_sigh,`SH:num`; n (prm.psh_sigh + prm.psh_omega),`ST:num`;
          n prm.psh_gamma,`GA:num`; n (2 * prm.psh_gamma),`G2:num`;
          n (4294967296 - prm.psh_gamma),`GN:num`]
         tm;;

(*** The events template: one function for each path of an iteration ***)

let glue_psh_template prm = glue_psh_inst prm
 `\(x:num->int32) (b:num->byte) (sig:int64) (w0:int64) (w1p:int64)
   (scratch:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
   APPEND
    (f_ev_epil x b sig w0 w1p scratch pc stackpointer returnaddress)
    (APPEND
      (ENUMERATEL (glue_hint_steps OM NN (HF x b))
        (\p. if glue_hint_fail OM (HF x b) p
             then if IF (x p)
                  then f_ev_f2 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
                  else f_ev_f1 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
             else if p MOD 256 < 255
             then if HF x b p
                  then if IF (x p)
                       then f_ev_m2 x b sig w0 w1p scratch pc stackpointer
                                    returnaddress p
                       else f_ev_m1 x b sig w0 w1p scratch pc stackpointer
                                    returnaddress p
                  else if x p = word GN
                  then f_ev_m4 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
                  else f_ev_m3 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
             else if p DIV 256 < KM1
             then if HF x b p
                  then if IF (x p)
                       then f_ev_e2 x b sig w0 w1p scratch pc stackpointer
                                    returnaddress p
                       else f_ev_e1 x b sig w0 w1p scratch pc stackpointer
                                    returnaddress p
                  else if x p = word GN
                  then f_ev_e4 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
                  else f_ev_e3 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
             else if HF x b p
             then if IF (x p)
                  then f_ev_l2 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
                  else f_ev_l1 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
             else if x p = word GN
             then f_ev_l4 x b sig w0 w1p scratch pc stackpointer
                          returnaddress p
             else f_ev_l3 x b sig w0 w1p scratch pc stackpointer
                          returnaddress p))
      (f_ev_prol x b sig w0 w1p scratch pc stackpointer returnaddress))
   :(uarch_event)list`;;

(*** The invariant at the head for position i: the registers and the       ***)
(*** stack, the inputs, the registers and the scratch polynomial for i if  ***)
(*** the code goes through it, the hint bytes so far if the code goes      ***)
(*** through i or there are at most omega hints, and the return value at   ***)
(*** the end                                                               ***)

let glue_psh_inv prm = glue_psh_inst prm
 `\i s.
  read RSP s = word_add stackpointer (word 8) /\
  read R13 s = scratch /\ read R15 s = word_add sig (word SH) /\
  read (memory :> bytes64 (word_add stackpointer (word 16))) s =
    word_add w1p (word WK) /\
  read (memory :> bytes64 (word_add stackpointer (word 32))) s = rbx_init /\
  read (memory :> bytes64 (word_add stackpointer (word 40))) s = rbp_init /\
  read (memory :> bytes64 (word_add stackpointer (word 48))) s = r12_init /\
  read (memory :> bytes64 (word_add stackpointer (word 56))) s = r13_init /\
  read (memory :> bytes64 (word_add stackpointer (word 64))) s = r14_init /\
  read (memory :> bytes64 (word_add stackpointer (word 72))) s = r15_init /\
  read (memory :> bytes64 (word_add stackpointer (word 80))) s =
    returnaddress /\
  (!q. q < NN
       ==> read(memory :> bytes32(word_add w0 (word(4 * q)))) s = x q) /\
  (!j. j < WK ==> read(memory :> bytes8(word_add w1p (word j))) s = b j) /\
  (i < glue_hint_steps OM NN H
   ==> read RAX s = word(i MOD 256) /\
       read RBX s = word(mld_hint_count H i) /\
       read R14 s = word_add w0 (word(1024 * i DIV 256)) /\
       read RBP s = word_add sig (word(ST + i DIV 256)) /\
       read R12 s = word_add w1p (word(WB * i DIV 256)) /\
       (!j. j < 256
            ==> read(memory :> bytes32(word_add scratch (word(4 * j)))) s =
                UNPACK (\t. b(WB * i DIV 256 + t)) j)) /\
  (i < glue_hint_steps OM NN H \/ mld_hint_count H NN <= OM
   ==> (!t. t < OM
            ==> read(memory :> bytes8(word_add sig (word(SH + t)))) s =
                mld_hint_index H i t) /\
       (!t. t < KK
            ==> read(memory :> bytes8(word_add sig (word(ST + t)))) s =
                if t < i DIV 256 then word(mld_hint_count H (256 * (t + 1)))
                else word 0)) /\
  (i = glue_hint_steps OM NN H
   ==> read RAX s = word_zx(mld_pack_hints_ret OM KK H))`;;

let GLUE_PSH_SETUP_TAC prm calleeth =
  let inst = glue_psh_inst prm in
  let np = inst `glue_hint_steps OM NN H` in
  let lbl l =
    mk_binary "+" (`pc:num`,mk_small_numeral(layout(prm.psh_fn ^ "_" ^ l))) in
  ASSUME_CALLEE_SAFETY_TAILED_TAC calleeth "H_UNPACK" THEN
  CONCRETIZE_F_EVENTS_TAC (glue_psh_template prm) THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst prm.psh_exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [glue_psh_hint prm; mk_small_numeral prm.psh_omega;
                mk_small_numeral(256 * prm.psh_k)] GLUE_HINT_STEPS) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC np (lbl "join4") (lbl "join6")
    (glue_psh_inv prm);;

(*** The call of the function unpacking w1, at step n (the callee) ***)

let GLUE_PSH_CALL_TAC prm (b':term) (slice:term) n =
  let sv = mk_var("s"^string_of_int(n-1),`:x86state`) in
  SUBGOAL_THEN (vsubst [sv,`s:x86state`] slice) ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc prm.psh_exec "H_UNPACK"
   [`read RDI s`; `read RSI s`; b'; `pc:num`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`] glue_psh_vars n;;

(* ------------------------------------------------------------------------- *)
(* The memset of the n = omega + k bytes of the hints at st that gcc inlines *)
(* for mldsa44 and mldsa87 (n = 84 and 83), as zero quadword stores at st    *)
(* and st + n - 8 and a REP STOSQ of (val st MOD 8 + n - 8) DIV 8 quadwords  *)
(* from the first multiple of 8 above st, st + (8 - val st MOD 8)            *)
(* (MEMSET_ALIGN_ADDR). As n is not a multiple of 8, the count depends       *)
(* on st (GLUE_STOS_COUNT, from its form in the simulation by bit-blasting), *)
(* unlike the memsets of MEMSET_PREP_TAC. Before the REP STOSQ,              *)
(* GLUE_PSH_STOS_PREP_TAC abbreviates zk = val st MOD 8, the count zq, its   *)
(* word zc and the tail zt, with 8 * zq + zt = zk + n - 8, so that the       *)
(* simulation can use their arithmetic, and splits the two quadwords into    *)
(* their parts outside the memory that the REP STOSQ clears.                 *)
(* GLUE_PSH_STOS_STEP_TAC steps it, and GLUE_PSH_STOS_DONE_TAC puts the      *)
(* three parts together as the n zero bytes at st, weakens the frame of the  *)
(* simulation to these n bytes and expands the abbreviations, which the      *)
(* events of the template cannot use. GLUE_STOS_SAFETY_TAC proves the events *)
(* of the code before the loop, with the bounds of the memory accesses of    *)
(* the REP STOSQ from the same abbreviations, and GLUE_ZERO_FINAL_TAC the    *)
(* zero bytes of the hints at its end. As the ABI requires on entry, the     *)
(* direction flag DF must be clear.                                          *)
(* ------------------------------------------------------------------------- *)

(*** The count of the REP STOSQ, the parts of the n bytes and their bytes ***)

let GLUE_STOS_COUNT = prove
 (`!st:int64 m.
        m < 2 EXP 32
        ==> word_ushr (word_add (word_and st (word 7)) (word m)) 3 =
            word((val st MOD 8 + m) DIV 8)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_and st (word 7):int64) = val st MOD 8` ASSUME_TAC
  THENL
   [REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `7 = 2 EXP 3 - 1`] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 3 = 8`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`val(st:int64)`; `8`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_64] THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`val(st:int64) MOD 8`,`k:num`) THEN
  REPEAT STRIP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`k + m:num`; `8`] DIV_LE) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  SUBGOAL_THEN `m MOD 18446744073709551616 = m /\
                (k + m) MOD 18446744073709551616 = k + m /\
                ((k + m) DIV 8) MOD 18446744073709551616 = (k + m) DIV 8`
   (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN SIMPLE_ARITH_TAC);;

let GLUE_STOS_SPLIT = prove
 (`!k m. k < 8 /\ m < 2 EXP 32
         ==> 8 * ((k + m) DIV 8) + (k + m) MOD 8 = k + m /\
             (k + m) MOD 8 < 8 /\
             val(word((k + m) DIV 8):int64) = (k + m) DIV 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`k + m:num`; `8`] DIVISION) THEN ARITH_TAC;
    ARITH_TAC;
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPECL [`k + m:num`; `8`] DIV_LE) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV
    THEN SIMPLE_ARITH_TAC]);;

let GLUE_ZERO_COMBINE = prove
 (`!a:int64 p q s:x86state.
        read (memory :> bytes(a,p)) s = 0 /\
        read (memory :> bytes(word_add a (word p),q)) s = 0
        ==> read (memory :> bytes(a,p + q)) s = 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let GLUE_ZERO_BYTES8 = prove
 (`!a:int64 n s:x86state.
        read (memory :> bytes(a,n)) s = 0
        ==> !i. i < n
                ==> read (memory :> bytes8 (word_add a (word i))) s = word 0`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!x. read (memory :> bytes(a,n)) s = x
        ==> !i. i < n
                ==> read (memory :> bytes8 (word_add a (word i))) s =
                    word((x DIV 2 EXP (8 * i)) MOD 2 EXP 8)`
   (fun th -> DISCH_THEN(MP_TAC o MATCH_MP th) THEN
              REWRITE_TAC[DIV_0; MOD_0]) THEN
  GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 2 EXP (8 * 1)`; READ_BYTES_MOD] THEN
  ASM_SIMP_TAC[ARITH_RULE `i < k ==> MIN (k - i) 1 = 1`] THEN
  REWRITE_TAC[READ_BYTES_1; BYTES8_ELEMENT; READ_ELEMENT; WORD_VAL]);;

let GLUE_ZERO_BYTES8_OFFSET = prove
 (`!sig:int64 k n e m s:x86state.
        read (memory :> bytes(word_add sig (word k),n)) s = 0 /\
        k <= e /\ e + m <= k + n
        ==> !t. t < m
                ==> read (memory :> bytes8(word_add sig (word(e + t)))) s =
                    word 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(e - k) + t:num` o
    MATCH_MP GLUE_ZERO_BYTES8) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  SUBGOAL_THEN `k + (e - k) + t = e + t` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; REWRITE_TAC[]]);;

(*** The address sig + SH of the hints, and the number of their bytes ***)

let glue_psh_st prm =
  mk_binop `word_add:int64->int64->int64` `sig:int64`
   (mk_comb(`word:num->int64`,mk_small_numeral prm.psh_sigh));;

let glue_psh_nb prm = prm.psh_omega + prm.psh_k;;

(*** The preparation for the REP STOSQ, in the state before it ***)

let GLUE_PSH_STOS_PREP_TAC prm =
  let nb = glue_psh_nb prm and st = glue_psh_st prm in
  let mkw n = mk_comb(`word:num->int64`,mk_small_numeral n) in
  let addw a n = mk_binop `word_add:int64->int64->int64` a (mkw n) in
  let st8 = addw `sig:int64` (prm.psh_sigh + 8)
  and hi = addw `sig:int64` (prm.psh_sigh + nb - 8)
  and mt = mk_small_numeral(nb - 8) in
  let ath = REWRITE_RULE[GSYM(WORD_RULE(mk_eq(st8,addw st 8)))]
             (SPEC st MEMSET_ALIGN_ADDR) in
  let cnt = subst [st,`st:int64`; mt,`m:num`]
   `word_ushr (word_add (word_and st (word 7)) (word m)) 3:int64` in
  let cth = MP (SPECL [st; mt] GLUE_STOS_COUNT)
               (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` mt
                                           `2 EXP 32`))) in
  let kt = mk_binop `MOD` (mk_comb(`val:int64->num`,st)) `8` in
  let is_reg r sv th =
    let c = concl th in
    is_eq c && lhand c = list_mk_icomb "read" [r; sv] in
  let rewr_count sv th =
    if is_reg `RCX` sv th then
      TRANS th (TRANS (BITBLAST_RULE(mk_eq(rand(concl th),cnt))) cth)
    else th in
  let is_zero64 a th =
    can (term_match []
          `read (memory :> bytes64 (a:int64)) (s:x86state) = word 0`)
        (concl th) &&
    rand(rand(lhand(lhand(concl th)))) = a in
  W(fun (asl,w) ->
    let sv = rand w in
    RULE_ASSUM_TAC(rewr_count sv) THEN
    RULE_ASSUM_TAC(fun th -> if is_reg `RDI` sv th then REWRITE_RULE[ath] th
                             else th)) THEN
  MP_TAC(REWRITE_RULE[ARITH_EQ] (SPECL [mk_comb(`val:int64->num`,st); `8`]
                                   MOD_LT_EQ)) THEN
  DISCH_TAC THEN
  ABBREV_TAC (mk_eq(`zk:num`,kt)) THEN
  MP_TAC(SPECL [`zk:num`; mt] GLUE_STOS_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                  STRIP_TAC] THEN
  ABBREV_TAC (subst [mt,`m:num`] `zq = (zk + m) DIV 8`) THEN
  ABBREV_TAC (subst [mt,`m:num`] `zt = (zk + m) MOD 8`) THEN
  ABBREV_TAC `zc = word zq:int64` THEN
  FIRST_X_ASSUM(fun th ->
    if is_zero64 st th
    then ASSUME_TAC(CONJUNCT1(MATCH_MP READ_MEMORY_BYTES64_ZERO_SPLIT
                     (CONJ th (ARITH_RULE `8 - zk <= 8`))))
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_zero64 hi th
    then MP_TAC(CONJUNCT2(MATCH_MP READ_MEMORY_BYTES64_ZERO_SPLIT
                     (CONJ th (ARITH_RULE `8 - zt <= 8`))))
    else NO_TAC) THEN
  SUBGOAL_THEN `8 - (8 - zt) = zt` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   (mk_eq(mk_binop `word_add:int64->int64->int64` hi `word(8 - zt):int64`,
          mk_binop `word_add:int64->int64->int64` st
            `word((8 - zk) + 8 * zq):int64`))
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
    DISCH_TAC];;

(*** Step the REP STOSQ, instruction n, keeping the fact for the memory    ***)
(*** that it clears, as MEMSET_STEP_TAC does, with the bound 8 * zq        ***)
(*** <= 2 EXP 64 of its size                                               ***)

let GLUE_STOS_RW_CONV lth =
  let memth = REWRITE_RULE[VALID_COMPONENT_CONV `valid_component memory`]
   (ISPEC `memory:(x86state,int64->byte)component`
     READ_WRITE_VALID_COMPONENT) in
  let bth = REWRITE_RULE[DIMINDEX_64]
   (INST_TYPE [`:64`,`:A`] READ_WRITE_BYTES) in
  REWRITE_CONV[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE; memth] THENC
  (fun tm -> MP (PART_MATCH (lhand o rand) bth tm) lth) THENC
  REWRITE_CONV[VAL_WORD_0; MULT_CLAUSES; NSUM_0; MOD_0];;

let GLUE_PSH_STOS_STEP_TAC prm n =
  let sname = "s" ^ string_of_int n in
  let sv = mk_var(sname,`:x86state`) in
  let bnd = `8 * zq <= 2 EXP 64` in
  let rpat = `read (memory :> bytes(a:int64,k)) (s:x86state)`
  and wpat = `read (memory :> bytes(a:int64,k))
                (write (c:(x86state,num)component) (y:num) (s:x86state))` in
  SUBGOAL_THEN bnd ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  X86_VSTEPS_TAC prm.psh_exec [n] THEN
  FIRST_ASSUM(fun lth ->
    if concl lth = bnd then
      RULE_ASSUM_TAC(fun th ->
        let c = concl th in
        if is_eq c && can (term_match [] rpat) (lhand c) &&
           rand(lhand c) = sv && can (term_match [] wpat) (rand c)
        then CONV_RULE(RAND_CONV(GLUE_STOS_RW_CONV lth)) th else th)
    else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC sname;;

(*** The n zero bytes in state n, from the three parts, the frame and the  ***)
(*** abbreviations expanded                                                ***)

let GLUE_PSH_STOS_DONE_TAC prm n =
  let nb = glue_psh_nb prm and st = glue_psh_st prm in
  let sv = mk_var("s" ^ string_of_int n,`:x86state`) in
  let zvs = [`zk:num`; `zq:num`; `zt:num`; `zc:int64`] in
  let mentions th = exists (fun v -> free_in v (concl th)) zvs in
  let is_abbrev th =
    let c = concl th in
    is_eq c && mem (rhs c) zvs && not(lhs c = `val(zc:int64)`) in
  let removable th =
    let c = concl th in
    mentions th && not(is_abbrev th) &&
    (can (term_match []
           `read (memory :> bytes(a:int64,k)) (s:x86state) = 0`) c ||
     (is_eq c && type_of(lhs c) = `:num`) ||
     is_binary "<" c || is_binary "<=" c) in
  let mz = subst [st,`a:int64`; mk_small_numeral nb,`n:num`]
   `MAYCHANGE [memory :> bytes(a,n)]:x86state->x86state->bool` in
  let is_part t =
    match t with
      Comb(Const("MAYCHANGE",_),l) ->
        (try match dest_list l with
               [c] -> let m,x = dest_binary ":>" c in
                      m = `memory` && free_in `sig:int64` x
             | _ -> false
         with Failure _ -> false)
    | _ -> false in
  let expand v =
    FIRST_X_ASSUM(fun th ->
      if is_abbrev th && rhs(concl th) = v then
        RULE_ASSUM_TAC(REWRITE_RULE[SYM th]) THEN REWRITE_TAC[SYM th]
      else NO_TAC) in
  MP_TAC(SPECL [st; `8 - zk`; `8 * zq`; sv] GLUE_ZERO_COMBINE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [st; `8 - zk + 8 * zq`; `zt:num`; sv] GLUE_ZERO_COMBINE) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   (mk_eq(mk_binop `(+):num->num->num` `8 - zk + 8 * zq` `zt:num`,
          mk_small_numeral nb))
  SUBST1_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if maychange_term c && mentions th then
      let parts = setify(find_terms is_part c) in
      SUBGOAL_THEN (subst (map (fun t -> mz,t) parts) c) ASSUME_TAC THENL
       [ASSUME_TAC th THEN MONOTONE_MAYCHANGE_TAC; ALL_TAC]
    else NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if removable th then ALL_TAC else NO_TAC)) THEN
  MAP_EVERY expand [`zc:int64`; `zt:num`; `zq:num`; `zk:num`];;

(*** The events of the code before the loop, with the bounds of the memory ***)
(*** accesses of the REP STOSQ, and the zero bytes of the hints at its end ***)

let GLUE_STOS_SAFETY_TAC prm =
  let nb = glue_psh_nb prm and st = glue_psh_st prm in
  let kt = mk_binop `MOD` (mk_comb(`val:int64->num`,st)) `8`
  and mt = mk_small_numeral(nb - 8) in
  let kth = REWRITE_RULE[ARITH_EQ]
             (SPECL [mk_comb(`val:int64->num`,st); `8`] MOD_LT_EQ) in
  let mth = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` mt
                                       `2 EXP 32`)) in
  let sth = MP (SPECL [kt; mt] GLUE_STOS_SPLIT) (CONJ kth mth) in
  let kmt = mk_binop `(+):num->num->num` kt mt in
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    (if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
     else ALL_TAC) THEN
    MP_TAC sth THEN MP_TAC kth THEN
    SPEC_TAC(mk_binop `MOD` kmt `8`,`zt:num`) THEN
    SPEC_TAC(mk_binop `DIV` kmt `8`,`zq:num`) THEN
    SPEC_TAC(kt,`zk:num`) THEN
    REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let GLUE_ZERO_FINAL_TAC prm =
  MATCH_MP_TAC GLUE_ZERO_BYTES8_OFFSET THEN
  EXISTS_TAC (mk_small_numeral prm.psh_sigh) THEN
  EXISTS_TAC (mk_small_numeral(glue_psh_nb prm)) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The code before the loop, from step n: the memset of the hints and the    *)
(* call for polynomial 0. For mldsa65, gcc inlines the memset as four        *)
(* (overlapping) 128-bit stores of zeros, whose bytes GLUE_STORE_TAC gives,  *)
(* for mldsa44 and mldsa87 with REP STOSQ at offset psh_stos.                *)
(* ------------------------------------------------------------------------- *)

let GLUE_PSH_PRO_FINAL_TAC prm =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[mld_hint_count; mld_hint_index; WORD_ADD_0; ADD_CLAUSES;
              ETA_AX; CONJUNCT1 LT] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(0 = n)`] THEN
  REPEAT CONJ_TAC THEN
  (if prm.psh_stos > 0 then TRY(GLUE_ZERO_FINAL_TAC prm THEN NO_TAC)
   else TRY(GLUE_BYTES_FINAL_TAC THEN NO_TAC)) THEN
  TRY(FIRST_ASSUM MATCH_ACCEPT_TAC THEN NO_TAC) THEN
  (if prm.psh_stos > 0 then GLUE_STOS_SAFETY_TAC prm
   else DISCHARGE_SAFETY_PROPERTY_TAC);;

let rec GLUE_PSH_PRO_TAC prm n (asl,w) =
  let inst = glue_psh_inst prm in
  let base = layout prm.psh_fn in
  let off = glue_pc_offset base (glue_current_pc (asl,w)) in
  if off = layout(prm.psh_fn ^ "_join4") - base then
    GLUE_PSH_PRO_FINAL_TAC prm (asl,w)
  else if off + base = layout prm.psh_callee then
    (GLUE_PSH_CALL_TAC prm `b:num->byte`
      (inst `!j. j < WB
                 ==> read(memory :> bytes8(word_add w1p (word j))) s =
                     (b:num->byte) j`) n THEN
     GLUE_PSH_PRO_TAC prm (n + 1)) (asl,w)
  else if prm.psh_stos > 0 && off = prm.psh_stos then
    (GLUE_PSH_STOS_PREP_TAC prm THEN GLUE_PSH_STOS_STEP_TAC prm n THEN
     GLUE_PSH_STOS_DONE_TAC prm n THEN GLUE_PSH_PRO_TAC prm (n + 1)) (asl,w)
  else
    (X86_STEPS_TAC prm.psh_exec [n] THEN
     (if prm.psh_stos = 0 then GLUE_STORE_TAC `sig:int64` else ALL_TAC) THEN
     GLUE_PSH_PRO_TAC prm (n + 1)) (asl,w);;

(*** Specialize an assumption !p. P p ==> Q p, matching pat, to tm ***)

let GLUE_ASM_SPEC_TAC pat tm =
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && can (term_match [] pat) (concl th) then
      MP_TAC(SPEC tm th) THEN ANTS_TAC THENL
       [SIMPLE_ARITH_TAC ORELSE (ASM_REWRITE_TAC[] THEN NO_TAC); DISCH_TAC]
    else NO_TAC);;

(*** The facts for the iteration for position i, before the simulation ***)

let GLUE_PSH_PREP_TAC prm =
  let inst = glue_psh_inst prm in
  GLUE_ASM_SPEC_TAC `!p. p < n ==> mld_hint_count h p <= m` `i:num` THEN
  SUBGOAL_THEN `i MOD 256 < 256` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN (inst `i DIV 256 < KK`) ASSUME_TAC THENL
   [SUBGOAL_THEN (inst `i < NN`) MP_TAC THENL
     [SIMPLE_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  GLUE_INDEX_FACTS_TAC `i MOD 256` THEN
  GLUE_INDEX_FACTS_TAC (inst `mld_hint_count H i`) THEN
  SUBGOAL_THEN
   `read(memory :> bytes32(word_add w0
                    (word(1024 * i DIV 256 + 4 * i MOD 256)))) s0 =
    (x:num->int32) i`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `1024 * i DIV 256 + 4 * i MOD 256 = 4 * i` SUBST1_TAC THENL
     [MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `scratch:int64` (concl th) then
      ASSUME_TAC(MP (SPEC `i MOD 256` th) (ASSUME `i MOD 256 < 256`))
    else NO_TAC) THEN
  SUBGOAL_THEN
   (inst `!t. t < OM /\ ~(t = mld_hint_count H i)
              ==> read(memory :> bytes8(word_add sig (word(SH + t)))) s0 =
                  mld_hint_index H i t`)
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (inst `!t. t < KK /\ ~(t = i DIV 256)
              ==> read(memory :> bytes8(word_add sig (word(ST + t)))) s0 =
                  if t < i DIV 256
                  then word(mld_hint_count H (256 * (t + 1)))
                  else word 0`)
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** Equations of words formed from small numbers, as WORD_SMALL_TAC of    ***)
(*** utils/mldsa_native.ml does, also for bytes, removing each MOD that    ***)
(*** the bounds allow                                                      ***)

let GLUE_MOD_LT_TAC =
  W(fun (asl,w) ->
    let tms = find_terms
     (fun t -> is_binary "MOD" t && is_numeral(rand t) &&
               not(is_numeral(lhand t))) w in
    FIRST(map (fun t ->
      MP_TAC(SPECL [lhand t; rand t] MOD_LT) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC])
     (sort free_in (setify tms))));;

let GLUE_WORD_SMALL_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN;
              VAL_WORD; VAL_WORD_SHL; DIMINDEX_8; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(GLUE_MOD_LT_TAC ORELSE
         (COND_CASES_TAC THEN TRY(FIRST_ASSUM(fun th ->
            if is_neg(concl th) then
              (MP_TAC th THEN SIMPLE_ARITH_TAC) else NO_TAC)))) THEN
  SIMPLE_ARITH_TAC;;

(*** Pointer updates by a negative immediate, x - (2^64 - c), as x + c ***)

let GLUE_SUB_NEG_CONV tm =
  match tm with
    Comb(Comb(Const("word_sub",_),x),Comb(Const("word",_),n))
      when type_of tm = `:int64` && is_numeral n &&
           dest_numeral n >=/ num_of_string "9223372036854775808" ->
      let c = mk_numeral(num_of_string "18446744073709551616" -/
                         dest_numeral n) in
      let rhs = list_mk_icomb "word_add" [x; mk_comb(`word:num->int64`,c)] in
      WORD_RULE(mk_eq(tm,rhs))
  | _ -> failwith "GLUE_SUB_NEG_CONV";;

let GLUE_PSH_NORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    if glue_pcev th then
      CONV_RULE(ONCE_DEPTH_CONV GLUE_SUB_NEG_CONV THENC
                ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
       (REWRITE_RULE[WORD_ZX_ZX_32_64_32; WORD_AND_REFL] th)
    else th) THEN
  GLUE_SMALL_REGS_TAC THEN GLUE_FLAGS_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if glue_pcev th then REWRITE_RULE[WORD_ZX_ZX_32_64_32] th else th);;

(*** The range test, as glue_hint_inr: the 32-bit sum a0 + gamma2 that the ***)
(*** code compares with 2 * gamma2, from its form in the simulation        ***)

let GLUE_PSH_RANGE_TAC prm =
  let inst = glue_psh_inst prm in
  let xi = `(x:num->int32) i` in
  let target = inst `word_add ((x:num->int32) i) (word GA)` in
  W(fun (asl,w) ->
    let es = setify(find_terms (fun t ->
      type_of t = `:int32` && free_in xi t && t <> target &&
      can (find_term ((=) xi)) t &&
      (try fst(dest_const(rator t)) = "word_zx" with Failure _ -> false)) w) in
    MAP_EVERY (fun e ->
      let v = genvar `:int32` in
      let th = BITBLAST_RULE(subst [v,xi] (mk_eq(e,target))) in
      TRY(REWRITE_TAC[INST [xi,v] th])) es) THEN
  REWRITE_TAC[GSYM prm.psh_inr_val] THEN ARITH_TAC;;

(*** Decide a branch from the facts, or split on the predicate of the      ***)
(*** events template that it is equivalent to                              ***)

let GLUE_PSH_DECIDE_TAC prm =
  let inst = glue_psh_inst prm in
  let hi = inst `(H:num->bool) i`
  and fl = inst `glue_hint_fail OM H i`
  and cnt = inst `mld_hint_count H i`
  and lastp = inst `i DIV 256 < KM1`
  and inr = inst `(IF:int32->bool) ((x:num->int32) i)`
  and eqg = inst `(x:num->int32) i = word GN`
  and unp = inst `(UNPACK:(num->byte)->num->int32)
                    (\t. (b:num->byte)(WB * i DIV 256 + t)) (i MOD 256)` in
  let canon eq =
    RULE_ASSUM_TAC(fun th ->
      if glue_pcev th then REWRITE_RULE[eq; NOT_CLAUSES] th else th) in
  W(fun (asl,w) ->
    let c0,_ = dest_cond(glue_current_pc (asl,w)) in
    let c = if is_neg c0 then rand c0 else c0 in
    let occurs t = can (find_term ((=) t)) c in
    if occurs `(x:num->int32) i` &&
       can (find_term (fun t -> try fst(dest_const(rator(rator t))) =
                                     "word_add" with Failure _ -> false)) c
    then
      SUBGOAL_THEN (mk_iff(c0,mk_neg inr)) canon THENL
       [GLUE_PSH_RANGE_TAC prm; ALL_TAC] THEN
      GLUE_CASES_TAC inr THENL
       [ALL_TAC;
        SUBGOAL_THEN hi ASSUME_TAC THENL
         [REWRITE_TAC[prm.psh_unfold] THEN MATCH_MP_TAC prm.psh_out THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC]]
    else if occurs `(x:num->int32) i` then
      SUBGOAL_THEN (mk_iff(c0,mk_neg eqg)) canon THENL
       [REWRITE_TAC[GSYM VAL_EQ] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV)
        THEN REWRITE_TAC[];
        ALL_TAC] THEN
      GLUE_CASES_TAC eqg THENL
       [ALL_TAC;
        SUBGOAL_THEN (mk_neg hi) ASSUME_TAC THENL
         [REWRITE_TAC[prm.psh_unfold] THEN
          W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) prm.psh_inr
                                   (rand w))) THEN
          ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN (mk_neg fl) ASSUME_TAC THENL
         [REWRITE_TAC[glue_hint_fail] THEN ASM_REWRITE_TAC[]; ALL_TAC]]
    else if occurs unp then
      SUBGOAL_THEN (mk_iff(c0,mk_neg hi)) canon THENL
       [REWRITE_TAC[prm.psh_unfold] THEN
        W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) prm.psh_inr
                                 (rand(rand w)))) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0];
        ALL_TAC] THEN
      GLUE_CASES_TAC hi THENL
       [ALL_TAC;
        SUBGOAL_THEN (mk_neg fl) ASSUME_TAC THENL
         [REWRITE_TAC[glue_hint_fail] THEN ASM_REWRITE_TAC[]; ALL_TAC]]
    else if occurs cnt then
      SUBGOAL_THEN (mk_iff(c0,mk_neg fl)) canon THENL
       [REWRITE_TAC[glue_hint_fail; ASSUME hi]; ALL_TAC] THEN
      GLUE_CASES_TAC fl THENL
       [ALL_TAC;
        SUBGOAL_THEN (inst `mld_hint_count H i < OM`) ASSUME_TAC THENL
         [UNDISCH_TAC (mk_neg fl) THEN
          REWRITE_TAC[glue_hint_fail; ASSUME hi] THEN SIMPLE_ARITH_TAC;
          ALL_TAC]]
    else if occurs `i MOD 256` then
      SUBGOAL_THEN (mk_iff(c0,`~(i MOD 256 < 255)`)) canon THENL
       [UNDISCH_TAC `i MOD 256 < 256` THEN ARITH_TAC; ALL_TAC] THEN
      GLUE_CASES_TAC `i MOD 256 < 255` THENL
       [MP_TAC(CONJUNCT1(SPEC `i:num` GLUE_MOD_NEXT));
        MP_TAC(CONJUNCT2(SPEC `i:num` GLUE_MOD_NEXT))] THEN
      (ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC])
    else
      SUBGOAL_THEN (mk_iff(c0,lastp)) canon THENL
       [REWRITE_TAC[VAL_EQ] THEN GLUE_WORD_SMALL_TAC; ALL_TAC] THEN
      GLUE_CASES_TAC lastp);;

(*** The registers for the next polynomial, at the head of its code, as    ***)
(*** GLUE_REG_TAC with GLUE_WORD_SMALL_TAC                                 ***)

let GLUE_PSH_REG_TAC (reg:term) (tm:term) =
  let rd = `read:(x86state,int64)component->x86state->int64` in
  FIRST_ASSUM(fun th ->
    try let l,r = dest_eq(concl th) in
        if rator l = mk_comb(rd,reg) then
          SUBGOAL_THEN (mk_eq(r,tm)) SUBST_ALL_TAC THENL
           [GLUE_WORD_SMALL_TAC; ALL_TAC]
        else NO_TAC
    with Failure _ -> NO_TAC);;

let GLUE_PSH_REGS_TAC prm =
  let inst = glue_psh_inst prm in
  GLUE_PSH_REG_TAC `R12`
    (inst `word_add w1p (word(WB * (i DIV 256 + 1))):int64`) THEN
  GLUE_PSH_REG_TAC `R14`
    `word_add w0 (word(1024 * (i DIV 256 + 1))):int64` THEN
  GLUE_PSH_REG_TAC `RBP`
    (inst `word_add sig (word(ST + (i DIV 256 + 1))):int64`);;

(*** The end of an iteration: the next position, and the invariant for it ***)

let GLUE_PSH_NEXT_TAC prm =
  let inst = glue_psh_inst prm in
  let fl = inst `glue_hint_fail OM H i` in
  let th0 = SPECL [glue_psh_hint prm; mk_small_numeral prm.psh_omega;
                   mk_small_numeral(256 * prm.psh_k); `i:num`]
                  GLUE_HINT_NEXT in
  let arith =
    MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    SIMPLE_ARITH_TAC in
  W(fun (asl,w) ->
    let has t = exists (fun (_,th) -> concl th = t) asl in
    MP_TAC(MP th0 (ASSUME(lhand(concl th0)))) THEN
    if has fl then
      DISCH_THEN(MP_TAC o C MP (ASSUME fl) o CONJUNCT1) THEN STRIP_TAC
    else if has (mk_neg `i MOD 256 < 255`) &&
            has (mk_neg(inst `i DIV 256 < KM1`)) then
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; arith];
                      STRIP_TAC]
    else
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; arith];
                      STRIP_TAC]);;

let GLUE_PSH_INDEX_TAC =
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN GLUE_WORD_SMALL_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];;

let GLUE_PSH_TALLY_TAC =
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN ASM_CASES_TAC `t = i DIV 256` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `k < k + 1`; MLD_HINT_COUNT_ADD1] THEN
    GLUE_WORD_SMALL_TAC;
    SUBGOAL_THEN `t < i DIV 256 + 1 <=> t < i DIV 256` SUBST1_TAC THENL
     [SIMPLE_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];;

let GLUE_PSH_RET_TAC =
  REWRITE_TAC[mld_pack_hints_ret] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;;

let GLUE_PSH_FINAL_TAC prm =
  GLUE_PSH_NEXT_TAC prm THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  W(fun (asl,w) ->
    if is_exists w then GLUE_EVENTS_REWRITE_TAC THEN GLUE_PATH_DISCHARGE_TAC
    else
      ASM_REWRITE_TAC[MLD_HINT_COUNT_ADD1; MLD_HINT_INDEX_ADD1; LT_REFL;
                      ADD_CLAUSES] THEN
      REPEAT CONJ_TAC THEN
      TRY(GLUE_WORD_SMALL_TAC THEN NO_TAC) THEN
      TRY(GLUE_PSH_INDEX_TAC THEN NO_TAC) THEN
      TRY(GLUE_PSH_TALLY_TAC THEN NO_TAC) THEN
      GLUE_PSH_RET_TAC);;

(*** The events so far as the variable e2 in the events facts, after a     ***)
(*** call: the inverse of the expansion that GLUE_E2_SHOW_TAC does         ***)

let GLUE_E2_FOLD_TAC =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var(rhs c) && fst(dest_var(rhs c)) = "e2" then
      RULE_ASSUM_TAC(fun th' ->
        let c' = concl th' in
        if is_eq c' && can (term_match [] `read events s`) (lhs c')
        then REWRITE_RULE[th] th' else th')
    else NO_TAC);;

(*** The call for the next polynomial in an iteration, with the events in  ***)
(*** the facts as functions of the variables of the template for the call  ***)

let GLUE_PSH_NEXT_CALL_TAC prm n =
  let inst = glue_psh_inst prm in
  GLUE_E2_SHOW_TAC THEN GLUE_TEMPLATE_SHOW_TAC THEN
  GLUE_PSH_CALL_TAC prm
    (inst `\t. (b:num->byte)(WB * (i DIV 256 + 1) + t)`)
    (inst `!j. j < WB
               ==> read(memory :> bytes8
                     (word_add w1p (word(WB * (i DIV 256 + 1) + j)))) s =
                   (b:num->byte)(WB * (i DIV 256 + 1) + j)`) n THEN
  GLUE_TEMPLATE_HIDE_TAC THEN GLUE_E2_HIDE_TAC THEN GLUE_E2_FOLD_TAC;;

(*** The simulation of an iteration from step n, to the head for the next  ***)
(*** position or to the end, with the call for the next polynomial, and    ***)
(*** with the events template and the events so far hidden, as in          ***)
(*** GLUE_SUH_ITER_TAC                                                     ***)

let rec GLUE_PSH_RUN_TAC prm final n (asl,w) =
  let base = layout prm.psh_fn in
  let lbl l = layout(prm.psh_fn ^ "_" ^ l) - base in
  let off = glue_pc_offset base (glue_current_pc (asl,w)) in
  if n > 1 && (off = lbl "join4" || off = lbl "join6") then final (asl,w)
  else if off + base = layout prm.psh_callee then
    (GLUE_PSH_NEXT_CALL_TAC prm n THEN
     GLUE_PSH_RUN_TAC prm final (n + 1)) (asl,w)
  else
    ((if off = lbl "join1" then GLUE_PSH_REGS_TAC prm else ALL_TAC) THEN
     X86_STEPS_TAC prm.psh_exec [n] THEN GLUE_PSH_NORM_TAC THEN
     (fun g -> if is_cond(glue_current_pc g) then GLUE_PSH_DECIDE_TAC prm g
               else ALL_TAC g) THEN
     GLUE_PSH_RUN_TAC prm final (n + 1)) (asl,w);;

let GLUE_PSH_BODY_TAC prm =
  let inst = glue_psh_inst prm in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ASSUME(inst `i < glue_hint_steps OM NN H`)] THEN
  FULL_INIT_TAC THEN GLUE_PSH_PREP_TAC prm THEN
  GLUE_TEMPLATE_HIDE_TAC THEN GLUE_E2_HIDE_TAC THEN
  GLUE_PSH_RUN_TAC prm
   (GLUE_E2_SHOW_TAC THEN GLUE_TEMPLATE_SHOW_TAC THEN GLUE_PSH_FINAL_TAC prm)
   1;;

(*** The return: the hints from the facts for all positions when the count ***)
(*** is at most omega                                                      ***)

let GLUE_PSH_BYTES_TAC prm =
  let inst = glue_psh_inst prm in
  let cnt_ok = inst `mld_hint_count H NN <= OM` in
  REWRITE_TAC[mld_pack_hints_ret] THEN CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THENL [ALL_TAC; CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[]]
  THEN DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && lhand(concl th) = cnt_ok && is_conj(rand(concl th))))
  THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && lhand(concl th) = cnt_ok && is_eq(rand(concl th))))
  THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST_ALL_TAC] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[mld_pack_hints] THEN
  COND_CASES_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN (inst `SH + t = ST + (t - OM)`) SUBST1_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (inst `t - OM < KK`) ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC (inst `t - OM`) o check (fun th ->
      is_forall(concl th) && free_in (inst `ST:num`) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]];;

(*** The return from the checkpoint at the end ***)

let GLUE_PSH_EXIT_TAC prm =
  REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC prm.psh_exec (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [GLUE_PSH_BYTES_TAC prm; DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** The whole proof, given the FULL theorem for unpacking w1, with the    ***)
(*** initial YMM0 as a ghost for mldsa65, whose legacy SSE instructions    ***)
(*** keep its upper part                                                   ***)

let GLUE_PSH_FULL_TAC prm calleeth =
  GLUE_PSH_SETUP_TAC prm calleeth THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC;
    (if prm.psh_stos > 0 then ALL_TAC
     else GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0`) THEN
    FULL_INIT_TAC THEN GLUE_PSH_PRO_TAC prm 1;
    GLUE_PSH_BODY_TAC prm;
    GLUE_PSH_EXIT_TAC prm];;
