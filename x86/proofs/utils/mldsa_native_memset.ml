(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the memsets that gcc inlines with REP STOSQ in mldsa-native's   *)
(* x86-64 code, as in the x86 proofs of mlkem-native. When st is not known   *)
(* to be aligned, gcc inlines a memset of n bytes at st, for n a multiple of *)
(* 8, as zero quadword stores at st and st + n - 8 and a REP STOSQ of n DIV  *)
(* 8 - 1 quadwords from the first multiple of 8 above st, which is st + (8 - *)
(* val st MOD 8) by MEMSET_ALIGN_ADDR. Before the REP STOSQ, MEMSET_PREP_TAC *)
(* evaluates the count, which is the same for any st, puts the address in    *)
(* that form, and splits the two quadwords into their parts outside the      *)
(* memory that it clears, so that the simulation keeps them. MEMSET_STEP_TAC *)
(* then steps the REP STOSQ, keeping the fact for the memory that it clears, *)
(* which the simulation does not simplify, and MEMSET_DONE_TAC puts the      *)
(* three parts together. As the ABI requires on entry, the direction flag DF *)
(* must be clear. The tools use READ_MEMORY_BYTES_SUB, the bytes of a part   *)
(* of a byte array, which other proofs use too.                              *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native.ml";;

let MEMSET_ALIGN_ADDR = prove
 (`!st:int64.
        word_and (word_add st (word 8)) (word 18446744073709551608) =
        word_add st (word (8 - val st MOD 8))`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(st:int64) MOD 8 = val(word_and st (word 7):int64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `7 = 2 EXP 3 - 1`] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 3 = 8`];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_and st (word 7):int64) <= 8` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`st:int64`; `word 7:int64`]
      (CONJUNCT2 VAL_WORD_AND_LE)) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (INST_TYPE [`:64`,`:N`] WORD_SUB2) o
    INST [`8`,`x:num`] o
    check (fun th -> concl th = `val(word_and st (word 7):int64) <= 8`)) THEN
  REWRITE_TAC[WORD_VAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

(*** Parts of bytes in memory, and of a quadword that is zero ***)

let READ_MEMORY_BYTES_SUB = prove
 (`!a:int64 n x k l s:x86state.
        read (memory :> bytes(a,n)) s = x /\ k + l <= n
        ==> read (memory :> bytes(word_add a (word k),l)) s =
            (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES64_ZERO_SPLIT = prove
 (`!a:int64 k s:x86state.
        read (memory :> bytes64 a) s = word 0 /\ k <= 8
        ==> read (memory :> bytes(a,k)) s = 0 /\
            read (memory :> bytes(word_add a (word k),8 - k)) s = 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; BYTES64_WBYTES] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`a:int64`; `8`; `0`; `0`; `k:num`; `s:x86state`]
      READ_MEMORY_BYTES_SUB);
    MP_TAC(SPECL [`a:int64`; `8`; `0`; `k:num`; `8 - k`; `s:x86state`]
      READ_MEMORY_BYTES_SUB)] THEN
  ASM_REWRITE_TAC[WORD_ADD_0; DIV_0; MOD_0] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;
(*** The three parts of the n bytes, and the address of the last ***)

let MEMSET_COMBINE = prove
 (`!st:int64 n k s:x86state.
        k < 8 /\ 8 <= n /\
        read (memory :> bytes(st,8 - k)) s = 0 /\
        read (memory :> bytes(word_add st (word(8 - k)),n - 8)) s = 0 /\
        read (memory :> bytes(word_add st (word(n - k)),k)) s = 0
        ==> read (memory :> bytes(st,n)) s = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n = (8 - k) + (n - 8) + k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; GSYM WORD_ADD_ASSOC;
              GSYM WORD_ADD] THEN
  SUBGOAL_THEN `(8 - k) + (n - 8) = n - k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let MEMSET_HIGH_ADDR = prove
 (`!st:int64 n k.
        k < 8 /\ 8 <= n
        ==> word_add (word_add st (word(n - 8))) (word(8 - k)) =
            word_add st (word(n - k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(*** The count of quadwords, the same for any st, by bit-blasting ***)

let MEMSET_COUNT_RULE th =
  let e = rand(concl th) in
  let st = lhand(lhand(find_term (can (term_match []
             `word_and (word_add x (word 8))
                       (word 18446744073709551608):int64`))
             e)) in
  let c = rhs(concl(WORD_REDUCE_CONV(subst [`word 0:int64`,st] e))) in
  TRANS th (BITBLAST_RULE(mk_eq(e,c)));;
(*** The preparation for the REP STOSQ, in the state before it ***)

let MEMSET_PREP_TAC (asl,w) =
  let mask = `word 18446744073709551608:int64` in
  let is_rcx th = can (term_match [] `read RCX s = x`) (concl th) &&
                  free_in mask (concl th)
  and is_rdi th = can (term_match []
    `read RDI s = word_and (word_add x (word 8)) (word 18446744073709551608)`)
    (concl th) in
  let rdi = snd(find (is_rdi o snd) asl) in
  let st = lhand(lhand(rand(concl rdi))) in
  let kt = mk_binop `MOD` (mk_comb(`val:int64->num`,st)) `8` in
  let dt = mk_binop `(-):num->num->num` `8` kt in
  let ltth = SPECL [mk_comb(`val:int64->num`,st); `8`] MOD_LT_EQ in
  let kth = REWRITE_RULE[ARITH_EQ] ltth in
  let dleth = ARITH_RULE(mk_binop `(<=):num->num->bool` dt `8`) in
  let split th =
    if can (term_match [] `read (memory :> bytes64 a) s = word 0`) (concl th)
    then
      let a = rand(rand(lhand(lhand(concl th)))) in
      let spl = MATCH_MP READ_MEMORY_BYTES64_ZERO_SPLIT (CONJ th dleth) in
      if a = st then [CONJUNCT1 spl]
      else if is_comb a && is_comb(rator a) && lhand a = st then
        let m = dest_small_numeral(rand(rand a)) in
        let hth = MP (SPECL [st; mk_small_numeral(m + 8); kt] MEMSET_HIGH_ADDR)
                     (CONJ kth (ARITH_RULE(mk_binop `(<=):num->num->bool`
                                  `8` (mk_small_numeral(m + 8))))) in
        let hth' = CONV_RULE(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
                     NUM_REDUCE_CONV)))) hth in
        let lth = ARITH_RULE(mk_eq(mk_binop `(-):num->num->num` `8` dt,kt)) in
        [REWRITE_RULE[hth'; lth] (CONJUNCT2 spl)]
      else []
    else [] in
  let news = itlist (fun (_,th) l -> split th @ l) asl [] in
  (RULE_ASSUM_TAC
    (fun th -> if is_rcx th then MEMSET_COUNT_RULE th else th) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[MEMSET_ALIGN_ADDR]) THEN
   ASSUME_TAC kth THEN MAP_EVERY ASSUME_TAC news) (asl,w);;

(*** The memory cleared, from the fact that the simulation leaves ***)

let MEMSET_RW_CONV =
  let memth = REWRITE_RULE[VALID_COMPONENT_CONV `valid_component memory`]
   (ISPEC `memory:(x86state,int64->byte)component`
     READ_WRITE_VALID_COMPONENT) in
  let bth = REWRITE_RULE[DIMINDEX_64]
   (INST_TYPE [`:64`,`:A`] READ_WRITE_BYTES) in
  REWRITE_CONV[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE; memth] THENC
  (fun tm -> let th = PART_MATCH (lhand o rand) bth tm in
             MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) THENC
  REWRITE_CONV[MULT_CLAUSES; NSUM_0; MOD_0];;

(*** Step the REP STOSQ instruction n, keeping the fact for the memory it
 *** clears, which the simulation does not simplify
 ***)

let MEMSET_STEP_TAC execth n =
  let sname = "s" ^ string_of_int n in
  let sv = mk_var(sname,`:x86state`) in
  X86_VSTEPS_TAC execth [n] THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read (memory :> bytes(a,k)) s`) (lhand c)
       && rand(lhand c) = sv &&
       can (term_match [] `read (memory :> bytes(a,k)) (write c y s)`) (rand c)
    then CONV_RULE(RAND_CONV MEMSET_RW_CONV) th else th) THEN
  DISCARD_OLDSTATE_TAC sname;;

(*** The n bytes at st cleared in state sname, from the three parts ***)

let MEMSET_DONE_TAC st n sname =
  let sv = mk_var(sname,`:x86state`) in
  let kt = mk_binop `MOD` (mk_comb(`val:int64->num`,st)) `8` in
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
    (SPECL [st; mk_small_numeral n; kt; sv] MEMSET_COMBINE)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;
