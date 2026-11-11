(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the FULL proofs of the samplers of mldsa-native for x86-64 (the *)
(* rejection sampling loops mld_rej_uniform_c and mld_rej_eta_c, and their   *)
(* callers), as for AArch64 (see arm/proofs/utils/mldsa_native_sampling.ml,  *)
(* whose tools these are, for the x86 model).                                *)
(*                                                                           *)
(* The loops keep small counters and positions in 32-bit registers and test  *)
(* them with CMP, SETcc and TEST, so that a step leaves flags and registers  *)
(* that are conditionals on comparisons of numbers. The tactics here decide  *)
(* those conditionals from arithmetic facts where possible                   *)
(* (SAMPLING_STEP_TAC simulates one step and does so), and put the test of   *)
(* the loop in the form i + 1 < k that ENSURES_EVENTS_WHILE_UP2_TAC expects. *)
(* The events of an iteration depend on which candidates are accepted; each  *)
(* path of the iteration gets its own meta-variable in the template, as in   *)
(* mldsa_native_full.ml, and SAMPLING_PATH_DISCHARGE_TAC also handles a path *)
(* that the simulation reaches in several ways.                              *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "common/mldsa_native_sampling.ml";;

(* ------------------------------------------------------------------------- *)
(* The list of the values that mld_rej_eta_c declassifies: its length, its   *)
(* elements, and the number of T among its first n.                          *)
(* ------------------------------------------------------------------------- *)

let MLD_REJ_ETA_DECLASS = prove
 (`!eta target offset (b:num->byte) buflen.
     LENGTH(mld_rej_eta_declass eta target offset b buflen) =
     2 * mld_rej_eta_bytes eta target offset b buflen /\
     (!k. k < 2 * mld_rej_eta_bytes eta target offset b buflen
          ==> (EL k (mld_rej_eta_declass eta target offset b buflen) <=>
               mld_rej_eta_valid eta (mld_rej_eta_nibble b k))) /\
     (!n. n <= 2 * mld_rej_eta_bytes eta target offset b buflen
          ==> LENGTH(FILTER (\x. x)
                (SUB_LIST(0,n)
                  (mld_rej_eta_declass eta target offset b buflen))) =
              LENGTH(mld_rej_eta_list eta b n))`,
  REWRITE_TAC[mld_rej_eta_declass; LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; MLD_SUB_LIST_LIST_OF_SEQ;
           LENGTH_MLD_REJ_ETA_LIST]);;

(* ------------------------------------------------------------------------- *)
(* The values that the code computes in 32-bit and 8-bit registers: the      *)
(* nibbles of a byte loaded with MOVZX, the position in the buffer from its  *)
(* distance to the base (LEA eax, [r+rdx*1] with the 32-bit r = c - buf),    *)
(* small counters after an ADD or a 32-bit LEA (whose result the model gives *)
(* as the sign extension word_sx of the 64-bit address, i.e. its low 32      *)
(* bits), the low byte of a register after a SETcc (a word_join of the old   *)
(* high bits and the byte), the results of a TEST of two SETcc results, and  *)
(* lengths of conditional lists.                                             *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_WORD_MOD_256 = prove
 (`!n. word(n MOD 256):byte = word n`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

let MLD_BYTE_NIBBLES = prove
 (`!y:byte. word_zx(word_and y (word 15)):int64 = word(val y MOD 16) /\
            word_zx(word_ushr y 4):int64 = word(val y DIV 16)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_USHR;
              ARITH_RULE `15 = 2 EXP 4 - 1`; VAL_WORD_AND_MASK_WORD;
              DIMINDEX_8; DIMINDEX_64] THEN
  MP_TAC(ISPEC `y:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  SPEC_TAC(`val(y:byte)`,`n:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `n MOD 16 MOD 256 = n MOD 16 /\
                n MOD 16 MOD 18446744073709551616 = n MOD 16 /\
                (n DIV 16) MOD 256 = n DIV 16 /\
                (n DIV 16) MOD 18446744073709551616 = n DIV 16`
   (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`n:num`; `16`] MOD_LT_EQ) THEN
  MP_TAC(SPECL [`n:num`; `16`] DIV_LE) THEN ASM_ARITH_TAC);;

let MLD_REJ_POS = prove
 (`!(buf:int64) k c.
        k + c < 2 EXP 32
        ==> word_zx(word_sx(word_add
              (word_zx(word_sub (word c) (word_zx buf:int32)):int64)
              (word(1 * val(word_add buf (word k):int64)))):int32):int64 =
            word(k + c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MULT_CLAUSES; WORD_VAL] THEN
  REWRITE_TAC[BITBLAST_RULE
   `!buf w c:int32.
      word_sx(word_add (word_zx(word_sub c (word_zx buf:int32)):int64)
                       (word_add buf w)):int32 =
      word_add c (word_zx w)`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `k < 4294967296 /\ c < 4294967296 /\ c + k < 4294967296 /\
                k < 18446744073709551616 /\ k + c < 18446744073709551616 /\
                c + k < 18446744073709551616`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `k + c < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
    ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT; ADD_SYM]]);;

let SAMPLING_WORD_SX_64_32 = prove
 (`!x:int64. word_sx x:int32 = word_zx x`,
  BITBLAST_TAC);;

let SAMPLING_WORD_ZX_SMALL = prove
 (`(!m k. m + k < 2 EXP 32
          ==> word_zx(word_add (word_zx(word m:int64):int32) (word k)):int64 =
              word(m + k)) /\
   (!m k. m + k < 2 EXP 32
          ==> word_zx(word_add (word m:int32) (word k)):int64 = word(m + k)) /\
   (!m k. m + k < 2 EXP 32
          ==> word_zx(word_sx(word_add (word m:int64) (word k)):int32):int64 =
              word(m + k)) /\
   (!m. m < 2 EXP 32 ==> word_zx(word m:int32):int64 = word m) /\
   (!m. m < 2 EXP 8 ==> word_zx(word m:byte):int32 = word m)`,
  REWRITE_TAC[SAMPLING_WORD_SX_64_32] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  TRY(SUBGOAL_THEN `m < 4294967296 /\ k < 4294967296 /\
                    m < 18446744073709551616 /\
                    k < 18446744073709551616 /\
                    m + k < 18446744073709551616` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC]) THEN
  TRY(SUBGOAL_THEN `m < 4294967296 /\ m < 18446744073709551616`
       STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_SIMP_TAC[MOD_LT]);;

let SAMPLING_VAL_WORD_64 = prove
 (`!n. n < 2 EXP 64 ==> val(word n:int64) = n`,
  REWRITE_TAC[GSYM DIMINDEX_64; VAL_WORD_EQ]);;

let SAMPLING_MOD_256_SMALL = prove
 (`!x. x < 256 ==> x MOD 256 = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

let SAMPLING_WORD_ZX_BYTE = prove
 (`(!n. word_zx(word n:int64):byte = word n) /\
   (!n. word_zx(word n:int32):byte = word n)`,
  CONJ_TAC THEN GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SAMPLING_JOIN_BYTE = prove
 (`(!(h:(56)word) (l:byte). word(val(word_join h l:int64) MOD 256):byte = l) /\
   (!(h:(56)word) (l:byte). word_zx(word_join h l:int64):byte = l)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[SAMPLING_WORD_MOD_256; GSYM word_zx] THEN BITBLAST_TAC);;

let SAMPLING_TEST_CONDS = prove
 (`(!p. val(if p then word 1 else word 0:byte) = 0 <=> ~p) /\
   (!p q. val(word_and (if p then word 1 else word 0)
                       (if q then word 1 else word 0):byte) = 0 <=>
          ~p \/ ~q) /\
   (!q. val(word_and (word 1) (if q then word 1 else word 0):byte) = 0 <=>
        ~q) /\
   (!p. val(word_and (if p then word 1 else word 0) (word 1):byte) = 0 <=>
        ~p) /\
   (!x. val(word_and (word 0) x:byte) = 0) /\
   (!x. val(word_and x (word 0):byte) = 0) /\
   (val(word_and (word 1) (word 1):byte) = 0 <=> F) /\
   (val(word 1:byte) = 0 <=> F) /\ (val(word 0:byte) = 0 <=> T)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_AND_0; VAL_WORD_0] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let SAMPLING_LENGTH_COND = prove
 (`!p (x:A). LENGTH(if p then [x] else []) = if p then 1 else 0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH; ONE]);;

(*** The flags of an 8-bit compare of small numbers, as WORD_CMP_32_FLAGS ***)

let WORD_CMP_8_FLAGS = prove
 (`!x y. x < 256 /\ y < 256
         ==> ((&(val(word x:byte)) - &(val(word y:byte)):int =
               &(val(word_sub (word x) (word y):byte)) <=> y <= x) /\
              (&(val(word x:byte)) - &y:int =
               &(val(word_sub (word x) (word y):byte)) <=> y <= x) /\
              (val(word_sub (word x) (word y):byte) = 0 <=> x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word x:byte) = x /\ val(word y:byte) = y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_8] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[INT_ARITH `x - y:int = z <=> x = y + z`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The coefficient for eta = 2 as the code computes it, (t * 205) >> 10      *)
(* being t DIV 5 and multiplying by 5 being an LEA, for a nibble in CL (the  *)
(* first, zero-extended to 32 bits) or in EAX (the second).                  *)
(* ------------------------------------------------------------------------- *)

let MLD_REJ_ETA2_COEFF = prove
 (`(!t. t < 16
        ==> word_sub (word 2)
             (word_sub (word_zx (word t:byte))
               (word_sx
                 (word_add
                   (word_zx (word_ushr (word_mul (word_zx (word t:byte):int32)
                                                 (word 205)) 10):int64)
                   (word (4 * val (word_zx (word_ushr
                      (word_mul (word_zx (word t:byte):int32) (word 205)) 10)
                      :int64)))))):int32 =
            word_sub (word 2)
             (word_sub (word t)
               (word_mul (word_ushr (word_mul (word 205) (word t)) 10)
                         (word 5)))) /\
   (!t. t < 16
        ==> word_sub (word 2)
             (word_sub (word t)
               (word_sx
                 (word_add
                   (word_zx (word_ushr (word_mul (word t:int32)
                                                 (word 205)) 10):int64)
                   (word (4 * val (word_zx (word_ushr
                      (word_mul (word t:int32) (word 205)) 10)
                      :int64)))))):int32 =
            word_sub (word 2)
             (word_sub (word t)
               (word_mul (word_ushr (word_mul (word 205) (word t)) 10)
                         (word 5))))`,
  CONJ_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(REPEATC(CHANGED_CONV(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV))));;

(* ------------------------------------------------------------------------- *)
(* Deciding conditions: a proposition by arithmetic, keeping it as an        *)
(* assumption (and discarding the assumptions that it reduces to T, which    *)
(* make the x86 simulation overflow the stack); the condition of a           *)
(* conditional jump; the carry and zero flags of a 32-bit or 8-bit compare;  *)
(* the conditions of the conditionals in the facts about the state (the      *)
(* results of SETcc); and the conditionals of the goal, from assumptions     *)
(* that are exactly their conditions or the negations. SAMPLING_CASES_TAC    *)
(* splits on a proposition about the declassified values and adds the        *)
(* instances of the assumptions EL k D <=> p that it implies.                *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_DISCARD_TRUTHS_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `T`)));;

let SAMPLING_DECIDE_PROP_TAC c =
  (SUBGOAL_THEN c
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO th]) THEN
               SAMPLING_DISCARD_TRUTHS_TAC THEN ASSUME_TAC th) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg c)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO th]) THEN
               SAMPLING_DISCARD_TRUTHS_TAC THEN ASSUME_TAC th) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]);;

let SAMPLING_DECIDE_BRANCH_TAC =
  FIRST_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if not (is_cond r) || not(can (term_match [] `read RIP s`) l)
    then failwith "SAMPLING_DECIDE_BRANCH_TAC" else
    SAMPLING_DECIDE_PROP_TAC (lhand(rator r)));;

let SAMPLING_DECIDE_FLAGS_TAC =
  let pat32 = `word_sub (word x) (word y):int32`
  and pat8 = `word_sub (word x) (word y):byte` in
  W32_SMALL_TAC THEN
  W(fun (asl,w) ->
    let tml = list_mk_conj(map (concl o snd) asl) in
    let jobs = map (fun t -> t,WORD_CMP_32_FLAGS)
                   (setify (find_terms (can (term_match [] pat32)) tml)) @
               map (fun t -> t,WORD_CMP_8_FLAGS)
                   (setify (find_terms (can (term_match [] pat8)) tml)) in
    MAP_EVERY (fun (t,cth) ->
      let x = rand(lhand t) and y = rand(rand t) in
      TRY(MP_TAC(SPECL [x;y] cth) THEN
          ANTS_TAC THENL
           [CONJ_TAC THEN SIMPLE_ARITH_TAC;
            DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))])) jobs) THEN
  W(fun (asl,w) ->
     let ps = mapfilter (fun (_,th) ->
       let l,r = dest_eq(concl th) in
       let f = rand(rator l) in
       if mem f [`CF`;`ZF`] && not(r = `T` || r = `F`) then r
       else failwith "") asl in
     MAP_EVERY (fun p -> TRY(SAMPLING_DECIDE_PROP_TAC p)) ps);;

let SAMPLING_DECIDE_CONDS_TAC =
  let has_read tm =
    can (find_term (fun t -> is_const t && fst(dest_const t) = "read")) tm in
  W(fun (asl,w) ->
    let rec conds bound tm acc =
      match tm with
        Comb(Comb(Comb(Const("COND",_),p),a),b) ->
          let acc' = if intersect (frees p) bound = [] && not (mem p acc)
                     then p::acc else acc in
          conds bound p (conds bound a (conds bound b acc'))
      | Comb(l,r) -> conds bound l (conds bound r acc)
      | Abs(v,bd) -> conds (v::bound) bd acc
      | _ -> acc in
    let ps = itlist (fun (_,th) acc ->
                if has_read (concl th) then conds [] (concl th) acc
                else acc) asl [] in
    MAP_EVERY (fun p -> TRY(SAMPLING_DECIDE_PROP_TAC p)) ps);;

let SAMPLING_SELECT_TAC =
  W(fun (asl,w) ->
    let conds = map (fun t -> rand(rator(rator t))) (find_terms is_cond w) in
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if mem c conds then EQT_INTRO th
      else if is_neg c && mem (rand c) conds then EQF_INTRO th
      else failwith "") asl in
    REWRITE_TAC ths);;

let SAMPLING_CASES_TAC tm =
  let tac b =
    W(fun (asl,w) ->
      let iffs = filter (fun th -> is_iff(concl th) &&
                   can (term_match [] `EL k (l:bool list)`) (lhs(concl th)))
                 (map snd asl) in
      let c = if b then tm else mk_neg tm in
      let th = REWRITE_RULE iffs (ASSUME c) in
      if concl th = c then ALL_TAC else STRIP_ASSUME_TAC th) in
  ASM_CASES_TAC tm THENL [tac true; tac false];;

(* ------------------------------------------------------------------------- *)
(* Simulation. SAMPLING_COND_REWRITE_TAC ths rewrites with the instances of  *)
(* the conditional equations ths whose conditions SIMPLE_ARITH_TAC proves;   *)
(* SAMPLING_W64_TAC so replaces the 64-bit zero extensions of small 32-bit   *)
(* sums and numbers, the positions and the bytes of small numbers by the     *)
(* numbers. SAMPLING_STEP_TAC execth n simulates step n with the facts       *)
(* val(word e) = e about the registers that hold small numbers word e, which *)
(* the address of a store with an index register needs, for that step only   *)
(* (SAMPLING_INDEX_THMS), and then the normalizations and decisions above,   *)
(* the registers holding sums of a base and small numbers being normalized   *)
(* to word_add base (word n) (SAMPLING_NORM_REGS_TAC); SAMPLING_RUN_TAC      *)
(* execth n stop simulates from step n until the RIP is in the list stop or  *)
(* is undecided.                                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The decisions leave facts whose hypotheses are the case assumptions, and  *)
(* X86_THM, which the simulation uses for each step, cannot instantiate its  *)
(* own variables n, instr and s' if they occur in those hypotheses: the      *)
(* proofs must not use those names for their variables (cf. the value n of   *)
(* the byte in the AArch64 proofs of mld_rej_eta_c, which is nb here).       *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_COND_REWRITE_TAC ths =
  let pats = map (fun th -> lhs(snd(dest_imp(snd(strip_forall(concl th))))),th)
                 (flat(map CONJUNCTS ths)) in
  W(fun (asl,w) ->
    let tml = list_mk_conj(w::map (concl o snd) asl) in
    let jobs = itlist (fun (pat,th) acc ->
       map (fun t -> t,th)
           (setify (find_terms (can (term_match [] pat)) tml)) @ acc)
       pats [] in
    MAP_EVERY (fun (t,th) ->
      let lth = PART_MATCH (lhs o rand) th t in
      TRY(MP_TAC lth THEN
          ANTS_TAC THENL
           [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
            DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                                 REWRITE_TAC[th])])) jobs);;

let SAMPLING_W64_TAC =
  SAMPLING_COND_REWRITE_TAC
   [SAMPLING_WORD_ZX_SMALL; MLD_REJ_POS; SAMPLING_MOD_256_SMALL];;

let SAMPLING_REGVAL r (asl,w) =
  rhs(concl(snd(find (fun (_,th) ->
    try rand(rator(lhs(concl th))) = r with Failure _ -> false) asl)));;

(*** Replacing the value of register reg by tm, proving them equal by      ***)
(*** rewriting with ths and bit-blasting                                    ***)

let SAMPLING_REG_TAC reg tm ths =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && (try rand(rator(lhs c)) = reg with Failure _ -> false)
    then ASSUME_TAC(TRANS th (prove(mk_eq(rhs c,tm),
                                    REWRITE_TAC ths THEN BITBLAST_TAC)))
    else failwith "SAMPLING_REG_TAC");;

let SAMPLING_GPRS =
  [`RAX`; `RCX`; `RDX`; `RBX`; `RSI`; `RDI`; `R8`; `R9`; `R10`; `R11`];;

let SAMPLING_ADD_ADD_CONV =
  let pth = prove
   (`word_add (word_add (x:int64) (word m)) (word n) =
     word_add x (word(m + n))`,
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_add",_),
                Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),_))),
           Comb(Const("word",_),_)) when type_of tm = `:int64` ->
        (REWR_CONV pth THENC TRY_CONV(RAND_CONV(RAND_CONV NUM_ADD_CONV))) tm
    | _ -> failwith "SAMPLING_ADD_ADD_CONV";;

let SAMPLING_NORM_REGS_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && (try mem (rand(rator(lhs c))) SAMPLING_GPRS
                   with Failure _ -> false)
    then CONV_RULE(RAND_CONV(TOP_DEPTH_CONV SAMPLING_ADD_ADD_CONV)) th
    else th);;

let SAMPLING_INDEX_THMS (asl,w) =
  mapfilter (fun r ->
    let t = SAMPLING_REGVAL r (asl,w) in
    match t with
      Comb(Const("word",_),e) when not(is_numeral e) &&
                                   type_of t = `:int64` ->
        SPEC e SAMPLING_VAL_WORD_64
    | _ -> failwith "") SAMPLING_GPRS;;

let SAMPLING_STEP_TAC execth n (asl,w) =
  let ths = SAMPLING_INDEX_THMS (asl,w) in
  let ts = map (fun th -> rand(concl th)) ths in
  (MAP_EVERY (fun th ->
     TRY(MP_TAC th THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC])) ths THEN
   X86_STEPS_TAC execth [n] THEN
   REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> mem (concl th) ts))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; SAMPLING_WORD_ZX_BYTE;
                               SAMPLING_JOIN_BYTE; SAMPLING_TEST_CONDS]) THEN
   SAMPLING_NORM_REGS_TAC THEN
   TRY SAMPLING_W64_TAC THEN TRY SAMPLING_DECIDE_FLAGS_TAC THEN
   TRY SAMPLING_DECIDE_CONDS_TAC THEN TRY SAMPLING_DECIDE_BRANCH_TAC THEN
   SAMPLING_DISCARD_TRUTHS_TAC) (asl,w);;

let rec SAMPLING_RUN_TAC execth n stop (asl,w) =
  (SAMPLING_STEP_TAC execth n THEN
   (fun g -> let pcv = SAMPLING_REGVAL `RIP` g in
             if is_cond pcv || mem pcv stop then ALL_TAC g
             else SAMPLING_RUN_TAC execth (n + 1) stop g)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The test of the loop at the end of iteration i: SAMPLING_LOOP_PC_TAC k    *)
(* ths proves the condition of the jump equivalent to i + 1 < k, by          *)
(* rewriting i + 1 < k with ths and the assumptions i + 1 < m <=> .., and    *)
(* replaces it. When the simulation has decided that the loop exits,         *)
(* SAMPLING_LOOP_EXIT_TAC k ths pc1 shows ~(i + 1 < k) and puts the RIP and  *)
(* the target of the last jump back as the conditional of the other paths.   *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_LOOP_EQ_TAC ths =
  REWRITE_TAC ths THEN
  W(fun (asl,w) ->
     let fs = mapfilter (fun (_,th) ->
       let c = concl th in
       if is_iff c && is_var(rand(lhand c)) &&
          lhand(lhand c) = mk_binop `(+):num->num->num` `i:num` `1`
       then th else failwith "") asl in
     REWRITE_TAC fs) THEN
  SAMPLING_SELECT_TAC THEN REPEAT COND_CASES_TAC THEN SIMPLE_ARITH_TAC;;

let SAMPLING_LOOP_PC_TAC k ths =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; SAMPLING_TEST_CONDS]) THEN
  let q = mk_binop `(<):num->num->bool`
              (mk_binop `(+):num->num->num` `i:num` `1`) k in
  W(fun g ->
    let pcv = SAMPLING_REGVAL `RIP` g in
    if is_cond pcv then
      let p = lhand(rator pcv) in
      SUBGOAL_THEN (mk_eq(p,q)) (fun eth ->
         RULE_ASSUM_TAC(REWRITE_RULE[eth]) THEN REWRITE_TAC[eth]) THENL
       [SAMPLING_LOOP_EQ_TAC ths; ALL_TAC]
    else failwith "SAMPLING_LOOP_PC_TAC: decided");;

let SAMPLING_LOOP_EXIT_TAC k ths pc1 =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; SAMPLING_TEST_CONDS]) THEN
  let q = mk_binop `(<):num->num->bool`
              (mk_binop `(+):num->num->num` `i:num` `1`) k in
  W(fun g ->
    let pcv = SAMPLING_REGVAL `RIP` g in
    if is_cond pcv then failwith "SAMPLING_LOOP_EXIT_TAC: not decided" else
    let ct = mk_cond(q,pc1,pcv) in
    SUBGOAL_THEN (mk_eq(pcv,ct)) (fun eth ->
       let headconv = RAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
                       (GEN_REWRITE_CONV I [eth])))) in
       RULE_ASSUM_TAC(fun th ->
         let c = concl th in
         if is_eq c && can (term_match [] `read RIP s`) (lhs c)
         then CONV_RULE(RAND_CONV(GEN_REWRITE_CONV I [eth])) th
         else if is_eq c && can (term_match [] `read events s`) (lhs c)
         then CONV_RULE headconv th
         else th)) THENL
     [SUBGOAL_THEN (mk_neg q) (fun nth -> REWRITE_TAC[nth]) THEN
      SAMPLING_LOOP_EQ_TAC ths;
      ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The events of an iteration that takes one of several paths, as            *)
(* PATH_DISCHARGE_TAC of mldsa_native_full.ml, except that a path whose      *)
(* meta-variable another case has already instantiated (the same events,     *)
(* reached with other facts) is checked by beta-reduction instead.           *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_PATH_DISCHARGE_TAC =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN SAMPLING_SELECT_TAC THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then
      CONJ_TAC THENL
       [FULL_UNIFY_F_EVENTS_TAC ORELSE
        (CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
         REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC);
        ALL_TAC]
    else ALL_TAC) THEN
  beta_all THEN
  REWRITE_TAC[NOT_LT] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(*** Elements of explicit lists ***)

let SAMPLING_EL_LIST_CONV =
  REWRITE_CONV[APPEND; EL; HD; TL; ONE; ADD_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* The incremental SHAKE functions of fips202.c on a short message (one      *)
(* partial block, as for the seeds of the samplers): absorbing it into the   *)
(* zero state and finalizing give the absorbed state of the 4-way functions, *)
(* so that the output of mld_shake256 is mld_shake256_stream; squeezing a    *)
(* whole number of blocks from position r, and the bytes of an output. The   *)
(* two facts about num_of_bytelist are NUM_OF_BYTELIST_APPEND and            *)
(* NUM_OF_BYTELIST_REPLICATE_0 of utils/keccak_fips202.ml, proved here       *)
(* rather than loading that file, which takes about 15 minutes to load in    *)
(* the toplevel, for the proofs that load this file.                         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/utils/mldsa_native_memset.ml";;

let SAMPLING_NUM_OF_BYTELIST_APPEND = prove
 (`!l1 l2. num_of_bytelist (APPEND l1 l2) =
           num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; num_of_bytelist; LENGTH; MULT_CLAUSES; EXP;
                  ADD_CLAUSES] THEN
  GEN_TAC THEN REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC NUM_RING);;

let SAMPLING_NUM_OF_BYTELIST_REPLICATE_0 = prove
 (`!n. num_of_bytelist (REPLICATE n (word 0:byte)) = 0`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; num_of_bytelist; VAL_WORD_0] THEN ARITH_TAC);;

let MLD_WORD_XOR_DISJOINT = prove
 (`!a b k. a < 2 EXP k
           ==> word_xor (word a) (word(2 EXP k * b)):N word =
               word(a + 2 EXP k * b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_and (word a) (word(2 EXP k * b)):N word = word 0`
  ASSUME_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD; BIT_WORD_0] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < k` THENL
     [SUBGOAL_THEN `~ODD((2 EXP k * b) DIV 2 EXP i)`
       (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `2 EXP k * b = 2 EXP i * (2 EXP (k - i) * b)` SUBST1_TAC
      THENL
       [REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD] THEN AP_THM_TAC THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[NOT_ODD; EVEN_MULT; EVEN_EXP; ARITH_EVEN] THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `a DIV 2 EXP i = 0` (fun th -> REWRITE_TAC[th; ODD]) THEN
      MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP k` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    ASM_SIMP_TAC[GSYM WORD_ADD_XOR; WORD_ADD]]);;

let MLD_NUM_OF_BYTELIST_LIST_OF_SEQ_DIGIT = prove
 (`!(f:num->byte) n j.
        j < n
        ==> (num_of_bytelist(list_of_seq f n) DIV 2 EXP (8 * j)) MOD 256 =
            val(f j)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT] THEN
  X_GEN_TAC `j:num` THEN
  REWRITE_TAC[list_of_seq; SAMPLING_NUM_OF_BYTELIST_APPEND;
              LENGTH_LIST_OF_SEQ; num_of_bytelist; MULT_CLAUSES;
              ADD_CLAUSES] THEN
  MP_TAC(ISPEC `list_of_seq (f:num->byte) n` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; ARITH_RULE `256 = 2 EXP 8`;
              GSYM EXP_MULT] THEN
  REWRITE_TAC[ARITH_RULE `8 * n = n * 8`] THEN
  ABBREV_TAC `x = num_of_bytelist(list_of_seq (f:num->byte) n)` THEN
  DISCH_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN
    MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `(f:num->byte) n` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; ARITH_RULE `8 * j = j * 8`]
    THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `2 EXP (n * 8) = 2 EXP (j * 8) * 2 EXP 8 * 2 EXP ((n - j - 1) * 8)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[MOD_MULT_ADD]]);;

let MLD_KECCAK_SQUEEZE_STATE_BLOCKS = prove
 (`!r (S:1600 word) n.
        0 < r /\ 0 < n
        ==> mld_keccak_squeeze_state r S r (r * n) = (keccak_squeeze n S,r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_keccak_squeeze_state] THEN
  ASM_SIMP_TAC[MULT_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `(r + r * n - 1) DIV r = n` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r - 1` THEN
    MP_TAC(SPECL [`r:num`; `n:num`] LT_MULT) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `0 < r` THEN ARITH_TAC;
    REWRITE_TAC[PAIR_EQ] THEN ARITH_TAC]);;

let MLD_KECCAK_PAD_SHORT = prove
 (`!r p inlen.
        inlen + 2 <= r /\ p < 256
        ==> num_of_bytelist(keccak_pad r p inlen) =
            p + 2 EXP (8 * (r - inlen - 1)) * 128`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_pad] THEN
  SUBGOAL_THEN `inlen MOD r = inlen` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(inlen = r - 1)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[num_of_bytelist; SAMPLING_NUM_OF_BYTELIST_APPEND;
              LENGTH_REPLICATE; SAMPLING_NUM_OF_BYTELIST_REPLICATE_0;
              VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  SUBGOAL_THEN `8 * (r - inlen - 1) = 8 + 8 * (r - inlen - 2)` SUBST1_TAC
  THENL [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD] THEN ARITH_TAC]);;

let MLD_KECCAK_ABSORB_ONCE_SHORT = prove
 (`!r p inlen M.
        inlen + 2 <= r /\ p < 128 /\ M < 2 EXP (8 * inlen)
        ==> mld_keccak_finalize r p
             (FST(mld_keccak_absorb r (word 0) 0 inlen M))
             (SND(mld_keccak_absorb r (word 0) 0 inlen M)) =
            mld_keccak_absorb_once r p inlen M`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_keccak_absorb; mld_keccak_finalize; mld_keccak_absorb_once;
              ADD_CLAUSES; MULT_CLAUSES; EXP; MULT_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `inlen DIV r = 0 /\ inlen MOD r = inlen` STRIP_ASSUME_TAC
  THENL [CONJ_TAC THENL [MATCH_MP_TAC DIV_LT; MATCH_MP_TAC MOD_LT] THEN
         ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[mld_keccak_absorb_blocks; keccak_absorb; MULT_CLAUSES; EXP;
                  DIV_1; WORD_XOR_0] THEN
  ASM_SIMP_TAC[MLD_KECCAK_PAD_SHORT; ARITH_RULE `p < 128 ==> p < 256`] THEN
  SUBGOAL_THEN `M < 2 EXP (8 * r)` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (8 * inlen)` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; MLD_WORD_XOR_DISJOINT] THEN
  SUBGOAL_THEN
   `2 EXP (8 * inlen) * (p + 2 EXP (8 * (r - inlen - 1)) * 128) =
    2 EXP (8 * inlen) * p + 2 EXP (8 * (r - 1)) * 128`
  SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD] THEN
    REWRITE_TAC[EQ_ADD_LCANCEL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `M + 2 EXP (8 * inlen) * p < 2 EXP (8 * (r - 1))` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (8 * inlen) + 2 EXP (8 * inlen) * 127` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `a < c /\ b <= d ==> a + b < c + d`) THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `a + a * 127 = 2 EXP 7 * a`; GSYM EXP_ADD] THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MLD_WORD_XOR_DISJOINT; ADD_ASSOC] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP (8 * (r - 1)) + 2 EXP (8 * (r - 1)) * 128` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[LT_ADD_RCANCEL]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `a + a * 128 = 129 * a`] THEN
  TRANS_TAC LE_TRANS `2 EXP 8 * 2 EXP (8 * (r - 1))` THEN
  CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM EXP_ADD; LE_EXP] THEN ASM_ARITH_TAC);;

let MLD_SHAKE256_BYTE_STREAM = prove
 (`!inlen M.
        inlen + 2 <= 136 /\ M < 2 EXP (8 * inlen)
        ==> mld_shake256_byte inlen M = mld_shake256_stream inlen M`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_shake256_byte; mld_shake256_stream; mld_shake256_state] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MLD_KECCAK_ABSORB_ONCE_SHORT THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The bytes of a buffer from its value as a number, or from a list of       *)
(* bytes, and the bytes of the blocks that mldsa_shake128x4_squeezeblocks    *)
(* and mldsa_shake256x4_squeezeblocks write as bytes of the stream from the  *)
(* state, for the precondition of the samplers.                              *)
(* ------------------------------------------------------------------------- *)

let MLD_READ_BYTES_BYTES8 = prove
 (`!a:int64 n x s:x86state.
        read (memory :> bytes(a,n)) s = x
        ==> !j. j < n
                ==> read (memory :> bytes8(word_add a (word j))) s =
                    word((x DIV 2 EXP (8 * j)) MOD 256)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `x:num`; `j:num`; `1`; `s:x86state`]
    READ_MEMORY_BYTES_SUB) THEN
  ASM_REWRITE_TAC[READ_MEMORY_BYTES_BYTES8] THEN
  ANTS_TAC THENL [UNDISCH_TAC `j < n` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(RAND_CONV NUM_REDUCE_CONV)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL]);;

let MLD_READ_BYTES_LIST_OF_SEQ = prove
 (`!a:int64 n (f:num->byte) s:x86state.
        read (memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n)
        ==> !j. j < n
                ==> read (memory :> bytes8(word_add a (word j))) s = f j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP MLD_READ_BYTES_BYTES8) THEN
  ASM_SIMP_TAC[MLD_NUM_OF_BYTELIST_LIST_OF_SEQ_DIGIT; WORD_VAL]);;

let MLD_SQUEEZE_BLOCKS_BYTES8 = prove
 (`!a:int64 r n (S:1600 word) s:x86state.
        0 < r /\
        read (memory :> bytes(a,r * n)) s =
        nsum {i | i < n}
         (\i. 2 EXP (8 * r * i) *
              val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * r))
        ==> !j. j < r * n
                ==> read (memory :> bytes8(word_add a (word j))) s =
                    mld_keccak_squeeze_byte r S r j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP MLD_READ_BYTES_BYTES8) THEN
  ASM_SIMP_TAC[MLD_SQUEEZE_BLOCKS_BYTE]);;

(* ------------------------------------------------------------------------- *)
(* The addresses in the facts !j. j < n ==> read (memory :> bytes8(a j)) s = *)
(* ... about the bytes of a buffer at offset k from a base, as given by      *)
(* MLD_READ_BYTES_LIST_OF_SEQ for example, put in the form word_add base     *)
(* (word(k + j)) in which the simulation states the precondition of a callee *)
(* that reads the buffer (e.g. mld_rej_uniform_c):                           *)
(* SAMPLING_BYTES_NORMALIZE_TAC.                                             *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_BYTES_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if is_forall(concl th) &&
       can (find_term (fun t -> match t with
              Const("bytes8",_) -> true | _ -> false)) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

(* ------------------------------------------------------------------------- *)
(* The tests of counts of coefficients against 255, as 32-bit compares, the  *)
(* conditional branches and SETBE, and the OR of the bytes from SETBE (as in *)
(* mldsa_poly_uniform_4x, where the high bits of a register may be unknown): *)
(* SAMPLING_COUNT_TEST_TAC cs res, for the counts cs, each of the form MIN   *)
(* 256 x, finds the conditional of the RIP that depends on them, proves that *)
(* its condition is res, a term in n0, n1, ..., for the counts (or its       *)
(* negation), for all counts up to 256, by case analysis and bit-blasting,   *)
(* and rewrites all assumptions with that and with 255 < MIN 256 x <=> 256   *)
(* <= x, so that the events have the condition in that form, without the     *)
(* unknown bits. SAMPLING_CASE_REWRITE_TAC rewrites the other assumptions    *)
(* with the last one, e.g. a case assumption, keeping it.                    *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_CMP_255 = prove
 (`!c. c < 2 EXP 32
       ==> val(word_zx(word c:int64):int32) = c /\
           (&c - &255:int =
            &(val(word_sub (word_zx (word c:int64):int32) (word 255))) <=>
            255 <= c) /\
           (val(word_sub (word_zx (word c:int64):int32) (word 255)) = 0 <=>
            c = 255)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word_zx(word c:int64):int32) = c` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT; ARITH_RULE
     `c < 4294967296 ==> c < 18446744073709551616`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN ASM_ARITH_TAC;
    CONJ_TAC THENL
     [MATCH_MP_TAC(TAUT `~a /\ ~b ==> (a <=> b)`) THEN
      CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      MATCH_MP_TAC(INT_ARITH
       `x < &255 /\ &0 <= y ==> ~(x - &255:int = y)`) THEN
      REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;

let SAMPLING_BYTE_DECIDE_CONV t =
  if not(can (find_term (fun u -> can dest_word_ty (type_of u))) t)
  then failwith "SAMPLING_BYTE_DECIDE_CONV" else
  try EQT_INTRO(BITBLAST_RULE t)
  with Failure _ -> EQF_INTRO(BITBLAST_RULE(mk_neg t));;

let SAMPLING_COUNT_TEST_PROVE_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    let bths = map (fun cth ->
                  let c = concl cth in
                  MP (ARITH_RULE(mk_imp(c,mk_binop `(<):num->num->bool`
                                              (lhand c) `2 EXP 32`))) cth)
                   (CONJUNCTS th) in
    MAP_EVERY ASSUME_TAC (CONJUNCTS th @ bths)) THEN
  ASM_SIMP_TAC[WORD_ZX_32_SMALL] THEN ASM_SIMP_TAC[SAMPLING_CMP_255] THEN
  REWRITE_TAC[SAMPLING_WORD_MOD_256; GSYM word_zx; VAL_EQ_0] THEN
  REPEAT COND_CASES_TAC THEN
  TRY(CONV_TAC(LAND_CONV SAMPLING_BYTE_DECIDE_CONV)) THEN
  REWRITE_TAC[] THEN ASM_ARITH_TAC;;

let SAMPLING_COUNT_TEST_TAC cs res =
  let vs = map (fun i -> mk_var("n"^string_of_int i,`:num`))
               (0--(length cs - 1)) in
  let ant = list_mk_conj
             (map (fun v -> mk_binop `(<=):num->num->bool` v `256`) vs) in
  let bth = end_itlist CONJ
             (map (fun c -> SPECL [`256`; rand c]
                    (ARITH_RULE `!a b. MIN a b <= a`)) cs) in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),_)),
           Comb(Comb(Comb(Const("COND",_),cnd),_),_))
        when exists (fun c -> free_in c cnd) cs ->
        let mk r = list_mk_forall(vs,mk_imp(ant,
                     mk_eq(subst (zip vs cs) cnd,r))) in
        let lth = try prove(mk res,SAMPLING_COUNT_TEST_PROVE_TAC)
                  with Failure _ ->
                    prove(mk(mk_neg res),SAMPLING_COUNT_TEST_PROVE_TAC) in
        RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL cs lth) bth;
                                    ARITH_RULE `255 < MIN 256 x <=> 256 <= x`])
    | _ -> NO_TAC);;

let SAMPLING_CASE_REWRITE_TAC =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    let eth = if is_neg c then EQF_INTRO th else EQT_INTRO th in
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = c then th' else REWRITE_RULE[eth] th'));;

(* ------------------------------------------------------------------------- *)
(* The events at the end of a part of a proof with calls, whose precondition *)
(* gives the memory safety of the events since the start as a whole:         *)
(* SAMPLING_PATH_DISCHARGE_SPINE_TAC is SAMPLING_PATH_DISCHARGE_TAC (which   *)
(* matches the events with the template, also for loops whose iterations     *)
(* take one of several paths), except for the check of the memory accesses,  *)
(* which DISCHARGE_MEMACCESS_INBOUNDS_TAC makes very slow for the long lists *)
(* of events of the samplers: it drops the assumptions about the state and   *)
(* the theorems of the callees, names the offsets 31 - val(x) MOD 32 of the  *)
(* realigned frames (bounded by 31), puts the event lists of the goal and of *)
(* the definitions of the events so far in one form                          *)
(* (SAMPLING_EVENTS_NORM_CONV: without APPEND [] or APPEND l [], with        *)
(* negated comparisons as in NOT_LE, and right-associated by                 *)
(* APPEND_SPINE_CONV of utils/mldsa_native_absorb.ml), and then checks the   *)
(* parts of the events of the goal one by one                                *)
(* (SAMPLING_MEMACCESS_SPINE_TAC): the events of a callee and the events so  *)
(* far by their facts, found by matching their lists, and the rest as        *)
(* concrete lists.                                                           *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/utils/mldsa_native_absorb.ml";;

let SAMPLING_EVENTS_NORM_CONV =
  REWRITE_CONV[APPEND_NIL; CONJUNCT1 APPEND; NOT_LE] THENC
  APPEND_SPINE_CONV;;

let SAMPLING_MEMACCESS_SPINE_TAC =
  let is_mi tm =
    is_comb tm && (try fst(dest_const(fst(strip_comb tm))) =
                       "memaccess_inbounds" with Failure _ -> false) in
  let mi_list tm = hd(snd(strip_comb tm)) in
  let list_conv conv = RATOR_CONV(RATOR_CONV(RAND_CONV conv)) in
  let contained_tac =
    MATCH_MP_TAC MEMACCESS_INBOUNDS_CONTAINED THEN
    DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC in
  let part_tac facts p =
    match (try Some(find (fun th -> mi_list(concl th) = p) facts)
           with Failure _ -> None) with
      Some th ->
        (fun (asl,w) ->
          if concl th = w then ACCEPT_TAC th (asl,w)
          else (MP_TAC th THEN
                ((MATCH_MP_TAC MEMACCESS_INBOUNDS_MEM THEN
                  REWRITE_TAC[ALL; MEM] THEN NO_TAC) ORELSE
                 contained_tac)) (asl,w))
    | None -> DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC in
  let rec spine_tac facts (asl,w) =
    let l = mi_list w in
    if exists (fun th -> mi_list(concl th) = l) facts then
      part_tac facts l (asl,w)
    else match l with
      Comb(Comb(Const("APPEND",_),a),b) ->
        (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
         CONJ_TAC THENL [part_tac facts a; spine_tac facts]) (asl,w)
    | Comb(Comb(Const("CONS",_),_),_) ->
        (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_CONS] THEN
         CONJ_TAC THENL
          [DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC;
           spine_tac facts]) (asl,w)
    | _ -> part_tac facts l (asl,w) in
  fun (asl,w) ->
    let defs = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && is_var(lhs c) && type_of(lhs c) = `:(uarch_event)list`
      then th else failwith "") asl in
    let facts = mapfilter (fun (_,th) ->
      if not(is_mi(concl th)) then failwith "" else
      let l = mi_list(concl th) in
      if is_var l then
        (try let d = find (fun d -> lhs(concl d) = l) defs in
             CONV_RULE(list_conv(REWR_CONV d THENC SAMPLING_EVENTS_NORM_CONV))
                      th
         with Failure _ -> th)
      else CONV_RULE(list_conv SAMPLING_EVENTS_NORM_CONV) th) asl in
    (CONV_TAC(list_conv SAMPLING_EVENTS_NORM_CONV) THEN
     spine_tac facts) (asl,w);;

let SAMPLING_ABBREV_DELTAS_TAC (asl,w) =
  let pat = `31 - val(x:int64) MOD 32` in
  let ts = setify(find_terms (can (term_match [] pat)) w) in
  MAP_EVERY (fun t ->
    ASSUME_TAC(ARITH_RULE(mk_binop `(<=):num->num->bool` t `31`)) THEN
    ABBREV_TAC(mk_eq(genvar `:num`,t))) ts (asl,w);;

let SAMPLING_PATH_DISCHARGE_SPINE_TAC =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  let has_const s tm =
    can (find_term (fun t -> is_const t && fst(dest_const t) = s)) tm in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN SAMPLING_SELECT_TAC THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then
      CONJ_TAC THENL
       [FULL_UNIFY_F_EVENTS_TAC ORELSE
        (CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
         REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC);
        ALL_TAC]
    else ALL_TAC) THEN
  beta_all THEN
  REWRITE_TAC[NOT_LT] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  DISCARD_ASSUMPTIONS_TAC
   (fun th -> has_const "read" (concl th) || has_const "ensures" (concl th))
  THEN
  SAMPLING_ABBREV_DELTAS_TAC THEN SAMPLING_MEMACCESS_SPINE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The extended seeds of the SHAKE256 samplers: the seed of 64 bytes as four *)
(* 128-bit words, as the code loads and stores it, and the 66 bytes of the   *)
(* seed followed by a 16-bit nonce, or by a nonce byte and a zero byte. The  *)
(* nonces are stored from 32-bit registers, as the low 16 or 8 bits, and the *)
(* nonces that the caller passes on the stack are loaded as 32-bit words     *)
(* from their 64-bit slots (SAMPLING_READ_BYTES32_OF_64).                    *)
(* ------------------------------------------------------------------------- *)

let MLD_READ_BYTES128 = prove
 (`!a:int64 s:x86state.
        read (memory :> bytes128 a) s = word(read (memory :> bytes(a,16)) s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory (s:x86state)`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let MLD_READ_BYTES_CHUNKS = prove
 (`!k (a:int64) n (s:x86state).
        read (memory :> bytes(a,16 * k)) s = n
        ==> !j. j < k
                ==> read (memory :> bytes128(word_add a (word(16 * j)))) s =
                    word((n DIV 2 EXP (128 * j)) MOD 2 EXP 128)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLD_READ_BYTES128] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`a:int64`; `16 * k`; `n:num`; `16 * j`; `16`; `s:x86state`]
    READ_MEMORY_BYTES_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `j < k` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * 16 * j = 128 * j`; ARITH_RULE `8 * 16 = 128`]);;

let MLD_BYTES_OF_CHUNKS = prove
 (`!k (a:int64) n (s:x86state).
        n < 2 EXP (128 * k) /\
        (!j. j < k
             ==> read (memory :> bytes128(word_add a (word(16 * j)))) s =
                 word((n DIV 2 EXP (128 * j)) MOD 2 EXP 128))
        ==> read (memory :> bytes(a,16 * k)) s = n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; ARITH_RULE `n < 1 <=> n = 0`] THEN
    SIMP_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * SUC k = 16 + 16 * k`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`word_add a (word 16):int64`; `n DIV 2 EXP 128`; `s:x86state`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      UNDISCH_TAC `n < 2 EXP (128 * SUC k)` THEN
      REWRITE_TAC[ARITH_RULE `128 * SUC k = 128 + 128 * k`];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j + 1`) THEN
      ANTS_TAC THENL [UNDISCH_TAC `j < k` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                  ARITH_RULE `16 + 16 * j = 16 * (j + 1)`;
                  ARITH_RULE `128 + 128 * j = 128 * (j + 1)`]];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[LT_0; MULT_CLAUSES; EXP; DIV_1; WORD_ADD_0;
              MLD_READ_BYTES128] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_128; MOD_MOD_REFL] THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory (s:x86state)`]
                READ_BYTES_BOUND) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ARITH_RULE `8 * 16 = 128`] THEN
  SIMP_TAC[MOD_LT] THEN DISCH_THEN(K ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`n:num`; `2 EXP 128`] DIVISION) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC);;

let MLD_READ_BYTES16 = prove
 (`!a:int64 s:x86state.
        read (memory :> bytes16 a) s = word(read (memory :> bytes(a,2)) s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`a:int64`; `2`; `read memory (s:x86state)`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let MLD_READ_BYTES66_NONCE16 = prove
 (`!a:int64 n (h:int16) s:x86state.
        read (memory :> bytes(a,64)) s = n /\
        read (memory :> bytes16(word_add a (word 64))) s = h
        ==> read (memory :> bytes(a,66)) s = n + 2 EXP 512 * val h`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[ARITH_RULE `66 = 64 + 2`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; MLD_READ_BYTES16; VAL_WORD;
              DIMINDEX_16] THEN
  AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`word_add a (word 64):int64`; `2`;
                 `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let MLD_READ_BYTES66_NONCE8 = prove
 (`!a:int64 n (b:byte) s:x86state.
        read (memory :> bytes(a,64)) s = n /\
        read (memory :> bytes8(word_add a (word 64))) s = b /\
        read (memory :> bytes8(word_add a (word 65))) s = word 0
        ==> read (memory :> bytes(a,66)) s = n + 2 EXP 512 * val b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `66 = (64 + 1) + 1`; READ_MEMORY_BYTES_SNOC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `64 + 1 = 65`; VAL_WORD_0] THEN ARITH_TAC);;

let SAMPLING_READ_BYTES32_OF_64 = prove
 (`!a:int64 x s:x86state.
        read (memory :> bytes64 a) s = x
        ==> read (memory :> bytes32 a) s = word_zx x`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; BYTES64_WBYTES; BYTES32_WBYTES;
              READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  MP_TAC(SPECL [`a:int64`; `8`;
                `read (memory :> bytes(a:int64,8)) (s:x86state)`;
                `0`; `4`; `s:x86state`] READ_MEMORY_BYTES_SUB) THEN
  REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIV_1]);;

let SAMPLING_WORD_ZX_16 = prove
 (`(!x:int64. word_zx(word_zx x:int32):int16 = word_zx x) /\
   (!x:int64. word_zx(word_zx(word_zx x:int32):int64):int16 = word_zx x) /\
   (!x:int16.
      word_zx(word_zx(word_zx(word_zx x:int32):int64):int32):int16 = x)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN BITBLAST_TAC);;

let SAMPLING_WORD_MOD_65536 = prove
 (`!n. word(n MOD 65536):int16 = word n`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

let SAMPLING_WORD_ZX_8 = prove
 (`(!x:int64. word_zx(word_zx x:int32):byte = word_zx x) /\
   (!x:int64. word_zx(word_zx(word_zx x:int32):int64):byte = word_zx x) /\
   (!x:byte.
      word_zx(word_zx(word_zx(word_zx x:int32):int64):int32):byte = x)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN BITBLAST_TAC);;

(*** From the bytes of a buffer below m to those below n <= m ***)

let SAMPLING_BOUND_RULE n th =
  let j,bd = dest_forall(concl th) in
  let ant,_ = dest_imp bd in
  let ant' = mk_binop `(<):num->num->bool` j (mk_small_numeral n) in
  let lth = ARITH_RULE(mk_imp(ant',ant)) in
  GEN j (DISCH ant' (MP (SPEC j th) (MP lth (ASSUME ant'))));;

let SAMPLING_NONCE_BYTES_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (memory :> bytes8 a) s = (x:byte)`) (concl th)
    then REWRITE_RULE[SAMPLING_WORD_MOD_256; GSYM word_zx; SAMPLING_WORD_ZX_8]
                     th
    else if can (term_match [] `read (memory :> bytes16 a) s = (x:int16)`)
                (concl th)
    then REWRITE_RULE[SAMPLING_WORD_MOD_65536; GSYM word_zx;
                      SAMPLING_WORD_ZX_16] th
    else th);;

let SAMPLING_SUBWORD_JOIN_128 = prove
 (`!(h:int128) (l:int128). word_subword (word_join h l:256 word) (0,128) = l`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* SAMPLING_GHOST_REGS_TAC rs s names the values of the registers rs in      *)
(* state s, e.g. the YMM registers whose low 128 bits the code loads, so     *)
(* that the facts about their new values, which keep the high bits, are not  *)
(* discarded as facts about an old state.                                    *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_GHOST_REGS_TAC rs s =
  let sv = mk_var(s,`:x86state`) in
  MAP_EVERY (fun r ->
    let n = String.lowercase_ascii(fst(dest_const r)) ^ "_" ^ s in
    let t = list_mk_icomb "read" [r; sv] in
    ABBREV_TAC(mk_eq(mk_var(n,type_of t),t))) rs;;

(* ------------------------------------------------------------------------- *)
(* The 16-bit nonces kappa + j of mld_polyvecl_uniform_gamma1, which the x86 *)
(* code computes with LEA and MOVZX in 32-bit registers and passes in R9 or  *)
(* RDX or on the stack as 64-bit words. SAMPLING_NONCE16_CONV kappa proves   *)
(* word_zx t = word_add (word_zx kappa) (word j), for the 16-bit word_zx of  *)
(* a term t in kappa alone, with j found by evaluating t at kappa = 0, and   *)
(* SAMPLING_NONCE16_TAC kappa rewrites the results of the callees with it,   *)
(* into the form of the statements.                                          *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_NONCE16_CONV =
  let nconv = REWRITE_CONV[SAMPLING_WORD_MOD_65536; SAMPLING_WORD_MOD_256;
                           GSYM word_zx] in
  fun kappa tm ->
    match tm with
      Comb(Const("word_zx",_),t)
        when type_of tm = `:int16` && t <> kappa && frees t = [kappa] ->
        let nth = nconv tm in
        let tm' = rhs(concl nth) in
        let t0 = vsubst [mk_comb(`word:num->int64`,`0`),kappa] tm' in
        let j = rand(rhs(concl(WORD_REDUCE_CONV t0))) in
        TRANS nth
         (BITBLAST_RULE
           (mk_eq(tm',list_mk_comb(`word_add:int16->int16->int16`,
                        [mk_comb(`word_zx:int64->int16`,kappa);
                         mk_comb(`word:num->int16`,j)]))))
    | _ -> failwith "SAMPLING_NONCE16_CONV";;

let SAMPLING_NONCE16_TAC kappa =
  let is_g1 t =
    match t with
      Const(n,_) -> String.length n >= 23 &&
                    String.sub n 0 23 = "mld_poly_uniform_gamma1"
    | _ -> false in
  RULE_ASSUM_TAC(fun th ->
    if can (find_term is_g1) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV(SAMPLING_NONCE16_CONV kappa)) th
    else th);;

(* ------------------------------------------------------------------------- *)
(* SAMPLING_ALIGNED_FROM_TAC base off0 w offs adds aligned w (word_add base  *)
(* (word off)) to the assumptions for each off in offs, given aligned w      *)
(* (word_add base (word off0)) there and w dividing off - off0, e.g. for the *)
(* addresses of the SSE stores in a frame aligned to 32 bytes, from the      *)
(* alignment that REALIGN_ALIGNED_TAC (utils/mldsa_native_realign.ml) gives, *)
(* in the form in which the simulation decides their alignment.              *)
(* ------------------------------------------------------------------------- *)

let SAMPLING_ALIGNED_FROM_TAC base off0 w offs =
  let mk n = mk_comb(mk_comb(`word_add:int64->int64->int64`,base),
                     mk_comb(`word:num->int64`,mk_small_numeral n)) in
  let al t = mk_comb(mk_comb(`aligned:num->int64->bool`,mk_small_numeral w),
                     t) in
  MAP_EVERY (fun off ->
    let t0 = mk off0 and t = mk off in
    SUBGOAL_THEN (al t) ASSUME_TAC THENL
     [SUBGOAL_THEN
       (mk_eq(t,mk_comb(mk_comb(`word_add:int64->int64->int64`,t0),
                        mk_comb(`word:num->int64`,
                                mk_small_numeral(off - off0)))))
       SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC]) offs;;
