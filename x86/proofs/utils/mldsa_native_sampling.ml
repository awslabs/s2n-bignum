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
