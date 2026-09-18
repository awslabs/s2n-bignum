(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "riscv/proofs/mldsa_ntt_layout.ml";;

(* ========================================================================= *)
(* Shared driver for the two forward-NTT arithmetic bridges.                 *)
(* ========================================================================= *)

let RV32_NTT_BOUNDS_ABS_LT = prove
 (`!x l u b:int.
     (l <= x /\ x <= u) /\ (--b < l /\ u < b)
     ==> abs x < b`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  REWRITE_TAC[INT_ABS] THEN
  COND_CASES_TAC THEN
  ASM_INT_ARITH_TAC);;

(* The arithmetic driver propagates congruence-and-bound facts through all
   four radix-4 phases. A backend chooses only how to close the input, stage,
   and output congruences. The structured backend replaces each expanded
   stage with a compact partial-transform theorem; the independent linear
   backend checks the fully expanded congruence directly. *)

type rv32_mldsa_ntt_phase1234_backend = {
  rv32_ntt_close_input : int -> thm -> thm;
  rv32_ntt_close_stage : int -> int -> thm -> thm;
  rv32_ntt_close_output : int -> thm -> thm
};;

let RV32_MLDSA_NTT_PHASE1234_PROVE backend =
  let congbound_map tms ths =
    let rec build tms ths =
      match tms,ths with
        [],[] -> undefined
      | tm::otms,th::oths -> (tm |-> th) (build otms oths)
      | _ -> failwith "congbound_map" in
    build tms ths in
  let input_bounds =
    map
     (fun n ->
        ASSUME
         (subst
           [mk_small_numeral n,`i:num`]
           `abs(ival((x:num->int32) i)) < &8380417`))
     (0--255) in
  let input_terms =
    map
     (fun n ->
        mk_comb
         (`x:num->int32`,mk_small_numeral n))
     (0--255) in
  let input_map =
    PROCESS_BOUND_ASSUMPTIONS input_bounds in
  let input_facts =
    List.mapi
     (fun n tm ->
        backend.rv32_ntt_close_input
          n (apply input_map tm))
     input_terms in
  let initial_map =
    congbound_map input_terms input_facts in
  let pair_terms =
    map
     (fun n ->
        mk_comb
         (`rv32_mldsa_ntt_pair`,mk_small_numeral n))
     (0--254) in
  let pair_thms =
    map
     ((GEN_REWRITE_CONV I [rv32_mldsa_ntt_pair] THENC
       DEPTH_CONV NUM_RED_CONV THENC
       GEN_REWRITE_CONV DEPTH_CONV [rv32_mldsa_ntt_zetas] THENC
       DEPTH_CONV EL_CONV))
     pair_terms in
  let pair_num_conv tm =
    let n = dest_small_numeral(rand tm) in
    let th = List.nth pair_thms n in
    if aconv (lhand(concl th)) tm then th
    else failwith "pair_num_conv" in
  let build_congbound rule conv tm =
    let eth = conv tm in
    let cth = rule (rand(concl eth)) in
    SUBS[SYM eth] cth in
  let build_congbound_groups base conv groups =
    flat
     (map
       (fun terms ->
          let rule = MEMOIZED_ASM_CONGBOUND_RULE base in
          map (build_congbound rule conv) terms)
       groups) in
  let run_stage phase base conv groups =
    let terms = flat groups in
    let raw =
      build_congbound_groups base conv groups in
    let closed =
      List.mapi
       (backend.rv32_ntt_close_stage phase)
       raw in
    congbound_map terms closed,closed in
  let phase1_term n =
    subst
     [mk_small_numeral (n mod 64),`j:num`;
      mk_small_numeral (n / 64),`r:num`]
     `rv32_mldsa_ntt_phase1 (x:num->int32) j r` in
  let phase1_expand_conv =
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [rv32_mldsa_ntt_phase1; rv32_mldsa_radix4] THENC
    DEPTH_CONV NUM_RED_CONV THENC
    TOP_DEPTH_CONV let_CONV THENC
    DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV in
  let phase1_groups =
    map
     (fun j ->
        map
         (fun r -> phase1_term (j + 64 * r))
         (0--3))
     (0--63) in
  let phase1_map,_ =
    run_stage 0 initial_map
      phase1_expand_conv phase1_groups in
  let phase12_term n =
    subst
     [mk_small_numeral (n / 64),`h:num`;
      mk_small_numeral (n mod 16),`l:num`;
      mk_small_numeral ((n / 16) mod 4),`r:num`]
     `rv32_mldsa_ntt_phase12 (x:num->int32) h l r` in
  let phase12_expand_conv =
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [rv32_mldsa_ntt_phase12; rv32_mldsa_ntt_phase2;
      rv32_mldsa_radix4] THENC
    DEPTH_CONV NUM_RED_CONV THENC
    TOP_DEPTH_CONV let_CONV THENC
    DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV THENC
    DEPTH_CONV pair_num_conv in
  let phase12_groups =
    flat
     (map
       (fun h ->
          map
           (fun l ->
              map
               (fun r ->
                  phase12_term (64 * h + l + 16 * r))
               (0--3))
           (0--15))
       (0--3)) in
  let phase12_map,_ =
    run_stage 1 phase1_map
      phase12_expand_conv phase12_groups in
  let phase123_term n =
    subst
     [mk_small_numeral (n / 16),`h:num`;
      mk_small_numeral (n mod 4),`l:num`;
      mk_small_numeral ((n / 4) mod 4),`r:num`]
     `rv32_mldsa_ntt_phase123 (x:num->int32) h l r` in
  let phase123_expand_conv =
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [rv32_mldsa_ntt_phase123; rv32_mldsa_ntt_phase3;
      rv32_mldsa_radix4] THENC
    DEPTH_CONV NUM_RED_CONV THENC
    TOP_DEPTH_CONV let_CONV THENC
    DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV THENC
    DEPTH_CONV pair_num_conv in
  let phase123_groups =
    flat
     (map
       (fun h ->
          map
           (fun l ->
              map
               (fun r ->
                  phase123_term (16 * h + l + 4 * r))
               (0--3))
           (0--3))
       (0--15)) in
  let phase123_map,_ =
    run_stage 2 phase12_map
      phase123_expand_conv phase123_groups in
  let phase1234_term n =
    subst
     [mk_small_numeral (n / 4),`g:num`;
      mk_small_numeral (n mod 4),`r:num`]
     `rv32_mldsa_ntt_phase1234 (x:num->int32) g r` in
  let phase1234_expand_conv =
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [rv32_mldsa_ntt_phase1234; rv32_mldsa_ntt_phase4;
      rv32_mldsa_radix4] THENC
    DEPTH_CONV NUM_RED_CONV THENC
    TOP_DEPTH_CONV let_CONV THENC
    DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV THENC
    DEPTH_CONV pair_num_conv in
  let phase1234_groups =
    map
     (fun g ->
        map
         (fun r -> phase1234_term (4 * g + r))
         (0--3))
     (0--63) in
  let _,phase1234_facts =
    run_stage 3 phase123_map
      phase1234_expand_conv phase1234_groups in
  let final_output_rule n cb =
    let congruence =
      backend.rv32_ntt_close_output n cb in
    let bounds = CONJUNCT2 cb in
    let lower,upper = dest_conj(concl bounds) in
    let ltm,xtm =
      dest_binop `(<=):int->int->bool` lower
    and xtm',utm =
      dest_binop `(<=):int->int->bool` upper in
    if not(aconv xtm xtm') then
      failwith "final_output_rule" else
    let side =
      EQT_ELIM
       (INT_REDUCE_CONV
         (subst
           [ltm,`l:int`; utm,`u:int`]
           `(-- &94279698:int) < l /\ (u:int) < &94279698`)) in
    let abs_bound =
      MATCH_MP
       (SPECL [xtm;ltm;utm;`&94279698:int`]
         RV32_NTT_BOUNDS_ABS_LT)
       (CONJ bounds side) in
    CONJ congruence abs_bound in
  let final_outputs =
    List.mapi final_output_rule phase1234_facts in
  let all_outputs =
    end_itlist CONJ
     (flat(map CONJUNCTS final_outputs)) in
  let input_conj =
    list_mk_conj(map concl input_bounds) in
  let all_outputs_imp =
    DISCH input_conj
     (itlist PROVE_HYP
       (CONJUNCTS(ASSUME input_conj))
       all_outputs) in
  prove
   (`!x:num->int32.
       (!i. i < 256 ==> abs(ival(x i)) < &8380417)
       ==> !i. i < 256
               ==> (ival
                     (rv32_mldsa_ntt_phase1234
                       x (i DIV 4) (i MOD 4)) ==
                    mldsa_bitreverse_forward_ntt (ival o x) i)
                   (mod &8380417) /\
                   abs(ival
                     (rv32_mldsa_ntt_phase1234
                       x (i DIV 4) (i MOD 4))) < &94279698`,
    GEN_TAC THEN
    DISCH_TAC THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    MATCH_MP_TAC all_outputs_imp THEN
    REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONV_TAC NUM_REDUCE_CONV);;

(* ========================================================================= *)
(* Functional interpretation of the four forward-NTT phases.                *)
(* ========================================================================= *)


let RV32_NTT_BLOCK_INDEX_LEFT = prove
 (`!l s j k.
     (l + s * k) + (4 * s) * j = l + s * (4 * j + k)`,
  CONV_TAC NUM_RING);;

let RV32_NTT_PARTIAL_256 = prove
 (`!f:num->int. !n.
     rv32_mldsa_ntt_partial_rv32 f 256 n 0 = f n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rv32_mldsa_ntt_partial_rv32] THEN
  CONV_TAC(DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV) THEN
  CONV_TAC
   (TOP_DEPTH_CONV
     (CHANGED_CONV
       (GEN_REWRITE_CONV I [BITREVERSE8_CLAUSES]))) THEN
  CONV_TAC(DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV) THEN
  CONV_TAC(LAND_CONV EXPAND_ISUM_CONV) THEN
  REWRITE_TAC[INT_POW; MULT_CLAUSES; ADD_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV RV32_NTT_CLOSED_INT_CONV) THEN
  REWRITE_TAC[INT_MUL_RID]);;

let RV32_NTT_INPUT_PARTIAL_CONG = prove
 (`!f:num->int. !n.
     (f n == rv32_mldsa_ntt_partial_rv32 f 256 n 0)
     (mod &0)`,
  REWRITE_TAC
   [INTEGER_RULE `(x:int == y) (mod &0) <=> x = y`;
    RV32_NTT_PARTIAL_256]);;

let RV32_NTT_PARTIAL_1_CONG = prove
 (`!f:num->int. !t.
     (rv32_mldsa_ntt_partial_rv32 f 1 0 t ==
      mldsa_bitreverse_forward_ntt f t)
     (mod &8380417)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
   [rv32_mldsa_ntt_partial_rv32;
    MLDSA_BITREVERSE_FORWARD_NTT_ALT] THEN
  CONV_TAC(DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM]);;

(* Bound each word-level stage with the shared congbound automation, then
   replace its expanded congruence with one partial-transform term. This
   keeps the input to every later stage at constant syntactic depth. *)

let RV32_MLDSA_NTT_PHASE1234_STRUCTURED_BACKEND,
    RV32_MLDSA_NTT_PHASE1234_CORRECT,
    RV32_MLDSA_NTT_PHASE1234_STRUCTURED_TIME =
  let start = Sys.time() in
  let bitreverse8_num n =
    let rec reverse i x y =
      if i = 8 then y
      else reverse (i + 1) (x / 2) (2 * y + x mod 2) in
    reverse 0 n 0 in
  let root_congs =
    Array.init 256
     (fun n ->
        let ntm = mk_small_numeral n in
        let rtm = mk_comb (`rv32_mldsa_ntt_root`,ntm)
        and btm = mk_comb (`bitreverse8`,ntm) in
        let eth = RV32_MLDSA_NTT_ROOT_CONV rtm
        and bth =
          GEN_REWRITE_CONV I [BITREVERSE8_CLAUSES] btm in
        SUBS[eth;bth]
         (SPEC ntm RV32_MLDSA_NTT_ROOT_CONG_FAST)) in
  let root_pattern_theorems =
    [|RV32_COEFF_PATTERN_R0_FAST;
      RV32_COEFF_PATTERN_R1_FAST;
      RV32_COEFF_PATTERN_R2_FAST;
      RV32_COEFF_PATTERN_R3_FAST|] in
  let int_cong_lhs th =
    let _,args = strip_comb(concl th) in
    List.nth args 0 in
  let build_root_pattern p i r =
    let n0 = (1 lsl (2 * p)) + i
    and n1 = (1 lsl (2 * p + 1)) + 2 * i in
    let h0 = root_congs.(n0)
    and h1 = root_congs.(n1)
    and h2 = root_congs.(n1 + 1) in
    let a = mk_small_numeral (bitreverse8_num n1) in
    let z0 = int_cong_lhs h0
    and z1 = int_cong_lhs h1
    and z2 = int_cong_lhs h2 in
    let pth =
      CONV_RULE
       (DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV)
       (SPECL [a;z0;z1;z2] root_pattern_theorems.(r)) in
    MATCH_MP pth (CONJ h0 (CONJ h1 h2)) in
  let root_patterns =
    flat
     (map
       (fun p ->
          flat
           (map
             (fun i ->
                map (build_root_pattern p i) (0--3))
             (0--((1 lsl (2 * p)) - 1))))
       (0--3)) in
  let root_pattern_index p i r =
    4 * (((1 lsl (2 * p)) - 1) / 3 + i) + r in
  let root_pattern_roots th =
    let _,body = dest_forall(concl th) in
    let _,cbody = dest_imp body in
    let _,cargs = strip_comb cbody in
    let coeff = List.nth cargs 0 in
    let _,args = strip_comb coeff in
    List.nth args 0,List.nth args 1,List.nth args 2 in
  let partial_transition_rule p i r =
    let groups = 1 lsl (2 * p) in
    if p < 0 || p > 3 || i < 0 || i >= groups ||
       r < 0 || r >= 4
    then failwith "partial_transition_rule" else
    let s = 64 / groups
    and m = groups - 1 in
    let a =
      (2 * bitreverse8_num (4 * s * i) + 1) * (4 * s)
    and b =
      (2 * bitreverse8_num (s * (4 * i + r)) + 1) * s in
    let coeff =
      List.nth root_patterns (root_pattern_index p i r) in
    let z0,z1,z2 = root_pattern_roots coeff in
    let pow = RV32_ROOT_PRODUCT_RULE_FAST a b in
    let jtm = `j:num`
    and ktm = `k:num`
    and mtm = mk_small_numeral m in
    let guard =
      subst [mtm,`m:num`] `j <= m /\ k < 4` in
    let pow_guarded =
      GENL [jtm;ktm]
       (DISCH guard (SPECL [jtm;ktm] pow)) in
    let rtm = mk_small_numeral r in
    let rlt =
      EQT_ELIM
       (NUM_REDUCE_CONV
         (subst [rtm,`r:num`] `r < 4`)) in
    let stm = mk_small_numeral s
    and ltm = `l:num`
    and atm = mk_small_numeral a
    and btm = mk_small_numeral b in
    let raw =
      MATCH_MP
       (SPECL
         [z0;z1;z2; `f:num->int`; stm;ltm;mtm;atm;btm;rtm]
         RV32_RADIX4_SUM_TRANSITION_FAST)
       (CONJ rlt (CONJ coeff pow_guarded)) in
    let raw =
      REWRITE_RULE[MULT_CLAUSES]
       (CONV_RULE
         (DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV)
         raw) in
    let itm = mk_small_numeral i in
    let goal =
      subst
       [z0,`z0:int`; z1,`z1:int`; z2,`z2:int`;
        stm,`s:num`; itm,`i:num`; rtm,`r:num`]
       `(rv32_mldsa_radix4_int_rv32 z0 z1 z2
           (\k. rv32_mldsa_ntt_partial_rv32
                  (f:num->int) (4 * s) (l + s * k) i) r ==
         rv32_mldsa_ntt_partial_rv32 f s l (4 * i + r))
        (mod &8380417)` in
    GENL [`f:num->int`;ltm]
     (TAC_PROOF
       (([],goal),
        REWRITE_TAC[rv32_mldsa_ntt_partial_rv32] THEN
        REWRITE_TAC[RV32_NTT_BLOCK_INDEX_LEFT] THEN
        CONV_TAC(DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV) THEN
        CONV_TAC
         (TOP_DEPTH_CONV
           (CHANGED_CONV
             (GEN_REWRITE_CONV I [BITREVERSE8_CLAUSES]))) THEN
        CONV_TAC(DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV) THEN
        REWRITE_TAC[MULT_ASSOC] THEN
        CONV_TAC(DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV) THEN
        REWRITE_TAC[MULT_CLAUSES] THEN
        MATCH_ACCEPT_TAC raw)) in
  let partial_transitions =
    flat
     (map
       (fun p ->
          flat
           (map
             (fun i ->
                map (partial_transition_rule p i) (0--3))
             (0--((1 lsl (2 * p)) - 1))))
       (0--3)) in
  let radix4_int_expand_conv =
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [rv32_mldsa_radix4_int_rv32] THENC
    TOP_DEPTH_CONV let_CONV THENC
    DEPTH_CONV BETA_CONV THENC
    DEPTH_CONV NUM_RED_CONV THENC
    DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV in
  let compact_congbound p i l r cb =
    let transition =
      SPECL
       [`ival o (x:num->int32)`;mk_small_numeral l]
       (List.nth
         partial_transitions
         (root_pattern_index p i r)) in
    let transition =
      CONV_RULE
       (DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV)
       transition in
    let _,targs = strip_comb(concl transition) in
    let radix = List.nth targs 0 in
    let expansion = radix4_int_expand_conv radix in
    let congruence =
      SUBS [SYM expansion] (CONJUNCT1 cb) in
    let compact =
      RV32_INT_CONG_TRANS_RULE_FAST congruence transition in
    CONV_RULE
     (DEPTH_CONV RV32_NTT_CLOSED_NUM_CONV)
     (CONJ compact (CONJUNCT2 cb)) in
  let close_input n cb =
    let ntm = mk_small_numeral n in
    let pc =
      REWRITE_RULE[o_THM]
       (SPECL [`ival o (x:num->int32)`;ntm]
         RV32_NTT_INPUT_PARTIAL_CONG) in
    CONJ
     (RV32_INT_CONG_TRANS_RULE_FAST
       (CONJUNCT1 cb) pc)
     (CONJUNCT2 cb) in
  let close_stage p n cb =
    if p = 0 then
      compact_congbound
        0 0 (n / 4) (n mod 4) cb
    else if p = 1 then
      let q = n / 4 in
      compact_congbound
        1 (q / 16) (q mod 16) (n mod 4) cb
    else if p = 2 then
      let q = n / 4 in
      compact_congbound
        2 (q / 4) (q mod 4) (n mod 4) cb
    else if p = 3 then
      compact_congbound
        3 (n / 4) 0 (n mod 4) cb
    else
      failwith "close_stage" in
  let close_output n cb =
    let ntm = mk_small_numeral n in
    let bridge =
      SPECL [`ival o (x:num->int32)`;ntm]
       RV32_NTT_PARTIAL_1_CONG in
    RV32_INT_CONG_TRANS_RULE_FAST
      (CONJUNCT1 cb) bridge in
  let backend = {
    rv32_ntt_close_input = close_input;
    rv32_ntt_close_stage = close_stage;
    rv32_ntt_close_output = close_output
  } in
  let theorem =
    RV32_MLDSA_NTT_PHASE1234_PROVE backend in
  backend,theorem,Sys.time() -. start;;
