(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The hint loops of mld_pack_sig_h as clang 23 -O3 has inlined them into    *)
(* mldsa44_signature_internal: for row k, after the w1 unpack loop has put   *)
(* the coefficients of row k of w1 at F + 9056, a scalar loop over the 256   *)
(* coefficients j. With x = w0 - c s2 + c t0 (row k at F + 4192 + 1024 k),   *)
(* b the packed w1 and H = mld_polyvec_make_hint_88 x b, iteration j         *)
(* decides the hint bit of position p = 256 k + j; for a hint, if 80 are     *)
(* stored already the code leaves for join9 (the attempt is rejected), else  *)
(* it stores j at sig + 2336 + count (x27 = sig + 2336, the count in w8).    *)
(* As for the gcc code (utils/mldsa_native_hints.ml), the loop goes through  *)
(* glue_hint_steps 80 (256 (k + 1)) H - 256 k iterations: all 256 if there   *)
(* are at most 80 hints up to the end of row k, else up to the hint that     *)
(* does not fit.                                                             *)
(*                                                                           *)
(* The region lemma SI_HROW goes from the head of the loop (j = 0 in x9, the *)
(* count of the rows before in w8) to the exit of the loop or to join9. The  *)
(* rows have three shapes:                                                   *)
(*   row 0: w0 through sp + 4192 (computed in the body), one conditional     *)
(*     comparison chain (cmp a1, #0; ccmp a0, -gamma2; ccmp a0 + gamma2,     *)
(*     2 gamma2 + 1) and b.cc to the increment, so a hint in range and one   *)
(*     out of range take the same path;                                      *)
(*   rows 1 and 3: w0 through x16 and x18, a0 = -gamma2 and a1 <> 0 by       *)
(*     ccmp and cset, then b.cs (out of range) to the test of the count,     *)
(*     tbnz (no hint) to the increment and b to the test of the count;       *)
(*   row 2: w0 through x17, the same tests with the test of the count after  *)
(*     them and a jump back to the increment after the store.                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_pack.ml";;
needs "common/fips204/properties/mldsa_native_hints.ml";;

type hrow_inst =
  { hr_k : int; hr_head : string; hr_exit : string; hr_lo : int;
    hr_hi : int; hr_wreg : string };;

let SI_HROW_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;
let SI_HROW_L s = "mldsa44_signature_internal_" ^ s;;

(*** Substitute the tokens of a template string ***)

let hrow_subst toks s =
  let rec go s = function
      [] -> s
    | (t,v)::r ->
        let n = String.length t in
        let b = Buffer.create (String.length s) in
        let rec scan i =
          if i >= String.length s then ()
          else if i + n <= String.length s && String.sub s i n = t then
            (Buffer.add_string b v; scan (i + n))
          else (Buffer.add_char b (String.get s i); scan (i + 1)) in
        scan 0; go (Buffer.contents b) r in
  go s toks;;

let hrow_toks c =
  ["@MC@",SI_HROW_MC; "@HEAD@",c.hr_head; "@EXIT@",c.hr_exit;
   "@K@",string_of_int c.hr_k;
   "@W@",string_of_int (4192 + 1024 * c.hr_k);
   "@WB@",string_of_int (192 * c.hr_k); "@P0@",string_of_int (256 * c.hr_k);
   "@P1@",string_of_int (256 * (c.hr_k + 1));
   "@WREG@",(if c.hr_wreg = "" then ""
             else "read " ^ c.hr_wreg ^ " s = word_add fp (word " ^
                  string_of_int (4192 + 1024 * c.hr_k) ^ ") /\\");
   "@MODS@",(if c.hr_k = 0 then "X8; X9; X10; X11" else "X8; X9; X10; X11; X12")];;

let hrow_sub c s = hrow_subst (hrow_toks c) s;;

(* The events: the iterations, each by its path (a hint that fails, in range *)
(* or not; for the other positions and for the last, a hint in range or not, *)
(* or none), with nothing before or after the loop.                         *)

let SI_HROW_TEMPLATE c = parse_term(hrow_sub c
 "\\(x:num->int32) (b:num->byte) (sig:int64) (fp:int64) (pc:num).
   APPEND (f_ev_epi x b sig fp pc)
   (APPEND
    (ENUMERATEL (glue_hint_steps 80 @P1@ (mld_polyvec_make_hint_88 x b) - @P0@)
      (\\i. if glue_hint_fail 80 (mld_polyvec_make_hint_88 x b) (@P0@ + i)
           then if glue_hint_inr_88 (x(@P0@ + i))
                then f_ev_f2 x b sig fp pc i else f_ev_f1 x b sig fp pc i
           else if i < 255
           then if mld_polyvec_make_hint_88 x b (@P0@ + i)
                then if glue_hint_inr_88 (x(@P0@ + i))
                     then f_ev_m2 x b sig fp pc i else f_ev_m1 x b sig fp pc i
                else f_ev_m3 x b sig fp pc i
           else if mld_polyvec_make_hint_88 x b (@P0@ + i)
                then if glue_hint_inr_88 (x(@P0@ + i))
                     then f_ev_l2 x b sig fp pc i else f_ev_l1 x b sig fp pc i
                else f_ev_l3 x b sig fp pc i))
    (f_ev_pro x b sig fp pc)) :(uarch_event)list");;

let SI_HROW_TERM c = parse_term(hrow_sub c
 "exists f_events.
    forall e (x:num->int32) (b:num->byte) (sig:int64) (fp:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      mld_hint_count (mld_polyvec_make_hint_88 x b) @P0@ <= 80 /\\
      ALL (nonoverlapping (word_add sig (word 2336),80))
          [(word_add fp (word @W@),1024); (word_add fp (word 9056),1024);
           (word pc,libmldsa_size)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc) @MC@ /\\
                read PC s = word (pc + @HEAD@) /\\
                read SP s = fp /\\
                read X23 s = word_add fp (word 9056) /\\
                read X27 s = word_add sig (word 2336) /\\ @WREG@
                read X13 s = word 4294872064 /\\ read X14 s = word 190465 /\\
                read X15 s = word 95232 /\\
                read X9 s = word 0 /\\
                read X8 s = word (mld_hint_count (mld_polyvec_make_hint_88 x b) @P0@) /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (@W@ + 4 * i)))) s =
                                 x (@P0@ + i)) /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (9056 + 4 * i)))) s =
                                 mld_polyw1_unpack_88 (\\t. b (@WB@ + t)) i) /\\
                (!t. t < 80 ==> read (memory :> bytes8 (word_add sig (word (2336 + t)))) s =
                                mld_hint_index (mld_polyvec_make_hint_88 x b) @P0@ t) /\\
                read events s = e)
           (\\s. read PC s =
                (if mld_hint_count (mld_polyvec_make_hint_88 x b) @P1@ <= 80
                 then word (pc + @EXIT@)
                 else word (pc + mldsa44_signature_internal_join9)) /\\
                (mld_hint_count (mld_polyvec_make_hint_88 x b) @P1@ <= 80
                 ==> read X8 s = word (mld_hint_count (mld_polyvec_make_hint_88 x b) @P1@) /\\
                     (!t. t < 80 ==> read (memory :> bytes8 (word_add sig (word (2336 + t)))) s =
                                     mld_hint_index (mld_polyvec_make_hint_88 x b) @P1@ t)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events x b sig fp pc /\\
                   memaccess_inbounds e2
                    [word_add fp (word @W@),1024; word_add fp (word 9056),1024;
                     word_add sig (word 2336),80]
                    [word_add sig (word 2336),80]))
           (MAYCHANGE [PC; @MODS@] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add sig (word 2336),80)])");;

(* The invariant at the head for iteration i: the frame, and, if the code    *)
(* goes through i or there are at most 80 hints, the index, the count and    *)
(* the hint bytes so far.                                                    *)

let SI_HROW_INV c = parse_term(hrow_sub c
 "\\i s. read SP s = fp /\\
        read X23 s = word_add fp (word 9056) /\\
        read X27 s = word_add sig (word 2336) /\\ @WREG@
        read X13 s = word 4294872064 /\\ read X14 s = word 190465 /\\
        read X15 s = word 95232 /\\
        (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (@W@ + 4 * i)))) s =
                         x (@P0@ + i)) /\\
        (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (9056 + 4 * i)))) s =
                         mld_polyw1_unpack_88 (\\t. b (@WB@ + t)) i) /\\
        (i < glue_hint_steps 80 @P1@ (mld_polyvec_make_hint_88 x b) - @P0@ \\/
         mld_hint_count (mld_polyvec_make_hint_88 x b) @P1@ <= 80
         ==> read X9 s = word i /\\
             read X8 s = word (mld_hint_count (mld_polyvec_make_hint_88 x b) (@P0@ + i)) /\\
             (!t. t < 80 ==> read (memory :> bytes8 (word_add sig (word (2336 + t)))) s =
                             mld_hint_index (mld_polyvec_make_hint_88 x b) (@P0@ + i) t))");;

let SI_HROW_EXEC c =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(layout "mldsa44_signature_internal" + c.hr_lo,
     layout "mldsa44_signature_internal" + c.hr_hi)];;

let SI_HROW_INSTS =
  [{hr_k = 0; hr_head = SI_HROW_L "loop46"; hr_exit = SI_HROW_L "loop46_exit2";
    hr_lo = 0x4f14; hr_hi = 0x4f54; hr_wreg = ""};
   {hr_k = 1; hr_head = SI_HROW_L "loop48"; hr_exit = SI_HROW_L "loop48_exit2";
    hr_lo = 0x5158; hr_hi = 0x519c; hr_wreg = "X16"};
   {hr_k = 2; hr_head = SI_HROW_L "loop50"; hr_exit = SI_HROW_L "loop50_exit2";
    hr_lo = 0x52cc; hr_hi = 0x5310; hr_wreg = "X17"};
   {hr_k = 3; hr_head = SI_HROW_L "loop52"; hr_exit = SI_HROW_L "loop52_exit2";
    hr_lo = 0x5440; hr_hi = 0x5484; hr_wreg = "X18"}];;

(* ------------------------------------------------------------------------- *)
(* Arithmetic (as x86's inline_hrow.ml).                                     *)
(* ------------------------------------------------------------------------- *)

(*** The row has at least one iteration if the count before it fits ***)

let SI_HROW_STEPS_POS = prove
 (`!h omega p0 p1. p0 < p1 /\ mld_hint_count h p0 <= omega
                   ==> p0 < glue_hint_steps omega p1 h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[glue_hint_steps] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`h:num->bool`; `omega:num`; `p1:num`] GLUE_HINT_FAIL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?p. glue_hint_fail omega (h:num->bool) p` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN BETA_TAC THEN
  ABBREV_TAC `m = minimal p. glue_hint_fail omega (h:num->bool) p` THEN
  REWRITE_TAC[glue_hint_fail] THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `p0 < m + 1 <=> ~(m < p0)`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`h:num->bool`; `m + 1`; `p0:num`] MLD_HINT_COUNT_MONO) THEN
  ASM_REWRITE_TAC[MLD_HINT_COUNT_ADD1] THEN ASM_ARITH_TAC);;

let SI_HROW_DIVMOD = prove
 (`!k i. i < 256 ==> (256 * k + i) DIV 256 = k /\ (256 * k + i) MOD 256 = i`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `i:num`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `k:num`] THEN ASM_ARITH_TAC);;

(*** The hint bit of position 256 k + i from the coefficients ***)

let SI_HROW_UNF = prove
 (`!x b k i. i < 256
     ==> (mld_polyvec_make_hint_88 x b (256 * k + i) <=>
          mld_make_hint_88 (x (256 * k + i))
           (mld_polyw1_unpack_88 (\t. b (192 * k + t)) i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GLUE_POLYVEC_HINT_88] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SI_HROW_DIVMOD th]));;

(*** The carry of cmp v, #190465 (or of ccmp): v >= 2 gamma2 + 1 ***)

let SI_HROW_CF = prove
 (`!v:int32. (&(val v) - &190465:int = &(val(word_sub v (word 190465)))) <=>
             ~(val v <= 190464)`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `v:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[INT_ARITH `&a - &c:int = &b <=> &a:int = &b + &c`;
                INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC]);;

(*** Row 0: the carry after cmp a1, #0; ccmp a0, -gamma2, #0, ne;       ***)
(*** ccmp a0 + gamma2, #190465, #2, ne is the hint bit                  ***)

let SI_HROW_C0 = prove
 (`!a0 a1:int32.
     (if ~(~(a1 = word 0) /\ a0 = word 4294872064)
      then &(val (word_add a0 (word 95232))) - &190465:int =
           &(val (word_sub (word_add a0 (word 95232)) (word 190465)))
      else T) <=> mld_make_hint_88 a0 a1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SI_HROW_CF; GLUE_INR_88] THEN
  ASM_CASES_TAC `glue_hint_inr_88 a0` THEN
  ASM_SIMP_TAC[GLUE_HINT_INR_88; GLUE_HINT_OUT_88] THEN
  ASM_CASES_TAC `~(a1:int32 = word 0) /\ a0:int32 = word 4294872064` THEN
  ASM_REWRITE_TAC[]);;

(*** The count and the index after an iteration ***)

let SI_HROW_INC32 = prove
 (`!n. n < 80
       ==> word_zx (word_add (word_zx (word n:int64):int32) (word 1)):int64 =
           word (n + 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 18446744073709551616 = n /\ n MOD 4294967296 = n /\
                (n + 1) MOD 4294967296 = n + 1 /\
                (n + 1) MOD 18446744073709551616 = n + 1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let SI_HROW_BYTE = prove
 (`!k i. i < 256
         ==> word_zx (word_zx (word i:int64):int32):byte =
             word ((256 * k + i) MOD 256)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SI_HROW_DIVMOD th]) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `i MOD 18446744073709551616 = i /\ i MOD 4294967296 = i /\
                i MOD 256 = i` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(*** Rows 1 to 3: tbnz on the result of cset eq after cmp a0, -gamma2 and  ***)
(*** ccmp a1, #0, #4, eq (taken if there is no hint, for a0 in range)      ***)

let SI_HROW_BIT0 = prove
 (`!p. bit 0 (if p then word 0 else word 1:N word) <=> ~p`,
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BIT_WORD; EXP; DIV_1; ARITH] THEN
  REWRITE_TAC[LE_1; DIMINDEX_GE_1; ARITH_RULE `0 < n <=> 1 <= n`]);;

let SI_HROW_TBNZ = prove
 (`!a0 a1:int32.
     glue_hint_inr_88 a0
     ==> ((if val (word_sub a0 (word 4294872064)) = 0
           then val (word_sub a1 (word 0)) = 0 else T) <=>
          ~mld_make_hint_88 a0 a1)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GLUE_HINT_INR_88] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; WORD_SUB_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The simulation of an iteration: one instruction at a time from the head,  *)
(* splitting the goal at each conditional branch on the predicate it tests   *)
(* (SI_HROW_DECIDE_TAC), up to the head, the exit of the loop or join9,     *)
(* where SI_HROW_FINAL_TAC proves the invariant for i + 1 and the events.    *)
(* ------------------------------------------------------------------------- *)

let SI_HROW_TM k s = subst [mk_small_numeral(256 * k),`P0:num`;
                            mk_small_numeral(256 * (k + 1)),`P1:num`] s;;
let SI_HROW_CNT k = SI_HROW_TM k
  `mld_hint_count (mld_polyvec_make_hint_88 x b) (P0 + i)`;;
let SI_HROW_FAIL k = SI_HROW_TM k
  `glue_hint_fail 80 (mld_polyvec_make_hint_88 x b) (P0 + i)`;;
let SI_HROW_H k = SI_HROW_TM k `mld_polyvec_make_hint_88 x b (P0 + i)`;;
let SI_HROW_INR k = SI_HROW_TM k `glue_hint_inr_88 (x (P0 + i))`;;
let SI_HROW_STEPS k = SI_HROW_TM k
  `glue_hint_steps 80 P1 (mld_polyvec_make_hint_88 x b)`;;

let hrow_current_pc (asl,w) =
  let s = rand w in
  rhs(concl(snd(find (fun (_,th) ->
    try lhs(concl th) = mk_comb(`read PC`,s) with Failure _ -> false) asl)));;

(*** Split on p, deciding the branch and the events in each case ***)

let SI_HROW_CASES_TAC (p:term) =
  let pcev th =
    let c = concl th in
    is_eq c &&
    (can (term_match [] `read PC s`) (lhs c) ||
     can (term_match [] `read events s`) (lhs c)) in
  ASM_CASES_TAC p THEN
  POP_ASSUM(fun cth ->
    let eq = if is_neg(concl cth) then EQF_INTRO cth else EQT_INTRO cth in
    RULE_ASSUM_TAC(fun th -> if pcev th then REWRITE_RULE[eq] th else th) THEN
    ASSUME_TAC cth);;

(*** On the path of a hint that fits: the count below 80, its forms as the  ***)
(*** address of the store, and the other hint bytes, stated for state s     ***)

let SI_HROW_CNT_FACTS_TAC k (s:term) =
  let cnt = SI_HROW_CNT k in
  let lt80 = mk_binop `(<):num->num->bool` cnt `80` in
  let lt80_tac = FIRST_ASSUM(MP_TAC o check (fun th -> concl th = lt80)) THEN
                 ARITH_TAC in
  SUBGOAL_THEN lt80 ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> concl th = mk_neg(SI_HROW_FAIL k))) THEN
    REWRITE_TAC[glue_hint_fail] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      concl th = mk_binop `(<=):num->num->bool` cnt `80`)) THEN
    ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC cnt VAL_WORD_ZX_UXTW) THEN ANTS_TAC THENL [lt80_tac; STRIP_TAC] THEN
  MP_TAC(SPEC cnt WORD_ZX_ZX_SMALL) THEN ANTS_TAC THENL [lt80_tac; DISCH_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,cnt)),cnt))
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN lt80_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN (vsubst [cnt,`c:num`; s,`s:armstate`] (SI_HROW_TM k
   `!t. t < 80 /\ ~(t = c)
        ==> read(memory :> bytes8(word_add sig (word(2336 + t)))) s =
            mld_hint_index (mld_polyvec_make_hint_88 x b) (P0 + i) t`))
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The hint bit when a0 is out of range ***)

let SI_HROW_HINT_OUT_TAC k =
  let th = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
             (SPECL [`x:num->int32`; `b:num->byte`; mk_small_numeral k; `i:num`]
                    SI_HROW_UNF) in
  SUBGOAL_THEN (SI_HROW_H k) ASSUME_TAC THENL
   [REWRITE_TAC[MP th (ASSUME `i < 256`)] THEN MATCH_MP_TAC GLUE_HINT_OUT_88 THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

let SI_HROW_DECIDE_TAC k (asl,w) =
  let th = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
             (SPECL [`x:num->int32`; `b:num->byte`; mk_small_numeral k; `i:num`]
                    SI_HROW_UNF) in
  let uf = MP th (ASSUME `i < 256`) in
  let s = rand w in
  let pcfact th = let c = concl th in
    is_eq c && (lhs c = mk_comb(`read PC`,s) || lhs c = mk_comb(`read events`,s)) in
  let norm = REWRITE_RULE[SI_HROW_CF; GLUE_INR_88] o REWRITE_RULE[GSYM uf] o
             REWRITE_RULE[SI_HROW_C0] o
             REWRITE_RULE[WORD_ZX_ZX_32_64_32; GLUE_CCMP_EQ] in
  (RULE_ASSUM_TAC(fun th -> if pcfact th then norm th else th) THEN
   W(fun (asl,w) ->
     let c0,_ = dest_cond(hrow_current_pc (asl,w)) in
     let c = if is_neg c0 then rand c0 else c0 in
     let occurs t = can (find_term ((=) t)) c in
     let canon eq =
       RULE_ASSUM_TAC(fun th -> if pcfact th then REWRITE_RULE[eq] th else th) in
     if c = SI_HROW_H k then SI_HROW_CASES_TAC c
     else if c = SI_HROW_INR k then
       SI_HROW_CASES_TAC c THENL [ALL_TAC; SI_HROW_HINT_OUT_TAC k]
     else if occurs `word 18446744073709551361:int64` then
       canon(MP (SPEC `i:num` GLUE_J_TEST) (ASSUME `i < 256`)) THEN
       SI_HROW_CASES_TAC `i < 255`
     else if occurs (SI_HROW_CNT k) then
       let fl = SI_HROW_FAIL k in
       SUBGOAL_THEN (mk_iff(c,fl)) canon THENL
        [REWRITE_TAC[glue_hint_fail; ASSUME (SI_HROW_H k)] THEN
         MATCH_MP_TAC GLUE_W32_EQ THEN CONV_TAC NUM_REDUCE_CONV THEN
         FIRST_ASSUM(MP_TAC o check (fun th ->
           concl th = mk_binop `(<=):num->num->bool` (SI_HROW_CNT k) `80`)) THEN
         ARITH_TAC;
         ALL_TAC] THEN
       SI_HROW_CASES_TAC fl THENL [ALL_TAC; SI_HROW_CNT_FACTS_TAC k s]
     else if is_comb c && rator(rator c) = `bit:num->int32->bool` ||
             is_comb c && rator(rator c) = `bit:num->int64->bool` then
       let h = SI_HROW_H k in
       SUBGOAL_THEN (mk_iff(c,mk_neg h)) canon THENL
        [REWRITE_TAC[SI_HROW_BIT0; NOT_CLAUSES; uf] THEN
         MATCH_MP_TAC SI_HROW_TBNZ THEN FIRST_ASSUM ACCEPT_TAC;
         ALL_TAC] THEN
       SI_HROW_CASES_TAC h
     else failwith ("SI_HROW_DECIDE_TAC: " ^ string_of_term c))) (asl,w);;

(*** The next position (GLUE_HINT_NEXT): the number of iterations and the ***)
(*** count of the row, in the cases of a failure, of another position and ***)
(*** of the last                                                         ***)

let SI_HROW_IDX_ARITH_TAC =
  MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`i < 255`; `~(i < 255)`; `i < 256`] THEN
  ARITH_TAC;;

let SI_HROW_NOFAIL_TAC =
  FIRST_ASSUM ACCEPT_TAC ORELSE (REWRITE_TAC[glue_hint_fail] THEN ASM_REWRITE_TAC[]);;

let SI_HROW_NEXT_TAC k =
  let p0 = 256 * k and p1 = 256 * (k + 1) in
  let p = mk_binop `(+):num->num->num` (mk_small_numeral p0) `i:num` in
  MP_TAC(SPECL [`mld_polyvec_make_hint_88 x b`; `80`; mk_small_numeral p1; p]
               GLUE_HINT_NEXT) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let fl = SI_HROW_FAIL k in
    let has t = exists (fun (_,th) -> concl th = t) asl in
    if has fl then DISCH_THEN(MP_TAC o C MP (ASSUME fl) o CONJUNCT1) THEN STRIP_TAC
    else
    (if has (mk_neg fl) then ALL_TAC
     else SUBGOAL_THEN (mk_neg fl) ASSUME_TAC THENL [SI_HROW_NOFAIL_TAC; ALL_TAC]) THEN
    if has `~(i < 255)` then
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [SI_HROW_NOFAIL_TAC; SI_HROW_IDX_ARITH_TAC];
                      STRIP_TAC]
    else
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [SI_HROW_NOFAIL_TAC; SI_HROW_IDX_ARITH_TAC];
                      STRIP_TAC]);;

let SI_HROW_STEPS_LT_TAC k =
  let tm = SI_HROW_TM k
   `i + 1 < glue_hint_steps 80 P1 (mld_polyvec_make_hint_88 x b) - P0 <=>
    (P0 + i) + 1 < glue_hint_steps 80 P1 (mld_polyvec_make_hint_88 x b)` in
  SUBGOAL_THEN tm SUBST1_TAC THENL [ARITH_TAC; ALL_TAC];;

let SI_HROW_BYTES_TAC k =
  let bth = MP (SPECL [mk_small_numeral k; `i:num`] SI_HROW_BYTE) (ASSUME `i < 256`) in
  let bth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) bth in
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[MLD_HINT_INDEX_ADD1] THEN
  ASM_REWRITE_TAC[] THEN
  TRY(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN ASM_REWRITE_TAC[bth] THEN
    NO_TAC;
    ALL_TAC]) THEN
  TRY(FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let SI_HROW_EVENTS_TAC k =
  let inr = SI_HROW_INR k in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
    if free_in inr w then ASM_CASES_TAC inr THEN ASM_REWRITE_TAC[]
    else ALL_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let SI_HROW_REGS_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD; MULT_CLAUSES]) THEN
  TRY(FIRST_ASSUM(fun th ->
    if is_comb(concl th) && can (term_match [] `mld_hint_count h p < 80`) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SI_HROW_INC32 th]) else NO_TAC));;

let SI_HROW_FINAL_TAC k =
  SI_HROW_REGS_TAC THEN
  SI_HROW_NEXT_TAC k THEN ENSURES_FINAL_STATE_TAC THEN
  SI_HROW_STEPS_LT_TAC k THEN
  ASM_REWRITE_TAC[GSYM ADD_ASSOC; LT_REFL] THEN
  REWRITE_TAC[ADD_ASSOC; MLD_HINT_COUNT_ADD1] THEN ASM_REWRITE_TAC[ADD_0] THEN
  REPEAT CONJ_TAC THEN
  TRY(SI_HROW_BYTES_TAC k THEN NO_TAC) THEN
  SI_HROW_EVENTS_TAC k;;

let rec SI_HROW_RUN_TAC c ex n (asl,w) =
  let k = c.hr_k in
  let pct = hrow_current_pc (asl,w) in
  let tgt l = mk_comb(`word:num->int64`,
                mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral(layout l))) in
  if n > 1 && mem pct (map tgt [c.hr_head; c.hr_exit; SI_HROW_L "join9"]) then
    SI_HROW_FINAL_TAC k (asl,w)
  else if is_cond pct then
    (SI_HROW_DECIDE_TAC k THEN SI_HROW_RUN_TAC c ex n) (asl,w)
  else (ARM_STEPS_TAC ex [n] THEN SI_HROW_RUN_TAC c ex (n + 1)) (asl,w);;

(*** An iteration: the facts for position i, then the simulation ***)

let SI_HROW_SPEC_TAC pat =
  FIRST_ASSUM(fun th -> if is_forall(concl th) && can (term_match [] pat) (concl th) then
    MP_TAC(SPEC `i:num` th) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC]
    else NO_TAC);;

let SI_HROW_BODY_TAC c ex =
  let k = c.hr_k in
  let p0 = mk_small_numeral(256 * k) and w = 4192 + 1024 * k in
  let steps = SI_HROW_STEPS k in
  let n = mk_binop `(-):num->num->num` steps p0 in
  let lt_n = mk_binop `(<):num->num->bool` `i:num` n in
  let p_lt = mk_binop `(<):num->num->bool` (mk_binop `(+):num->num->num` p0 `i:num`) steps in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN p_lt ASSUME_TAC THENL
   [UNDISCH_TAC lt_n THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i < 256` ASSUME_TAC THENL
   [UNDISCH_TAC p_lt THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      concl th = mk_binop `(<=):num->num->bool` steps (mk_small_numeral(256 * (k + 1))))) THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<=):num->num->bool` (SI_HROW_CNT k) `80`) ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match [] `!p. p < n ==> mld_hint_count h p <= 80`) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME lt_n] THEN
  FULL_INIT_TAC THEN
  SI_HROW_SPEC_TAC (parse_term(Printf.sprintf
    "!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s0 = y i" w)) THEN
  SI_HROW_SPEC_TAC
    `!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (9056 + 4 * i)))) s0 = y i` THEN
  VAL_INT64_TAC `i:num` THEN
  SI_HROW_RUN_TAC c ex 1;;

(*** After the loop: nothing to do, at the exit or at join9 ***)

(*** The events when the functions of the template are already known (the ***)
(*** second case of the exit): e2 is the term itself                       ***)

let SI_CLOSED_E2_TAC =
  W(fun (asl,w) ->
    let _,bod = dest_exists w in
    match conjuncts bod with
      [_; eq; _] -> EXISTS_TAC (rhs eq)
    | _ -> failwith "SI_CLOSED_E2_TAC") THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[APPEND] THEN
  ASM_REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(fun th ->
        if is_eq(concl th) && is_var(lhs(concl th)) && name_of(lhs(concl th)) = "e2"
        then SUBST_ALL_TAC th else NO_TAC) THEN
      ASM_REWRITE_TAC[]);;

let SI_HROW_EXIT_TAC k =
  let cntok = SI_HROW_TM k `mld_hint_count (mld_polyvec_make_hint_88 x b) P1 <= 80` in
  let steps_eq = SI_HROW_TM k
    `glue_hint_steps 80 P1 (mld_polyvec_make_hint_88 x b) = P1` in
  let fin = FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
            (DISCHARGE_SAFETY_PROPERTY_TAC ORELSE SI_CLOSED_E2_TAC) in
  ASM_CASES_TAC cntok THENL
   [SUBGOAL_THEN steps_eq SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_imp(concl th) && lhand(concl th) = cntok)) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN fin;
    ASM_REWRITE_TAC[] THEN fin];;

let SI_HROW_PROVE c =
  let ex = SI_HROW_EXEC c and k = c.hr_k in
  let p0 = mk_small_numeral(256 * k) and p1 = mk_small_numeral(256 * (k + 1)) in
  let pcn l = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral(layout l)) in
  prove(SI_HROW_TERM c,
  CONCRETIZE_F_EVENTS_TAC (SI_HROW_TEMPLATE c) THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `x:num->int32`; `b:num->byte`;
                       `sig:int64`; `fp:int64`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst ex] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`mld_polyvec_make_hint_88 x b`; `80`; p1] GLUE_HINT_STEPS) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (mk_binop `(-):num->num->num` (SI_HROW_STEPS k) p0)
   (pcn c.hr_head)
   (mk_cond(SI_HROW_TM k `mld_hint_count (mld_polyvec_make_hint_88 x b) P1 <= 80`,
            pcn c.hr_exit, pcn (SI_HROW_L "join9")))
   (SI_HROW_INV c) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`mld_polyvec_make_hint_88 x b`; `80`; p0; p1] SI_HROW_STEPS_POS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ARITH_TAC];
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    SI_HROW_BODY_TAC c ex;
    SI_HROW_EXIT_TAC k]);;
