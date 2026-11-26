(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The hints of row i of mldsa65_verify_internal and mldsa87_verify_internal *)
(* (omega = 55 and 75, K = 6 and 8), as clang 23 -O3 has inlined            *)
(* mld_unpack_hints into the row loop: the same code as for ML-DSA-44        *)
(* (inline_sign_hints44.ml) with omega and K as parameters, the row index    *)
(* in x26 rather than on the stack, and without the constants of use_hint,   *)
(* which this code sets after join7. From loop<n>_exit to join7 when the     *)
(* hints of the row are well formed, join3 with -6 in w27 otherwise: the     *)
(* checks of the count nw = hb[omega + i] against omega and against the      *)
(* count st of the rows before, the memset of h at F + 352, the first hint,  *)
(* the loop over the others (INLINE_HUNPK_LOOP) and, for the last row, the   *)
(* check that the unused bytes are zero (INLINE_ZCHKK_LOOP). The result is   *)
(* mld_unpack_hints omega hb i in h when mld_unpack_hints_ret omega K hb i   *)
(* = 0.                                                                       *)
(*                                                                           *)
(* The terms of the tactics are written with the variables OM (omega), KK    *)
(* (K), K1 (K - 1), OK1 (omega - 1) and HB (omega + K), which hk_inst         *)
(* replaces by the numerals of the instance, as glue_suh_inst does for the   *)
(* gcc builds (utils/mldsa_native_hints.ml).                                 *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_hints_tac.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;

type hk_inst =
  { hk_fn : string; hk_om : int; hk_k : int; hk_entry : string;
    hk_zloop : string; hk_hloop : string };;

let hk_inst p tm =
  let n = mk_small_numeral in
  vsubst [n p.hk_om,`OM:num`; n (p.hk_om - 1),`OK1:num`; n p.hk_k,`KK:num`;
          n (p.hk_k - 1),`K1:num`; n (p.hk_om + p.hk_k),`HB:num`;
          n (p.hk_om + 1),`OP1:num`] tm;;

let hk_lbl p l = p.hk_fn ^ "_" ^ l;;

(* ------------------------------------------------------------------------- *)
(* The check that the unused bytes P[n .. omega - 1] are zero (the loop of   *)
(* shape 47 with the bound omega): the definitions and lemmas of             *)
(* inline_sign_hints.ml with omega as a parameter om.                        *)
(* ------------------------------------------------------------------------- *)

let INLINE_ZRUNK = new_definition
 `inline_zrunk om (b:num->byte) n =
    minimal j. n <= j /\ (j = om \/ ~(b j = word 0))`;;

let INLINE_ZSTEPSK = new_definition
 `inline_zstepsk om (b:num->byte) n =
    if inline_zrunk om b n = om then om - n else inline_zrunk om b n - n + 1`;;

let INLINE_ZRUNK_FACTS = prove
 (`!om (b:num->byte) n.
     n < om
     ==> n <= inline_zrunk om b n /\ inline_zrunk om b n <= om /\
         (inline_zrunk om b n = om \/ ~(b(inline_zrunk om b n) = word 0)) /\
         (!j. n <= j /\ j < inline_zrunk om b n ==> b j = word 0) /\
         ((!j. n <= j /\ j < om ==> b j = word 0) <=> inline_zrunk om b n = om)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?j. n <= j /\ (j = om \/ ~((b:num->byte) j = word 0))`
   (fun th -> MP_TAC(MATCH_MP (fst(EQ_IMP_RULE(REWRITE_RULE[GSYM INLINE_ZRUNK] (BETA_RULE
     (SPEC `\j. n <= j /\ (j = om \/ ~((b:num->byte) j = word 0))` MINIMAL))))) th)) THENL
   [EXISTS_TAC `om:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = inline_zrunk om (b:num->byte) n` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `m <= om` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `om:num` o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. n <= j /\ j < m ==> (b:num->byte) j = word 0` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(j:num = om)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th -> is_forall(concl th) &&
      free_in `om:num` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check(fun th -> is_forall(concl th) &&
      free_in `m:num` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let INLINE_ZFACTSK_TAC =
  REWRITE_TAC[INLINE_ZSTEPSK] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`om:num`; `b:num->byte`;`n:num`] INLINE_ZRUNK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = inline_zrunk om (b:num->byte) n` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `m:num = om` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[];;

let INLINE_ZSTEPSK_POS = prove
 (`!om (b:num->byte) n. n < om ==> 0 < inline_zstepsk om b n`,
  REPEAT GEN_TAC THEN INLINE_ZFACTSK_TAC THEN ASM_ARITH_TAC);;

let INLINE_ZSTEPSK_LT = prove
 (`!om (b:num->byte) n p. n < om /\ p < inline_zstepsk om b n
        ==> n + p < om /\ n + p <= inline_zrunk om b n`,
  REPEAT GEN_TAC THEN INLINE_ZFACTSK_TAC THEN ASM_ARITH_TAC);;

let INLINE_ZSTEPSK_MID = prove
 (`!om (b:num->byte) n p. n < om /\ p + 1 < inline_zstepsk om b n
        ==> b(n + p) = word 0 /\ n + p + 1 < om`,
  REPEAT GEN_TAC THEN INLINE_ZFACTSK_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + p` o
    check (fun th -> is_forall(concl th))) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let INLINE_ZSTEPSK_OK = prove
 (`!om (b:num->byte) n p. n < om /\ p + 1 = inline_zstepsk om b n /\
                       (!j. n <= j /\ j < om ==> b j = word 0)
        ==> b(n + p) = word 0 /\ n + p + 1 = om`,
  REPEAT GEN_TAC THEN INLINE_ZFACTSK_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + p` o
    check (fun th -> is_forall(concl th))) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let INLINE_ZSTEPSK_FAIL = prove
 (`!om (b:num->byte) n p. n < om /\ p + 1 = inline_zstepsk om b n /\
                       ~(!j. n <= j /\ j < om ==> b j = word 0)
        ==> ~(b(n + p) = word 0)`,
  REPEAT GEN_TAC THEN INLINE_ZFACTSK_TAC THEN
  (SUBGOAL_THEN `n + p = m` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_MESON_TAC[]);;

let INLINE_ZRUNK_OK = prove
 (`!om (b:num->byte) n. n < om /\ (!j. n <= j /\ j < om ==> b j = word 0)
        ==> inline_zrunk om b n = om`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`om:num`; `b:num->byte`;`n:num`] INLINE_ZRUNK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let INLINE_ZRUNK_FAIL = prove
 (`!om (b:num->byte) n p. n < om /\ p + 1 = inline_zstepsk om b n /\
                       ~(!j. n <= j /\ j < om ==> b j = word 0)
        ==> inline_zrunk om b n = n + p`,
  REPEAT GEN_TAC THEN INLINE_ZFACTSK_TAC THEN ASM_ARITH_TAC);;

(*** The loop test of the instance: add 1 and compare with omega ***)

let INLINE_ZBK_PC p =
  let neg = mk_numeral(Num.num_of_string "18446744073709551616" -/
                       num (p.hk_om - 1)) in
  let h tm = vsubst [neg,`NEG:num`] (hk_inst p tm) in
  prove(h `!k. k < OM ==> (val(word_add (word k:int64) (word NEG)) = 0 <=> k = OK1)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[VAL_EQ_0] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC (h `word_add (word k:int64) (word NEG) = word 0`) THEN
    REWRITE_TAC[GSYM WORD_ADD; GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; VAL_WORD_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_CASES_TAC (h `(k:num) = OK1`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [h `k + NEG`; `18446744073709551616`] MOD_LT) THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_REDUCE_CONV]);;

(*** The statement ***)

let INLINE_ZCHKK_LOOP_TERM p mc loop exit fail (rs:string list) =
  let r k = List.nth rs k in
  hk_inst p (parse_term(Printf.sprintf
   "exists f_events.
      forall e sg (b:num->byte) n pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        n < OM
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = sg /\\ read %s s = word n /\\
                  (!j. j < OM
                       ==> read(memory :> bytes8(word_add sg (word j))) s =
                           b j) /\\
                  read events s = e)
             (\\s. read PC s = word (if (!j. n <= j /\\ j < OM ==> b j = word 0)
                                    then pc + %s else pc + %s) /\\
                  ((!j. n <= j /\\ j < OM ==> b j = word 0)
                   ==> read %s s = word OM) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events b n sg pc /\\
                     memaccess_inbounds e2 [sg,OM] []))
             (MAYCHANGE [PC; %s; %s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events])"
   mc loop (r 1) (r 2) exit fail (r 2) (r 0) (r 2)));;

let INLINE_ZTPLK p = hk_inst p
 `\(b:num->byte) (n:num) (sg:int64) (pc:num).
   APPEND ([]:(uarch_event)list)
    (APPEND (ENUMERATEL (inline_zstepsk OM b n)
       (\p. if p + 1 < inline_zstepsk OM b n then f_ev_a b n sg pc p
            else if (!j. n <= j /\ j < OM ==> b j = word 0)
                 then f_ev_ok b n sg pc p else f_ev_fail b n sg pc p))
      ([]:(uarch_event)list))`;;

let INLINE_ZSTARTK_TAC p exec inv =
  CONCRETIZE_F_EVENTS_TAC (INLINE_ZTPLK p) THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sg:int64`; `b:num->byte`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GLUE_EVENTS_WHILE_TAC (hk_inst p `inline_zstepsk OM (b:num->byte) n`) inv THEN
  REPEAT CONJ_TAC;;

let INLINE_ZINITK_TAC p =
  let om = mk_small_numeral p.hk_om in
  MP_TAC(SPECL [om; `b:num->byte`;`n:num`] INLINE_ZSTEPSK_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [om; `b:num->byte`;`n:num`] INLINE_ZRUNK_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_0; ENUMERATEL; APPEND] THEN
  ASM_SIMP_TAC[INLINE_MIN_LE_L] THEN
  EXISTS_TAC `[]:(uarch_event)list` THEN REWRITE_TAC[APPEND_NIL;APPEND] THEN
  DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC;;

let INLINE_ZBODY_PREPK_TAC p =
  let om = mk_small_numeral p.hk_om in
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  MP_TAC(SPECL [om; `b:num->byte`;`n:num`;`i:num`] INLINE_ZSTEPSK_LT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (SUBGOAL_THEN (hk_inst p `MIN (n + i) (inline_zrunk OM b n) = n + i`)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [ASM_SIMP_TAC[INLINE_MIN_LE_L]; ALL_TAC]) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) &&
       can (find_term (fun t -> try fst(dest_const t) = "bytes8" with Failure _ -> false)) (concl th)
    then MP_TAC(SPEC `n + i` th) THEN (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC])
    else NO_TAC);;

let INLINE_ZSTEP_EQK_TAC p =
  SUBGOAL_THEN (hk_inst p `i + 1 = inline_zstepsk OM b n`) ASSUME_TAC THENL
   [INLINE_ARITH_WITH (map (hk_inst p) [`i < inline_zstepsk OM b n`;
                                        `~(i + 1 < inline_zstepsk OM b n)`]);
    ALL_TAC];;

let INLINE_ZALLZ p = hk_inst p `forall j. n <= j /\ j < OM ==> (b:num->byte) j = word 0`;;

let INLINE_ZBODY_BK_TAC p exec =
  let om = mk_small_numeral p.hk_om and h = hk_inst p in
  INLINE_ZSTEP_EQK_TAC p THEN
  STRIP_ASSUME_TAC(MATCH_MP (SPECL [om; `b:num->byte`;`n:num`;`i:num`] INLINE_ZSTEPSK_OK)
    (end_itlist CONJ (map ASSUME [h `n < OM`; h `i + 1 = inline_zstepsk OM b n`;
       INLINE_ZALLZ p]))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = h `i + 1 = inline_zstepsk OM b n`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(b:num->byte) (n + i) = word 0`]) THEN
  ASSUME_TAC(MATCH_MP (SPECL [om; `b:num->byte`;`n:num`] INLINE_ZRUNK_OK)
    (CONJ (ASSUME (h `n < OM`)) (ASSUME (INLINE_ZALLZ p)))) THEN
  ARM_STEPS_TAC exec (1--5) THEN
  MP_TAC(SPEC `n + i` (INLINE_ZBK_PC p)) THEN
  (ANTS_TAC THENL [INLINE_ARITH_WITH [h `n + i < OM`]; DISCH_TAC]) THEN
  SUBGOAL_THEN (h `(n + i = OK1) <=> T`) ASSUME_TAC THENL
   [REWRITE_TAC[] THEN INLINE_ARITH_WITH [h `n + i + 1 = OM`]; ALL_TAC] THEN
  SUBGOAL_THEN (h `MIN (n + i + 1) (inline_zrunk OM b n) = OM`) ASSUME_TAC THENL
   [INLINE_ARITH_WITH [h `n + i + 1 = OM`; h `inline_zrunk OM b n = OM`]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC;;

let INLINE_ZBODY_CK_TAC p exec =
  let om = mk_small_numeral p.hk_om and h = hk_inst p in
  INLINE_ZSTEP_EQK_TAC p THEN
  ASSUME_TAC(MATCH_MP (SPECL [om; `b:num->byte`;`n:num`;`i:num`] INLINE_ZSTEPSK_FAIL)
    (end_itlist CONJ (map ASSUME [h `n < OM`; h `i + 1 = inline_zstepsk OM b n`;
       mk_neg(INLINE_ZALLZ p)]))) THEN
  ASSUME_TAC(MATCH_MP (SPECL [om; `b:num->byte`;`n:num`;`i:num`] INLINE_ZRUNK_FAIL)
    (end_itlist CONJ (map ASSUME [h `n < OM`; h `i + 1 = inline_zstepsk OM b n`;
       mk_neg(INLINE_ZALLZ p)]))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = h `i + 1 = inline_zstepsk OM b n`)) THEN
  ARM_STEPS_TAC exec (1--2) THEN
  MP_TAC(SPEC `(b:num->byte) (n + i)` INLINE_ZB_EQ0) THEN
  (ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  SUBGOAL_THEN (h `MIN (n + i + 1) (inline_zrunk OM b n) = n + i`) ASSUME_TAC THENL
   [INLINE_ARITH_WITH [h `inline_zrunk OM b n = n + i`]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC;;

let INLINE_ZBODY_AK_TAC p exec =
  let om = mk_small_numeral p.hk_om and h = hk_inst p in
  MP_TAC(SPECL [om; `b:num->byte`;`n:num`;`i:num`] INLINE_ZSTEPSK_MID) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(b:num->byte) (n + i) = word 0`]) THEN
  MP_TAC(SPECL [om; `b:num->byte`;`n:num`;`i + 1`] INLINE_ZSTEPSK_LT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ARM_STEPS_TAC exec (1--5) THEN
  SUBGOAL_THEN (h `~(n + i = OK1)`) ASSUME_TAC THENL
   [INLINE_ARITH_WITH [h `n + i + 1 < OM`]; ALL_TAC] THEN
  MP_TAC(SPEC `n + i` (INLINE_ZBK_PC p)) THEN
  (ANTS_TAC THENL [INLINE_ARITH_WITH [h `n + i < OM`]; DISCH_TAC]) THEN
  SUBGOAL_THEN (h `MIN (n + i + 1) (inline_zrunk OM b n) = n + i + 1`) ASSUME_TAC THENL
   [MATCH_MP_TAC INLINE_MIN_LE_L THEN
    INLINE_ARITH_WITH [h `n + (i + 1) <= inline_zrunk OM b n`]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC;;

let INLINE_ZBODYK_TAC p exec =
  let h = hk_inst p in
  INLINE_ZBODY_PREPK_TAC p THEN
  ASM_CASES_TAC (h `i + 1 < inline_zstepsk OM b n`) THENL
   [INLINE_ZBODY_AK_TAC p exec THENL [CONV_TAC WORD_RULE; PATH_DISCHARGE_TAC]; ALL_TAC] THEN
  ASM_CASES_TAC (INLINE_ZALLZ p) THENL
   [INLINE_ZBODY_BK_TAC p exec THENL
     [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN
      INLINE_ARITH_WITH [h `n + i + 1 = OM`]; PATH_DISCHARGE_TAC];
    INLINE_ZBODY_CK_TAC p exec THENL
     [AP_TERM_TAC THEN ARITH_TAC; PATH_DISCHARGE_TAC]];;

let INLINE_ZEXITK_TAC p =
  let om = mk_small_numeral p.hk_om and h = hk_inst p in
  REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  MP_TAC(SPECL [om; `b:num->byte`;`n:num`] INLINE_ZRUNK_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    ASSUME_TAC(MATCH_MP (SPECL [om; `b:num->byte`;`n:num`] INLINE_ZRUNK_OK)
      (CONJ (ASSUME (h `n < OM`)) (ASSUME (INLINE_ZALLZ p)))) THEN
    ASM_REWRITE_TAC[INLINE_ZSTEPSK] THEN AP_TERM_TAC THEN INLINE_ARITH_WITH [h `n < OM`];
    EXISTS_TAC `e2:(uarch_event)list` THEN ASM_REWRITE_TAC[APPEND]];;

let INLINE_ZCHKK_LOOP p mc exec loop exit fail (rs:string list) =
  let r k = List.nth rs k in
  let tm = INLINE_ZCHKK_LOOP_TERM p mc loop exit fail rs in
  let inv = hk_inst p (parse_term(Printf.sprintf
   "\\p s. aligned_bytes_loaded s (word pc) %s /\\
          read %s s = sg /\\ read %s s = word(MIN (n + p) (inline_zrunk OM b n)) /\\
          (!j. j < OM ==> read(memory :> bytes8(word_add sg (word j))) s = b j) /\\
          read PC s = word(if p < inline_zstepsk OM b n then pc + %s
                           else if (!j. n <= j /\\ j < OM ==> b j = word 0)
                                then pc + %s else pc + %s)"
   mc (r 1) (r 2) loop exit fail)) in
  prove(tm, INLINE_ZSTARTK_TAC p exec inv THENL
    [INLINE_ZINITK_TAC p; INLINE_ZBODYK_TAC p exec; INLINE_ZEXITK_TAC p]);;

let INLINE_ZCHKK_OF p =
  let mc = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc" in
  let l = hk_lbl p in
  INLINE_ZCHKK_LOOP p mc (INLINE_LOOP_EXEC (l p.hk_zloop) (l "join7"))
    (l p.hk_zloop) (l "join7") (l "join2") ["X8";"X27";"X24"];;

(* ------------------------------------------------------------------------- *)
(* The loop of mld_unpack_hints over the hints j = s + 1, ... (shapes 53/54, *)
(* INLINE_HUNP_LOOP of inline_sign_hints.ml) with the registers of 65 and    *)
(* 87: R0 = x9 = j, R1 = x10 = P + j, R2 = x13 = 1, R3 = x28 = h, R4 = x11,  *)
(* R5 = x24 = w, R6 = x8 = s, R7 = x12; the bound w <= omega. The exec range *)
(* is from join10 to the end of the hint code, the exits join6 and           *)
(* loop<n>_exit2.                                                            *)
(* ------------------------------------------------------------------------- *)

let INLINE_HUNPK_TERM p =
  let mc = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc" in
  let l = hk_lbl p in
  let rs = ["X9";"X10";"X13";"X28";"X11";"X24";"X8";"X12"] in
  let r k = List.nth rs k in
  hk_inst p (parse_term(Printf.sprintf
   "exists f_events.
      forall e a h (b:num->byte) (x:num->int32) s w pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        s + 1 < w /\\ w <= OM /\\
        ALL (nonoverlapping (h,1024)) [(word pc,libmldsa_size); (a,OM)]
        ==> ensures arm
             (\\s'. aligned_bytes_loaded s' (word pc) %s /\\
                  read PC s' = word (pc + %s) /\\
                  read %s s' = word (s + 1) /\\
                  read %s s' = word_add a (word (s + 1)) /\\
                  read %s s' = word 1 /\\ read %s s' = h /\\
                  read %s s' = word w /\\ read %s s' = word s /\\
                  (!j. j < OM
                       ==> read(memory :> bytes8(word_add a (word j))) s' = b j) /\\
                  (!q. q < 256
                       ==> read(memory :> bytes32(word_add h (word(4 * q)))) s' =
                           x q) /\\
                  read events s' = e)
             (\\s'. read PC s' = word (if inline_hrun b s w = w
                                      then pc + %s else pc + %s) /\\
                  read %s s' = word (inline_hrun b s w) /\\
                  read %s s' = word_add a (word (inline_hrun b s w)) /\\
                  (!q. q < 256
                       ==> read(memory :> bytes32(word_add h (word(4 * q)))) s' =
                           inline_hset x b s (inline_hrun b s w) q) /\\
                  (exists e2.
                     read events s' = APPEND e2 e /\\
                     e2 = f_events b s w a h pc /\\
                     memaccess_inbounds e2 [a,OM] [h,1024]))
             (MAYCHANGE [PC; %s; %s; %s; %s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(h,1024)])"
   mc (l p.hk_hloop) (r 0) (r 1) (r 2) (r 3) (r 5) (r 6) (l "join6")
   (l (p.hk_hloop ^ "_exit2")) (r 0) (r 1) (r 0) (r 1) (r 4) (r 7)));;

let HK_HEXEC_CACHE = ref [];;

let INLINE_HEXECK p =
  try assoc p.hk_fn (!HK_HEXEC_CACHE) with Failure _ ->
  let th = INLINE_LOOP_EXEC (hk_lbl p "join10")
                            (hk_lbl p "in_sig_unpack_hints_part2_end") in
  HK_HEXEC_CACHE := (p.hk_fn,th) :: (!HK_HEXEC_CACHE); th;;

let INLINE_HINVK p = hk_inst p (parse_term(Printf.sprintf
 "\\i s'. aligned_bytes_loaded s' (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
      read X9 s' = word(MIN (s + 1 + i) (inline_hrun b s w)) /\\
      read X10 s' = word_add a (word(MIN (s + 1 + i) (inline_hrun b s w))) /\\
      read X13 s' = word 1 /\\ read X28 s' = h /\\ read X24 s' = word w /\\
      read X8 s' = word s /\\
      (!j. j < OM ==> read(memory :> bytes8(word_add a (word j))) s' = b j) /\\
      (!q. q < 256 ==> read(memory :> bytes32(word_add h (word(4 * q)))) s' =
           inline_hset x b s (MIN (s + 1 + i) (inline_hrun b s w)) q) /\\
      read PC s' = word(if i < inline_hsteps b s w then pc + %d
                       else if inline_hrun b s w = w then pc + %d else pc + %d)"
 (layout (hk_lbl p p.hk_hloop)) (layout (hk_lbl p "join6"))
 (layout (hk_lbl p (p.hk_hloop ^ "_exit2")))));;

let INLINE_HSTARTK_TAC p =
  CONCRETIZE_F_EVENTS_TAC INLINE_HTPL THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `h:int64`; `b:num->byte`;
                       `x:num->int32`; `s:num`; `w:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; fst (INLINE_HEXECK p); NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GLUE_EVENTS_WHILE_TAC `inline_hsteps (b:num->byte) s w` (INLINE_HINVK p) THEN
  REPEAT CONJ_TAC;;

let INLINE_HBODY_PREPK_TAC p =
  let h = hk_inst p in
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`;`i:num`] INLINE_HSTEPS_LT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (SUBGOAL_THEN `MIN (s + 1 + i) (inline_hrun b s w) = s + 1 + i`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
    [MATCH_MP_TAC INLINE_MIN_LE_L THEN INLINE_ARITH_WITH [`s + 1 + i <= inline_hrun b s w`]; ALL_TAC]) THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) &&
       can (find_term (fun t -> try fst(dest_const t) = "bytes8" with Failure _ -> false)) (concl th)
    then
      MP_TAC(SPEC `s + 1 + i` th) THEN (ANTS_TAC THENL [INLINE_ARITH_WITH [`s + 1 + i < w`; h `w <= OM`]; DISCH_TAC]) THEN
      MP_TAC(SPEC `s + i` th) THEN (ANTS_TAC THENL [INLINE_ARITH_WITH [`s + 1 + i < w`; h `w <= OM`]; ALL_TAC]) THEN
      DISCH_THEN(fun th2 -> ASSUME_TAC th2 THEN
        SUBGOAL_THEN `read (memory :> bytes8 (word_add (word_add a (word (s + 1 + i))) (word 18446744073709551615))) s0 = (b:num->byte) (s + i)` ASSUME_TAC THENL
         [REWRITE_TAC[INLINE_HADDR] THEN ACCEPT_TAC th2; ALL_TAC] THEN
        SUBGOAL_THEN `read (memory :> bytes8 (word_add a (word ((s + 1 + i) + 18446744073709551615)))) s0 = (b:num->byte) (s + i)` ASSUME_TAC THENL
         [REWRITE_TAC[INLINE_HADDR2] THEN ACCEPT_TAC th2; ALL_TAC])
    else NO_TAC);;

let INLINE_HSIM_HEADK_TAC p =
  let h = hk_inst p in
  MP_TAC(SPECL [`s:num`;`s + 1 + i`] INLINE_HL_CMP) THEN
  (ANTS_TAC THENL [INLINE_ARITH_WITH [`s + 1 + i < w`; h `w <= OM`]; DISCH_TAC]) THEN
  ARM_STEPS_TAC (INLINE_HEXECK p) (1--3) THEN INLINE_REWRITE_ASSUMS_WITH_TOP THEN
  ARM_STEPS_TAC (INLINE_HEXECK p) (4--6) THEN
  MP_TAC(SPECL [`(b:num->byte)(s + 1 + i)`;`(b:num->byte)(s + i)`] INLINE_HL_HI) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

let INLINE_HSTORE_STEPSK_TAC p =
  ARM_STEPS_TAC (INLINE_HEXECK p) (7--8) THEN INLINE_HSTORE_NONOV_TAC THEN
  ARM_STEPS_TAC (INLINE_HEXECK p) (9--11);;

let INLINE_HBODY_AK_TAC p =
  let h = hk_inst p in
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`;`i:num`] INLINE_HSTEPS_MID) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  INLINE_HFRAME_PREP_TAC THEN
  INLINE_HSIM_HEADK_TAC p THEN INLINE_HSTORE_PREP_TAC THEN INLINE_HCMP_PC_TAC THEN
  INLINE_HSTORE_STEPSK_TAC p THEN
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`;`i + 1`] INLINE_HSTEPS_LT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`w:num`; `s + 1 + i`] INLINE_HL_EQ) THEN
  ANTS_TAC THENL [INLINE_ARITH_WITH [`s + 1 + i < w`; h `w <= OM`]; DISCH_TAC] THEN
  SUBGOAL_THEN `~(s + 1 + i + 1 = w)` ASSUME_TAC THENL
   [INLINE_ARITH_WITH [`s + 1 + i + 1 < w`]; ALL_TAC] THEN
  SUBGOAL_THEN `MIN (s + 1 + i + 1) (inline_hrun b s w) = s + 1 + i + 1`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC INLINE_MIN_LE_L THEN
    INLINE_ARITH_WITH [`s + 1 + (i + 1) <= inline_hrun b s w`]; ALL_TAC] THEN
  INLINE_HFINAL_TAC;;

let INLINE_HBODY_BK_TAC p =
  let h = hk_inst p in
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`;`i:num`] INLINE_HSTEPS_OK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `i + 1 = inline_hsteps b s w`)) THEN
  INLINE_HFRAME_PREP_TAC THEN
  INLINE_HSIM_HEADK_TAC p THEN INLINE_HSTORE_PREP_TAC THEN INLINE_HCMP_PC_TAC THEN
  INLINE_HSTORE_STEPSK_TAC p THEN
  MP_TAC(SPECL [`w:num`; `s + 1 + i`] INLINE_HL_EQ) THEN
  ANTS_TAC THENL [INLINE_ARITH_WITH [`s + 1 + i < w`; h `w <= OM`]; DISCH_TAC] THEN
  SUBGOAL_THEN `MIN (s + 1 + i + 1) (inline_hrun b s w) = w`
   (fun th -> REWRITE_TAC[th]) THENL
   [INLINE_ARITH_WITH [`s + 1 + i + 1 = w`; `inline_hrun b s w = w`]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [INLINE_HB_W_TAC THEN CONV_TAC WORD_RULE THEN NO_TAC;
         INLINE_HB_W_TAC THEN INLINE_HA_MEM_TAC THEN NO_TAC;
         SUBGOAL_THEN `s + 1 + i + 1 = w` ASSUME_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         REWRITE_TAC[GSYM ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         REWRITE_TAC[INLINE_HADDR] THEN GLUE_PATH_DISCHARGE_TAC THEN NO_TAC;
         INLINE_HFRAME_TAC];;

let INLINE_HBODY_CK_TAC p =
  MP_TAC(SPECL [`b:num->byte`;`s:num`;`w:num`;`i:num`] INLINE_HSTEPS_FAIL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    concl th = `i + 1 = inline_hsteps b s w`)) THEN
  INLINE_HSIM_HEADK_TAC p THEN
  SUBGOAL_THEN `~(val((b:num->byte)(s + i)) < val(b(s + 1 + i)))`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `MIN (s + 1 + i + 1) (s + 1 + i) = s + 1 + i`] THEN
  REPEAT CONJ_TAC THEN
  FIRST [REWRITE_TAC[INLINE_HADDR] THEN GLUE_PATH_DISCHARGE_TAC THEN NO_TAC;
         MONOTONE_MAYCHANGE_TAC];;

let INLINE_HUNPK_LOOP p =
  prove
   (INLINE_HUNPK_TERM p,
    INLINE_HSTARTK_TAC p THENL
     [INLINE_HINIT_TAC;
      INLINE_HBODY_PREPK_TAC p THEN
      ASM_CASES_TAC `i + 1 < inline_hsteps b s w` THENL
       [INLINE_HBODY_AK_TAC p;
        SUBGOAL_THEN `i + 1 = inline_hsteps b s w` ASSUME_TAC THENL
         [INLINE_ARITH_WITH [`i < inline_hsteps b s w`;
                             `~(i + 1 < inline_hsteps b s w)`]; ALL_TAC] THEN
        ASM_CASES_TAC `inline_hrun b s w = w` THENL
         [INLINE_HBODY_BK_TAC p; INLINE_HBODY_CK_TAC p]];
      INLINE_HEXIT_TAC]);;

(*** The instances ***)

let INLINE_HINTS65_INST =
  { hk_fn = "mldsa65_verify_internal"; hk_om = 55; hk_k = 6;
    hk_entry = "loop11_exit"; hk_zloop = "loop12"; hk_hloop = "loop14" };;

let INLINE_HINTS87_INST =
  { hk_fn = "mldsa87_verify_internal"; hk_om = 75; hk_k = 8;
    hk_entry = "loop13_exit"; hk_zloop = "loop14"; hk_hloop = "loop16" };;

(* ------------------------------------------------------------------------- *)
(* The hints of row i (INLINE_HINTS44 of inline_sign_hints44.ml with omega   *)
(* and K): the statement.                                                    *)
(* ------------------------------------------------------------------------- *)

let INLINE_HINTSK_TERM p =
  hk_inst p (parse_term(Printf.sprintf
 "!mf ea el ev.
   memset_ret_full_contract mf ea el ev
   ==> exists f_events.
    forall e (fp:int64) (sg:int64) (hb:num->byte) i (r22:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\ i < KK /\\
      ALL (nonoverlapping (word_add fp (word 352),1024))
          [(word pc,libmldsa_size); (sg,HB); (ea,el);
           (word_add fp (word 32),8)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + %s) /\\
                read SP s = fp /\\ read X27 s = sg /\\ read X26 s = word i /\\
                read X22 s = r22 /\\ read X28 s = word_add fp (word 352) /\\
                read (memory :> bytes64 (word_add fp (word 32))) s =
                  word_add sg (word 1) /\\
                read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
                  mf /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (!j. j < HB
                     ==> read(memory :> bytes8(word_add sg (word j))) s = hb j) /\\
                read events s = e)
           (\\s. read PC s = word (if mld_unpack_hints_ret OM KK hb i = word 0
                                  then pc + %s else pc + %s) /\\
                (mld_unpack_hints_ret OM KK hb i = word 0
                 ==> read X3 s = word i /\\ read X27 s = sg /\\ read X26 s = r22 /\\
                     (!q. q < 256
                          ==> read(memory :> bytes32(word_add fp (word(352 + 4 * q)))) s =
                              mld_unpack_hints OM hb i q)) /\\
                (~(mld_unpack_hints_ret OM KK hb i = word 0)
                 ==> read X27 s = word 4294967290) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events hb sg fp i mf pc /\\
                   memaccess_inbounds e2
                    [sg,HB; word_add fp (word 32),8;
                     word_add fp (word 352),1024;
                     word_add (word pc) (word got_memset),8; ea,el]
                    [word_add fp (word 352),1024]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X18; X19; X21; X22; X24; X26; X27; X30] ,,
            MAYCHANGE [memory :> bytes(word_add fp (word 352),1024)])"
  (hk_lbl p p.hk_entry) (hk_lbl p "join7") (hk_lbl p "join3")));;

(*** The well-formedness of the hints as the outcomes of the tests ***)

let HK_HOK_EQ p =
  let h = hk_inst p and om = mk_small_numeral p.hk_om in
  prove(h
 `!(b:num->byte) i.
     i < KK
     ==> (mld_unpack_hints_ret OM KK b i = word 0 <=>
          val(b(OM + i)) <= OM /\
          mld_hints_start OM b i <= val(b(OM + i)) /\
          (mld_hints_start OM b i + 1 < val(b(OM + i))
           ==> inline_hrun b (mld_hints_start OM b i) (val(b(OM + i))) =
               val(b(OM + i))) /\
          (i = K1 /\ val(b(OM + i)) < OM
           ==> inline_zrunk OM b (val(b(OM + i))) = OM))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN (h `mld_unpack_hints_ret OM KK (b:num->byte) i = word 0 <=>
                mld_unpack_hints_ok OM KK b i`) SUBST1_TAC THENL
   [REWRITE_TAC[mld_unpack_hints_ret] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[mld_unpack_hints_ok] THEN
  ABBREV_TAC (h `st = mld_hints_start OM (b:num->byte) i`) THEN
  ABBREV_TAC (h `nw = val((b:num->byte)(OM + i))`) THEN
  SUBGOAL_THEN
   `(!j. st < j /\ j < nw ==> val((b:num->byte)(j - 1)) < val(b j)) <=>
    (st + 1 < nw ==> inline_hrun b st nw = nw)` SUBST1_TAC THENL
   [ASM_CASES_TAC `st + 1 < nw` THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`b:num->byte`; `st:num`; `nw:num`] INLINE_HRUN_FACTS) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN (h
   `(i = KK - 1 ==> !j. nw <= j /\ j < OM ==> (b:num->byte) j = word 0) <=>
    (i = K1 /\ nw < OM ==> inline_zrunk OM b nw = OM)`) SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE (h `KK - 1 = K1`)] THEN
    ASM_CASES_TAC (h `(i:num) = K1`) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC (h `nw < OM`) THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(SPECL [om; `b:num->byte`; `nw:num`] INLINE_ZRUNK_FACTS) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN ASM_ARITH_TAC];
    MESON_TAC[]]);;

let HK_UNPACK_MANY p = prove(hk_inst p
 `!(b:num->byte) i q.
     mld_hints_start OM b i < val(b(OM + i))
     ==> mld_unpack_hints OM b i q =
         inline_hset (\q. if val(b(mld_hints_start OM b i)) = q then word 1
                          else word 0) b (mld_hints_start OM b i)
                     (val(b(OM + i))) q`,
  SIMP_TAC[HR_HSET_EQ; mld_unpack_hints]);;

let HK_UNPACK_NONE p = prove(hk_inst p
 `!(b:num->byte) i q.
     val(b(OM + i)) <= mld_hints_start OM b i
     ==> mld_unpack_hints OM b i q = word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_unpack_hints] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN ASM_ARITH_TAC);;

(*** The events template: one meta-variable per path ***)

let HK_TPL p =
  let args = "hb sg fp i mf pc" in
  let hrf n = "(f_ev_" ^ n ^ " " ^ args ^ ")" in
  let nw = "val((hb:num->byte)(OM + i))" and st = "mld_hints_start OM hb i" in
  let hz s = "(if " ^ st ^ " < " ^ nw ^ " then (if " ^ st ^ " + 1 < " ^ nw ^ " then " ^
             hrf ("h" ^ s) ^ " else " ^ hrf ("o" ^ s) ^ ") else " ^ hrf ("n" ^ s) ^ ")" in
  hk_inst p (parse_term(
  "\\(hb:num->byte) (sg:int64) (fp:int64) (i:num) (mf:int64) (pc:num). " ^
  "if OM < " ^ nw ^ " then (if i = 0 then " ^ hrf "a0" ^ " else " ^ hrf "a1" ^ ") else " ^
  "if " ^ nw ^ " < " ^ st ^ " then " ^ hrf "b" ^ " else " ^
  "if " ^ st ^ " + 1 < " ^ nw ^ " /\\ ~(inline_hrun hb (" ^ st ^ ") (" ^ nw ^ ") = " ^ nw ^ ") " ^
  "then (if i = 0 then " ^ hrf "hf0" ^ " else " ^ hrf "hf1" ^ ") else " ^
  "if i = 0 then " ^ hz "0" ^ " else " ^
  "if i = K1 then (if " ^ nw ^ " < OM then (if inline_zrunk OM hb (" ^ nw ^ ") = OM then " ^ hz "z" ^
  " else " ^ hz "zf" ^ ") else " ^ hz "3" ^ ") else " ^ hz "1" ^ " :(uarch_event)list"));;

(*** The exec theorem of the region, decoded once per function ***)

let HK_EXEC_CACHE = ref [];;

let HK_EXEC p =
  try assoc p.hk_fn (!HK_EXEC_CACHE) with Failure _ ->
  let th =
    ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (hk_lbl p p.hk_entry), layout (hk_lbl p "join7"));
      (layout (hk_lbl p "join2"), layout (hk_lbl p "join3"));
      (layout (hk_lbl p "in_poly_use_hint_end"),
       layout (hk_lbl p "in_sig_unpack_hints_part2_end"));
      layout_range "plt_memset"] in
  HK_EXEC_CACHE := (p.hk_fn,th) :: (!HK_EXEC_CACHE); th;;

let HK_ST p = hk_inst p `mld_hints_start OM (hb:num->byte) i`;;
let HK_NW p = hk_inst p `val((hb:num->byte)(OM + i))`;;

let HK_PC_TAC = HR_PC_TAC;;

let HK_BYTE_FACT_TAC off vtm =
  FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `hb:num->byte` (concl th) then
    let tm = subst [mk_small_numeral off,`k:num`] `i + k` in
    MP_TAC(SPEC tm th) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun bth -> MP_TAC(TRANS bth (AP_TERM `hb:num->byte` (ARITH_RULE(mk_eq(tm,vtm)))))) THEN
    DISCH_TAC
   else NO_TAC);;

(*** The prefix: i = 0 (steps 1-9) or i <> 0 (steps 1-11), to the test of nw ***)

let HK_PREFIX_TAC p =
  let h = hk_inst p and ex = HK_EXEC p in
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `val(word i:int64) = i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  HK_BYTE_FACT_TAC p.hk_om (h `OM + i`) THEN
  ARM_STEPS_TAC ex (1--2) THEN
  ASM_CASES_TAC `i = 0` THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `i = 0` then
      ASSUME_TAC(MP (ARITH_RULE `i = 0 ==> i <= 0`) th) else NO_TAC) THEN
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read PC s = (if b then x else y):int64`) (concl th)
      then REWRITE_RULE[ASSUME `val(word i:int64) = i`;
                        MP (ARITH_RULE `i <= 0 ==> i = 0`) (ASSUME `i <= 0`)] th
      else th) THEN
    ARM_STEPS_TAC ex (3--8) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INLINE_HL_ZX]) THEN
    ARM_STEPS_TAC ex [9] THEN GLUE_W32_FLAGS_TAC;
    MP_TAC(ARITH_RULE (h `~(i = 0) ==> i + OK1 = OM + (i - 1)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `hb:num->byte` (concl th) then
      MP_TAC(SPEC (h `i + OK1`) th) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun bth -> ASSUME_TAC(TRANS bth (AP_TERM `hb:num->byte`
        (ASSUME (h `i + OK1 = OM + (i - 1)`)))))
     else NO_TAC) THEN
    RULE_ASSUM_TAC(fun th -> if concl th = `~(i = 0)` then th
                             else REWRITE_RULE[ASSUME `~(i = 0)`] th) THEN
    ARM_STEPS_TAC ex (3--9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INLINE_HL_ZX]) THEN
    ARM_STEPS_TAC ex (10--11) THEN GLUE_W32_FLAGS_TAC];;

let HK_NOTHOK_TAC p =
  let h = hk_inst p in
  SUBGOAL_THEN (h `~(mld_unpack_hints_ret OM KK hb i = word 0)`) ASSUME_TAC THENL
   [MP_TAC(SPECL [`hb:num->byte`; `i:num`] (HK_HOK_EQ p)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN GLUE_ARITH_TAC; ALL_TAC];;

let HK_ST_BOUND p = prove(hk_inst p
 `!(hb:num->byte) i. mld_hints_start OM hb i < 256`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_hints_start] THEN COND_CASES_TAC THEN
  REWRITE_TAC[INLINE_HL_VAL256] THEN ARITH_TAC);;

(*** x21 = st after the prefix ***)

let HK_X21_TAC p k =
  let s = mk_var("s"^string_of_int k,`:armstate`) in
  W(fun (asl,w) ->
    let th = snd(find (fun (_,th) -> is_eq(concl th) &&
                         lhs(concl th) = mk_comb(`read X21`,s)) asl) in
    SUBGOAL_THEN (mk_eq(rhs(concl th),
                        mk_comb(`word:num->int64`,HK_ST p)))
      (fun eq -> ASSUME_TAC(TRANS th eq)) THENL
     [REWRITE_TAC[mld_hints_start] THEN HR_I0_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC) THEN
      ASM_ARITH_TAC;
      ALL_TAC]) THEN
  FIRST_X_ASSUM(fun th -> if lhs(concl th) = mk_comb(`read X21`,s) &&
                             not(free_in `mld_hints_start` (concl th))
                          then ALL_TAC else NO_TAC) THEN
  ASSUME_TAC(SPECL [`hb:num->byte`; `i:num`] (HK_ST_BOUND p));;

let HK_ALLOWED = [`hb:num->byte`; `sg:int64`; `fp:int64`; `i:num`; `mf:int64`; `pc:num`];;

let HK_MEMSET_TAC p n =
  LIBC_PLT_TAC (HK_EXEC p) n THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" (HK_EXEC p)
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`]
   (ref HK_ALLOWED) (n + 5);;

let HK_ZERO_TAC k =
  let s = mk_var("s"^string_of_int k,`:armstate`) in
  MP_TAC(SPECL [`word_add (fp:int64) (word 352)`; `256`; s] GLUE_ZERO32) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `word_zx (word 0:int64):byte` (concl th)
                          then ACCEPT_TAC th else NO_TAC);
    DISCH_TAC];;

let HK_HOK_TAC p =
  let h = hk_inst p in
  SUBGOAL_THEN (h `mld_unpack_hints_ret OM KK hb i = word 0`) ASSUME_TAC THENL
   [MP_TAC(SPECL [`hb:num->byte`; `i:num`] (HK_HOK_EQ p)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REPEAT CONJ_TAC THEN
    REPEAT STRIP_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN GLUE_ARITH_TAC; ALL_TAC];;

let HK_H_FORM = prove
 (`!(fp:int64) q. word_add (word_add fp (word 352)) (word (4 * q)) =
                  word_add fp (word (352 + 4 * q))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let HK_I3 p = prove(hk_inst p
 `!i. i < KK ==> (val (word_sub (word i:int64) (word K1)) = 0 <=> i = K1)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV));;

let HK_I3_TAC p =
  FIRST_ASSUM(fun th -> if concl th = hk_inst p `i < KK` then
    RULE_ASSUM_TAC(fun t ->
      if can (term_match [] `read PC s = (if b then x else y):int64`) (concl t)
      then REWRITE_RULE[MP (SPEC `i:num` (HK_I3 p)) th] t else t) else NO_TAC);;

let HK_HFACT_TAC lem =
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  W(fun (asl,w) ->
    let st = rand(lhs w) in
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in st (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "bytes32" with _ -> false)) (concl th)
      then REWRITE_TAC[MATCH_MP (REWRITE_RULE[HK_H_FORM] th) (ASSUME `q < 256`)]
      else NO_TAC)) THEN
  lem;;

let HK_NONE_LEM p =
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC (HK_UNPACK_NONE p) THEN ASM_ARITH_TAC;;

let HK_DECIDE_TAC = HR_DECIDE_TAC;;
let HK_COND_TAC = HR_COND_TAC;;

let HK_GEN_ST_TAC p =
  let st = HK_ST p in
  W(fun (asl,w) ->
    if not(free_in st w) then ALL_TAC else
    SUBGOAL_THEN (mk_binop `(<):num->num->bool` st (mk_small_numeral(p.hk_om + 1)))
     MP_TAC THENL
     [GLUE_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(st,genvar `:num`) THEN GEN_TAC THEN DISCH_TAC);;

let HK_PATH_DISCHARGE_TAC p =
  let st = HK_ST p in
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
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if ((try fst(dest_const(fst(strip_comb c))) = "memaccess_inbounds"
         with Failure _ -> false) ||
        (is_eq c && is_var(lhs c) && (try String.sub (fst(dest_var(lhs c))) 0 2 = "e2" with _ -> false))) &&
       (free_in `hb:num->byte` c || free_in st c)
    then MP_TAC th else NO_TAC)) THEN
  HK_GEN_ST_TAC p THEN GLUE_GEN_BYTES_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let HK_EVENTS_TAC p =
  HR_I0_TAC THEN VERIF_EVENTS_ONLY_TAC THEN HK_COND_TAC THEN HK_COND_TAC THEN
  HK_PATH_DISCHARGE_TAC p;;

let HK_FAIL_FINAL_TAC p =
  HK_NOTHOK_TAC p THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN FIRST [INLINE_HFRAME_TAC THEN NO_TAC; HK_EVENTS_TAC p];;

let HK_OK_FINAL_TAC p hlem =
  HK_HOK_TAC p THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [HK_HFACT_TAC hlem THEN NO_TAC; INLINE_HFRAME_TAC THEN NO_TAC;
         HK_EVENTS_TAC p];;

let HK_HB p = subst [HK_ST p,`st:num`] `val((hb:num->byte) st)`;;
let HK_H = `word_add (fp:int64) (word 352)`;;

(*** The peel: x8 = st, the byte hb st, the store h[hb st] := 1 ***)

let HK_PEEL1_TAC p m =
  let ex = HK_EXEC p and st = HK_ST p in
  ARM_STEPS_TAC ex [m + 1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC st HR_ZX_SMALL)
                               (SPECL [`hb:num->byte`; `i:num`] (HK_ST_BOUND p))]) THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `hb:num->byte` (concl th) &&
                           free_in `sg:int64` (concl th) then
    MP_TAC(SPEC st th) THEN ANTS_TAC THENL [GLUE_ARITH_TAC; DISCH_TAC]
   else NO_TAC) THEN
  ARM_STEPS_TAC ex [m + 2] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INLINE_HL_ZX]) THEN
  ASSUME_TAC(SPEC (subst [st,`st:num`] `(hb:num->byte) st`) INLINE_HL_VAL256) THEN
  ASSUME_TAC(SPEC (subst [st,`st:num`] `(hb:num->byte) st`) INLINE_HL_VALW) THEN
  ARM_STEPS_TAC ex ((m + 3)--(m + 4));;

let HK_FRAME_PREP_TAC p =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!q. q < 256 ==> read (memory :> bytes32 (word_add h (word (4 * q)))) s = (f:num->int32) q`) (concl th)
    then
      let st = rand(lhs(snd(dest_imp(snd(dest_forall(concl th)))))) in
      SUBGOAL_THEN (subst [HK_HB p,`v:num`; st,`s:armstate`]
        `!q. q < 256 /\ ~(q = v)
             ==> read (memory :> bytes32 (word_add (word_add fp (word 352)) (word (4 * q)))) s =
                 word 0`) ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MP_TAC(SPEC `q:num` th) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
        ALL_TAC]
    else NO_TAC);;

let HK_X0 p = subst [HK_HB p,`v:num`]
  `\q:num. if (v:num) = q then word 1 else word 0:int32`;;

let HK_COMBINE_TAC p s =
  SUBGOAL_THEN (subst [s,`s:armstate`; HK_HB p,`v:num`]
    `!q. q < 256
         ==> read (memory :> bytes32 (word_add (word_add fp (word 352)) (word (4 * q)))) s =
             (if v = q then word 1 else word 0:int32)`) ASSUME_TAC THENL
   [X_GEN_TAC `q:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[HK_H_FORM] THEN
      FIRST_ASSUM(fun th -> if rhs(concl th) = `word 1:int32` &&
                    can (find_term (fun t -> try fst(dest_const t) = "bytes32" with _ -> false)) (concl th)
                  then ACCEPT_TAC th else NO_TAC);
      FIRST_ASSUM(fun th -> if is_forall(concl th) && is_conj(lhand(snd(dest_forall(concl th))))
                  then MATCH_MP_TAC th else NO_TAC) THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[]];
    ALL_TAC];;

let HK_PEEL2_TAC p m =
  let ex = HK_EXEC p in
  HK_FRAME_PREP_TAC p THEN
  SUBGOAL_THEN (subst [HK_HB p,`v:num`] `nonoverlapping (word_add (word_add fp (word 352)) (word (4 * v)):int64,4) (word pc,libmldsa_size)`)
    ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC ex [m + 5] THEN
  HK_COMBINE_TAC p (mk_var("s"^string_of_int(m + 5),`:armstate`)) THEN
  ARM_STEPS_TAC ex [m + 6] THEN
  MP_TAC(SPECL [HK_ST p; HK_NW p] HR_EQ1) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun eq -> RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read PC s = (if b then x else y):int64`) (concl th)
      then REWRITE_RULE[eq] th else th));;

let HK_ONE_LEM p =
  MP_TAC(SPECL [`hb:num->byte`; `i:num`; `q:num`] (HK_UNPACK_MANY p)) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [HK_X0 p; `hb:num->byte`; HK_ST p; HK_NW p; `q:num`] INLINE_HSET_0) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  BETA_TAC THEN REFL_TAC;;

let HK_MANY_LEM p =
  MP_TAC(SPECL [`hb:num->byte`; `i:num`; `q:num`] (HK_UNPACK_MANY p)) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
     (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "inline_hrun" with _ -> false)
     then REWRITE_TAC[th] else NO_TAC);;

(*** The bytes of the index part only, P[0 .. omega - 1] ***)

let HK_BYTESOM_TAC p n =
  let s = mk_var("s"^string_of_int n,`:armstate`) in
  let h = hk_inst p in
  SUBGOAL_THEN (subst [s,`s:armstate`] (h
    `!j. j < OM ==> read(memory :> bytes8(word_add sg (word j))) s = (hb:num->byte) j`))
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `hb:num->byte` (concl th) &&
                             free_in (mk_small_numeral(p.hk_om + p.hk_k)) (concl th)
                          then MATCH_MP_TAC th else NO_TAC) THEN
    UNDISCH_TAC (h `j < OM`) THEN ARITH_TAC;
    ALL_TAC];;

let HK_ZCHK_TAC p zth n lem =
  let h = hk_inst p and om = mk_small_numeral p.hk_om in
  HK_BYTESOM_TAC p (n - 1) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc (HK_EXEC p) "H_ZCHK"
   [`read X27 s`; `hb:num->byte`; HK_NW p; `pc:num`] HK_ALLOWED n THEN
  MP_TAC(SPECL [om; `hb:num->byte`; HK_NW p] INLINE_ZRUNK_FACTS) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> let eq = CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 th))) in
    RULE_ASSUM_TAC(REWRITE_RULE[eq])) THEN
  ASM_CASES_TAC (subst [HK_NW p,`w:num`] (h `inline_zrunk OM hb w = OM`)) THENL
   [HR_LOG "zok" (HK_PC_TAC THEN HK_OK_FINAL_TAC p lem);
    HR_LOG "zf" (HK_PC_TAC THEN ARM_STEPS_TAC (HK_EXEC p) [n + 1] THEN HK_FAIL_FINAL_TAC p)];;

let HK_NOT3_TAC p =
  TRY(FIRST_ASSUM(fun th -> if concl th = `i <= 0` then
        UNDISCH_TAC (hk_inst p `K1 <= i`) THEN UNDISCH_TAC `i <= 0` THEN ARITH_TAC
      else NO_TAC));;

(*** join6: the test of the last row (2 instructions), then for the last  ***)
(*** row the test of nw against omega and the check of the zero bytes     ***)

let HK_TAIL_TAC p zth m lem =
  let h = hk_inst p and ex = HK_EXEC p in
  ARM_STEPS_TAC ex ((m + 1)--(m + 2)) THEN HK_I3_TAC p THEN
  ASM_CASES_TAC (h `K1 <= i`) THENL
   [HK_NOT3_TAC p THEN HK_PC_TAC THEN ARM_STEPS_TAC ex [m + 3] THEN
    GLUE_W32_FLAGS_TAC THEN ARM_STEPS_TAC ex [m + 4] THEN
    ASM_CASES_TAC (subst [HK_NW p,`w:num`] (h `w < OM`)) THENL
     [HK_PC_TAC THEN HK_ZCHK_TAC p zth (m + 5) lem;
      HR_LOG "ge" (HK_PC_TAC THEN HK_OK_FINAL_TAC p lem)];
    HR_LOG "notlast" (HK_PC_TAC THEN HK_OK_FINAL_TAC p lem)];;

let HK_MANY_TAC p zth m =
  let h = hk_inst p and ex = HK_EXEC p in
  HK_PC_TAC THEN ARM_STEPS_TAC ex ((m + 7)--(m + 9)) THEN HR_X9X10_TAC (m + 9) THEN
  HK_BYTESOM_TAC p (m + 9) THEN
  SUBGOAL_THEN (mk_binop `(<=):num->num->bool` (HK_NW p) (mk_small_numeral p.hk_om))
   ASSUME_TAC THENL [GLUE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (h `nonoverlapping (word_add (fp:int64) (word 352),1024) (sg,OM)`) MP_TAC THENL
   [NONOVERLAPPING_TAC; REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN DISCH_TAC] THEN
  RULE_ASSUM_TAC(fun th -> if is_forall(concl th) then REWRITE_RULE[HK_H_FORM] th else th) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc ex "H_HUNP"
   [`sg:int64`; HK_H; `hb:num->byte`; HK_X0 p; HK_ST p; HK_NW p; `pc:num`] HK_ALLOWED (m + 10) THEN
  ASM_CASES_TAC (subst [HK_ST p,`st:num`; HK_NW p,`w:num`] `inline_hrun hb st w = w`) THENL
   [HK_PC_TAC THEN HK_TAIL_TAC p zth (m + 10) (HK_MANY_LEM p);
    HR_LOG "hf" (HK_PC_TAC THEN ARM_STEPS_TAC ex ((m + 11)--(m + 12)) THEN HK_FAIL_FINAL_TAC p)];;

let HK_PEEL_TAC p zth m =
  HK_PC_TAC THEN HK_PEEL1_TAC p m THEN HK_PEEL2_TAC p m THEN
  ASM_CASES_TAC (subst [HK_ST p,`st:num`; HK_NW p,`w:num`] `st + 1 < w`) THENL
   [HK_MANY_TAC p zth m;
    HK_PC_TAC THEN HK_TAIL_TAC p zth (m + 6) (HK_ONE_LEM p)];;

let HK_J5_TAC p zth k =
  let ex = HK_EXEC p in
  HK_X21_TAC p k THEN ARM_STEPS_TAC ex [k + 1] THEN GLUE_W32_FLAGS_TAC THEN
  ARM_STEPS_TAC ex [k + 2] THEN
  ASM_CASES_TAC (subst [HK_ST p,`st:num`; HK_NW p,`w:num`] `w < st`) THENL
   [TRY(UNDISCH_TAC (subst [HK_ST p,`st:num`; HK_NW p,`w:num`] `w < st`) THEN
        REWRITE_TAC[mld_hints_start] THEN HR_I0_TAC THEN ASM_REWRITE_TAC[] THEN
        ARITH_TAC THEN NO_TAC) THEN
    HR_LOG "b" (HK_PC_TAC THEN HK_FAIL_FINAL_TAC p);
    HK_PC_TAC THEN ARM_STEPS_TAC ex ((k + 3)--(k + 7)) THEN MLD_WRAP_GOT_TAC THEN
    HK_MEMSET_TAC p (k + 7) THEN HK_ZERO_TAC (k + 12) THEN
    ARM_STEPS_TAC ex [k + 13] THEN GLUE_W32_FLAGS_TAC THEN
    ARM_STEPS_TAC ex ((k + 14)--(k + 17)) THEN
    ASM_CASES_TAC (subst [HK_ST p,`st:num`; HK_NW p,`w:num`] `st < w`) THENL
     [HK_PEEL_TAC p zth (k + 17);
      HK_PC_TAC THEN HK_TAIL_TAC p zth (k + 17) (HK_NONE_LEM p)]];;

let HK_SETUP_TAC p hth zth =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_ret_full_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC hth "H_HUNP" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC zth "H_ZCHK" THEN
  CONCRETIZE_F_EVENTS_TAC (HK_TPL p) THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `sg:int64`; `hb:num->byte`;
                       `i:num`; `r22:int64`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; fst (HK_EXEC p)] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI];;

let INLINE_HINTSK_PROVE p =
  let h = hk_inst p and ex = HK_EXEC p in
  let hth = INLINE_HUNPK_LOOP p and zth = INLINE_ZCHKK_OF p in
  prove(INLINE_HINTSK_TERM p,
  HK_SETUP_TAC p hth zth THEN HK_PREFIX_TAC p THENL
   [ASM_CASES_TAC (h `OM < val((hb:num->byte)(OM + i))`) THENL
     [HR_LOG "a0" (ARM_STEPS_TAC ex [10] THEN HK_PC_TAC THEN HK_FAIL_FINAL_TAC p);
      ARM_STEPS_TAC ex [10] THEN HK_PC_TAC THEN HK_J5_TAC p zth 10];
    ASM_CASES_TAC (h `OM < val((hb:num->byte)(OM + i))`) THENL
     [HR_LOG "a1" (HK_PC_TAC THEN ARM_STEPS_TAC ex [12] THEN HK_FAIL_FINAL_TAC p);
      HK_PC_TAC THEN HK_J5_TAC p zth 11]]);;
