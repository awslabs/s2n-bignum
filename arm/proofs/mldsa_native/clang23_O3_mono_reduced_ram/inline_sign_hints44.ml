(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The hints of row i of mldsa44_verify_internal, as clang 23 -O3 has        *)
(* inlined mld_unpack_hints into the row loop (loop10_exit to join7 when the *)
(* hints of the row are well formed, join3 with -6 in w26 otherwise):        *)
(* the checks of the count nw = hb[80 + i] against 80 and against the count  *)
(* st of the rows before, the memset of h at F + 448, the first hint, the    *)
(* loop over the others (INLINE_HUNP_LOOP), the constants of use_hint and,   *)
(* for the last row, the check that the unused bytes are zero                *)
(* (INLINE_ZCHK_LOOP). The result is mld_unpack_hints 80 hb i in h when      *)
(* mld_unpack_hints_ret 80 4 hb i = 0.                                       *)
(*                                                                           *)
(* The proof splits on the outcomes of the tests and simulates each path to  *)
(* its end; the events template has one meta-variable per path (HR_TPL).     *)
(* The prefix differs for i = 0 (st = 0, no load), which is kept as i <= 0   *)
(* so that the simulation does not rewrite the addresses with it.            *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_hints_tac.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;

(* ------------------------------------------------------------------------- *)
(* The statement.                                                            *)
(* ------------------------------------------------------------------------- *)

let INLINE_HINTS44_TERM =
 `!mf ea el ev.
   memset_ret_full_contract mf ea el ev
   ==> exists f_events.
    forall e (fp:int64) (sg:int64) (hb:num->byte) i pc.
      aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
      aligned 16 fp /\ i < 4 /\
      ALL (nonoverlapping (word_add fp (word 448),1024))
          [(word pc,libmldsa_size); (sg,84); (ea,el);
           (word_add fp (word 24),8); (word_add fp (word 440),8)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                read PC s = word (pc + mldsa44_verify_internal_loop10_exit) /\
                read SP s = fp /\ read X26 s = sg /\
                read X27 s = word_add fp (word 448) /\
                read (memory :> bytes64 (word_add fp (word 440))) s = word i /\
                read (memory :> bytes64 (word_add fp (word 24))) s =
                  word_add sg (word 1) /\
                read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
                  mf /\
                read (memory :> bytes(ea,el)) s = ev /\
                (!j. j < 84
                     ==> read(memory :> bytes8(word_add sg (word j))) s = hb j) /\
                read events s = e)
           (\s. read PC s = word (if mld_unpack_hints_ret 80 4 hb i = word 0
                                  then pc + mldsa44_verify_internal_join7
                                  else pc + mldsa44_verify_internal_join3) /\
                (mld_unpack_hints_ret 80 4 hb i = word 0
                 ==> read X3 s = word i /\ read X26 s = sg /\
                     read X13 s = word 4286586879 /\ read X14 s = word 11275 /\
                     read X15 s = word 8388608 /\ read X16 s = word 43 /\
                     read X17 s = word 4294776832 /\ read X18 s = word 4190208 /\
                     (!q. q < 256
                          ==> read(memory :> bytes32(word_add fp (word(448 + 4 * q)))) s =
                              mld_unpack_hints 80 hb i q)) /\
                (~(mld_unpack_hints_ret 80 4 hb i = word 0)
                 ==> read X26 s = word 4294967290) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   e2 = f_events hb sg fp i mf pc /\
                   memaccess_inbounds e2
                    [sg,84; word_add fp (word 24),8; word_add fp (word 440),8;
                     word_add fp (word 448),1024;
                     word_add (word pc) (word got_memset),8; ea,el]
                    [word_add fp (word 448),1024]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X18; X19; X21; X23; X25; X26; X30] ,,
            MAYCHANGE [memory :> bytes(word_add fp (word 448),1024)])`;;

(*** The well-formedness of the hints as the outcomes of the tests ***)

let HR_HOK_EQ = prove
 (`!(b:num->byte) i.
     i < 4
     ==> (mld_unpack_hints_ret 80 4 b i = word 0 <=>
          val(b(80 + i)) <= 80 /\
          mld_hints_start 80 b i <= val(b(80 + i)) /\
          (mld_hints_start 80 b i + 1 < val(b(80 + i))
           ==> inline_hrun b (mld_hints_start 80 b i) (val(b(80 + i))) =
               val(b(80 + i))) /\
          (i = 3 /\ val(b(80 + i)) < 80
           ==> inline_zrun b (val(b(80 + i))) = 80))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mld_unpack_hints_ret 80 4 (b:num->byte) i = word 0 <=>
                mld_unpack_hints_ok 80 4 b i` SUBST1_TAC THENL
   [REWRITE_TAC[mld_unpack_hints_ret] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[mld_unpack_hints_ok] THEN
  ABBREV_TAC `st = mld_hints_start 80 (b:num->byte) i` THEN
  ABBREV_TAC `nw = val((b:num->byte)(80 + i))` THEN
  SUBGOAL_THEN
   `(!j. st < j /\ j < nw ==> val((b:num->byte)(j - 1)) < val(b j)) <=>
    (st + 1 < nw ==> inline_hrun b st nw = nw)` SUBST1_TAC THENL
   [ASM_CASES_TAC `st + 1 < nw` THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`b:num->byte`; `st:num`; `nw:num`] INLINE_HRUN_FACTS) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(i = 4 - 1 ==> !j. nw <= j /\ j < 80 ==> (b:num->byte) j = word 0) <=>
    (i = 3 /\ nw < 80 ==> inline_zrun b nw = 80)` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 - 1 = 3`] THEN
    ASM_CASES_TAC `i = 3` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `nw < 80` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(SPECL [`b:num->byte`; `nw:num`] INLINE_ZRUN_FACTS) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN ASM_ARITH_TAC];
    MESON_TAC[]]);;

let HR_UNPACK_MANY = prove
 (`!(b:num->byte) i q.
     mld_hints_start 80 b i < val(b(80 + i))
     ==> mld_unpack_hints 80 b i q =
         inline_hset (\q. if val(b(mld_hints_start 80 b i)) = q then word 1
                          else word 0) b (mld_hints_start 80 b i)
                     (val(b(80 + i))) q`,
  SIMP_TAC[HR_HSET_EQ; mld_unpack_hints]);;

let HR_UNPACK_NONE = prove
 (`!(b:num->byte) i q.
     val(b(80 + i)) <= mld_hints_start 80 b i
     ==> mld_unpack_hints 80 b i q = word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_unpack_hints] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN ASM_ARITH_TAC);;

let HR_ARGS = "hb sg fp i mf pc";;
let HR_NEW = "val((hb:num->byte)(80 + i))";;
let HR_OLD = "mld_hints_start 80 hb i";;
let hrf n = "(f_ev_" ^ n ^ " " ^ HR_ARGS ^ ")";;
let HR_TPL =
  let nw = HR_NEW and st = HR_OLD in
  let hz s = "(if " ^ st ^ " < " ^ nw ^ " then (if " ^ st ^ " + 1 < " ^ nw ^ " then " ^
             hrf ("h" ^ s) ^ " else " ^ hrf ("o" ^ s) ^ ") else " ^ hrf ("n" ^ s) ^ ")" in
  parse_term(
  "\\(hb:num->byte) (sg:int64) (fp:int64) (i:num) (mf:int64) (pc:num). " ^
  "if 80 < " ^ nw ^ " then (if i = 0 then " ^ hrf "a0" ^ " else " ^ hrf "a1" ^ ") else " ^
  "if " ^ nw ^ " < " ^ st ^ " then " ^ hrf "b" ^ " else " ^
  "if " ^ st ^ " + 1 < " ^ nw ^ " /\\ ~(inline_hrun hb (" ^ st ^ ") (" ^ nw ^ ") = " ^ nw ^ ") " ^
  "then (if i = 0 then " ^ hrf "hf0" ^ " else " ^ hrf "hf1" ^ ") else " ^
  "if i = 0 then " ^ hz "0" ^ " else " ^
  "if i = 3 then (if " ^ nw ^ " < 80 then (if inline_zrun hb (" ^ nw ^ ") = 80 then " ^ hz "z" ^
  " else " ^ hz "zf" ^ ") else " ^ hz "3" ^ ") else " ^ hz "1" ^ " :(uarch_event)list");;
let ZCHK44 = INLINE_ZCHK_LOOP_OF (hd INLINE_ZCHK_LOOP_INSTANCES);;


let HR_EXEC = ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout "mldsa44_verify_internal_loop10_exit", layout "mldsa44_verify_internal_loop6_exit5");
   (layout "mldsa44_verify_internal_join2", layout "mldsa44_verify_internal_join3");
   layout_range "plt_memset"];;

let HR_ST = `mld_hints_start 80 (hb:num->byte) i`;;
let HR_NW = `val((hb:num->byte)(80 + i))`;;

let HR_JOIN5 = `\s. aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
    read PC s = word (pc + mldsa44_verify_internal_join5) /\
    read SP s = fp /\ read X9 s = word i /\
    read X25 s = word (mld_hints_start 80 hb i) /\
    read X21 s = word (val((hb:num->byte)(80 + i))) /\
    read X23 s = sg /\ read X26 s = word 4294967290 /\
    read X27 s = word_add fp (word 448) /\
    read (memory :> bytes64 (word_add fp (word 24))) s = word_add sg (word 1) /\
    read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
    read (memory :> bytes(ea,el)) s = ev /\
    (!j. j < 84 ==> read(memory :> bytes8(word_add sg (word j))) s = hb j)`;;

let HR_JOIN6 = `\s. aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
    read PC s = word (pc + mldsa44_verify_internal_join6) /\
    read SP s = fp /\ read X3 s = word i /\
    read X21 s = word (val((hb:num->byte)(80 + i))) /\
    read X26 s = sg /\ read X27 s = word_add fp (word 448) /\
    (!j. j < 84 ==> read(memory :> bytes8(word_add sg (word j))) s = hb j) /\
    (!q. q < 256
         ==> read(memory :> bytes32(word_add fp (word(448 + 4 * q)))) s =
             mld_unpack_hints 80 hb i q)`;;

let HR_BYTE_FACT_TAC off vtm =
  FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `hb:num->byte` (concl th) then
    let tm = subst [mk_small_numeral off,`k:num`] `i + k` in
    MP_TAC(SPEC tm th) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun bth -> MP_TAC(TRANS bth (AP_TERM `hb:num->byte` (ARITH_RULE(mk_eq(tm,vtm)))))) THEN
    DISCH_TAC
   else NO_TAC);;

(*** The prefix: i = 0 (steps 1-9) or i <> 0 (steps 1-10), to the test of nw ***)

let HR_PREFIX_TAC =
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `val(word i:int64) = i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  HR_BYTE_FACT_TAC 80 `80 + i` THEN
  ARM_STEPS_TAC HR_EXEC (1--2) THEN
  ASM_CASES_TAC `i = 0` THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `i = 0` then
      ASSUME_TAC(MP (ARITH_RULE `i = 0 ==> i <= 0`) th) else NO_TAC) THEN
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read PC s = (if b then x else y):int64`) (concl th)
      then REWRITE_RULE[ASSUME `val(word i:int64) = i`;
                        MP (ARITH_RULE `i <= 0 ==> i = 0`) (ASSUME `i <= 0`)] th
      else th) THEN
    ARM_STEPS_TAC HR_EXEC (3--7) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INLINE_HL_ZX]) THEN
    ARM_STEPS_TAC HR_EXEC [8] THEN GLUE_W32_FLAGS_TAC;
    MP_TAC(ARITH_RULE `~(i = 0) ==> i + 79 = 80 + (i - 1)`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `hb:num->byte` (concl th) then
      MP_TAC(SPEC `i + 79` th) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun bth -> ASSUME_TAC(TRANS bth (AP_TERM `hb:num->byte` (ASSUME `i + 79 = 80 + (i - 1)`))))
     else NO_TAC) THEN
    RULE_ASSUM_TAC(fun th -> if concl th = `~(i = 0)` then th
                             else REWRITE_RULE[ASSUME `~(i = 0)`] th) THEN
    ARM_STEPS_TAC HR_EXEC (3--8) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INLINE_HL_ZX]) THEN
    ARM_STEPS_TAC HR_EXEC (9--10) THEN GLUE_W32_FLAGS_TAC];;

let HR_NOTHOK_TAC =
  SUBGOAL_THEN `~(mld_unpack_hints_ret 80 4 hb i = word 0)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`hb:num->byte`; `i:num`] HR_HOK_EQ) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN GLUE_ARITH_TAC; ALL_TAC];;

let HR_FAIL_FINAL_TAC =
  HR_NOTHOK_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN HR_I0_TAC THEN
  VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC [];;

let HR_ST_BOUND = prove
 (`!(hb:num->byte) i. mld_hints_start 80 hb i < 256`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_hints_start] THEN COND_CASES_TAC THEN
  REWRITE_TAC[INLINE_HL_VAL256] THEN ARITH_TAC);;

let HR_X25_TAC k =
  let s = mk_var("s"^string_of_int k,`:armstate`) in
  W(fun (asl,w) ->
    let th = snd(find (fun (_,th) -> is_eq(concl th) &&
                         lhs(concl th) = mk_comb(`read X25`,s)) asl) in
    SUBGOAL_THEN (mk_eq(rhs(concl th),`word (mld_hints_start 80 hb i):int64`))
      (fun eq -> ASSUME_TAC(TRANS th eq)) THENL
     [REWRITE_TAC[mld_hints_start] THEN HR_I0_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC) THEN
      ASM_ARITH_TAC;
      ALL_TAC]) THEN
  FIRST_X_ASSUM(fun th -> if lhs(concl th) = mk_comb(`read X25`,s) &&
                             not(free_in `mld_hints_start` (concl th))
                          then ALL_TAC else NO_TAC) THEN
  ASSUME_TAC(SPECL [`hb:num->byte`; `i:num`] HR_ST_BOUND);;

let HR_ALLOWED = [`hb:num->byte`; `sg:int64`; `fp:int64`; `i:num`; `mf:int64`; `pc:num`];;

let HR_MEMSET_TAC n =
  LIBC_PLT_TAC HR_EXEC n THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" HR_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`]
   (ref HR_ALLOWED) (n + 5);;

let HR_ZERO_TAC k =
  let s = mk_var("s"^string_of_int k,`:armstate`) in
  MP_TAC(SPECL [`word_add (fp:int64) (word 448)`; `256`; s] GLUE_ZERO32) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `word_zx (word 0:int64):byte` (concl th)
                          then ACCEPT_TAC th else NO_TAC);
    DISCH_TAC];;

let HR_HOK_TAC =
  SUBGOAL_THEN `mld_unpack_hints_ret 80 4 hb i = word 0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`hb:num->byte`; `i:num`] HR_HOK_EQ) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REPEAT CONJ_TAC THEN
    REPEAT STRIP_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN GLUE_ARITH_TAC; ALL_TAC];;

(* the 32-bit words of h at join6 in the form of the statement *)

let HR_H_FORM = prove
 (`!(fp:int64) q. word_add (word_add fp (word 448)) (word (4 * q)) =
                  word_add fp (word (448 + 4 * q))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let HR_J6_TAC m =
  ARM_STEPS_TAC HR_EXEC ((m + 1)--(m + 2)) THEN
  ARM_STEPS_TAC HR_EXEC ((m + 3)--(m + 9));;

let HR_I3 = prove
 (`!i. i < 4 ==> (val (word_sub (word i:int64) (word 3)) = 0 <=> i = 3)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV));;

let HR_I3_TAC =
  FIRST_ASSUM(fun th -> if concl th = `i < 4` then
    RULE_ASSUM_TAC(fun t ->
      if can (term_match [] `read PC s = (if b then x else y):int64`) (concl t)
      then REWRITE_RULE[MP (SPEC `i:num` HR_I3) th] t else t) else NO_TAC);;

let HR_HFACT_TAC lem =
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  W(fun (asl,w) ->
    let st = rand(lhs w) in
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in st (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "bytes32" with _ -> false)) (concl th)
      then REWRITE_TAC[MATCH_MP (REWRITE_RULE[HR_H_FORM] th) (ASSUME `q < 256`)]
      else NO_TAC)) THEN
  lem;;

let HR_OK_FINAL_TAC hlem =
  HR_HOK_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [HR_HFACT_TAC hlem; HR_I0_TAC THEN VERIF_EVENTS_ONLY_TAC THEN VERIF_EVENTS_TAC []];;

let HR_NONE_LEM =
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC HR_UNPACK_NONE THEN ASM_ARITH_TAC;;

(*** The truth values of the conditions of the template, for the events ***)
let HR_EVENTS_TAC =
  HR_I0_TAC THEN VERIF_EVENTS_ONLY_TAC THEN HR_COND_TAC THEN HR_COND_TAC THEN
  GLUE_PATH_DISCHARGE_TAC;;

let HR_FAIL_FINAL_TAC =
  HR_NOTHOK_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN HR_EVENTS_TAC;;

let HR_OK_FINAL_TAC hlem =
  HR_HOK_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [HR_HFACT_TAC hlem; HR_EVENTS_TAC];;

let HR_ST = `mld_hints_start 80 (hb:num->byte) i`;;

(*** The peel: x8 = st, the byte hb st, the store h[hb st] := 1 ***)
let HR_PEEL1_TAC m =
  ARM_STEPS_TAC HR_EXEC [m + 1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC HR_ST HR_ZX_SMALL)
                               (SPECL [`hb:num->byte`; `i:num`] HR_ST_BOUND)]) THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `hb:num->byte` (concl th) &&
                           free_in `sg:int64` (concl th) then
    MP_TAC(SPEC HR_ST th) THEN ANTS_TAC THENL [GLUE_ARITH_TAC; DISCH_TAC]
   else NO_TAC) THEN
  ARM_STEPS_TAC HR_EXEC [m + 2] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INLINE_HL_ZX]) THEN
  ASSUME_TAC(SPEC (subst [HR_ST,`st:num`] `(hb:num->byte) st`) INLINE_HL_VAL256) THEN
  ASSUME_TAC(SPEC (subst [HR_ST,`st:num`] `(hb:num->byte) st`) INLINE_HL_VALW) THEN
  ARM_STEPS_TAC HR_EXEC ((m + 3)--(m + 4));;

let HR_H = `word_add (fp:int64) (word 448)`;;
let HR_HB = subst [HR_ST,`st:num`] `val((hb:num->byte) st)`;;

let HR_FRAME_PREP_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `!q. q < 256 ==> read (memory :> bytes32 (word_add h (word (4 * q)))) s = (f:num->int32) q`) (concl th)
    then
      let st = rand(lhs(snd(dest_imp(snd(dest_forall(concl th)))))) in
      SUBGOAL_THEN (subst [HR_HB,`v:num`; st,`s:armstate`]
        `!q. q < 256 /\ ~(q = v)
             ==> read (memory :> bytes32 (word_add (word_add fp (word 448)) (word (4 * q)))) s =
                 word 0`) ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MP_TAC(SPEC `q:num` th) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
        ALL_TAC]
    else NO_TAC);;

let HR_X0 = subst [HR_HB,`v:num`]
  `\q:num. if (v:num) = q then word 1 else word 0:int32`;;

let HR_COMBINE_TAC s =
  SUBGOAL_THEN (subst [s,`s:armstate`; HR_HB,`v:num`]
    `!q. q < 256
         ==> read (memory :> bytes32 (word_add (word_add fp (word 448)) (word (4 * q)))) s =
             (if v = q then word 1 else word 0:int32)`) ASSUME_TAC THENL
   [X_GEN_TAC `q:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[HR_H_FORM] THEN
      FIRST_ASSUM(fun th -> if rhs(concl th) = `word 1:int32` &&
                    can (find_term (fun t -> try fst(dest_const t) = "bytes32" with _ -> false)) (concl th)
                  then ACCEPT_TAC th else NO_TAC);
      FIRST_ASSUM(fun th -> if is_forall(concl th) && is_conj(lhand(snd(dest_forall(concl th))))
                  then MATCH_MP_TAC th else NO_TAC) THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[]];
    ALL_TAC];;

let HR_PEEL2_TAC m =
  HR_FRAME_PREP_TAC THEN
  SUBGOAL_THEN (subst [HR_HB,`v:num`] `nonoverlapping (word_add (word_add fp (word 448)) (word (4 * v)):int64,4) (word pc,libmldsa_size)`)
    ASSUME_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC HR_EXEC [m + 5] THEN
  HR_COMBINE_TAC (mk_var("s"^string_of_int(m + 5),`:armstate`)) THEN
  ARM_STEPS_TAC HR_EXEC [m + 6] THEN
  MP_TAC(SPECL [HR_ST; `val((hb:num->byte)(80 + i))`] HR_EQ1) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun eq -> RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read PC s = (if b then x else y):int64`) (concl th)
      then REWRITE_RULE[eq] th else th));;

let HR_NW = `val((hb:num->byte)(80 + i))`;;

let HR_ONE_LEM =
  MP_TAC(SPECL [`hb:num->byte`; `i:num`; `q:num`] HR_UNPACK_MANY) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [HR_X0; `hb:num->byte`; HR_ST; HR_NW; `q:num`] INLINE_HSET_0) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  BETA_TAC THEN REFL_TAC;;

let HR_MANY_LEM =
  MP_TAC(SPECL [`hb:num->byte`; `i:num`; `q:num`] HR_UNPACK_MANY) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) &&
     (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "inline_hrun" with _ -> false)
     then REWRITE_TAC[th] else NO_TAC);;

let HR_BYTES80_TAC n =
  let s = mk_var("s"^string_of_int n,`:armstate`) in
  SUBGOAL_THEN (subst [s,`s:armstate`]
    `!j. j < 80 ==> read(memory :> bytes8(word_add sg (word j))) s = (hb:num->byte) j`)
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `hb:num->byte` (concl th) &&
                             free_in `84` (concl th)
                          then MATCH_MP_TAC th else NO_TAC) THEN
    UNDISCH_TAC `j < 80` THEN ARITH_TAC;
    ALL_TAC];;

let HR_ZCHK_TAC n lem =
  HR_BYTES80_TAC (n - 1) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc HR_EXEC "H_ZCHK"
   [`read X26 s`; `hb:num->byte`; HR_NW; `pc:num`] HR_ALLOWED n THEN
  MP_TAC(SPECL [`hb:num->byte`; HR_NW] INLINE_ZRUN_FACTS) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> let eq = CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 th))) in
    RULE_ASSUM_TAC(REWRITE_RULE[eq])) THEN
  ASM_CASES_TAC (subst [HR_NW,`w:num`] `inline_zrun hb w = 80`) THENL
   [HR_LOG "zok" (HR_PC_TAC THEN HR_OK_FINAL_TAC lem);
    HR_LOG "zf" (HR_PC_TAC THEN ARM_STEPS_TAC HR_EXEC [n + 1] THEN HR_FAIL_FINAL_TAC)];;

let HR_NOT3_TAC =
  TRY(FIRST_ASSUM(fun th -> if concl th = `i <= 0` then
        UNDISCH_TAC `3 <= i` THEN UNDISCH_TAC `i <= 0` THEN ARITH_TAC else NO_TAC));;

let HR_TAIL_TAC m lem =
  HR_J6_TAC m THEN HR_I3_TAC THEN
  ASM_CASES_TAC `3 <= i` THENL
   [HR_NOT3_TAC THEN HR_PC_TAC THEN ARM_STEPS_TAC HR_EXEC [m + 10] THEN
    GLUE_W32_FLAGS_TAC THEN ARM_STEPS_TAC HR_EXEC [m + 11] THEN
    ASM_CASES_TAC (subst [HR_NW,`w:num`] `w < 80`) THENL
     [HR_PC_TAC THEN HR_ZCHK_TAC (m + 12) lem;
      HR_LOG "ge80" (HR_PC_TAC THEN HR_OK_FINAL_TAC lem)];
    HR_LOG "not3" (HR_PC_TAC THEN HR_OK_FINAL_TAC lem)];;

let HR_MANY_TAC m =
  HR_PC_TAC THEN ARM_STEPS_TAC HR_EXEC ((m + 7)--(m + 9)) THEN HR_X9X10_TAC (m + 9) THEN
  HR_BYTES80_TAC (m + 9) THEN
  SUBGOAL_THEN (mk_binop `(<=):num->num->bool` HR_NW `80`) ASSUME_TAC THENL
   [GLUE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `nonoverlapping (word_add (fp:int64) (word 448),1024) (sg,80)` MP_TAC THENL
   [NONOVERLAPPING_TAC; REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN DISCH_TAC] THEN
  RULE_ASSUM_TAC(fun th -> if is_forall(concl th) then REWRITE_RULE[HR_H_FORM] th else th) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc HR_EXEC "H_HUNP"
   [`sg:int64`; HR_H; `hb:num->byte`; HR_X0; HR_ST; HR_NW; `pc:num`] HR_ALLOWED (m + 10) THEN
  ASM_CASES_TAC (subst [HR_ST,`st:num`; HR_NW,`w:num`] `inline_hrun hb st w = w`) THENL
   [HR_PC_TAC THEN HR_TAIL_TAC (m + 10) HR_MANY_LEM;
    HR_LOG "hf" (HR_PC_TAC THEN ARM_STEPS_TAC HR_EXEC ((m + 11)--(m + 12)) THEN HR_FAIL_FINAL_TAC)];;

let HR_PEEL_TAC m =
  HR_PC_TAC THEN HR_PEEL1_TAC m THEN HR_PEEL2_TAC m THEN
  ASM_CASES_TAC (subst [HR_ST,`st:num`; HR_NW,`w:num`] `st + 1 < w`) THENL
   [HR_MANY_TAC m;
    HR_PC_TAC THEN HR_TAIL_TAC (m + 6) HR_ONE_LEM];;

let HR_GEN_ST_TAC =
  W(fun (asl,w) ->
    if not(free_in HR_ST w) then ALL_TAC else
    SUBGOAL_THEN (mk_binop `(<):num->num->bool` HR_ST `81`) MP_TAC THENL
     [GLUE_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(HR_ST,genvar `:num`) THEN GEN_TAC THEN DISCH_TAC);;

let HR_PATH_DISCHARGE_TAC =
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
       (free_in `hb:num->byte` c || free_in HR_ST c)
    then MP_TAC th else NO_TAC)) THEN
  HR_GEN_ST_TAC THEN GLUE_GEN_BYTES_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let HR_EVENTS_TAC =
  HR_I0_TAC THEN VERIF_EVENTS_ONLY_TAC THEN HR_COND_TAC THEN HR_COND_TAC THEN
  HR_PATH_DISCHARGE_TAC;;

let HR_FAIL_FINAL_TAC =
  HR_NOTHOK_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN FIRST [INLINE_HFRAME_TAC THEN NO_TAC; HR_EVENTS_TAC];;

let HR_OK_FINAL_TAC hlem =
  HR_HOK_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [HR_HFACT_TAC hlem THEN NO_TAC; INLINE_HFRAME_TAC THEN NO_TAC;
         HR_EVENTS_TAC];;


(*** re-bound after the final tactics ***)

let HR_ZCHK_TAC n lem =
  HR_BYTES80_TAC (n - 1) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc HR_EXEC "H_ZCHK"
   [`read X26 s`; `hb:num->byte`; HR_NW; `pc:num`] HR_ALLOWED n THEN
  MP_TAC(SPECL [`hb:num->byte`; HR_NW] INLINE_ZRUN_FACTS) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> let eq = CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 th))) in
    RULE_ASSUM_TAC(REWRITE_RULE[eq])) THEN
  ASM_CASES_TAC (subst [HR_NW,`w:num`] `inline_zrun hb w = 80`) THENL
   [HR_LOG "zok" (HR_PC_TAC THEN HR_OK_FINAL_TAC lem);
    HR_LOG "zf" (HR_PC_TAC THEN ARM_STEPS_TAC HR_EXEC [n + 1] THEN HR_FAIL_FINAL_TAC)];;

let HR_NOT3_TAC =
  TRY(FIRST_ASSUM(fun th -> if concl th = `i <= 0` then
        UNDISCH_TAC `3 <= i` THEN UNDISCH_TAC `i <= 0` THEN ARITH_TAC else NO_TAC));;

let HR_TAIL_TAC m lem =
  HR_J6_TAC m THEN HR_I3_TAC THEN
  ASM_CASES_TAC `3 <= i` THENL
   [HR_NOT3_TAC THEN HR_PC_TAC THEN ARM_STEPS_TAC HR_EXEC [m + 10] THEN
    GLUE_W32_FLAGS_TAC THEN ARM_STEPS_TAC HR_EXEC [m + 11] THEN
    ASM_CASES_TAC (subst [HR_NW,`w:num`] `w < 80`) THENL
     [HR_PC_TAC THEN HR_ZCHK_TAC (m + 12) lem;
      HR_LOG "ge80" (HR_PC_TAC THEN HR_OK_FINAL_TAC lem)];
    HR_LOG "not3" (HR_PC_TAC THEN HR_OK_FINAL_TAC lem)];;

let HR_MANY_TAC m =
  HR_PC_TAC THEN ARM_STEPS_TAC HR_EXEC ((m + 7)--(m + 9)) THEN HR_X9X10_TAC (m + 9) THEN
  HR_BYTES80_TAC (m + 9) THEN
  SUBGOAL_THEN (mk_binop `(<=):num->num->bool` HR_NW `80`) ASSUME_TAC THENL
   [GLUE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `nonoverlapping (word_add (fp:int64) (word 448),1024) (sg,80)` MP_TAC THENL
   [NONOVERLAPPING_TAC; REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN DISCH_TAC] THEN
  RULE_ASSUM_TAC(fun th -> if is_forall(concl th) then REWRITE_RULE[HR_H_FORM] th else th) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc HR_EXEC "H_HUNP"
   [`sg:int64`; HR_H; `hb:num->byte`; HR_X0; HR_ST; HR_NW; `pc:num`] HR_ALLOWED (m + 10) THEN
  ASM_CASES_TAC (subst [HR_ST,`st:num`; HR_NW,`w:num`] `inline_hrun hb st w = w`) THENL
   [HR_PC_TAC THEN HR_TAIL_TAC (m + 10) HR_MANY_LEM;
    HR_LOG "hf" (HR_PC_TAC THEN ARM_STEPS_TAC HR_EXEC ((m + 11)--(m + 12)) THEN HR_FAIL_FINAL_TAC)];;

let HR_PEEL_TAC m =
  HR_PC_TAC THEN HR_PEEL1_TAC m THEN HR_PEEL2_TAC m THEN
  ASM_CASES_TAC (subst [HR_ST,`st:num`; HR_NW,`w:num`] `st + 1 < w`) THENL
   [HR_MANY_TAC m;
    HR_PC_TAC THEN HR_TAIL_TAC (m + 6) HR_ONE_LEM];;

let HR_J5_TAC k =
  HR_X25_TAC k THEN ARM_STEPS_TAC HR_EXEC [k + 1] THEN GLUE_W32_FLAGS_TAC THEN
  ARM_STEPS_TAC HR_EXEC [k + 2] THEN
  ASM_CASES_TAC (subst [HR_ST,`st:num`; HR_NW,`w:num`] `w < st`) THENL
   [TRY(UNDISCH_TAC (subst [HR_ST,`st:num`; HR_NW,`w:num`] `w < st`) THEN
        REWRITE_TAC[mld_hints_start] THEN HR_I0_TAC THEN ASM_REWRITE_TAC[] THEN
        ARITH_TAC THEN NO_TAC) THEN
    HR_LOG "b" (HR_PC_TAC THEN HR_FAIL_FINAL_TAC);
    HR_PC_TAC THEN ARM_STEPS_TAC HR_EXEC ((k + 3)--(k + 7)) THEN MLD_WRAP_GOT_TAC THEN
    HR_MEMSET_TAC (k + 7) THEN HR_ZERO_TAC (k + 12) THEN
    ARM_STEPS_TAC HR_EXEC [k + 13] THEN GLUE_W32_FLAGS_TAC THEN
    ARM_STEPS_TAC HR_EXEC ((k + 14)--(k + 17)) THEN
    ASM_CASES_TAC (subst [HR_ST,`st:num`; HR_NW,`w:num`] `st < w`) THENL
     [HR_PEEL_TAC (k + 17);
      HR_PC_TAC THEN HR_TAIL_TAC (k + 17) HR_NONE_LEM]];;

let HR_SETUP_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_ret_full_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC INLINE_HUNP_LOOP "H_HUNP" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC ZCHK44 "H_ZCHK" THEN
  CONCRETIZE_F_EVENTS_TAC HR_TPL THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `sg:int64`; `hb:num->byte`; `i:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; fst HR_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI];;
let HR_MAIN_TAC =
  HR_SETUP_TAC THEN HR_PREFIX_TAC THENL
   [ASM_CASES_TAC `80 < val((hb:num->byte)(80 + i))` THENL
     [HR_LOG "a0" (ARM_STEPS_TAC HR_EXEC [9] THEN HR_PC_TAC THEN HR_FAIL_FINAL_TAC);
      ARM_STEPS_TAC HR_EXEC [9] THEN HR_PC_TAC THEN HR_J5_TAC 9];
    ASM_CASES_TAC `80 < val((hb:num->byte)(80 + i))` THENL
     [HR_LOG "a1" (HR_PC_TAC THEN ARM_STEPS_TAC HR_EXEC [11] THEN HR_FAIL_FINAL_TAC);
      HR_PC_TAC THEN HR_J5_TAC 10]];;


(* ------------------------------------------------------------------------- *)
(* The lemma.                                                                *)
(* ------------------------------------------------------------------------- *)

let INLINE_HINTS44 = prove(INLINE_HINTS44_TERM, HR_MAIN_TAC);;
