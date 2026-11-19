(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing the hints of a signature: the proof (see pack_sig_h_44_spec.ml).  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/pack_sig_h_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_hints.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The proof of GLUE_PSH_FULL_TAC of utils/mldsa_native_hints.ml, for the    *)
(* code at -Os: the registers of the loops differ, memset is called to zero  *)
(* the hints, and the call of the unpacking of w1 comes from the head of the *)
(* loop over the polynomials, with its argument computed from the counter.   *)
(* ------------------------------------------------------------------------- *)

(*** The range test, with the branch the other way round (b.hi) ***)

let GLUE_RANGE_POS_88 = prove
 (`!a:int32.
     (&(val(word_add a (word 95232))) - &190464:int =
      &(val(word_sub (word_add a (word 95232)) (word 190464))) /\
      ~(val(word_sub (word_add a (word 95232)) (word 190464)) = 0)) <=>
     ~glue_hint_inr_88 a`,
  GEN_TAC THEN REWRITE_TAC[GSYM GLUE_RANGE_88] THEN MESON_TAC[]);;

let GLUE_RANGE_POS_32 = prove
 (`!a:int32.
     (&(val(word_add a (word 261888))) - &523776:int =
      &(val(word_sub (word_add a (word 261888)) (word 523776))) /\
      ~(val(word_sub (word_add a (word 261888)) (word 523776)) = 0)) <=>
     ~glue_hint_inr_32 a`,
  GEN_TAC THEN REWRITE_TAC[GSYM GLUE_RANGE_32] THEN MESON_TAC[]);;

(*** The test of the polynomial counter: the code computes k + 1 - K, and ***)
(*** glue_ktest says that this is 0 exactly for the last polynomial        ***)

let glue_ktest = ref TRUTH;;

let GLUE_PSHO_DECIDE_TAC prm =
  let inst = glue_psh_inst prm in
  let hi = inst `(H:num->bool) i`
  and fl = inst `glue_hint_fail OM H i`
  and cnt = inst `mld_hint_count H i`
  and lastp = inst `i DIV 256 < K1` in
  let pcev th =
    let c = concl th in
    is_eq c &&
    (can (term_match [] `read PC s`) (lhs c) ||
     can (term_match [] `read events s`) (lhs c)) in
  let canon eq =
    RULE_ASSUM_TAC(fun th ->
      if pcev th then REWRITE_RULE[eq; NOT_CLAUSES] th else th) in
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; prm.psh_range;
                              GLUE_CCMP_EQ]) THEN
  W(fun (asl,w) ->
    let c0,_ = dest_cond(glue_current_pc (asl,w)) in
    let c = if is_neg c0 then rand c0 else c0 in
    let occurs t = can (find_term ((=) t)) c in
    if is_comb c && is_const(rator c) &&
       mem (fst(dest_const(rator c))) ["glue_hint_inr_88"; "glue_hint_inr_32"]
    then
      GLUE_PSH_CASES_TAC c THENL
       [ALL_TAC;
        SUBGOAL_THEN hi ASSUME_TAC THENL
         [REWRITE_TAC[prm.psh_unfold] THEN MATCH_MP_TAC prm.psh_out THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC]]
    else if is_conj c then
      SUBGOAL_THEN (mk_iff(c,hi)) canon THENL
       [REWRITE_TAC[prm.psh_unfold] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC prm.psh_inr THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      GLUE_PSH_CASES_TAC hi THENL
       [ALL_TAC;
        SUBGOAL_THEN (mk_neg fl) ASSUME_TAC THENL
         [REWRITE_TAC[glue_hint_fail] THEN ASM_REWRITE_TAC[]; ALL_TAC]]
    else if occurs cnt then
      SUBGOAL_THEN (mk_iff(c,fl)) canon THENL
       [REWRITE_TAC[glue_hint_fail; ASSUME hi] THEN
        MATCH_MP_TAC GLUE_W32_EQ THEN CONV_TAC NUM_REDUCE_CONV THEN
        SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      GLUE_PSH_CASES_TAC fl THENL
       [ALL_TAC;
        SUBGOAL_THEN (inst `mld_hint_count H i < OM`) ASSUME_TAC THENL
         [UNDISCH_TAC (mk_neg fl) THEN
          REWRITE_TAC[glue_hint_fail; ASSUME hi] THEN SIMPLE_ARITH_TAC;
          ALL_TAC]]
    else if occurs `i MOD 256` then
      canon(MP (SPEC `i MOD 256` GLUE_J_TEST) (ASSUME `i MOD 256 < 256`))
      THEN GLUE_PSH_CASES_TAC `i MOD 256 < 255` THENL
       [MP_TAC(CONJUNCT1(SPEC `i:num` GLUE_MOD_NEXT));
        MP_TAC(CONJUNCT2(SPEC `i:num` GLUE_MOD_NEXT))] THEN
      (ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC])
    else
      SUBGOAL_THEN (mk_iff(c,mk_neg lastp)) canon THENL
       [REWRITE_TAC[VAL_EQ_0] THEN
        FIRST [REWRITE_TAC[WORD_SUB_EQ_0] THEN GLUE_WORD_SMALL_TAC;
               MP_TAC(SPEC `i DIV 256` !glue_ktest) THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      GLUE_PSH_CASES_TAC lastp);;


(*** The address of the w1 bytes of the next polynomial, as the code ***)
(*** computes it with val of the counter plus one ***)

let GLUE_X1_ADDR = prove
 (`!(w:int64) k n. k < 4294967296
     ==> word(val w + val(word_add (word k:int64) (word 1)) * n) =
         word_add w (word(n * (k + 1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add (word k:int64) (word 1)) = k + 1`
   SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `k + 1 < 18446744073709551616` ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `k MOD 18446744073709551616 = k` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD; WORD_VAL; MULT_SYM]);;

let GLUE_X1_SHL = prove
 (`!k. word_shl (word_add (word k:int64) (word 1)) 7 = word(128 * (k + 1))`,
  GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC WORD_BLAST);;

let glue_psho_vars =
  [`x:num->int32`; `b:num->byte`; `sig:int64`; `w0:int64`; `w1p:int64`;
   `scratch:int64`; `mf:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `i:num`];;

let GLUE_PSHO_CALL_TAC prm (b':term) (slice:term) n =
  let sv = mk_var("s"^string_of_int(n-1),`:armstate`) in
  SUBGOAL_THEN (vsubst [sv,`s:armstate`] slice) ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc prm.psh_exec "H_UNPACK"
   [`read X0 s`; `read X1 s`; b'; `pc:num`; `read X30 s`] glue_psho_vars n;;

let rec GLUE_PSHO_RUN_TAC prm n (asl,w) =
  let inst = glue_psh_inst prm in
  let base = layout prm.psh_fn in
  let lbl l = layout(prm.psh_fn ^ "_" ^ l) - base in
  let pct = glue_current_pc (asl,w) in
  let off = glue_pc_offset base pct in
  if n > 1 && (off = lbl "loop2" || off = lbl "join3") then
    GLUE_PSH_FINAL_TAC prm (asl,w)
  else if off + base = layout prm.psh_callee then
    (MP_TAC(SPECL [`w1p:int64`; `i DIV 256`;
                   mk_small_numeral prm.psh_wbytes] GLUE_X1_ADDR) THEN
     ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[SPEC `i DIV 256` GLUE_X1_SHL]) THEN
     GLUE_PSHO_CALL_TAC prm
       (inst `\t. (b:num->byte)(WB * (i DIV 256 + 1) + t)`)
       (inst `!j. j < WB
                  ==> read(memory :> bytes8
                        (word_add w1p (word(WB * (i DIV 256 + 1) + j)))) s =
                      (b:num->byte)(WB * (i DIV 256 + 1) + j)`) n THEN
     GLUE_PSHO_RUN_TAC prm (n + 1)) (asl,w)
  else
    (ARM_STEPS_TAC prm.psh_exec [n] THEN TRY GLUE_PSH_EVENTS_TAC THEN
     (fun g -> if is_cond(glue_current_pc g) then GLUE_PSHO_DECIDE_TAC prm g
               else ALL_TAC g) THEN
     GLUE_PSHO_RUN_TAC prm (n + 1)) (asl,w);;

let GLUE_PSHO_BODY_TAC prm =
  let inst = glue_psh_inst prm in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ASSUME(inst `i < glue_hint_steps OM NN H`)] THEN
  FULL_INIT_TAC THEN GLUE_PSH_PREP_TAC prm THEN GLUE_PSHO_RUN_TAC prm 1;;

(*** The events template, as for the code at -O2 ***)

let glue_psho_template prm = glue_psh_inst prm
 `\(x:num->int32) (b:num->byte) (sig:int64) (w0:int64) (w1p:int64)
   (scratch:int64) (mf:int64) (pc:num) (stackpointer:int64)
   (returnaddress:int64).
   APPEND
    (f_ev_epil x b sig w0 w1p scratch mf pc stackpointer returnaddress)
    (APPEND
      (ENUMERATEL (glue_hint_steps OM NN (HF x b))
        (\p. if glue_hint_fail OM (HF x b) p
             then if IF (x p)
                  then f_ev_f2 x b sig w0 w1p scratch mf pc stackpointer
                               returnaddress p
                  else f_ev_f1 x b sig w0 w1p scratch mf pc stackpointer
                               returnaddress p
             else if p MOD 256 < 255
             then if HF x b p
                  then if IF (x p)
                       then f_ev_m2 x b sig w0 w1p scratch mf pc stackpointer
                                    returnaddress p
                       else f_ev_m1 x b sig w0 w1p scratch mf pc stackpointer
                                    returnaddress p
                  else f_ev_m3 x b sig w0 w1p scratch mf pc stackpointer
                               returnaddress p
             else if p DIV 256 < K1
             then if HF x b p
                  then if IF (x p)
                       then f_ev_e2 x b sig w0 w1p scratch mf pc stackpointer
                                    returnaddress p
                       else f_ev_e1 x b sig w0 w1p scratch mf pc stackpointer
                                    returnaddress p
                  else f_ev_e3 x b sig w0 w1p scratch mf pc stackpointer
                               returnaddress p
             else if HF x b p
             then if IF (x p)
                  then f_ev_l2 x b sig w0 w1p scratch mf pc stackpointer
                               returnaddress p
                  else f_ev_l1 x b sig w0 w1p scratch mf pc stackpointer
                               returnaddress p
             else f_ev_l3 x b sig w0 w1p scratch mf pc stackpointer
                          returnaddress p))
      (f_ev_prol x b sig w0 w1p scratch mf pc stackpointer returnaddress))
   :(uarch_event)list`;;


(*** The invariant at the head of the loop over the positions for -Os: ***)

let glue_psho_inv prm = glue_psh_inst prm
 `\i s.
  read SP s = stackpointer /\
  read X21 s = sig /\ read X22 s = scratch /\ read X23 s = w0 /\
  read X24 s = w1p /\ read X25 s = word_add sig (word SH) /\
  read X26 s = word WB /\ read X27 s = word GA /\ read X28 s = word G2 /\
  read (memory :> bytes64 stackpointer) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 8))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 16))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 32))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 40))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 48))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 56))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 64))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 72))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 80))) s =
    returnaddress /\
  (!q. q < NN
       ==> read(memory :> bytes32(word_add w0 (word(4 * q)))) s = x q) /\
  (!j. j < WK ==> read(memory :> bytes8(word_add w1p (word j))) s = b j) /\
  (i < glue_hint_steps OM NN H
   ==> read X4 s = word(i MOD 256) /\
       read X19 s = word(i DIV 256) /\
       read X20 s = word(mld_hint_count H i) /\
       read X1 s = word_add w0 (word(1024 * i DIV 256)) /\
       read X2 s = word GN /\
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
   ==> read X0 s = word_zx(mld_pack_hints_ret OM KK H))`;;

(*** The bytes of the hints and of their counts after the call of memset ***)

let GLUE_PSHO_ZBYTES_TAC prm =
  let inst = glue_psh_inst prm in
  let pat = `!i. i < n ==> read(memory :> bytes8
                              (word_add sig (word(c + i)))) s = v` in
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] pat) (concl th) then
      FIRST
       [MP_TAC(SPEC (inst `OM + t`) th) THEN ANTS_TAC THENL
         [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV;
        MP_TAC(SPEC `t:num` th) THEN ANTS_TAC THENL
         [SIMPLE_ARITH_TAC; ALL_TAC]] THEN
      REWRITE_TAC[WORD_ZX_0]
    else NO_TAC);;

(*** The code before the loop: the call of memset for the hints, with the ***)
(*** zero bytes of its result, and the call for polynomial 0, from step n ***)

let rec GLUE_PSHO_PRO_TAC prm n (asl,w) =
  let inst = glue_psh_inst prm in
  let base = layout prm.psh_fn in
  let off = glue_pc_offset base (glue_current_pc (asl,w)) in
  if off = layout(prm.psh_fn ^ "_loop2") - base then
    (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[mld_hint_count; mld_hint_index; WORD_ADD_0; ADD_CLAUSES;
                 ETA_AX; CONJUNCT1 LT] THEN
     ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(0 = n)`] THEN
     REPEAT CONJ_TAC THEN
     TRY(GLUE_PSHO_ZBYTES_TAC prm THEN NO_TAC) THEN
     DISCHARGE_SAFETY_PROPERTY_TAC) (asl,w)
  else if off + base = layout prm.psh_callee then
    (RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; WORD_VAL; WORD_ADD_0]) THEN
     TRY(GLUE_REG_TAC `X1` `w1p:int64`) THEN
     GLUE_PSHO_CALL_TAC prm `b:num->byte`
      (inst `!j. j < WB
                 ==> read(memory :> bytes8(word_add w1p (word j))) s =
                     (b:num->byte) j`) n THEN
     GLUE_PSHO_PRO_TAC prm (n + 1)) (asl,w)
  else
    (ARM_STEPS_TAC prm.psh_exec [n] THEN
     GLUE_PSHO_PRO_TAC prm (n + 1)) (asl,w);;

(*** The whole proof for the code that calls memset, given the FULL ***)
(*** theorem for unpacking w1; n0 is the step of the call of memset ***)

let GLUE_PSHO_FULL_TAC prm n0 calleeth =
  let inst = glue_psh_inst prm in
  let np = inst `glue_hint_steps OM NN H` in
  let lbl l =
    mk_binary "+" (`pc:num`,mk_small_numeral(layout(prm.psh_fn ^ "_" ^ l))) in
  REPEAT GEN_TAC THEN REWRITE_TAC[memset_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC calleeth "H_UNPACK" THEN
  CONCRETIZE_F_EVENTS_TAC (glue_psho_template prm) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst prm.psh_exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`]
                                WORD_ADD]) THEN
  MP_TAC(SPECL [glue_psh_hint prm; mk_small_numeral prm.psh_omega;
                mk_small_numeral(256 * prm.psh_k)] GLUE_HINT_STEPS) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC np (lbl "loop2") (lbl "join3")
    (glue_psho_inv prm) THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC;
    FULL_INIT_TAC THEN
    ARM_STEPS_TAC prm.psh_exec (1--n0) THEN
    LIBC_PLT_TAC prm.psh_exec n0 THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" prm.psh_exec
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `read X30 s`]
     (ref (butlast glue_psho_vars)) (n0 + 5) THEN
    GLUE_PSHO_PRO_TAC prm (n0 + 6);
    GLUE_PSHO_BODY_TAC prm;
    GLUE_PSH_EXIT_TAC prm];;

(*** The test of the polynomial counter for 4 polynomials ***)

let GLUE_KTEST_44 = prove
 (`!k. k < 4
       ==> ((word_add (word k) (word 18446744073709551613):int64 = word 0) <=>
            ~(k < 3))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

glue_ktest := GLUE_KTEST_44;;

let GLUE_PSH_PARAMS_44 =
   {psh_exec = MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_EXEC;
    psh_fn = "mldsa44_pack_sig_h";
    psh_callee = "mldsa_polyw1_unpack_88";
    psh_hintf = `mld_polyvec_make_hint_88`;
    psh_inrf = `glue_hint_inr_88`;
    psh_unpackf = `mld_polyw1_unpack_88`;
    psh_range = CONJ GLUE_RANGE_88 GLUE_RANGE_POS_88;
    psh_inr = GLUE_HINT_INR_88;
    psh_out = GLUE_HINT_OUT_88;
    psh_unfold = GLUE_POLYVEC_HINT_88;
    psh_omega = 80; psh_k = 4; psh_wbytes = 192;
    psh_sigh = 2336;
    psh_gamma = 95232};;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with one loop over *)
(* the 1024 positions of the vector, as GLUE_PSH_FULL_TAC does it.           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  GLUE_PSHO_FULL_TAC GLUE_PSH_PARAMS_44 22
   MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
       MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
       MLDSA_NATIVE_PACK_SIG_H_44_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)));;
