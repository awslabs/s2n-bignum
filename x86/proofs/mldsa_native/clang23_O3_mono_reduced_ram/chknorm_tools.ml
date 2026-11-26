(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proofs of mldsa{44,65,87}_polyvecl_chknorm in the clang 23 build,     *)
(* which has inlined mldsa_poly_chknorm: L loops over the 256 coefficients   *)
(* of the polynomials in turn. Loop k keeps the index of the coefficient in  *)
(* a register idx_k and the OR of its masks in acc_k, which differ from loop *)
(* to loop, with the masks of the earlier polynomials in the registers of    *)
(* their loops. Some of the callee-saved registers are pushed between two    *)
(* of the loops, when the code needs them, and popped at the end. The        *)
(* proofs differ in the numbers and the registers: chk_cfg gives them.       *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_polyvec.ml";;
needs "x86/proofs/utils/mldsa_native_scalar.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/clang_tools.ml";;

(*** The absolute value as the code selects it, with the mask of the sign ***)

let MLD_CT_ABS_SELECT = prove
 (`!y:int32. mld_ct_abs y =
             word_xor (word_and (word_xor (word_neg y) y) (word_ishr y 31)) y`,
  REWRITE_TAC[mld_ct_abs; GSYM MSB_IVAL; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC);;

let WORD_OR_ONES_32 = prove
 (`!y:int32. word_or (word 4294967295) y = word 4294967295`,
  BITBLAST_TAC);;

let EXISTS_LT_SUC_SPLIT = prove
 (`!P i. (?j. j < i + 1 /\ P j) <=> (?j. j < i /\ P j) \/ P i`,
  REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN MESON_TAC[]);;

(*** The code takes the mask from the sign-extended difference with a
     logical shift, which gives the same low 32 bits as the shift by 31 of
     the difference ***)

let WORD_ZX_USHR_SX_31 = prove
 (`!x:int32. word_zx(word_ushr (word_sx x:int64) 31):int32 = word_ishr x 31`,
  BITBLAST_TAC);;

(*** The code forms the difference B - 1 - |x i| as B + ~|x i| ***)

let CHK_NOT_ADD = WORD_RULE
 `!y b:int32. word_add (word_not y) b = word_sub (word_sub b (word 1)) y`;;

let VAL_WORD_SMALL_IDX = prove
 (`!i. i < 256 ==> val(word i:int64) = i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The configuration: the number L of polynomials, the registers of the      *)
(* accumulators and the indexes of the loops, the number of steps before     *)
(* each loop, the loop after whose exit the registers are pushed (counted    *)
(* from 0, with the registers in the order of the pushes), the number of     *)
(* steps of the return, and the name of the function and its EXEC theorem.   *)
(* ------------------------------------------------------------------------- *)

type chk_cfg =
 { chk_l : int; chk_acc : string list; chk_idx : string list;
   chk_mids : int list; chk_push : int; chk_pushed : string list;
   chk_ret : int; chk_name : string; chk_exec : thm * thm option array;
   chk_lowreg : string -> string };;

(*** The coefficient j of polynomial k of x ***)

let chk_coef k j =
  if k = 0 then Printf.sprintf "x(%s)" j
  else Printf.sprintf "x(%d + %s)" (256 * k) j;;

let chk_partial k =
  Printf.sprintf "word_zx(if ?j. j < i /\\ ival(word_sub (word_sub (word_zx (bnd:int64)) (word 1)) (mld_ct_abs(%s))) < &0 then word 4294967295 else word 0:int32)" (chk_coef k "j");;

let chk_result j =
  Printf.sprintf "word_zx(mld_poly_chknorm (mld_poly_of x %d) (word_zx (bnd:int64)))" j;;

(*** The facts about the frame: RSP, the return address, and the registers
     to be saved, still in their registers before they are pushed, and in
     the frame after ***)

let chk_common cfg k =
  let p = length cfg.chk_pushed in
  let pushed = k >= cfg.chk_push in
  let sp = if pushed then "stackpointer"
           else Printf.sprintf "word_add stackpointer (word %d)" (8 * p) in
  let regs =
    if pushed then
      mapi (fun j r ->
        let off = 8 * (p - 1 - j) in
        if off = 0 then
          Printf.sprintf "read (memory :> bytes64 stackpointer) s = %s_init"
            (cfg.chk_lowreg r)
        else
          Printf.sprintf "read (memory :> bytes64 (word_add stackpointer (word %d))) s = %s_init"
            off (cfg.chk_lowreg r)) cfg.chk_pushed
    else map (fun r -> Printf.sprintf "read %s s = %s_init" r (cfg.chk_lowreg r))
             cfg.chk_pushed in
  Printf.sprintf "read RDI s = v /\\ read RSI s = bnd /\\ read RSP s = %s /\\ \
           read (memory :> bytes64 (word_add stackpointer (word %d))) s = returnaddress /\\ \
           %s /\\ \
           (!j. j < %d ==> read(memory :> bytes32(word_add v (word(4 * j)))) s = x j)"
    sp (8 * p) (end_itlist (fun a b -> a ^ " /\\ " ^ b) regs) (256 * cfg.chk_l);;

(*** The invariant of loop k for iteration i ***)

let chk_inv cfg k =
  let earlier = map (fun j ->
    Printf.sprintf "read %s s = %s" (el j cfg.chk_acc) (chk_result j))
    (0--(k-1)) in
  parse_term
   (Printf.sprintf "\\i s. read %s s = word i /\\ read %s s = %s /\\ %s%s"
      (el k cfg.chk_idx) (el k cfg.chk_acc) (chk_partial k)
      (chk_common cfg k)
      (itlist (fun t r -> " /\\ " ^ t ^ r) earlier ""));;

(*** The state at the exit of loop k, with the results of the loops so far ***)

let chk_exit cfg k =
  let rs = map (fun j ->
    Printf.sprintf "read %s s = %s" (el j cfg.chk_acc) (chk_result j))
    (0--k) in
  parse_term
   (Printf.sprintf "\\s. %s%s" (chk_common cfg k)
      (itlist (fun t r -> " /\\ " ^ t ^ r) rs ""));;

(* ------------------------------------------------------------------------- *)
(* The addresses of the coefficients: for loop k the simulation addresses    *)
(* them as word_add v (word(4 * val(word i) + 1024 * k)), as the index       *)
(* register holds word i, and the facts about them must have that form.      *)
(* ------------------------------------------------------------------------- *)

let IDX_ALT_ADDR_TAC k =
  let c = 256 * k in
  let t =
    if k = 0 then
      `read (memory :> bytes32 (word_add v (word (4 * val (word i:int64))))) s0
       = (x:num->int32) i`
    else
      parse_term(Printf.sprintf
       "read (memory :> bytes32 (word_add v (word (4 * val (word i:int64) + %d)))) s0 = (x:num->int32) (%d + i)"
       (4 * c) c) in
  let eq =
    if k = 0 then `4 * i = 4 * i` else
    parse_term(Printf.sprintf "4 * i + %d = 4 * (%d + i)" (4 * c) c) in
  SUBGOAL_THEN t ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word i:int64) = i` SUBST1_TAC THENL
     [ASM_SIMP_TAC[VAL_WORD_SMALL_IDX]; ALL_TAC] THEN
    (if k = 0 then ALL_TAC
     else SUBGOAL_THEN eq (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

(*** One iteration of loop k: the mask of coefficient i is ORed into acc_k.
     The loop test is the end of the body. ***)

let chk_body_pre cfg k =
  let idx = if k = 0 then `i:num` else
            mk_binop `(+):num->num->num` (mk_small_numeral(256 * k)) `i:num` in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC idx o check (fun th ->
    is_forall(concl th) && free_in `x:num->int32` (concl th) &&
    free_in `v:int64` (concl th))) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  IDX_ALT_ADDR_TAC k THEN
  X86_STEPS_TAC cfg.chk_exec (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC;;

let chk_body_post k =
  let ex = parse_term(Printf.sprintf
    "?j. j < i /\\ ival(word_sub (word_sub (word_zx (bnd:int64)) (word 1)) \
                         (mld_ct_abs(%s))) < &0" (chk_coef k "j")) in
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(W(fun (asl,w) ->
        if can (find_term (fun t -> is_const t && name_of t = "mld_ct_abs")) w
        then NO_TAC else CONV_TAC WORD_RULE THEN NO_TAC)) THEN
  TRY(REWRITE_TAC[EXISTS_LT_SUC_SPLIT] THEN ASM_REWRITE_TAC[] THEN
      SPEC_TAC(ex,`p:bool`) THEN GEN_TAC THEN ASM_CASES_TAC `p:bool` THEN
      ASM_REWRITE_TAC[] THENL
       [REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_SX_32_64_32;
                    WORD_ZX_USHR_SX_31; WORD_OR_ONES_32];
        REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_ZX_SX_32_64_32;
                    WORD_ZX_USHR_SX_31] THEN
        REWRITE_TAC[WORD_OR_0; WORD_ISHR_31_COND; MLD_CT_ABS_SELECT;
                    CHK_NOT_ADD]] THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let chk_body_tac cfg k = chk_body_pre cfg k THEN chk_body_post k;;

(*** The code before the loop: init_steps steps from the entry or from the
     exit of the previous loop, and the exit of the loop, whose state is the
     invariant for 256 with the result in place of the partial result ***)

let chk_loop_init cfg init_steps =
  VEC_FULL_INIT_TAC cfg.chk_exec init_steps
    [mld_poly_chknorm; mld_poly_of; WORD_ZX_0; LT; EXISTS_SIMP];;

(*** The events at the exit of a loop k > 0 whose code before it has no
     events (for the loop after the pushes, the stores of the pushes are
     events and the standard tactic applies). So that the unifier of DISCHARGE_SAFETY_PROPERTY_TAC meets
     APPEND enum Z = APPEND (APPEND f_ev enum) Z, which it does not know:
     here f_ev is [] by NIL_IMPLIES_APPEND_EQ. ***)

let CHK_EXIT_EVENTS_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [PURE_REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN
    CONJ_TAC THENL [REFL_TAC; UNIFY_F_EVENTS_TAC];
    ALL_TAC] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let chk_loop_exit cfg k =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[mld_poly_chknorm; mld_poly_of; MULT_CLAUSES;
                  ADD_CLAUSES] THEN
  TRY(CONV_TAC(DEPTH_CONV NUM_MULT_CONV)) THEN
  REPEAT CONJ_TAC THEN
  TRY(REFL_TAC THEN NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  (if k = 0 || k = cfg.chk_push then DISCHARGE_SAFETY_PROPERTY_TAC
   else CHK_EXIT_EVENTS_TAC);;

let chk_lbl cfg n =
  parse_term(Printf.sprintf "pc + %s_%s" cfg.chk_name n);;

(*** Report the part of the proof in which a tactic fails ***)

let chk_wrap name (tac:tactic) : tactic = fun g ->
  try tac g with ex ->
    (Printf.printf "chknorm: failure in %s\n%!" name; raise ex);;

let chk_loop_tac cfg k =
  ENSURES_EVENTS_WHILE_UP2_TAC `256`
   (chk_lbl cfg (Printf.sprintf "loop%d" (k + 1)))
   (chk_lbl cfg (Printf.sprintf "loop%d_exit" (k + 1))) (chk_inv cfg k) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    chk_wrap (Printf.sprintf "the code before loop %d" k)
     (chk_loop_init cfg (el k cfg.chk_mids));
    chk_wrap (Printf.sprintf "the body of loop %d" k) (chk_body_tac cfg k);
    chk_wrap (Printf.sprintf "the exit of loop %d" k) (chk_loop_exit cfg k)];;

(*** The template of the events: one segment for each loop, the code before
     it and its loop, and the return ***)

let chk_template cfg =
  let args = [`v:int64`; `bnd:int64`; `pc:num`; `stackpointer:int64`;
              `returnaddress:int64`] in
  let fty = itlist (fun a t -> mk_fun_ty (type_of a) t) args
                   `:(uarch_event)list` in
  let ityp = itlist (fun a t -> mk_fun_ty (type_of a) t) args
                    (mk_fun_ty `:num` `:(uarch_event)list`) in
  let app n = list_mk_comb(mk_var(n,fty),args) in
  let ap = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` in
  let mk_ap a b = list_mk_comb(ap,[a;b]) in
  let enum k =
    let fl = list_mk_comb(mk_var("f_ev_loop" ^ string_of_int k,ityp),args) in
    list_mk_comb(`ENUMERATEL:num->(num->(uarch_event)list)->(uarch_event)list`,
                 [`256`; mk_abs(`i:num`,mk_comb(fl,`i:num`))]) in
  let seg k = mk_ap (app("f_ev_exit" ^ string_of_int k))
                    (mk_ap (enum k) (app("f_ev_pre" ^ string_of_int k))) in
  let segs = map seg (1--cfg.chk_l) in
  let body = mk_ap (app "f_ev_ret")
              (end_itlist mk_ap (rev segs)) in
  list_mk_abs(args,body);;

(*** The return: the value is the OR of the results of the loops, in the
     other order of the association than mld_polyvec_chknorm. ***)

let CHK_POLYVEC_UNFOLD l =
  let suc = prove
   (`!n (x:num->int32) B.
       mld_polyvec_chknorm (n + 1) x B =
       word_or (mld_polyvec_chknorm n x B) (mld_poly_chknorm (mld_poly_of x n) B)`,
    REWRITE_TAC[GSYM ADD1; mld_polyvec_chknorm]) in
  CONJUNCT1 mld_polyvec_chknorm ::
  map (fun n ->
    CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
      (SPECL [mk_small_numeral n; `x:num->int32`; `B:int32`] suc)) (0--(l-1));;

(*** The OR of the results in the order of the code (the last loop first),
     and in the order of mld_polyvec_chknorm ***)

let CHK_OR_LEMMA l =
  let ps = map (fun i -> mk_var("p" ^ string_of_int i,`:int32`)) (0--(l-1)) in
  let wor a b = mk_comb(mk_comb(`word_or:int32->int32->int32`,a),b) in
  let code = end_itlist wor (rev ps) in
  let spec = List.fold_left wor (hd ps) (tl ps) in
  prove(list_mk_forall(ps,mk_eq(code,spec)),
        REPEAT GEN_TAC THEN BITBLAST_TAC);;

let chk_ret_tac cfg =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC cfg.chk_exec (1--cfg.chk_ret) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC (CHK_POLYVEC_UNFOLD cfg.chk_l @
                   [WORD_OR_0; WORD_ZX_ZX_32_64_32]) THEN
  REPEAT CONJ_TAC THEN
  TRY(AP_TERM_TAC THEN MATCH_ACCEPT_TAC(CHK_OR_LEMMA cfg.chk_l) THEN NO_TAC) THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The whole proof of the FULL theorem ***)

let chk_full_tac cfg =
  let p = length cfg.chk_pushed in
  let rec seq k =
    if k = 0 then chk_loop_tac cfg 0 else
    ENSURES_EVENTS_SEQUENCE_TAC
     (chk_lbl cfg (Printf.sprintf "loop%d_exit" k)) (chk_exit cfg (k - 1)) THEN
    CONJ_TAC THENL [seq (k - 1); chk_loop_tac cfg k] in
  CONCRETIZE_F_EVENTS_TAC (chk_template cfg) THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; NONOVERLAPPING_CLAUSES; ALL; fst cfg.chk_exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  EVERY(map (fun r ->
    ENSURES_PRESERVED_TAC (cfg.chk_lowreg r ^ "_init") (parse_term r))
    cfg.chk_pushed) THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   (chk_lbl cfg (Printf.sprintf "loop%d_exit" cfg.chk_l))
   (chk_exit cfg (cfg.chk_l - 1)) THEN
  CONJ_TAC THENL
   [seq (cfg.chk_l - 1);
    chk_wrap "the return" (chk_ret_tac cfg)];;
