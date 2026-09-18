(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "riscv/proofs/mldsa_ntt_arithmetic.ml";;
needs "common/int_linear.ml";;
needs "common/mlkem_mldsa_linear.ml";;

(* ========================================================================= *)
(* Expanded linear-congruence backend for the forward NTT.                   *)
(* ========================================================================= *)


let RV32_MLDSA_NTT_PHASE1234_LINEAR_BACKEND = {
  rv32_ntt_close_input =
    (fun _ cb -> cb);
  rv32_ntt_close_stage =
    (fun _ _ cb -> cb);
  rv32_ntt_close_output =
    (fun n cb ->
      let ntm = mk_small_numeral n in
      let transform =
        subst
         [ntm,`i:num`]
         `mldsa_bitreverse_forward_ntt
            (ival o (x:num->int32)) i` in
      let speq =
        MLDSA_BITREVERSE_FORWARD_NTT_REORDERED_CONV
          transform in
      let _,args =
        strip_comb(concl(CONJUNCT1 cb)) in
      let layered = List.nth args 1 in
      let bridge_goal =
        subst
         [layered,`l:int`; ntm,`i:num`]
         `(l ==
           mldsa_bitreverse_forward_ntt
             (ival o (x:num->int32)) i)
          (mod &8380417)` in
      (* Reindex the direct specification into the layered input order.
         The generic rule then checks only the resulting linear
         coefficient congruence. *)
      let bridge =
        TAC_PROOF
         (([],bridge_goal),
          REWRITE_TAC[speq; GSYM INT_REM_EQ; o_THM] THEN
          CONV_TAC INT_REM_DOWN_CONV THEN
          REWRITE_TAC[INT_REM_EQ] THEN
          W(fun (_,goal) ->
             ACCEPT_TAC(INT_LINEAR_CONG_RULE goal))) in
      RV32_INT_CONG_TRANS_RULE_FAST
        (CONJUNCT1 cb) bridge)
};;

(* ========================================================================= *)
(* Expanded linear-congruence proof of the forward NTT.                      *)
(* ========================================================================= *)


let RV32_MLDSA_NTT_PHASE1234_LINEAR_CORRECT,
    RV32_MLDSA_NTT_PHASE1234_LINEAR_TIME =
  let start = Sys.time() in
  let theorem =
    RV32_MLDSA_NTT_PHASE1234_PROVE
      RV32_MLDSA_NTT_PHASE1234_LINEAR_BACKEND in
  theorem,Sys.time() -. start;;

(* ========================================================================= *)
(* Compare the structured and expanded forward-NTT arithmetic bridges.       *)
(* ========================================================================= *)


let RV32_MLDSA_NTT_PHASE1234_BACKEND_TIMES =
  let structured =
    RV32_MLDSA_NTT_PHASE1234_CORRECT
  and linear =
    RV32_MLDSA_NTT_PHASE1234_LINEAR_CORRECT in
  let same_hypotheses =
    forall
     (fun h -> exists (aconv h) (hyp linear))
     (hyp structured) &&
    forall
     (fun h -> exists (aconv h) (hyp structured))
     (hyp linear) in
  if not(aconv (concl structured) (concl linear)) then
    failwith
      "phase1234_compare: theorem statements differ"
  else if not same_hypotheses then
    failwith
      "phase1234_compare: theorem hypotheses differ"
  else if hyp structured <> [] then
    failwith
      "phase1234_compare: theorem has assumptions"
  else begin
    Printf.printf
      "RV32_PHASE1234_BACKENDS structured=%.6f \
       linear=%.6f ratio=%.3f assumptions=%d\n%!"
      RV32_MLDSA_NTT_PHASE1234_STRUCTURED_TIME
      RV32_MLDSA_NTT_PHASE1234_LINEAR_TIME
      (RV32_MLDSA_NTT_PHASE1234_LINEAR_TIME /.
       RV32_MLDSA_NTT_PHASE1234_STRUCTURED_TIME)
      (length(hyp structured));
    RV32_MLDSA_NTT_PHASE1234_STRUCTURED_TIME,
    RV32_MLDSA_NTT_PHASE1234_LINEAR_TIME
  end;;
