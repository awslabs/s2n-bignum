(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of mldsa-native's absorbing of messages *)
(* into Keccak states, copied from the proof of mlk_keccak_absorb_once in    *)
(* mlkem_native/gcc12_O2/keccak_absorb_once.ml (whose code mldsa-native      *)
(* does not have), without the parts that refer to that function. The        *)
(* tactics at the end are for the FULL proofs of the SHAKE functions, which  *)
(* absorb and squeeze.                                                       *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_absorb.ml.                         *)

needs "arm/proofs/utils/mldsa_native_keccak.ml";;
needs "arm/proofs/utils/keccak_fips202.ml";;
needs "arm/proofs/utils/mlkem_native_image.ml";;
needs "arm/proofs/consttime.ml";;
needs "common/fips204/properties/mldsa_native_absorb.ml";;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the arguments, the bytes of the message and the blocks.      *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_SUB = prove
 (`!a:int64 n x k l s:armstate.
        read (memory :> bytes(a,n)) s = x /\ k + l <= n
        ==> read (memory :> bytes(word_add a (word k),l)) s =
            (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(*** The state at a as a 1600-bit word, from it as 200 bytes, and a tactic ***)
(*** applied to that word (as in keccakf1600_permute_spec.ml)              ***)

let KECCAK_STATE_AT_TAC a =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),_)),
           Comb(Const("val",_),_))
        when aa = mk_pair(a,`200`) ->
          ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] th)
    | _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* For absorbing code inlined into its caller, as in                         *)
(* mldsa_shake256x4_absorb_once of the reduced-RAM build (from the proof of  *)
(* mlk_keccak_absorb_once in mlkem_native/gcc12_O3): ABSORB_BRANCH_TAC       *)
(* decides a branch on a comparison with a constant by arithmetic, and       *)
(* ABSORB_DISCHARGE_TAC is DISCHARGE_SAFETY_PROPERTY_TAC, also when the      *)
(* events for the last block are already known from the case of a short      *)
(* message.                                                                  *)
(* ------------------------------------------------------------------------- *)

let ABSORB_BRANCH_TAC =
  TRY(FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),l),Comb(Comb(Comb(Const("COND",_),c),_),_))
        when can (term_match [] `read PC s`) l ->
        (SUBGOAL_THEN c (fun cth -> ASSUME_TAC(REWRITE_RULE[cth] th)) THENL
          [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
        (SUBGOAL_THEN (mk_neg c)
          (fun cth -> ASSUME_TAC(REWRITE_RULE[cth] th)) THENL
          [SIMPLE_ARITH_TAC; ALL_TAC])
    | _ -> NO_TAC));;
