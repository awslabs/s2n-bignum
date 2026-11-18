(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of mldsa-native's absorbing of messages *)
(* into Keccak states, as in arm/proofs/utils/mldsa_native_absorb.ml (those  *)
(* of the proof of mlk_keccak_absorb_once of mlkem-native), for the x86      *)
(* state and without the parts for the AArch64 code. Unlike that file, it    *)
(* does not load utils/keccak_fips202.ml, which takes minutes to load, so    *)
(* that the proofs that do not need it load quickly. The tactics at the end  *)
(* are for the FULL proofs of the SHAKE functions, which absorb and squeeze. *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/consttime.ml";;
needs "common/fips204/properties/mldsa_native_absorb.ml";;

(* ------------------------------------------------------------------------- *)
(* Tactics for the arguments and the flags.                                  *)
(* ------------------------------------------------------------------------- *)

(*** The values of the 64-bit words for r and mlen ***)

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
