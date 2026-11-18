(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of mld_H44, mld_H65 and mld_H87, which absorb up to *)
(* three inputs into one SHAKE256 context: absorbing two messages one after  *)
(* the other (mld_keccak_absorb of common/mldsa_native_fips202.ml, from the  *)
(* position the first one leaves) is absorbing their concatenation.          *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_hash.ml.                           *)

needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "common/fips204/properties/mldsa_native_hash.ml";;

let MLD_H_READ_BYTES_BOUND = prove
 (`!a n (s:armstate) x.
        read (memory :> bytes(a,n)) s = x ==> x < 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let MLD_H_BOUND_TAC a =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read (memory :> bytes(a,n)) s = x:num`) c &&
       fst(dest_pair(rand(rand(rand(rator(lhand c)))))) = a
    then ASSUME_TAC(MATCH_MP MLD_H_READ_BYTES_BOUND th) else NO_TAC);;

let MLD_H_GUARD_ADDR_TAC =
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM WORD_ADD] o check (fun th ->
    can (term_match []
          `read (memory :> bytes64 (word_add (word pc) (word n))) s =
           guard:int64`) (concl th)));;
