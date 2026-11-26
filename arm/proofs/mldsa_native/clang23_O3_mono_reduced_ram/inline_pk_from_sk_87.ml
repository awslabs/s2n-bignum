(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The inlined code of mldsa87_pk_from_sk in the clang 23 -O3 monolithic     *)
(* reduced-RAM build, as lemmas for the proof of its statement: the norm     *)
(* check of each of the eight polynomials of s2 (the loops 2 to 9, in the    *)
(* registers of each: INLINE_CHKNORM_LOOP of inline_sign_arith.ml), the      *)
(* comparison of t0 with that in the secret key (loop 10, INLINE_MEMCMPB_LOOP *)
(* of inline_keygen.ml) and the SHAKE256 of the public key (KG_SHAKE_PROVE). *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_arith.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keygen.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keygen_shake.ml";;

let KG_MEMCMP87 =
  INLINE_MEMCMPB_LOOP "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   (INLINE_LOOP_EXEC "mldsa87_pk_from_sk_loop10" "mldsa87_pk_from_sk_loop10_exit")
   "mldsa87_pk_from_sk_loop10" "mldsa87_pk_from_sk_loop10_exit" 104 1568
   ["X8";"X21";"X22";"X9";"X10"] "Q2";;

let PK87_LOOPS =
  [("loop2","X20","X13"); ("loop3","X20","X24"); ("loop4","X20","X25");
   ("loop5","X20","X26"); ("loop6","X20","X27"); ("loop7","X20","X28");
   ("loop8","X22","X20"); ("loop9","X22","X23")];;

let PK87_CHK_THS =
  map (fun (l,a,acc) ->
    let ll = "mldsa87_pk_from_sk_" ^ l in
    INLINE_CHKNORM_LOOP "17" "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
      (INLINE_LOOP_EXEC ll (ll ^ "_exit")) ll (ll ^ "_exit") 0
      ["X10"; a; "X8"; "X11"; "X12"; "X9"; acc]) PK87_LOOPS;;

let KG_SHAKE87 = KG_SHAKE_PROVE KG_SHAKE87_INST "X19";;
