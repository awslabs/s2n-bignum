(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The inlined code of mldsa44_pk_from_sk in the clang 23 -O3 monolithic     *)
(* reduced-RAM build, as lemmas for the proof of its statement: the norm     *)
(* check of each of the four polynomials of s2 (the loops 2 to 5, in the     *)
(* registers of each: INLINE_CHKNORM_LOOP of inline_sign_arith.ml), the      *)
(* comparison of t0 with that in the secret key (loop 6, INLINE_MEMCMP_LOOP) *)
(* and the SHAKE256 of the public key (KG_SHAKE_PROVE).                      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_arith.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keygen.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keygen_shake.ml";;

let KG_MEMCMP44 =
  INLINE_MEMCMP_LOOP "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   (INLINE_LOOP_EXEC "mldsa44_pk_from_sk_loop6" "mldsa44_pk_from_sk_loop6_exit")
   "mldsa44_pk_from_sk_loop6" "mldsa44_pk_from_sk_loop6_exit" 52 896
   ["X8";"X9";"X10";"X11";"X27"];;

let PK44_LOOPS =
  [("loop2","X23","X22"); ("loop3","X25","X23");
   ("loop4","X26","X25"); ("loop5","X28","X26")];;

let PK44_CHK_THS =
  map (fun (l,a,acc) ->
    let ll = "mldsa44_pk_from_sk_" ^ l in
    INLINE_CHKNORM_LOOP "17" "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
      (INLINE_LOOP_EXEC ll (ll ^ "_exit")) ll (ll ^ "_exit") 0
      ["X10"; a; "X8"; "X11"; "X12"; "X9"; acc]) PK44_LOOPS;;

let KG_SHAKE44 = KG_SHAKE_PROVE KG_SHAKE44_INST "X19";;
