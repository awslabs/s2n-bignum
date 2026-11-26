(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The inlined code of mldsa65_pk_from_sk in the clang 23 -O3 monolithic     *)
(* reduced-RAM build, as lemmas for the proof of its statement: the          *)
(* unpacking of the polynomials of s1 (one block) and s2 (one region each,   *)
(* INLINE_ETA4_65 of inline_eta4.ml), the norm check of each of the six      *)
(* polynomials of s2 (the loops 2 to 7, in the registers of each:            *)
(* INLINE_CHKNORM_LOOP of inline_sign_arith.ml), the comparison of t0 with   *)
(* that in the secret key (loop 8, INLINE_MEMCMP_LOOP) and the SHAKE256 of   *)
(* the public key (KG_SHAKE_PROVE).                                          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_arith.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keygen.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keygen_shake.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_eta4.ml";;

let KG_ETA4_S1 = INLINE_ETA4_65_S1 ();;

let KG_ETA4_P = map INLINE_ETA4_65 (0--5);;

let KG_MEMCMP65 =
  INLINE_MEMCMP_LOOP "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   (INLINE_LOOP_EXEC "mldsa65_pk_from_sk_loop8" "mldsa65_pk_from_sk_loop8_exit")
   "mldsa65_pk_from_sk_loop8" "mldsa65_pk_from_sk_loop8_exit" 78 1536
   ["X8";"X9";"X10";"X11";"X24"];;

let PK65_LOOPS =
  [("loop2","X26"); ("loop3","X28"); ("loop4","X22"); ("loop5","X21");
   ("loop6","X27"); ("loop7","X23")];;

let PK65_CHK_THS =
  map (fun (l,acc) ->
    let ll = "mldsa65_pk_from_sk_" ^ l in
    INLINE_CHKNORM_LOOP "17" "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
      (INLINE_LOOP_EXEC ll (ll ^ "_exit")) ll (ll ^ "_exit") 0
      ["X11"; "X9"; "X8"; "X12"; "X13"; "X10"; acc]) PK65_LOOPS;;

let KG_SHAKE65 = KG_SHAKE_PROVE KG_SHAKE65_INST "X19";;
