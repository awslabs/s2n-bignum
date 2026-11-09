(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Known-answer tests: evaluate the HOL definitions of common/fips204.ml by  *)
(* proof on NIST ACVP vectors (converted to HOL terms in vectors/ by         *)
(* make_vectors.py), and check the results against the expected values.      *)
(* For example                                                               *)
(*                                                                           *)
(*   mldsa_kat "keygen44";;                                                  *)
(*                                                                           *)
(* returns a theorem |- mldsa_keygen_internal mldsa44 xi = (pk,sk) with      *)
(* explicit byte lists, and reports whether pk and sk are as expected. The   *)
(* signing tests give |- mldsa_sign_internal mldsa44 sk m rnd = SOME sg and  *)
(* the verification tests |- mldsa_verify_internal mldsa44 pk m sg <=> T or  *)
(* <=> F. Each test takes from minutes to hours; independent tests can be    *)
(* run in separate sessions.                                                 *)
(* ========================================================================= *)

needs "tests/mldsa/mldsa_eval.ml";;

(* The vector files call mldsa_kat_vector to record their terms.             *)

let mldsa_kat_vectors = Hashtbl.create 12;;

let mldsa_kat_vector name (fields:(string*term)list) =
  Hashtbl.replace mldsa_kat_vectors name fields;;

let mldsa_kat_ids =
  ["keygen44"; "keygen65"; "keygen87";
   "sign44"; "sign65"; "sign87";
   "verify44_valid"; "verify44_reject"; "verify65_valid"; "verify65_reject";
   "verify87_valid"; "verify87_reject"];;

let mldsa_kat id =
  loadt ("tests/mldsa/vectors/" ^ id ^ ".ml");
  let v = try Hashtbl.find mldsa_kat_vectors id
          with Not_found -> failwith ("mldsa_kat: no vector " ^ id) in
  let get s = assoc s v in
  let has p = String.length id >= String.length p &&
              String.sub id 0 (String.length p) = p in
  let params =
    let n = List.find (fun n -> has ("keygen" ^ n) || has ("sign" ^ n) ||
                                has ("verify" ^ n)) ["44"; "65"; "87"] in
    mk_const("mldsa" ^ n,[]) in
  let call f args = list_mk_comb(mk_icomb(mk_const(f,[]),params),args) in
  let tm,expected =
    if has "keygen" then
      call "mldsa_keygen_internal" [get "xi"],
      mk_pair(get "pk",get "sk")
    else if has "sign" then
      call "mldsa_sign_internal" [get "sk"; get "m"; get "rnd"],
      mk_comb(`SOME:byte list->(byte list)option`,get "sg")
    else
      call "mldsa_verify_internal" [get "pk"; get "m"; get "sg"],
      get "ok" in
  let t0 = Sys.time() in
  let th = MLDSA_TOP_EVAL_CONV tm in
  let ok = rand(concl th) = expected && hyp th = [] in
  Printf.printf "KAT %s: %s (%.0f s)\n%!"
    id (if ok then "PASS" else "FAIL") (Sys.time() -. t0);
  th;;

let mldsa_kat_all () = map mldsa_kat mldsa_kat_ids;;
