(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Known-answer tests: evaluate the HOL definitions of common/fips203.ml by  *)
(* proof on NIST ACVP vectors (converted to HOL terms in vectors/ by         *)
(* make_vectors.py), and check the results against the expected values.      *)
(* For example                                                               *)
(*                                                                           *)
(*   mlkem_kat "keygen512";;                                                 *)
(*                                                                           *)
(* returns a theorem |- mlkem_keygen_internal mlkem512 d z = (ek,dk) with    *)
(* explicit byte lists, and reports whether ek and dk are as expected. Each  *)
(* test takes 10-70 minutes, almost all of it in Keccak, so mlkem_kat_all    *)
(* takes several hours; independent tests can be run in separate sessions.   *)
(* ========================================================================= *)

needs "tests/mlkem/mlkem_eval.ml";;

(* The vector files call mlkem_kat_vector to record their byte strings.      *)

let mlkem_kat_vectors = Hashtbl.create 12;;

let mlkem_kat_vector name (fields:(string*term)list) =
  Hashtbl.replace mlkem_kat_vectors name fields;;

let mlkem_kat_ids =
  ["keygen512"; "encaps512"; "decaps512_valid"; "decaps512_reject";
   "keygen768"; "encaps768"; "decaps768_valid"; "decaps768_reject";
   "keygen1024"; "encaps1024"; "decaps1024_valid"; "decaps1024_reject"];;

let mlkem_kat id =
  loadt ("tests/mlkem/vectors/" ^ id ^ ".ml");
  let v = try Hashtbl.find mlkem_kat_vectors id
          with Not_found -> failwith ("mlkem_kat: no vector " ^ id) in
  let get s = assoc s v in
  let has p = String.length id >= String.length p &&
              String.sub id 0 (String.length p) = p in
  let params =
    let n = List.find (fun n -> has ("keygen" ^ n) || has ("encaps" ^ n) ||
                                has ("decaps" ^ n)) ["512"; "768"; "1024"] in
    mk_const("mlkem" ^ n,[]) in
  let call f args = list_mk_comb(mk_icomb(mk_const(f,[]),params),args) in
  let tm,expected =
    if has "keygen" then
      call "mlkem_keygen_internal" [get "d"; get "z"],
      mk_pair(get "ek",get "dk")
    else if has "encaps" then
      call "mlkem_encaps_internal" [get "ek"; get "m"],
      mk_pair(get "k",get "c")
    else
      call "mlkem_decaps_internal" [get "dk"; get "c"],
      get "k" in
  let t0 = Sys.time() in
  let th = MLKEM_TOP_EVAL_CONV tm in
  let ok = rand(concl th) = expected && hyp th = [] in
  Printf.printf "KAT %s: %s (%.0f s)\n%!"
    id (if ok then "PASS" else "FAIL") (Sys.time() -. t0);
  th;;

let mlkem_kat_all () = map mlkem_kat mlkem_kat_ids;;
