(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Audit of the equivalence of the generated and the handwritten FIPS 204.   *)
(* Run from the repository root in a session that has loaded all.ml:    *)
(*    loadt "common/fips204/generated/core/check.ml";;                      *)
(* ========================================================================= *)

let check_section s = Printf.printf "\n== %s ==\n%!" s;;
let check_run cmd = Printf.printf "$ %s\n%!" cmd; ignore (Sys.command cmd);;

check_section "1. Axioms (expected: INFINITY, SELECT, ETA)";;
List.iter (fun th -> Printf.printf "  %s\n" (string_of_thm th)) (axioms());;

check_section "2. Main theorems";;
Printf.printf "  %d theorems (expected 56)\n" (length EQUIVALENCE_THEOREMS);;
Printf.printf "  with hypotheses or free variables: %d (expected 0)\n"
  (length (filter (fun (_,th) -> hyp th <> [] || frees (concl th) <> [])
                  EQUIVALENCE_THEOREMS));;
List.iter (fun (n,th) ->
    Printf.printf "\n%s   [%d hypotheses]\n  %s\n" n (length (hyp th))
                  (string_of_term (concl th)))
  EQUIVALENCE_THEOREMS;;

check_section "2b. The statements of fips204_equivalence.ml";;
loadt "common/fips204/generated/fips204_equivalence.ml";;
Printf.printf "  %d statements; not the conclusion of the theorem of that name: %d (expected 0)\n"
  (length FIPS204_EQUIVALENCE_STATEMENTS)
  (length (filter (fun (n,tm) -> not (aconv tm (concl (assoc n EQUIVALENCE_THEOREMS))))
                  FIPS204_EQUIVALENCE_STATEMENTS));;

check_section "3. Constants of the statements made by the equivalence files";;
let check_stmt_consts =
  setify (itlist (fun (_,th) l ->
      map (fun c -> fst (dest_const c)) (find_terms is_const (concl th)) @ l)
    EQUIVALENCE_THEOREMS []);;
Printf.printf "  %s\n  (expected: lift_sign_internal_result lift_sign_result lift_verify_bool lift_verify_result top_prehash xof_ok)\n"
  (String.concat " " (sort (<) (filter (fun c -> not (mem c CONSTANTS_AFTER_SPECS))
                                       check_stmt_consts)));;

check_section "4. All constants added by the equivalence files";;
let check_added = filter (fun (c,_) -> not (mem c CONSTANTS_AFTER_SPECS))
                         (constants());;
Printf.printf "  %d new constants\n" (length check_added);;
List.iter (fun (c,ty) -> Printf.printf "  %s : %s\n" c (string_of_type ty))
          (sort (fun (a,_) (b,_) -> a < b) check_added);;

check_section "5. Escape hatches in the sources (expected: no match)";;
check_run "grep -nE 'mk_thm|new_axiom|CHEAT_TAC|new_constant|new_type|new_basic_type' --exclude=check.ml common/fips204/generated/core/*.ml || echo '  (no match)'";;

check_section "6. SHA-256 of the generated files (expected: 3 x OK)";;
check_run "cd common/fips204/generated && printf '%s  %s\\n' 90398bdfb0006f63ae76a3fd000ac307a6f010d296ea7e70e5c5e9a0cca9107e fips204_generated.ml 163795a255f9fb972c600dd6d60ff81ee6dadf3df41a08768788eb5ee875b7a1 core/compiler/fips_hol_prelude.ml 8bad950a5405f1fe77efbf8283c305efa1b55bf556d689d037e123a64d04e3aa core/compiler/fips204_obligations.ml | sha256sum -c -";;

check_section "7. Uninterpreted constants of the generated files, and xof_ok";;
check_run "grep -n 'new_constant' common/fips204/generated/fips204_generated.ml common/fips204/generated/core/compiler/fips_hol_prelude.ml common/fips204/generated/core/compiler/fips204_obligations.ml | grep -v ', new_constant'";;
Printf.printf "  %s\n" (string_of_thm xof_ok);;
