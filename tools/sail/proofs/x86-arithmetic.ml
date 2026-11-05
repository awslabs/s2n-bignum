(* Complete 8/16/32/64-bit register arithmetic agreement.

   GPR proofs include every operand alias and flag outcome, legacy high
   bytes, dword upper-bit clearing and all remaining state. Multiplication
   additionally covers implicit outputs and two independent destinations.
   Supplied input bytes and processor configuration are explicit boundaries
   in docs/X86.md; these claims do not include instruction-fetch effects. *)
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-gpr-lemmas.ml";;
needs "tools/sail/proofs/x86-gpr-claims.ml";;
needs "tools/sail/proofs/proof-fork.ml";;

let sail_hl_arithmetic_before = definitions ();;
loadt "tools/sail/_build/x86-arithmetic.ml";;
let sail_hl_arithmetic_definitions =
  filter (fun theorem -> not(mem theorem sail_hl_arithmetic_before))
    (definitions ());;

loadt "tools/sail/proofs/x86-multiply-claims.ml";;
(* The multiply claims above are shared setup. Each scalar claim below is
   proved, and each multiply claim printed, by exactly one process when the
   claims are split across forked processes (proof-fork.ml). *)
sail_hl_proof_fork "SAIL_HOL_LIGHT_X86_ARITHMETIC_PROOFS_OK";;
let sail_hl_arithmetic_scalar_claims =
  SAIL_HL_X86_GPR_PROOFS sail_hl_arithmetic_definitions [8;16;32;64];;
let sail_hl_arithmetic_claims =
  sail_hl_arithmetic_scalar_claims @ SAIL_HL_X86_MULTIPLY_CLAIMS;;
if length SAIL_HL_X86_MULTIPLY_CLAIMS <> 15 ||
   sail_hl_proof_whole () &&
   (length sail_hl_arithmetic_scalar_claims <> 69 ||
    length(setify(map fst sail_hl_arithmetic_claims)) <> 84) then
  failwith "wrong complete arithmetic inventory";;
List.iter sail_hl_report
  (sail_hl_arithmetic_scalar_claims @
   filter (fun (name,_) ->
     sail_hl_proof_shard (String.sub name 8 (String.length name - 11)))
   SAIL_HL_X86_MULTIPLY_CLAIMS);;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_ARITHMETIC_PROOFS_OK";;
