(* Complete 8/16/32/64-bit register arithmetic agreement.

   GPR proofs include every operand alias and flag outcome, legacy high
   bytes, dword upper-bit clearing and all remaining state. Multiplication
   additionally covers implicit outputs and two independent destinations.
   Supplied input bytes and processor configuration are explicit boundaries
   in docs/X86.md; these claims do not include instruction-fetch effects. *)
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-gpr-lemmas.ml";;
needs "tools/sail/proofs/x86-gpr-claims.ml";;

let sail_hl_arithmetic_before = definitions ();;
loadt "tools/sail/_build/x86-arithmetic.ml";;
let sail_hl_arithmetic_definitions =
  filter (fun theorem -> not(mem theorem sail_hl_arithmetic_before))
    (definitions ());;

loadt "tools/sail/proofs/x86-multiply-claims.ml";;
let sail_hl_arithmetic_scalar_claims =
  SAIL_HL_X86_GPR_PROOFS sail_hl_arithmetic_definitions [8;16;32;64];;

(* s2n-bignum's x86_IMUL dest src is x86_IMUL3 dest (dest,src), so the
   truncated-IMUL theorems restate directly for x86_IMUL, the definition
   that the decoder produces for 0F AF. *)
let sail_hl_arithmetic_imul_claims = map (fun (width,theorem) ->
  let component = SAIL_HL_X86_GPR_COMPONENT width false in
  let root = Printf.sprintf "X86_IMUL%d_RR" width in
  let statement = parse_term(Printf.sprintf
    "!d m:4 word. !s t:x86state. sail_hl_X86_5fIMUL%d_5fRR d m s t <=> \
     x86_IMUL %s %s s t" width (component "d") (component "m")) in
  "SAIL_HL_" ^ root ^ "_IMUL_EQ",
  prove(statement, REWRITE_TAC[x86_IMUL; theorem]))
  [64,SAIL_HL_X86_IMUL64_RR_EQ; 32,SAIL_HL_X86_IMUL32_RR_EQ;
   16,SAIL_HL_X86_IMUL16_RR_EQ];;

let sail_hl_arithmetic_claims =
  sail_hl_arithmetic_scalar_claims @ SAIL_HL_X86_MULTIPLY_CLAIMS @
  sail_hl_arithmetic_imul_claims;;
if length SAIL_HL_X86_MULTIPLY_CLAIMS <> 15 ||
   length sail_hl_arithmetic_scalar_claims <> 69 ||
   length(setify(map fst sail_hl_arithmetic_claims)) <> 87 then
  failwith "wrong complete arithmetic inventory";;
List.iter sail_hl_report
  sail_hl_arithmetic_claims;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_ARITHMETIC_PROOFS_OK";;
