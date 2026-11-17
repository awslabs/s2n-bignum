(* Facts about s2n-bignum's SSE register view, shared by the legacy SSE
   and AES-NI suites.

   A legacy-encoded instruction changes only the low 128 bits of a vector
   register and keeps the other bits; s2n-bignum's SIMD128_SSE is the
   component simdregisters :> element r :> bottom_256 :> bottom_128. A VEX
   instruction clears the rest, as SIMD128 does. Sail's legacy bodies
   assign `ZMM[xreg][127..0]`, which the translator maps to a write of
   the whole 512-bit element `simdregisters :> element r` with
   `word_insert` of the new low half. These lemmas turn SIMD128_SSE into
   the same two forms: a read of its low 128 bits, which equals a read of
   SIMD128 (the one that Sail's read_simd cut uses), and that insertion. *)
needs "x86/proofs/base.ml";;
needs "tools/sail/proofs/x86-vector-lemmas.ml";;

let SAIL_HL_X86_SSE_READ = prove
 (`!(r:5 word) (s:x86state).
    read (simdregisters :> element r :> bottom_256 :> bottom_128) s =
    read (SIMD128 (Simdreg r Lower_128)) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SIMD128; COMPONENT_COMPOSE_ASSOC; READ_BOTTOM_128;
              READ_BOTTOM_256; READ_ZEROTOP_128;
              READ_ZEROTOP_256] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_ZX; BIT_WORD_SUBWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> i < 256 /\ i < 512 /\ MIN i 256 = i`]);;

let SAIL_HL_X86_SSE_WRITE = prove
 (`!(r:5 word) (s:x86state) y.
    write (simdregisters :> element r :> bottom_256 :> bottom_128) y s =
    write (simdregisters :> element r)
      (word_insert (read (simdregisters :> element r) s) (0,128) y) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPONENT_COMPOSE_ASSOC; WRITE_BOTTOM_128;
              WRITE_BOTTOM_256; READ_BOTTOM_256] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SPEC_TAC(`read (simdregisters :> element r) (s:x86state):512 word`,
           `d:512 word`) THEN
  GEN_TAC THEN SPEC_TAC(`y:128 word`,`y:128 word`) THEN GEN_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_JOIN; BIT_WORD_SUBWORD;
              BIT_WORD_INSERT] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

(* The statement of one legacy SSE form is s2n-bignum's relation applied
   to SIMD128_SSE components. Both facts above are rewrites of that
   component. *)
let SAIL_HL_X86_SSE_REWRITES =
  [SAIL_HL_X86_SSE_READ; SAIL_HL_X86_SSE_WRITE];;

(* The statement of one form: the generated root applied to its fields is
   s2n-bignum's relation applied to the operand components. "S" is the
   legacy SSE view of a vector register, "X" the VEX view, a general
   register operand is the 32- or 64-bit view with the architectural
   upper-half clearing, and an immediate is a read-only value. *)
let SAIL_HL_X86_SSE_STATEMENT
    (root, source, instruction, target, parameters, operands) =
  let component (kind, width, argument) =
    match kind with
    | "S" -> Printf.sprintf
        "(SIMD128_SSE (Simdreg (word_zx %s:5 word) Lower_128))" argument
    | "X" -> Printf.sprintf
        "(SIMD%d (Simdreg (word_zx %s:5 word) Lower_%d))" width argument width
    | "G" when width = 32 ->
        Printf.sprintf "(GPR32_Z (Gpr %s Lower_32))" argument
    | "G" -> Printf.sprintf "(GPR64 (Gpr %s Full_64))" argument
    | _ -> Printf.sprintf "(rvalue %s)" argument in
  let quantified = String.concat ""
    (map (fun (name, bits) -> Printf.sprintf "!%s:%d word. " name bits)
         parameters) in
  parse_term
    (quantified ^ "!s t:x86state. " ^ fst(dest_const(fst(strip_comb
       (lhand(snd(strip_forall(concl source))))))) ^ " " ^
     String.concat " " (map fst parameters) ^ " s t <=> x86_" ^
     instruction ^ " " ^ String.concat " " (map component operands) ^
     " s t");;
