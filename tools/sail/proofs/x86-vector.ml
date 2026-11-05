(* VEX register effects under the documented supplied-byte/LongMode boundary.
   Every register alias is included. These theorems compare complete states,
   including zeroing above a written vector width, specified flag effects
   and preservation of all other state. VPTEST preserves every vector bit.
   It does not compare instruction fetch, feature checks or the full step. *)
needs "x86/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-vector-lemmas.ml";;
needs "tools/sail/proofs/fresh-model.ml";;
needs "tools/sail/proofs/proof-fork.ml";;

let sail_hl_vector_standard_new_definition = new_definition;;
(* Declare the generated bodies with fresh-model.ml's new_definition: with
   HOL's own, which first searches for an equivalent earlier definition,
   this suite takes 2.5 times as long. *)
module Sail_hl_x86_vector_model = struct
let new_definition = Sail_hl_fresh_model.new_definition;;
loadt "tools/sail/_build/x86-vector.ml";;
end;;
open Sail_hl_x86_vector_model;;
let new_definition = sail_hl_vector_standard_new_definition;;

(* Sail extracts a lane by shifting, then taking low bits. HOL's SIMD
   functions use nested subwords. Normalize their wiring while leaving
   the lane's arithmetic calculation opaque. *)
let SAIL_HL_X86_SHIFTED_SUBWORD = prove
 (`!x:M word. !k l.
   (word_subword (word_ushr x k) (0,l):N word) = word_subword x (k,l)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_USHR;
              ADD_CLAUSES; ADD_SYM]);;

(* These conversion checks exercise branch pruning after a guard changes,
   tuple bindings, function results and accumulator substitution. *)
List.iter (fun term ->
  let theorem = SAIL_HL_X86_STRICT_LET_CONV term in
  if rand(concl theorem) <> `y:8 word` then
    failwith "x86 strict-let conversion did not normalize its rebuilt root")
 [`if T = F then (x:8 word) else (y:8 word)`;
  `let (a,b) = (x:8 word,y:8 word) in if F then a else b`;
  `let a = if T = F then (x:8 word) else (y:8 word) in
   let b = if F then a else a in b`;
  `(\(a:8 word,b:8 word). if F then a else b) (x,y)`;
  `(let a = (x:8 word) in \b:8 word. if F then a else b) y`;
  `(let a = (x:8 word) and b = (y:8 word) in
    \c:8 word. if F then a else b) x`];;
let paired_state_check = SAIL_HL_X86_STRICT_LET_CONV
  `LET (\(n:int,u:A). t = (f:A->A) u) (&64,s)`;;
if rand(concl paired_state_check) <> `t = (f:A->A) s` then
  failwith "x86 strict-let conversion retained a paired state binding";;
List.iter (fun (term, expected) ->
  let theorem = SAIL_HL_X86_STRICT_LET_CONV term in
  if rand(concl theorem) <> expected then
    failwith ("x86 strict-let conversion did not factor a shared application:\n" ^
      string_of_term(rand(concl theorem)) ^ "\nexpected:\n" ^
      string_of_term expected))
 [`LET (\(u:A,z:8 word). t = (f:8 word->A->A) z u)
      (if p then (s,x:8 word) else (s,y:8 word))`,
  `t = (f:8 word->A->A) (if p then x else y) s`;
  `if p then (s:A,x:8 word) else (r:A,y:8 word)`,
  `if p then (s:A,x:8 word) else (r:A,y:8 word)`;
  `if p then (word 65535:16 word) else word 0`,
  `if p then (word 65535:16 word) else word 0`;
  `(if p then word_insert (a:128 word) (0,32) (x:32 word)
         else word_insert a (0,32) (y:32 word)):128 word`,
  `word_insert (a:128 word) (0,32)
     (if p then x:32 word else y):128 word`];;
(* An unknown tuple must not be guessed to contain a particular pair.
   Instantiate the returned equality afterwards to check its calculation. *)
let unknown_pair_term =
  `LET (\(a:8 word,b:8 word). word_add a b) (p:8 word#8 word)`;;
let unknown_pair_theorem = SAIL_HL_X86_STRICT_LET_CONV unknown_pair_term;;
if hyp unknown_pair_theorem <> [] ||
   not(aconv(lhand(concl unknown_pair_theorem)) unknown_pair_term) then
  failwith "unknown tuple binding lost its original term";;
let known_pair_theorem = CONV_RULE
  (RAND_CONV SAIL_HL_X86_STRICT_LET_CONV)
  (INST [`(x:8 word,y:8 word)`,`p:8 word#8 word`] unknown_pair_theorem);;
if rand(concl known_pair_theorem) <> `word_add (x:8 word) y` then
  failwith "unknown tuple binding selected an arbitrary value";;
print_endline "x86 vector: strict-let conversion checks passed";;

(* The instruction body has already reduced constant words and widths.
   Give the lane rewrite matcher the same kernel-derived normal form.
   Normalize assembly association and product orientation on both sides,
   never reorder bytes. *)
let SAIL_HL_X86_VECTOR_LANE_REWRITES =
  map (CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC WORD_REDUCE_CONV THENC
     NUM_REDUCE_CONV THENC INT_REDUCE_CONV))
    [SAIL_HL_X86_BYTE_PAIR_SATURATED; SAIL_HL_X86_UNSIGNED_PACK_LANE];;

let SAIL_HL_X86_BYTE_ASSEMBLY_REWRITES =
  map (fun theorem -> REWRITE_RULE[ADD_ASSOC; MULT_SYM; MULT_CLAUSES]
    (CONV_RULE NUM_REDUCE_CONV theorem))
    [SAIL_HL_X86_BYTES16; SAIL_HL_X86_BYTES32];;

let SAIL_HL_X86_ARITHMETIC_SHIFT_REWRITES =
  [SAIL_HL_X86_ARITHMETIC_SHIFT16; SAIL_HL_X86_ARITHMETIC_SHIFT32] @
  map (REWRITE_RULE[SAIL_HL_X86_SINGLE_BIT_SUBWORD])
    [SAIL_HL_X86_ARITHMETIC_SHIFT16; SAIL_HL_X86_ARITHMETIC_SHIFT32];;

let SAIL_HL_X86_VECTOR_VALUE_TAC =
  W(fun (_, goal) ->
    let is_write term =
      match strip_comb term with
      | Const("write",_), [_; _; _] -> true
      | _ -> false in
    let _, source = strip_comb(find_term is_write (lhand goal)) in
    let _, target = strip_comb(find_term is_write (rand goal)) in
    if el 0 source <> el 0 target || el 2 source <> el 2 target then
      failwith ("x86 vector writes differ in component or input state:\n" ^
        "source component: " ^ string_of_term(el 0 source) ^ "\n" ^
        "target component: " ^ string_of_term(el 0 target) ^ "\n" ^
        "source state: " ^ string_of_term(el 2 source) ^ "\n" ^
        "target state: " ^ string_of_term(el 2 target) ^ "\n" ^
        "enclosing target term: " ^ string_of_term(rand goal));
    SUBGOAL_THEN (mk_eq(el 1 source,el 1 target))
      (fun theorem -> REWRITE_TAC[theorem; EQ_SYM_EQ]) THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; SAIL_HL_X86_BIT_COND;
      BIT_WORD_INSERT; BIT_WORD_JOIN;
      BIT_WORD_SUBWORD; BIT_WORD_ZX; BIT_WORD_0;
      BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_XOR; BIT_WORD_NOT] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    (* Late helper expansion exposes scaled counts as integer products.
       Contract products of embedded naturals before matching the clamp.
       Keep arbitrary signed products and earlier lane calculations intact. *)
    REWRITE_TAC[INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
                INT_OF_NUM_LT; MULT_SYM] THEN
    REWRITE_TAC SAIL_HL_X86_SHIFT_CLAMP_REWRITES THEN REWRITE_TAC[]);;

let SAIL_HL_X86_VECTOR_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC(definitions @
    [assign; FST; SND; OUTL; OUTR; READ_RVALUE;
     NUM_OF_INT_OF_NUM; GSYM WORD_IWORD; WORD_VAL; WORD_ZX_TRIVIAL;
     simd2; simd4; simd8; simd16; simd32; usimd2; usimd4; usimd8; usimd16]) THEN
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  REWRITE_TAC[FST; SND; OUTL; OUTR; GSYM WORD_IWORD; WORD_VAL;
              WORD_ZX_TRIVIAL] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
              INT_GT; INT_OF_NUM_LT; MULT_SYM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  (* Saturation needs the original integer sum and branchless masks.
     Apply the proved lane identities before generic arithmetic and mask
     rewrites change those shapes. This changes the proof, not the model. *)
  REWRITE_TAC SAIL_HL_X86_VECTOR_LANE_REWRITES THEN
  REWRITE_TAC[IWORD_INT_MUL; IWORD_INT_ADD; IWORD_IVAL;
              GSYM word_sx; WORD_SX_TRIVIAL] THEN
  (* Arithmetic rewrites can expose fresh constant words and low-width
     casts. Normalize those before matching the rounding identity. *)
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (* Match the source sign-mask shifts before window normalization changes
     their low-subword form. Products stay opaque throughout rounding. *)
  REWRITE_TAC SAIL_HL_X86_ARITHMETIC_SHIFT_REWRITES THEN
  REWRITE_TAC[SAIL_HL_X86_ROUNDED_LOW16] THEN
  REWRITE_TAC[SAIL_HL_X86_SHIFTED_SUBWORD] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[SAIL_HL_X86_REGISTER_BITS; SAIL_HL_X86_REGISTER_INDEX;
              WORD_ZX_TRIVIAL; EQ_SYM_EQ] THEN
  (* Reducing a fixed width can select a helper result and expose a paired
     binding that the first pass could not simplify. Normalize it before
     comparing either side's write component and original input state. *)
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  REWRITE_TAC SAIL_HL_X86_VECTOR_LANE_REWRITES THEN
  (* Prove each lane calculation once, then compare only lane placement.
     In particular, high products remain opaque and signed comparison uses
     a proved extra-bit difference, not multiplier/borrow bit-blasting. *)
  REWRITE_TAC[SAIL_HL_X86_SIGNED_HIGH16; SAIL_HL_X86_UNSIGNED_HIGH16;
              SAIL_HL_X86_ABS_MASK32; SAIL_HL_X86_SIGNED_GREATER16;
              SAIL_HL_X86_SIGNED_GREATER32; SAIL_HL_X86_SIGN_MASK;
              SAIL_HL_X86_SHL_MIN; SAIL_HL_X86_USHR_MIN;
              WORD_MASK] THEN
  REWRITE_TAC SAIL_HL_X86_SHIFT_MIN_REWRITES THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[INT_GE; INT_OF_NUM_LE] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[ADD_ASSOC; MULT_SYM; MULT_CLAUSES] THEN
  REWRITE_TAC SAIL_HL_X86_BYTE_ASSEMBLY_REWRITES THEN
  SAIL_HL_X86_VECTOR_VALUE_TAC THEN
  (REFL_TAC ORELSE PRINT_GOAL_TAC);;

(* Construct proof statements only, never instruction calculations.
   Every source definition and every target relation is named explicitly
   below; the same wiring proof covers both widths and all lane sizes. *)
let SAIL_HL_X86_VECTOR_CLAIM ?(immediate=false)
    instruction width source target sources =
  if width <> 128 && width <> 256 then failwith "x86 VEX proof width";
  let _, body = strip_forall(concl source) in
  let source_name = fst(dest_const(fst(strip_comb(lhand body)))) in
  let component width register =
    Printf.sprintf "(SIMD%d (Simdreg (word_zx %s:5 word) Lower_%d))"
      width register width in
  let operands = ("d",width) :: sources in
  let names = String.concat " " (map fst operands) in
  let target_arguments = String.concat " "
    (map (fun (register, width) -> component width register) operands) ^
    (if immediate then " (rvalue count)" else "") in
  let statement = parse_term
    ("!" ^ names ^ ":4 word. " ^
     (if immediate then "!count:8 word. " else "") ^
     "!s t:x86state. " ^ source_name ^
     " " ^ names ^ (if immediate then " count" else "") ^
     " s t <=> x86_" ^ instruction ^ " " ^
     target_arguments ^ " s t") in
  let name = Printf.sprintf "SAIL_HL_X86_%s%d_%s_EQ" instruction width
    (String.make (List.length operands) 'R' ^
     (if immediate then "I" else "")) in
  let started = Sys.time() in
  print_endline("Starting complete-state proof: " ^ name);
  let theorem = prove(statement, SAIL_HL_X86_VECTOR_TAC [source; target]) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name, theorem;;

(* Each form is proved by exactly one process when the claims are split
   across forked processes (proof-fork.ml). *)
sail_hl_proof_fork "SAIL_HOL_LIGHT_X86_VECTOR_PROOFS_OK";;

let sail_hl_x86_vector_mine operands forms =
  filter (fun (instruction, width, _, _) ->
    sail_hl_proof_shard (Printf.sprintf "%s%d_%s" instruction width operands))
    forms;;

let SAIL_HL_X86_VECTOR_BINARY_CLAIMS = map
  (fun (instruction, width, source, target) ->
    SAIL_HL_X86_VECTOR_CLAIM instruction width source target
      ["n",width; "m",width]) (sail_hl_x86_vector_mine "RRR" [
  "VPADDQ",256,sail_hl_X86_5fVPADDQ256_5fRRR,x86_VPADDQ;
  "VPADDQ",128,sail_hl_X86_5fVPADDQ128_5fRRR,x86_VPADDQ;
  "VPADDD",256,sail_hl_X86_5fVPADDD256_5fRRR,x86_VPADDD;
  "VPADDD",128,sail_hl_X86_5fVPADDD128_5fRRR,x86_VPADDD;
  "VPADDW",256,sail_hl_X86_5fVPADDW256_5fRRR,x86_VPADDW;
  "VPADDW",128,sail_hl_X86_5fVPADDW128_5fRRR,x86_VPADDW;
  "VPADDB",256,sail_hl_X86_5fVPADDB256_5fRRR,x86_VPADDB;
  "VPADDB",128,sail_hl_X86_5fVPADDB128_5fRRR,x86_VPADDB;
  "VPSUBQ",256,sail_hl_X86_5fVPSUBQ256_5fRRR,x86_VPSUBQ;
  "VPSUBQ",128,sail_hl_X86_5fVPSUBQ128_5fRRR,x86_VPSUBQ;
  "VPSUBD",256,sail_hl_X86_5fVPSUBD256_5fRRR,x86_VPSUBD;
  "VPSUBD",128,sail_hl_X86_5fVPSUBD128_5fRRR,x86_VPSUBD;
  "VPSUBW",256,sail_hl_X86_5fVPSUBW256_5fRRR,x86_VPSUBW;
  "VPSUBW",128,sail_hl_X86_5fVPSUBW128_5fRRR,x86_VPSUBW;
  "VPSUBB",256,sail_hl_X86_5fVPSUBB256_5fRRR,x86_VPSUBB;
  "VPSUBB",128,sail_hl_X86_5fVPSUBB128_5fRRR,x86_VPSUBB;
  "VPAND",256,sail_hl_X86_5fVPAND256_5fRRR,x86_VPAND;
  "VPAND",128,sail_hl_X86_5fVPAND128_5fRRR,x86_VPAND;
  "VPANDN",256,sail_hl_X86_5fVPANDN256_5fRRR,x86_VPANDN;
  "VPANDN",128,sail_hl_X86_5fVPANDN128_5fRRR,x86_VPANDN;
  "VPOR",256,sail_hl_X86_5fVPOR256_5fRRR,x86_VPOR;
  "VPOR",128,sail_hl_X86_5fVPOR128_5fRRR,x86_VPOR;
  "VPXOR",256,sail_hl_X86_5fVPXOR256_5fRRR,x86_VPXOR;
  "VPXOR",128,sail_hl_X86_5fVPXOR128_5fRRR,x86_VPXOR;
  "VPMULLW",256,sail_hl_X86_5fVPMULLW256_5fRRR,x86_VPMULLW;
  "VPMULLW",128,sail_hl_X86_5fVPMULLW128_5fRRR,x86_VPMULLW;
  "VPMULLD",256,sail_hl_X86_5fVPMULLD256_5fRRR,x86_VPMULLD;
  "VPMULLD",128,sail_hl_X86_5fVPMULLD128_5fRRR,x86_VPMULLD;
  "VPMULDQ",256,sail_hl_X86_5fVPMULDQ256_5fRRR,x86_VPMULDQ;
  "VPMULDQ",128,sail_hl_X86_5fVPMULDQ128_5fRRR,x86_VPMULDQ;
  "VPMADDWD",256,sail_hl_X86_5fVPMADDWD256_5fRRR,x86_VPMADDWD;
  "VPMADDWD",128,sail_hl_X86_5fVPMADDWD128_5fRRR,x86_VPMADDWD;
  "VPMULHW",256,sail_hl_X86_5fVPMULHW256_5fRRR,x86_VPMULHW;
  "VPMULHW",128,sail_hl_X86_5fVPMULHW128_5fRRR,x86_VPMULHW;
  "VPMULHUW",256,sail_hl_X86_5fVPMULHUW256_5fRRR,x86_VPMULHUW;
  "VPMULHUW",128,sail_hl_X86_5fVPMULHUW128_5fRRR,x86_VPMULHUW;
  "VPMULHRSW",256,sail_hl_X86_5fVPMULHRSW256_5fRRR,x86_VPMULHRSW;
  "VPMULHRSW",128,sail_hl_X86_5fVPMULHRSW128_5fRRR,x86_VPMULHRSW;
  "VPCMPGTW",256,sail_hl_X86_5fVPCMPGTW256_5fRRR,x86_VPCMPGTW;
  "VPCMPGTW",128,sail_hl_X86_5fVPCMPGTW128_5fRRR,x86_VPCMPGTW;
  "VPCMPGTD",256,sail_hl_X86_5fVPCMPGTD256_5fRRR,x86_VPCMPGTD;
  "VPCMPGTD",128,sail_hl_X86_5fVPCMPGTD128_5fRRR,x86_VPCMPGTD;
  "VPSLLVD",256,sail_hl_X86_5fVPSLLVD256_5fRRR,x86_VPSLLVD;
  "VPSLLVD",128,sail_hl_X86_5fVPSLLVD128_5fRRR,x86_VPSLLVD;
  "VPSRLVD",256,sail_hl_X86_5fVPSRLVD256_5fRRR,x86_VPSRLVD;
  "VPSRLVD",128,sail_hl_X86_5fVPSRLVD128_5fRRR,x86_VPSRLVD;
  "VPSRLVQ",256,sail_hl_X86_5fVPSRLVQ256_5fRRR,x86_VPSRLVQ;
  "VPSRLVQ",128,sail_hl_X86_5fVPSRLVQ128_5fRRR,x86_VPSRLVQ;
  "VPMADDUBSW",128,sail_hl_X86_5fVPMADDUBSW128_5fRRR,x86_VPMADDUBSW;
  "VPMADDUBSW",256,sail_hl_X86_5fVPMADDUBSW256_5fRRR,x86_VPMADDUBSW;
  "VPACKUSWB",128,sail_hl_X86_5fVPACKUSWB128_5fRRR,x86_VPACKUSWB_ALT;
  "VPACKUSWB",256,sail_hl_X86_5fVPACKUSWB256_5fRRR,x86_VPACKUSWB_ALT;
]);;

(* Immediate operands are supplied 8-bit values. HOL represents such values
   as read-only components; rvalue does not read or modify machine state.
   These claims quantify every imm8 and retain all source/destination aliases. *)
let SAIL_HL_X86_VECTOR_IMMEDIATE_CLAIMS = map
  (fun (instruction, width, source, target) ->
    SAIL_HL_X86_VECTOR_CLAIM ~immediate:true instruction width source target
      ["m",width]) (sail_hl_x86_vector_mine "RRI" [
  "VPSLLW",128,sail_hl_X86_5fVPSLLW128_5fRRI,x86_VPSLLW;
  "VPSLLW",256,sail_hl_X86_5fVPSLLW256_5fRRI,x86_VPSLLW;
  "VPSLLD",128,sail_hl_X86_5fVPSLLD128_5fRRI,x86_VPSLLD;
  "VPSLLD",256,sail_hl_X86_5fVPSLLD256_5fRRI,x86_VPSLLD;
  "VPSLLQ",128,sail_hl_X86_5fVPSLLQ128_5fRRI,x86_VPSLLQ;
  "VPSLLQ",256,sail_hl_X86_5fVPSLLQ256_5fRRI,x86_VPSLLQ;
  "VPSRLW",128,sail_hl_X86_5fVPSRLW128_5fRRI,x86_VPSRLW;
  "VPSRLW",256,sail_hl_X86_5fVPSRLW256_5fRRI,x86_VPSRLW;
  "VPSRLD",128,sail_hl_X86_5fVPSRLD128_5fRRI,x86_VPSRLD;
  "VPSRLD",256,sail_hl_X86_5fVPSRLD256_5fRRI,x86_VPSRLD;
  "VPSRLQ",128,sail_hl_X86_5fVPSRLQ128_5fRRI,x86_VPSRLQ;
  "VPSRLQ",256,sail_hl_X86_5fVPSRLQ256_5fRRI,x86_VPSRLQ;
  "VPSRAW",128,sail_hl_X86_5fVPSRAW128_5fRRI,x86_VPSRAW;
  "VPSRAW",256,sail_hl_X86_5fVPSRAW256_5fRRI,x86_VPSRAW;
  "VPSRAD",128,sail_hl_X86_5fVPSRAD128_5fRRI,x86_VPSRAD;
  "VPSRAD",256,sail_hl_X86_5fVPSRAD256_5fRRI,x86_VPSRAD;
  "VPSRLDQ",128,sail_hl_X86_5fVPSRLDQ128_5fRRI,x86_VPSRLDQ;
  "VPSRLDQ",256,sail_hl_X86_5fVPSRLDQ256_5fRRI,x86_VPSRLDQ;
]);;

(* These widening encodings read the required low part of an XMM register,
   also when the destination is a YMM register. The complete state claim
   preserves every source alias and still observes all 512 register bits. *)
let SAIL_HL_X86_VECTOR_WIDEN_CLAIMS = map
  (fun (instruction, width, source, target) ->
    SAIL_HL_X86_VECTOR_CLAIM instruction width source target ["m",128])
  (sail_hl_x86_vector_mine "RR" [
  "VPMOVZXBD",256,sail_hl_X86_5fVPMOVZXBD256_5fRR,x86_VPMOVZXBD;
  "VPMOVZXBD",128,sail_hl_X86_5fVPMOVZXBD128_5fRR,x86_VPMOVZXBD;
  "VPMOVZXBW",256,sail_hl_X86_5fVPMOVZXBW256_5fRR,x86_VPMOVZXBW;
  "VPMOVZXBW",128,sail_hl_X86_5fVPMOVZXBW128_5fRR,x86_VPMOVZXBW;
  "VPMOVSXBD",256,sail_hl_X86_5fVPMOVSXBD256_5fRR,x86_VPMOVSXBD;
  "VPMOVSXBD",128,sail_hl_X86_5fVPMOVSXBD128_5fRR,x86_VPMOVSXBD;
]);;
let SAIL_HL_X86_VECTOR_UNARY_CLAIMS = map
  (fun (instruction, width, source, target) ->
    SAIL_HL_X86_VECTOR_CLAIM instruction width source target ["m",width])
  (sail_hl_x86_vector_mine "RR" [
  "VPABSD",256,sail_hl_X86_5fVPABSD256_5fRR,x86_VPABSD;
  "VPABSD",128,sail_hl_X86_5fVPABSD128_5fRR,x86_VPABSD;
]);;

(* VPTEST writes flags, not a vector destination. Both vectors and all
   other state stay observed. Sail writes OF before AF; these distinct
   components commute, so compare the complete writes in HOL's order. *)
let SAIL_HL_X86_VPTEST_AF_OF_COMMUTE =
  let writes = REWRITE_RULE[orthogonal_components]
    (ORTHOGONAL_COMPONENTS_CONV `orthogonal_components AF OF`) in
  CONJUNCT1 writes;;

let SAIL_HL_X86_VPTEST_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC(definitions @ [assign; SEQ; FST; SND; OUTL; OUTR]) THEN
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  REWRITE_TAC[FST; SND; OUTL; OUTR; GSYM WORD_IWORD; WORD_VAL;
              WORD_ZX_TRIVIAL] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM; SAIL_HL_X86_REGISTER_BITS;
              SAIL_HL_X86_REGISTER_INDEX; WORD_ZX_TRIVIAL] THEN
  CONV_TAC SAIL_HL_X86_STRICT_LET_CONV THEN
  REWRITE_TAC[BIT_WORD_NOT; BIT_WORD_BITVAL;
              SAIL_HL_X86_OR_REDUCTION_512; GSYM VAL_EQ_0;
              SAIL_HL_X86_VPTEST_AF_OF_COMMUTE] THEN
  SIMP_TAC[VAL_WORD_ZX; DIMINDEX_1; DIMINDEX_128; DIMINDEX_256;
           DIMINDEX_512; ARITH_RULE `128 <= 512`;
           ARITH_RULE `256 <= 512`; ARITH_RULE `0 < 1`] THEN
  REWRITE_TAC[WORD_AND_SYM] THEN
  (REFL_TAC ORELSE PRINT_GOAL_TAC);;

let SAIL_HL_X86_VPTEST_CLAIMS = map (fun (width, source) ->
  let _, body = strip_forall(concl source) in
  let source_name = fst(dest_const(fst(strip_comb(lhand body)))) in
  let component register = Printf.sprintf
    "(SIMD%d (Simdreg (word_zx %s) Lower_%d))" width register width in
  let statement = parse_term
    ("!n m:4 word. !s t:x86state. " ^ source_name ^
     " n m s t <=> x86_VPTEST " ^ component "n" ^ " " ^
     component "m" ^ " s t") in
  Printf.sprintf "SAIL_HL_X86_VPTEST%d_RR_EQ" width,
  prove(statement, SAIL_HL_X86_VPTEST_TAC [source; x86_VPTEST]))
  (filter (fun (width, _) ->
     sail_hl_proof_shard (Printf.sprintf "VPTEST%d_RR" width))
   [128,sail_hl_X86_5fVPTEST128_5fRR;256,sail_hl_X86_5fVPTEST256_5fRR]);;

let SAIL_HL_X86_VECTOR_CLAIMS =
  SAIL_HL_X86_VECTOR_BINARY_CLAIMS @ SAIL_HL_X86_VECTOR_WIDEN_CLAIMS @
  SAIL_HL_X86_VECTOR_UNARY_CLAIMS @ SAIL_HL_X86_VPTEST_CLAIMS @
  SAIL_HL_X86_VECTOR_IMMEDIATE_CLAIMS;;
if sail_hl_proof_whole () &&
   (length SAIL_HL_X86_VECTOR_CLAIMS <> 80 ||
    length(setify(map fst SAIL_HL_X86_VECTOR_CLAIMS)) <> 80) then
  failwith "vector claim count or duplicate";;
List.iter sail_hl_report SAIL_HL_X86_VECTOR_CLAIMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_VECTOR_PROOFS_OK";;
