(* Agreement of REMS register arithmetic with s2n-bignum.

   Each claim compares the core observation of a REMS root, which restores
   the entry RIP after the body's own RIP advance, with the corresponding
   s2n-bignum instruction on the entire state. The roots' rflags and rip
   parameters are the low 32 bits of HOL rflags and HOL RIP. Operand
   values, flags and register numbers are unrestricted; operands may alias.
   Instruction bytes and processor mode are the boundaries documented in
   docs/X86.md. *)
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-rems-lemmas.ml";;
needs "tools/sail/proofs/fresh-model.ml";;
needs "tools/sail/proofs/proof-fork.ml";;

let sail_hl_rems_arithmetic_before = definitions ();;
(* Declare each supplied body directly in the kernel. The generated file
   finally rewrites every root with all of its helpers and reduces
   numerals over the whole body; the proofs evaluate the helper equations
   by value instead, so both post-passes are skipped and the model keeps
   each root as its definition. *)
module Sail_hl_x86_rems_arithmetic_model = struct
let new_definition = Sail_hl_fresh_model.new_definition;;
let REWRITE_RULE (_:thm list) (theorem:thm) = theorem;;
let CONV_RULE (_:conv) (theorem:thm) = theorem;;
loadt "tools/sail/_build/x86-rems-arithmetic.ml";;
end;;
let sail_hl_rems_arithmetic_definitions =
  filter (fun theorem -> not(mem theorem sail_hl_rems_arithmetic_before))
    (definitions ());;

let sail_hl_rems_arithmetic_compset = SAIL_HL_X86_REMS_COMPSET
  sail_hl_rems_arithmetic_definitions
  Sail_hl_x86_rems_arithmetic_model.sail_hl_case_x86_2drems_2darithmetic_result
  Sail_hl_x86_rems_arithmetic_model.sail_hl_type_x86_2drems_2darithmetic_proc_5fmode_DISTINCT;;

let sail_hl_rems_arithmetic_facts =
  map (fun width -> width, SAIL_HL_X86_REMS_FACTS width) [8;16;32;64];;

(* Prove that the core observation of root agrees with target, the
   s2n-bignum instruction applied to its operand components. The root's
   operands are register fields; a legacy byte form has three-bit fields
   and is split on the high-byte case. *)
let SAIL_HL_X86_REMS_ARITHMETIC_CLAIM root names legacy facts instruction target =
  let bits = if legacy then 3 else 4 in
  let constant = "sail_hl_" ^
    String.concat "_5f" (String.split_on_char '_' root) in
  let arguments = map (fun name -> mk_var(name, mk_type("word",[mk_finty(num bits)])))
    names in
  let statement = parse_term(Printf.sprintf
    "!%s:%d word. !s t:x86state. \
     sail_hl_x86_core (%s (rflags :> bottom_32) RIP %s) s t <=> %s s t"
    (String.concat " " names) bits constant (String.concat " " names) target) in
  let name = "SAIL_HL_" ^ root ^ "_EQ" in
  print_endline(name ^ " starting");
  let started = Sys.time() in
  let _,_,narrowing = facts in
  let applied = list_mk_comb(mk_const(constant,[]),
    [`rflags :> bottom_32`; `RIP`] @ arguments @ [`s:x86state`; `u:x86state`]) in
  let normalized = GEN_ALL(SAIL_HL_X86_REMS_NORMALIZE
    sail_hl_rems_arithmetic_compset facts applied) in
  Printf.printf "normalized: %.3fs\n%!" (Sys.time() -. started);
  let theorem = prove(statement,
    SAIL_HL_X86_REMS_CLAIM_TAC normalized instruction narrowing
      (if legacy then arguments else [])) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name,theorem;;

let sail_hl_x86_rems_root operation width legacy operands =
  Printf.sprintf "X86_REMS_%s%d%s_%s" operation width
    (if legacy then "_LEGACY" else "") operands;;

(* The REMS ALU, TEST and group-3/4/5 bodies, at every register width and
   both byte encodings. *)
let SAIL_HL_X86_REMS_ALU_OPERATIONS =
 ["ADD",x86_ADD,false; "ADC",x86_ADC,false;
  "SUB",x86_SUB,false; "SBB",x86_SBB,false; "CMP",x86_CMP,false;
  "AND",x86_AND,false; "OR",x86_OR,false; "XOR",x86_XOR,false;
  "TEST",x86_TEST,false;
  "INC",x86_INC,true; "DEC",x86_DEC,true; "NEG",x86_NEG,true;
  "NOT",x86_NOT,true];;

let SAIL_HL_X86_REMS_FORMS =
  [64,false; 32,false; 16,false; 8,false; 8,true];;

(* Each REMS form below is proved by exactly one process when the claims
   are split across forked processes (proof-fork.ml). *)
sail_hl_proof_fork "SAIL_HOL_LIGHT_X86_REMS_ARITHMETIC_PROOFS_OK";;

let sail_hl_rems_alu_claims =
  List.concat_map (fun (width,legacy) ->
    map (fun (operation,instruction,unary) ->
      let names = if unary then ["d"] else ["d";"m"] in
      SAIL_HL_X86_REMS_ARITHMETIC_CLAIM
        (sail_hl_x86_rems_root operation width legacy
          (if unary then "R" else "RR"))
        names legacy (assoc width sail_hl_rems_arithmetic_facts) instruction
        ("x86_" ^ operation ^ " " ^ String.concat " "
          (map (SAIL_HL_X86_GPR_COMPONENT width legacy) names)))
      (filter (fun (operation,_,unary) -> sail_hl_proof_shard
         (sail_hl_x86_rems_root operation width legacy
           (if unary then "R" else "RR")))
       SAIL_HL_X86_REMS_ALU_OPERATIONS))
    SAIL_HL_X86_REMS_FORMS;;

(* One-operand MUL and IMUL write the double-width product to the
   implicit pair RDX:RAX, EDX:EAX, DX:AX or AH:AL. *)
let SAIL_HL_X86_REMS_PRODUCT_PAIR width =
  match width with
    64 -> "(RDX,RAX)"
  | 32 -> "(RDX :> zerotop_32,RAX :> zerotop_32)"
  | 16 -> "(DX,AX)"
  | _ -> "(AH,AL)";;

let sail_hl_rems_widening_claims =
  List.concat_map (fun (width,legacy) ->
    map (fun (operation,instruction,name) ->
      SAIL_HL_X86_REMS_ARITHMETIC_CLAIM
        (sail_hl_x86_rems_root operation width legacy "R")
        ["m"] legacy (assoc width sail_hl_rems_arithmetic_facts) instruction
        (Printf.sprintf "%s %s %s" name (SAIL_HL_X86_REMS_PRODUCT_PAIR width)
          (SAIL_HL_X86_GPR_COMPONENT width legacy "m")))
      (filter (fun (operation,_,_) -> sail_hl_proof_shard
         (sail_hl_x86_rems_root operation width legacy "R"))
       ["MUL",x86_MUL2,"x86_MUL2"; "IMUL1",x86_IMUL2,"x86_IMUL2"]))
    SAIL_HL_X86_REMS_FORMS;;

(* Two-operand IMUL keeps the low half of the product in d. *)
let sail_hl_rems_truncated_claims =
  map (fun width ->
    let d = SAIL_HL_X86_GPR_COMPONENT width false "d"
    and m = SAIL_HL_X86_GPR_COMPONENT width false "m" in
    SAIL_HL_X86_REMS_ARITHMETIC_CLAIM
      (sail_hl_x86_rems_root "IMUL" width false "RR") ["d";"m"] false
      (SAIL_HL_X86_REMS_TRUNCATED_FACTS width
        (assoc width sail_hl_rems_arithmetic_facts))
      x86_IMUL3 (Printf.sprintf "x86_IMUL3 %s (%s,%s)" d d m))
    (filter (fun width -> sail_hl_proof_shard
       (sail_hl_x86_rems_root "IMUL" width false "RR")) [64; 32; 16]);;

let sail_hl_rems_arithmetic_claims =
  sail_hl_rems_alu_claims @ sail_hl_rems_widening_claims @
  sail_hl_rems_truncated_claims;;

if sail_hl_proof_whole () && length sail_hl_rems_arithmetic_claims <> 78 then
  failwith "wrong REMS arithmetic inventory";;
List.iter sail_hl_report sail_hl_rems_arithmetic_claims;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_REMS_ARITHMETIC_PROOFS_OK";;
