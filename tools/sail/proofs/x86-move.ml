(* Flag instructions, no-operation forms, MOV and XCHG on registers.

   Each claim compares the whole generated relation with s2n-bignum's
   instruction: every register alias, every flag and the rest of the
   state. The roots select one opcode branch of decode_execute or
   dispatch_2byte_gpr and keep its prefix handling, ModR/M decoding and
   operand-size selection; only the instruction bytes after the prefixes
   are supplied (docs/X86.md). Memory operands, immediates and the string
   and stack forms of these opcodes are not compared.

   CLD and STD write DF, which the translator maps to the Boolean flag
   component DF like the six arithmetic flags. MOV r/m, r and XCHG r/m, r
   with a register-direct r/m are compared with x86_MOV and x86_XCHG:
   ModR/M.r/m is the destination of MOV, and the first operand of
   s2n-bignum's XCHG is ModR/M.reg. *)
needs "x86/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-scalar-lemmas.ml";;
needs "tools/sail/proofs/fresh-model.ml";;

let sail_hl_move_standard_new_definition = new_definition;;
let sail_hl_move_before = definitions ();;
(* Declare the generated bodies with fresh-model.ml's new_definition, as
   x86-vector.ml does. *)
module Sail_hl_x86_move_model = struct
let new_definition = Sail_hl_fresh_model.new_definition;;
loadt "tools/sail/_build/x86-move.ml";;
end;;
open Sail_hl_x86_move_model;;
let new_definition = sail_hl_move_standard_new_definition;;
let sail_hl_move_definitions =
  filter (fun theorem -> not(mem theorem sail_hl_move_before))
    (definitions ());;

(* The bodies of these instructions are a flag write or nothing. *)
let SAIL_HL_X86_MOVE_FLAG_TAC definitions instruction =
  SAIL_HL_X86_REWRITE_TAC(definitions @
    [instruction; assign; LET_DEF; LET_END_DEF; FST; SND]) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[BIT_WORD_0; BIT_WORD_1; BIT_WORD_NOT; BIT_WORD_BITVAL;
              ASSIGNS_THM; COND_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  TRY(CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[]) THEN
  (REFL_TAC ORELSE PRINT_GOAL_TAC);;

let SAIL_HL_X86_MOVE_FLAG_CLAIMS = map (fun (name,instruction) ->
  let statement = parse_term(Printf.sprintf
    "!s t:x86state. sail_hl_X86_5f%s s t <=> x86_%s s t" name name) in
  "SAIL_HL_X86_" ^ name ^ "_EQ",
  prove(statement, REPEAT GEN_TAC THEN
    SAIL_HL_X86_MOVE_FLAG_TAC sail_hl_move_definitions instruction))
  ["CLC",x86_CLC; "STC",x86_STC; "CMC",x86_CMC; "CLD",x86_CLD;
   "STD",x86_STD; "NOP",x86_NOP; "ENDBR64",x86_ENDBR64];;

let SAIL_HL_X86_NOP_N_EQ = prove
 (`!m:4 word. !s t:x86state.
   sail_hl_X86_5fNOP_5fN m s t <=> x86_NOP_N (registers :> element m) s t`,
  GEN_TAC THEN SAIL_HL_X86_MOVE_FLAG_TAC sail_hl_move_definitions x86_NOP_N);;

(* x86_XCHG dest src writes dest, then src. The two orders agree when the
   operands are one component or two orthogonal ones: orthogonal writes
   commute, and both values are read in the initial state. *)
let SAIL_HL_X86_XCHG_SYMMETRY = prove
 (`!c c':(x86state,N word)component.
     (c = c' \/ orthogonal_components c c')
     ==> x86_XCHG c c' = x86_XCHG c' c`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[FUN_EQ_THM; x86_XCHG; assign; seq; LET_DEF; LET_END_DEF] THEN
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`c:(x86state,N word)component`;
                   `c':(x86state,N word)component`;
                   `read (c':(x86state,N word)component) (x:x86state)`;
                   `read (c:(x86state,N word)component) (x:x86state)`;
                   `x:x86state`] SAIL_HL_X86_WRITE_COMMUTE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[UNWIND_THM1] THEN ASM_REWRITE_TAC[]]);;

(* Two registers at one width, or the byte registers AL..BL and AH..BH
   (three-bit fields), are the same component or orthogonal ones. Distinct
   registers differ in their `element`; one register's high and low byte
   are disjoint parts of it. *)
let SAIL_HL_X86_REGISTER_ORTHOGONAL = prove
 (`!d m:4 word. ~(d = m) ==>
     orthogonal_components (registers :> element d) (registers :> element m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN
  CONJ_TAC THENL
   [CONV_TAC VALID_COMPONENT_CONV;
    ASM_SIMP_TAC[ORTHOGONAL_COMPONENTS_ELEMENT]]);;

let SAIL_HL_X86_ORTHOGONAL_VALID_TAC =
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN
  CONJ_TAC THENL [CONV_TAC VALID_COMPONENT_CONV; ALL_TAC];;

(* orthogonal (element i :> X) (element j :> Y), for i = j or i <> j. *)
let SAIL_HL_X86_ORTHOGONAL_ELEMENTS_TAC =
  FIRST
   [MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN
    ASM_SIMP_TAC[ORTHOGONAL_COMPONENTS_ELEMENT] THEN NO_TAC;
    ASM_REWRITE_TAC[] THEN REPEAT SAIL_HL_X86_ORTHOGONAL_VALID_TAC THEN
    CONV_TAC ORTHOGONAL_COMPONENTS_CONV];;

let SAIL_HL_X86_ORTHOGONAL_REGISTERS_TAC =
  FIRST
   [MATCH_MP_TAC SAIL_HL_X86_REGISTER_ORTHOGONAL THEN
    FIRST_ASSUM ACCEPT_TAC THEN NO_TAC;
    SAIL_HL_X86_ORTHOGONAL_VALID_TAC THEN SAIL_HL_X86_ORTHOGONAL_ELEMENTS_TAC];;

let SAIL_HL_X86_ELEMENT_INDEX component =
  let x = rand component in
  if (try fst(dest_const(rator x)) = "element" with Failure _ -> false)
  then rand x else rand(lhand x);;

(* Goal: A = B \/ orthogonal_components A B for two register components.
   Equal register numbers give the same component, or, for a high and a
   low byte, two disjoint ones. *)
let SAIL_HL_X86_DISJOINT_TAC (asl,w) =
  let _,orthogonal = dest_disj w in
  let a,b = match snd(strip_comb orthogonal) with
    | [a;b] -> a,b | _ -> failwith "register components" in
  let i = SAIL_HL_X86_ELEMENT_INDEX a and j = SAIL_HL_X86_ELEMENT_INDEX b in
  (ASM_CASES_TAC (mk_eq(i,j)) THENL
    [FIRST [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
            DISJ2_TAC THEN SAIL_HL_X86_ORTHOGONAL_REGISTERS_TAC];
     DISJ2_TAC THEN SAIL_HL_X86_ORTHOGONAL_REGISTERS_TAC]) (asl,w);;

let SAIL_HL_X86_REGISTER_DISJOINT width legacy =
  let component = SAIL_HL_X86_GPR_COMPONENT width legacy in
  prove(parse_term(Printf.sprintf
    "!d m:%d word. %s = %s \\/ orthogonal_components %s %s"
    (if legacy then 3 else 4) (component "d") (component "m")
    (component "d") (component "m")),
   REPEAT GEN_TAC THEN
   (if legacy then
     ASM_CASES_TAC `4 <= val(d:3 word)` THEN
     ASM_CASES_TAC `4 <= val(m:3 word)`
    else ALL_TAC) THEN
   ASM_REWRITE_TAC[GPR8;GPR16;GPR32_Z;GPR64] THEN
   SAIL_HL_X86_DISJOINT_TAC);;

(* MOV and XCHG at one width and byte encoding. The destination of MOV is
   the r/m field m and the source the reg field d. The decoder produces
   x86_XCHG reg rm for 86 and 87 (decode.ml), that is x86_XCHG d m; Sail
   writes r/m first, so the Sail root is first proved against x86_XCHG m d
   and the symmetry of x86_XCHG on these operands turns that around. *)
let SAIL_HL_X86_MOVE_CLAIM (operation,instruction,destination,source)
    width legacy =
  let bits = if legacy then 3 else 4 in
  let root = Printf.sprintf "X86_%s%d%s_RR" operation width
    (if legacy then "_LEGACY" else "") in
  let constant = "sail_hl_" ^
    String.concat "_5f" (String.split_on_char '_' root) in
  let component = SAIL_HL_X86_GPR_COMPONENT width legacy in
  let statement destination source = parse_term(Printf.sprintf
    "!d m:%d word. !s t:x86state. %s d m s t <=> x86_%s %s %s s t"
    bits constant operation (component destination) (component source)) in
  let name = "SAIL_HL_" ^ root ^ "_EQ" in
  print_endline(name ^ " starting");
  let started = Sys.time() in
  let tactic = SAIL_HL_X86_SCALAR_TAC sail_hl_move_definitions [width]
    (if legacy then ["d";"m"] else []) [instruction] in
  let theorem =
    if operation = "XCHG" then
      let in_sail_order = prove(statement "m" "d", tactic) in
      let symmetry = GEN_ALL(MATCH_MP SAIL_HL_X86_XCHG_SYMMETRY
        (SPEC_ALL(SAIL_HL_X86_REGISTER_DISJOINT width legacy))) in
      prove(statement "d" "m",
        REPEAT GEN_TAC THEN REWRITE_TAC[in_sail_order; symmetry])
    else prove(statement destination source, tactic) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name,theorem;;

let SAIL_HL_X86_MOVE_REGISTER_CLAIMS =
  List.concat_map (fun operation ->
    List.concat_map (fun width ->
      map (SAIL_HL_X86_MOVE_CLAIM operation width)
        (if width = 8 then [false;true] else [false]))
      [64;32;16;8])
    ["MOV",x86_MOV,"m","d"; "XCHG",x86_XCHG,"d","m"];;

let SAIL_HL_X86_MOVE_CLAIMS =
  SAIL_HL_X86_MOVE_FLAG_CLAIMS @ ["SAIL_HL_X86_NOP_N_EQ",SAIL_HL_X86_NOP_N_EQ] @
  SAIL_HL_X86_MOVE_REGISTER_CLAIMS;;
if length SAIL_HL_X86_MOVE_CLAIMS <> 18 ||
   length(setify(map fst SAIL_HL_X86_MOVE_CLAIMS)) <> 18 then
  failwith "wrong move claim inventory";;
List.iter sail_hl_report SAIL_HL_X86_MOVE_CLAIMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_MOVE_PROOFS_OK";;
