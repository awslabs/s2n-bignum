(* Bit test and modify on registers: BT, BTS, BTR and BTC at 32 and 64 bits.

   Sail's BT, BTS, BTR and BTC (0F A3, AB, B3, BB) set CF to the selected
   bit, change that bit for BTS, BTR and BTC, leave ZF unchanged and make
   OF, SF, AF and PF undefined. s2n-bignum's relations also make ZF
   undefined: the Intel manual keeps ZF unchanged, AMD makes it undefined,
   and x86/proofs/x86.ml follows AMD. So shina permits a subset of what
   s2n-bignum permits, and as for RCL and RCR at 8 and 16 bits each form
   has two theorems:

   - _EXACT: shina's relation is s2n-bignum's with ZF also kept. It holds
     for every register pair, including equal registers, and every state.
   - _DIFF: s2n-bignum permits a final state, ZF flipped and the other
     flags kept, that shina rejects. It follows from _EXACT.

   The destination is ModR/M.r/m (m) and the bit offset ModR/M.reg (d),
   reduced modulo the operand size, as in s2n-bignum. Memory operands and
   the immediate forms (0F BA) are not compared. *)
needs "x86/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-scalar-lemmas.ml";;
needs "tools/sail/proofs/fresh-model.ml";;

let sail_hl_bit_standard_new_definition = new_definition;;
let sail_hl_bit_before = definitions ();;
module Sail_hl_x86_bit_model = struct
let new_definition = Sail_hl_fresh_model.new_definition;;
loadt "tools/sail/_build/x86-bit.ml";;
end;;
open Sail_hl_x86_bit_model;;
let new_definition = sail_hl_bit_standard_new_definition;;
let sail_hl_bit_definitions =
  filter (fun theorem -> not(mem theorem sail_hl_bit_before))
    (definitions ());;

(* Writing one bit of a word is inserting a one-bit word. *)
let SAIL_HL_X86_BITELEMENT_WRITE = prove
 (`!i b (x:N word). i < dimindex(:N) ==>
   write (bitelement i) b x = word_insert x (i,1) (word(bitval b):1 word)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bitelement; write] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_OF_BITS; IN_INSERT; IN_DELETE; IN_BITS_OF_WORD;
              BIT_WORD_INSERT] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `i <= j /\ j < i + 1 <=> j = i`] THEN
  ASM_CASES_TAC `j:num = i` THEN
  ASM_REWRITE_TAC[BIT_WORD_1; BIT_WORD_0; SUB_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SIMP_TAC[ARITH_RULE `0 < 1`; DIMINDEX_1]);;

let SAIL_HL_X86_BITELEMENT_COMPOSE_WRITE = prove
 (`!(c:(S,N word)component) i b s. i < dimindex(:N) ==>
   write (c :> bitelement i) b s =
   write c (word_insert (read c s) (i,1) (word(bitval b):1 word)) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WRITE_COMPONENT_COMPOSE] THEN
  ASM_SIMP_TAC[SAIL_HL_X86_BITELEMENT_WRITE]);;

let SAIL_HL_X86_WORD_NOT_BITVAL = prove
 (`!b. word_not (word(bitval b):1 word) = word(bitval(~b))`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* Put two states, each an explicit chain of writes, in one order. *)
let SAIL_HL_X86_BIT_CLOSE_TAC =
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  SIMP_TAC[SAIL_HL_X86_BITELEMENT_COMPOSE_WRITE; DIMINDEX_64; DIMINDEX_32;
           MOD_LT_EQ; ARITH_EQ] THEN
  REWRITE_TAC[SAIL_HL_X86_WORD_NOT_BITVAL; BIT_WORD_BITVAL; DIMINDEX_1;
              BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
  REWRITE_TAC[GSYM word_zx; WORD_ZX_TRIVIAL] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
  (REFL_TAC ORELSE PRINT_GOAL_TAC);;

let sail_hl_bit_constant root =
  "sail_hl_" ^ String.concat "_5f" (String.split_on_char '_' root);;

(* shina's undefined OF, SF, AF and PF are four one-bit choices; s2n-bignum
   has five Boolean choices, ZF among them. Given shina's choices, ZF is the
   old one; given s2n-bignum's with ZF unchanged, the one-bit words are the
   values of the Booleans. *)
let SAIL_HL_X86_BIT_EXACT_TAC definitions instruction width =
  SAIL_HL_X86_SCALAR_NORMALIZE ALL_TAC ALL_TAC definitions [width] [] [instruction] THEN
  EQ_TAC THENL
  [DISCH_THEN(X_CHOOSE_THEN `a:1 word` (X_CHOOSE_THEN `b:1 word`
     (X_CHOOSE_THEN `c:1 word` (X_CHOOSE_THEN `e:1 word`
       (SUBST1_TAC o SYM))))) THEN
   CONJ_TAC THENL
    [MAP_EVERY EXISTS_TAC [`read ZF (s:x86state)`; `bit 0 (b:1 word)`;
       `bit 0 (e:1 word)`; `bit 0 (a:1 word)`; `bit 0 (c:1 word)`] THEN
     SAIL_HL_X86_BIT_CLOSE_TAC;
     CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN REFL_TAC];
   DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN MP_TAC(CONJUNCT1 th)) THEN
   DISCH_THEN(X_CHOOSE_THEN `y1:bool` (X_CHOOSE_THEN `y2:bool`
     (X_CHOOSE_THEN `y3:bool` (X_CHOOSE_THEN `y4:bool`
       (X_CHOOSE_THEN `y5:bool` (SUBST_ALL_TAC o SYM)))))) THEN
   DISCH_TAC THEN
   RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV)) THEN
   ASM_REWRITE_TAC[] THEN
   MAP_EVERY EXISTS_TAC [`word(bitval y4):1 word`; `word(bitval y2):1 word`;
     `word(bitval y5):1 word`; `word(bitval y3):1 word`] THEN
   SAIL_HL_X86_BIT_CLOSE_TAC];;

let SAIL_HL_X86_BIT_EXACT_CLAIM (operation,instruction) width =
  let root = Printf.sprintf "X86_%s%d_RR" operation width in
  let component = SAIL_HL_X86_GPR_COMPONENT width false in
  let statement = parse_term(Printf.sprintf
    "!d m:4 word. !s t:x86state. %s d m s t <=> \
     (x86_%s %s %s s t /\\ read ZF t = read ZF s)"
    (sail_hl_bit_constant root) operation (component "m") (component "d")) in
  let name = "SAIL_HL_" ^ root ^ "_EXACT" in
  print_endline(name ^ " starting");
  let started = Sys.time() in
  let theorem = prove(statement,
    REPEAT GEN_TAC THEN
    SAIL_HL_X86_BIT_EXACT_TAC sail_hl_bit_definitions instruction width) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name,theorem;;

(* The counterexample: s2n-bignum may flip ZF and keep every other flag
   as it was, with CF the tested bit and the tested bit changed as the
   instruction does. By _EXACT, shina rejects it because it flips ZF. *)
let SAIL_HL_X86_BIT_DIFF_CLAIM (operation,instruction) width exact =
  let root = Printf.sprintf "X86_%s%d_RR" operation width in
  let component = SAIL_HL_X86_GPR_COMPONENT width false in
  let index = Printf.sprintf "val(read %s s) MOD %d" (component "d") width in
  let tested = Printf.sprintf "bit (%s) (read %s s)" index (component "m") in
  let before_cf = match operation with
    | "BT" -> "s"
    | "BTS" -> Printf.sprintf "write (%s :> bitelement (%s)) T s"
        (component "m") index
    | "BTR" -> Printf.sprintf "write (%s :> bitelement (%s)) F s"
        (component "m") index
    | _ -> Printf.sprintf "write (%s :> bitelement (%s)) (~(%s)) s"
        (component "m") index tested in
  let final = Printf.sprintf "write ZF (~read ZF s) (write CF (%s) (%s))"
    tested before_cf in
  let statement = parse_term(Printf.sprintf
    "!d m:4 word. !s:x86state. x86_%s %s %s s (%s) /\\ ~(%s d m s (%s))"
    operation (component "m") (component "d") final
    (sail_hl_bit_constant root) final) in
  let name = "SAIL_HL_" ^ root ^ "_DIFF" in
  print_endline(name ^ " starting");
  let started = Sys.time() in
  let theorem = prove(statement,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[exact] THEN
    CONJ_TAC THENL
     [SAIL_HL_X86_REWRITE_TAC[instruction; assign; SEQ; ASSIGNS_THM; LET_DEF;
        LET_END_DEF; UNDEFINED_VALUES; SEQ_ID; ASSIGNS_SEQ] THEN
      MAP_EVERY EXISTS_TAC [`~read ZF (s:x86state)`; `read SF (s:x86state)`;
        `read PF (s:x86state)`; `read OF (s:x86state)`;
        `read AF (s:x86state)`] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
      SIMP_TAC[SAIL_HL_X86_BITELEMENT_COMPOSE_WRITE; DIMINDEX_64;
               DIMINDEX_32; MOD_LT_EQ; ARITH_EQ] THEN
      CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC[BITVAL_CLAUSES; GPR8; GPR16; GPR32_Z; GPR64] THEN
      REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES THEN
      REWRITE_TAC[GSYM word_zx; WORD_ZX_TRIVIAL] THEN
      CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
      (REFL_TAC ORELSE PRINT_GOAL_TAC);
      CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      CONV_TAC TAUT]) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name,theorem;;

let SAIL_HL_X86_BIT_CLAIMS =
  List.concat_map (fun operation ->
    List.concat_map (fun width ->
      let exact_name,exact = SAIL_HL_X86_BIT_EXACT_CLAIM operation width in
      [SAIL_HL_X86_BIT_DIFF_CLAIM operation width exact;
       exact_name,exact]) [64;32])
    ["BT",x86_BT; "BTS",x86_BTS; "BTR",x86_BTR; "BTC",x86_BTC];;
if length SAIL_HL_X86_BIT_CLAIMS <> 16 ||
   length(setify(map fst SAIL_HL_X86_BIT_CLAIMS)) <> 16 then
  failwith "wrong bit claim inventory";;
List.iter sail_hl_report SAIL_HL_X86_BIT_CLAIMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_BIT_PROOFS_OK";;
