(* Bit scans and bit counts on registers: BSF, BSR, TZCNT, LZCNT and POPCNT
   at 64, 32 and 16 bits.

   Sail computes these with branchless helpers: popcount adds the bits of a
   64-bit word in six masked steps and asserts that the sum is at most the
   width; ctz and clz are built on popcount. The generated relation keeps
   each assertion as a guard that rejects a final state. The lemmas in
   x86-count-lemmas.ml show that the helpers compute word_popcount,
   word_ctz and word_clz, so every guard holds and the relation is the
   instruction's.

   - TZCNT, LZCNT and POPCNT (F3 0F BC, F3 0F BD and F3 0F B8, with the
     feature flags assumed present) are compared with x86_TZCNT, x86_LZCNT
     and x86_POPCNT. s2n-bignum's x86_POPCNT also appends the event
     EventX86POPCNT(x, width); Sail records no events. As for the RV32
     division events, the statement follows Sail's relation by that event,
     taken from s2n-bignum's definition and not checked against Sail.
   - BSF (0F BC) and BSR (0F BD): leave the destination unchanged for a
     zero source. s2n-bignum makes the destination undefined, so shina
     permits a subset of what s2n-bignum permits, and as for BT each form
     has two theorems:
       _EXACT: shina's relation is s2n-bignum's with the low `width` bits
               of the destination kept for a zero source;
       _DIFF:  s2n-bignum permits a final state for a zero source with a
               changed destination, which shina rejects.
     For 32 bits, Sail leaves bits 63:32 undefined after a zero source, as
     s2n-bignum does through OPERAND32_FULL.
   BSR takes 63 minus the leading zeros of zero_extend(x) | 1, counted
   by the smear and popcount of LZCNT. The generated chain of lets is
   rewritten as a whole before it is substituted: see
   SAIL_HL_X86_BSR_CHAIN in x86-count-lemmas.ml. Memory operands are not
   compared. *)
needs "x86/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-select-lemmas.ml";;
needs "tools/sail/proofs/x86-count-lemmas.ml";;
needs "tools/sail/proofs/fresh-model.ml";;

let sail_hl_count_standard_new_definition = new_definition;;
let sail_hl_count_before = definitions ();;
module Sail_hl_x86_count_model = struct
let new_definition = Sail_hl_fresh_model.new_definition;;
loadt "tools/sail/_build/x86-count.ml";;
end;;
open Sail_hl_x86_count_model;;
let new_definition = sail_hl_count_standard_new_definition;;

(* The generated definitions, without the recursion theorem's constant:
   rewriting must use the theorem, not unfold the constant. *)
let sail_hl_count_definitions =
  filter (fun theorem ->
    not (try fst(dest_const(fst(strip_comb
           (lhs(snd(strip_forall(concl theorem))))))) = "sail_hl_result_case"
         with Failure _ -> false))
    (filter (fun theorem -> not(mem theorem sail_hl_count_before))
       (definitions ()));;

(* CLAIMS BEGIN *)
let sail_hl_count_constant root =
  "sail_hl_" ^ String.concat "_5f" (String.split_on_char '_' root);;

(* Rewrites of the guard and the helpers, common to every instruction at
   this width. The popcount adds the zero-extended operand to 64 bits. *)
let SAIL_HL_X86_COUNT_COMMON width =
  [SAIL_HL_X86_SWAR_POPCOUNT width; SAIL_HL_X86_OR_REDUCTION_512;
   SAIL_HL_X86_ZERO_EXTEND_512 width; BIT_WORD_BITVAL;
   SAIL_HL_X86_WORD_NOT_BITVAL; COND_CLAUSES; sail_hl_result_case] @
  (if width = 64 then [] else [SAIL_HL_X86_ZX_WORD width 64]);;

(* Undefined flags are one-bit choices in Sail and Boolean choices in
   s2n-bignum. Order the flag writes alike; the choices then differ only
   in the order of their quantifiers, which a first-order search settles. *)
let SAIL_HL_X86_COUNT_FLAGS_TAC =
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  REWRITE_TAC[SAIL_HL_X86_ARBITRARY_BIT0];;

let SAIL_HL_X86_TZCNT_TAC definitions width =
  SAIL_HL_X86_SCALAR_NORMALIZE ALL_TAC ALL_TAC definitions [width] []
    [x86_TZCNT; sail_hl_result_case] THEN
  REWRITE_TAC(GSYM WORD_CTZ_EMULATION_POPCOUNT ::
    SAIL_HL_X86_CTZ_VAL width 64 :: SAIL_HL_X86_CTZ_VAL width width ::
    SAIL_HL_X86_CTZ_BOUND width :: WORD_CTZ_EQ_0 ::
    SAIL_HL_X86_COUNT_COMMON width) THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SAIL_HL_X86_COUNT_FLAGS_TAC THEN MESON_TAC[];;

let SAIL_HL_X86_LZCNT_TAC definitions width =
  SAIL_HL_X86_SCALAR_NORMALIZE ALL_TAC ALL_TAC definitions [width] []
    [x86_LZCNT; sail_hl_result_case] THEN
  REWRITE_TAC(SAIL_HL_X86_CLZ_POPCOUNT width ::
    SAIL_HL_X86_SUB_VAL width 64 :: SAIL_HL_X86_SUB_BOUND width ::
    SAIL_HL_X86_INT_SUB width :: GSYM WORD_IWORD ::
    SAIL_HL_X86_CLZ_VAL width width :: WORD_CLZ_EQ_0 ::
    SAIL_HL_X86_COUNT_COMMON width) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SAIL_HL_X86_COUNT_FLAGS_TAC THEN MESON_TAC[];;

(* POPCNT sets five flags to constants; its source is read as a word of
   the operand size and counted on 64 bits. *)
let SAIL_HL_X86_POPCNT_TAC definitions width =
  SAIL_HL_X86_SCALAR_NORMALIZE ALL_TAC ALL_TAC definitions [width] []
    [x86_POPCNT; sail_hl_result_case; seq] THEN
  REWRITE_TAC(SAIL_HL_X86_POPCOUNT_VAL width 64 ::
    SAIL_HL_X86_POPCOUNT_BOUND width :: VAL_EQ_0 ::
    SAIL_HL_X86_COUNT_COMMON width) THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_EVENTS_INWARD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  (REFL_TAC ORELSE PRINT_GOAL_TAC);;

let SAIL_HL_X86_COUNT_CLAIM root statement tactic =
  let name = "SAIL_HL_" ^ root ^ "_EQ" in
  print_endline(name ^ " starting");
  let started = Sys.time() in
  let theorem = prove(parse_term statement, tactic) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name,theorem;;

let SAIL_HL_X86_COUNT_PLAIN_CLAIM definitions (operation,instruction,tactic) width =
  let root = Printf.sprintf "X86_%s%d_RR" operation width in
  let component = SAIL_HL_X86_GPR_COMPONENT width false in
  SAIL_HL_X86_COUNT_CLAIM root (Printf.sprintf
    "!d m:4 word. !s t:x86state. %s d m s t <=> x86_%s %s %s s t"
    (sail_hl_count_constant root) operation (component "d") (component "m"))
    (tactic definitions width);;

(* x86_POPCNT also appends EventX86POPCNT(x, width) with x the source read
   in the initial state. Sail has no events; the statement follows Sail's
   relation by that event, as the RV32 division statements do. *)
let SAIL_HL_X86_POPCNT_CLAIM definitions width =
  let root = Printf.sprintf "X86_POPCNT%d_RR" width in
  let component = SAIL_HL_X86_GPR_COMPONENT width false in
  SAIL_HL_X86_COUNT_CLAIM root (Printf.sprintf
    "!d m:4 word. !s t:x86state. \
     (%s d m ,, \
      (\\u. (events := CONS (EventX86POPCNT(word_zx (read %s s), \
                                            dimindex(:%d))) \
                              (read events u)) u)) s t <=> \
     x86_POPCNT %s %s s t"
    (sail_hl_count_constant root) (component "m") width
    (component "d") (component "m"))
    (SAIL_HL_X86_POPCNT_TAC definitions width);;

let SAIL_HL_X86_COUNT_PLAIN_CLAIMS =
  List.concat_map (fun instruction ->
    map (SAIL_HL_X86_COUNT_PLAIN_CLAIM sail_hl_count_definitions instruction)
      [64;32;16])
    ["TZCNT",x86_TZCNT,SAIL_HL_X86_TZCNT_TAC;
     "LZCNT",x86_LZCNT,SAIL_HL_X86_LZCNT_TAC] @
  map (SAIL_HL_X86_POPCNT_CLAIM sail_hl_count_definitions) [64;32;16];;

(* BSF. The destination of a zero source stays as it was in Sail
   and is undefined in s2n-bignum, whose destx is the whole register for a
   32-bit operand. [low] is the part of the destination that shina keeps
   for a zero source: the operand itself, or the low half of the register
   after a 32-bit scan, whose upper half Sail leaves undefined. *)
let SAIL_HL_X86_SCAN_COMPONENTS width =
  let component = SAIL_HL_X86_GPR_COMPONENT width false in
  let full = "(registers :> element d)" in
  (* The part of the destination that a zero source leaves alone. *)
  let low state =
    if width = 32 then
      Printf.sprintf "word_zx (read %s %s):32 word" full state
    else Printf.sprintf "read %s %s" (component "d") state in
  component "d",
  (if width = 32 then full else component "d"),
  component "m",
  low;;

(* Substitute the variable that is the right side of an equation. *)
let SAIL_HL_X86_SUBST_RIGHT_VARIABLE =
  FIRST_X_ASSUM(fun theorem ->
    let conclusion = concl theorem in
    if is_eq conclusion && is_var(rand conclusion)
    then SUBST_ALL_TAC(SYM theorem) else failwith "no variable on the right");;

(* A zero source. Sail's final register is the old one, with the flags
   written; s2n-bignum writes any value to destx and requires the low
   part of the destination to be the old one. [witness] is the value of
   destx that keeps the register; [facts] simplify the destination that
   a write leaves, and [low] rewrites the hypothesis "the low part is
   unchanged" into "the written value is the old one". *)
let SAIL_HL_X86_SCAN_ZERO_TAC width =
  let register = "(registers :> element d)" in
  let value = if width = 16 then
      "word_zx (read " ^ register ^ " (s:x86state)):16 word"
    else "read " ^ register ^ " (s:x86state)" in
  let join = if width = 16 then [SAIL_HL_X86_JOIN16] else [] in
  let prefix =
    CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
    CONV_TAC(DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
    REWRITE_TAC([UNWIND_THM1; SAIL_HL_X86_ARBITRARY_BIT0; VAL_WORD_0] @ join) THEN
    CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) in
  if width = 32 then
    (* Sail's final register has an undefined upper half u: the old low half
       with u above it. s2n-bignum's destx is any register with that low
       half, which is the old low half with the upper half of destx. *)
    prefix THEN EQ_TAC THENL
     [REPEAT STRIP_TAC THEN SAIL_HL_X86_SUBST_RIGHT_VARIABLE THEN
      CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC[SAIL_HL_X86_JOINLOW32] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN SAIL_HL_X86_SUBST_RIGHT_VARIABLE THEN
      SAIL_HL_X86_SUBST_RIGHT_VARIABLE THEN
      RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV)) THEN
      FIRST_ASSUM(fun theorem ->
        SUBST1_TAC(SYM(MATCH_MP SAIL_HL_X86_JOINSPLIT32 theorem))) THEN
      MESON_TAC[]]
  else
  prefix THEN
  EQ_TAC THENL
   [REPEAT STRIP_TAC THEN SAIL_HL_X86_SUBST_RIGHT_VARIABLE THENL
     [EXISTS_TAC `s:x86state` THEN CONJ_TAC THENL
       [EXISTS_TAC (parse_term value) THEN REWRITE_TAC join THEN
        CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN
        REWRITE_TAC[];
        MESON_TAC[]];
      CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN SAIL_HL_X86_SUBST_RIGHT_VARIABLE THEN
    SAIL_HL_X86_SUBST_RIGHT_VARIABLE THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SAIL_HL_X86_JOINLOW16]) THEN
    FIRST_X_ASSUM(fun theorem ->
      let conclusion = concl theorem in
      if is_eq conclusion && is_var(lhs conclusion)
      then SUBST_ALL_TAC theorem else failwith "no variable on the left") THEN
    REWRITE_TAC join THEN
    CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN MESON_TAC[]];;

(* BSF is the count of trailing zeros; its source is zero-extended to 64
   bits and counted by the popcount of ~x & (x - 1), as for TZCNT. BSR
   subtracts from 63 the leading zeros of that extension with bit 0 set,
   which is counted by the smear and popcount of LZCNT. *)
let SAIL_HL_X86_SCAN_FACTS operation width =
  if operation = "BSF" then
    [GSYM WORD_CTZ_EMULATION_POPCOUNT; SAIL_HL_X86_CTZ_VAL width 64;
     SAIL_HL_X86_CTZ_VAL width width; SAIL_HL_X86_CTZ_BOUND width]
  else
    [SAIL_HL_X86_SUB_VAL 64 64; SAIL_HL_X86_SUB_BOUND 64;
     SAIL_HL_X86_INT_SUB 64; SAIL_HL_X86_CLZ_OR_ONE_BOUND;
     SAIL_HL_X86_INT_SUB_63; INT_OF_NUM_LT; GSYM WORD_IWORD;
     SAIL_HL_X86_ZX_WORD width 64];;

let SAIL_HL_X86_SCAN_EXACT_TAC definitions (operation,instruction) width =
  let zero = if width = 64 then
      "read (registers :> element m) (s:x86state) = word 0"
    else Printf.sprintf
      "word_zx (read (registers :> element m) (s:x86state)):%d word = word 0"
      width in
  (* BSR scans zero_extend(x) | 1. For a nonzero source the leading zeros
     are those of x, plus the 64 - width of the extension. A conditional
     rewrite does not discharge its condition here, so apply the fact to
     the assumption that the source is nonzero. *)
  let nonzero_source = if operation = "BSF" then ALL_TAC else
    let count = if width = 64 then
        REWRITE_RULE[WORD_ZX_TRIVIAL; ADD_CLAUSES]
          (SAIL_HL_X86_CLZ_OR_ONE 64)
      else SAIL_HL_X86_CLZ_OR_ONE width in
    FIRST_ASSUM(fun theorem ->
      REWRITE_TAC[MATCH_MP count theorem; SAIL_HL_X86_SCAN_ARITH width]) in
  (* BSR first replaces the chain of lets that counts leading zeros by its
     value, as SAIL_HL_X86_BSR_CHAIN explains. That needs the generated
     definitions unfolded without substituting any let. *)
  (if operation = "BSF" then ALL_TAC else
   REPEAT GEN_TAC THEN PURE_REWRITE_TAC definitions THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV SAIL_HL_X86_BSR_CHAIN))) THEN
  SAIL_HL_X86_SCALAR_NORMALIZE ALL_TAC ALL_TAC definitions [width] []
    [instruction; sail_hl_result_case; seq] THEN
  REWRITE_TAC(SAIL_HL_X86_SCAN_FACTS operation width @
    SAIL_HL_X86_COUNT_COMMON width @ SAIL_HL_X86_BLEND_FACTS @
    [NOT_CLAUSES]) THEN
  ASM_CASES_TAC (parse_term zero) THEN
  ASM_REWRITE_TAC[COND_CLAUSES] THENL
   [SAIL_HL_X86_SCAN_ZERO_TAC width;
    nonzero_source THEN
    CONV_TAC(DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV) THEN
    REWRITE_TAC[UNWIND_THM1; SAIL_HL_X86_ARBITRARY_BIT0; VAL_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_ORDER_WRITES_CONV) THEN
    (MESON_TAC[] ORELSE PRINT_GOAL_TAC)];;

let SAIL_HL_X86_SCAN_EXACT_CLAIM definitions (operation,instruction) width =
  let root = Printf.sprintf "X86_%s%d_RR" operation width in
  let destination,full,source,low = SAIL_HL_X86_SCAN_COMPONENTS width in
  let name = "SAIL_HL_" ^ root ^ "_EXACT" in
  print_endline(name ^ " starting");
  let started = Sys.time() in
  let statement = parse_term(Printf.sprintf
    "!d m:4 word. !s t:x86state. %s d m s t <=> \
     (x86_%s %s %s %s s t /\\ \
      (read %s s = word 0 ==> %s = %s))"
    (sail_hl_count_constant root) operation destination full source
    source (low "t") (low "s")) in
  let theorem = prove(statement,
    SAIL_HL_X86_SCAN_EXACT_TAC definitions (operation,instruction) width) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name,theorem;;

(* A word differs from its complement, on any width in the scan forms. *)
let SAIL_HL_X86_NOT_DIFFERS width =
  if width = 32 then
    prove(`!r:64 word. ~(word_zx (word_not r:64 word):32 word = word_zx r)`,
      GEN_TAC THEN BITBLAST_TAC)
  else
    prove(parse_term(Printf.sprintf "!x:%d word. ~(word_not x = x)" width),
      GEN_TAC THEN BITBLAST_TAC);;

(* The counterexample: for a zero source, s2n-bignum permits the final state
   in which ZF is set, the flags that it may leave undefined are as they
   were and the whole of destx is inverted. _EXACT shows that shina rejects
   it, since the destination of a zero source must keep its low part. *)
let SAIL_HL_X86_SCAN_DIFF_CLAIM definitions (operation,instruction) width exact =
  let root = Printf.sprintf "X86_%s%d_RR" operation width in
  let destination,full,source,low = SAIL_HL_X86_SCAN_COMPONENTS width in
  let final = Printf.sprintf
    "write ZF T (write %s (word_not (read %s s)) s)" full full in
  let name = "SAIL_HL_" ^ root ^ "_DIFF" in
  print_endline(name ^ " starting");
  let started = Sys.time() in
  (* A 16-bit destination is a part of the register. Writes to it commute
     with the flags once it is written as the register it belongs to. *)
  let unfold = if width = 16 then
      REWRITE_TAC[GPR16] THEN REWRITE_TAC SAIL_HL_X86_GPR_SHORT_REWRITES
    else ALL_TAC in
  let statement = parse_term(Printf.sprintf
    "!d m:4 word. !s:x86state. read %s s = word 0 ==> \
     x86_%s %s %s %s s (%s) /\\ ~(%s d m s (%s))"
    source operation destination full source final
    (sail_hl_count_constant root) final) in
  let theorem = prove(statement,
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[exact] THEN CONJ_TAC THENL
     [SAIL_HL_X86_REWRITE_TAC[instruction; assign; SEQ; ASSIGNS_THM;
        LET_DEF; LET_END_DEF; UNDEFINED_VALUES; SEQ_ID; ASSIGNS_SEQ] THEN
      ASM_REWRITE_TAC[COND_CLAUSES] THEN
      REWRITE_TAC[seq; VAL_WORD_0] THEN
      CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[UNWIND_THM1] THEN
      CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      EXISTS_TAC (parse_term(Printf.sprintf
        "write %s (word_not (read %s (s:x86state))) s" full full)) THEN
      CONJ_TAC THENL
       [EXISTS_TAC (parse_term(Printf.sprintf
          "word_not (read %s (s:x86state))" full)) THEN (REFL_TAC ORELSE PRINT_GOAL_TAC);
        MAP_EVERY EXISTS_TAC
          [`read CF (s:x86state)`; `read OF (s:x86state)`;
           `read SF (s:x86state)`; `read PF (s:x86state)`;
           `read AF (s:x86state)`] THEN
        unfold THEN
        CONV_TAC(TOP_DEPTH_CONV SAIL_HL_X86_SELF_WRITE_CONV) THEN (REFL_TAC ORELSE PRINT_GOAL_TAC)];
      ASM_REWRITE_TAC[] THEN unfold THEN
      CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      REWRITE_TAC(SAIL_HL_X86_NOT_DIFFERS width ::
                  (if width = 16 then [SAIL_HL_X86_JOINLOW16] else []))]) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name,theorem;;

(* The scan claims, in the order of x86_forms.py: for each form the
   counterexample and then the exact relation. *)
let SAIL_HL_X86_SCAN_CLAIMS =
  List.concat_map (fun (operation,instruction) ->
    List.concat_map (fun width ->
      let exact_name,exact =
        SAIL_HL_X86_SCAN_EXACT_CLAIM sail_hl_count_definitions
          (operation,instruction) width in
      [SAIL_HL_X86_SCAN_DIFF_CLAIM sail_hl_count_definitions
         (operation,instruction) width exact;
       exact_name,exact]) [64;32;16])
    ["BSF",x86_BSF; "BSR",x86_BSR];;

let SAIL_HL_X86_COUNT_CLAIMS =
  SAIL_HL_X86_SCAN_CLAIMS @ SAIL_HL_X86_COUNT_PLAIN_CLAIMS;;
if length SAIL_HL_X86_COUNT_CLAIMS <> 21 ||
   length(setify(map fst SAIL_HL_X86_COUNT_CLAIMS)) <> 21 then
  failwith "wrong count claim inventory";;

(* CLAIMS END *)

List.iter sail_hl_report SAIL_HL_X86_COUNT_CLAIMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_COUNT_PROOFS_OK";;
