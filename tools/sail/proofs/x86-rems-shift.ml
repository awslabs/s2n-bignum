(* REMS register shifts and rotates, compared with s2n-bignum.

   Each REMS root takes HOL's low 32 RFLAGS bits and RIP, one or two
   register fields and an arbitrary count byte. The bodies mask the count
   to six bits for 64-bit operands and five bits otherwise; the claims use
   s2n-bignum's relation at the same masked count, val count MOD 64 or
   MOD 32. Claims compare the core observation of the REMS root, which
   restores the entry RIP, with the whole s2n-bignum relation. Register
   values, flags and aliases stay unrestricted.

   Agreement: SHL/SHR at every width and encoding, SAR at 64 and 32 bits,
   RCL/RCR at 64 and 32 bits and SHLD/SHRD at 64, 32 and 16 bits. The
   remaining 19 forms differ from s2n-bignum; their _DIFF theorems
   exhibit a final state one relation permits and the other rejects, as
   recorded in docs/X86-DIVERGENCES.md:
     ROL/ROR        at masked count zero REMS leaves OF undefined;
     ROR            at count 2 REMS takes CF from the result's low bit;
     SAR 16/8/8L    at counts of at least the width REMS leaves CF
                    undefined;
     ROL/ROR/RCL/RCR 16/8/8L  above the rotated width REMS shifts by a
                    negative amount, whose result is unknown. *)
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-rems-shift-lemmas.ml";;
needs "tools/sail/proofs/fresh-model.ml";;

let sail_hl_rems_shift_before = definitions ();;
(* Declare each supplied body directly. The generated file finally
   rewrites every root with its helpers and reduces numerals over the
   whole body; the proofs evaluate the helpers by value instead. Both
   post-passes are skipped here: on these large bodies the numeral pass
   alone takes tens of minutes. *)
module Sail_hl_x86_rems_shift_model = struct
let new_definition = Sail_hl_fresh_model.new_definition;;
let REWRITE_RULE (_:thm list) (theorem:thm) = theorem;;
let CONV_RULE (_:conv) (theorem:thm) = theorem;;
loadt "tools/sail/_build/x86-rems-shift.ml";;
end;;
let sail_hl_rems_shift_definitions =
  filter (fun theorem -> not(mem theorem sail_hl_rems_shift_before))
    (definitions ());;

let sail_hl_rems_shift_compset = SAIL_HL_X86_REMS_COMPSET
  sail_hl_rems_shift_definitions
  Sail_hl_x86_rems_shift_model.sail_hl_case_x86_2drems_2dshift_result
  Sail_hl_x86_rems_shift_model.sail_hl_type_x86_2drems_2dshift_proc_5fmode_DISTINCT;;

let sail_hl_rems_shift_facts =
  map (fun width -> width, SAIL_HL_X86_REMS_FACTS width) [8;16;32;64];;

let sail_hl_x86_rems_shift_root operation width legacy double =
  Printf.sprintf "X86_REMS_%s%d%s_%s" operation width
    (if legacy then "_LEGACY" else "") (if double then "RRI" else "RI");;

let sail_hl_x86_rems_constant root =
  "sail_hl_" ^ String.concat "_5f" (String.split_on_char '_' root);;

let sail_hl_x86_rems_count_bits width = if width = 64 then 6 else 5;;

(* The normalized REMS relation for literal or variable operands. *)
let sail_hl_x86_rems_shift_normalized root width operands =
  let applied = list_mk_comb(mk_const(sail_hl_x86_rems_constant root,[]),
    [`rflags :> bottom_32`; `RIP`] @ operands @ [`s:x86state`; `u:x86state`]) in
  GEN_ALL(SAIL_HL_X86_REMS_SHIFT_NORMALIZE sail_hl_rems_shift_compset
    (assoc width sail_hl_rems_shift_facts)
    (sail_hl_x86_rems_count_bits width) applied);;

let SAIL_HL_X86_REMS_SHIFT_CLAIM (operation,instruction,width,legacy,double) =
  let bits = if legacy then 3 else 4 in
  let root = sail_hl_x86_rems_shift_root operation width legacy double in
  let constant = sail_hl_x86_rems_constant root in
  let names = if double then ["d";"m"] else ["d"] in
  let registers = map (fun name ->
    mk_var(name, mk_type("word",[mk_finty(num bits)]))) names in
  let statement = parse_term(Printf.sprintf
    "!%s:%d word. !count:8 word. !s t:x86state. \
     sail_hl_x86_core (%s (rflags :> bottom_32) RIP %s count) s t <=> \
     x86_%s %s (val count MOD %d) s t"
    (String.concat " " names) bits constant (String.concat " " names)
    operation (String.concat " "
      (map (SAIL_HL_X86_GPR_COMPONENT width legacy) names))
    (1 lsl sail_hl_x86_rems_count_bits width)) in
  let name = "SAIL_HL_" ^ root ^ "_EQ" in
  print_endline(name ^ " starting");
  let started = Sys.time() in
  let normalized = sail_hl_x86_rems_shift_normalized root width
    (registers @ [`count:8 word`]) in
  Printf.printf "normalized: %.3fs\n%!" (Sys.time() -. started);
  let _,_,narrowing = assoc width sail_hl_rems_shift_facts in
  let theorem = prove(statement,
    SAIL_HL_X86_REMS_SHIFT_CLAIM_TAC normalized instruction narrowing
      (if legacy then registers else [])
      (sail_hl_x86_rems_count_bits width) width) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name,theorem;;

let sail_hl_rems_shift_claims =
  map SAIL_HL_X86_REMS_SHIFT_CLAIM
   (List.concat_map (fun (width,legacy) ->
      ["SHL",SAIL_HL_X86_SHL_DEF,width,legacy,false; "SHR",SAIL_HL_X86_SHR_DEF,width,legacy,false])
      [64,false; 32,false; 16,false; 8,false; 8,true] @
    ["SAR",x86_SAR,64,false,false; "SAR",x86_SAR,32,false,false;
     "RCL",x86_RCL,64,false,false; "RCL",x86_RCL,32,false,false;
     "RCR",x86_RCR,64,false,false; "RCR",x86_RCR,32,false,false] @
    List.concat_map (fun width ->
      ["SHLD",SAIL_HL_X86_SHLD_DEF,width,false,true; "SHRD",SAIL_HL_X86_SHRD_DEF,width,false,true])
      [64; 32; 16]);;

if length sail_hl_rems_shift_claims <> 22 then
  failwith "wrong REMS shift agreement inventory";;

(* Witness states: register 0 holds x; CF and OF are clear; every other
   component is that of an arbitrary state s. *)
let sail_hl_x86_rems_diff_initial = new_definition
 `sail_hl_x86_rems_diff_initial (x:64 word) (s:x86state) =
   write OF F (write CF F (write (registers :> element (word 0)) x s))`;;

(* One witness: the instruction, width and encoding, the literal value of
   register 0, the count byte, the final state as a function of the
   initial state, the component that tells the relations apart, whether
   REMS permits the final state that s2n-bignum rejects, and values for
   unknown words that are not written directly. *)
let SAIL_HL_X86_REMS_WITNESS (operation,instruction,width,legacy,value,
                              count,final,observed,permits,hints) =
  let root = sail_hl_x86_rems_shift_root operation width legacy false in
  let bits = if legacy then 3 else 4 in
  let register = Printf.sprintf "(word 0:%d word)" bits in
  let initial = Printf.sprintf "sail_hl_x86_rems_diff_initial (word %d) s" value in
  let final = final initial in
  let core relation = Printf.sprintf "sail_hl_x86_core (%s) (%s) (%s)"
    relation initial final in
  let rems = core (Printf.sprintf "%s (rflags :> bottom_32) RIP %s (word %d)"
    (sail_hl_x86_rems_constant root) register count) in
  let s2n = Printf.sprintf "x86_%s %s %d (%s) (%s)" operation
    (SAIL_HL_X86_GPR_COMPONENT width legacy register) count initial final in
  let pair a b = parse_term(Printf.sprintf "%s /\\ ~(%s)" a b) in
  let normalized = sail_hl_x86_rems_shift_normalized root width
    [mk_comb(inst [mk_finty(num bits),`:N`] `word:num->N word`, `0`);
     mk_comb(`word:num->8 word`, mk_small_numeral count)] in
  let start = REWRITE_TAC[sail_hl_x86_rems_diff_initial] in
  (* With register 0 known, evaluate what remains of the REMS calculation. *)
  let rems_tac = start THEN SAIL_HL_X86_REMS_CORE_UNFOLD_TAC normalized THEN
    CONV_TAC(Compute.CBV_CONV sail_hl_rems_shift_compset) THEN
    CONV_TAC(DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC WORD_REDUCE_CONV) in
  let s2n_tac = start THEN SAIL_HL_X86_REMS_UNFOLD_TAC [instruction] in
  let prove_pair a b ta tb = prove(pair a b, CONJ_TAC THENL
    [ta THEN SAIL_HL_X86_REMS_PERMITS_WITH_TAC hints;
     tb THEN SAIL_HL_X86_REMS_REJECTS_TAC observed]) in
  if permits then prove_pair rems s2n rems_tac s2n_tac
  else prove_pair s2n rems s2n_tac rems_tac;;

(* The counterexamples of one form against s2n-bignum. *)
let SAIL_HL_X86_REMS_DIFF root witnesses =
  "SAIL_HL_" ^ root ^ "_DIFF", GEN `s:x86state`
    (end_itlist CONJ (map SAIL_HL_X86_REMS_WITNESS witnesses));;

let sail_hl_x86_rems_zero_of instruction operation width legacy =
  operation,instruction,width,legacy,0,0,
  (fun initial -> "write OF T (" ^ initial ^ ")"),`OF`,true,[];;

let sail_hl_x86_rems_ror_cf width legacy =
  "ROR",x86_ROR,width,legacy,4,2,
  (fun initial -> "write (registers :> element (word 0)) (word 1) (" ^ initial ^ ")"),
  `CF`,false,[];;

let sail_hl_x86_rems_sar_cf width legacy =
  let value = if width = 8 then 255 else 65535 in
  "SAR",x86_SAR,width,legacy,value,width,
  (fun initial -> "write ZF F (write SF T (write PF T (" ^ initial ^ ")))"),
  `CF`,true,[];;

(* 8- and 16-bit rotates by a count above the rotated width, w + 1 bits
   for RCL/RCR with CF: REMS shifts by a negative amount, whose result is
   unknown. With register 0 holding 1, REMS permits the register to keep
   1, the OCaml runtime's result for ROL/RCL, whereas s2n-bignum rotates
   by the count modulo the rotated width: by one bit, giving 2 for
   ROL/RCL, 0x80 or 0x8000 for ROR and 0 for RCR. CF is the low result bit
   for ROL/ROR and bit w for RCL/RCR. *)
let sail_hl_x86_rems_wide_rotate instruction operation width legacy =
  let carry = mem operation ["RCL"; "RCR"] in
  let rotated = if carry then width + 1 else width in
  operation,instruction,width,legacy,1,rotated + 1,
  (fun initial -> if carry then initial else "write CF T (" ^ initial ^ ")"),
  `registers :> element (word 0:4 word)`,true,
  [mk_comb(inst [mk_finty(num rotated),`:N`] `word:num->N word`, `1`)];;

let sail_hl_rems_shift_differences = map (fun (root,witnesses) ->
  SAIL_HL_X86_REMS_DIFF root witnesses)
 (List.concat_map (fun (operation,instruction) ->
   map (fun (width,legacy) ->
     let wide = width <= 16 in
     sail_hl_x86_rems_shift_root operation width legacy false,
     (if wide then [sail_hl_x86_rems_wide_rotate instruction operation width legacy]
      else []) @
     (if mem operation ["ROL"; "ROR"]
      then [sail_hl_x86_rems_zero_of instruction operation width legacy] else []) @
     (if operation = "ROR" then [sail_hl_x86_rems_ror_cf width legacy] else []))
     ((if mem operation ["ROL"; "ROR"] then [64,false; 32,false] else []) @
      [16,false; 8,false; 8,true]))
  ["ROL",x86_ROL; "ROR",x86_ROR; "RCL",x86_RCL; "RCR",x86_RCR] @
  ["X86_REMS_SAR16_RI", [sail_hl_x86_rems_sar_cf 16 false];
   "X86_REMS_SAR8_RI", [sail_hl_x86_rems_sar_cf 8 false];
   "X86_REMS_SAR8_LEGACY_RI", [sail_hl_x86_rems_sar_cf 8 true]]);;

if length sail_hl_rems_shift_differences <> 19 then
  failwith "wrong REMS shift counterexample inventory";;
List.iter sail_hl_report
  (sail_hl_rems_shift_claims @ sail_hl_rems_shift_differences);;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_REMS_SHIFT_PROOFS_OK";;
