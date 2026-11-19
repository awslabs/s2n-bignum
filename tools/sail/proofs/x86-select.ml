(* Condition-code, extension and byte-swap instructions on registers.

   Each claim compares the whole generated relation with s2n-bignum's
   instruction, for every register, flag and remaining state. The root
   fixes the opcode byte of dispatch_2byte_gpr, so each condition code
   (CMOVcc, SETcc) and each BSWAP register is its own root, as docs/X86.md
   explains; the branch keeps its ModR/M decoding and operand access.

   - CMOVcc at 32 and 64 bits (the widths the s2n-bignum decoder accepts)
     against x86_CMOV with the matching Condition_ constructor. The
     32-bit form writes, and so zero-extends, its destination whether or
     not the condition holds, as x86_CMOV does through GPR32_Z.
   - SETcc on a REX or legacy byte register.
   - MOVZX and MOVSX from a byte (REX or legacy) or word register to a
     32- or 64-bit register. The 64-bit destination needs REX, so there is
     no legacy 64-bit form.
   - BSWAP of a 32- or 64-bit register: the low three bits come from the
     opcode, REX.B is the parameter b.
   - MOVSXD (63 /r) to a 64-bit register (REX.W) or a 32-bit one, from a
     32-bit register, against x86_MOVSX. Its opcode branch in
     decode_execute fetches ModR/M once per processor mode (and holds ARPL
     for the others); the entry replaces the LongMode call (selected_call
     0) and leaves the others as original code, dead under the assumption
     cur_mode = LongMode. *)
needs "x86/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-select-lemmas.ml";;
needs "tools/sail/proofs/fresh-model.ml";;

let sail_hl_select_standard_new_definition = new_definition;;
let sail_hl_select_before = definitions ();;
module Sail_hl_x86_select_model = struct
let new_definition = Sail_hl_fresh_model.new_definition;;
loadt "tools/sail/_build/x86-select.ml";;
end;;
open Sail_hl_x86_select_model;;
let new_definition = sail_hl_select_standard_new_definition;;
let sail_hl_select_definitions =
  filter (fun theorem -> not(mem theorem sail_hl_select_before))
    (definitions ());;

let SAIL_HL_X86_SELECT_CONDITIONS =
  ["O";"NO";"B";"NB";"Z";"NZ";"BE";"NBE";"S";"NS";"P";"NP";"L";"NL";"LE";"NLE"];;

let sail_hl_select_constant root =
  "sail_hl_" ^ String.concat "_5f" (String.split_on_char '_' root);;

(* Prove one statement and report its name and CPU time. *)
let sail_hl_select_claim root statement tactic =
  let name = "SAIL_HL_" ^ root ^ "_EQ" in
  print_endline(name ^ " starting");
  let started = Sys.time() in
  let theorem = prove(parse_term statement, tactic) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name,theorem;;

let SAIL_HL_X86_CMOV_CLAIMS =
  List.concat_map (fun condition ->
    map (fun width ->
      let root = Printf.sprintf "X86_CMOV%s%d_RR" condition width in
      let component = SAIL_HL_X86_GPR_COMPONENT width false in
      sail_hl_select_claim root (Printf.sprintf
        "!d m:4 word. !s t:x86state. %s d m s t <=> \
         x86_CMOV Condition_%s %s %s s t"
        (sail_hl_select_constant root) condition
        (component "d") (component "m"))
        (SAIL_HL_X86_SELECT_TAC sail_hl_select_definitions [width] []
          [x86_CMOV; condition_semantics])) [64;32])
    SAIL_HL_X86_SELECT_CONDITIONS;;

let SAIL_HL_X86_SET_CLAIMS =
  List.concat_map (fun condition ->
    map (fun legacy ->
      let root = Printf.sprintf "X86_SET%s8%s_R" condition
        (if legacy then "_LEGACY" else "") in
      sail_hl_select_claim root (Printf.sprintf
        "!m:%d word. !s t:x86state. %s m s t <=> \
         x86_SET Condition_%s %s s t"
        (if legacy then 3 else 4) (sail_hl_select_constant root) condition
        (SAIL_HL_X86_GPR_COMPONENT 8 legacy "m"))
        (SAIL_HL_X86_SELECT_TAC sail_hl_select_definitions [8]
          (if legacy then ["m"] else []) [x86_SET; condition_semantics]))
      [false;true])
    SAIL_HL_X86_SELECT_CONDITIONS;;

(* The destination field d of a legacy-encoded extension has three bits;
   a no-REX 32-bit register is one of the first eight. *)
let SAIL_HL_X86_EXTENSION_DESTINATION width legacy =
  let index = if legacy then "(word_zx d:4 word)" else "d" in
  if width = 64 then "(registers :> element " ^ index ^ ")"
  else "(GPR32_Z(Gpr " ^ index ^ " Lower_32))";;

let SAIL_HL_X86_EXTENSION_CLAIMS =
  List.concat_map (fun (operation,instruction) ->
    map (fun (source,legacy,width) ->
      let root = Printf.sprintf "X86_%s%d_%d%s_RR" operation width source
        (if legacy then "_LEGACY" else "") in
      sail_hl_select_claim root (Printf.sprintf
        "!d m:%d word. !s t:x86state. %s d m s t <=> x86_%s %s %s s t"
        (if legacy then 3 else 4) (sail_hl_select_constant root) operation
        (SAIL_HL_X86_EXTENSION_DESTINATION width legacy)
        (if source = 16 then SAIL_HL_X86_GPR_COMPONENT 16 false "m"
         else SAIL_HL_X86_GPR_COMPONENT 8 legacy "m"))
        (SAIL_HL_X86_SELECT_TAC sail_hl_select_definitions [width;source]
          (if legacy then ["m"] else [])
          (instruction :: SAIL_HL_X86_SX_TRUNCATE)))
      [8,false,64; 8,false,32; 8,true,32; 16,false,64; 16,false,32])
    ["MOVZX",x86_MOVZX; "MOVSX",x86_MOVSX];;

(* MOVSXD copies a 32-bit register with sign extension to 64 bits (REX.W)
   or plainly to a 32-bit register. s2n-bignum decodes both as x86_MOVSX
   with a 32-bit source. *)
let SAIL_HL_X86_MOVSXD_CLAIMS =
  map (fun width ->
    let root = Printf.sprintf "X86_MOVSXD%d_32_RR" width in
    sail_hl_select_claim root (Printf.sprintf
      "!d m:4 word. !s t:x86state. %s d m s t <=> x86_MOVSX %s %s s t"
      (sail_hl_select_constant root)
      (SAIL_HL_X86_GPR_COMPONENT width false "d")
      (SAIL_HL_X86_GPR_COMPONENT 32 false "m"))
      (SAIL_HL_X86_SELECT_TAC sail_hl_select_definitions [width;32] []
        [x86_MOVSX; WORD_SX_TRIVIAL]))
    [64;32];;

let SAIL_HL_X86_BSWAP_CLAIMS =
  List.concat_map (fun width ->
    map (fun low ->
      let root = Printf.sprintf "X86_BSWAP%d_R%d" width low in
      let register = Printf.sprintf "(word_join (b:1 word) (word %d:3 word):4 word)" low in
      sail_hl_select_claim root (Printf.sprintf
        "!b:1 word. !s t:x86state. %s b s t <=> x86_BSWAP %s s t"
        (sail_hl_select_constant root)
        (if width = 64 then "(registers :> element " ^ register ^ ")"
         else "(GPR32_Z(Gpr " ^ register ^ " Lower_32))"))
        (SAIL_HL_X86_SCALAR_TAC sail_hl_select_definitions [width] []
          (x86_BSWAP :: SAIL_HL_X86_BSWAP_FACTS)))
      (0--7))
    [64;32];;

let SAIL_HL_X86_SELECT_CLAIMS =
  SAIL_HL_X86_CMOV_CLAIMS @ SAIL_HL_X86_SET_CLAIMS @
  SAIL_HL_X86_EXTENSION_CLAIMS @ SAIL_HL_X86_MOVSXD_CLAIMS @
  SAIL_HL_X86_BSWAP_CLAIMS;;
if length SAIL_HL_X86_SELECT_CLAIMS <> 92 ||
   length(setify(map fst SAIL_HL_X86_SELECT_CLAIMS)) <> 92 then
  failwith "wrong select claim inventory";;
List.iter sail_hl_report SAIL_HL_X86_SELECT_CLAIMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_SELECT_PROOFS_OK";;
