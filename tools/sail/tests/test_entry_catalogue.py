#!/usr/bin/env python3
"""Check Arm's export requests using Sail's OCaml syntax-tree library.

The fingerprint fixes all 1,404 names, operand types, modes and source
calls. Independent examples check aliases, field domains, operand order
and feature/half selectors. The 146 additional memory forms and the 8
scalar DUP forms are checked exhaustively. This does not count
instruction proofs or replace generation with the actual Sail model.
"""
import hashlib
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import _project
import coverage
import x86_forms
from x86_forms import required_forms

ROOT = _project.ROOT
# Changes to operand types, encodings or Sail's AST rendering need a reviewed
# update of this fingerprint, rather than being accepted silently.
CATALOGUE_SHA256 = "86167501d84dd872a0dfeb18af2cc598023770823cf6c10dbc91d54ca3939676"
MEMORY_FAMILIES = (
    "memory-pair", "memory-four", "memory-structure2", "memory-structure3",
    "memory-replicate",
)

HARNESS = r'''
open Libsail
open Ast
open Ast_defs
open Ast_util

let require condition message = if not condition then failwith message
let entries = Arm.entries
let root name = List.find (fun (entry : Entry.t) -> entry.name = name) entries
let names entries =
  List.sort String.compare (List.map (fun (entry : Entry.t) -> entry.name) entries)
let normalize_type typ =
  Str.global_replace (Str.regexp_string "bits(") "bitvector(" (string_of_typ typ)

(* Single-statement blocks do not change the parameter wrapper. Leave all
   operators and expression nodes otherwise unchanged. *)
let normalize_body body =
  let e_block = function
    | [E_aux (body, _)] -> body
    | bodies -> E_block bodies in
  let body = Rewriter.fold_exp {Rewriter.id_exp_alg with e_block} body in
  Str.global_replace (Str.regexp_string "bits(") "bitvector(" (string_of_exp body)

(* Retain the baseline column spelling while checking the completion
   requirement. Both kinds now export relations, never state functions. *)
let mode (entry : Entry.t) = if entry.retirement then "retirement" else "state"

let check_closure requested expected =
  let actual = names (Entry.closure entries (List.map root requested)) in
  require (actual = List.sort String.compare expected)
    ("incorrect alias closure: " ^ String.concat "," requested)

let audit_catalogue () =
  require (List.length entries = 1404) "complete Arm catalogue root count changed";
  require (List.length (names entries) =
    List.length (List.sort_uniq String.compare (names entries))) "duplicate Arm root";
  List.iter (fun (entry : Entry.t) ->
    let expanded = names (Entry.closure entries [entry]) in
    require (List.mem entry.name expanded) ("lost requested root " ^ entry.name);
    List.iter (fun dependency ->
      if List.exists (fun (e : Entry.t) -> e.name = dependency) entries then
        require (List.mem dependency expanded)
          ("unclosed catalogue alias: " ^ entry.name ^ " -> " ^ dependency)
    ) (Entry.dependencies entry);
    Printf.printf "ENTRY\t%s\t%s\t%s\t%s\t%s\t%s\n"
      entry.family entry.name
      (String.concat "," (List.map (fun (name, typ) ->
        name ^ ":" ^ normalize_type typ) entry.parameters))
      (normalize_type entry.result) (mode entry) (normalize_body entry.body)
  ) entries;
  List.iter (fun (requested, expected) -> check_closure [requested] expected) [
    "arm_CINC32", ["arm_CINC32"; "arm_CSINC32"];
    "arm_CINV64", ["arm_CINV64"; "arm_CSINV64"];
    "arm_CNEG64", ["arm_CNEG64"; "arm_CSNEG64"];
    "arm_CSET32", ["arm_CSET32"; "arm_CSINC32"];
    "arm_CSETM64", ["arm_CSETM64"; "arm_CSINV64"];
    "arm_MUL32", ["arm_MUL32"; "arm_MADD32"];
    "arm_MNEG64", ["arm_MNEG64"; "arm_MSUB64"];
    "arm_UMULL64", ["arm_UMULL64"; "arm_UMADDL64"];
    "arm_UMNEGL64", ["arm_UMNEGL64"; "arm_UMSUBL64"]
  ];
  check_closure ["ARM_ADC32"; "ARM_ADC64"] ["ARM_ADC32"; "ARM_ADC64"];
  List.iter (fun (family, roots) ->
    require (List.length roots = List.length (List.sort_uniq String.compare roots))
      ("duplicate family root: " ^ family);
    List.iter (fun name ->
      require (List.exists (fun (entry : Entry.t) -> entry.name = name) entries)
        ("unknown family root: " ^ name)
    ) roots
  ) Arm.family_roots;
  require (List.length Arm.family_roots =
    List.length (List.sort_uniq String.compare (List.map fst Arm.family_roots)))
    "duplicate family name";
  List.iter (fun (family, expected) ->
    require (List.assoc family Arm.family_roots = expected)
      ("family bundle changed: " ^ family)
  ) [
    "branch-basic", ["arm_B"; "arm_BL"; "arm_RET"];
    "hints", ["arm_NOP"; "arm_BTI_C"];
    "fp-select", ["arm_FCSEL32"; "arm_FCSEL64"];
    "vector-polynomial-multiply", ["arm_PMUL_VEC64E8"; "arm_PMUL_VEC128E8"];
    "vector-poly", ["arm_PMULL_VEC128E8"; "arm_PMULL_VEC128E64";
      "arm_PMULL2_VEC128E8"; "arm_PMULL2_VEC128E64"];
    "vector-fpbits", ["arm_FMOV_FtoI32_LO"; "arm_FMOV_FtoI64_LO";
      "arm_FMOV_FtoI64_HI"; "arm_FMOV_ItoF64_LO"; "arm_FMOV_ItoF64_HI"]
  ];
  Printf.printf "AUDIT\t1404 roots\t9 alias cases\t%d family bundles\n"
    (List.length Arm.family_roots)

(* Cut identities and value-effect permissions are separate choices. In
   particular, memory writes must not acquire an impure value
   interpretation merely because they occur in the cut list. *)
let audit_contracts () =
  let open Entry in
  require (Arm.contracts = [
    "X_read", true; "X_set", false; "SP_read", true; "SP_set", false;
    "V_read", true; "V_set", false; "CheckFPAdvSIMDEnabled64", false;
    "CheckFPEnabled64", false; "AArch64_CheckFPAdvSIMDEnabled", false;
    "BranchTo", false; "BranchNotTaken", false;
    "IsFeatureImplemented", true; "SCTLR_read__1", true;
    "CreateAccDescGPR", true; "CreateAccDescASIMD", true;
    "Mem_read", true; "Mem_set", false; "Mem_read__1", true; "Mem_set__1", false;
    "BigEndian", true; "EndOfInstruction", false
  ]) "Arm cut identities or value-effect permissions changed";
  require (Rv32.contracts = [
    "rX_bits", true; "wX_bits", false;
    "get_arch_pc", true; "get_next_pc", true; "set_next_pc", false;
    "vmem_read", false; "vmem_write", false; "currentlyEnabled", true;
    "trap", true; "exception_context", true;
    "sail_barrier", true; "generate_event", true; "is_fiom_active", true
  ]) "RV32 cut identities or value-effect permissions changed";
  require (Arm.faults = ["AArch64_SPAlignmentFault"])
    "architectural fault boundaries changed";
  require (Arm.cuts = List.map fst Arm.contracts @ Arm.faults &&
           Rv32.cuts = List.map fst Rv32.contracts) "cuts differ from their contracts";
  print_endline "CONTRACT-AUDIT\t22 Arm cuts\t13 RV32 cuts"

(* The full fingerprint fixes every call. These independent examples make
   important choices visible rather than reproducing every family factory:
   operand order, all indexed field domains, source halves and feature paths.
   Neither check establishes Sail-to-HOL translation correctness. *)
let audit_selections () =
  let open Entry in
  let u name = call "unsigned" [id name] in
  let fields names = List.map (fun name -> name, word 5) names in
  let field_width lanes = match lanes with
    | 1 -> 0 | 2 -> 1 | 4 -> 2 | 8 -> 3 | 16 -> 4 | 32 -> 5 | 64 -> 6
    | _ -> failwith "unexpected selection field domain" in
  let vector operation width element =
    Printf.sprintf "arm_%s%dE%d" operation width element in
  let plus left right = mk_exp (E_app (mk_operator "+", [left; right])) in
  let literal width value =
    mk_lit_exp (L_bin (non_empty_singleton (List.init width (fun index ->
      if value land (1 lsl (width - index - 1)) = 0 then Bin_0 else Bin_1)))) in
  let checked = ref [] in
  let check family name parameters source arguments =
    let entry = root name in
    require (entry.family = family && not entry.retirement)
      ("incorrect selection family/mode: " ^ name);
    require (List.map (fun (n,t) -> n, normalize_type t) entry.parameters =
             List.map (fun (n,t) -> n, normalize_type t) parameters)
      ("incorrect selection parameter domain/order: " ^ name);
    require (normalize_type entry.result = normalize_type unit_typ)
      ("incorrect selection result: " ^ name);
    require (normalize_body entry.body = normalize_body (call source arguments))
      ("incorrect selection source call: " ^ name);
    checked := name :: !checked in
  check "carry" "ARM_ADC64" (fields ["d"; "n"; "m"])
    "execute_aarch64_instrs_integer_arithmetic_add_sub_carry"
    [call "UInt" [id "d"]; int 64; call "UInt" [id "m"]; call "UInt" [id "n"];
     bool false; bool false];
  check "carry" "ARM_NGC32" (fields ["d"; "m"])
    "execute_aarch64_instrs_integer_arithmetic_add_sub_carry"
    [call "UInt" [id "d"]; int 32; call "UInt" [id "m"]; int 31; bool false; bool true];
  List.iter (fun (operation, source, part, subtract, unsigned) ->
    List.iter (fun element ->
      check "vector-addsub-widen" (vector operation 128 element)
        (fields ["d"; "n"; "m"])
        ("execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_" ^ source)
        [u "d"; int 64; int (64 / element); int element; u "m"; u "n";
         int part; bool subtract; bool unsigned]
    ) [8;32]
  ) ["SSUBL", "long", 0, true, false; "USUBL2", "long", 1, true, true;
     "SADDW2", "wide", 1, false, false];
  List.iter (fun element ->
    List.iter (fun high ->
      let index = if element = 64 then int (if high then 1 else 0)
        else if high then plus (u "index") (int (64 / element)) else u "index" in
      check "vector-insert"
        (vector "INS" 128 element ^ if high then "_HI" else "_LO")
        (fields ["d"; "n"] @ ["dest", word (field_width (128 / element))] @
         if element = 64 then [] else ["index", word (field_width (64 / element))])
        "execute_aarch64_instrs_vector_transfer_vector_insert"
        [u "d"; u "dest"; int element; int (if high then 128 else 64); u "n"; index]
    ) [false;true];
    check "vector-insert" (vector "INS_GEN" 128 element)
      (fields ["d"; "n"] @ ["dest", word (field_width (128 / element))])
      "execute_aarch64_instrs_vector_transfer_integer_insert"
      [u "d"; int 128; int element; u "dest"; u "n"]
  ) [8;16;32;64];
  check "vector-round-halving" "arm_URHADD_VEC128E16" (fields ["d"; "n"; "m"])
    "execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding"
    [u "d"; int 128; int 8; int 16; u "m"; u "n"; bool true];
  check "vector-variable-shift" "arm_USHL_VEC64E8" (fields ["d"; "n"; "m"])
    "execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd"
    [u "d"; int 64; int 8; int 8; u "m"; u "n"; bool false; bool false; bool true];
  check "fp-select" "arm_FCSEL32" (("condition", word 4) :: fields ["d"; "n"; "m"])
    "execute_aarch64_instrs_float_move_fp_select"
    [id "condition"; u "d"; int 32; u "m"; u "n"];
  check "vector-fpbits" "arm_FMOV_ItoF64_HI" (fields ["d"; "n"])
    "execute_aarch64_instrs_float_convert_int"
    [u "d"; int 64; int 64; u "n"; id "FPConvOp_MOV_ItoF"; int 1;
     id "FPRounding_TIEEVEN"; bool false];
  check "vector-table" "arm_TBL3128" (fields ["d"; "n"; "m"])
    "execute_aarch64_instrs_vector_transfer_vector_table"
    [u "d"; int 128; int 16; bool true; u "m"; u "n"; int 3];
  List.iter (fun (operation, part, round) ->
    List.iter (fun element ->
      check "vector-saturating-narrow" (vector operation 64 element)
        (("amount", word (field_width element)) :: fields ["d"; "n"])
        "execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd"
        [u "d"; int 64; int (64 / element); int element; u "n"; int part;
         bool round; plus (u "amount") (int 1)]
    ) [8;16;32]
  ) ["SQSHRUN",0,false; "SQSHRUN2",1,false;
     "SQRSHRUN",0,true; "SQRSHRUN2",1,true];
  List.iter (fun (operation, round) ->
    List.iter (fun width ->
      List.iter (fun element ->
        check "vector-doubling" (vector operation width element)
          (fields ["d"; "n"; "m"])
          "execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd"
          [u "d"; int width; int (width / element); int element; u "m"; u "n"; bool round];
        List.iter (fun high ->
          check "vector-doubling"
            (vector operation width element ^ if high then "_HI" else "_LO")
            (fields ["d"; "n"] @ ["m",word (if element = 16 then 4 else 5);
              "index",word (if element = 16 then 2 else 1)])
            "execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd"
            [u "d"; int width; int (width / element); int element;
             int (if high then 128 else 64);
             (if high then plus (u "index") (int (64 / element)) else u "index");
             u "m"; u "n"; bool round]
        ) [false;true]
      ) [16;32]
    ) [64;128]
  ) ["SQDMULH_VEC",false; "SQRDMULH_VEC",true];
  List.iter (fun width ->
    check "vector-polynomial-multiply" (vector "PMUL_VEC" width 8) (fields ["d"; "n"; "m"])
      "execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product"
      [u "d"; int width; int (width / 8); int 8; u "m"; u "n"; bool true]
  ) [64;128];
  List.iter (fun (operation, part) ->
    List.iter (fun element ->
      check "vector-poly" (vector operation 128 element) (fields ["d"; "n"; "m"])
        "decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly"
        [id "d"; id "n"; id "m"; literal 2 (if element = 8 then 0 else 3); literal 1 part]
    ) [8;64]
  ) ["PMULL_VEC",0; "PMULL2_VEC",1];
  require (List.length !checked = List.length (List.sort_uniq String.compare !checked))
    "duplicate independently checked selection";
  Printf.printf "SELECTION-AUDIT\t%d exact source calls and domains\n"
    (List.length !checked)

(* Check every new memory request independently of the table builders.
   The source signatures take encoded fields, not selected register values.
   Retaining bitvector(5) for all register parameters admits index 31 and
   every overlap; consecutive vector indices are computed upstream. *)
let audit_memory () =
  let open Entry in
  let fields names = List.map (fun name -> name, word 5) names in
  let literal width value =
    mk_lit_exp (L_bin (non_empty_singleton (List.init width (fun index ->
      if value land (1 lsl (width - index - 1)) = 0 then Bin_0 else Bin_1)))) in
  let checked = ref [] in
  let check family name parameters source arguments =
    let entry = root name in
    require (entry.family = family && not entry.retirement)
      ("incorrect memory family/completion: " ^ name);
    require (List.map (fun (n,t) -> n, normalize_type t) entry.parameters =
             List.map (fun (n,t) -> n, normalize_type t) parameters)
      ("incorrect memory parameter domain/order: " ^ name);
    require (normalize_type entry.result = normalize_type unit_typ)
      ("incorrect memory result: " ^ name);
    require (normalize_body entry.body = normalize_body (call source arguments))
      ("incorrect memory source call: " ^ name);
    checked := name :: !checked in
  (* opc distinguishes GPR width from SIMD width; imm7 is deliberately not
     sign-expanded or scaled in the request. The decoder performs both. *)
  List.iter (fun (operation, l) ->
    List.iter (fun (width, view, source_view, opc) ->
      List.iter (fun (mode, source_mode) ->
        check "memory-pair"
          (Printf.sprintf "arm_%s%d_%s_%s" operation width view mode)
          (fields ["t"; "t2"; "n"] @ ["imm", word 7])
          ("decode_" ^ String.lowercase_ascii operation ^ "_" ^
           (if view = "GPR" then "gen" else "fpsimd") ^
           "_aarch64_instrs_memory_pair_" ^ source_view ^ "_" ^ source_mode)
          [id "t"; id "n"; id "t2"; id "imm"; literal 1 l; literal 2 opc]
      ) ["POST","post_idx"; "PRE","pre_idx"; "OFFSET","offset"]
    ) [32,"GPR","general",0; 64,"GPR","general",2;
       64,"SIMD","simdfp",1; 128,"SIMD","simdfp",2]
  ) ["LDP",1; "STP",0];
  let multiple family operation width mnemonic opcode element size mode l =
    let name = Printf.sprintf "arm_%s%d_SIMD_LD%d_E%d_%s"
      operation width mnemonic element mode in
    let suffix, parameters, arguments = match mode with
      | "NO" -> "no_wb", fields ["t"; "n"],
          [id "t"; id "n"; literal 2 size; literal 4 opcode; literal 1 l;
           literal 1 (if width = 128 then 1 else 0)]
      | "POSTI" -> "post_inc", fields ["t"; "n"],
          [id "t"; id "n"; literal 2 size; literal 4 opcode; literal 5 31;
           literal 1 l; literal 1 (if width = 128 then 1 else 0)]
      | "POSTR" -> "post_inc", fields ["t"; "n"; "m"],
          [id "t"; id "n"; literal 2 size; literal 4 opcode; id "m";
           literal 1 l; literal 1 (if width = 128 then 1 else 0)]
      | _ -> failwith "unknown memory test addressing mode" in
    check family name parameters
      (Printf.sprintf "decode_%s%d_advsimd_mult_aarch64_instrs_memory_vector_multiple_%s"
        (if l = 1 then "ld" else "st") mnemonic suffix) arguments in
  (* opcode=10 gives two whole Q registers, not LD2 interleaving. *)
  List.iter (fun (operation, l) ->
    List.iter (fun (element, size) ->
      List.iter (fun mode ->
        multiple "memory-pair" operation 128 1 10 element size mode l
      ) ["NO"; "POSTI"; "POSTR"]
    ) [8,0; 16,1; 32,2; 64,3]
  ) ["LDP",1; "STP",0];
  (* opcode=2 gives four whole registers; all four size fields are legal
     for both D and Q because the source selects one structure element. *)
  List.iter (fun (operation, l) ->
    List.iter (fun width ->
      List.iter (fun (element, size) ->
        List.iter (fun mode ->
          multiple "memory-four" operation width 1 2 element size mode l
        ) ["NO"; "POSTI"; "POSTR"]
      ) [8,0; 16,1; 32,2; 64,3]
    ) [64;128]
  ) ["LDP4",1; "STP4",0];
  List.iter (fun (family, mnemonic, opcode, operations, modes) ->
    List.iter (fun (operation, l) ->
      List.iter (fun (width, lanes) ->
        List.iter (fun (element, size) ->
          List.iter (fun mode ->
            multiple family operation width mnemonic opcode element size mode l
          ) modes
        ) lanes
      ) [64,[8,0;16,1;32,2]; 128,[8,0;16,1;32,2;64,3]]
    ) operations
  ) ["memory-structure2",2,8,["LD2",1;"ST2",0],["POSTI"];
     "memory-structure3",3,4,["LD3",1;"ST3",0],["POSTI";"POSTR"]];
  List.iter (fun width ->
    List.iter (fun (element, size) ->
      check "memory-replicate"
        (Printf.sprintf "arm_LD1R%d_SIMD_LD1R_E%d_POSTI" width element)
        (fields ["t"; "n"])
        "decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc"
        [id "t"; id "n"; literal 2 size; literal 1 0; literal 3 6;
         literal 5 31; literal 1 0; literal 1 1;
         literal 1 (if width = 128 then 1 else 0)]
    ) [8,0;16,1;32,2;64,3]
  ) [64;128];
  require (List.length !checked = 146 &&
           List.length (List.sort_uniq String.compare !checked) = 146)
    "missing or duplicate independently checked memory form";
  List.iter (fun (family, count) ->
    let actual = names (List.filter (fun (e : Entry.t) -> e.family = family) entries) in
    require (List.length actual = count &&
      actual = List.sort String.compare
        (List.filter (fun name -> (root name).family = family) !checked))
      ("memory family has an unaudited or missing form: " ^ family)
  ) ["memory-pair",48; "memory-four",48; "memory-structure2",14;
     "memory-structure3",28; "memory-replicate",8];
  print_endline "MEMORY-AUDIT\t146 exact source calls and domains"

(* The independent Python scope fixes every x86 name and operand domain.
   Check the decoded scalar choices here as actual Sail syntax trees:
   selected source function, acquired field, retained prefix and input order.
   This does not substitute for generation with the external source model. *)
let audit_x86 () =
  let open Entry in
  let root name =
    List.find (fun (entry : Entry.t) -> entry.name = name) X86_shina.entries in
  let text = string_of_exp in
  let rec field name = function
    | E_aux (E_struct_update (base,fields), _) ->
        (match List.find_opt (fun (FE_aux (FE_fexp (id,_),_)) ->
            string_of_id id = name) fields with
         | Some (FE_aux (FE_fexp (_,value),_)) -> value
         | None -> field name base)
    | _ -> failwith ("missing x86 prefix field: " ^ name) in
  let check_field prefix name expected =
    require (text (field name prefix) = text expected)
      ("incorrect x86 prefix field: " ^ name) in
  let call (entry : Entry.t) = match entry.body with
    | E_aux (E_app (id,args), _) -> string_of_id id,args
    | _ -> failwith ("incorrect x86 call shape: " ^ entry.name) in
  List.iter (fun (entry : Entry.t) ->
    require (not entry.retirement && string_of_typ entry.result = "unit")
      ("incorrect x86 completion/result: " ^ entry.name);
    Printf.printf "X86-ENTRY\t%s\t%s\t%s\n" entry.family entry.name
      (String.concat "," (List.map (fun (_,typ) -> normalize_type typ) entry.parameters))
  ) X86_shina.entries;
  List.iter (fun width ->
    List.iter (fun operation ->
      let entry = root (Printf.sprintf "X86_%s%d_RR" operation width) in
      let lift = List.hd entry.input_lifts in
      let source,args = call entry in
      let test = operation = "TEST" in
      require (source = lifted_name lift && lift.expected_inputs = 1 &&
        lift.input_function = "fetch" && lift.through = Some "fetch_modrm" &&
        lift.source_function = (if test then "decode_execute" else "dispatch_opcode_2byte") &&
        lift.fixed_arguments = (if test then [] else ["opcode",56]) &&
        lift.acquired = Some {
          callee = (if test then "scan_prefixes" else "fetch");
          fixed_binding = (if test then "opcode",133 else "opcode3",246)})
        ("incorrect x86 acquired source: " ^ entry.name);
      let prefix = match args with
        | [unit;prefix;_] when test && text unit = text Entry.unit -> prefix
        | [prefix;_] when not test -> prefix
        | _ -> failwith ("incorrect x86 supplied-input order: " ^ entry.name) in
      check_field prefix "rex_w" (bool (width = 64));
      check_field prefix "has_rex" (bool true);
      check_field prefix "has_opsize" (bool (operation = "ADCX"));
      if not test then check_field prefix "has_rep" (bool (operation = "ADOX"));
      require (X86_shina.assumptions [entry] =
        Initial_enum ("cur_mode","LongMode") ::
        (if test then [] else [Initial_bool ("has_adx",true)]))
        ("incorrect x86 acquired assumptions: " ^ entry.name)
    ) ["ADCX";"ADOX";"TEST"]
  ) [32;64];
  List.iter (fun (width,legacy) ->
    let name = Printf.sprintf "X86_TEST%d%s_RR" width
      (if legacy then "_LEGACY" else "") in
    let entry = root name in
    let source,args = call entry in
    let lift = List.hd entry.input_lifts in
    require (source = lifted_name lift &&
      lift.acquired = Some {callee="scan_prefixes";
        fixed_binding="opcode",(if width = 8 then 132 else 133)})
      ("incorrect narrow TEST opcode: " ^ name);
    let prefix = match args with
      | [unit;prefix;_] when text unit = text Entry.unit -> prefix
      | _ -> failwith ("incorrect narrow TEST input order: " ^ name) in
    check_field prefix "has_rex" (bool (not legacy));
    check_field prefix "has_opsize" (bool (width = 16));
    check_field prefix "rex_w" (bool false);
    if legacy then
      List.iter (fun name -> check_field prefix name
        (mk_lit_exp (L_bin (non_empty_singleton [Bin_0])))) ["rex_r";"rex_b"]
  ) [8,false;8,true;16,false];
  require (X86_shina.contracts = ["read_simd",true;"write_simd",false] &&
    X86_shina.cuts = List.map fst X86_shina.contracts) "x86 GPR helper unexpectedly became a cut";
  require (X86_shina.assumptions [root "X86_MULX32_RRR"] =
    [Initial_enum ("cur_mode","LongMode");Initial_bool ("has_bmi2",true)] &&
    X86_shina.assumptions [root "X86_ADD64_RR";root "X86_ADD8_LEGACY_RR"] = [] &&
    X86_shina.assumptions [root "X86_ADD32_RR";root "X86_SAR32_RI"] =
      [Initial_enum ("cur_mode","LongMode")]) "incorrect x86 mode/features";
  print_endline "X86-AUDIT\t205 roots\t9 acquisitions\tGPR helpers retained"

(* REMS selects decoded execution bodies with register-direct encodings.
   Its GPR accessors are the only cuts; RIP logging is fixed off. *)
let audit_x86_rems () =
  List.iter (fun (entry : Entry.t) ->
    require (not entry.retirement && string_of_typ entry.result = "unit")
      ("incorrect REMS completion/result: " ^ entry.name);
    Printf.printf "X86-REMS-ENTRY\t%s\t%s\t%s\n" entry.family entry.name
      (String.concat "," (List.map (fun (_,typ) -> normalize_type typ) entry.parameters))
  ) X86_rems.entries;
  require (X86_rems.source.contracts = ["read_gpr",true;"write_gpr",false])
    "REMS GPR accessors must be the only cuts";
  require (X86_rems.assumptions X86_rems.entries =
    [Entry.Initial_bool ("log_register_writes",false)])
    "incorrect REMS assumptions";
  print_endline "X86-REMS-AUDIT\tGPR accessors cut\tRIP logging off"

let () =
  audit_catalogue ();
  audit_contracts ();
  audit_selections ();
  audit_memory ();
  audit_x86 ();
  audit_x86_rems ()
'''


MODULES = ("entry", "arm", "rv32", "x86", "x86_shina", "x86_rems")


class EntryCatalogueTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not shutil.which("ocamlfind") or not shutil.which("ocamlopt"):
            raise AssertionError("Run inside the matching OCaml switch providing libsail")
        available = subprocess.run(
            ["ocamlfind", "query", "libsail"], capture_output=True, text=True)
        if available.returncode:
            raise AssertionError("The matching OCaml switch must provide libsail")
        cls.directory = tempfile.TemporaryDirectory(prefix="sail-entry-catalogue-")
        cls.addClassCleanup(cls.directory.cleanup)
        cls.build = Path(cls.directory.name)
        cls.includes = ["-I", str(cls.build)]
        # Link the installed AST library consistently. The plugin's separately
        # rebuilt Sail compiler may use different native checksums or Menhir
        # packaging; those compiler artifacts are not inputs to this audit.
        for module in MODULES:
            cls.run_command([
                "ocamlfind", "ocamlopt", *cls.includes, "-package", "libsail",
                "-c", str(ROOT / "backend" / (module + ".ml")),
                "-o", str(cls.build / (module + ".cmx"))])
        harness = cls.build / "audit.ml"
        harness.write_text(HARNESS)
        cls.executable = cls.build / "audit.native"
        cls.run_command([
            "ocamlfind", "ocamlopt", *cls.includes, "-package", "libsail,str", "-linkpkg",
            *(str(cls.build / (module + ".cmx")) for module in MODULES),
            str(harness), "-o", str(cls.executable)])
        cls.output = cls.run_command([str(cls.executable)])

    @staticmethod
    def run_command(command):
        result = subprocess.run(command, capture_output=True, text=True, timeout=60)
        if result.returncode:
            raise AssertionError(
                f"command failed ({result.returncode}): {' '.join(command)}\n"
                f"{result.stdout}\n{result.stderr}")
        return result.stdout

    def test_catalogue_matches_the_audited_baseline(self):
        rows = sorted(line for line in self.output.splitlines()
                      if line.startswith("ENTRY\t"))
        self.assertEqual(len(rows), 1404)
        fingerprint = hashlib.sha256(("\n".join(rows) + "\n").encode()).hexdigest()
        self.assertEqual(fingerprint, CATALOGUE_SHA256)

    def test_scalar_duplicate_forms_call_the_scalar_decoders_body(self):
        # The scalar decoder passes datasize = esize, one element, a 64- or
        # 128-bit source by imm5<4> and the index including that bit.
        source = "execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd"
        expected = set()
        for element in (8, 16, 32, 64):
            for high in (False, True):
                parameters = "d:bitvector(5),n:bitvector(5)"
                if element == 64:
                    index = "1" if high else "0"
                else:
                    bits = {8: 3, 16: 2, 32: 1}[element]
                    parameters += f",index:bitvector({bits})"
                    index = (f"(operator +)(unsigned(index), {64 // element})"
                             if high else "unsigned(index)")
                name = f"arm_DUP_ELEM_SCALAR_E{element}_{'HI' if high else 'LO'}"
                expected.add(
                    f"ENTRY\tvector-duplicate-element-scalar\t{name}\t{parameters}"
                    f"\tunit\tstate\t{source}(unsigned(d), {element}, 1, {element}, "
                    f"{128 if high else 64}, {index}, unsigned(n))")
        actual = {line for line in self.output.splitlines()
                  if line.startswith("ENTRY\tvector-duplicate-element-scalar\t")}
        self.assertEqual(actual, expected)

    def test_alias_closure_and_family_bundles(self):
        self.assertIn("AUDIT\t1404 roots\t9 alias cases\t69 family bundles",
                      self.output)

    def test_operand_domains_and_selectors_have_independent_examples(self):
        self.assertIn("SELECTION-AUDIT\t67 exact source calls and domains",
                      self.output)

    def test_cut_identities_and_effect_permissions(self):
        self.assertIn("CONTRACT-AUDIT\t22 Arm cuts\t13 RV32 cuts", self.output)

    def test_all_additional_memory_forms_have_exact_source_calls(self):
        self.assertIn("MEMORY-AUDIT\t146 exact source calls and domains", self.output)

    def test_memory_coverage_profiles_match_every_typed_binding(self):
        families = ("memory-single", *MEMORY_FAMILIES)
        actual = {}
        for line in self.output.splitlines():
            columns = line.split("\t")
            if columns[0] == "ENTRY" and columns[1] in families:
                field_types = []
                for parameter in columns[3].split(","):
                    _, typ = parameter.split(":", 1)
                    self.assertTrue(typ.startswith("bitvector(") and typ.endswith(")"))
                    field_types.append(typ[10:-1] + " word")
                actual[columns[2]] = (columns[1], field_types)
        expected = {}
        for family in families:
            specification = coverage.ARM_FAMILIES[family]
            self.assertTrue(specification["safe_domain_proofs"])
            self.assertTrue(specification["encoded_signatures_only"])
            for name in specification["instructions"]:
                for variant in coverage.arm_instruction_variants(family, name):
                    expected[variant["root"]] = (family, variant["argument_types"])
        self.assertEqual(len(expected), 246)
        self.assertEqual(actual, expected)

    def test_x86_catalogue_matches_every_required_name_and_operand_domain(self):
        actual = {}
        for line in self.output.splitlines():
            columns = line.split("\t")
            if columns[0] == "X86-ENTRY":
                family, name, parameters = columns[1:]
                self.assertNotIn(name, actual)
                types = []
                for typ in parameters.split(","):
                    self.assertTrue(typ.startswith("bitvector(") and typ.endswith(")"))
                    types.append(typ[10:-1] + " word")
                actual[name] = (family, types)
        self.assertEqual(actual, {
            row["root"]: (row["family"], row["argument_types"])
            for row in required_forms()
        })
        self.assertIn("X86-AUDIT\t205 roots\t9 acquisitions\tGPR helpers retained",
                      self.output)

    def test_rems_catalogue_is_exactly_the_exportable_rems_forms(self):
        actual = {}
        for line in self.output.splitlines():
            columns = line.split("\t")
            if columns[0] == "X86-REMS-ENTRY":
                family, name, parameters = columns[1:]
                self.assertNotIn(name, actual)
                types = []
                for typ in parameters.split(","):
                    self.assertTrue(typ.startswith("bitvector(") and typ.endswith(")"))
                    types.append(typ[10:-1] + " word")
                actual[name] = (family, types)
        expected = {
            "X86_REMS_" + row["root"].removeprefix("X86_"):
                (row["family"], row["argument_types"])
            for row in required_forms()
            if x86_forms.export_status(row, "rems") == "available"}
        self.assertEqual(len(expected), 119)
        self.assertEqual(actual, expected)
        self.assertIn("X86-REMS-AUDIT\tGPR accessors cut\tRIP logging off",
                      self.output)


if __name__ == "__main__":
    unittest.main()
