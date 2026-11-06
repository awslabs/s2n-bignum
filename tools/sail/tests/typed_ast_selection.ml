(* Check that the exporter's dependency selection keeps exactly what a root
   needs. Callgraph selection from a root must keep the functions, type
   abbreviations and let bindings it uses and drop unrelated ones; a cut
   helper keeps its signature but loses its body. The program is a small
   syntax tree built here, not an architecture model. *)
open Libsail
open Ast
open Ast_defs
open Ast_util
open Ast_compare

module Exporter = Sail_plugin_hol_light

let error message = raise (Reporting.err_general Parse_ast.Unknown message)

let selection_sanity () =
  let alias name = mk_def (DEF_type (TD_aux (
    TD_abbrev (mk_id name, [], mk_typ_arg (A_typ bool_typ)),
    (Parse_ast.Unknown, empty_uannot)))) () in
  let binding name = mk_def (DEF_let (
    mk_pat (P_id (mk_id name)), mk_lit_exp L_false)) () in
  let function_def name typ body = [
    mk_val_spec (VS_val_spec (
      mk_typschm [] (function_typ [typ] typ), mk_id name, None));
    mk_fundef [mk_funcl (mk_id name)
      (mk_pat (P_typ (typ, mk_pat (P_id (mk_id "argument"))))) body]] in
  let alias_type = mk_id_typ (mk_id "MUTATION_ALIAS") in
  let call_helper () = mk_exp (E_app (
    mk_id "MUTATION_HELPER", [mk_exp (E_id (mk_id "argument"))])) in
  let definitions =
    [alias "MUTATION_ALIAS"; alias "MUTATION_UNUSED_ALIAS";
     binding "MUTATION_USED_LET"; binding "MUTATION_UNUSED_LET"] @
    function_def "MUTATION_HELPER" alias_type
      (mk_exp (E_id (mk_id "argument"))) @
    function_def "MUTATION_UNUSED_FUNCTION" bool_typ (mk_lit_exp L_false) @
    function_def "MUTATION_ROOT" alias_type (mk_exp (E_if (
      mk_exp (E_id (mk_id "MUTATION_USED_LET")), call_helper (),
      call_helper ()))) in
  let definitions, _ =
    Type_check.check_defs Type_check.initial_env definitions in
  let original_ast = {defs = definitions; comments = []} in
  let ast = Callgraph.filter_ast_ids
    (IdSet.singleton (mk_id "MUTATION_ROOT")) IdSet.empty
    original_ast in
  let retained = List.fold_left (fun nodes definition ->
    Callgraph.NodeSet.union nodes (Callgraph.nodes_of_def definition))
    Callgraph.NodeSet.empty ast.defs in
  List.iter (fun node ->
    if not (Callgraph.NodeSet.mem node retained) then
      error ("selection dropped dependency " ^
        string_of_id (Callgraph.node_id node))) [
    Callgraph.Function (mk_id "MUTATION_ROOT");
    Callgraph.Function (mk_id "MUTATION_HELPER");
    Callgraph.Type (mk_id "MUTATION_ALIAS");
    Callgraph.Letbind (mk_id "MUTATION_USED_LET")];
  List.iter (fun node ->
    if Callgraph.NodeSet.mem node retained then
      error ("selection retained unrelated definition " ^
        string_of_id (Callgraph.node_id node))) [
    Callgraph.Function (mk_id "MUTATION_UNUSED_FUNCTION");
    Callgraph.Type (mk_id "MUTATION_UNUSED_ALIAS");
    Callgraph.Letbind (mk_id "MUTATION_UNUSED_LET")];
  let cut = Callgraph.filter_ast_ids
    (IdSet.singleton (mk_id "MUTATION_ROOT"))
    (IdSet.singleton (mk_id "MUTATION_HELPER")) original_ast in
  if List.exists (fun definition ->
      Exporter.root_of_def definition = Some "MUTATION_HELPER") cut.defs then
    error "selection retained a cut helper body";
  if not (List.exists (function
      | DEF_aux (DEF_val (VS_aux (VS_val_spec (_, name, _), _)), _) ->
          string_of_id name = "MUTATION_HELPER"
      | _ -> false) cut.defs) then
    error "selection discarded the original cut helper signature";
  print_endline "TYPED_AST_SELECTION_SANITY_PASS"

let sanity () =
  selection_sanity ();
  exit 0

let _ = Target.register ~name:"hol_light_selection"
  ~supports_abstract_types:true ~supports_runtime_config:true
  ~options:[
    (Flag.create ~prefix:["hol_light_selection"] "sanity",
     Arg.Unit sanity, "check dependency selection on a small AST")
  ] ~rewrites:[] (fun _ _ -> error "use --hol-light-selection-sanity")
