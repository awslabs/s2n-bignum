(* Run the real Sail compiler and HOL exporter on a test program from stdin.
   Supply the text through Sail's file handler without writing a model file;
   Sail parses, checks and rewrites it before invoking the production target. *)
open Libsail

(* Test the production printer directly. This does not bypass the real
   frontend in instruction tests. *)
let check_term_printer () =
  let open Sail_plugin_hol_light in
  let check term expected =
    if print_term term <> expected then failwith "HOL term printer changed bytes" in
  check (App ("f", [Atom "x"; Typed (Atom "y", Word 32)]))
    "(f x (y:32 word))";
  check (Lambda (Atom "x", Let (Atom "y", Tuple_term [Atom "x"; Atom "z"],
    Cond (Atom "p", Infix ("+", Atom "y", Atom "x"), App ("g", [])))))
    "(\\x. (let y = (x,z) in\n    (if p then (y + x) else (g ))))";
  check (String_literal "\000\255")
    "(CONS (ASCII F F F F F F F F) (CONS (ASCII T T T T T T T T) (NIL:char list)))";
  check (Tuple_term []) "()";
  let string_alias = alias_value (Atom "label")
    (Typed (String_literal "\000\255", String_type)) in
  check string_alias "label";
  if string_literal string_alias <> Some "\000\255" then
    failwith "string alias lost its exact literal bytes";
  let first = Atom "sail_hl_ctor_First"
  and second = Atom "sail_hl_ctor_Second" in
  let enum value = Typed (value, Enum "Choice") in
  let scoped = enum (Let (Atom "tag", first,
    Let (Atom "saved", Atom "tag", Let (Atom "tag", second, Atom "saved")))) in
  if literal_key scoped <> Some ("enum:Choice", "sail_hl_ctor_First") then
    failwith "enum fact lost its original lexical binding";
  List.iter (fun value ->
    if literal_key (enum value) <> None then
      failwith "unknown or control-bearing enum acquired a constructor fact")
    [Atom "unknown"; Cond (Atom "flag", first, second);
     Let (Atom "tag", Fault, first); Let (Atom "tag", Reject, first)];
  let deep = ref (Atom "x") in
  for _ = 1 to 10000 do deep := Let (Atom "x", Atom "y", !deep) done;
  let text = print_term !deep in
  if String.length text <> 190001 then
    failwith "deep printer lost a binding";
  let saved_enums = !used_enums in
  Fun.protect ~finally:(fun () -> used_enums := saved_enums) (fun () ->
    let first = "First", [Ast_util.mk_id "FirstOnly"]
    and second = "Second", [Ast_util.mk_id "SecondOnly"] in
    used_enums := [];
    for index = 1 to 1_000_000 do
      used_enums := (if index mod 2 = 0 then first else second) :: !used_enums
    done;
    if exported_enum_names () <> ["First"; "Second"] then
      failwith "large enum report lost or duplicated a type");
  let saved_primitives = !used_primitives in
  Fun.protect ~finally:(fun () -> used_primitives := saved_primitives) (fun () ->
    used_primitives := [];
    for index = 1 to 1_000_000 do
      used_primitives :=
        (if index mod 2 = 0 then "first" else "second") :: !used_primitives
    done;
    if exported_primitive_contracts ["root", "state-computation"] <>
       ["first"; "second"] then
      failwith "large primitive report changed a state computation";
    if exported_primitive_contracts ["root", "normal-retirement"] <>
       ["first"; "second"; "successful-root-jump-event"] then
      failwith "large primitive report lost the retirement contract");
  print_endline "HOL term printer checks passed"

let read_stdin () =
  let buffer = Buffer.create 4096 in
  (try while true do Buffer.add_channel buffer stdin 4096 done
   with End_of_file -> ());
  Buffer.contents buffer

let canonical_option (name, specification, description) =
  let name = String.map (function '_' -> '-' | character -> character) name in
  let name = if String.length name > 2 then "-" ^ name else name in
  name, specification, description

let named_integer argument =
  match String.split_on_char '=' argument with
  | [name; value] when name <> "" ->
      (try name, int_of_string value with Failure _ ->
        raise (Arg.Bad "fixed argument must be name=integer"))
  | _ -> raise (Arg.Bad "fixed argument must be name=integer")

let main () =
  Util.opt_colors := false;
  Reporting.opt_warnings := false;
  let output = ref None in
  let lift_source = ref "" and lift_requests = ref [] in
  let input_spans = ref "" and acquired_callee = ref "" in
  let save_smt = ref "" in
  let options =
    ("--unit-save-smt", Arg.Set_string save_smt,
     "check the program, write Sail's z3 answers to this file and stop") ::
    ("-o", Arg.String (fun name -> output := Some name), "output stem") ::
    ("--unit-lift", Arg.Tuple [
       Arg.Set_string lift_source;
       Arg.String (fun callee ->
         lift_requests := Entry.input_lift !lift_source callee :: !lift_requests)],
       "derive a supplied-input function for a frontend regression") ::
    ("--unit-fixed-argument", Arg.String (fun argument ->
       let name, value = named_integer argument in
       match !lift_requests with
       | lift :: remaining ->
           lift_requests := Entry.input_lift
             ~fixed_arguments:((name, value) :: lift.Entry.fixed_arguments)
             ~expected_inputs:lift.Entry.expected_inputs
             ?through:lift.Entry.through ?acquired:lift.Entry.acquired
             ~evaluate_arguments:lift.Entry.evaluate_arguments
             lift.Entry.source_function lift.Entry.input_function :: remaining
       | [] -> raise (Arg.Bad "fixed argument requires a preceding --unit-lift")),
       "fix a numeric parameter of the preceding supplied-input request") ::
    ("--unit-input-count", Arg.Int (fun count ->
       match !lift_requests with
       | lift :: remaining ->
           lift_requests := {lift with Entry.expected_inputs = count} :: remaining
       | [] -> raise (Arg.Bad "input count requires a preceding --unit-lift")),
       "set the expected direct-call count of the preceding input request") ::
    ("--unit-evaluate-arguments", Arg.Unit (fun () ->
       match !lift_requests with
       | lift :: remaining ->
           lift_requests := {lift with Entry.evaluate_arguments = true} :: remaining
       | [] -> raise (Arg.Bad "argument evaluation requires a preceding --unit-lift")),
       "evaluate the replaced input call's arguments before supplying it") ::
    ("--unit-through", Arg.String (fun child ->
       match !lift_requests with
       | lift :: remaining ->
           lift_requests := {lift with Entry.through = Some child} :: remaining
       | [] -> raise (Arg.Bad "helper path requires a preceding --unit-lift")),
       "retain one helper call and forward the supplied inputs through it") ::
    ("--unit-acquired", Arg.Tuple [
       Arg.Set_string acquired_callee;
       Arg.String (fun argument ->
         let fixed_binding = named_integer argument in
         match !lift_requests with
         | lift :: remaining ->
             lift_requests := {lift with Entry.acquired = Some {
               callee = !acquired_callee; fixed_binding}} :: remaining
         | [] -> raise (Arg.Bad "acquired selection requires a preceding --unit-lift"))],
       "fix one scalar result field of an original acquired-input let") ::
    ("--unit-input-spans", Arg.Symbol (["missing"; "duplicate"],
       fun mutation -> input_spans := mutation),
       "mutate checked input-call locations for refusal regressions") ::
    List.map (fun option -> canonical_option (Flag.to_arg option))
      (Target.extract_options ()) in
  Arg.parse options
    (fun name -> raise (Arg.Bad ("unexpected file argument: " ^ name)))
    "unit_frontend [HOL Light target options] < test program";
  let target = match Target.get ~name:"hol_light" with
    | Some target -> target
    | None -> failwith "the production HOL Light target is not linked" in
  let default_sail_dir = Sys.getenv "SAIL_DIR" in
  let path, _ = Sail_file.add_virtual_file ~contents:(read_stdin ()) "unit-input.sail" in
  Target.run_pre_parse_hook target ();
  (* Every test checks the prelude again. test_backend.py records the z3
     answers of one prelude-only check; through Sail's memo loader each
     test reuses them and asks z3 only its own new questions. *)
  Option.iter Constraint.load_digests (Sys.getenv_opt "SAIL_HOL_UNIT_SMT_CACHE");
  let symbols, ctx, ast, env, effect_info =
    Frontend.load_paths ~target ~default_sail_dir options Type_check.initial_env
      [Corelib_sail.path; path] in
  if !save_smt <> "" then (Constraint.save_digests !save_smt; exit 0);
  let configuration = `Assoc [] in
  let ast, instantiation =
    Frontend.instantiate_abstract_types (Some target) configuration
      Ast_compare.Bindings.empty ast in
  let _, ast = Config.rewrite_ast target env instantiation configuration ast in
  let ast, env =
    if Target.skip_initial_rewrite target then ast, env
    else Frontend.initial_rewrite effect_info env ast in
  let effect_info = Effects.infer_side_effects (Target.asserts_termination target) ast in
  Target.run_pre_rewrites_hook target ast effect_info env;
  let ctx, ast, effect_info, env =
    Rewrites.rewrite ctx effect_info env (Target.rewrites target) ast in
  let state : Interactive.State.istate =
    {symbols; ctx; ast; effect_info; env; options; default_sail_dir; config = None} in
  (* Test-only location mutations. Calculations, checked types and effects
     remain unchanged; production entry code must refuse ambiguous origin. *)
  let state = if !input_spans = "" then state else
    let open Ast in
    let first = ref None in
    let mutate (aux, (loc, annotation)) =
      let loc = match aux with
        | E_app (callee, _) when List.exists (fun lift ->
            let name = Ast_util.string_of_id callee in
            lift.Entry.input_function = name ||
            Option.fold ~none:false ~some:(fun selected ->
              selected.Entry.callee = name) lift.Entry.acquired)
            !lift_requests ->
            if !input_spans = "missing" then Parse_ast.Unknown else
            (match !first with
             | Some first -> first
             | None -> first := Some loc; loc)
        | _ -> loc in
      E_aux (aux, (loc, annotation)) in
    let ast = Rewriter.rewrite_ast_base
      {Rewriter.rewriters_base with
       rewrite_exp = (fun _ exp ->
         Rewriter.fold_exp {Rewriter.id_exp_alg with e_aux = mutate} exp)}
      state.ast in
    {state with ast} in
  let state = if !lift_requests = [] then state else
    Entry.lift_inputs ~record:Sail_plugin_hol_light.record_input_boundary
      state !lift_requests in
  Target.action target !output state

let () =
  try
    if List.tl (Array.to_list Sys.argv) = ["--check-term-printer"]
    then check_term_printer () else main ()
  with
  | Reporting.Fatal_error error ->
      Reporting.print_error error;
      exit 1
  | Type_error.Type_error (location, error) ->
      let message, hint = Type_error.string_of_type_error error in
      Reporting.print_type_error ?hint location message;
      exit 1
