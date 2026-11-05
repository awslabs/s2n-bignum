(* Describe instruction bindings and source-function export requests.

   A comparison needs a named HOL function with variable register operands
   and fixed instruction choices, such as width and flag updates. The Arm,
   RV32 and x86 tables describe each such instruction binding in an Entry.t
   record, called an "entry" here. This module builds and checks the bindings.

   The translator separately requests shared upstream function definitions.
   Those requests name the Sail function and necessary numeric type arguments;
   their operands come from the checked source, not another handwritten list.

   For example, the ADC64 binding keeps d, m and n as register parameters
   while selecting 64-bit addition without flag updates. Its body is a call
   to the upstream instruction, not a replacement arithmetic formula.

   This code runs inside Sail's compiler, using libsail's syntax constructors
   and typechecker. Each binding becomes a checked Sail function in memory;
   the translator subsequently follows its upstream instruction and helpers.
   No HOL proof runs here. *)
open Libsail
open Ast
open Ast_defs
open Ast_util
open Ast_compare

(* Instructions export relations between initial and final machine states.
   Pure calculation helpers still return values. Some RV32 bindings compare
   successful retirement, including the completion tag and jump event; this
   is a semantic requirement, not a different output representation. *)
type untyped_exp = uannot exp

(* A source-function request fixes numeric type arguments, not HOL operands.
   The common translator obtains its parameter names, types and order from
   Sail's checked function pattern. An empty type_arguments list asks it to
   retain width polymorphism where the body supports that representation.

   The instruction bindings below are separate: they retain the established
   HOL instruction names and operand conventions, for example ADC's two
   false Boolean selectors. They do not describe the shared function's
   parameters or supply its calculation. *)
type function_request = {
  source : string;
  type_arguments : (string * int) list;
}

(* Architecture assumptions are separate from instruction/type choices.
   Feature fixes an availability query for this processor. Initial_bit fixes
   a one-bit source register field at entry; the translator must reject writes
   that could invalidate it. Names are resolved against Sail's checked
   declarations. Initial_bit's Boolean argument denotes the field's 0b0/0b1
   value, not a Boolean register.
   Initial_enum fixes a declared enum register to one of its constructors;
   Initial_bool fixes a declared Boolean register, such as an x86 feature
   availability bit. Writes to either register reject for the same reason. *)
type assumption =
  | Feature of string * bool
  | Initial_bit of string * string * bool
  | Initial_enum of string * string
  | Initial_bool of string * bool

let request ?(type_arguments = []) source = {source; type_arguments}

(* An instruction body may acquire an input that is outside the core
   instruction claim, for example fetching its operand byte. A lift derives
   a function from that checked body by replacing a requested number of
   direct calls with separate parameters. One call is the default.
   Optional through names one retained helper: derive the helper first,
   then forward the supplied parameters through its single original call.
   Each parameter's type comes from its call, not this request.
   The excluded call's effects are an explicit, trusted input boundary;
   every other statement remains in the original body and is rechecked.
   Optional fixed_arguments select a dispatch path before input discovery.
   Each value is checked against its original numeric or fixed-width bit
   type and removed from the derived signature. Bit values are not truncated.
   These choices never supply the instruction's calculations. *)
(* Select one scalar field of an acquired result. The original immutable
   let pattern names that field; other tuple fields become typed inputs.
   For example, fixing opcode in let (pfx,opcode) = scan_prefixes() keeps
   pfx variable without translating or copying the prefix-scanning loop. *)
type acquired_selection = {
  callee : string;
  fixed_binding : string * int;
}

(* By default every argument of a replaced input call must be a literal,
   so removing the call removes no other evaluation. With
   evaluate_arguments the replacement instead evaluates the original
   arguments in order and discards their values before supplying the
   input; only the call itself is excluded. REMS fetches an immediate as
     rme_size(proc_mode, select_address_size(proc_mode, Some(prefixes)),
              1, sail_sign_extend(temp_rip, 64), ...)
   whose address arguments are computed from the instruction state. *)
type input_lift = {
  source_function : string;
  input_function : string;
  fixed_arguments : (string * int) list;
  expected_inputs : int;
  through : string option;
  acquired : acquired_selection option;
  evaluate_arguments : bool;
}

(* A retained caller edge is not an excluded operation. Its arguments and
   the helper body still execute; only the leaf input acquisition is removed. *)
type input_caller = {
  caller_location : Parse_ast.l;
  caller_call : untyped_exp;
  caller_specialized_call : untyped_exp option;
  derived_child : string;
}

(* Evidence records the original checked call and, when different, the
   call after numeric selection. Both identify the same source occurrence.
   Consumers can distinguish this boundary from a translated operation. *)
type input_slot = {
  input_type : typ;
  input_index : int;                 (* zero-based derived-function input *)
  parameter : string;                (* fresh Sail parameter *)
  result_path : int list;             (* zero-based tuple fields, [] scalar *)
  forwarded_index : int option;      (* child slot, when forwarded *)
}

type fixed_acquired_binding = {
  binding : string;
  value : untyped_exp;
  binding_type : typ;
  binding_path : int list;
}

type input_boundary = {
  lift : input_lift;
  location : Parse_ast.l;
  call : untyped_exp;
  specialized_call : untyped_exp option;
  input_type : typ;                  (* complete acquisition result *)
  slots : input_slot list;            (* empty when its result is fixed *)
  fixed_binding : fixed_acquired_binding option;
  replacement : untyped_exp option;
  caller : input_caller option;
}

let input_lift ?(fixed_arguments = []) ?(expected_inputs = 1) ?through
    ?acquired ?(evaluate_arguments = false)
    source_function input_function =
  {source_function; input_function;
   expected_inputs; through; acquired; evaluate_arguments;
   fixed_arguments = List.sort (fun (left, _) (right, _) ->
     String.compare left right) fixed_arguments}

let selection_text lift =
  String.concat "," (List.map (fun (name, value) ->
    name ^ "=" ^ string_of_int value) lift.fixed_arguments)

let lifted_name lift =
  "HOL_INPUT_" ^ lift.source_function ^ "__" ^ lift.input_function ^
  String.concat "" (List.map (fun (name, value) ->
    "__" ^ name ^ "_" ^
    String.map (function '-' -> 'm' | character -> character)
      (string_of_int value)) lift.fixed_arguments) ^
  (if lift.expected_inputs = 1 then ""
   else "__inputs_" ^ string_of_int lift.expected_inputs) ^
  (match lift.through with None -> "" | Some child -> "__through_" ^ child) ^
  (match lift.acquired with
   | None -> ""
   | Some selection ->
       let binding, value = selection.fixed_binding in
       "__acquired_" ^ selection.callee ^ "__" ^ binding ^ "_" ^
       String.map (function '-' -> 'm' | character -> character)
         (string_of_int value)) ^
  (if lift.evaluate_arguments then "__evaluated" else "")

type t = {
  family : string;                    (* command-line group and output file *)
  name : string;                      (* name of the constructed Sail function *)
  parameters : (string * typ) list;    (* symbolic operands, in HOL argument order *)
  body : untyped_exp;                  (* Sail nodes, checked by instantiate *)
  result : typ;                       (* source result, unit by default *)
  retirement : bool;                  (* require successful RV32 completion *)
  input_lifts : input_lift list;       (* explicit source-input boundaries *)
}

(* These build syntax, not values: int 64 is a Sail literal node and
   call "UInt" [id "m"] is a Sail call whose declaration is checked later. *)
let word n = bitvector_typ (nconstant (Big_int.of_int n))
let id name = mk_exp (E_id (mk_id name))
let int n = mk_lit_exp (L_num (Big_int.of_int n))
let bool b = mk_lit_exp (if b then L_true else L_false)
let call name arguments = mk_exp (E_app (mk_id name, arguments))
(* Binary literals list their digits most significant first. *)
let binary_digits width value =
  non_empty_singleton (List.init width (fun index ->
    if value land (1 lsl (width - index - 1)) = 0 then Bin_0 else Bin_1))
let bit_literal width value = mk_lit_exp (L_bin (binary_digits width value))
let slice value high low = mk_exp (vector_subrange value (int high) (int low))
let call_lifted_inputs ?(acquired_inputs = []) lift arguments inputs =
  if List.length inputs <> lift.expected_inputs then
    invalid_arg "HOL input lift: supplied input count differs from request";
  call (lifted_name lift) (arguments @ acquired_inputs @ inputs)
let call_lifted ?acquired_inputs lift arguments input =
  call_lifted_inputs ?acquired_inputs lift arguments [input]
let unsigned name = call "unsigned" [id name]
let tuple values = mk_exp (E_tuple values)
let unit = mk_lit_exp L_unit

let make ?(retirement = false) ?(result = unit_typ) ?(input_lifts = [])
    ~family name parameters body =
  {family; name; parameters; body; result; retirement; input_lifts}

(* Construct an instruction binding's type declaration and body. Every
   parameter has an explicit Sail type; a parameterless binding takes unit. *)
let definitions entry =
  let name = mk_id entry.name in
  let types = List.map snd entry.parameters in
  let types = if types = [] then [unit_typ] else types in
  let signature = mk_typschm [] (function_typ types entry.result) in
  let pattern = match entry.parameters with
    | [] -> mk_pat (P_lit (mk_lit L_unit))
    | [name, typ] -> mk_pat (P_typ (typ, mk_pat (P_id (mk_id name))))
    | parameters ->
        mk_pat (P_tuple (List.map (fun (name, typ) ->
          mk_pat (P_typ (typ, mk_pat (P_id (mk_id name))))) parameters)) in
  [mk_val_spec (VS_val_spec (signature, name, None));
   mk_fundef [mk_funcl name pattern entry.body]]

let dependencies entry =
  let calls = ref [] in
  let e_app (id, arguments) =
    calls := string_of_id id :: !calls;
    E_app (id, arguments) in
  ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with e_app} entry.body);
  List.sort_uniq String.compare !calls

(* Aliases may call another binding, for example CINC calls CSINC with the
   condition inverted. Discover that dependency from the constructed nodes
   so selecting one alias does not require a handwritten helper list.
   This finds only calls between bindings in the catalogue. prepare_upstream
   subsequently finds the upstream instructions and helpers they call. *)
let closure catalog requested =
  let rec visit seen = function
    | [] -> seen
    | name :: pending when List.mem name seen -> visit seen pending
    | name :: pending ->
        (match List.find_opt (fun entry -> entry.name = name) catalog with
         | None -> visit seen pending
         | Some entry -> visit (name :: seen) (dependencies entry @ pending)) in
  let names = visit [] (List.map (fun entry -> entry.name) requested) in
  List.filter (fun entry -> List.mem entry.name names) catalog

let lifts entries =
  List.sort_uniq compare (List.concat_map (fun entry -> entry.input_lifts) entries)

(* A selected byte often becomes a local integer before a source dispatch:
     let op = unsigned(opcode); match op { ... }
   Evaluate copies of small, closed scalar expressions to discover those
   choices. Never evaluate or replace the retained instruction body.

   The interpreter has no source bodies, global initializers or registers.
   Check declarations as well as primitive names; undefined values, source
   functions, mappings and impure externals cannot acquire constant facts.
   Facts come only from this traversal's immutable lexical bindings. *)
let closed_scalar_value (state : Interactive.State.istate) =
  let primitives = ["eq_int"; "lt"; "lteq"; "gt"; "gteq"; "eq_bool";
                    "and_bool"; "or_bool"; "not"; "uint"; "tmod_int";
                    "rem_round_zero"] in
  let primops = Constant_fold.StringMap.filter
    (fun name _ -> List.mem name primitives) Constant_fold.safe_primops in
  let defined = Type_check.Env.get_defined_val_specs state.env in
  let allowed_call environment id =
        not (IdSet.mem id defined) &&
        Type_check.Env.is_pure_extern id environment &&
        Effects.function_is_pure id state.effect_info &&
        Type_check.Env.is_extern id environment "interpreter" &&
        List.mem (Type_check.Env.get_extern id environment "interpreter") primitives in
  let rec close facts (E_aux (aux, annotation) as exp) =
    let rebuild aux = Some (E_aux (aux, annotation)) in
    match aux with
    | E_lit (L_aux ((L_num _ | L_true | L_false), _)) -> Some exp
    | E_lit (L_aux ((L_bin _ | L_hex _), _)) ->
        (match Type_check.destruct_bitvector (Type_check.env_of exp)
            (Type_check.typ_of exp) with
         | Some width ->
             (match get_nexp_constant (nexp_simp width) with
              | Some width when Big_int.compare width (Big_int.of_int 1) >= 0 &&
                  Big_int.compare width (Big_int.of_int 2048) <= 0 -> Some exp
              | _ -> None)
         | None -> None)
    | E_id id ->
        (match Type_check.Env.lookup_id id (Type_check.env_of exp) with
         | Local (Immutable, _) -> Bindings.find_opt id facts
         | _ -> None)
    | E_typ (typ, value) ->
        Option.bind (close facts value) (fun value -> rebuild (E_typ (typ, value)))
    | E_app (id, arguments) when allowed_call (Type_check.env_of exp) id ->
        Option.bind (Util.map_all (close facts) arguments) (fun arguments ->
          rebuild (E_app (id, arguments)))
    | _ -> None in
  fun facts exp ->
    if !Interactive.opt_interactive then None else
    try
      Option.bind (close facts exp) (fun candidate ->
        (* Resolve nested primitive results before typing their callers.
           For eq_int(unsigned(byte),56), unsigned first produces a checked
           integer literal. The equality's Boolean refinement then refers
           to that value, not an unresolved existential integer witness.
           Check every value against its inferred source result type: an
           external declaration cannot supply an impossible constant fact. *)
        let rec evaluate (E_aux (aux, annotation) as candidate) =
          let checked_arguments = match aux with
            | E_app (id,arguments) ->
                Option.map (fun arguments -> E_aux (E_app (id,arguments), annotation))
                  (Util.map_all (fun argument ->
                    Option.map snd (evaluate argument)) arguments)
            | E_typ (typ,argument) ->
                Option.map (fun (_,argument) ->
                  E_aux (E_typ (typ,argument), annotation)) (evaluate argument)
            | E_lit _ -> Some candidate
            | _ -> None in
          Option.bind checked_arguments (fun candidate ->
            let environment = Type_check.Env.open_all_modules
              (Type_check.env_of candidate) in
            let checked = Type_check.infer_exp environment
              (Type_check.strip_exp candidate) in
            (* Inference can resolve an overload; validate its calls again. *)
            Option.bind (close Bindings.empty checked) (fun _ ->
              let interpreter = Interpreter.initial_state ~registers:false
                ~fold_target:"hol_light" empty_ast environment primops in
              let value = Constant_fold.run (Interpreter.Step
                (lazy "", interpreter, Interpreter.Monad.pure checked, [])) in
              match value with
              | V_int _ | V_bool _ | V_bitvector _ ->
                  let literal = Type_check.check_exp environment
                    (Constant_fold.exp_of_value value) (Type_check.typ_of checked) in
                  Some (value,literal)
              | _ -> None)) in
        evaluate candidate)
    with
    | Type_error.Type_error _ | Failure _ | Assert_failure _ | Not_found
    | Division_by_zero -> None

(* Follow immutable locals only within their lexical scope. Keep each
   original RHS and evaluate a selected match/if condition once in the
   emitted body. Ordered patterns and guards still determine selection;
   an unknown matched guard prevents choosing a later case.
   Bounds use the outer scope of a for-loop. Mutable declarations and
   exception/case patterns cannot inherit facts from a shadowed name. *)
let prune_closed_selectors state body =
  let evaluate = closed_scalar_value state in
  let without_pattern facts pattern =
    Bindings.filter (fun id _ -> not (IdSet.mem id (pat_ids pattern))) facts in
  let rec binder = function
    | P_aux (P_id id, _) -> Some id
    | P_aux ((P_typ (_, pattern) | P_var (pattern, _)), _) -> binder pattern
    | _ -> None in
  let bind facts pattern value =
    let facts = without_pattern facts pattern in
    match binder pattern, value with
    | Some id, Some (_, literal) -> Bindings.add id literal facts
    | _ -> facts in
  (* A supplied tuple can mix unknown inputs with selected literals.
     Record only independently closed leaves, never a fact for the tuple
     or for an unknown sibling. Reset every binder before entering scope. *)
  let bind_rhs facts pattern rhs =
    let outer = facts in
    let rec leaves facts pattern rhs =
      match pattern, rhs with
      | P_aux ((P_typ (_, pattern) | P_var (pattern, _)), _), _ ->
          leaves facts pattern rhs
      | _, E_aux (E_typ (_, rhs), _) -> leaves facts pattern rhs
      | P_aux (P_tuple patterns, _), E_aux (E_tuple values, _)
          when List.length patterns = List.length values ->
          List.fold_left2 leaves facts patterns values
      | _ ->
          (match binder pattern, evaluate outer rhs with
           | Some id, Some (_, literal) -> Bindings.add id literal facts
           | _ -> facts) in
    leaves (without_pattern facts pattern) pattern rhs in
  let preserve (E_aux (_, annotation) as value) body =
    let E_aux (_, result_annotation) = body in
    E_aux (E_let (P_aux (P_wild, annotation), value, body), result_annotation) in
  let rec matches value = function
    | P_aux (P_lit (L_aux (L_num expected, _)), _) ->
        (match value with V_int value -> Some (Big_int.equal value expected) | _ -> None)
    | P_aux (P_wild, _) | P_aux (P_id _, _) -> Some true
    | P_aux (P_typ (_, pattern), _) -> matches value pattern
    | _ -> None in
  let rec rewrite facts (E_aux (aux, annotation) as exp) =
    let rewrap aux = E_aux (aux, annotation) in
    let case facts case =
      let pattern, guard, body, annotation = destruct_pexp case in
      let facts = without_pattern facts pattern in
      construct_pexp (pattern, Option.map (rewrite facts) guard,
        rewrite facts body, annotation) in
    match aux with
    | E_let (pattern, rhs, body) ->
        let rhs = rewrite facts rhs in
        rewrap (E_let (pattern, rhs, rewrite (bind_rhs facts pattern rhs) body))
    | E_internal_plet (pattern, rhs, body) ->
        rewrap (E_internal_plet (pattern, rewrite facts rhs,
          rewrite (without_pattern facts pattern) body))
    | E_if (condition, yes, no) ->
        let condition = rewrite facts condition in
        (match evaluate facts condition with
         | Some (V_bool value, _) ->
             preserve condition (rewrite facts (if value then yes else no))
         | _ -> rewrap (E_if (condition, rewrite facts yes, rewrite facts no)))
    | E_match (selector, cases) ->
        let selector = rewrite facts selector in
        (match evaluate facts selector with
         | Some (value, _) as known ->
             (match select facts selector known value cases with
              | Some selected -> selected
              | None -> rewrap (E_match (selector, List.map (case facts) cases)))
         | _ -> rewrap (E_match (selector, List.map (case facts) cases)))
    | E_try (body, cases) ->
        rewrap (E_try (rewrite facts body, List.map (case facts) cases))
    | E_for (id, first, last, step, order, body) ->
        rewrap (E_for (id, rewrite facts first, rewrite facts last,
          rewrite facts step, order, rewrite (Bindings.remove id facts) body))
    | E_var (lexp, rhs, body) ->
        rewrap (E_var (lexp, rewrite facts rhs, rewrite Bindings.empty body))
    | _ ->
        Rewriter.rewrite_exp {Rewriter.rewriters_base with
          rewrite_exp = (fun _ -> rewrite facts)} exp
  and select facts selector known value = function
    | [] -> None
    | case :: remaining ->
        let pattern, guard, body, _ = destruct_pexp case in
        match matches value pattern with
        | Some false -> select facts selector known value remaining
        | Some true ->
            let inside = bind facts pattern known in
            let chosen () =
              let body = rewrite inside body in
              let body = match guard with None -> body | Some guard -> preserve guard body in
              match binder pattern with
              | Some _ ->
                  let E_aux (_, annotation) = body in
                  Some (E_aux (E_let (pattern, selector, body), annotation))
              | None -> Some (preserve selector body) in
            (match guard with
             | None -> chosen ()
             | Some guard ->
                 (match evaluate inside guard with
                  | Some (V_bool true, _) -> chosen ()
                  | Some (V_bool false, _) -> select facts selector known value remaining
                  | _ -> None))
        | _ -> None in
  rewrite Bindings.empty body

(* Use the checked source type for both formal and acquired selections.
   Width and range checks precede construction; a selected byte cannot wrap
   or silently become a value outside a dependent numeric constraint. *)
let checked_selection_literal env loc typ value =
  let fail message =
    raise (Reporting.err_general loc ("HOL input lift: " ^ message)) in
  let numeric = match Type_check.Env.expand_synonyms env typ with
    | Typ_aux (Typ_id id, _) when string_of_id id = "int" -> true
    | _ -> Option.is_some (Type_check.destruct_range env typ) in
  if not (KidSet.is_empty (tyvars_of_typ typ)) then
    fail "fixed argument requires a closed numeric type or bitvector width";
  let literal = if numeric then int value else
    match Type_check.destruct_bitvector env typ with
    | Some width ->
        let width = match get_nexp_constant (nexp_simp width) with
          | Some width when Big_int.compare width (Big_int.of_int 1) >= 0 &&
              Big_int.compare width (Big_int.of_int 2048) <= 0 ->
              Big_int.to_int width
          | _ -> fail "fixed bit argument requires width 1 through 2048" in
        let integer = Big_int.of_int value in
        if value < 0 ||
            Big_int.compare integer (Big_int.pow_int_positive 2 width) >= 0 then
          fail "fixed bit argument is outside its source width";
        (* Sail's conversion is MSB-first and truncates to width. *)
        let digits = List.map (function
          | Ast.Bit.B0 -> Bin_0 | Ast.Bit.B1 -> Bin_1)
          (Sail_lib.to_bits' width integer) in
        mk_lit_exp (L_bin (non_empty_singleton digits))
    | None ->
        fail "fixed argument requires a closed numeric type or bitvector width" in
  try Type_check.check_exp env literal typ with
  | Type_error.Type_error _ ->
      fail "fixed argument does not satisfy its source type"

(* Sail's substitution handles immutable let/case shadowing. Reject the
   mutable/reference/loop-binder cases it does not preserve for a removed
   formal parameter. After specialization the entire derived function is
   rechecked, including remaining signature constraints and effect order. *)
let specialize_arguments state pat arguments types body fixed =
  let fail loc message =
    raise (Reporting.err_general loc ("HOL input lift: " ^ message)) in
  if fixed = [] then arguments, types, body else begin
    let names = List.map fst fixed in
    if List.length names <> List.length (List.sort_uniq String.compare names) then
      fail (pat_loc pat) "duplicate fixed argument";
    let rec parameter = function
      | P_aux ((P_typ (_, pattern) | P_var (pattern, _)), _) -> parameter pattern
      | P_aux (P_id id, _) -> Some id
      | _ -> None in
    let paired = List.combine arguments types in
    let selected = List.map (fun (name, value) ->
      let id, typ = match List.find_opt (fun (pattern, _) ->
        Option.map string_of_id (parameter pattern) = Some name) paired with
      | Some (pattern, typ) -> Option.get (parameter pattern), typ
      | None -> fail (pat_loc pat) ("unknown fixed argument: " ^ name) in
      let env = Type_check.env_of_pat pat in
      let checked = checked_selection_literal env (pat_loc pat) typ value in
      let rec declares = function
        | LE_aux ((LE_id binder | LE_typ (_, binder)), _) ->
            Id.compare id binder = 0
        | LE_aux (LE_tuple declarations, _) -> List.exists declares declarations
        | _ -> false in
      ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with
        e_ref = (fun referenced ->
          if Id.compare id referenced = 0 then
            fail (id_loc referenced) "fixed argument is referenced";
          E_ref referenced);
        e_var = (fun (lexp, value, body) ->
          if declares lexp then
            fail (lexp_loc lexp) "fixed argument has a mutable shadow";
          E_var (lexp, value, body));
        e_for = (fun (binder, first, last, step, order, body) ->
          if Id.compare id binder = 0 then
            fail (id_loc binder) "fixed argument has a loop shadow";
          E_for (binder, first, last, step, order, body))
      } body);
      id, checked
    ) fixed in
    let body = List.fold_left (fun body (id, value) ->
      subst id value body) body selected |> prune_closed_selectors state in
    let remaining = List.filter (fun (pattern, _) ->
      match parameter pattern with
      | Some id -> not (List.mem (string_of_id id) names)
      | None -> true) paired in
    let arguments, types = List.split remaining in
    arguments, types, body
  end

(* Read the checked clause and original signature used by both direct
   input lifting and retained-helper redirection. *)
let checked_source (state : Interactive.State.istate) source fixed =
  let fail loc message =
    raise (Reporting.err_general loc ("HOL input lift: " ^ message)) in
  let source_id = mk_id source in
  let definition, pat, body =
    match List.find_opt (function
      | DEF_aux (DEF_fundef (FD_aux (FD_function (_, _, clauses), _)), _) ->
          List.exists (function
            | FCL_aux (FCL_funcl (id, _), _) -> Id.compare id source_id = 0) clauses
      | _ -> false) state.ast.defs with
    | Some (DEF_aux (DEF_fundef (FD_aux (FD_function (_, _, [
        FCL_aux (FCL_funcl (_, Pat_aux (Pat_exp (pat, body), _)), _)
      ]), _)), _) as definition) -> definition, pat, body
    | _ -> fail Parse_ast.Unknown "requires one unguarded source function clause" in
  let loc = def_loc definition in
  let quantifiers, signature =
    if fixed = [] then Type_check.Env.get_val_spec_orig source_id state.env
    else
      (* The environment represents range parameters by quantified atoms.
         The original checked declaration retains their closed source range. *)
      match List.find_map (function
        | DEF_aux (DEF_val (VS_aux (VS_val_spec (
            TypSchm_aux (TypSchm_ts (quantifiers, signature), _), id, _), _)), _)
            when Id.compare id source_id = 0 -> Some (quantifiers, signature)
        | _ -> None) state.ast.defs with
      | Some specification -> specification
      | None -> fail loc "source has no checked declaration" in
  let argument_types, result = match signature with
    | Typ_aux (Typ_fn (arguments, result), _) -> arguments, result
    | _ -> fail loc "source declaration is not a function" in
  definition, pat, body, quantifiers, argument_types, result

let argument_patterns pat types =
  let rec unwrap = function
    | P_aux (P_typ (_, pat), _) -> unwrap pat
    | pat -> pat in
  match types, unwrap (Type_check.strip_pat pat) with
  | [_], pat -> [pat]
  | types, P_aux (P_tuple pats, _) when List.length types = List.length pats -> pats
  | _ -> raise (Reporting.err_general (pat_loc pat)
      "HOL input lift: source pattern does not match its parameter list")

let real_source_span location =
  match Reporting.simp_loc location with
  | Some (first,last) when first.pos_fname = last.pos_fname &&
      first.pos_lnum > 0 && last.pos_lnum >= first.pos_lnum &&
      first.pos_cnum >= 0 && first.pos_cnum < last.pos_cnum -> Some (first,last)
  | _ -> None

let original_source_call body callee matched =
  let fail message =
    raise (Reporting.err_general (exp_loc matched) ("HOL input lift: " ^ message)) in
  let span = match real_source_span (exp_loc matched) with
    | Some span -> span
    | None -> fail "selected input has no original source span" in
  let originals = ref [] in
  ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with
    e_aux = (fun (aux, annotation) ->
      let exp = E_aux (aux, annotation) in
      (match aux with
       | E_app (id, _) when string_of_id id = callee &&
           Reporting.simp_loc (exp_loc exp) = Some span ->
           originals := exp :: !originals
       | _ -> ());
      exp)} body);
  match !originals with
  | [exp] -> Type_check.strip_exp exp
  | _ -> fail "selected input has no unique original source call"

let literal_input_argument =
  let rec literal = function
    | E_aux (E_lit _, _) -> true
    | E_aux (E_typ (_, value), _) -> literal value
    | _ -> false in
  literal

type prepared_lift_source = {
  definition : Type_check.typed_def;
  pattern : Type_check.tannot pat;
  original_body : Type_check.tannot exp;
  body : Type_check.tannot exp;
  quantifiers : typquant;
  arguments : uannot pat list;
  argument_types : typ list;
  result : typ;
  identifiers : IdSet.t ref;
  acquired_parameters : (id * typ) list;
  acquired_boundaries : input_boundary list;
}

(* Prepare both direct and retained-helper clones in the same order.
   First select closed formal arguments. Then replace one immutable input
   acquisition, preserving its original let and tuple shape, and use only
   its fixed leaf to select further source control flow.
   The requested binder identifies that one acquisition. Other calls to
   the same callee remain unless their source branch is then proved dead.

   Every supplied tuple leaf has the type of the checked acquisition result.
   Fixed leaves are checked literals, not copied calculations. Calls under
   loops, nonliteral arguments and unbound result types fail closed. *)
let prepare_lift_source (state : Interactive.State.istate) lift =
  let fail loc message =
    raise (Reporting.err_general loc ("HOL input lift: " ^ message)) in
  let definition, pattern, original_body, quantifiers, types, result =
    checked_source state lift.source_function lift.fixed_arguments in
  let loc = def_loc definition in
  let arguments, argument_types, selected =
    specialize_arguments state pattern (argument_patterns pattern types)
      types original_body lift.fixed_arguments in
  let identifiers = ref (IdSet.union (ids_of_ast state.ast) (pat_ids pattern)) in
  let remember id = identifiers := IdSet.add id !identifiers in
  let pat_alg = {Rewriter.id_pat_alg with p_aux = (fun (aux, annotation) ->
    let pat = P_aux (aux, annotation) in
    identifiers := IdSet.union (pat_ids pat) !identifiers; pat)} in
  ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with pat_alg;
    e_id = (fun id -> remember id; E_id id);
    e_ref = (fun id -> remember id; E_ref id);
    e_app = (fun (id,args) -> remember id; E_app (id,args));
    e_for = (fun (id,a,b,c,d,e) -> remember id; E_for (id,a,b,c,d,e));
    le_id = (fun id -> remember id; LE_id id);
    le_typ = (fun (typ,id) -> remember id; LE_typ (typ,id))
  } original_body);
  let rec fresh index =
    let name = "__hol_input" ^ string_of_int index in
    if IdSet.mem (mk_id name) !identifiers then fresh (index + 1) else
    let id = mk_id ~loc name in remember id; id in
  let body, acquired_parameters, acquired_boundaries = match lift.acquired with
    | None -> selected, [], []
    | Some selection ->
        let body = prune_closed_selectors state selected in
        let rec selected_call = function
          | E_aux (E_app (id, _), _) as exp
              when string_of_id id = selection.callee -> Some exp
          | E_aux (E_typ (_, exp), _) -> selected_call exp
          | _ -> None in
        let fixed_name, fixed_value = selection.fixed_binding in
        let binds_fixed pattern =
          IdSet.exists (fun id -> string_of_id id = fixed_name) (pat_ids pattern) in
        let contains_binding exp =
          let found = ref false in
          ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with
            e_let = (fun (pattern,rhs,body) ->
              if binds_fixed pattern && Option.is_some (selected_call rhs) then
                found := true;
              E_let (pattern,rhs,body))} exp);
          !found in
        let other_bindings = ref false and bindings = ref [] in
        ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with
          e_aux = (fun (aux, annotation) ->
            let exp = E_aux (aux, annotation) in
            (match aux with
             | E_let (pat,rhs,tail) ->
                 Option.iter (fun call ->
                   if binds_fixed pat then
                     bindings := (pat,rhs,tail,call) :: !bindings
                   else other_bindings := true) (selected_call rhs)
             | (E_for _ | E_loop _) when contains_binding exp ->
                 fail (exp_loc exp) "acquired calls under loops are unsupported"
             | _ -> ());
            exp)} body);
        let pat, rhs, tail, matched = match !bindings with
          | [binding] -> binding
          | [] when !other_bindings ->
              fail loc ("unknown acquired fixed binding: " ^ fixed_name)
          | _ -> fail loc "requires exactly one immutable acquired-input let" in
        let call_arguments = match matched with
          | E_aux (E_app (_,arguments), _) -> arguments
          | _ -> assert false in
        if not (List.for_all literal_input_argument call_arguments) then
          fail (exp_loc matched) "acquired call arguments must be literals";
        let original = original_source_call original_body selection.callee matched in
        let selected = Type_check.strip_exp matched in
        let fixed = ref None and parameters = ref [] and slots = ref [] in
        let environment = Type_check.env_of rhs in
        let rec replace path pat typ =
          if not (KidSet.is_empty (tyvars_of_typ typ)) then
            fail (pat_loc pat) "acquired result field type must be closed";
          match pat with
          | P_aux ((P_typ (_,pat) | P_var (pat,_)), _) -> replace path pat typ
          | P_aux (P_tuple patterns, (_, annotation)) ->
              (match Type_check.Env.expand_synonyms environment typ with
               | Typ_aux (Typ_tuple types, _)
                   when List.length patterns = List.length types ->
                   let values = List.mapi (fun index (pat,typ) ->
                     replace (path @ [index]) pat typ) (List.combine patterns types) in
                   E_aux (E_tuple values, (pat_loc pat, annotation))
               | _ -> fail (pat_loc pat) "acquired pattern does not match result type")
          | P_aux (P_id id, (leaf_loc, _)) ->
              (match Type_check.Env.lookup_id id (Type_check.env_of tail) with
               | Local (Immutable, _) -> ()
               | _ -> fail leaf_loc "acquired result requires immutable identifier fields");
              if string_of_id id = fixed_name then begin
                if !fixed <> None then fail leaf_loc "acquired fixed binding is ambiguous";
                let value = checked_selection_literal environment leaf_loc typ fixed_value in
                fixed := Some {binding = fixed_name; value = Type_check.strip_exp value;
                  binding_type = typ; binding_path = path};
                value
              end else begin
                let parameter = fresh 0 in
                let input_index = List.length !parameters in
                parameters := !parameters @ [parameter,typ];
                slots := !slots @ [{input_type = typ; input_index;
                  parameter = string_of_id parameter; result_path = path;
                  forwarded_index = None}];
                E_aux (E_id parameter, (leaf_loc, Type_check.mk_tannot environment typ))
              end
          | _ -> fail (pat_loc pat) "acquired result requires identifier or tuple fields" in
        let input_type = Type_check.typ_of rhs in
        let replacement = replace [] pat input_type in
        let fixed_binding = match !fixed with
          | Some fixed -> Some fixed
          | None -> fail (pat_loc pat) ("unknown acquired fixed binding: " ^ fixed_name) in
        let span = Option.get (real_source_span (exp_loc matched)) in
        let replaced = Rewriter.fold_exp {Rewriter.id_exp_alg with
          e_aux = (fun (aux, annotation) ->
            match aux with
            | E_let (pat,rhs,tail) ->
                (match selected_call rhs with
                 | Some call when real_source_span (exp_loc call) = Some span ->
                     E_aux (E_let (pat,replacement,tail), annotation)
                 | _ -> E_aux (aux,annotation))
            | _ -> E_aux (aux,annotation))} body in
        prune_closed_selectors state replaced, !parameters,
        [{lift; location = exp_loc matched; call = original;
          specialized_call = (if string_of_exp original = string_of_exp selected
            then None else Some selected);
          input_type; slots = !slots; fixed_binding;
          replacement = Some (Type_check.strip_exp replacement); caller = None}] in
  {definition; pattern; original_body; body; quantifiers; arguments;
   argument_types; result; identifiers; acquired_parameters; acquired_boundaries}

(* Clone a single checked function clause, preserving its source locations.
   Require literal call arguments: deleting their evaluation then cannot
   erase a register read/write, exception or early return. Calls in helpers
   are not replaced. Match the requested number of static occurrences;
   the default still rejects zero or multiple calls.

   Multiple inputs require unique real source spans. Sort argument slots
   by filename/start/end, not by fold callback order: a tree traversal is
   not an execution trace. Replace each occurrence at its original place,
   so branches, intervening writes and evaluation order remain unchanged.

   A fresh parameter avoids capture by any original identifier. Adding the
   call's result type to the original quantified signature also makes input
   changes visible: fetch(4) requires 32 bits where fetch(1) required 8.
   Existential witnesses not bound by that signature are rejected. *)
let lifted_definitions (state : Interactive.State.istate) lift =
  let fail loc message =
    raise (Reporting.err_general loc ("HOL input lift: " ^ message)) in
  if lift.expected_inputs <= 0 then
    fail Parse_ast.Unknown "expected input count must be positive";
  let prepared = prepare_lift_source state lift in
  let loc = def_loc prepared.definition in
  let pat = prepared.pattern and body = prepared.body in
  let original_body = prepared.original_body and quantifiers = prepared.quantifiers in
  let arguments = prepared.arguments and argument_types = prepared.argument_types
  and result = prepared.result in
  let derived = mk_id ~loc (lifted_name lift) in
  if IdSet.mem derived (ids_of_ast state.ast) then
    fail loc ("derived name already exists: " ^ lifted_name lift);
  let identifiers = prepared.identifiers in
  let remember id = identifiers := IdSet.add id !identifiers in
  let pat_alg = {Rewriter.id_pat_alg with
    p_aux = (fun (aux, annotation) ->
      let pat = P_aux (aux, annotation) in
      identifiers := IdSet.union (pat_ids pat) !identifiers;
      pat);
    p_id = (fun id -> remember id; P_id id);
    p_as = (fun (pat, id) -> remember id; P_as (pat, id))} in
  ignore (Rewriter.fold_pat pat_alg pat);
  let matches = ref [] in
  let contains_input exp =
    let found = ref false in
    ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with e_app = (fun (id, args) ->
      if string_of_id id = lift.input_function then found := true;
      E_app (id, args))} exp);
    !found in
  let e_aux (aux, annotation) =
    let exp = E_aux (aux, annotation) in
    match aux with
    | E_app (callee, arguments)
        when string_of_id callee = lift.input_function ->
        if not lift.evaluate_arguments &&
           not (List.for_all literal_input_argument arguments) then
          fail (exp_loc exp) "input call arguments must be literals";
        matches := exp :: !matches;
        exp
    | (E_for _ | E_loop _) when contains_input exp ->
        fail (exp_loc exp) "input calls under loops are unsupported"
    | _ -> exp in
  ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with
    e_aux; pat_alg;
    e_id = (fun id -> remember id; E_id id);
    e_ref = (fun id -> remember id; E_ref id);
    e_app = (fun (id, arguments) -> remember id; E_app (id, arguments));
    e_for = (fun (id, first, last, step, order, body) ->
      remember id; E_for (id, first, last, step, order, body));
    le_id = (fun id -> remember id; LE_id id);
    le_typ = (fun (typ, id) -> remember id; LE_typ (typ, id))
  } body);
  if List.length !matches <> lift.expected_inputs then
    fail loc (if lift.expected_inputs = 1 then
      "requires exactly one direct input call"
    else Printf.sprintf "requires exactly %d direct input calls"
      lift.expected_inputs);
  let source_span exp =
    match real_source_span (exp_loc exp) with
    | Some (first, last) ->
        Sail_file.Path.to_string (Sail_file.to_path first.pos_fname),
        first.pos_cnum, last.pos_cnum
    | _ -> fail (exp_loc exp) "multiple inputs require real source spans" in
  let matched =
    if lift.expected_inputs = 1 then !matches else
    let located = List.map (fun exp -> source_span exp, exp) !matches in
    let keys = List.map fst located in
    if List.length keys <> List.length (List.sort_uniq compare keys) then
      fail loc "multiple inputs have duplicate source spans";
    List.sort (fun (left, _) (right, _) -> compare left right) located
    |> List.map snd in
  let original_call matched =
    if lift.fixed_arguments = [] && lift.acquired = None then
      Type_check.strip_exp matched
    else original_source_call original_body lift.input_function matched in
  let rec fresh index =
    let name = "__hol_input" ^ string_of_int index in
    if IdSet.mem (mk_id name) !identifiers then fresh (index + 1) else name in
  let quantified, _ = quant_split quantifiers in
  let bound = KidSet.of_list (List.map kopt_kid quantified) in
  let inputs = List.mapi (fun index matched ->
    let input_index = List.length prepared.acquired_parameters + index in
    let parameter = fresh 0 in
    let input = mk_id ~loc parameter in
    remember input;
    let input_type = Type_check.typ_of matched in
    if not (KidSet.subset (tyvars_of_typ input_type) bound) then
      fail (exp_loc matched) "input type has an unbound source type witness";
    let original = original_call matched in
    let selected = Type_check.strip_exp matched in
    let specialized_call =
      if string_of_exp original = string_of_exp selected then None
      else Some selected in
    matched, input, input_type,
    {lift; location = exp_loc matched; call = original;
     specialized_call; input_type;
     slots = [{input_type; input_index; parameter; result_path = [];
       forwarded_index = None}];
     fixed_binding = None; replacement = None; caller = None}
  ) matched in
  let replaced = Rewriter.fold_exp {Rewriter.id_exp_alg with
    e_aux = (fun (aux, annotation) ->
      let exp = E_aux (aux, annotation) in
      match aux with
      | E_app (callee, arguments) when string_of_id callee = lift.input_function ->
          let _, input, _, _ = List.find (fun (matched, _, _, _) ->
            lift.expected_inputs = 1 || source_span exp = source_span matched)
            inputs in
          let supplied = E_aux (E_id input, annotation) in
          if not lift.evaluate_arguments then supplied else
          (* Arguments without effects need no evaluation; the others are
             bound to a typed wildcard in their original order. *)
          let rec effect_free (E_aux (aux, _) as exp) = match aux with
            | E_lit _ -> true
            | E_id id -> not (Type_check.Env.is_register id (Type_check.env_of exp))
            | E_typ (_, value) -> effect_free value
            | E_tuple values -> List.for_all effect_free values
            | E_app (id, values) ->
                Effects.function_is_pure id state.effect_info &&
                List.for_all effect_free values
            | _ -> false in
          List.fold_right (fun argument body ->
            if effect_free argument then body else
            let E_aux (_, argument_annotation) = argument in
            let pattern = P_aux (P_typ (Type_check.typ_of argument,
              P_aux (P_wild, argument_annotation)), argument_annotation) in
            E_aux (E_let (pattern, argument, body), annotation))
            arguments supplied
      | _ -> exp)} body in
  let parameters = prepared.acquired_parameters @
    List.map (fun (_,input,typ,_) -> input,typ) inputs in
  let patterns = arguments @ List.map (fun (input, input_type) ->
    mk_pat ~loc (P_typ (input_type, mk_pat ~loc (P_id input)))) parameters in
  let pattern = match patterns with
    | [pattern] -> pattern
    | patterns -> mk_pat ~loc (P_tuple patterns) in
  let definitions = [mk_val_spec ~loc (VS_val_spec (
     mk_typschm ~loc quantifiers (function_typ
       (argument_types @ List.map snd parameters) result),
     derived, None));
   mk_fundef ~loc [mk_funcl ~loc derived pattern (Type_check.strip_exp replaced)]] in
  definitions, prepared.acquired_boundaries @
    List.map (fun (_, _, _, boundary) -> boundary) inputs

let check_definitions (state : Interactive.State.istate) definitions =
  let input : untyped_ast = {defs = definitions; comments = []} in
  let checked, env = Type_error.check
      (Type_check.Env.open_all_modules state.env) input in
  let ast = {state.ast with defs = state.ast.defs @ checked.defs} in
  let effect_info = Effects.infer_side_effects false ast in
  {state with ast; env; effect_info}

let child_lift lift child =
  {lift with source_function = child; fixed_arguments = []; through = None;
    acquired = None}

(* Forward supplied inputs through one original helper call. The derived
   child has already been checked by Sail; replacing its caller preserves
   every original argument expression, the child body and their effects.
   This does not inline the child or substitute its returned decoded operand.

   Only closed child input types are supported. Transporting a child's type
   witnesses into a different caller would need checked type instantiation,
   not matching variable names. Reject that case instead. *)
let redirected_definitions state lift boundaries =
  let fail loc message =
    raise (Reporting.err_general loc ("HOL input lift: " ^ message)) in
  let child = Option.get lift.through in
  if child = lift.source_function then fail Parse_ast.Unknown "recursive helper path";
  let _,_,child_body,_,_,_ = checked_source state child [] in
  ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with
    e_app = (fun (id,args) ->
      if List.mem (string_of_id id) [child; lift.source_function] then
        fail (id_loc id) "recursive helper path";
      E_app (id,args))} child_body);
  let prepared = prepare_lift_source state lift in
  let loc = def_loc prepared.definition in
  let original = prepared.original_body and body = prepared.body in
  let quantifiers = prepared.quantifiers and arguments = prepared.arguments
  and types = prepared.argument_types and result = prepared.result in
  let derived = mk_id ~loc (lifted_name lift) in
  if IdSet.mem derived (ids_of_ast state.ast) then
    fail loc ("derived name already exists: " ^ lifted_name lift);
  let identifiers = prepared.identifiers in
  let remember id = identifiers := IdSet.add id !identifiers in
  let calls = ref [] in
  let contains_child exp =
    let found = ref false in
    ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with
      e_app = (fun (id, args) ->
        if string_of_id id = child then found := true;
        E_app (id,args))} exp);
    !found in
  let pat_alg = {Rewriter.id_pat_alg with p_aux = (fun (aux, annotation) ->
    let pattern = P_aux (aux, annotation) in
    identifiers := IdSet.union (pat_ids pattern) !identifiers; pattern)} in
  ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with pat_alg;
    e_id = (fun id -> remember id; E_id id);
    e_ref = (fun id -> remember id; E_ref id);
    e_app = (fun (id,args) -> remember id; E_app (id,args));
    e_for = (fun (id,a,b,c,d,e) -> remember id; E_for (id,a,b,c,d,e));
    le_id = (fun id -> remember id; LE_id id);
    le_typ = (fun (typ,id) -> remember id; LE_typ (typ,id));
    e_aux = (fun (aux, annotation) ->
      let exp = E_aux (aux, annotation) in
      (match aux with
       | E_app (id,_) when string_of_id id = lift.source_function ->
           fail (exp_loc exp) "recursive caller is unsupported"
       | E_app (id,_) when string_of_id id = child -> calls := exp :: !calls
       | (E_for _ | E_loop _) when contains_child exp ->
           fail (exp_loc exp) "helper calls under loops are unsupported"
       | _ -> ());
      exp)} body);
  let call = match !calls with
    | [call] -> call
    | _ -> fail loc "requires exactly one direct helper call" in
  let span = match real_source_span (exp_loc call) with
    | Some span -> span
    | _ -> fail (exp_loc call) "helper call requires a real source span" in
  let originals = ref [] in
  ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with
    e_aux = (fun (aux,annotation) ->
      let exp = E_aux (aux,annotation) in
      (match aux with
       | E_app (id,_) when string_of_id id = child &&
           Reporting.simp_loc (exp_loc exp) = Some span ->
           originals := exp :: !originals
       | _ -> ());
      exp)} original);
  let original_call = match !originals with
    | [call] -> Type_check.strip_exp call
    | _ -> fail (exp_loc call) "helper call has no unique original source call" in
  let selected_call = Type_check.strip_exp call in
  let caller = Some {caller_location = exp_loc call; caller_call = original_call;
    caller_specialized_call = (if string_of_exp original_call =
      string_of_exp selected_call then None else Some selected_call);
    derived_child = lifted_name (child_lift lift child)} in
  let rec fresh index =
    let name = "__hol_input" ^ string_of_int index in
    if IdSet.mem (mk_id name) !identifiers then fresh (index + 1) else name in
  let next_index = ref (List.length prepared.acquired_parameters) in
  let inputs, forwarded_boundaries = List.map (fun boundary ->
    if real_source_span boundary.location = None then
      fail boundary.location "helper input requires a real source span";
    let parameters, slots = List.map (fun (slot : input_slot) ->
      if not (KidSet.is_empty (tyvars_of_typ slot.input_type)) then
        fail boundary.location "helper input type must be closed";
      let parameter = fresh 0 in
      let input = mk_id ~loc parameter in
      remember input;
      let input_index = !next_index in incr next_index;
      (input,slot.input_type), {slot with parameter; input_index;
        forwarded_index = Some slot.input_index}
    ) boundary.slots |> List.split in
    parameters, {boundary with lift; slots; caller}
  ) boundaries |> List.split in
  let inputs = List.concat inputs in
  let replaced = Rewriter.fold_exp {Rewriter.id_exp_alg with
    e_aux = (fun (aux,annotation) ->
      match aux with
      | E_app (id,args) when string_of_id id = child ->
          E_aux (E_app (mk_id ~loc (lifted_name (child_lift lift child)),
            args @ List.map (fun (input,_) -> mk_exp ~loc (E_id input)) inputs),
            annotation)
      | _ -> E_aux (aux,annotation))} (Type_check.strip_exp body) in
  let parameters = prepared.acquired_parameters @ inputs in
  let patterns = arguments @ List.map (fun (input,typ) ->
    mk_pat ~loc (P_typ (typ,mk_pat ~loc (P_id input)))) parameters in
  let pattern = match patterns with
    | [pattern] -> pattern
    | patterns -> mk_pat ~loc (P_tuple patterns) in
  [mk_val_spec ~loc (VS_val_spec (mk_typschm ~loc quantifiers
     (function_typ (types @ List.map snd parameters) result),
     derived,None));
   mk_fundef ~loc [mk_funcl ~loc derived pattern replaced]],
  prepared.acquired_boundaries @ forwarded_boundaries

let lift_inputs ?(record = fun _ -> ()) state requested =
  let requested = List.sort_uniq compare requested in
  let check_names requests =
    let names = List.map lifted_name requests in
    if List.length names <> List.length (List.sort_uniq String.compare names) then
      raise (Reporting.err_general Parse_ast.Unknown "HOL input lift: derived names collide") in
  check_names requested;
  let direct = List.filter (fun lift -> lift.through = None) requested in
  let children = List.filter_map (fun lift -> Option.map (child_lift lift)
    lift.through) requested in
  let leaf_lifts = List.sort_uniq compare (direct @ children) in
  check_names leaf_lifts;
  let leaves = List.map (fun lift ->
    let definitions,boundaries = lifted_definitions state lift in
    lift,definitions,boundaries) leaf_lifts in
  let state = check_definitions state
    (List.concat_map (fun (_,definitions,_) -> definitions) leaves) in
  let definitions, boundaries = List.filter (fun lift -> lift.through <> None) requested
    |> List.map (fun lift ->
      let child = child_lift lift (Option.get lift.through) in
      let _,_,boundaries = List.find (fun (leaf,_,_) -> leaf = child) leaves in
      redirected_definitions state lift boundaries) |> List.split in
  let state = if definitions = [] then state
    else check_definitions state (List.concat definitions) in
  (* Each reached child definition must describe its own excluded input,
     even when no instruction directly requested that clone. Parent records
     separately describe forwarding; publication filters both by reachability. *)
  let leaf_boundaries = List.concat_map (fun (_,_,boundaries) -> boundaries) leaves in
  List.iter record (leaf_boundaries @ List.concat boundaries);
  state

(* Ask Sail to check the bindings against the loaded upstream declarations.
   Types come before bodies so aliases can refer to other bindings.
   Recompute effects: a wrapper around a register-writing instruction
   must itself be classified as effectful. No source file is written. *)
let instantiate ?record (state : Interactive.State.istate) entries =
  let state = match lifts entries with
    | [] -> state
    | requested -> lift_inputs ?record state requested in
  let names = List.map (fun entry -> entry.name) entries in
  if List.length names <> List.length (List.sort_uniq String.compare names) then
    raise (Reporting.err_general Parse_ast.Unknown "duplicate HOL instruction entry");
  let specifications, bodies = List.split (List.map (fun entry ->
    match definitions entry with
    | [specification; body] -> specification, body
    | _ -> assert false) entries) in
  check_definitions state (specifications @ bodies)
