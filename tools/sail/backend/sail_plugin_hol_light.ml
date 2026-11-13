open Libsail
open Ast
open Ast_defs
open Ast_util
open Ast_compare
(* After Ast_util, whose constructors Unit and Bool it shadows. *)
open Hol_term

(* Sail compiler target: checked Sail program -> HOL definition source.

   This module runs inside Sail's OCaml compiler process, using libsail.
   The Arm/RV32 tables supply instruction bindings: named Sail calls grouped
   into families, preserving the existing HOL instruction operand order.
   Source-function requests are inferred from their checked calls and fix
   only necessary numeric type arguments; checked Sail patterns supply operands.
   prepare_upstream checks the bindings and finds the functions they call;
   export_checked translates them; publish writes HOL new_definition source.

   A selected function is a root; called helpers retain their actual bodies.
   Cuts replace register, memory and platform bodies with explicit meanings.
   Supported primitives also receive handwritten HOL meanings.
   Arm state-computation exports explicitly omit FPSR and branch-target
   metadata (BTypeNext/BTypeCompatible) component writes:
   assign retains selectors, values, reads and every other effect.
   The dependency report names both trusted observation boundaries.
   Every instruction exports a relation between initial and final states.
   Normal execution equates the calculated state with the candidate final
   state. A reached Arm.faults boundary instead permits every final state,
   skipping the remaining instruction; other exceptions remain unsupported.
   Unsupported reachable constructs raise fail rather than produce output.

   The translation and its architecture interpretations are trusted: a kernel
   proof about the generated definition does not prove Sail preservation.
   Each architecture's table file (arm.ml, rv32.ml, x86_shina.ml,
   x86_rems.ml) lists its cuts and the source names this file interprets.

   Sail concepts used here
   ----------------------
   Sail is a language for describing instruction set architectures. Its
   compiler parses the external model, resolves names and checks types before
   calling this target. The target receives Interactive.State.istate:
     ast         program declarations and definitions;
     env         types, constructors, registers and numeric constraints;
     effect_info operations such as register writes, used to carry state.

   Ast is libsail's syntax-tree module. Each expression is an E_aux wrapper
   around a constructor such as E_app (call), E_if (conditional), E_assign
   (assignment) or E_return. P_aux wraps patterns; Typ_aux wraps types;
   DEF_aux wraps top-level declarations/definitions. The wrappers carry
   source locations. Checked expression/pattern wrappers additionally carry
   Type_check.tannot annotations.
   Type_check.typ_of and env_of recover the expression's checked type and
   the scope in which that type was established. The location is for errors;
   the type/environment are inputs to the translation's safety checks.

   Sail distinguishes a function's val declaration from its function body.
   The declaration gives its interface, including any preconditions. A cut
   keeps that declaration and removes the body: this is how an upstream
   register or platform operation receives our explicit HOL interpretation.
   All other supported reachable bodies are translated from the program.

   Sail types can depend on numbers. bits('N) is a bitvector whose length
   is the numeric type variable 'N; int('i) describes the singleton integer
   value 'i. Constraints such as 0 <= 'i <= 31 belong to the source type
   environment. In libsail, id names a program identifier, kid names a type
   variable, nexp represents a numeric type expression and n_constraint a
   proposition about those expressions. KBindings maps type variables to
   their instantiations; K_int and K_type distinguish numbers from types.

   Instruction bindings select widths and operations. Called source functions
   first receive a generic translation attempt, then necessary fixed widths,
   retaining other operands. number resolves fixed lengths; poly_dimension
   represents supported symbolic lengths using HOL type dimensions.
   specialize_helper_types substitutes
   type arguments into a helper's checked body; specialize_helper transports
   numeric facts only after checking them in the caller's scope. These checks
   use Sail's constraint prover (and its solver), not HOL proof tactics.
   They therefore belong to the trusted translation. Root refinements that
   cannot be represented without losing preconditions are rejected.

   How the translation is organized
   --------------------------------
   prepare_upstream checks requests and selects all their called functions.
   export_checked sets each root's completion conditions and traverses its body:
     pure/tail     a value expression or pure helper result;
     computation   sequential state/local changes, loops and early returns.
   simple_write and flat_memory interpret writes and accesses. computation
   uses continuations: functions saying what HOL expression to emit after
   the source computation produces a value/state.
   They construct syntax during export; they do not execute an instruction.

   These checks protect different properties of the source computation.
   For F + write_then(), argument binding captures F before the helper can
   change it. A helper return resumes its caller rather than exiting the
   root. A partially assigned word retains unknown bits until the selected
   bits are proved initialized. A concrete word width does not discharge
   the callee's other numeric preconditions.

   htyp and term are our HOL representation and expression tree. A source
   assignment becomes a HOL let binding of a new state/local value. Argument
   evaluation, lexical scope and helper returns must survive that conversion.
   print_term only prints the resulting tree; a separate HOL Light process
   creates the definitions and checks agreement with s2n-bignum.
   shared_function_call infers reusable definitions from checked parameters;
   translation_checkpoint restores all bookkeeping after a failed attempt.
   Shared_value carries literal/bounds facts separately from the emitted call.
   Source refinements restrict correspondence to the original call domain.
   definition_source_comments copies original Sail bodies beside definitions.

   Audit the handwritten choices as well as the traversal. In particular:
     hol_type and observes_projected_payload: representation/projection;
     call and computation's primitive cases: word/state/platform meaning;
     numeric checks and value tracking: conditions permitting specialization;
     scope/continuations/argument binding: source evaluation order and effects;
     export_checked: the domain and observation of the exported instruction.
   A well-typed, kernel-checked HOL definition can still be a mistranslation.
   The tests and dependency reports support review; they are not a general
   theorem that this compiler preserves Sail semantics. *)

(* Command-line selections and per-export bookkeeping.
   Within one process the roots of an artifact are translated one after
   another, and these refs are shared across them; with --hol-light-jobs
   each family runs in its own forked worker, which starts from the
   parent's prepared state.
   export_checked resets dependency/check collections for each artifact, and
   the root mode, fresh names, register tracking and loop budget for each
   root. Their lifetime matters: a contract or specialization from one
   family must not silently govern another. *)
let roots = ref []
let used_primitives = ref []
let used_functions = ref []
let used_globals = ref []
let used_registers = ref []
let fresh_index = ref 0
let defined_functions = ref []
let effect_info = ref Effects.empty_side_effect_info
let state_type = ref "armstate"
let used_enums = ref []
let used_results = ref false
(* Assertions proved during translation: the assertion's text and
   location for the translation log, its source text and file:line for
   the dependency report, the chain of functions it was reached through,
   and whether z3 proved it (otherwise it evaluated to true). *)
let proved_assertions : (string * string * string * string * bool) list ref = ref []
let guarded_assertions = ref []
(* Conditionals decided during translation: the location, whether the then
   branch was kept, the condition's source text, the chain of functions it
   was reached through, and whether z3 decided it (otherwise the translated
   condition was already true or false). The location is file:line:column
   ranges; the report shows file:line. *)
let selected_branches : (string * bool * string * string * bool) list ref =
  ref []
(* Interpretations applied during translation, for the dependency report:
   the interpretation names, the Sail call or construct, and the HOL term
   that replaced it. See record_interpretation. *)
let applied_interpretations : (string list * string * string) list ref = ref []
let disabled_extensions = ref []
let normal_retirement = ref false
let state_computation = ref false
let requested_retirement = ref false
(* Sharing is safe only when a helper cannot reach non-local control or an
   arbitrary source value: those need the whole instruction continuation.
   Recomputed from the selected checked bodies, conservatively including
   both arms of conditionals. Instruction outputs are always relations.
   Constructs not listed here, such as exit and unproved assertions, are
   lowered to markers that the term printer refuses, so a shared helper
   that reached one would fail to print rather than hide it. *)
let faulting_functions = ref []
(* Self-recursive helpers with no numeric type parameters, such as REMS's
   logcount_int on int. They unfold only by value bounds at a call site, so
   a shared HOL definition with an unbounded parameter cannot exist; the
   translator skips that attempt instead of repeating it at every level. *)
let value_recursive_functions = ref []
let unobserved_undefined = ref []
let case_name = ref "sail_hl_result_case"
let mapping_definitions = ref []
let used_mappings = ref []
(* Deduplicate report text, not proof queries or source contexts. Inlined
   lane loops encounter the same printed fact millions of times. A
   persistent set keeps the report bounded and checkpoint restoration exact;
   every call site still performs its original constraint proof first. *)
module Evidence_set = Set.Make(String)
let proved_numeric_arguments = ref Evidence_set.empty
let record_numeric_argument_fact name fact =
  proved_numeric_arguments := Evidence_set.add
    (name ^ " " ^ string_of_n_constraint fact) !proved_numeric_arguments

(* Type translation records every enum encounter. Map that potentially
   large list tail-recursively before sorting its distinct report names. *)
let exported_enum_names () =
  List.sort_uniq String.compare (List.rev_map fst !used_enums)
(* Primitive encounters can also exceed the native stack limit. Prepend the
   optional retirement contract instead of copying the encounter list with
   append; sorting still gives exactly the same distinct report entries. *)
let exported_primitive_contracts exported_roots =
  let primitives =
    if List.exists (fun (_, mode) -> mode = "normal-retirement") exported_roots
    then "successful-root-jump-event" :: !used_primitives
    else !used_primitives in
  List.sort_uniq String.compare primitives
let successful_checks = ref []
let unrolled_loops = ref []
let loop_budget = ref 0
(* Unfolded calls of value-bounded integer recursion in the current root.
   A byte's logcount unfolds into 511 calls, so it has a separate bound. *)
let value_recursion_budget = ref 0
(* The upstream path keeps the architecture's genuine declarations. Only
   these explicitly named boundary views project richer source types to
   the observations present in s2n-bignum's instruction state. *)
let upstream_architecture = ref None
(* The x86 model compiled in this run. Exactly one source descriptor
   governs the instruction table, state bindings and output names; the
   translator never mixes another source's helpers or flags. *)
let x86_model : string option ref = ref None
let upstream_families : string list ref = ref []
let used_case_names = ref []
let output_directory : string option ref = ref None
let active_root = ref "upstream preparation"
let requested_assumptions : Entry.assumption list ref = ref []
let configured_assumptions : Entry.assumption list ref = ref []
let used_assumptions : Entry.assumption list ref = ref []
let artifact_assumptions : Entry.assumption list ref = ref []
let assumption_key = function
  | Entry.Feature (name, _) -> "feature " ^ name
  | Entry.Initial_bit (register, field, _) -> "initial-bit " ^ register ^ "." ^ field
  | Entry.Initial_enum (register, _) -> "initial-enum " ^ register
  | Entry.Initial_bool (register, _) -> "initial-bool " ^ register
let assumption_text fact =
  assumption_key fact ^ "=" ^
  (match fact with
   | Entry.Feature (_, value) -> string_of_bool value
   | Entry.Initial_bit (_, _, value) -> if value then "0b1" else "0b0"
   | Entry.Initial_enum (_, constructor) -> constructor
   | Entry.Initial_bool (_, value) -> string_of_bool value)
let assumption_comments facts =
  match List.sort_uniq compare facts with
  | [] -> ""
  | facts ->
      "(* Source assumptions: " ^
      String.concat "; " (List.map assumption_text facts) ^
      ".\n   These constrain Sail's processor/input state; specialization is trusted. *)\n"
(* One definition's source dependencies, separate from the artifact-wide
   dependency report. Reset at each root so earlier roots cannot hide a
   shared helper's source from the next definition's commentary. *)
let definition_sources = ref []
let input_boundaries : Entry.input_boundary list ref = ref []
let record_input_boundary boundary =
  input_boundaries := boundary :: !input_boundaries

let fail loc message = raise (Reporting.err_general loc ("HOL Light: " ^ message))
let x86_source () =
  match !x86_model with
  | Some "shina" -> X86_shina.source
  | Some "rems" -> X86_rems.source
  | _ -> fail Parse_ast.Unknown "x86 requires --hol-light-x86-source rems|shina"
(* A state binding applies only when the selected source declares it. *)
let x86_binds binding =
  !upstream_architecture = Some "x86" && List.mem binding (x86_source ()).X86.bindings
(* Under REMS's Gpr_access binding, register i is registers :> element i,
   reached only through the read_gpr/write_gpr cuts. A direct read or write
   of one of those source registers would become a separate component
   parameter, so it is refused. *)
let refuse_bound_gpr loc name =
  if x86_binds X86.Gpr_access && List.mem name X86_rems.registers then
    raise (Reporting.err_general loc
      ("HOL Light: REMS register " ^ name ^ " is accessed only through read_gpr/write_gpr"))
(* The REMS evaluation profile; see X86.source.extended_evaluation. *)
let extended_evaluation () =
  !upstream_architecture = Some "x86" && (x86_source ()).X86.extended_evaluation
let x86_shina_registers () =
  !upstream_architecture = Some "x86" && (x86_source ()).X86.model = "shina"
let fresh () = let n = !fresh_index in incr fresh_index; "v" ^ string_of_int n

(* Membership in !defined_functions, which lists every function of the
   prepared program: several thousand names for the Arm batch. Translation
   asks millions of times, so index the current list (rebuilt whenever the
   reference holds a different list) instead of scanning it. *)
let defined_index = ref ([], Hashtbl.create 1)
let is_defined_function name =
  let known, _ = !defined_index in
  if known != !defined_functions then begin
    let index = Hashtbl.create (2 * List.length !defined_functions + 1) in
    List.iter (fun name -> Hashtbl.replace index name ()) !defined_functions;
    defined_index := (!defined_functions, index)
  end;
  Hashtbl.mem (snd !defined_index) name
(* Specializing a comparison interprets a primitive just as emitting its
   ordinary call does. Such paths must use the original declaration's
   effect information, not merely recognize its spelling. *)
let pure_external id =
  not (is_defined_function (string_of_id id)) &&
  Effects.function_is_pure id !effect_info

let kid_name kid =
  let name = string_of_kid kid in
  if String.length name > 0 && name.[0] = '\'' then
    String.sub name 1 (String.length name - 1)
  else name

(* Encode source names into HOL/OCaml identifiers, escaping every non-
   alphanumeric byte. Name mangling establishes no semantic correspondence:
   the checked source declaration and translated body provide that context. *)
let symbol prefix name =
  let b = Buffer.create 32 in
  Buffer.add_string b prefix;
  String.iter (fun c ->
    if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
       (c >= '0' && c <= '9') then Buffer.add_char b c
    else Buffer.add_string b (Printf.sprintf "_%02x" (Char.code c))
  ) name;
  Buffer.contents b

(* HOL datatypes and constructors are global in one kernel. Sources that
   qualify their names put the escaped output stem between the fixed
   prefix and the escaped source name: REMS's proc_mode in x86-rems-shift
   becomes sail_hl_type_x86_2drems_2dshift_proc_5fmode. Otherwise the
   established unqualified names remain. *)
let type_namespace = ref ""
let type_symbol name = symbol ("sail_hl_type_" ^ !type_namespace) name
let ctor_symbol name = symbol ("sail_hl_ctor_" ^ !type_namespace) name

(* Resolve a numeric TYPE expression, not an arbitrary runtime expression.
   ctx contains fixed numeric type arguments. Affine cancellation can yield
   a constant slice length even with a symbolic offset; an unresolved length
   must fail here; poly_dimension separately handles generic word types. *)
let number ctx (Nexp_aux (_, loc) as expression) =
  (* A fixed slice length may contain a symbolic offset twice, such as
     (offset + width - 1) - offset + 1. Cancel affine coefficients rather
     than invent a value for that offset. Use unbounded arithmetic until
     converting the final, genuinely constant expression. *)
  let merge left right =
    List.fold_left (fun terms (name, value) ->
      let value = Big_int.add value
        (Option.value (List.assoc_opt name terms) ~default:Big_int.zero) in
      let terms = List.remove_assoc name terms in
      if Big_int.equal value Big_int.zero then terms else (name, value) :: terms
    ) left right in
  let scale n terms = List.filter_map (fun (name, value) ->
    let value = Big_int.mul n value in
    if Big_int.equal value Big_int.zero then None else Some (name, value)
  ) terms in
  let rec affine (Nexp_aux (aux, nloc) as expression) =
    match aux with
    | Nexp_constant n -> n, []
    | Nexp_var kid ->
        (match List.assoc_opt (kid_name kid) ctx with
         | Some n -> Big_int.of_int n, []
         | None -> Big_int.zero, [kid_name kid, Big_int.of_int 1])
    | Nexp_sum (x, y) ->
        let xc, xs = affine x and yc, ys = affine y in
        Big_int.add xc yc, merge xs ys
    | Nexp_minus (x, y) ->
        let xc, xs = affine x and yc, ys = affine y in
        Big_int.sub xc yc, merge xs (scale (Big_int.of_int (-1)) ys)
    | Nexp_neg x ->
        let c, xs = affine x in
        Big_int.negate c, scale (Big_int.of_int (-1)) xs
    | Nexp_times (x, y) ->
        let xc, xs = affine x and yc, ys = affine y in
        if xs = [] then Big_int.mul xc yc, scale xc ys
        else if ys = [] then Big_int.mul xc yc, scale yc xs
        else fail nloc "nonlinear symbolic numeric type expressions are unsupported"
    | Nexp_app (Id_aux (Id "div", _), [x; y]) ->
        (* This is Sail's built-in numeric type operation, not a call to a
           source function named DIV. Evaluate only fixed operands, using
           the same unbounded division as Ast_util.nexp_simp. Positive
           divisors have the Euclidean meaning used by sizeof's ediv_int
           rewrite; unresolved or nonpositive divisors remain unsupported.
           No runtime calculation or helper body is replaced here. *)
        let xc, xs = affine x and yc, ys = affine y in
        if xs <> [] || ys <> [] then
          fail nloc "numeric type division requires fixed operands";
        if Big_int.less_equal yc Big_int.zero then
          fail nloc "numeric type division requires a positive divisor";
        Big_int.div xc yc, []
    | _ -> fail nloc ("unsupported numeric type expression " ^ string_of_nexp expression) in
  match affine expression with
  | constant, [] -> Nat_big_num.to_int constant
  | _, (name, _) :: _ ->
      fail loc ("uninstantiated numeric type variable '" ^ name)

let contract_registers : (string * htyp) list ref = ref []
(* A generic attempt binds only interface width variables. A stamp is the
   variable's shadowing depth and its binding location. The depth keeps a
   same-spelled variable in a nested scope from acquiring the interface's
   HOL type; the location keeps an inlined helper's own 'n, whose depth is
   also 0, from acquiring the shared function's facts about its 'n.
   Ordinary instruction translation leaves this map empty; unsupported
   dimensions trigger width specialization. *)
type kid_stamp = int * Parse_ast.l option
let kid_stamp env kid : kid_stamp =
  Type_check.Env.shadows kid env,
  KBindings.find_opt kid (Type_check.Env.get_typ_var_locs env)
let poly_dimensions : (string * kid_stamp * string) list ref = ref []
let poly_width_expressions : (nexp * (string * kid_stamp) list * string) list ref = ref []
let poly_fixed_arguments : (string * kid_stamp * int) list ref = ref []
let generic_widths_active () =
  !poly_dimensions <> [] || !poly_width_expressions <> []

let poly_variable env kid =
  List.find_map (fun (name, scope, dimension) ->
    if name = kid_name kid && scope = kid_stamp env kid then
      Some dimension else None) !poly_dimensions

let positive_poly_environment env =
  let env = List.fold_left (fun env (name, scope, value) ->
    let kid = mk_kid name in
    if kid_stamp env kid = scope &&
       KBindings.find_opt kid (Type_check.Env.get_typ_vars env) = Some K_int
    then Type_check.Env.add_constraint (nc_eq (nvar kid) (nint value)) env
    else env) env !poly_fixed_arguments in
  List.fold_left (fun env (name, scope, _) ->
    let kid = mk_kid name in
    if kid_stamp env kid = scope &&
       KBindings.find_opt kid (Type_check.Env.get_typ_vars env) = Some K_int
    then Type_check.Env.add_constraint (nc_lt (nint 0) (nvar kid)) env
    else env) env !poly_dimensions

(* Discharge a SOURCE numeric proposition in its checked scope, extended by
   established specialization facts: numeric widths fixed by the caller and
   proved facts about the current helper's parameters. Type_check.prove
   calls Sail's constraint machinery; it does not create a HOL theorem.
   A successful answer permits an otherwise unsafe translation (e.g. a
   bounded index or static slice).

   The answer depends only on the environment, the goal, the widths and
   facts, and the generic-width facts that positive_poly_environment adds.
   Translation asks the same question many times: the x86 vector family
   asks about five million, over 99% of them repeats, as unrolled lanes
   reach the same checked calls. Remember the answers within one artifact.
   Environments are immutable and compared physically; the other inputs
   structurally. A remembered answer is the one Type_check.prove gave for
   the same inputs. *)
(* compare, unlike (=), skips physically shared subterms; both agree on
   these closure-free syntax trees. *)
let same x y = x == y || compare x y = 0
let rec same_list xs ys = xs == ys || match xs, ys with
  | x :: xs, y :: ys -> same x y && same_list xs ys
  | [], [] -> true
  | _ -> false
module Proof_key = struct
  type t = n_constraint * (string * int) list * n_constraint list
  let equal (goal, widths, facts) (goal', widths', facts') =
    same goal goal' && same_list widths widths' &&
    List.compare_lengths facts facts' = 0 && same_list facts facts'
  (* Consecutive questions usually share one facts list; hash it once. *)
  let last_facts = ref ([], 0)
  let facts_hash facts =
    let known, hash = !last_facts in
    if known == facts then hash else begin
      let hash = List.fold_left (fun hash fact ->
        hash * 65599 + Hashtbl.hash_param 12 120 fact) 0 facts in
      last_facts := (facts, hash);
      hash
    end
  let hash (goal, widths, facts) =
    (Hashtbl.hash_param 50 500 goal * 31 + Hashtbl.hash widths) * 65599 +
    facts_hash facts
end
module Proof_table = Hashtbl.Make (Proof_key)
(* Each question keeps one binding; its answers are listed per environment. *)
let proved_goals :
  (Type_check.Env.t * (string * kid_stamp * int) list *
   (string * kid_stamp * string) list * bool)
  list ref Proof_table.t = Proof_table.create 4096

(* Consecutive questions usually come from one helper call, with the same
   environment, widths, facts and generic-width state. Adding every fact to
   the environment dominates a new question, so keep the last such scope. *)
let last_scope = ref None

let proved_in env widths facts goal =
  let key = goal, widths, facts in
  let fixed = !poly_fixed_arguments and dimensions = !poly_dimensions in
  let answers = match Proof_table.find_opt proved_goals key with
    | Some answers -> answers
    | None ->
        let answers = ref [] in
        Proof_table.add proved_goals key answers;
        answers in
  match List.find_opt (fun (known, fixed', dimensions', _) ->
      known == env && same_list fixed fixed' && same_list dimensions dimensions')
      !answers with
  | Some (_, _, _, proved) -> proved
  | None ->
      let scope = match !last_scope with
        | Some (env', widths', facts', fixed', dimensions', scope)
          when env' == env && widths' == widths && facts' == facts &&
               fixed' == fixed && dimensions' == dimensions -> scope
        | _ ->
            (* A caller-selected width also specializes constraints in the
               original helper environment, not just the goal being proved.
               Never add a binding for a type variable absent from that
               environment. *)
            let scope = List.fold_left (fun env (name, n) ->
              let kid = mk_kid name in
              match KBindings.find_opt kid (Type_check.Env.get_typ_vars env) with
              | Some K_int -> Type_check.Env.add_constraint
                  (nc_eq (nvar kid) (nint n)) env
              | _ -> env
            ) (positive_poly_environment env) widths in
            let scope = List.fold_left (fun env fact ->
              Type_check.Env.add_constraint fact env
            ) scope facts in
            last_scope := Some (env, widths, facts, fixed, dimensions, scope);
            scope in
      let specialized = List.fold_left (fun goal (name, n) ->
        constraint_subst (mk_kid name) (arg_nexp (nconstant (Nat_big_num.of_int n))) goal
      ) goal widths in
      let proved = Type_check.prove __POS__ scope specialized in
      answers := (env, fixed, dimensions, proved) :: !answers;
      proved

(* Generic word types must instantiate to the concrete numeral types used
   by instruction bindings. tybit0 does: substituting N=32 gives 64 exactly.
   finite_sum/prod/diff have the calculated dimensions, but do not reduce to
   numeral types. Until calls include explicit word conversions for those
   constructions, specialize them rather than emit ill-typed applications.
   The source prover must also establish positivity. *)
let rec poly_dimension env (Nexp_aux (aux, loc) as width) =
  if not (proved_in env [] [] (nc_lt (nint 0) width)) then
    fail loc "polymorphic words require a proved positive source width";
  let expression = List.find_map (fun (expression, scopes, dimension) ->
    if List.for_all (fun (name, scope) ->
        let kid = mk_kid name in
        KBindings.mem kid (Type_check.Env.get_typ_vars env) &&
        kid_stamp env kid = scope) scopes &&
       proved_in env [] [] (nc_eq width expression)
    then Some dimension else None) !poly_width_expressions in
  let variable = List.find_map (fun (name, scope, dimension) ->
    let kid = mk_kid name in
    if KBindings.mem kid (Type_check.Env.get_typ_vars env) &&
       kid_stamp env kid = scope &&
       proved_in env [] [] (nc_eq width (nvar kid))
    then Some dimension else None) !poly_dimensions in
  match expression, variable with
  | Some dimension, _ | _, Some dimension -> dimension
  | None, None ->
  match aux with
  | Nexp_constant n -> Nat_big_num.to_string n
  | Nexp_var kid ->
      (match poly_variable env kid with Some dimension -> dimension
       | None -> fail loc ("operand-dependent width " ^ string_of_nexp width))
  | Nexp_sum (left, right) when
      proved_in env [] [] (nc_eq left right) ->
      (* Checked concatenation types often spell doubling as N + N.
         Use the binary constructor so numeral instances have exactly the
         requested HOL type, rather than an isomorphic finite_sum type. *)
      "(" ^ poly_dimension env left ^ ")tybit0"
  | Nexp_times (Nexp_aux (Nexp_constant n, _), right)
      when Nat_big_num.equal n (Nat_big_num.of_int 2) ->
      "(" ^ poly_dimension env right ^ ")tybit0"
  | Nexp_times (left, Nexp_aux (Nexp_constant n, _))
      when Nat_big_num.equal n (Nat_big_num.of_int 2) ->
      "(" ^ poly_dimension env left ^ ")tybit0"
  | _ -> fail loc ("unsupported polymorphic dimension " ^ string_of_nexp width)
(* HOL surface types. Records use ordered products; result/option use sums;
   enum declarations are emitted later with define_type. These choices, and
   the exceptional architecture projections in hol_type, are part of the TCB.
   The printed unit type "1" also represents empty bits, but htyp keeps the two
   source types distinct so primitive signature checks can distinguish them. *)
let rec type_text = function
  | Word n -> string_of_int n ^ " word"
  | Poly_word dimension -> "(" ^ dimension ^ ")word"
  (* Sail's empty bitvector has one value. It is not a HOL 0 word:
     HOL's dimindex(:0) is not zero. Keep its unique representation distinct
     from Unit internally, including in primitive signature checks. *)
  | Empty_bits -> "1"
  (* Internal variable-width bits carry their evaluated source width and
     unsigned payload. Roots and architectural state cannot expose them. *)
  | Dynamic_bits -> "(int#num)"
  | Int -> "int"
  | Bool -> "bool"
  | String_type -> "string"
  | Unit -> "1"
  | Tuple ts -> "(" ^ String.concat "#" (List.map type_text ts) ^ ")"
  | Enum name -> type_symbol name
  | Record fields -> type_text (Tuple (List.map snd fields))
  | Result (ok, err) -> "(" ^ type_text ok ^ "+" ^ type_text err ^ ")"
  | Option_type payload -> "(1+" ^ type_text payload ^ ")"
  | Unit_variant (name, _) -> type_symbol name
  | Binary_variant ((_, left), (_, right)) ->
      type_text (Result (left, right))

(* Append each token once. Concatenating the string for every enclosing let
   copies the whole tail repeatedly, making deep generated bodies quadratic. *)
let print_term term =
  let buffer = Buffer.create 4096 in
  let add = Buffer.add_string buffer in
  let rec separated separator = function
    | [] -> ()
    | [value] -> print value
    | value :: rest -> print value; add separator; separated separator rest
  and print = function
  | Fault | Stop _ | Reject | Choose _ ->
      fail Parse_ast.Unknown "unlowered instruction control"
  | Atom text -> add text
  | String_literal text ->
      (* HOL's string type is char list. ASCII's Boolean arguments are
         ordered from bit7 to bit0, as in HOL's mk_char/pmk_char. Printing
         constructors preserves every byte without exposing quote, backtick,
         backslash, NUL or non-ASCII bytes to either quotation parser. *)
      let character byte =
        let code = Char.code byte in
        let bits = List.init 8 (fun index ->
          if code land (1 lsl (7 - index)) <> 0 then "T" else "F") in
        "(ASCII " ^ String.concat " " bits ^ ")" in
      for index = 0 to String.length text - 1 do
        add "(CONS "; add (character text.[index]); add " "
      done;
      add "(NIL:char list)";
      for _ = 1 to String.length text do add ")" done
  | App (name, arguments) ->
      add "("; add name; add " "; separated " " arguments; add ")"
  | Infix (operator, left, right) ->
      add "("; print left; add " "; add operator; add " "; print right; add ")"
  | Cond (condition, yes, no) ->
      add "(if "; print condition; add " then "; print yes;
      add " else "; print no; add ")"
  | Tuple_term values -> add "("; separated "," values; add ")"
  | Let (pattern, value, body) ->
      add "(let "; print pattern; add " = "; print value;
      add " in\n    "; print body; add ")"
  | Typed (value, typ) ->
      add "("; print value; add ":"; add (type_text typ); add ")"
  | Lambda (pattern, body) ->
      add "(\\"; print pattern; add ". "; print body; add ")"
  | Exists (pattern, body) ->
      add "(?"; print pattern; add ". "; print body; add ")"
  | Partial_word (backing, _, _) | Bounded_value (backing, _, _)
  | Shared_value (backing, _) -> print backing in
  print term;
  Buffer.contents buffer

(* The dependency report shows each interpretation as the Sail call or
   construct it replaces and the HOL term the translator emitted for it.
   That term is printed with
   - each subterm in placeholders replaced by its name: the translations
     of the call's arguments become a, b, ..., the state before the call
     s, and the state at the start of the instruction s0;
   - each let-bound variable replaced by its value;
   - a fault as "every final state" and a rejection as "no final state";
   - no type annotations.
   compare, not =, so that a subterm physically shared with an argument
   is recognised without traversing it. *)
let interpretation_text placeholders term =
  let rec schema bindings term =
    match List.find_opt (fun (value, _) -> compare value term = 0) placeholders with
    | Some (_, name) -> Atom name
    | None ->
    let go = schema bindings in
    match term with
    | Atom name -> Option.value (List.assoc_opt name bindings) ~default:term
    | Let ((Atom name | Typed (Atom name, _)), value, body) ->
        schema ((name, go value) :: bindings) body
    | Let (pattern, value, body) -> Let (pattern, go value, go body)
    | App (name, values) -> App (name, List.map go values)
    | Infix (operator, left, right) -> Infix (operator, go left, go right)
    | Cond (condition, yes, no) -> Cond (go condition, go yes, go no)
    | Tuple_term values -> Tuple_term (List.map go values)
    | Lambda (pattern, body) -> Lambda (pattern, go body)
    | Exists (pattern, body) -> Exists (pattern, go body)
    | Typed (value, _) | Partial_word (value, _, _) | Bounded_value (value, _, _)
    | Shared_value (value, _) -> go value
    | Fault -> Atom "every final state"
    | Reject -> Atom "no final state"
    | Stop state -> go state
    | Choose (_, body) -> go body
    | String_literal _ -> term in
  (* Without the parentheses around the whole term, unless it is a tuple. *)
  let term = schema [] term in
  let text = print_term term in
  let n = String.length text in
  let rec closes_at_end depth index =
    if index = n then false
    else match text.[index] with
      | '(' -> closes_at_end (depth + 1) (index + 1)
      | ')' -> if depth = 1 then index = n - 1 else closes_at_end (depth - 1) (index + 1)
      | _ -> closes_at_end depth (index + 1) in
  match term with
  | Tuple_term _ -> text
  | _ when n >= 2 && text.[0] = '(' && closes_at_end 0 0 -> String.sub text 1 (n - 2)
  | _ -> text

let record_interpretation names sail text =
  let entry = (names, sail, text) in
  if not (List.mem entry !applied_interpretations) then
    applied_interpretations := entry :: !applied_interpretations

(* A fault exits the instruction, not merely the helper or current loop.
   Loop joins bind an intermediate tuple before continuing, so replacing a
   fault by T during traversal would produce an ill-typed tuple and continue
   execution. Keep Fault until the complete relation is built, then use a
   temporary sum: INL one means fault, INR value means normal evaluation.
   A case propagates INL without entering the bound continuation. At the
   outer relation, fault is T for every candidate final state.

   Only let values need these sums; ordinary branches and arithmetic remain
   unchanged. Fault-capable helpers are inlined, so no shared state function
   can hide a non-local fault behind an ordinary return value. *)
let lower_faults expression =
  (* A fresh choice has no free-variable dependence on where it is made.
     All represented HOL types are inhabited, so binding it outside a
     branch that does not use it preserves that branch's outcomes. Hoisting
     lets choices pass loop/value joins without choosing one witness or
     duplicating a continuation. Each executed unknown call has its own
     fresh variable; repeated uses of that call's result share its variable. *)
  let choices = ref [] in
  let rec hoist = function
    | Choose (variable, body) ->
        choices := variable :: !choices; hoist body
    | Stop state -> Stop (hoist state)
    | App (name, values) -> App (name, List.map hoist values)
    | Tuple_term values -> Tuple_term (List.map hoist values)
    | Infix (op, left, right) -> Infix (op, hoist left, hoist right)
    | Cond (condition, yes, no) -> Cond (hoist condition, hoist yes, hoist no)
    | Let (pat, value, body) -> Let (pat, hoist value, hoist body)
    | Typed (value, typ) -> Typed (hoist value, typ)
    | Lambda (pat, body) -> Lambda (pat, hoist body)
    | Exists (pat, body) -> Exists (pat, hoist body)
    | Partial_word (value, width, mask) -> Partial_word (hoist value, width, mask)
    | Bounded_value (value, low, high) -> Bounded_value (hoist value, low, high)
    | Shared_value (value, facts) -> Shared_value (hoist value, hoist facts)
    | value -> value in
  let expression = hoist expression in
  let rec contains = function
    | Fault | Stop _ | Reject -> true
    | Choose _ -> assert false
    | Atom _ | String_literal _ -> false
    | App (_, values) | Tuple_term values -> List.exists contains values
    | Infix (_, left, right) | Lambda (left, right) | Exists (left, right) ->
        contains left || contains right
    | Cond (condition, yes, no) -> contains condition || contains yes || contains no
    | Let (pat, value, body) -> contains pat || contains value || contains body
    | Typed (value, _) | Partial_word (value, _, _) | Bounded_value (value, _, _) ->
        contains value
    | Shared_value (value, facts) -> contains value || contains facts in
  let rec extended = function
    | Stop _ | Reject -> true
    | App (_, values) | Tuple_term values -> List.exists extended values
    | Infix (_, left, right) | Lambda (left, right) | Exists (left, right) ->
        extended left || extended right
    | Cond (c, y, n) -> extended c || extended y || extended n
    | Let (p, v, b) -> extended p || extended v || extended b
    | Typed (v, _) | Partial_word (v, _, _) | Bounded_value (v, _, _) -> extended v
    | Shared_value (v, facts) -> extended v || extended facts
    | _ -> false in
  let extended = extended expression in
  let one = Typed (Atom "one", Unit) in
  let left value = App ("INL", [value])
  and right value = App ("INR", [value]) in
  let fault = left (if extended then left one else one) in
  let cases value early on_early pat on_normal =
    used_case_names := !case_name :: !used_case_names;
    App (!case_name, [Lambda (early, on_early);
      Lambda (pat, on_normal); value]) in
  let case value on_fault pat on_normal =
    cases value (Atom (fresh ())) on_fault pat on_normal in
  (* Preserve the original two-way fault/value encoding when it suffices.
     Otherwise the early-exit payload is unit + (state + unit):
     fault, normal early termination, or failed source assertion. *)
  let terminal value =
    if not extended then Atom "T" else
    let rest = Atom (fresh ()) and state = Atom (fresh ()) in
    cases value (Typed (Atom (fresh ()), Unit)) (Atom "T") rest
      (cases rest state (Infix ("=", state, Atom "t"))
        (Typed (Atom (fresh ()), Unit)) (Atom "F")) in
  let rec outcome = function
    | Fault -> fault
    | Stop state -> left (right (left state))
    | Reject -> left (right (right one))
    | Let (pat, value, body) when contains value ->
        if not extended then case (outcome value) fault pat (outcome body)
        else let early = Atom (fresh ()) in
          cases (outcome value) early (left early) pat (outcome body)
    | Let (pat, value, body) -> Let (pat, value, outcome body)
    | Cond (condition, yes, no) ->
        Cond (condition, outcome yes, outcome no)
    | value when not (contains value) -> App ("INR", [value])
    | _ -> fail Parse_ast.Unknown "architectural fault in an unsupported value position"
  and relation = function
    | Fault -> Atom "T"
    | Stop state -> Infix ("=", state, Atom "t")
    | Reject -> Atom "F"
    | Let (pat, value, body) when contains value ->
        if not extended then case (outcome value) (Atom "T") pat (relation body)
        else let early = Atom (fresh ()) in
          cases (outcome value) early (terminal early) pat (relation body)
    | Let (pat, value, body) -> Let (pat, value, relation body)
    | Cond (condition, yes, no) ->
        Cond (condition, relation yes, relation no)
    | Infix ("/\\", condition, body) when not (contains condition) ->
        (* RV32 assertion guards precede their continuation. An abort in
           that continuation rejects the guarded path, not the other paths
           of the enclosing instruction. Retain the guard unchanged. *)
        Infix ("/\\", condition, relation body)
    | value when not (contains value) -> value
    | term ->
        fail Parse_ast.Unknown "architectural fault in an unsupported relation position"
  in List.fold_left (fun body variable -> Exists (variable, body))
    (relation expression) !choices

(* Map a checked source type to its supported HOL representation. Use Sail
   to expand synonyms and inspect declarations; standard named types and
   architecture projections also have explicit cases below.
   Numeric/refined types share HOL int/bool internally;
   callers must retain their source constraints when using them.

   Architecture projections are deliberate exceptions: RV regidx becomes a
   five-bit field; state mode projects ExecutionResult to unit; retirement
   keeps tags but omits exception payloads; Arm ProcState retains only named
   fields. Such omissions are justified only
   by the stated observation boundary, not by a type-isomorphism proof.
   observes_projected_payload blocks operations that could distinguish values
   using omitted information. Unknown/unsupported types fail. *)
let rec hol_type ctx env typ =
  match Type_check.destruct_bitvector env typ with
  | Some n ->
      let width = try Some (number ctx n)
        with Reporting.Fatal_error _ when generic_widths_active () -> None
           | Reporting.Fatal_error _ when !state_computation -> None in
      (* Internal tables can exceed architectural register widths: TBL3
         concatenates 384 bits and AES uses packed 2048-bit byte tables.
         This bound does not widen X_read/V_read or register-write contracts. *)
      (match width with
       | None when generic_widths_active () -> Poly_word (poly_dimension env n)
       | None -> Dynamic_bits
       | Some width ->
           if width < 0 || width > 2048 then
             fail (typ_loc typ) "only bitvector widths 0 through 2048 are supported";
           if width = 0 then Empty_bits else Word width)
  | None ->
      let typ = Type_check.Env.base_typ_of env typ in
      match typ with
      | Typ_aux (Typ_tuple ts, _) -> Tuple (List.map (hol_type ctx env) ts)
      | Typ_aux (Typ_exist (_, _, t), _) -> hol_type ctx env t
      | Typ_aux (Typ_app (id, [A_aux (A_typ ok, _); A_aux (A_typ err, _)]), _)
          when string_of_id id = "result" ->
          used_results := true;
          used_case_names := !case_name :: !used_case_names;
          Result (hol_type ctx env ok, hol_type ctx env err)
      | Typ_aux (Typ_app (id, [A_aux (A_typ payload, _)]), _)
          when string_of_id id = "option" ->
          used_results := true;
          used_case_names := !case_name :: !used_case_names;
          Option_type (hol_type ctx env payload)
      | _ when Option.is_some (Type_check.destruct_numeric typ) -> Int
      | Typ_aux (Typ_id id, _) when string_of_id id = "unit" -> Unit
      | Typ_aux (Typ_id id, _) when string_of_id id = "string" -> String_type
      | Typ_aux (Typ_id id, _) when Type_check.Env.is_enum id env ->
          let name = string_of_id id in
          used_enums := (name, Type_check.Env.get_enum id env) :: !used_enums;
          Enum name
      | Typ_aux (Typ_id id, _) when Type_check.Env.is_variant id env ->
          let quant, _ = Bindings.find id (Type_check.Env.get_variants env) in
          if fst (quant_split quant) <> [] then
            fail (typ_loc typ) "only monomorphic unit-payload variants are supported";
          let fields = Type_check.instantiate_variant env id [] in
          let name = string_of_id id in
          if !upstream_architecture = Some "rv32" && name = "regidx" then begin
            match fields with
            | [(constructor, payload)] when string_of_id constructor = "Regidx" &&
                  hol_type ctx env payload = Word 5 -> Word 5
            | _ -> fail (typ_loc typ) "upstream RV32 regidx requires Regidx(bits(5))"
          end else if !upstream_architecture = Some "rv32" &&
                      name = "ExecutionResult" && !state_computation then
            Unit
          else if not (!upstream_architecture = Some "rv32" &&
                  List.mem name ["ExecutionResult"; "ExceptionType"]) &&
              List.length fields = 2 &&
              List.exists (fun (_, payload) -> hol_type ctx env payload <> Unit) fields then begin
            (* A two-constructor, monomorphic union is exactly a HOL sum.
               Keep both payloads and declaration order; unlike the RV32
               completion projection above, no information is discarded. *)
            used_results := true;
            used_case_names := !case_name :: !used_case_names;
            match fields with
            | [(left, a); (right, b)] ->
                Binary_variant ((string_of_id left, hol_type ctx env a),
                  (string_of_id right, hol_type ctx env b))
            | _ -> assert false
          end else begin
            (* Exception payloads are not observed by a normal-retirement
               relation. Constructor identity remains observable, and
               constructing a projected value must still evaluate its
               arguments through the computation path. *)
            if not (!upstream_architecture = Some "rv32" &&
                    List.mem name ["ExecutionResult"; "ExceptionType"]) then
              List.iter (fun (_, payload) ->
                if hol_type ctx env payload <> Unit then
                  fail (typ_loc payload) "only unit payloads are supported in named variants"
              ) fields;
            let members = List.map fst fields in
            used_enums := (name, members) :: !used_enums;
            Unit_variant (name, members)
          end
      | Typ_aux (Typ_id id, _) when Type_check.Env.is_record id env ->
          let quant, fields = Type_check.Env.get_record id env in
          if fst (quant_split quant) <> [] || fields = [] then
            fail (typ_loc typ) "only nonempty monomorphic records are supported";
          let fields =
            if !upstream_architecture = Some "aarch64" &&
               string_of_id id = "ProcState" then begin
              let find name = match List.find_opt
                (fun (_, field) -> string_of_id field = name) fields with
                | Some field -> field
                | None -> fail (typ_loc typ) ("upstream ProcState lacks " ^ name) in
              List.map find Arm.pstate_fields
            end else if !upstream_architecture = Some "rv32" &&
               string_of_id id = "ExceptionContext" then begin
              let find name = match List.find_opt
                (fun (_, field) -> string_of_id field = name) fields with
                | Some field -> field
                | None -> fail (typ_loc typ) ("upstream ExceptionContext lacks " ^ name) in
              [find "trap"; find "excinfo"]
            end else fields in
          Record (List.map (fun (typ, id) -> string_of_id id, hol_type ctx env typ) fields)
      | _ when Option.is_some (Type_check.destruct_atom_bool env typ) -> Bool
      | _ when Option.is_some (Type_check.destruct_boolean typ) -> Bool
      | _ -> fail (typ_loc typ) ("unsupported type " ^ string_of_typ typ)

let exp_type ctx exp = hol_type ctx (Type_check.env_of exp) (Type_check.typ_of exp)

(* Detect omitted information even inside a tuple/record/variant container.
   Equality or constructing an arbitrary projected record would expose more
   source information than its HOL view keeps. Those operations must reject,
   rather than become an equality/construction on a silently smaller value. *)
let observes_projected_payload env typ =
  let projected id = match !upstream_architecture with
    | Some "rv32" ->
        List.mem (string_of_id id) ["ExecutionResult"; "ExceptionType"; "ExceptionContext"]
    | Some "aarch64" -> string_of_id id = "ProcState"
    | _ -> false in
  let rec visit seen typ =
    let named id arguments =
      projected id ||
      List.exists (function A_aux (A_typ typ, _) -> visit seen typ | _ -> false) arguments ||
      (not (IdSet.mem id seen) &&
       let seen = IdSet.add id seen in
       if Type_check.Env.is_record id env then
         List.exists (fun (field, _) -> visit seen field)
           (snd (Type_check.Env.get_record id env))
       else if Type_check.Env.is_variant id env then
         List.exists (fun (_, payload) -> visit seen payload)
           (Type_check.instantiate_variant env id arguments)
       else false) in
    match Type_check.Env.base_typ_of env typ with
    | Typ_aux (Typ_id id, _) -> named id []
    | Typ_aux (Typ_tuple types, _) -> List.exists (visit seen) types
    | Typ_aux (Typ_exist (_, _, typ), _) -> visit seen typ
    | Typ_aux (Typ_app (id, arguments), _) -> named id arguments
    | _ -> false in
  visit IdSet.empty typ
let nat n = Atom (string_of_int n)
let integer n =
  if Nat_big_num.less n Nat_big_num.zero then
    App ("--", [App ("&", [Atom (Nat_big_num.to_string (Nat_big_num.negate n))])])
  else App ("&", [Atom (Nat_big_num.to_string n)])

let word_dimension = function
  | Word n -> nat n
  | Poly_word dimension -> Atom ("(dimindex(:" ^ dimension ^ "))")
  | _ -> fail Parse_ast.Unknown "expected a nonempty word dimension"

let is_word = function Word _ | Poly_word _ -> true | _ -> false
let is_poly_word = function Poly_word _ -> true | _ -> false

let rec numeric_type_term widths env (Nexp_aux (aux, loc) as expression) =
  try integer (Nat_big_num.of_int (number widths expression)) with
  | Reporting.Fatal_error _ ->
      match aux with
      | Nexp_var kid ->
          (match poly_variable env kid with
           | Some dimension -> App ("&", [Atom ("(dimindex(:" ^ dimension ^ "))")])
           | None -> fail loc ("unbound numeric type expression " ^ string_of_nexp expression))
      | Nexp_sum (left, right) ->
          Infix ("+", numeric_type_term widths env left, numeric_type_term widths env right)
      | Nexp_minus (left, right) ->
          Infix ("-", numeric_type_term widths env left, numeric_type_term widths env right)
      | Nexp_times (left, right) ->
          Infix ("*", numeric_type_term widths env left, numeric_type_term widths env right)
      | _ -> fail loc ("unsupported generic sizeof " ^ string_of_nexp expression)

(* Translate a source binding pattern and extend the local-name environment.
   A tuple pattern binds all its elements; a type annotation gives the emitted
   HOL parameter its concrete representation. This is binding syntax, not
   source matching/evaluation; match clauses have separate translators below. *)
let rec pattern ctx env (P_aux (aux, (loc, _)) as pat) =
  match aux with
  | P_typ (_, p) | P_var (p, _) -> pattern ctx env p
  | P_id id ->
      let name = fresh () in
      Typed (Atom name, hol_type ctx (Type_check.env_of_pat pat) (Type_check.typ_of_pat pat)),
      (string_of_id id, Atom name) :: env
  | P_tuple ps ->
      let ps, env = List.fold_left (fun (ps, env) p ->
        let p, env = pattern ctx env p in ps @ [p], env
      ) ([], env) ps in
      Tuple_term ps, env
  | P_lit (L_aux (L_unit, _)) -> Typed (Atom "unit_arg", Unit), env
  | P_wild -> Typed (Atom (fresh ()),
                    hol_type ctx (Type_check.env_of_pat pat) (Type_check.typ_of_pat pat)), env
  | _ -> fail loc "unsupported binding pattern"

let root_of_def = function
  | DEF_aux (DEF_fundef (FD_aux (FD_function (_, _, clauses), _)), _) ->
      (match clauses with
       | FCL_aux (FCL_funcl (id, _), _) :: _ -> Some (string_of_id id)
       | [] -> None)
  | _ -> None

(* Preserve the original source, not a pretty-printed reconstruction of the
   checked tree. Locations still refer to the external input after Sail's
   transformations. Val declarations record the source preconditions;
   function declarations show the calculation being translated.

   Checkout-relative filenames make output independent of checkout paths.
   OCaml quoted strings inside comments protect arbitrary Sail text from
   OCaml comment delimiters and unmatched quotes without altering its bytes. *)
let source_filename path =
  let prefixes = [
    "SAIL_ARM_DIR", "sail-arm"; "SAIL_RISCV_DIR", "sail-riscv";
    "SAIL_X86_SHINA_DIR", "sail-x86"; "SAIL_X86_REMS_DIR", "sail-x86-from-acl2";
    "SAIL_DIR", "sail"
  ] in
  match List.find_map (fun (variable, label) ->
    Option.bind (Sys.getenv_opt variable) (fun directory ->
      let prefix = Filename.concat directory "" in
      let length = String.length prefix in
      if String.length path >= length && String.sub path 0 length = prefix then
        Some (label ^ "/" ^ String.sub path length (String.length path - length))
      else None)) prefixes with
  | Some path -> path
  | None -> path

(* Quote text as an OCaml quoted string, {name|...|name}, so that a comment
   containing it ends only where intended. The name is extended until the
   text cannot close it early. *)
let quoted_text prefix text =
  let rec delimiter suffix =
    let name = prefix ^ String.make suffix 'x' in
    let close = "|" ^ name ^ "}" in
    let rec contains offset =
      offset + String.length close <= String.length text &&
      (String.sub text offset (String.length close) = close ||
       contains (offset + 1)) in
    if contains 0 then delimiter (suffix + 1) else name in
  let delimiter = delimiter 0 in
  "{" ^ delimiter ^ "|" ^ text ^ "|" ^ delimiter ^ "}"

(* By default a model names each Sail source it came from by path:line.
   --hol-light-quote-sources also copies the source text into the model. *)
let quote_sources = ref false

let source_comment label loc =
  match Reporting.simp_loc loc with
  | None -> ""
  | Some (first, _) when first.pos_fname = Sail_file.dummy -> ""
  | Some (first, last) ->
      let path = Sail_file.Path.to_string (Sail_file.to_path first.pos_fname) in
      let length = String.length (Sail_file.contents first.pos_fname) in
      if first.pos_fname <> last.pos_fname || first.pos_cnum < 0 ||
         last.pos_cnum < first.pos_cnum || last.pos_cnum > length then
        fail loc (Printf.sprintf "invalid original source range for %s: %s:%d-%d (file length %d)"
          label path first.pos_cnum last.pos_cnum length);
      let reference = source_filename path ^ ":" ^ string_of_int first.pos_lnum in
      if not !quote_sources then Printf.sprintf "(* Sail source %S, %S *)\n" label reference
      else
        let text = Reporting.loc_range_to_src first last in
        Printf.sprintf "(* Sail source %S, %S\n%s\n*)\n"
          label reference (quoted_text "sail_source" text)

(* The instruction-table entry that defines a root, printed before its
   definition so that the selected function, its fixed arguments and the
   operand order can be checked in the model itself. hol_arguments are the
   printed HOL parameters after any register components, in entry order. *)
let entry_comment (entry : Entry.t) hol_arguments =
  let call = Printf.sprintf "%s(%s) = %s" entry.Entry.name
    (String.concat ", " (List.map (fun (name, typ) ->
       name ^ " : " ^ string_of_typ typ) entry.Entry.parameters))
    (string_of_exp entry.Entry.body) in
  let variable printed =
    match String.index_opt printed ':' with
    | Some colon when String.length printed > 1 && printed.[0] = '(' ->
        String.sub printed 1 (colon - 1)
    | _ -> printed in
  let names = List.map fst entry.Entry.parameters in
  if List.length names <> List.length hol_arguments then
    fail Parse_ast.Unknown ("root " ^ entry.Entry.name ^
      " has a different number of HOL and entry parameters");
  let mapping =
    if names = [] then ""
    else "HOL parameters: " ^ String.concat ", " (List.map2 (fun hol name ->
      variable hol ^ " is " ^ name) hol_arguments names) ^ ".\n" in
  Printf.sprintf "(* Selected Sail call, from the instruction table:\n%s\n%s*)\n"
    (quoted_text "sail_entry" call) mapping

(* A split execute function can inherit the scattered declaration's location
   in a different file. Prefer a location covering its actual clause/body,
   rather than printing the declaration again in place of the calculation. *)
let function_source_location definition =
  let covers outer inner =
    match Reporting.simp_loc outer, Reporting.simp_loc inner with
    | Some (first, last), Some (body_first, body_last) ->
        first.pos_fname = body_first.pos_fname &&
        first.pos_cnum <= body_first.pos_cnum &&
        last.pos_cnum >= body_last.pos_cnum
    | _ -> false in
  (* A split clause's own location can miss its body. Its parameter
     pattern still points at the upstream clause head, so start the quote
     there to keep the parameter order visible. *)
  let from_pattern pattern body =
    match Reporting.simp_loc (pat_loc pattern), Reporting.simp_loc body with
    | Some (first, _), Some (body_first, body_last)
      when first.pos_fname = body_first.pos_fname &&
           first.pos_cnum < body_first.pos_cnum ->
        Parse_ast.Range (first, body_last)
    | _ -> body in
  match definition with
  | DEF_aux (DEF_fundef (FD_aux (FD_function (_, _, [
      FCL_aux (FCL_funcl (_, Pat_aux (Pat_exp (pattern, body), _)), (clause, _))
    ]), _)), _) ->
      let location = def_loc definition and body = exp_loc body in
      if covers location body then location
      else if covers clause.loc body then clause.loc
      else from_pattern pattern body
  | _ -> def_loc definition

let rec global_name = function
  | P_aux (P_id id, _) -> Some (string_of_id id)
  | P_aux ((P_typ (_, pat) | P_var (pat, _)), _) -> global_name pat
  | _ -> None

let definition_source_comments definitions names =
  (* Sail generates bitfield constructors/accessors; they have no original
     function text. Their checked signatures name the record whose original
     bitfield declaration specifies the layout. Print that declaration as
     the origin, rather than reading the compiler's dummy string location
     or presenting generated function text as upstream source. *)
  let type_origins name =
    let types = List.fold_left (fun types -> function
      | DEF_aux (DEF_val (VS_aux (VS_val_spec (
          TypSchm_aux (TypSchm_ts (_, typ), _), id, _), _)), _)
          when string_of_id id = name -> IdSet.union types (ids_of_typ typ)
      | _ -> types) IdSet.empty definitions in
    List.filter_map (function
      | DEF_aux (DEF_type type_definition, _) as definition
          when IdSet.mem (id_of_type_def type_definition) types ->
          Some (source_comment
            (name ^ " generated from type " ^
             string_of_id (id_of_type_def type_definition))
            (def_loc definition))
      | _ -> None) definitions |> String.concat "" in
  let originals = List.sort_uniq String.compare names |> List.concat_map (fun name ->
    List.filter_map (function
      | DEF_aux (DEF_val (VS_aux (VS_val_spec (_, id, _), _)), _) as definition
          when string_of_id id = name ->
          Some (source_comment (name ^ " declaration") (def_loc definition))
      | DEF_aux (DEF_fundef _, _) as definition
          when root_of_def definition = Some name ->
          let text = source_comment name (function_source_location definition) in
          Some (if text = "" then type_origins name else text)
      | DEF_aux (DEF_let (pattern, _), _) as definition
          when global_name pattern = Some name ->
          Some (source_comment (name ^ " global") (def_loc definition))
      | _ -> None) definitions) |> String.concat "" in
  let boundaries = List.filter_map (fun boundary ->
    let lift = boundary.Entry.lift in
    if List.mem (Entry.lifted_name lift) names then
      let selection = match lift.Entry.fixed_arguments with
        | [] -> ""
        | _ -> Printf.sprintf
            "(* Fixed source arguments: %s in %s.\n   Checked integer or fixed-width bit literals replace these parameters,\n   which are removed from the derived signature. Only numeric patterns\n   and closed comparison/Boolean guards select a branch; the selected\n   instruction body is retained. *)\n"
            (Entry.selection_text lift) lift.Entry.source_function in
      let input_source = match boundary.Entry.caller with
        | None -> lift.Entry.source_function
        | Some _ -> Option.value ~default:lift.Entry.source_function
            lift.Entry.through in
      let retained = match boundary.Entry.caller with
        | None -> ""
        | Some caller -> Printf.sprintf
            "(* Retained helper call in %s: %S.\n   Redirected to %s with the original arguments followed by supplied inputs.\n   Argument evaluation and the helper's remaining body are retained. *)\n"
            lift.Entry.source_function
            (string_of_exp caller.Entry.caller_call) caller.Entry.derived_child in
      let description = match boundary.Entry.fixed_binding, boundary.Entry.slots with
        | None, [slot] -> Printf.sprintf
            "(* Source input boundary: %s input %d, parameter %s, replaces\n   one %s call in %s. Its effects are outside this relation;\n   all remaining source statements are retained and rechecked by Sail. *)\n"
            (Entry.lifted_name lift) slot.Entry.input_index
            slot.Entry.parameter lift.Entry.input_function input_source
        | Some fixed, slots ->
            let remaining = List.map (fun slot -> Printf.sprintf
              "input %d %s : %s" slot.Entry.input_index slot.Entry.parameter
              (string_of_typ slot.Entry.input_type)) slots |> String.concat ", " in
            Printf.sprintf
              "(* Acquired source input boundary in %s: %S.\n   Fix %s : %s to %S; supplied fields: %s.\n   The original immutable let and tuple shape remain. The excluded call's\n   effects are outside this relation; all other statements are rechecked. *)\n"
              input_source (string_of_exp boundary.Entry.call) fixed.Entry.binding
              (string_of_typ fixed.Entry.binding_type) (string_of_exp fixed.Entry.value)
              (if remaining = "" then "none" else remaining)
        | _ -> assert false in
      Some (selection ^ description ^ retained)
    else None) !input_boundaries |> String.concat "" in
  originals ^ boundaries

let input_location_text location =
  match Reporting.simp_loc location with
    | Some (first, last) ->
        source_filename (Sail_file.Path.to_string (Sail_file.to_path first.pos_fname)) ^
        Printf.sprintf ":%d:%d-%d:%d" first.pos_lnum
          (first.pos_cnum - first.pos_bol + 1) last.pos_lnum
          (last.pos_cnum - last.pos_bol + 1)
    | None -> "unknown source location"

let assertion_text condition =
  string_of_exp (Type_check.strip_exp condition) ^ " at " ^
  input_location_text (exp_loc condition)

(* file:line of a location. *)
let short_location location =
  match String.split_on_char ':' (input_location_text location) with
  | file :: line :: _ -> file ^ ":" ^ line
  | _ -> input_location_text location

(* The source text of an expression on one line, or its printed syntax if
   the source is not available. *)
let source_text exp =
  let printed () = string_of_exp (Type_check.strip_exp exp) in
  match Reporting.simp_loc (exp_loc exp) with
  | Some (first, last) when first.pos_fname = last.pos_fname ->
      (try
         let text = Reporting.loc_range_to_src first last in
         String.concat " " (List.filter (fun word -> word <> "")
           (String.split_on_char ' '
              (String.map (function '\n' | '\t' | '\r' -> ' ' | c -> c) text)))
       with _ -> printed ())
  | _ -> printed ()

let input_boundary_text boundary =
  let lift = boundary.Entry.lift in
  let selection = match lift.Entry.fixed_arguments with
    | [] -> ""
    | _ -> " (fix " ^ Entry.selection_text lift ^ " in " ^
           lift.Entry.source_function ^ ")" in
  let location = input_location_text boundary.Entry.location in
  let specialized = match boundary.Entry.specialized_call with
    | None -> ""
    | Some call -> " (specialized call: " ^ string_of_exp call ^ ")" in
  let caller = match boundary.Entry.caller with
    | None -> ""
    | Some caller ->
        let selected = match caller.Entry.caller_specialized_call with
          | None -> ""
          | Some call -> " (selected call: " ^ string_of_exp call ^ ")" in
        let forwarded = List.filter_map (fun slot ->
          Option.map string_of_int slot.Entry.forwarded_index)
          boundary.Entry.slots |> String.concat "," in
        Printf.sprintf " (retained caller: %s%s at %s -> %s, input %s)"
          (string_of_exp caller.Entry.caller_call) selected
          (input_location_text caller.Entry.caller_location)
          caller.Entry.derived_child forwarded in
  let slots = match boundary.Entry.fixed_binding, boundary.Entry.slots with
    | None, [slot] -> Printf.sprintf "input %d, parameter %s"
        slot.Entry.input_index slot.Entry.parameter
    | Some fixed, slots ->
        let path indexes = match indexes with
          | [] -> "result"
          | indexes -> "result." ^ String.concat "." (List.map string_of_int indexes) in
        let fixed = Printf.sprintf "fix %s (%s) : %s = %s"
          fixed.Entry.binding (path fixed.Entry.binding_path)
          (string_of_typ fixed.Entry.binding_type) (string_of_exp fixed.Entry.value) in
        let supplied = List.map (fun slot -> Printf.sprintf
          "input %d, parameter %s (%s) : %s" slot.Entry.input_index
          slot.Entry.parameter (path slot.Entry.result_path)
          (string_of_typ slot.Entry.input_type)) slots in
        String.concat "; " (fixed :: supplied)
    | _ -> assert false in
  let replacement = match boundary.Entry.replacement with
    | None -> ""
    | Some replacement -> " (replacement: " ^ string_of_exp replacement ^ ")" in
  Printf.sprintf "%s%s [%s] <- %s%s at %s : %s%s%s"
    (Entry.lifted_name lift) selection slots (string_of_exp boundary.Entry.call)
    specialized location (string_of_typ boundary.Entry.input_type) caller
    replacement

(* Supported function bodies have one unguarded clause. Sail split rewrites
   the RISC-V execute dispatch into such callable functions. If a reachable
   definition still has unsupported clauses, it cannot fall back to a
   primitive interpretation just because its name resembles a known helper. *)
let function_clause loc def =
  match def with
  | DEF_aux (DEF_fundef (FD_aux (FD_function (_, _, [
      FCL_aux (FCL_funcl (_, Pat_aux (Pat_exp (pat, body), _)), _)
    ]), _)), _) -> pat, body
  | _ -> fail loc "only single, unguarded function clauses are supported"

let has_source_return expression =
  let found = ref false in
  ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with
    e_return = (fun value -> found := true; E_return value)} expression);
  !found

(* Translation environment for one point in the source computation.
   state advances after writes; entry_state preserves the instruction address.
   locals holds translated bindings (including mutable ones), while widths
   and numeric_facts describe the currently scoped type/numeric information.
   stack checks recursion and rejects unsupported cycles. Tracking survives
   transfers and scope changes until an actual observation is checked. *)
type context = {
  widths : (string * int) list;
  numeric_facts : n_constraint list;
  locals : (string * term) list;
  functions : (string * Type_check.tannot exp * Type_check.tannot pat) list;
  globals : (string * Type_check.tannot exp) list;
  stack : string list;
  state : term option;
  entry_state : term option;
  mutable_locals : string list;
  uninitialized : string list;
}

(* The functions through which translation reached the current point,
   root first. *)
let decision_context ctx = String.concat " > " (List.rev ctx.stack)

let record_selected_branch ctx condition truth ~by_z3 =
  selected_branches :=
    (input_location_text (exp_loc condition), truth,
     source_text condition, decision_context ctx,
     by_z3) :: !selected_branches

(* assertion is the whole assert(...) expression. *)
let record_proved_assertion ctx assertion condition ~by_z3 =
  proved_assertions :=
    (assertion_text condition, source_text assertion, short_location (exp_loc assertion),
     decision_context ctx, by_z3) :: !proved_assertions

(* The state before the current point is s; the state at the start of the
   instruction, where it differs, is s0. *)
let state_placeholders ctx =
  (match ctx.state with Some state -> [state, "s"] | None -> []) @
  (match ctx.entry_state with
   | Some entry when Some entry <> ctx.state -> [entry, "s0"]
   | _ -> [])

(* An interpretation that gives a value. *)
let record_value ctx names sail placeholders value =
  record_interpretation names sail
    (interpretation_text (placeholders @ state_placeholders ctx) value)

(* An interpretation that changes the state, with its result if it has
   one. *)
let record_update ctx names sail placeholders ?result update =
  let text = interpretation_text (placeholders @ state_placeholders ctx) in
  record_interpretation names sail
    ("s' = " ^ text update ^
     match result with Some value -> ", returning " ^ text value | None -> "")

(* Validate the entire configuration before selecting source dependencies.
   Use genuine enum membership, register declarations and field types, not
   names alone. One-bit fields become word literals; capabilities become
   Boolean query results. Duplicate facts are refused even when equal.
   This checks the representation, not every architectural validity rule:
   source assertions must still be proved or retained as outcome guards. *)
let validate_assumptions env facts =
  let seen = ref [] in
  List.iter (fun fact ->
    let key = assumption_key fact in
    if List.mem key !seen then fail Parse_ast.Unknown ("duplicate assumption: " ^ key);
    seen := key :: !seen;
    match fact with
    | Entry.Feature (name, value) ->
        if not (Type_check.Env.is_enum (mk_id "Feature") env) ||
           not (List.exists (fun id -> string_of_id id = name)
             (Type_check.Env.get_enum (mk_id "Feature") env)) then
          fail Parse_ast.Unknown ("assumed feature is not in Sail's Feature enum: " ^ name);
        let _, signature = Type_check.Env.get_val_spec_orig
          (mk_id "IsFeatureImplemented") env in
        (match signature with
         | Typ_aux (Typ_fn ([argument], result), _) when
             hol_type [] env argument = Enum "Feature" && hol_type [] env result = Bool &&
             Option.is_none (Type_check.destruct_atom_bool env result) -> ()
         | _ -> fail Parse_ast.Unknown "feature assumptions require Feature -> bool");
        if name = "FEAT_GCS" && value then
          fail Parse_ast.Unknown "FEAT_GCS=true conflicts with the disabled GCS contract"
    | Entry.Initial_bit (register, field, _) ->
        let id = mk_id register in
        if not (Type_check.Env.is_register id env) then
          fail Parse_ast.Unknown ("assumed initial bit requires a source register: " ^ register);
        let declared = Type_check.Env.base_typ_of env (Type_check.Env.get_register id env) in
        let fields = match declared with
          | Typ_aux (Typ_id record, _) when Type_check.Env.is_record record env ->
              snd (Type_check.Env.get_record record env)
          | _ -> fail Parse_ast.Unknown ("assumed initial bit requires a record register: " ^ register) in
        (match List.find_opt (fun (_, id) -> string_of_id id = field) fields with
        | Some (typ, _) when hol_type [] env typ = Word 1 -> ()
        | _ -> fail Parse_ast.Unknown ("assumed initial field requires bits(1): " ^ register ^ "." ^ field))
    | Entry.Initial_bool (register, _) ->
        let id = mk_id register in
        if not (Type_check.Env.is_register id env) then
          fail Parse_ast.Unknown ("assumed Boolean requires a source register: " ^ register);
        let declared = Type_check.Env.base_typ_of env (Type_check.Env.get_register id env) in
        (* HOL's Bool view also accepts some existential/refined source
           types. A configured truth value must not contradict those source
           refinements, so accept only the expanded ordinary bool type. *)
        (match declared with
         | Typ_aux (Typ_id id, _) when Id.compare id (mk_id "bool") = 0 -> ()
         | _ -> fail Parse_ast.Unknown ("assumed Boolean requires bool: " ^ register))
    | Entry.Initial_enum (register, constructor) ->
        let id = mk_id register in
        if not (Type_check.Env.is_register id env) then
          fail Parse_ast.Unknown ("assumed enum requires a source register: " ^ register);
        let declared = Type_check.Env.base_typ_of env (Type_check.Env.get_register id env) in
        (match declared with
         | Typ_aux (Typ_id enum, _) when Type_check.Env.is_enum enum env &&
             List.exists (fun id -> string_of_id id = constructor)
               (Type_check.Env.get_enum enum env) -> ()
         | _ -> fail Parse_ast.Unknown
             ("assumed constructor is not in the source register's enum: " ^
              register ^ "=" ^ constructor))
  ) facts;
  List.sort compare facts

let assumed_initial_bit ctx env register field =
  if List.mem_assoc (string_of_id register) ctx.locals ||
     not (Type_check.Env.is_register register env) then None else
  List.find_opt (function
    | Entry.Initial_bit (r, f, _) ->
        r = string_of_id register && f = string_of_id field
    | _ -> false) !configured_assumptions

let assumed_bit_value ctx env register field =
  Option.map (function
    | Entry.Initial_bit (_, _, value) as fact ->
        used_assumptions := fact :: !used_assumptions;
        Typed (App ("word", [nat (if value then 1 else 0)]), Word 1)
    | _ -> assert false) (assumed_initial_bit ctx env register field)

let assumed_register_value ctx env register =
  if List.mem_assoc (string_of_id register) ctx.locals ||
     not (Type_check.Env.is_register register env) then None else
  List.find_map (function
    | Entry.Initial_enum (name, constructor) as fact
        when name = string_of_id register ->
        used_assumptions := fact :: !used_assumptions;
        Some (Atom (ctor_symbol constructor))
    | Entry.Initial_bool (name, value) as fact
        when name = string_of_id register ->
        used_assumptions := fact :: !used_assumptions;
        Some (Atom (if value then "T" else "F"))
    | _ -> None) !configured_assumptions

(* Facts describe the instruction's input, not permanent replacement state.
   Until fact invalidation is implemented, refuse any reachable write to an
   assumed field, its whole container, or FeatureImpl when capabilities are
   fixed. Apply the check to every assignment, including in helper bodies,
   tuple/range targets and writes before the first assumed read. Local names
   shadowing source registers do not acquire architectural assumptions. *)
let check_assumed_write ctx env lexp =
  let check loc id field =
    if Type_check.Env.is_register id env &&
       not (List.mem_assoc (string_of_id id) ctx.locals) then
      List.iter (fun fact ->
        let invalidates = match fact with
          | Entry.Feature _ -> string_of_id id = "FeatureImpl"
          | Entry.Initial_bit (register, assumed, _) ->
              register = string_of_id id &&
              (field = None || field = Some assumed)
          | Entry.Initial_enum (register, _)
          | Entry.Initial_bool (register, _) -> register = string_of_id id in
        if invalidates then fail loc
          ("write may invalidate source assumption: " ^ assumption_text fact)
      ) !configured_assumptions in
  let rec target field (LE_aux (aux, (loc, _))) = match aux with
    | LE_id id | LE_typ (_, id) -> check loc id field
    | LE_field (base, name) -> target (Some (string_of_id name)) base
    | LE_vector (base, _) | LE_vector_range (base, _, _) -> target field base
    | LE_tuple bases | LE_vector_concat bases -> List.iter (target field) bases
    | _ -> () in
  target None lexp

(* Shared functions are inferred from checked source patterns. A pure call
   returns its value; a state call returns (value, final_state), with the
   instruction-entry state passed separately to preserve frozen-PC reads.
   The callback is installed after both value and state translators exist.
   No request enumerates these HOL parameters. *)
type shared_call = { expression : term; returns_state : bool }
type shared_function = {
  request : Entry.function_request;
  constant : string;
  arguments : int list;
  registers : (string * htyp) list;
  returns_state : bool;
  sources : string list;
  text : string;
  assumptions : Entry.assumption list;
}
let shared_functions : (string * shared_function) list ref = ref []
let shared_failures : (string * string) list ref = ref []
let shared_decisions : string list ref = ref []
let shared_namespace = ref ""
let source_definitions : Type_check.typed_def list ref = ref []
let computing_shared_facts = ref false
let share_source_function :
    (context -> Type_check.tannot exp -> id -> Type_check.tannot exp ->
     Type_check.tannot pat -> Type_check.tannot exp list -> shared_call option) ref =
  ref (fun _ _ _ _ _ _ -> None)

let translation_checkpoint () =
  let save reference =
    let value = !reference in fun () -> reference := value in
  let restore = [
    save fresh_index; save loop_budget; save value_recursion_budget;
    save used_primitives; save used_functions; save used_globals;
    save used_registers; save contract_registers; save used_enums;
    save used_results; save used_case_names; save proved_assertions;
    save guarded_assertions; save disabled_extensions; save used_mappings;
    save unobserved_undefined; save proved_numeric_arguments; save successful_checks;
    save unrolled_loops; save selected_branches; save applied_interpretations;
    save definition_sources;
    save shared_functions;
    save used_assumptions; save artifact_assumptions;
    save shared_failures; save shared_decisions; save poly_dimensions;
    save poly_width_expressions; save poly_fixed_arguments
  ] in
  fun () -> List.iter (fun restore -> restore ()) restore

let restore_scope outer inner =
  {inner with
   locals = List.map (fun (name, value) ->
     if List.mem name outer.mutable_locals then
       name, Option.value (List.assoc_opt name inner.locals) ~default:value
     else name, value) outer.locals @
     List.filter (fun (name, _) -> List.mem name outer.uninitialized &&
       not (List.mem_assoc name outer.locals)) inner.locals;
   mutable_locals = outer.mutable_locals;
   uninitialized = List.filter (fun name -> List.mem name inner.uninitialized)
                    outer.uninitialized}

let rec pattern_names (P_aux (aux, _)) =
  match aux with
  | P_id id -> [string_of_id id]
  | P_typ (_, pat) | P_var (pat, _) -> pattern_names pat
  | P_tuple pats -> List.concat_map pattern_names pats
  | _ -> []

(* A match clause binds its names only for the clause body: a binder of an
   outer mutable local would replace that local's value after the clause
   (see restore_scope). Widths and numeric facts are keyed by type-variable
   name, so a pattern such as y as int('n) would inherit an outer 'n's facts.
   Refuse both. *)
let check_clause_patterns ctx clauses =
  let rec type_variable (P_aux (aux, _)) = match aux with
    | P_var _ -> true
    | P_typ (_, pat) | P_as (pat, _) -> type_variable pat
    | P_app (_, pats) | P_tuple pats | P_vector pats -> List.exists type_variable pats
    | _ -> false in
  List.iter (fun clause ->
    let pat, _, _, _ = destruct_pexp clause in
    if IdSet.exists (fun id -> List.mem (string_of_id id) ctx.mutable_locals) (pat_ids pat) then
      fail (pat_loc pat) "a match pattern cannot bind the name of a mutable local";
    if type_variable pat then
      fail (pat_loc pat) "type-variable patterns in match clauses are unsupported") clauses

let hide_uninitialized ctx pat =
  let shadowed = pattern_names pat in
  {ctx with uninitialized = List.filter (fun name -> not (List.mem name shadowed)) ctx.uninitialized}

(* Leave a lexical binding without leaking its shadowed names or numeric
   assumptions. Keep state changes and updates to the outer mutable locals. *)
let restore_binding_scope outer inner pat =
  let shadowed = pattern_names pat in
  let restored = restore_scope outer inner in
  {restored with
   widths = outer.widths;
   numeric_facts = outer.numeric_facts;
   locals = List.filter (fun (name, _) -> not (List.mem name shadowed)) restored.locals @
            List.filter (fun (name, _) -> List.mem name shadowed) outer.locals;
   uninitialized = List.filter (fun name -> not (List.mem name shadowed)) restored.uninitialized @
                   List.filter (fun name -> List.mem name shadowed) outer.uninitialized}

(* A source let binding can also introduce singleton numeric type variables.
   Re-enter the checked body's numeric scope and remove the widths and facts
   of a type variable that the binding introduces or shadows. The program's
   variable names and numeric type-variable names are distinct namespaces,
   but both must respect the source lexical scope. *)
let singleton_pattern_variable pat =
  let env = Type_check.env_of_pat pat in
  match Type_check.destruct_atom_nexp env (Type_check.typ_of_pat pat) with
  | Some (Nexp_aux (Nexp_var kid, _)) when
      KBindings.find_opt kid (Type_check.Env.get_typ_vars env) = Some K_int ->
      Some kid
  | _ -> None

let numeric_binding_scope ctx pat initial_expression body =
  let rec type_binders (TP_aux (aux, _)) = match aux with
    | TP_var kid -> [kid]
    | TP_app (_, pats) -> List.concat_map type_binders pats
    | _ -> [] in
  let rec binders (P_aux (aux, _) as pat) = match aux with
    | P_var (pat, typ) -> type_binders typ @ binders pat
    | P_typ (_, pat) -> binders pat
    | P_tuple pats -> List.concat_map binders pats
    | P_id _ -> Option.to_list (singleton_pattern_variable pat)
    | _ -> [] in
  let old_env = Type_check.env_of initial_expression and new_env = Type_check.env_of body in
  List.fold_left (fun ctx kid ->
    (* A plain alias can have int('n) without introducing 'n. Its existing
       facts remain valid; only a new or shadowed witness starts a scope. *)
    if KBindings.mem kid (Type_check.Env.get_typ_vars old_env) &&
       Type_check.Env.shadows kid new_env <= Type_check.Env.shadows kid old_env
    then ctx else
    {ctx with
     widths = List.filter (fun (bound, _) -> bound <> kid_name kid) ctx.widths;
     numeric_facts = List.filter (fun fact ->
       not (KidSet.mem kid (tyvars_of_constraint fact))) ctx.numeric_facts}
  ) ctx (binders pat)

let arm_flag name =
  match name with "N" -> Some "NF" | "Z" -> Some "ZF"
                | "C" -> Some "CF" | "V" -> Some "VF" | _ -> None

(* Sail's x86 flags are one-bit registers; the existing HOL flags are
   Boolean components of RFLAGS. Check the source register and its exact
   type before choosing this canonical view. No extra component parameter
   or excluded write may stand in for an observed arithmetic flag. *)
let x86_flag loc env id =
  if !upstream_architecture <> Some "x86" ||
     not (List.exists (function
       | X86.Flag_bits flags -> List.mem (string_of_id id) flags
       | _ -> false) (x86_source ()).X86.bindings) then None
  else begin
    if not (Type_check.Env.is_register id env) ||
       hol_type [] env (Type_check.Env.get_register id env) <> Word 1 then
      fail loc "x86 flag interpretation requires a declared one-bit register";
    used_primitives := "x86-six-Boolean-flags" :: !used_primitives;
    Some (Atom (string_of_id id))
  end

(* Explicit view of the upstream processor-status register. NZCV fields map
   to s2n-bignum's Boolean flag components through one-bit words. Configuration
   fields use separate components. Check the genuine register/record and field
   types before choosing a view; an unrelated same-named field is insufficient. *)
let arm_pstate_field loc ctx env field =
  let pstate = mk_id "PSTATE" in
  if not (Type_check.Env.is_register pstate env) then
    fail loc "PSTATE field projection requires the upstream register";
  let declared = Type_check.Env.base_typ_of env (Type_check.Env.get_register pstate env) in
  let fields = match declared with
    | Typ_aux (Typ_id record, _) when string_of_id record = "ProcState" &&
          Type_check.Env.is_record record env ->
        snd (Type_check.Env.get_record record env)
    | _ -> fail loc "upstream PSTATE requires the ProcState record" in
  let name = string_of_id field in
  let expected = match arm_flag name, name with
    | Some _, _ | None, "nRW" -> Word 1
    | None, ("EL" | "BTYPE") -> Word 2
    | _ -> fail loc ("unsupported upstream PSTATE field " ^ name) in
  let actual = match List.find_opt
    (fun (_, id) -> Id.compare id field = 0) fields with
    | Some (typ, _) -> hol_type ctx.widths env typ
    | None -> fail loc ("upstream ProcState lacks " ^ name) in
  if actual <> expected then
    fail loc ("upstream PSTATE field has an incompatible type: " ^ name);
  match arm_flag name, ctx.state with
  | Some component, Some state ->
      used_primitives := "PSTATE-NZCV-projection" :: !used_primitives;
      let value =
        Typed (App ("word", [App ("bitval", [App ("read", [Atom component; state])])]), Word 1) in
      record_value ctx ["PSTATE-NZCV-projection"] ("PSTATE." ^ name) [] value;
      value
  | None, Some state ->
      used_registers := "PSTATE" :: !used_registers;
      used_primitives := "Arm-explicit-PSTATE-config-projection" :: !used_primitives;
      let rec project names term = match names with
        | [last] when last = name -> term
        | first :: rest ->
            if first = name then App ("FST", [term])
            else project rest (App ("SND", [term]))
        | _ -> fail loc ("unavailable PSTATE configuration field " ^ name) in
      let value = Typed (project Arm.pstate_fields
        (App ("read", [Atom (symbol "reg_" "PSTATE"); state])), expected) in
      record_value ctx ["Arm-explicit-PSTATE-config-projection"] ("PSTATE." ^ name) [] value;
      value
  | _, None -> fail loc "PSTATE field read in a pure function"

(* Read the HOL state at the current source point. Ordinary source registers
   can appear as extra component parameters in the exported definition.
   Instruction-PC reads are exceptional: source PC denotes the entry address,
   whereas next-PC operations use mutable state. Sampling/configuration
   projections are explicit architecture assumptions, recorded as contracts. *)
let register loc ctx id ty =
  let name = string_of_id id in
  refuse_bound_gpr loc name;
  match ctx.state with
  | None -> fail loc ("register read in a pure function: " ^ name)
  | Some state ->
      if !state_type = "armstate" && !state_computation && name = "SPESampleInFlight" then begin
        if ty <> Bool then fail loc "SPESampleInFlight must be Boolean";
        disabled_extensions := "Arm-SPE-sampling" :: !disabled_extensions;
        record_value ctx ["Arm-SPE-sampling"] name [] (Atom "F");
        Atom "F"
      end else if !state_type = "armstate" && !state_computation && name = "PSTATE" then begin
        let flags = ["N", Word 1; "Z", Word 1; "C", Word 1; "V", Word 1] in
        let fields = match ty with
          | Record fields when List.length fields >= 4 &&
                List.filteri (fun i _ -> i < 4) fields = flags -> fields
          | _ -> fail loc "PSTATE projection requires the declared N/Z/C/V one-bit record" in
        let config = List.filteri (fun i _ -> i >= 4) fields in
        let allowed = ["EL", Word 2; "BTYPE", Word 2; "nRW", Word 1] in
        if List.exists (fun field -> not (List.mem field allowed)) config ||
           List.length (List.sort_uniq String.compare (List.map fst config)) <>
             List.length config then
          fail loc "PSTATE configuration requires exact EL/BTYPE two-bit or nRW one-bit fields";
        (* nRW here comes from the quantified reg_PSTATE component, not
           from its initial-bit assumption, which only field reads use.
           A theorem over every reg_PSTATE includes the assumed value. *)
        used_primitives := "PSTATE-NZCV-projection" :: !used_primitives;
        let flag_values = List.map (fun component ->
            Typed (App ("word", [App ("bitval", [App ("read", [Atom component; state])])]), Word 1))
          ["NF"; "ZF"; "CF"; "VF"] in
        if config = [] then begin
          let value = Tuple_term flag_values in
          record_value ctx ["PSTATE-NZCV-projection"] name [] value;
          value
        end else begin
          used_registers := name :: !used_registers;
          used_primitives := "Arm-explicit-PSTATE-config-projection" :: !used_primitives;
          let record = App ("read", [Atom (symbol "reg_" name); state]) in
          let rec project index fields value =
            match index, fields with
            | 0, [_] -> value
            | 0, _ :: _ -> App ("FST", [value])
            | n, _ :: rest -> project (n - 1) rest (App ("SND", [value]))
            | _ -> assert false in
          let value = Tuple_term (flag_values @ List.mapi (fun i (_, ty) ->
            Typed (project (i + 4) fields record, ty)) config) in
          record_value ctx ["PSTATE-NZCV-projection"; "Arm-explicit-PSTATE-config-projection"]
            name [] value;
          value
        end
      end else if !state_type = "riscvstate" && name = "PC" then begin
        if ty <> Word 32 then fail loc "source current PC must be a 32-bit word";
        let value entry = App ("riscv_instruction_pc", [entry]) in
        record_value ctx ["RV32-instruction-PC"] name [] (value (Atom "s0"));
        value (Option.get ctx.entry_state)
      end else if !state_type = "armstate" && !state_computation && name = "_PC" then begin
        if ty <> Word 64 then fail loc "source instruction PC must be a 64-bit word";
        used_registers := name :: !used_registers;
        used_primitives := "Arm-frozen-instruction-PC64" :: !used_primitives;
        let value entry = App ("read", [Atom (symbol "reg_" name); entry]) in
        record_value ctx ["Arm-frozen-instruction-PC64"] name [] (value (Atom "s0"));
        value (Option.get ctx.entry_state)
      end else
      let component = symbol "reg_" name in
      used_registers := name :: !used_registers;
      let value = App ("read", [Atom component; state]) in
      record_value ctx ["register-component"] name [] value;
      value

let contract_register loc ctx name typ =
  match ctx.state with
  | None -> fail loc ("configuration component read in a pure function: " ^ name)
  | Some state ->
      contract_registers := (name, typ) :: List.remove_assoc name !contract_registers;
      used_registers := name :: !used_registers;
      App ("read", [Atom (symbol "reg_" name); state])

let constant_index ctx exp =
  match Type_check.destruct_atom_nexp (Type_check.env_of exp) (Type_check.typ_of exp) with
  | Some n -> number ctx.widths n
  | None -> fail (exp_loc exp) "only statically known bit positions are supported"

(* Discharge a SOURCE numeric proposition with the context's widths and
   facts; see proved_in. *)
let prove_specialized ctx env constraint_ =
  proved_in env ctx.widths ctx.numeric_facts constraint_

let numeric_argument exp =
  let env = Type_check.env_of exp in
  let typ = Type_check.Env.expand_synonyms env (Type_check.typ_of exp) in
  (* Direct calls such as UInt(x) have a bounded existential result rather
     than a named singleton. Open the compiler's fresh witness and retain
     its constraints; an unconstrained int therefore proves no bounds. *)
  let typ, env = match Type_check.destruct_exist typ with
    | Some (kids, constraint_, typ) ->
        let env = List.fold_left (fun env kid ->
          Type_check.Env.add_typ_var (exp_loc exp) kid env
        ) env kids in
        typ, Type_check.Env.add_constraint constraint_ env
    | None -> typ, env in
  env, Type_check.destruct_atom_nexp env typ

let bitvector_argument exp =
  let env = Type_check.env_of exp in
  let typ = Type_check.Env.expand_synonyms env (Type_check.typ_of exp) in
  let typ, env = match Type_check.destruct_exist typ with
    | Some (kids, constraint_, typ) ->
        let env = List.fold_left (fun env kid ->
          Type_check.Env.add_typ_var (exp_loc exp) kid env
        ) env kids in
        typ, Type_check.Env.add_constraint constraint_ env
    | None -> typ, env in
  env, Type_check.destruct_bitvector env typ

(* Use the argument's source refinement/witness to prove a required bound.
   A plain, unconstrained int gives no license to assume an index is in range.
   Failure stops export instead of narrowing the generated function's domain. *)
let require_numeric_fact ctx exp condition message =
  let env, numeric = numeric_argument exp in
  match numeric with
  | Some numeric when prove_specialized ctx env (condition numeric) -> ()
  | _ -> fail (exp_loc exp) message

let arm_branch_type loc ctx exp =
  let env = Type_check.env_of exp in
  if exp_type ctx.widths exp <> Enum "BranchType" then
    fail loc "Arm branches require the BranchType enumeration";
  let members = Type_check.Env.get_enum (mk_id "BranchType") env
    |> List.map string_of_id |> List.sort String.compare in
  let expected = List.sort String.compare [
    "BranchType_DIRCALL"; "BranchType_INDCALL"; "BranchType_ERET";
    "BranchType_DBGEXIT"; "BranchType_RET"; "BranchType_DIR";
    "BranchType_INDIR"; "BranchType_EXCEPTION"; "BranchType_TMFAIL";
    "BranchType_RESET"; "BranchType_UNKNOWN"] in
  if members <> expected then
    fail loc "BranchType must retain the declared Arm branch constructors"

let arm_instruction_pc loc ctx env =
  let id = mk_id "_PC" in
  if not (Type_check.Env.is_register id env) then
    fail loc "Arm branches require the explicit source _PC register";
  let ty = hol_type ctx.widths env (Type_check.Env.get_register id env) in
  register loc ctx id ty

(* Instantiate this call's actual typed helper body. Match source type
   variables against the call's argument/result types; preserve nested
   shadowing. A matching helper name alone never establishes its semantics. *)
let specialize_helper_types ctx exp body pat args =
  let definition_env = Type_check.env_of body in
  let actual_env = Type_check.env_of exp in
  let variables = Type_check.Env.get_typ_vars definition_env in
  let is_type_variable kid =
    KBindings.find_opt kid variables = Some K_type in
  let concrete env typ =
    try Some (hol_type ctx.widths env typ)
    with Reporting.Fatal_error _ -> None in
  let substitutions = KBindings.filter (fun kid arg ->
    is_type_variable kid && match arg with
    | A_aux (A_typ typ, _) ->
        Option.is_some (concrete (Type_check.env_of exp) typ)
    | _ -> false
  ) (Type_check.instantiation_of exp) in
  let rec correspond env formal actual_env actual substitutions =
    let formal = Type_check.Env.base_typ_of env formal in
    match formal with
    | Typ_aux (Typ_var kid, _) when is_type_variable kid ->
        let actual_type = match concrete actual_env actual with
          | Some ty -> ty
          | None -> fail (exp_loc exp) "helper type arguments must have a concrete supported representation" in
        (match KBindings.find_opt kid substitutions with
         | Some (A_aux (A_typ previous, _)) ->
             if concrete (Type_check.env_of exp) previous <> Some actual_type then
               fail (exp_loc exp) "helper type argument disagrees with its typed actual arguments";
             substitutions
         | _ -> KBindings.add kid (arg_typ actual) substitutions)
    | Typ_aux (Typ_tuple formals, _) ->
        (match Type_check.Env.base_typ_of actual_env actual with
         | Typ_aux (Typ_tuple actuals, _) when List.length formals = List.length actuals ->
             List.fold_left2 (fun substitutions formal actual ->
               correspond env formal actual_env actual substitutions
             ) substitutions formals actuals
         | _ -> substitutions)
    | Typ_aux (Typ_app (formal_id, formals), _) ->
        (match Type_check.Env.base_typ_of actual_env actual with
         | Typ_aux (Typ_app (actual_id, actuals), _)
             when Id.compare formal_id actual_id = 0 &&
                  List.length formals = List.length actuals ->
             List.fold_left2 (fun substitutions formal actual ->
               match formal, actual with
               | A_aux (A_typ formal, _), A_aux (A_typ actual, _) ->
                   correspond env formal actual_env actual substitutions
               | _ -> substitutions
             ) substitutions formals actuals
         | _ -> substitutions)
    | _ -> substitutions in
  let actual_type = match args with
    | [arg] -> Type_check.typ_of arg
    | _ -> mk_typ (Typ_tuple (List.map Type_check.typ_of args)) in
  let substitutions = correspond (Type_check.env_of_pat pat)
    (Type_check.typ_of_pat pat) (Type_check.env_of exp) actual_type substitutions in
  let substitutions = correspond definition_env (Type_check.typ_of body)
    (Type_check.env_of exp) (Type_check.typ_of exp) substitutions in
  if KBindings.is_empty substitutions then body, pat else
  (* neq_any precedes MemOp in Arm's source. Substituting MemOp for 'a
     changes the helper's annotations, but its original environment cannot
     resolve that later enum. Replay only the checked enum declaration in
     that environment; never borrow caller locals or numeric assumptions.
     Other missing named types remain unsupported. *)
  let rec import_enums env = function
    | Typ_aux (Typ_tuple types, _) -> List.fold_left import_enums env types
    | Typ_aux (Typ_exist (_, _, typ), _) -> import_enums env typ
    | Typ_aux (Typ_app (_, arguments), _) ->
        List.fold_left (fun env -> function
          | A_aux (A_typ typ, _) -> import_enums env typ
          | _ -> env) env arguments
    | Typ_aux (Typ_id id, loc) when Type_check.Env.is_enum id actual_env ->
        let members env = IdSet.of_list (Type_check.Env.get_enum id env) in
        if Type_check.Env.is_enum id env then begin
          if not (IdSet.equal (members env) (members actual_env)) then
            fail loc "helper enum declaration differs from its actual argument";
          env
        end else begin
          let declaration = match List.find_opt (function
            | DEF_aux (DEF_type (TD_aux (TD_enum (name, _, _), _)), _) ->
                Id.compare name id = 0
            | _ -> false) !source_definitions with
            | Some declaration -> Type_check.strip_def declaration
            | None -> fail loc "specialized enum lacks its checked declaration" in
          let _, extended = Type_error.check env {defs = [declaration]; comments = []} in
          if not (IdSet.equal (members extended) (members actual_env)) then
            fail loc "replayed helper enum differs from its actual argument";
          if Type_check.Env.get_locals extended <> Type_check.Env.get_locals env ||
             Type_check.Env.get_constraints extended <> Type_check.Env.get_constraints env ||
             Type_check.Env.get_typ_vars extended <> Type_check.Env.get_typ_vars env ||
             not (KBindings.for_all (fun kid _ ->
               Type_check.Env.shadows kid extended = Type_check.Env.shadows kid env)
               (Type_check.Env.get_typ_vars env)) ||
             Type_check.Env.get_ret_typ extended <> Type_check.Env.get_ret_typ env then
            fail loc "enum declaration changed the helper's local or numeric scope";
          extended
        end
    | _ -> env in
  (* Specialize the actual typed body, not a replacement for its name.
     Each call has its own substitutions. A nested binder that shadows
     a same-spelled type variable does not inherit its caller's binding. *)
  let annotation (loc, annot) =
    if Type_check.is_empty_tannot annot then loc, annot else
    let env = Type_check.env_of_tannot annot in
    let scoped = KBindings.filter (fun kid _ ->
      KBindings.find_opt kid (Type_check.Env.get_typ_vars env) = Some K_type &&
      Type_check.Env.shadows kid env = Type_check.Env.shadows kid definition_env
    ) substitutions in
    let typ = Type_check.subst_unifiers scoped (Type_check.typ_of_tannot annot) in
    let env = import_enums env typ in
    loc, Type_check.replace_env env (Type_check.replace_typ typ annot) in
  map_exp_annot annotation body, map_pat_annot annotation pat

(* Construct the callee's numeric scope. Concrete widths come from the checked
   call and interface; imported bounds/preconditions must be proved for actual
   arguments in the caller's environment. Do not use callee assumptions to
   justify their own preconditions, or capture same-named caller variables. *)
let specialize_helper ?(check_result = true) ?value_measure ctx exp name body pat args =
  let rec untyped_tuple = function
    | E_aux (E_typ (_, exp), _) -> untyped_tuple exp
    | E_aux (E_tuple args, _) -> Some args
    | _ -> None in
  let rec formal_arguments (P_aux (aux, _) as pat) args =
    match aux, args with
    | (P_typ (_, pat) | P_var (pat, _)), _ -> formal_arguments pat args
    | P_tuple _, [arg] when Option.is_some (untyped_tuple arg) ->
        formal_arguments pat (Option.get (untyped_tuple arg))
    | P_tuple pats, args when List.length pats = List.length args ->
        List.concat (List.map2 (fun pat arg -> formal_arguments pat [arg]) pats args)
    | P_id _, [arg] -> [pat, arg]
    | _ -> [] in
  let arguments = formal_arguments pat args in
  let widths = KBindings.fold (fun kid arg ws ->
    match arg with
    | A_aux (A_nexp n, _) ->
        let name = kid_name kid in
        let ws = List.remove_assoc name ws in
        (try (name, number ctx.widths n) :: ws with Reporting.Fatal_error _ -> ws)
    | _ -> ws
  ) (Type_check.instantiation_of exp) ctx.widths in
  let rec interface_widths env typ actual ws =
    match Type_check.destruct_bitvector env typ, actual with
    | Some (Nexp_aux (Nexp_var kid, _)), Word n ->
        (kid_name kid, n) :: List.remove_assoc (kid_name kid) ws
    | None, Tuple actual ->
        (match Type_check.Env.base_typ_of env typ with
         | Typ_aux (Typ_tuple ts, _) when List.length ts = List.length actual ->
             List.fold_left2 (fun ws typ ty -> interface_widths env typ ty ws) ws ts actual
         | _ -> ws)
    | _ -> ws in
  let arg_type = match args with
    | [arg] -> exp_type ctx.widths arg
    | _ -> Tuple (List.map (exp_type ctx.widths) args) in
  let widths = interface_widths (Type_check.env_of_pat pat)
    (Type_check.typ_of_pat pat) arg_type widths in
  let widths = interface_widths (Type_check.env_of body)
    (Type_check.typ_of body) (exp_type ctx.widths exp) widths in
  (* A fixed singleton integer argument also supplies its numeric type
     variable. Sail's call instantiation need not repeat that information.
     Resolve only the actual checked numeric type in the caller's scope;
     an arbitrary int or symbolic runtime value supplies no fixed measure. *)
  let widths = List.fold_left (fun widths (formal, actual) ->
    match Type_check.destruct_atom_nexp (Type_check.env_of_pat formal)
            (Type_check.typ_of_pat formal), snd (numeric_argument actual) with
    | Some (Nexp_aux (Nexp_var kid, _)), Some actual ->
        (try
           let value = number ctx.widths actual in
           (kid_name kid, value) :: List.remove_assoc (kid_name kid) widths
         with Reporting.Fatal_error _ -> widths)
    | _ -> widths
  ) widths arguments in
  let variables = Type_check.Env.get_typ_vars (Type_check.env_of body) in
  let widths = List.filter (fun (name, _) ->
    KBindings.mem (mk_kid name) variables
  ) widths in
  if List.mem name ctx.stack then begin
    (* Direct source recursion can be unfolded when its checked numeric
       instance decreases. Reduce__1, for example, halves N until N=esize.
       Compare the same helper's fixed numeric variables, never printed
       expressions or a guessed recursive result. Every known measure must
       remain nonnegative and nonincreasing, and at least one must decrease.
       Reject mutual recursion and unresolved/runtime decreases. This is
       finite translation of the original body, not a HOL recursion axiom. *)
    let formal_variables = Type_check.Env.get_typ_vars (Type_check.env_of_pat pat) in
    let previous = List.filter (fun (variable, _) ->
      KBindings.mem (mk_kid variable) formal_variables) ctx.widths in
    let measures = List.map (fun (variable, previous) ->
      Option.map (fun current -> previous, current)
        (List.assoc_opt variable widths)) previous in
    let static_decrease =
      List.for_all (function Some (previous, current) ->
        previous >= 0 && current >= 0 && current <= previous | None -> false) measures &&
      List.exists (function Some (previous, current) ->
        current < previous | None -> false) measures in
    (* A pure caller can instead supply bounds on integer arguments: the
       callee's current interval and the recursive call's interval. *)
    let value_decrease = not static_decrease && extended_evaluation () &&
      match value_measure with
      | Some measure -> measure ()
      | None -> false in
    if not !state_computation || List.hd ctx.stack <> name ||
       not (static_decrease || value_decrease)
    then fail (exp_loc exp) ("recursive call lacks a decreasing static instance: " ^ name);
    let budget, limit = if value_decrease then value_recursion_budget, 65536
      else loop_budget, 4096 in
    incr budget;
    if List.length ctx.stack >= 64 || !budget > limit then
      fail (exp_loc exp) "recursive unfolding exceeds the static expansion bound"
  end;
  if check_result &&
     hol_type widths (Type_check.env_of body) (Type_check.typ_of body) <>
     exp_type ctx.widths exp then
    fail (exp_loc exp) ("callee result specialization disagrees with typed call: " ^ name);
  (* Opening a range type introduces a fresh existential witness. Reuse
     that same witness and environment for every proof and substitution. *)
  let numeric_arguments = List.map (fun (formal, actual) ->
    let env, numeric = numeric_argument actual in formal, env, numeric
  ) arguments in
  let numeric_facts = List.concat_map (fun (formal, actual_env, actual_number) ->
    let formal_env = Type_check.env_of_pat formal in
    match Type_check.destruct_atom_nexp formal_env (Type_check.typ_of_pat formal),
          actual_number with
    | Some (Nexp_aux (Nexp_var kid, _)), Some actual_number ->
        (* Only transfer facts the actual argument environment proves.
           Facts refer to this helper's own singleton numeric parameter;
           discard the caller's facts rather than capture same-named kids. *)
        let parameter = nvar kid in
        let simple = List.filter_map (fun bound ->
          if prove_specialized ctx actual_env (bound actual_number) then begin
            let fact = bound parameter in
            record_numeric_argument_fact name fact;
            Some fact
          end else None
        ) [ (fun n -> nc_lteq (nint 0) n);
            (fun n -> nc_lt (nint 0) n);
            (fun n -> nc_lteq n (nint 31)) ] in
        (* An actual such as unsigned(index) + 8 is not a variable that can
           be inverted into the formal. Find a caller-proved finite bound
           instead; the list limits solver work, never assumes a bound. *)
        let tight_bound = List.find_map (fun maximum ->
          if prove_specialized ctx actual_env
              (nc_lteq actual_number (nint maximum)) then begin
            let fact = nc_lteq parameter (nint maximum) in
            record_numeric_argument_fact name fact;
            Some fact
          end else None
        ) [0; 1; 3; 7; 15; 31; 63; 127; 255] in
        simple @ Option.to_list tight_bound
    | _ -> []
  ) numeric_arguments in
  (* Retain helper preconditions only after proving their actual-argument
     instance in a caller environment. Substitution is simultaneous: an
     actual named N must not be captured by another formal also named N.
     Do not import the helper's own assumptions into the caller proof. *)
  let substitutions = List.fold_left (fun substitutions (name, value) ->
    KBindings.add (mk_kid name) (nint value) substitutions
  ) KBindings.empty widths in
  let substitutions, actual_environments = List.fold_left
    (fun (substitutions, environments) (formal, actual_env, actual_number) ->
      let formal_env = Type_check.env_of_pat formal in
      match Type_check.destruct_atom_nexp formal_env (Type_check.typ_of_pat formal),
            actual_number with
      | Some (Nexp_aux (Nexp_var kid, _)), Some actual_number ->
          KBindings.add kid actual_number substitutions,
          actual_env :: environments
      | _ -> substitutions, actual_env :: environments)
    (substitutions, [Type_check.env_of exp]) numeric_arguments in
  let definition_env = Type_check.env_of body in
  (* Transport caller constraints that mention only actual singleton
     parameters (or known static widths). This preserves, for example,
     the bound of an encoded lane index across an intermediate helper,
     without guessing a new bound from the helper's name or its use. *)
  let inverse_substitutions = List.fold_left (fun inverse (formal, _, actual_number) ->
    let formal_env = Type_check.env_of_pat formal in
    match Type_check.destruct_atom_nexp formal_env (Type_check.typ_of_pat formal),
          actual_number with
    | Some (Nexp_aux (Nexp_var formal, _)),
      Some (Nexp_aux (Nexp_var actual, _)) ->
        if KBindings.mem actual inverse then inverse
        else KBindings.add actual (nvar formal) inverse
    | _ -> inverse
  ) KBindings.empty numeric_arguments in
  let inverse_substitutions = List.fold_left (fun inverse (name, value) ->
    let kid = mk_kid name in
    if KBindings.mem kid inverse then inverse
    else KBindings.add kid (nint value) inverse
  ) inverse_substitutions ctx.widths in
  let inherited_facts = List.concat_map (fun env ->
    List.filter_map (fun constraint_ ->
      let variables = tyvars_of_constraint constraint_ in
      (* A global configuration constraint with no parameter variables is
         not a fact about this call. Its named numeric types may be outside
         the earlier helper's module/environment, so do not transport it. *)
      if KidSet.is_empty variables ||
         not (KidSet.for_all (fun kid -> KBindings.mem kid inverse_substitutions)
          variables) then None else
      let formal_constraint = subst_kids_nc inverse_substitutions constraint_ in
      if not (KidSet.for_all (fun kid ->
        KBindings.mem kid (Type_check.Env.get_typ_vars definition_env)
      ) (tyvars_of_constraint formal_constraint)) then None
      else if not (try
        ignore (Type_check.Env.add_constraint formal_constraint definition_env); true
      with Type_error.Type_error _ -> false) then
        (* A parameter fact may still mention a caller-only named numeric
           type. Checking it in the callee's original environment avoids
           importing an out-of-scope declaration along with the fact. *)
        None
      else if prove_specialized ctx env constraint_ then begin
        record_numeric_argument_fact name formal_constraint;
        Some formal_constraint
      end else None
    ) (Type_check.Env.get_constraints env @ ctx.numeric_facts)
  ) actual_environments in
  let candidates = ref [] in
  ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with
    e_assert = (fun (condition, message) ->
      let env = Type_check.env_of condition in
      (match Type_check.destruct_atom_bool env (Type_check.typ_of condition) with
       | Some constraint_ ->
           let variables = tyvars_of_constraint constraint_ in
           if KidSet.for_all (fun kid ->
             KBindings.mem kid substitutions &&
             KBindings.mem kid (Type_check.Env.get_typ_vars definition_env) &&
             Type_check.Env.shadows kid env =
               Type_check.Env.shadows kid definition_env
           ) variables then
             candidates := constraint_ :: !candidates
       | None -> ());
      E_assert (condition, message))
  } body);
  let asserted_facts = List.filter_map (fun constraint_ ->
    let actual_constraint = subst_kids_nc substitutions constraint_ in
    let actual_variables = tyvars_of_constraint actual_constraint in
    if List.exists (fun env ->
      KidSet.for_all (fun kid ->
        KBindings.mem kid (Type_check.Env.get_typ_vars env)
      ) actual_variables &&
      prove_specialized ctx env actual_constraint
    ) actual_environments then begin
      record_numeric_argument_fact name constraint_;
      Some constraint_
    end else None
  ) !candidates in
  let numeric_facts = List.sort_uniq (fun x y ->
    String.compare (string_of_n_constraint x) (string_of_n_constraint y)
  ) (numeric_facts @ inherited_facts @ asserted_facts) in
  {ctx with widths; numeric_facts; locals = []; stack = name :: ctx.stack;
    mutable_locals = []; uninitialized = []}

(* Value metadata used while translating, erased only at printing.
   Bounded_value keeps sound bounds for an already evaluated backing term.
   Partial_word keeps the exact set of assigned bit positions. Transfers may
   carry a partial value, but observations (conditions, arithmetic, writes)
   require the relevant bits to be known. This is not a model of arbitrary
   undefined values: accepted programs must not expose the unknown backing. *)
let rec strip_term = function
  | Typed (t, _) | Bounded_value (t, _, _) -> strip_term t
  | Shared_value (_, facts) -> strip_term facts
  | t -> t

let partial_word value =
  match strip_term value with
  | Partial_word (backing, width, known) -> Some (backing, width, known)
  | _ -> None

let rec contains_partial = function
  | Partial_word _ -> true
  | Typed (value, _) | Lambda (_, value) | Exists (_, value)
  | Choose (_, value) | Stop value | Bounded_value (value, _, _) ->
      contains_partial value
  | Shared_value (value, facts) -> contains_partial value || contains_partial facts
  | App (_, values) | Tuple_term values -> List.exists contains_partial values
  | Infix (_, x, y) -> contains_partial x || contains_partial y
  | Cond (c, x, y) -> List.exists contains_partial [c; x; y]
  | Let (_, value, body) -> contains_partial value || contains_partial body
  | Atom _ | String_literal _ | Fault | Reject -> false

let tracked_word backing width known =
  let known = List.sort_uniq Int.compare known in
  if List.length known = width then Typed (backing, Word width)
  else Partial_word (Typed (backing, Word width), width, known)

(* Last check before observing a transferred value, including externally
   visible writes. undefined locals are not arbitrary zero values: their
   backing terms remain unobservable until the required bits are assigned. *)
let observable_value loc value =
  if contains_partial value then
    fail loc "an observable value contains uninitialized bits";
  value

(* This only evaluates the already translated, pure integer term tree.
   The original Let bindings and helper bodies remain in the emitted model.
   Unknown atoms/operations never acquire a guessed value. *)
let rec integer_literal term =
  let decimal text =
    if text <> "" && String.for_all (fun c -> c >= '0' && c <= '9') text then
      Some (Nat_big_num.of_string text) else None in
  let binary operation x y =
    match integer_literal x, integer_literal y with
    | Some x, Some y -> Some (operation x y)
    | _ -> None in
  match term with
  | Typed (value, _) -> integer_literal value
  | Bounded_value (_, low, high) when Nat_big_num.equal low high -> Some low
  | Bounded_value (value, _, _) -> integer_literal value
  | _ -> match strip_term term with
  | App ("&", [Atom text]) -> decimal text
  | App ("&", [Infix ("EXP", Atom "2", App ("num_of_int", [amount]))]) ->
      (match integer_literal amount with
       | Some amount when not (Nat_big_num.less amount Nat_big_num.zero) &&
                          not (Nat_big_num.greater amount (Nat_big_num.of_int 256)) ->
           Some (Nat_big_num.pow_int (Nat_big_num.of_int 2) (Nat_big_num.to_int amount))
       | _ -> None)
  | App ("--", [x]) -> Option.map Nat_big_num.negate (integer_literal x)
  | Infix ("+", x, y) -> binary Nat_big_num.add x y
  | Infix ("-", x, y) -> binary Nat_big_num.sub x y
  | Infix ("*", x, y) -> binary Nat_big_num.mul x y
  (* Nat_big_num.div and modulus are Euclidean (Z.ediv, Z.erem), as are
     HOL's integer div and rem for a positive divisor. *)
  | Infix (("div" | "rem" as operation), x, y) ->
      (match integer_literal x, integer_literal y with
       | Some x, Some y when Nat_big_num.greater y Nat_big_num.zero ->
           Some ((if operation = "div" then Nat_big_num.div else Nat_big_num.modulus) x y)
       | _ -> None)
  | App (("min" | "max" as operation), [x; y]) ->
      binary (fun x y ->
        if (if operation = "min" then Nat_big_num.less x y else Nat_big_num.greater x y)
        then x else y) x y
  | Let (_, _, body) -> integer_literal body
  | _ -> None

let decimal text =
  if String.length text > 0 &&
     String.for_all (fun c -> c >= '0' && c <= '9') text then
    Some (Nat_big_num.of_string text)
  else None

let word_maximum width = Nat_big_num.sub
  (Nat_big_num.pow_int (Nat_big_num.of_int 2) width) (Nat_big_num.of_int 1)

(* Conservative bounds on translated word values. These help specialize a
   branch/index when source types alone are too coarse. Each successful case
   must bound the actual backing value, not replace its evaluation. Unknown
   word operations fall back to the full width's range, never a guessed value. *)
let rec word_bounds value =
  match value with
  | Typed (value, Word width) ->
      let maximum = word_maximum width in
      let full () = Some (Nat_big_num.zero, maximum) in
      let valid low high =
        not (Nat_big_num.less low Nat_big_num.zero) &&
        not (Nat_big_num.less high low) &&
        not (Nat_big_num.greater high maximum) in
      let rec bounds = function
        | Typed (value, _) -> bounds value
        | Shared_value (_, facts) -> bounds facts
        | Bounded_value (_, low, high) when valid low high -> Some (low, high)
        | App ("word", [Atom text]) ->
            (match decimal text with
             | Some n when valid n n -> Some (n, n)
             | _ -> full ())
        | App ("word_join", [high; low]) ->
            (match high, low, word_bounds high, word_bounds low with
             | Typed (_, Word h), Typed (_, Word l),
               Some (hl, hh), Some (ll, lh) when h + l = width ->
                 let factor = Nat_big_num.pow_int (Nat_big_num.of_int 2) l in
                 Some (Nat_big_num.add (Nat_big_num.mul hl factor) ll,
                       Nat_big_num.add (Nat_big_num.mul hh factor) lh)
             | _ -> full ())
        | App ("iword", [operand]) when extended_evaluation () ->
            (* iword of a known integer is that integer modulo 2^width. *)
            (match integer_literal operand with
             | Some value ->
                 let modulus = Nat_big_num.add maximum (Nat_big_num.of_int 1) in
                 let value = Nat_big_num.modulus value modulus in
                 Some (value, value)
             | None -> full ())
        | App ("word_not", [operand]) ->
            (match operand, word_bounds operand with
             | Typed (_, Word n), Some (low, high) when n = width ->
                 Some (Nat_big_num.sub maximum high, Nat_big_num.sub maximum low)
             | _ -> full ())
        | App (("word_and" | "word_or" | "word_xor") as operation, [left; right])
            when extended_evaluation () &&
                 (match word_bounds left, word_bounds right with
                  | Some (ll, lh), Some (rl, rh) ->
                      Nat_big_num.equal ll lh && Nat_big_num.equal rl rh
                  | _ -> false) ->
            (* Two known words of this width have one known result. *)
            let value side = fst (Option.get (word_bounds side)) in
            let result = (match operation with
              | "word_and" -> Nat_big_num.bitwise_and
              | "word_or" -> Nat_big_num.bitwise_or
              | _ -> Nat_big_num.bitwise_xor) (value left) (value right) in
            if valid result result then Some (result, result) else full ()
        | App ("word_and", [left; right]) ->
            (match left, right, word_bounds left, word_bounds right with
             | Typed (_, Word l), Typed (_, Word r),
               Some (_, lh), Some (_, rh) when l = width && r = width ->
                 (* An unsigned bitwise intersection is no larger than
                    either operand. No nonzero lower bound follows. *)
                 Some (Nat_big_num.zero,
                   if Nat_big_num.less lh rh then lh else rh)
             | _ -> full ())
        | App ("word_zx", [operand]) ->
            (match operand, word_bounds operand with
             | Typed (_, Word _), Some (low, high) ->
                 if not (Nat_big_num.greater high maximum) then Some (low, high)
                 else Some (Nat_big_num.zero, maximum)
             | _ -> full ())
        | App ("word_subword", [operand; Tuple_term [Atom start; Atom length]]) ->
            (* A slice is monotone within one modulus period after the lower
               bits are discarded. Crossing a period retains the full range.
               Constant prefixes with symbolic low bits work without
               replacing the original expression or its evaluation. *)
            (match decimal start, decimal length, word_bounds operand with
             | Some start, Some length, Some (low, high)
                 when Nat_big_num.equal length (Nat_big_num.of_int width) &&
                      Nat_big_num.less_equal start (Nat_big_num.of_int 256) ->
                 let divisor = Nat_big_num.pow_int (Nat_big_num.of_int 2)
                   (Nat_big_num.to_int start) in
                 let modulus = Nat_big_num.pow_int (Nat_big_num.of_int 2) width in
                 let low = Nat_big_num.div low divisor
                 and high = Nat_big_num.div high divisor in
                 if Nat_big_num.equal (Nat_big_num.div low modulus)
                     (Nat_big_num.div high modulus) then
                   Some (Nat_big_num.modulus low modulus,
                         Nat_big_num.modulus high modulus)
                 else full ()
             | _ -> full ())
        | Let (_, _, body) ->
            (match word_bounds body with
             | Some (low, high) when valid low high -> Some (low, high)
             | _ -> full ())
        | App ("word", [App ("bitval", [App ("bit", [Atom bit; operand])])])
            when width = 1 ->
            (match decimal bit, word_bounds operand with
             | Some bit, Some (low, high) ->
                 let bit = try Some (Nat_big_num.to_int bit) with _ -> None in
                 (match bit with
                  | Some bit when bit >= 0 && bit <= 256 ->
                      let factor = Nat_big_num.pow_int (Nat_big_num.of_int 2) bit in
                      let low = Nat_big_num.div low factor
                      and high = Nat_big_num.div high factor in
                      if Nat_big_num.equal low high then
                        let bit = Nat_big_num.modulus low (Nat_big_num.of_int 2) in
                        Some (bit, bit)
                      else full ()
                  | _ -> full ())
             | _ -> full ())
        | _ -> full () in
      bounds value
  | _ -> None

(* An equality key for the arithmetic bounds analysis, not emitted code.
   Resolve lexical let bindings with their outer values before entering the
   body, so shadowed helper parameters cannot capture one another. The
   original evaluated expression and every effect remain in print_term. *)
let arithmetic_key value =
  let exception Unsupported_key in
  let rec normalize environment value =
    match value with
    | Atom name -> Option.value (List.assoc_opt name environment) ~default:value
    | String_literal _ -> value
    | Typed (value, _) | Bounded_value (value, _, _) -> normalize environment value
    | Shared_value (_, facts) -> normalize environment facts
    | Tuple_term values -> Tuple_term (List.map (normalize environment) values)
    | Let (pattern, value, body) ->
        let value = normalize environment value in
        let rec bind pattern value environment =
          match pattern with
          | Typed (pattern, _) -> bind pattern value environment
          | Atom name -> Some ((name, value) :: List.remove_assoc name environment)
          | Tuple_term patterns ->
              let rec fields environment patterns value =
                match patterns with
                | [] -> Some environment
                | [pattern] -> bind pattern value environment
                | pattern :: rest ->
                    (match bind pattern (project true value) environment with
                     | Some environment -> fields environment rest (project false value)
                     | None -> None)
              in fields environment patterns value
          | _ -> None
        and project first = function
          | Tuple_term (value :: rest) ->
              if first then value else
                (match rest with [value] -> value | _ -> Tuple_term rest)
          | value -> App ((if first then "FST" else "SND"), [value]) in
        (match bind pattern value environment with
         | Some environment -> normalize environment body
         | None -> raise Unsupported_key)
    | App (("FST" | "SND" as projection), [value]) ->
        (match normalize environment value with
         | Tuple_term (first :: rest) when rest <> [] ->
             if projection = "FST" then first else
             (match rest with [last] -> last | _ -> Tuple_term rest)
         | value -> App (projection, [value]))
    | App (function_, values) -> App (function_, List.map (normalize environment) values)
    | Infix (operation, left, right) ->
        Infix (operation, normalize environment left, normalize environment right)
    | Cond (condition, yes, no) -> Cond (normalize environment condition,
        normalize environment yes, normalize environment no)
    | Partial_word _ | Lambda _ | Exists _ | Choose _ | Stop _ | Fault | Reject ->
        raise Unsupported_key in
  try Some (normalize [] value) with Unsupported_key -> None

let positive_remainder_bound value =
  match arithmetic_key value with
  | Some (Infix ("-", dividend,
      Infix ("*", divisor, Infix ("div", same_dividend, same_divisor))))
      when dividend = same_dividend && divisor = same_divisor ->
      (match integer_literal divisor with
       | Some divisor when Nat_big_num.greater divisor Nat_big_num.zero ->
           Some (Nat_big_num.zero, Nat_big_num.sub divisor (Nat_big_num.of_int 1))
       | _ -> None)
  | _ -> None

let rec integer_bounds value =
  match value with
  | Typed (value, Int) -> integer_bounds value
  | Shared_value (_, facts) -> integer_bounds facts
  | Bounded_value (_, low, high) -> Some (low, high)
  | App ("&", [App ("val", [word])]) -> word_bounds word
  | App ("ival", [Typed (_, Word width)]) ->
      let half = Nat_big_num.pow_int (Nat_big_num.of_int 2) (width - 1) in
      Some (Nat_big_num.negate half,
            Nat_big_num.sub half (Nat_big_num.of_int 1))
  | App ("--", [value]) ->
      Option.map (fun (low, high) ->
        Nat_big_num.negate high, Nat_big_num.negate low) (integer_bounds value)
  | Infix ("rem", _, divisor) ->
      (* Euclidean remainder lies in 0..d-1 for a positive divisor,
         independently of the dividend's sign. Never infer this interval
         for zero, negative or unresolved divisors. *)
      (match integer_literal divisor with
       | Some divisor when Nat_big_num.greater divisor Nat_big_num.zero ->
           Some (Nat_big_num.zero,
                 Nat_big_num.sub divisor (Nat_big_num.of_int 1))
       | _ -> None)
  | Infix ("div", dividend, divisor) when extended_evaluation () ->
      (* Floor quotient by a positive literal of a nonnegative interval. *)
      (match integer_bounds dividend, integer_literal divisor with
       | Some (low, high), Some divisor when
           Nat_big_num.greater_equal low Nat_big_num.zero &&
           Nat_big_num.greater divisor Nat_big_num.zero ->
           Some (Nat_big_num.div low divisor, Nat_big_num.div high divisor)
       | _ -> None)
  | Infix (("+" | "-" as operation), left, right) ->
      (match (if operation = "-" then positive_remainder_bound value else None),
             integer_bounds left, integer_bounds right with
       | Some interval, _, _ -> Some interval
       | None, Some (ll, lh), Some (rl, rh) ->
           if operation = "+" then
             Some (Nat_big_num.add ll rl, Nat_big_num.add lh rh)
           else Some (Nat_big_num.sub ll rh, Nat_big_num.sub lh rl)
       | _ -> None)
  | Let (_, _, body) ->
      (match positive_remainder_bound value with
       | Some interval -> Some interval | None -> integer_bounds body)
  | _ -> Option.map (fun n -> n, n) (integer_literal value)

let value_bounds = function
  | Typed (_, Word _) as value -> word_bounds value
  | Typed (_, Int) as value -> integer_bounds value
  | Bounded_value (_, low, high) -> Some (low, high)
  | _ -> None

let retain_bounds backing value =
  match value_bounds value with
  | Some (low, high) -> Bounded_value (backing, low, high)
  | None -> backing

(* Supplement a coarse source integer type with bounds on the actual
   translated value. These intervals follow primitive meanings and survive
   bindings; they are not assumptions about a caller or a hardware index. *)
let integer_bounds_proved ctx expression value minimum maximum =
  let env, numeric = numeric_argument expression in
  let lower numeric = nc_lteq (nint minimum) numeric in
  let source_proved = match numeric with
    | Some numeric -> prove_specialized ctx env (match maximum with
        | Some maximum -> nc_and (lower numeric) (nc_lteq numeric (nint maximum))
        | None -> lower numeric)
    | None -> false in
  let value_proved = match integer_bounds value with
    | Some (low, high) ->
        Nat_big_num.greater_equal low (Nat_big_num.of_int minimum) &&
        Option.fold ~none:true ~some:(fun maximum ->
          Nat_big_num.less_equal high (Nat_big_num.of_int maximum)) maximum
    | None -> false in
  source_proved || value_proved

let require_integer_bounds ctx expression value minimum maximum message =
  if not (integer_bounds_proved ctx expression value minimum maximum) then
    fail (exp_loc expression) message

let require_integer_interval ctx expression value minimum maximum message =
  require_integer_bounds ctx expression value minimum (Some maximum) message

let require_integer_lower_bound ctx expression value minimum message =
  require_integer_bounds ctx expression value minimum None message

(* Bit-vector shifts by an integer amount: the source type, or with the
   REMS profile the evaluated amount's bounds (8 - places for a count
   masked to 0..31), proves the amount nonnegative. *)
let integer_shift_nonnegative ctx shift value =
  if extended_evaluation () then integer_bounds_proved ctx shift value 0 None
  else match numeric_argument shift with
    | env, Some numeric -> prove_specialized ctx env (nc_lteq (nint 0) numeric)
    | _, None -> false

let integer_shift_operation = function
  | "sail_shiftleft" | "shiftl" -> "word_shl"
  | "sail_shiftright" | "shiftr" -> "word_ushr"
  | _ -> "word_ishr"

(* Restrict an established local interval on one arm of an actual emitted
   integer comparison. This is path information, not an instruction-domain
   restriction: the complementary arm remains in the generated conditional.
   Match the evaluated backing term, not a printed variable name. *)
let rec comparison_context ctx condition truth =
  match strip_term condition with
  | App ("~", [condition]) -> comparison_context ctx condition (not truth)
  | Infix (("<" | "<=" | ">" | ">=" as operation), left, right) ->
      (match integer_literal right, integer_bounds left with
       | Some bound, Some _ ->
           let previous = Nat_big_num.sub bound (Nat_big_num.of_int 1)
           and following = Nat_big_num.add bound (Nat_big_num.of_int 1) in
           let lower, upper = match operation, truth with
             | ">=", true | "<", false -> Some bound, None
             | ">", true | "<=", false -> Some following, None
             | "<=", true | ">", false -> None, Some bound
             | _ -> None, Some previous in
           let locals = List.map (fun (name, value) ->
             if strip_term value <> strip_term left then name, value
             else match value_bounds value with
               | None -> name, value
               | Some (low, high) ->
                   let low = match lower with Some lower when Nat_big_num.greater lower low ->
                     lower | _ -> low in
                   let high = match upper with Some upper when Nat_big_num.less upper high ->
                     upper | _ -> high in
                   (* An impossible arm need not be used to justify a
                      translation. Keep its original bounds and let ordinary
                      checks refuse it rather than infer a false interval. *)
                   if Nat_big_num.greater low high then name, value
                   else name, Bounded_value (value, low, high)
           ) ctx.locals in
           {ctx with locals}
       | _ -> ctx)
  | _ -> ctx

let rec source_comparison_context ctx expression evaluated truth =
  match expression with
  | E_aux (E_typ (_, expression), _) ->
      source_comparison_context ctx expression evaluated truth
  | E_aux (E_app (id, [expression]), _) when string_of_id id = "not_bool" &&
      pure_external id ->
      source_comparison_context ctx expression evaluated (not truth)
  | E_aux (E_app (id, [E_aux (E_id local, _) as left;
                      E_aux (E_lit (L_aux (L_num bound, _)), _) as right]), _)
      when pure_external id &&
           List.map (exp_type ctx.widths) [left; right; expression] = [Int; Int; Bool] ->
      let operation = match string_of_id id with
        | "lt_int" | "lt_atom" -> Some "<"
        | "lteq_int" | "lteq_atom" -> Some "<="
        | "gt_int" | "gt_atom" -> Some ">"
        | "gteq_int" | "gteq_atom" -> Some ">="
        | _ -> None in
      (match operation, List.assoc_opt (string_of_id local) ctx.locals with
       | Some operation, Some value ->
           (* Capturing comparison arguments gives their HOL temporaries new
              names. A pure comparison of a bare local and literal has no
              selector/RHS effects, so the same local value is still current.
              Do not apply this shortcut to arbitrary helper expressions. *)
           comparison_context ctx (Infix (operation, Typed (value, Int), integer bound)) truth
       | _ -> comparison_context ctx evaluated truth)
  | _ -> comparison_context ctx evaluated truth

(* A literal helper result may contain already evaluated let bindings.
   Recover only its exact returned bytes, without comparing printed text,
   normalizing Unicode, trimming whitespace or stopping at a NUL byte.
   The bindings and helper calculations remain in the emitted term. *)
let rec string_literal value =
  match strip_term value with
  | String_literal bytes -> Some bytes
  | Let (_, _, body) -> string_literal body
  | _ -> None

(* Literal specialization never inspects printed Sail/HOL source. Its word
   cases are typed, in-range literals; strings retain exact source bytes.
   Other compound values remain symbolic. *)
let rec boolean_literal term =
  match strip_term term with
  | Atom "T" -> Some true | Atom "F" -> Some false
  | Infix ("=", left, right) ->
      (match literal_key left, literal_key right with
       | Some (left_type, left), Some (right_type, right) when left_type = right_type ->
           Some (left = right)
       | _ -> None)
  | Infix (("<" | "<=" | ">" | ">=" as operation), left, right) ->
      (match integer_literal left, integer_literal right with
       | Some left, Some right ->
           let less = Nat_big_num.less left right and equal = Nat_big_num.equal left right in
           Some (match operation with "<" -> less | "<=" -> less || equal
                 | ">" -> not (less || equal) | _ -> not less)
       | _ ->
           (match integer_bounds left, integer_bounds right with
            | Some (ll, lh), Some (rl, rh) ->
                let less_equal x y = Nat_big_num.less_equal x y in
                let less x y = Nat_big_num.less x y in
                let yes, no = match operation with
                  | "<" -> less lh rl, less_equal rh ll
                  | "<=" -> less_equal lh rl, less rh ll
                  | ">" -> less rh ll, less_equal lh rl
                  | _ -> less_equal rh ll, less lh rl in
                if yes then Some true else if no then Some false else None
            | _ -> None))
  | App ("~", [value]) -> Option.map not (boolean_literal value)
  | Let (_, _, body) -> boolean_literal body
  | Infix (("/\\" | "\\/" as op), left, right) ->
      (match boolean_literal left, boolean_literal right with
       | Some left, Some right -> Some (if op = "/\\" then left && right else left || right)
       | Some false, _ | _, Some false when op = "/\\" -> Some false
       | Some true, _ | _, Some true when op = "\\/" -> Some true
       | _ -> None)
  | _ -> None

and literal_key term =
  match term with
  | Typed (_, Bool) ->
      Option.map (fun value -> "bool", string_of_bool value) (boolean_literal term)
  | Typed (_, Int) ->
      Option.map (fun value -> "int", Nat_big_num.to_string value) (integer_literal term)
  | Typed (_, String_type) ->
      Option.map (fun value -> "string", value) (string_literal term)
  | Typed (_, Empty_bits) -> Some ("empty-bits", "")
  | Typed (value, Word width) ->
      (match word_bounds (Typed (value, Word width)) with
       | Some (low, high) when Nat_big_num.equal low high ->
           Some ("word" ^ string_of_int width, Nat_big_num.to_string low)
       | _ -> None)
  | Typed (value, Enum name) ->
      (* A helper's returned constructor can be behind lexical bindings.
         Resolve those bindings with their original scope, using the same
         capture-free analysis as record fields. The backing helper call and
         its argument evaluation remain in the emitted term. Unknown values,
         partial initialization and control markers establish no literal. *)
      (match arithmetic_key value with
       | Some (Atom constructor)
           when String.starts_with ~prefix:"sail_hl_ctor_" constructor ->
           Some ("enum:" ^ name, constructor)
       | _ -> None)
  | Typed (value, _) -> literal_key value
  | String_literal value -> Some ("string", value)
  | Atom ("T" | "F" as value) -> Some ("bool", if value = "T" then "true" else "false")
  | _ -> None

(* A checked singleton Boolean type can establish truth when the runtime
   interval analysis is coarser than Sail's numeric facts. Consult it only
   after translating/evaluating the operand: neither its type nor its
   proposition licenses skipping that operand's effects or failures.
   An explicit translated literal takes priority over any source fact. *)
let evaluated_boolean_truth ctx expression value =
  match boolean_literal value with
  | Some _ as truth -> truth
  | None ->
      let env = Type_check.env_of expression in
      (match Type_check.destruct_atom_bool env (Type_check.typ_of expression) with
       | Some proposition when prove_specialized ctx env proposition -> Some true
       | Some proposition when prove_specialized ctx env (nc_not proposition) ->
           Some false
       | _ -> None)

let rec term_atom term =
  match boolean_literal term with
  | Some true -> Some "T" | Some false -> Some "F"
  | None -> (match term with
      | Atom name -> Some name | Typed (t, _) -> term_atom t | _ -> None)

let canonical_literal value =
  match literal_key value with
  | Some ("int", _) -> Typed (integer (Option.get (integer_literal value)), Int)
  | Some ("bool", _) -> Typed (Atom (if Option.get (boolean_literal value) then "T" else "F"), Bool)
  | Some ("empty-bits", _) -> Typed (Atom "one", Empty_bits)
  | Some ("string", bytes) -> Typed (String_literal bytes, String_type)
  | Some (kind, constructor) when String.starts_with ~prefix:"enum:" kind ->
      (* A shared helper can establish a constructor while printing a local
         call-result variable. A control-flow join must retain the known
         constructor, not that discovery-only variable's lexical scope. *)
      Typed (Atom constructor, Enum (String.sub kind 5 (String.length kind - 5)))
  | Some (kind, decimal) when String.starts_with ~prefix:"word" kind ->
      (match value with
       | Typed (_, Word width) -> Typed (App ("word", [Atom decimal]), Word width)
       | _ -> value)
  | _ -> value

(* A fresh binding keeps established facts, not the old variable name.
   Tuple projections retain independent field facts, including initialization
   masks. None of these facts replaces evaluation of the backing term. *)
let rec alias_value backing value =
  (* A pure helper can return a record through lexical lets rather than a
     bare tuple. Recover its fields by capture-free let substitution, using
     the checked result type to restore field types. Keep the complete
     evaluated value as backing; this is evidence, not emitted evaluation.
     Never normalize away a partial-initialization mask. *)
  let value = if contains_partial value then value else
    let fields = match value with
      | Typed (_, Record fields) -> Some (List.map snd fields)
      | Typed (_, Tuple fields) -> Some fields
      | _ -> None in
    (* The substituted key drops type annotations, and with them the word
       bounds of its fields. The returned tuple under the helper's lets
       still records each field's established bounds; keep those. *)
    let rec returned_fields = function
      | Typed (value, _) | Shared_value (_, value) | Let (_, _, value) ->
          returned_fields value
      | Tuple_term values -> Some values
      | _ -> None in
    match fields with
    | Some fields ->
        (match arithmetic_key value with
         | Some (Tuple_term values) when List.length fields = List.length values ->
             let bounds = match returned_fields value with
               | Some returned when extended_evaluation () &&
                   List.length returned = List.length values ->
                   List.map value_bounds returned
               | _ -> List.map (fun _ -> None) values in
             Shared_value (value,
               Tuple_term (List.map2 (fun (value, bounds) typ ->
                 let value = match bounds with
                   | Some (low, high) -> Bounded_value (value, low, high)
                   | None -> value in
                 Typed (value, typ)) (List.combine values bounds) fields))
         | _ -> value)
    | None -> value in
  match partial_word value, strip_term value with
  | Some (_, width, known), _ -> tracked_word backing width known
  | None, Tuple_term values when List.exists contains_partial values ->
      let rec fields backing = function
        | [] -> []
        | [value] -> [alias_value backing value]
        | value :: rest ->
            alias_value (App ("FST", [backing])) value ::
              fields (App ("SND", [backing])) rest in
      Tuple_term (fields backing values)
  | None, Tuple_term values ->
      let rec fields backing = function
        | [] -> []
        | [value] -> [alias_value backing value]
        | value :: rest ->
            alias_value (App ("FST", [backing])) value ::
              fields (App ("SND", [backing])) rest in
      Shared_value (backing, Tuple_term (fields backing values))
  | None, _ when Option.is_some (string_literal value) ->
      (* Keep the evaluated binding in generated code. Copying its literal
         bytes into every argument and comparison made FPCR's implementation
         queries megabytes long. Shared_value retains the exact bytes for
         static equality without repeating their HOL character-list value. *)
      Shared_value (backing, canonical_literal value)
  | None, _ when Option.is_some (literal_key value) -> canonical_literal value
  | None, App (("INL" | "INR" as constructor), [payload])
      when (match value with
            | Typed (_, Binary_variant _) -> true
            | Typed (_, Option_type _) -> extended_evaluation ()
            | _ -> false) ->
      (* Keep the evaluated sum as the backing value. Constructor identity
         permits a checked match to select one arm; its payload comes from
         that same captured value, not a reevaluation of its source. *)
      Shared_value (backing, App (constructor, [
        alias_value (App ((if constructor = "INL" then "OUTL" else "OUTR"),
          [backing])) payload]))
  | _ -> retain_bounds backing value

(* Inserting a slice does not observe the bits it overwrites. Retain exactly
   the untouched known base bits and the assigned inserted bits. A dynamic
   offset is safe here only when both inputs are fully initialized. *)
let insert_word loc base_width width base inserted static position
    base_error inserted_error dynamic_error =
  let backing expected error value = match partial_word value with
    | Some (backing, actual, known) when actual = expected -> backing, known
    | Some _ -> fail loc error
    | None -> value, List.init expected Fun.id in
  let base, base_known = backing base_width base_error base
  and inserted, inserted_known = backing width inserted_error inserted in
  let known = match static with
    | Some low ->
        let high = low + width - 1 in
        List.filter (fun bit -> bit < low || bit > high) base_known @
          List.map ((+) low) inserted_known
    | None ->
        if List.length base_known <> base_width || List.length inserted_known <> width then
          fail loc dynamic_error;
        List.init base_width Fun.id in
  App ("word_insert", [base; Tuple_term [position; nat width]; inserted]), known

(* Transport established literal/range information through source bindings.
   Keep source type-variable scope and HOL local-value aliases synchronized;
   only a single known value authorizes literal branch specialization. *)
let rec static_numeric_binding ctx pat value =
  let bind kid value ctx =
    let ctx = match integer_bounds value with
      | Some (low, high) ->
          let facts = [nc_lteq (nconstant low) (nvar kid);
                       nc_lteq (nvar kid) (nconstant high)] in
          {ctx with numeric_facts = facts @ ctx.numeric_facts}
      | None -> ctx in
    match integer_literal value with
    | None -> ctx
    | Some value ->
        let value = try Some (Nat_big_num.to_int value) with _ -> None in
        (match value with
         | None -> ctx
         | Some value ->
             let name = kid_name kid in
             {ctx with widths = (name, value) :: List.remove_assoc name ctx.widths}) in
  match pat with
  | P_aux (P_typ (_, pat), _) -> static_numeric_binding ctx pat value
  | P_aux (P_var (pat, _), _) -> static_numeric_binding ctx pat value
  | P_aux (P_id _, _) ->
      (* Ordinary lets can open an existential integer result without an
         explicit type-variable pattern. Bind that checked witness to the
         evaluated value, not to a guessed width or the source variable name. *)
      (match singleton_pattern_variable pat with
       | Some kid -> bind kid value ctx
       | None -> ctx)
  | P_aux (P_tuple pats, _) ->
      (match strip_term value with
       | Tuple_term values when List.length pats = List.length values ->
           List.fold_left2 static_numeric_binding ctx pats values
       | _ -> ctx)
  | _ -> ctx

(* A named tuple has the same initialization evidence as its fields.
   A helper's checked tuple type cannot make its unknown bits readable. *)
let rec literal_bindings pat value locals =
  match pat with
  | P_aux ((P_typ (_, pat) | P_var (pat, _)), _) -> literal_bindings pat value locals
  | P_aux (P_id id, _) when contains_partial value ->
      let name = string_of_id id in
      let binding = match List.assoc_opt name locals with
        | Some binding -> alias_value binding value
        | None -> fail (id_loc id) "partial formal binding has no local target" in
      (name, binding) :: List.remove_assoc name locals
  | P_aux (P_id id, _) when Option.is_some (literal_key value) ->
      let name = string_of_id id in
      let value = alias_value (List.assoc name locals) value in
      (name, value) :: List.remove_assoc name locals
  | P_aux (P_id id, _) when
      (match value, strip_term value with
       | Typed (_, (Record _ | Tuple _)), _ | _, Tuple_term _ -> true
       | _ -> false) ->
      let name = string_of_id id in
      (name, alias_value (List.assoc name locals) value) :: List.remove_assoc name locals
  | P_aux (P_id id, _) when
      (match value with
       | Typed (_, Binary_variant _) -> true
       | Typed (_, Option_type _) -> extended_evaluation ()
       | _ -> false) ->
      let name = string_of_id id in
      (name, alias_value (List.assoc name locals) value) :: List.remove_assoc name locals
  | P_aux (P_id id, _) when Option.is_some (value_bounds value) ->
      let name = string_of_id id in
      let backing = List.assoc name locals in
      (name, retain_bounds backing value) :: List.remove_assoc name locals
  | P_aux (P_tuple pats, _) ->
      (match strip_term value with
       | Tuple_term values when List.length pats = List.length values ->
           List.fold_left2 (fun locals pat value -> literal_bindings pat value locals)
             locals pats values
       | _ -> locals)
  | _ -> locals

(* Sail represents its short-circuit operators by And_bool/Or_bool AST
   identifiers. Ordinary function calls still evaluate every argument,
   even if their names or external symbols resemble these operators.
   Check the entire application before selecting a reachable operand. *)
let short_circuit_operands ctx exp id operands =
  let loc = exp_loc exp in
  match operands with
  | [left; right] when exp_type ctx.widths exp = Bool &&
      exp_type ctx.widths left = Bool && exp_type ctx.widths right = Bool ->
      used_primitives := string_of_id id :: !used_primitives;
      left, right
  | _ -> fail loc "short-circuit operators require two Boolean operands and result"

(* Record values use products in declaration order. Construction still
   evaluates fields in the order of the checked source E_struct node.
   Validate the entire field set before visiting any values; a projected
   upstream record cannot be constructed by dropping its omitted fields.
   The one construction contract: a retirement relation keeps the trap and
   excinfo fields of RV32's ExceptionContext (hol_type), as ECALL builds
   it. Every declared field is still evaluated; the others are dropped. *)
let record_construction_fields ctx exp fields =
  let loc = exp_loc exp in
  let env = Type_check.env_of exp in
  let contract = match Type_check.Env.base_typ_of env (Type_check.typ_of exp) with
    | Typ_aux (Typ_id id, _) when !normal_retirement &&
          !upstream_architecture = Some "rv32" &&
          string_of_id id = "ExceptionContext" && Type_check.Env.is_record id env ->
        Some (List.map (fun (_, field) -> string_of_id field)
          (snd (Type_check.Env.get_record id env)))
    | _ -> None in
  if contract = None && observes_projected_payload env (Type_check.typ_of exp) then
    fail loc "projected upstream records require an explicit construction contract";
  let order = match exp_type ctx.widths exp with
    | Record order -> order
    | _ -> fail loc "struct construction requires a supported record type" in
  let declared = Option.value contract ~default:(List.map fst order) in
  let fields = List.map (fun (FE_aux (FE_fexp (id, value), _)) ->
    string_of_id id, value) fields in
  let names = List.map fst fields in
  if List.length names <> List.length declared ||
     List.sort_uniq String.compare names <> List.sort String.compare declared then
    fail loc "record construction requires every declared field exactly once";
  List.iter (fun (name, value) ->
    match List.assoc_opt name order with
    | Some typ when exp_type ctx.widths value <> typ ->
        fail (exp_loc value) ("record field type disagrees with its declaration: " ^ name)
    | _ -> ()
  ) fields;
  order, fields

let record_field loc fields id value =
  let name = string_of_id id in
  let rec project fields value = match fields with
    | [(last, _)] when last = name -> value
    | (first, _) :: rest ->
        if first = name then App ("FST", [value])
        else project rest (App ("SND", [value]))
    | _ -> fail loc ("unknown record field " ^ name) in
  let backing = project fields value in
  match strip_term value with
  | Tuple_term values when List.length values = List.length fields ->
      alias_value backing (List.assoc name (List.combine (List.map fst fields) values))
  | _ -> backing

(* A functional record update evaluates its base before the listed fields.
   Only named fields change; omitted fields retain the evaluated base value.
   Projected architecture records cannot use this general representation. *)
let record_update_fields ctx exp base fields =
  let loc = exp_loc exp in
  if observes_projected_payload (Type_check.env_of exp) (Type_check.typ_of exp) then
    fail loc "projected upstream records require an explicit update contract";
  let order = match exp_type ctx.widths exp with
    | Record order when exp_type ctx.widths base = Record order -> order
    | _ -> fail loc "record update requires the same supported base/result type" in
  let fields = List.map (fun (FE_aux (FE_fexp (id, value), _)) ->
    string_of_id id, value) fields in
  let names = List.map fst fields in
  if List.length names <> List.length (List.sort_uniq String.compare names) ||
     List.exists (fun name -> not (List.mem_assoc name order)) names then
    fail loc "record update requires unique declared fields";
  List.iter (fun (name, value) ->
    if exp_type ctx.widths value <> List.assoc name order then
      fail (exp_loc value) ("record update field type disagrees with its declaration: " ^ name)
  ) fields;
  order, fields

(* Decode finite word matches once, then validate before choosing a known
   matched value. The two policies stay distinct: <=4 bits requires each exact
   value once; 5..8 bits admits ordered overlapping masks. A final default in
   the exact policy expands only over missing values, preserving its old
   branch order. Guarded clauses are refused. *)
(* Decode selectors can be integers rather than words or enums. Select a
   source clause only when its already evaluated value is exactly known.
   Retain source order and reject guarded/binding patterns or an unknown
   selector, rather than manufacture an exhaustiveness/default rule. *)
(* A Boolean match is a conditional. Use the first unguarded true, false
   or wildcard clause for each truth value, in source order; a known
   condition selects its clause statically. *)
let boolean_match loc clauses value branch =
  let rec pattern = function
    | P_aux ((P_typ (_, pat) | P_var (pat, _)), _) -> pattern pat
    | P_aux (P_lit (L_aux (L_true, _)), _) -> Some true
    | P_aux (P_lit (L_aux (L_false, _)), _) -> Some false
    | P_aux (P_wild, _) -> None
    | _ -> fail loc "Boolean matches require true, false or wildcard patterns" in
  let cases = List.map (function
    | Pat_aux (Pat_exp (pat, body), _) -> pattern pat, body
    | _ -> fail loc "guarded Boolean matches are unsupported") clauses in
  let clause truth =
    match List.find_opt (fun (selected, _) ->
      selected = None || selected = Some truth) cases with
    | Some (_, body) -> body
    | None -> fail loc "Boolean match has no clause for a truth value" in
  match boolean_literal value with
  | Some truth -> branch (clause truth)
  | None -> Cond (value, branch (clause true), branch (clause false))

let constant_integer_match loc clauses value branch =
  let selected = match integer_literal value, value_bounds value with
    | Some value, _ -> value
    | None, Some (low, high) when Nat_big_num.equal low high -> low
    | _ -> fail loc "integer matches require a statically known selector" in
  let rec pattern = function
    | P_aux ((P_typ (_, pat) | P_var (pat, _)), _) -> pattern pat
    | P_aux (P_lit (L_aux (L_num number, _)), _) -> Some number
    | P_aux (P_wild, _) -> None
    | _ -> fail loc "integer matches require numeric literals or a final wildcard" in
  let cases = List.mapi (fun index -> function
    | Pat_aux (Pat_exp (pat, body), _) ->
        let value = pattern pat in
        if value = None && index <> List.length clauses - 1 then
          fail loc "integer match wildcard must be final";
        value, body
    | _ -> fail loc "guarded integer matches are unsupported") clauses in
  let rec select = function
    | [] -> fail loc "integer match has no clause for its known selector"
    | (Some number, body) :: _ when Nat_big_num.equal number selected -> branch body
    | (None, body) :: _ -> branch body
    | _ :: rest -> select rest in
  select cases

let word_match loc n clauses value branch =
  let exact = n <= 4 and maximum = (1 lsl n) - 1 in
  let rec strip_pattern (P_aux (aux, _) as pat) = match aux with
    | P_typ (_, inner) | P_var (inner, _) -> strip_pattern inner
    | _ -> pat in
  let rec wildcard = function
    | P_aux (P_typ (_, pat), _) -> wildcard pat
    | P_aux (P_wild, _) -> true
    | _ -> false in
  let decode width digits =
    let bits = BitList.of_bin_lit digits in
    if List.length bits <> width then
      fail loc (if exact then "bit match literal width mismatch"
                else "ordered bit match literal width mismatch");
    Nat_big_num.to_int (Sail_lib.uint bits) in
  let unsupported clause =
    fail loc ((if exact then "bit matches require unguarded binary literal cases: "
      else "ordered bit matches reject guarded patterns: ") ^
      string_of_pexp (Type_check.strip_pexp clause)) in
  let pattern_mask pat =
    let pat = if exact then pat else strip_pattern pat in
    match pat with
    | P_aux (P_lit (L_aux (L_bin digits, _)), _) -> maximum, decode n digits
    | _ when exact && wildcard pat -> 0, 0
    | P_aux (P_wild, _) when not exact -> 0, 0
    | P_aux (P_vector pats, _) when not exact && List.length pats = n ->
        List.fold_left (fun (mask, bits) pat ->
          match strip_pattern pat with
          | P_aux (P_wild, _) -> mask lsl 1, bits lsl 1
          | P_aux (P_lit (L_aux (L_bin digits, _)), _) ->
              (mask lsl 1) lor 1, (bits lsl 1) lor decode 1 digits
          | _ -> fail loc "ordered bit-vector patterns require one-bit literals or wildcards"
        ) (0, 0) pats
    | _ -> fail loc "ordered bit matches require binary literals, vector masks or a final wildcard" in
  let cases = List.mapi (fun index clause -> match clause with
    | Pat_aux (Pat_exp (pat, body), _) ->
        let mask, bits = if exact then
            (match pat with
             | P_aux (P_lit (L_aux (L_bin _, _)), _) -> pattern_mask pat
             | _ when wildcard pat -> 0, 0
             | _ -> unsupported clause)
          else pattern_mask pat in
        if mask = 0 && index <> List.length clauses - 1 then
          (if exact then unsupported clause else fail loc "ordered bit match default must be final");
        mask, bits, body
    | Pat_aux (Pat_when _, _) -> unsupported clause
  ) clauses in
  let all = List.init (maximum + 1) Fun.id in
  let cases = if exact then begin
    let present = List.filter_map (fun (mask, bits, _) ->
      if mask = maximum then Some bits else None) cases in
    let missing = List.filter (fun candidate -> not (List.mem candidate present)) all in
    let cases = List.concat_map (fun (mask, bits, body) ->
      if mask = 0 then List.map (fun bits -> maximum, bits, body) missing
      else [mask, bits, body]) cases in
    if List.sort Int.compare (List.map (fun (_, bits, _) -> bits) cases) <> all then
      fail loc "bit match must contain every value exactly once";
    cases
  end else begin
    let masks = List.map (fun (mask, bits, _) -> mask, bits) cases in
    if List.length (List.sort_uniq compare masks) <> List.length masks then
      fail loc "ordered bit match contains duplicate patterns";
    cases
  end in
  let matches candidate (mask, bits, _) = candidate land mask = bits in
  if not exact && not (List.for_all (fun candidate -> List.exists (matches candidate) cases) all) then
    fail loc "ordered bit match must cover every possible value";
  let rec branches = function
    | [] -> fail loc "empty ordered bit match"
    | [_, _, body] -> branch body
    | (mask, bits, body) :: rest ->
        let masked = if mask = maximum then value else
          App ("word_and", [value; Typed (App ("word", [nat mask]), Word n)]) in
        Cond (Infix ("=", masked, Typed (App ("word", [nat bits]), Word n)),
              branch body, branches rest) in
  match literal_key value with
  | Some (kind, decimal) when kind = "word" ^ string_of_int n ->
      let _, _, body = List.find (matches (int_of_string decimal)) cases in
      branch body
  | _ -> branches cases

(* A match on a tuple of words, such as FENCE's
     match (pred[1 .. 0], succ[1 .. 0]) { (0b11, 0b11) => ..., (_, 0b00) => () }
   tests its clauses in source order. Each component is a binary literal or
   a wildcard. The words have at most 8 bits in all, and the clauses must
   cover every value, so the last clause needs no test. *)
let tuple_word_match loc widths clauses value branch =
  if List.fold_left (+) 0 widths > 8 then
    fail loc "tuple bit matches support at most 8 bits";
  let rec strip (P_aux (aux, _) as pat) = match aux with
    | P_typ (_, inner) -> strip inner
    | _ -> pat in
  let component width pat = match strip pat with
    | P_aux (P_wild, _) -> None
    | P_aux (P_lit (L_aux (L_bin digits, _)), _) ->
        let bits = BitList.of_bin_lit digits in
        if List.length bits <> width then fail loc "tuple bit match literal width mismatch";
        Some (Nat_big_num.to_int (Sail_lib.uint bits))
    | _ -> fail loc "tuple bit matches require binary literals or wildcards" in
  let cases = List.map (function
    | Pat_aux (Pat_exp (pat, body), _) ->
        (match strip pat with
         | P_aux (P_tuple pats, _) when List.length pats = List.length widths ->
             List.map2 component widths pats, body
         | _ -> fail loc "tuple bit matches require tuple patterns")
    | Pat_aux (Pat_when _, _) -> fail loc "guarded tuple bit matches are unsupported"
  ) clauses in
  let matches candidate (pattern, _) =
    List.for_all2 (fun value bits -> bits = None || bits = Some value) candidate pattern in
  let candidates = List.fold_right (fun width tails ->
    List.concat_map (fun tail -> List.init (1 lsl width) (fun value -> value :: tail)) tails)
    widths [[]] in
  if not (List.for_all (fun candidate -> List.exists (matches candidate) cases) candidates) then
    fail loc "tuple bit match must cover every possible value";
  let names = List.map (fun width -> Typed (Atom (fresh ()), Word width)) widths in
  let rec branches = function
    | [] -> fail loc "empty tuple bit match"
    | [_, body] -> branch body
    | (pattern, body) :: rest ->
        let tests = List.concat (List.map2 (fun (name, width) bits -> match bits with
          | Some bits -> [Infix ("=", name, Typed (App ("word", [nat bits]), Word width))]
          | None -> []) (List.combine names widths) pattern) in
        let condition = match tests with
          | [] -> Atom "T"
          | first :: others -> List.fold_left (fun left right ->
              Infix ("/\\", left, right)) first others in
        Cond (condition, branch body, branches rest) in
  Let (Tuple_term names, value, branches cases)

(* Translate value expressions using checked types and the current bindings.
   State-changing evaluation goes through computation below.
   Static branch selection uses established literal values; otherwise both
   reachable branches must translate. Unsupported forms are rejected. *)
(* HOL's registers :> element (word i) for an index proved in 0..15. *)
let x86_gpr_element ctx index evaluated_index message =
  require_integer_interval ctx index evaluated_index 0 15 message;
  Infix (":>", Atom "registers", App ("element", [
    Typed (App ("iword", [evaluated_index]), Word 4)]))

let x86_gpr ctx exp width index value evaluated_index =
  let loc = exp_loc exp in
  if constant_index ctx width <> 64 || exp_type ctx.widths index <> Int ||
     (match value with None -> exp_type ctx.widths exp <> Word 64
      | Some value -> exp_type ctx.widths value <> Word 64 ||
                      exp_type ctx.widths exp <> Unit) then
    fail loc "x86 register interpretation supports only full-width 64-bit accesses";
  x86_gpr_element ctx index evaluated_index
    "x86 register index is not proved in 0..15"

(* REMS's read_gpr(idx) and write_gpr(idx, value) are cuts. Their removed
   bodies select rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8..r15 for
   idx = 0..15, which is HOL's numbering of registers :> element; the
   numbering is checked against the source bodies before they are cut.
   The index must be proved in 0..15 and the value must have 64 bits. *)
let x86_rems_gpr ctx exp index value evaluated_index =
  let loc = exp_loc exp in
  if exp_type ctx.widths index <> Int ||
     (match value with None -> exp_type ctx.widths exp <> Word 64
      | Some value -> exp_type ctx.widths value <> Word 64 ||
                      exp_type ctx.widths exp <> Unit) then
    fail loc "REMS register interpretation requires an integer index and 64-bit value";
  used_primitives := "x86-REMS-GPR-access" :: !used_primitives;
  x86_gpr_element ctx index evaluated_index
    "REMS register index is not proved in 0..15"

(* The source GPR array is the existing bank of sixteen 64-bit registers.
   Interpret only direct, checked element accesses. The source read/write
   helpers retain their slices, REX byte selection and LongMode test; an
   aggregate array value or alias is not given a new HOL representation.

   An element read captures the bank before evaluating its index. A partial
   write instead reads its unchanged bits after the RHS has run, just like
   the ordinary assignment traversal below. Neither operation adds a
   separate reg_GPR component or changes any instruction calculation. *)
let x86_bank_register ctx env id =
  if !upstream_architecture <> Some "x86" ||
     !state_type <> "x86state" ||
     not (x86_binds (X86.Gpr_bank (string_of_id id))) ||
     List.mem_assoc (string_of_id id) ctx.locals ||
     (match Type_check.Env.lookup_id id env with Register _ -> false | _ -> true)
  then false else begin
    let declared = Type_check.Env.get_register id env in
    (match Type_check.destruct_vector env declared with
     | Some (length, element) when
         get_nexp_constant (nexp_simp length) = Some (Big_int.of_int 16) &&
         Option.bind (Type_check.destruct_bitvector env element)
           (fun width -> get_nexp_constant (nexp_simp width)) =
             Some (Big_int.of_int 64) -> ()
     | _ -> fail (id_loc id)
         "x86 raw GPR bank requires its declared vector(16,bits(64))");
    if ctx.state = None then
      fail (id_loc id) "x86 raw GPR bank requires a stateful instruction";
    used_primitives := "x86-raw-GPR-bank" :: !used_primitives;
    true
  end

let rec x86_bank_base ctx = function
  | E_aux (E_typ (_, value), _) -> x86_bank_base ctx value
  | E_aux (E_id id, _) as value ->
      x86_bank_register ctx (Type_check.env_of value) id
  | _ -> false

let rec x86_bank_target ctx = function
  | LE_aux ((LE_id id | LE_typ (_, id)), _) as target ->
      x86_bank_register ctx (Type_check.env_of_lexp target) id
  | _ -> false

let x86_bank_component ctx index evaluated_index =
  if exp_type ctx.widths index <> Int then
    fail (exp_loc index) "x86 raw GPR index requires an integer";
  x86_gpr_element ctx index evaluated_index
    "x86 raw GPR index is not proved in 0..15"

let x86_bank_read ctx exp id base =
  if string_of_id id <> "plain_vector_access" || not (x86_bank_base ctx base)
  then false else begin
    let env = Type_check.env_of exp in
    if is_defined_function (string_of_id id) ||
       not (Type_check.Env.is_pure_extern id env) ||
       not (Type_check.Env.is_extern id env "interpreter") ||
       Type_check.Env.get_extern id env "interpreter" <> "access" ||
       exp_type ctx.widths exp <> Word 64 then
      fail (exp_loc exp) "x86 raw GPR read requires the checked vector access";
    true
  end

(* These components read the low bits and zero all higher bits on write,
   matching the source read_simd/write_simd operations. This is not a
   low-vector observation projection: all 32 full 512-bit registers remain. *)
let x86_simd ctx exp width index value evaluated_index =
  let loc = exp_loc exp in
  let width = constant_index ctx width in
  if not (List.mem width [128; 256]) || exp_type ctx.widths index <> Int ||
     (match value with None -> exp_type ctx.widths exp <> Word width
      | Some value -> exp_type ctx.widths value <> Word width ||
                      exp_type ctx.widths exp <> Unit) then
    fail loc "x86 SIMD interpretation requires a checked 128/256-bit access";
  require_integer_interval ctx index evaluated_index 0 31
    "x86 SIMD register index is not proved in 0..31";
  App ("SIMD" ^ string_of_int width, [
    App ("Simdreg", [Typed (App ("iword", [evaluated_index]), Word 5);
                     Atom ("Lower_" ^ string_of_int width)])])

(* Calls of value-recursive helpers reachable from a branch without
   passing a binder. Their free variables therefore have the meaning they
   have at the enclosing conditional. *)
let rec unbound_recursive_calls (E_aux (aux, _) as exp) =
  match aux with
  | E_app (id, args) ->
      (if List.mem (string_of_id id) !value_recursive_functions then [exp] else []) @
      List.concat_map unbound_recursive_calls args
  | E_typ (_, value) -> unbound_recursive_calls value
  | E_tuple values -> List.concat_map unbound_recursive_calls values
  | E_if (c, t, e) -> List.concat_map unbound_recursive_calls [c; t; e]
  | _ -> []

let common_recursive_call yes no =
  let key exp = string_of_exp (Type_check.strip_exp exp) in
  let others = List.map key (unbound_recursive_calls no) in
  List.find_opt (fun call -> List.mem (key call) others) (unbound_recursive_calls yes)

let rec replace_common_call shared replacement (E_aux (aux, annotation) as exp) =
  let key exp = string_of_exp (Type_check.strip_exp exp) in
  let replace = replace_common_call shared replacement in
  match aux with
  | E_app _ when key exp = key shared -> replacement
  | E_app (id, args) -> E_aux (E_app (id, List.map replace args), annotation)
  | E_typ (typ, value) -> E_aux (E_typ (typ, replace value), annotation)
  | E_tuple values -> E_aux (E_tuple (List.map replace values), annotation)
  | E_if (c, t, e) -> E_aux (E_if (replace c, replace t, replace e), annotation)
  | _ -> exp

(* ctx.functions holds every function body of the prepared program. Find a
   callee through an index of the current list; the first binding of a name
   wins, as with List.find_opt. *)
let function_index = ref ([], Hashtbl.create 1)
let find_function functions name =
  let known, _ = !function_index in
  if known != functions then begin
    let index = Hashtbl.create (2 * List.length functions + 1) in
    List.iter (fun ((function_name, _, _) as entry) ->
      if not (Hashtbl.mem index function_name) then Hashtbl.add index function_name entry)
      functions;
    function_index := (functions, index)
  end;
  Hashtbl.find_opt (snd !function_index) name

(* The Sail side of a call's interpretation, and the placeholders for its
   arguments. values are the translated arguments. A unit argument is not
   shown, an integer or Boolean literal is shown by its value and an enum
   constructor by its name; any other argument is a letter, the same
   letter for arguments with the same translation. *)
let call_placeholders ctx name arguments values =
  let letters = ref [] in
  let shown = List.concat (List.map2 (fun argument value ->
    if exp_type ctx.widths argument = Unit then []
    else match literal_key value with
      | Some (("int" | "bool"), literal) -> [literal]
      | Some (kind, constructor) when String.starts_with ~prefix:"enum:" kind ->
          let enum = String.sub kind 5 (String.length kind - 5) in
          let members = try Type_check.Env.get_enum (mk_id enum) (Type_check.env_of argument)
            with _ -> [] in
          (match List.find_opt (fun member ->
             ctor_symbol (string_of_id member) = constructor) members with
           | Some member -> [string_of_id member]
           | None -> [constructor])
      | _ ->
          match List.find_opt (fun (known, _) -> compare known value = 0) !letters with
          | Some (_, letter) -> [letter]
          | None ->
              let letter = String.make 1 (Char.chr (Char.code 'a' + List.length !letters)) in
              letters := (value, letter) :: !letters;
              [letter]) arguments values) in
  name ^ "(" ^ String.concat ", " shown ^ ")", List.rev !letters

let rec pure ctx (E_aux (aux, (loc, _)) as exp) =
  let ty = exp_type ctx.widths exp in
  let t =
    match aux with
    | E_id id ->
        if List.mem (string_of_id id) ctx.uninitialized then
          fail loc ("read of an undefined local before assignment: " ^ string_of_id id);
        (match List.assoc_opt (string_of_id id) ctx.locals with
         | Some t -> t
         | None when Type_check.Env.is_register id (Type_check.env_of exp) ->
             if !upstream_architecture = Some "aarch64" && string_of_id id = "PSTATE" then
               fail loc "whole upstream PSTATE reads are unsupported; use explicit fields";
             (match assumed_register_value ctx (Type_check.env_of exp) id with
              | Some value -> value
              | None -> match x86_flag loc (Type_check.env_of exp) id, ctx.state with
              | Some flag, Some state ->
                  let value = App ("word", [App ("bitval", [App ("read", [flag; state])])]) in
                  record_value ctx ["x86-six-Boolean-flags"] (string_of_id id) [] value;
                  value
              | Some _, None -> fail loc "x86 flag read requires a stateful instruction"
              | None, _ -> register loc ctx id ty)
         | None when Type_check.is_enum_member id (Type_check.env_of exp) ->
             Atom (ctor_symbol (string_of_id id))
         | None when List.mem_assoc (string_of_id id) ctx.globals ->
             let name = string_of_id id in
             if List.mem name ctx.stack then fail loc ("recursive global " ^ name);
             used_globals := name :: !used_globals;
             definition_sources := name :: !definition_sources;
             (* The initializer is translated at each use. Sail rejects
                effectful top-level lets; translate it without a state too. *)
             pure {ctx with locals = []; stack = name :: ctx.stack;
                            state = None; entry_state = None}
               (List.assoc name ctx.globals)
         | None -> fail loc ("unbound or unsupported identifier " ^ string_of_id id))
    | E_lit (L_aux (L_num n, _)) -> integer n
    | E_lit (L_aux (L_true, _)) -> Atom "T"
    | E_lit (L_aux (L_false, _)) -> Atom "F"
    | E_lit (L_aux (L_string bytes, _)) -> String_literal bytes
    | E_lit (L_aux (L_unit, _)) -> Atom "one"
    | E_lit (L_aux ((L_bin _ | L_hex _) as lit, _)) ->
        let bits = match lit with
          | L_bin digits -> BitList.of_bin_lit digits
          | L_hex digits -> BitList.of_hex_lit digits
          | _ -> assert false in
        let n = Sail_lib.uint bits in
        if ty = Empty_bits then Atom "one" else
          App ("word", [Atom (Nat_big_num.to_string n)])
    | E_typ (_, e) -> pure ctx e
    | E_sizeof n -> numeric_type_term ctx.widths (Type_check.env_of exp) n
    | E_tuple es -> Tuple_term (List.map (pure ctx) es)
    | E_struct (_, fields) ->
        let order, fields = record_construction_fields ctx exp fields in
        (* As for an update below, each captured field keeps the facts of
           its evaluated value, such as the known high bits of a ModR/M byte
           built from a literal and register fields. *)
        let rec evaluate captured = function
          | [] -> Tuple_term (List.map (fun (name, _) -> List.assoc name captured) order)
          | (name, expression) :: rest ->
              let value = pure ctx expression in
              let variable = Typed (Atom (fresh ()), exp_type ctx.widths expression) in
              let field = if extended_evaluation ()
                then alias_value variable value else variable in
              Let (variable, value, evaluate ((name, field) :: captured) rest) in
        evaluate [] fields
    | E_struct_update (base, fields) ->
        let order, fields = record_update_fields ctx exp base fields in
        let value = pure ctx base in
        let variable = Typed (Atom (fresh ()), ty) in
        let captured_base = alias_value variable value in
        let rec evaluate captured = function
          | [] -> Tuple_term (List.map (fun (name, _) ->
              match List.assoc_opt name captured with
              | Some value -> value
              | None -> record_field loc order (mk_id name) captured_base) order)
          | (name, expression) :: rest ->
              let value = pure ctx expression in
              let variable = Typed (Atom (fresh ()), exp_type ctx.widths expression) in
              Let (variable, value,
                evaluate ((name, alias_value variable value) :: captured) rest) in
        Let (variable, value, evaluate [] fields)
    | E_field (E_aux (E_id register, _), field)
        when Option.is_some (assumed_initial_bit ctx (Type_check.env_of exp) register field) ->
        Option.get (assumed_bit_value ctx (Type_check.env_of exp) register field)
    | E_field (E_aux (E_id register, _), field)
        when !upstream_architecture = Some "aarch64" &&
             string_of_id register = "PSTATE" &&
             not (List.mem_assoc "PSTATE" ctx.locals) ->
        arm_pstate_field loc ctx (Type_check.env_of exp) field
    | E_field (value, id) ->
        (match exp_type ctx.widths value with
         | Record fields ->
             record_field loc fields id (pure ctx value)
         | _ -> fail loc "field access requires a supported record type")
    | E_if (c, t, e) ->
        let condition = pure ctx c in
        let truth = if extended_evaluation ()
          then evaluated_boolean_truth ctx c condition
          else boolean_literal condition in
        (match truth with
         | Some truth ->
             record_selected_branch ctx c truth
               ~by_z3:(boolean_literal condition = None);
             pure ctx (if truth then t else e)
         | None -> branches ctx condition t e pure)
    | E_match (scrutinee, clauses) ->
        check_clause_patterns ctx clauses;
        (match exp_type ctx.widths scrutinee with
         | Result _ -> result_match ctx scrutinee clauses (pure ctx scrutinee) pure
         | Binary_variant ((left, _), (right, _)) ->
             binary_variant_match ctx scrutinee clauses (pure ctx scrutinee) left right pure
         | Option_type _ -> option_match ctx scrutinee clauses (pure ctx scrutinee) pure
         | Unit_variant (_, members) ->
             unit_variant_match ctx members clauses (pure ctx scrutinee) pure
         | Bool when extended_evaluation () ->
             boolean_match loc clauses (pure ctx scrutinee) (pure ctx)
         | _ -> enum_match ctx scrutinee clauses (pure ctx scrutinee) (pure ctx))
    | E_let (p, e, body) ->
        let value = pure ctx e in
        let binding, locals = pattern ctx.widths ctx.locals p in
        let locals = literal_bindings p value locals in
        let scoped = hide_uninitialized
          (static_numeric_binding (numeric_binding_scope ctx p e body) p value) p in
        Let (binding, value, pure {scoped with locals} body)
    | E_block es ->
        let rec sequence = function
          | [] -> Atom "one"
          | [last] -> pure ctx last
          | e :: rest -> Let (Atom (fresh ()), pure ctx e, sequence rest) in
        sequence es
    | E_assert (condition, message) ->
        (match message with
         | E_aux (E_lit (L_aux (L_string _, _)), _) -> ()
         | _ -> fail loc "assertion messages must be literal strings");
        let env = Type_check.env_of condition in
        (* Evaluate the source condition even when its refinement is true.
           A literal result of an inlined body can also establish truth, but
           an unknown primitive or false result must never be discarded. *)
        let value = pure ctx condition in
        let proved = match Type_check.destruct_atom_bool env (Type_check.typ_of condition) with
          | Some constraint_ -> prove_specialized ctx env constraint_
          | None -> false in
        if boolean_literal value = Some false ||
           not (proved || boolean_literal value = Some true) then
          fail loc "pure assertions must be statically proved, not discarded";
        record_proved_assertion ctx exp condition
          ~by_z3:(boolean_literal value <> Some true);
        Let (Atom (fresh ()), value, Atom "one")
    | E_vector [] when ty = Empty_bits -> Atom "one"
    | E_vector [e] ->
        if exp_type ctx.widths e <> Word 1 then fail loc "expected a singleton bitvector";
        pure ctx e
    | E_vector_append (x, y) ->
        concat ctx loc x y (pure ctx x) (pure ctx y)
    | E_app (id, operands) when is_and_bool id || is_or_bool id ->
        let left, right = short_circuit_operands ctx exp id operands in
        let condition = pure ctx left in
        let truth = evaluated_boolean_truth ctx left condition in
        let evaluate_right truth =
          pure (source_comparison_context ctx left condition truth) right in
        let result = if is_and_bool id then
            match truth with
            | Some true -> evaluate_right true
            | Some false -> Atom "F"
            | None -> Cond (condition, evaluate_right true, Atom "F")
          else
            match truth with
            | Some true -> Atom "T"
            | Some false -> evaluate_right false
            | None -> Cond (condition, Atom "T", evaluate_right false) in
        (* A literal result may contain an inlined calculation or a proved
           assertion. Keep its evaluation rather than replacing the entire
           left operand with that result. Symbolic conditions occur once. *)
        if Option.is_some truth then
          Let (Atom (fresh ()), condition, result)
        else result
    | E_app (id, [base; index]) when x86_bank_read ctx exp id base ->
        let index_value = pure ctx index in
        let value = App ("read", [x86_bank_component ctx index index_value;
                                  Option.get ctx.state]) in
        record_value ctx ["x86-raw-GPR-bank"]
          (string_of_exp (Type_check.strip_exp base) ^ "[a]") [index_value, "a"] value;
        value
    | E_app (id, es) -> call ctx exp id es
    | _ -> fail loc ("unsupported pure AST node: " ^ string_of_exp (Type_check.strip_exp exp))
  in let value = Typed (observable_value loc t, ty) in
     Typed (retain_bounds t value, ty)

(* Direct recursion on integers, such as REMS's logcount_int, unfolds
   while every integer argument stays nonnegative, no upper bound grows
   and one shrinks; the base case must then resolve statically. The
   unfolding still fails at the fixed depth and size bounds. Each unfolded
   call is the original body, so the measure only ensures translation
   finishes; it is not an assumption about the result. *)
and recursion_value_measure ctx name pat args =
  (* Evaluating the arguments here only reads their bounds; restore
     fresh names and evidence before the call is translated. *)
  let restore = translation_checkpoint () in
  Fun.protect ~finally:restore @@ fun () ->
  let formals = pattern_names pat in
  List.length formals = List.length args &&
  let measures = List.filter_map (fun (formal, argument) ->
    if exp_type ctx.widths argument <> Int then None else
    Some (Option.bind (List.assoc_opt formal ctx.locals) integer_bounds,
          integer_bounds (pure ctx argument))) (List.combine formals args) in
  let nonnegative = Nat_big_num.greater_equal in
  measures <> [] &&
  List.for_all (function
    | Some (previous_low, previous_high), Some (current_low, current_high) ->
        nonnegative previous_low Nat_big_num.zero &&
        nonnegative current_low Nat_big_num.zero &&
        Nat_big_num.less_equal current_high previous_high
    | _ -> false) measures &&
  List.exists (function
    | Some (_, previous_high), Some (_, current_high) ->
        Nat_big_num.less current_high previous_high
    | _ -> false) measures

and concat ctx loc x y left right =
  match exp_type ctx.widths x, exp_type ctx.widths y with
  | (Word _ | Poly_word _), (Word _ | Poly_word _) -> App ("word_join", [left; right])
  | Empty_bits, (Empty_bits | Word _) ->
      Let (Typed (Atom (fresh ()), Empty_bits), left, right)
  | Word _, Empty_bits ->
      let value = fresh () in
      Let (Atom value, left, Let (Typed (Atom (fresh ()), Empty_bits), right, Atom value))
  | _ -> fail loc "concatenation requires bitvectors"

(* Binding/copying a value need not observe all its bits. This limited path
   propagates a partial local or tuple of partials without calling pure's
   observation checks. Arithmetic, tests and externally visible writes still
   go through the appropriate checks; it is not a general escape hatch. *)
and transfer_value ctx (E_aux (aux, _) as exp) =
  (* Raw copies into a known helper/local are permitted, but retain their
     mask. Foreign primitives, arithmetic, tests and register writes still
     use pure()/observable_value and may not inspect uninitialized bits. *)
  match aux with
  | E_typ (_, value) -> transfer_value ctx value
  | E_id id ->
      (match List.assoc_opt (string_of_id id) ctx.locals with
       | Some value when contains_partial value -> value
       | _ -> pure ctx exp)
  | E_tuple values -> Tuple_term (List.map (transfer_value ctx) values)
  | _ -> pure ctx exp

and partial_slice_context ctx name args =
  match args with
  | (E_aux (E_id id, _) as input) :: positions ->
      (match List.assoc_opt (string_of_id id) ctx.locals with
       | Some value when Option.is_some (partial_word value) ->
           let backing, width, known = Option.get (partial_word value) in
           let high, low = match name, positions with
             | ("bitvector_subrange" | "subrange_bits"), [high; low] ->
                 constant_index ctx high, constant_index ctx low
             | "bitvector_access", [index] ->
                 let index = constant_index ctx index in index, index
             | "slice", [start; length] ->
                 let low = constant_index ctx start in
                 low + constant_index ctx length - 1, low
             | _ -> fail (exp_loc input) "partial words require a statically checked slice" in
           if low < 0 || high < low || high >= width ||
              not (List.for_all (fun bit -> List.mem bit known)
                (List.init (high - low + 1) (fun n -> low + n))) then
             fail (exp_loc input) "read of uninitialized bits in a partial word";
           {ctx with
            locals = (string_of_id id, backing) :: List.remove_assoc (string_of_id id) ctx.locals;
            uninitialized = List.filter ((<>) (string_of_id id)) ctx.uninitialized}
       | _ -> ctx)
  | _ -> ctx

(* Match helpers preserve the declared constructor alternatives in HOL.
   The source must supply the supported exhaustive patterns; a missing or
   unexpected case fails instead of choosing a favorable result.
   translate decides how each branch continues in the caller's mode. *)
and result_match ctx scrutinee clauses value translate =
  let cases = List.map (function
    | Pat_aux (Pat_exp (P_aux (P_app (id, [pat]), _), body), _)
        when List.mem (string_of_id id) ["Ok"; "Err"] ->
        string_of_id id, (pat, body)
    | _ -> fail (exp_loc scrutinee) "only unguarded Ok/Err payload cases are supported"
  ) clauses in
  if List.sort String.compare (List.map fst cases) <> ["Err"; "Ok"] then
    fail (exp_loc scrutinee) "result match must contain Ok and Err exactly once";
  let branch name =
    let pat, body = List.assoc name cases in
    let p, locals = pattern ctx.widths ctx.locals pat in
    Lambda (p, translate {ctx with locals} body) in
  App (!case_name, [branch "Ok"; branch "Err"; value])

(* An exact sum view of a checked, two-constructor union. Validate the entire
   match even when its constructor is known. Select an arm only from retained
   constructor facts for an already evaluated value; unsupported reachable
   arms still fail when the constructor is not known. No payload is erased. *)
and binary_variant_match ctx scrutinee clauses value left right translate =
  let cases = List.map (function
    | Pat_aux (Pat_exp (P_aux (P_app (id, [pat]), _), body), _)
        when List.mem (string_of_id id) [left; right] ->
        string_of_id id, (pat, body)
    | _ -> fail (exp_loc scrutinee) "binary union match requires unguarded payload cases"
  ) clauses in
  if List.sort String.compare (List.map fst cases) <> List.sort String.compare [left; right] then
    fail (exp_loc scrutinee) "binary union match must contain each constructor exactly once";
  let branch name payload =
    let pat, body = List.assoc name cases in
    let p, locals = pattern ctx.widths ctx.locals pat in
    match payload with
    | None -> Lambda (p, translate {ctx with locals} body)
    | Some value ->
        let locals = literal_bindings pat value locals in
        Let (p, value, translate {ctx with locals} body) in
  match strip_term value with
  | App ("INL", [payload]) -> branch left (Some payload)
  | App ("INR", [payload]) -> branch right (Some payload)
  | _ -> App (!case_name, [branch left None; branch right None; value])

and option_match ctx scrutinee clauses value translate =
  let cases = List.map (function
    | Pat_aux (Pat_exp (P_aux (P_app (id, [pat]), _), body), _)
        when string_of_id id = "Some" -> "Some", Some pat, body
    | Pat_aux (Pat_exp (P_aux (P_app (id, ps), _), body), _)
        when string_of_id id = "None" &&
             (ps = [] || List.for_all (function
               | P_aux (P_lit (L_aux (L_unit, _)), _) -> true | _ -> false) ps) ->
        "None", None, body
    | _ -> fail (exp_loc scrutinee) "only unguarded Some/None option cases are supported"
  ) clauses in
  if List.sort String.compare (List.map (fun (name, _, _) -> name) cases) <> ["None"; "Some"] then
    fail (exp_loc scrutinee) "option match must contain Some and None exactly once";
  let branch name =
    let _, pat, body = List.find (fun (n, _, _) -> n = name) cases in
    let p, locals = match pat with
      | Some pat -> pattern ctx.widths ctx.locals pat
      | None -> Typed (Atom (fresh ()), Unit), ctx.locals in
    Lambda (p, translate {ctx with locals} body) in
  (* As for binary unions, a known Some selects its clause; the evaluated
     payload is bound to the Some pattern. *)
  match strip_term value with
  | App ("INR", [payload]) when extended_evaluation () ->
      (match List.find (fun (n, _, _) -> n = "Some") cases with
       | _, Some pat, body ->
           let p, locals = pattern ctx.widths ctx.locals pat in
           let locals = literal_bindings pat payload locals in
           Let (p, payload, translate {ctx with locals} body)
       | _ -> assert false)
  | _ -> App (!case_name, [branch "None"; branch "Some"; value])

and unit_variant_match ctx members clauses value translate =
  let rec branches seen = function
    | [] -> fail Parse_ast.Unknown "unit variant match is not exhaustive"
    | Pat_aux (Pat_exp (P_aux (P_app (id, ps), _), body), _) :: rest ->
        if not (List.exists (fun member -> Id.compare id member = 0) members) ||
           List.exists (fun member -> Id.compare id member = 0) seen ||
           not (ps = [] || List.for_all (function
             | P_aux (P_lit (L_aux (L_unit, _)), _) -> true | _ -> false) ps) then
          fail (id_loc id) "invalid or repeated unit variant constructor pattern";
        let branch = translate ctx body in
        if rest = [] && List.length seen + 1 = List.length members then branch
        else Cond (Infix ("=", value, Atom (ctor_symbol (string_of_id id))),
                   branch, branches (id :: seen) rest)
    | [Pat_aux (Pat_exp (P_aux (P_id id, _), body), _)] ->
        if List.exists (fun member -> Id.compare id member = 0) members then
          fail (id_loc id) "unit variants require constructor applications in patterns";
        translate {ctx with locals = (string_of_id id, value) :: ctx.locals} body
    | _ -> fail Parse_ast.Unknown "only unguarded constructor cases and a final variable are supported"
  in branches [] clauses

and enum_match ctx scrutinee clauses evaluated translate =
  let loc = exp_loc scrutinee in
  let name = match exp_type ctx.widths scrutinee with
    | Enum name -> name
    | _ -> fail loc "only exhaustive enumeration matches are supported" in
  let enum = Type_check.Env.get_enum (mk_id name) (Type_check.env_of scrutinee) in
  let parsed = List.mapi (fun index -> function
    | Pat_aux (Pat_exp (P_aux (P_id id, _), body), _)
        when List.exists (fun member -> Id.compare member id = 0) enum -> Some id, body
    | Pat_aux (Pat_exp (P_aux (P_wild, _), body), _)
        when index = List.length clauses - 1 -> None, body
    | _ -> fail loc "only unguarded enumeration constructor cases are supported"
  ) clauses in
  let named = List.filter_map (fun (id, _) -> id) parsed in
  if List.length named <> List.length (List.sort_uniq Id.compare named) then
    fail loc "enumeration match repeats a constructor";
  let cases = List.concat_map (fun (id, body) -> match id with
    | Some id -> [id, body]
    | None ->
        let missing = List.filter (fun id ->
          not (List.exists (fun present -> Id.compare id present = 0) named)) enum in
        if missing = [] then fail loc "enumeration wildcard covers no remaining constructor";
        List.map (fun id -> id, body) missing
  ) parsed in
  let constructors = List.map (fun (id, _) -> string_of_id id) cases in
  if List.sort String.compare constructors <>
     List.sort String.compare (List.map string_of_id enum) then
    fail loc "enumeration match must contain each constructor exactly once";
  let rec atom = function Atom name -> Some name | Typed (t, _) -> atom t | _ -> None in
  let known = atom evaluated in
  let selected = Option.bind known (fun value ->
    List.find_opt (fun (id, _) -> value = ctor_symbol (string_of_id id)) cases) in
  match selected with
  | Some (_, body) -> translate body
  | None ->
  let value = fresh () in
  (* Validation above expands a wildcard only to check exhaustiveness and
     select a known constructor. Emission follows the original cases: a
     final wildcard is one fallback, not a copy for every enum member.
     Each copy would also duplicate the caller's remaining computation. *)
  let rec branches = function
    | [] -> fail loc "empty enumeration match"
    | [_, body] -> translate body
    | (Some id, body) :: rest ->
        Cond (Infix ("=", Atom value, Atom (ctor_symbol (string_of_id id))),
              translate body, branches rest)
    | (None, _) :: _ -> fail loc "enumeration wildcard must be last" in
  Let (Atom value, evaluated, branches parsed)

(* A pure helper's final return denotes its returned value. Earlier binding
   structure is retained as HOL lets; stateful early returns use computation's
   distinct continuations instead. This path does not implement arbitrary
   source exceptions or recursion. *)
and tail ctx (E_aux (aux, _) as exp) =
  match aux with
  | E_return e -> pure ctx e
  | E_typ (_, e) | E_block [e] -> tail ctx e
  | E_let (p, e, body) ->
      let value = pure ctx e in
      let binding, locals = pattern ctx.widths ctx.locals p in
      let locals = literal_bindings p value locals in
      let scoped = hide_uninitialized
        (static_numeric_binding (numeric_binding_scope ctx p e body) p value) p in
      Let (binding, value, tail {scoped with locals} body)
  | E_if (c, t, e) ->
      let condition = pure ctx c in
      let truth = if extended_evaluation ()
        then evaluated_boolean_truth ctx c condition
        else boolean_literal condition in
      (match truth with
       | Some true -> tail ctx t
       | Some false -> tail ctx e
       | None -> branches ctx condition t e tail)
  | _ -> pure ctx exp

(* Translate both arms of a pure conditional with an unknown condition.
   When both arms call the same value-recursive helper on the same
   arguments, as in REMS's logcount_int:
     if isEven(x) then logcount_int(shr_int(x, 1))
     else logcount_int(shr_int(x, 1)) + 1
   evaluate that call once before the conditional. The call is pure and
   total, and its arguments mean the same in both arms. Otherwise every
   unfolded level would copy the rest of the unfolding into both arms. *)
and branches ctx condition yes no translate =
  match common_recursive_call yes no with
  | None -> Cond (condition, translate ctx yes, translate ctx no)
  | Some shared ->
      let value = pure ctx shared in
      let variable_name = fresh () in
      let variable = Typed (Atom variable_name, exp_type ctx.widths shared) in
      let name = "!hol-light-common-call:" ^ variable_name in
      let E_aux (_, annotation) = shared in
      let replacement = E_aux (E_id (mk_id name), annotation) in
      let inner = {ctx with locals = (name, alias_value variable value) :: ctx.locals} in
      let yes = replace_common_call shared replacement yes
      and no = replace_common_call shared replacement no in
      Let (variable, value, Cond (condition, translate inner yes, translate inner no))

and call ctx exp id args =
  let loc = exp_loc exp in
  let name = string_of_id id in
  (* Defined callees are translated, never replaced by a name-based contract.
     Typechecker instantiations specialize their numeric type variables. *)
  match find_function ctx.functions name with
  | Some (_, body, pat) ->
      if not (Effects.function_is_pure id !effect_info) &&
         not (!normal_retirement || !state_computation) then
        fail loc ("effectful helper call " ^ name ^ " is unsupported");
      used_functions := name :: !used_functions;
      definition_sources := name :: !definition_sources;
      let body, pat = specialize_helper_types ctx exp body pat args in
      (* Concrete callers retain the existing precondition/result checks.
         Generic helper calls retain Sail's checked symbolic interface; each
         callee is translated independently, rather than capturing a caller's
         similarly named width variable or specialized Boolean operand. *)
      let value_measure () = recursion_value_measure ctx name pat args in
      let checked = if not (generic_widths_active ()) then
          Some (specialize_helper ~value_measure ctx exp name body pat args) else None in
      let shared = if Effects.function_is_pure id !effect_info &&
          not (List.mem name !value_recursive_functions) then
          !share_source_function ctx exp id body pat args else None in
      let inline () =
           let ctx' = match checked with Some ctx -> ctx
             | None -> specialize_helper ctx exp name body pat args in
           let p, locals = pattern ctx'.widths [] pat in
           let values = match args with
             | [arg] -> pure ctx arg
             | _ -> Tuple_term (List.map (pure ctx) args) in
           let locals = literal_bindings pat values locals in
           Let (p, values, tail {ctx' with locals} body) in
      (match shared with
       | Some {expression; returns_state = false} ->
           (* restore also resets fresh_index, so names inside the facts
              can recur later. That is safe only because facts never hold
              a Choose, whose binders lower_faults hoists by name. *)
           let restore = translation_checkpoint () in
           let previous = !computing_shared_facts in
           let facts = if generic_widths_active () then None else
             Fun.protect ~finally:(fun () ->
             computing_shared_facts := previous; restore ()) (fun () ->
             computing_shared_facts := true;
             try Some (inline ()) with
             | Reporting.Fatal_error (Reporting.Err_general _) -> None) in
           (match facts with Some facts -> Shared_value (expression, facts)
            | None -> expression)
       | _ -> inline ())
  | None ->
      (* This is the handwritten primitive boundary: ordinary word/integer
         operations and explicit architecture contracts. Keep type, enum,
         constructor and effect checks here in view when auditing a mapping.
         A defined but unsupported helper must not fall through to a contract. *)
      if is_defined_function name then
        fail loc ("unsupported defined helper " ^ name);
      if List.mem name ["eq_any"; "neq_any"; "eq_anything"; "neq_anything"] &&
         List.exists (fun argument -> observes_projected_payload
           (Type_check.env_of argument) (Type_check.typ_of argument)) args then
        fail loc "equality cannot observe omitted upstream payloads";
      let ctx = if List.mem name ["bitvector_subrange"; "subrange_bits"; "bitvector_access"; "slice"]
        then partial_slice_context ctx name args else ctx in
      (* Length is a property of the declared word type, not an observation
         of its possibly undefined bits. The computation path evaluates
         argument helpers before reaching this primitive. *)
      let xs = List.mapi (fun index argument ->
        if name = "bitvector_length" ||
           (name = "set_slice_bits" && List.mem index [2; 4])
        then transfer_value ctx argument else pure ctx argument
      ) args in
      if (List.exists (fun argument -> exp_type ctx.widths argument = Dynamic_bits) args ||
          exp_type ctx.widths exp = Dynamic_bits) &&
         not (List.mem name ["sail_zeros"; "zeros"; "not_vec"; "ZeroExtend0";
                            "replicate_bits"]) then
        fail loc ("unsupported primitive on internal dynamic bitvectors: " ^ name);
      let empty_input = List.exists (fun arg -> exp_type ctx.widths arg = Empty_bits) args in
      let empty_result = exp_type ctx.widths exp = Empty_bits in
      if (empty_input || empty_result) &&
         not (List.mem name ["sail_zeros"; "zeros"; "sail_ones";
           "bitvector_concat"; "bitvector_length"; "replicate_bits";
           "eq_bits"; "neq_bits"; "eq_any"; "neq_any";
           "eq_anything"; "neq_anything"]) then
        fail loc ("unsupported primitive on empty bitvectors: " ^ name);
      if empty_input && List.mem name
          ["eq_bits"; "neq_bits"; "eq_any"; "neq_any"; "eq_anything"; "neq_anything"] &&
         (List.map (exp_type ctx.widths) args <> [Empty_bits; Empty_bits] ||
          exp_type ctx.widths exp <> Bool) then
        fail loc "empty bitvector equality requires equal empty input types and Boolean result";
      let mapping = List.find_map (fun (mapping, clauses) ->
        if name = mapping ^ "_forwards" then Some (mapping, false, clauses)
        else if name = mapping ^ "_backwards" then Some (mapping, true, clauses)
        else None
      ) !mapping_definitions in
      match mapping with
      | Some (mapping, backwards, clauses) ->
          let literal = function
            | MPat_aux (MPat_pat (MP_aux (MP_lit (L_aux (lit, _)), _)), _) -> lit
            | _ -> fail loc "finite mappings require unguarded literal pairs" in
          let cases = List.map (function
            | MCL_aux (MCL_bidir (left, right), _) -> literal left, literal right
            | _ -> fail loc "finite mappings require bidirectional clauses"
          ) clauses in
          let boolean = function L_true -> 1 | L_false -> 0
                                | _ -> fail loc "finite mapping domain must be Boolean" in
          let bit = function
            | L_bin digits ->
                let bits = BitList.of_bin_lit digits in
                if List.length bits <> 1 then fail loc "finite mapping range must be one bit";
                Nat_big_num.to_int (Sail_lib.uint bits)
            | _ -> fail loc "finite mapping range must be one bit" in
          if List.sort Int.compare (List.map (fun (left, _) -> boolean left) cases) <> [0;1] ||
             List.sort Int.compare (List.map (fun (_, right) -> bit right) cases) <> [0;1] then
            fail loc "Boolean/bit mapping must be a total bijection";
          let cases = if backwards then List.map (fun (x,y) -> y,x) cases else cases in
          let term = function L_true -> Typed (Atom "T", Bool)
                            | L_false -> Typed (Atom "F", Bool)
                            | L_bin _ as lit -> Typed (App ("word", [nat (bit lit)]), Word 1)
                            | _ -> assert false in
          used_mappings := (mapping ^ (if backwards then " backwards" else " forwards")) ::
                           !used_mappings;
          (match xs, cases with
           | [value], [(left, right); (_, last)] ->
               Cond (Infix ("=", value, term left), term right, term last)
           | _ -> fail loc "finite mapping takes one argument")
      | None ->
      (* Defined helpers and checked finite mappings above contribute their
         actual bodies. This branch instead supplies primitive contracts.
         Only explicit architecture contracts may interpret an impure
         external call; stateless operations require a pure declaration. *)
      let contracts = match !state_type with
        | "armstate" -> Arm.contracts
        | "x86state" -> (x86_source ()).X86.contracts
        | _ -> Rv32.contracts in
      let state_contract =
        Option.value (List.assoc_opt name contracts) ~default:false &&
        (!state_computation || !state_type = "riscvstate") in
      if not state_contract && not (Effects.function_is_pure id !effect_info) then
        fail loc ("unsupported primitive " ^ name ^
                  ": stateless operations require a pure external declaration");
      used_primitives := name :: !used_primitives;
      let binary op = match xs with [x; y] -> Infix (op, x, y)
        | _ -> fail loc ("wrong primitive arity for " ^ name) in
      let unary f = match xs with [x] -> App (f, [x])
        | _ -> fail loc ("wrong primitive arity for " ^ name) in
      let before = !used_primitives in
      let result = match name, args with
      (* The generic cases use the checked source widths for bounds/equality
         proofs, and the HOL result annotation for its word type. Numeric
         parameters remain evaluated operands; sizeof alone denotes a type
         dimension. Unsupported generic operations use the ordinary checked
         width-specialized path, never an approximate bitvector width. *)
      | ("SignExtend0" | "ZeroExtend0"), [input; width]
          when is_poly_word (exp_type ctx.widths input) ||
               is_poly_word (exp_type ctx.widths exp) ->
          let env = Type_check.env_of exp in
          let input_width = snd (bitvector_argument input)
          and output_width = snd (bitvector_argument exp)
          and requested_width = snd (numeric_argument width) in
          (match input_width, output_width, requested_width with
           | Some input_width, Some output_width, Some requested_width
               when is_word (exp_type ctx.widths input) &&
                    is_word (exp_type ctx.widths exp) &&
                    prove_specialized ctx env
                      (nc_and (nc_lteq input_width output_width)
                        (nc_eq requested_width output_width)) ->
               App ((if name = "SignExtend0" then "word_sx" else "word_zx"),
                    [List.hd xs])
           | _ -> fail loc "generic extension requires matching, nondecreasing source widths")
      | ("sail_zeros" | "zeros" | "sail_ones"), [width]
          when is_poly_word (exp_type ctx.widths exp) ->
          (match snd (numeric_argument width), snd (bitvector_argument exp) with
           | Some requested, Some result when
               prove_specialized ctx (Type_check.env_of exp) (nc_eq requested result) -> ()
           | _ -> fail loc "generic fill requires its exact checked source width");
          if name = "sail_ones" then App ("word_not", [App ("word", [nat 0])])
          else App ("word", [nat 0])
      | "bitvector_length", [input] when is_poly_word (exp_type ctx.widths input) ->
          if exp_type ctx.widths exp <> Int then fail loc "word length requires an integer result";
          App ("&", [word_dimension (exp_type ctx.widths input)])
      | "bitvector_access", [input; index]
          when is_poly_word (exp_type ctx.widths input) ->
          if exp_type ctx.widths index <> Int || exp_type ctx.widths exp <> Word 1 then
            fail loc "generic bit access requires an integer index and one-bit result";
          let width = match snd (bitvector_argument input) with
            | Some width -> width | None -> assert false in
          require_numeric_fact ctx index (fun index ->
            nc_and (nc_lteq (nint 0) index) (nc_lt index width))
            "generic bit access requires proved source bounds";
          App ("word", [App ("bitval", [App ("bit", [
            App ("num_of_int", [List.nth xs 1]); List.hd xs])])])
      | "get_slice_int", [width; value; start]
          when is_poly_word (exp_type ctx.widths exp) ->
          if List.exists (fun input -> exp_type ctx.widths input <> Int) args then
            fail loc "generic integer slices require integer operands";
          (match snd (numeric_argument width), snd (bitvector_argument exp) with
           | Some requested, Some result when
               prove_specialized ctx (Type_check.env_of exp) (nc_eq requested result) -> ()
           | _ -> fail loc "generic integer slice requires its exact source result width");
          require_numeric_fact ctx start (fun start -> nc_lteq (nint 0) start)
            "generic integer slice requires a nonnegative start";
          (* Match the concrete interpretation at a known zero offset.
             Argument evaluation has already retained any source effects. *)
          let shifted = match integer_literal (List.nth xs 2) with
            | Some start when Nat_big_num.equal start Nat_big_num.zero ->
                List.nth xs 1
            | _ -> Infix ("div", List.nth xs 1,
                Infix ("pow", integer (Nat_big_num.of_int 2),
                  App ("num_of_int", [List.nth xs 2]))) in
          App ("iword", [shifted])
      | ("bitvector_subrange" | "subrange_bits"), [input; high; low]
          when is_poly_word (exp_type ctx.widths input) ||
               is_poly_word (exp_type ctx.widths exp) ->
          let input_width = snd (bitvector_argument input)
          and output_width = snd (bitvector_argument exp)
          and high_width = snd (numeric_argument high)
          and low_width = snd (numeric_argument low) in
          (match input_width, output_width, high_width, low_width with
           | Some input_width, Some output_width, Some high, Some low
               when is_word (exp_type ctx.widths input) &&
                    is_word (exp_type ctx.widths exp) &&
                    prove_specialized ctx (Type_check.env_of exp)
                      (nc_and (nc_lteq (nint 0) low)
                        (nc_and (nc_lteq low high)
                          (nc_and (nc_lt high input_width)
                            (nc_eq (nsum (nminus high low) (nint 1)) output_width)))) -> ()
           | _ -> fail loc "generic subrange requires exact length and proved source bounds");
          App ("word_subword", [List.hd xs; Tuple_term [
            App ("num_of_int", [List.nth xs 2]);
            word_dimension (exp_type ctx.widths exp)]])
      | "replicate_bits", [input; count]
          when is_poly_word (exp_type ctx.widths input) ||
               is_poly_word (exp_type ctx.widths exp) ->
          let copies = constant_index ctx count in
          (match snd (bitvector_argument input), snd (bitvector_argument exp) with
           | Some input_width, Some output_width when copies > 0 &&
               is_word (exp_type ctx.widths input) && is_word (exp_type ctx.widths exp) &&
               prove_specialized ctx (Type_check.env_of exp)
                 (nc_eq output_width (ntimes input_width (nint copies))) -> ()
           | _ -> fail loc "generic replication requires a static count and exact source width");
          if copies = 1 then List.hd xs
          else if copies = 2 then App ("word_join", [List.hd xs; List.hd xs])
          else App ("word_duplicate", [List.hd xs])
      | "Regidx", [value] when !upstream_architecture = Some "rv32" &&
            Type_check.Env.is_union_constructor id (Type_check.env_of exp) ->
          if exp_type ctx.widths value <> Word 5 || exp_type ctx.widths exp <> Word 5 then
            fail loc "upstream Regidx requires its five-bit source payload";
          List.hd xs
      | "Retire_Success", [value] when !upstream_architecture = Some "rv32" &&
            !state_computation &&
            Type_check.Env.is_union_constructor id (Type_check.env_of exp) ->
          if exp_type ctx.widths value <> Unit || exp_type ctx.widths exp <> Unit then
            fail loc "successful state computation requires the unit retirement payload";
          Atom "one"
      | ("Some" | "None"), _ when Type_check.Env.is_union_constructor id (Type_check.env_of exp) ->
          (match exp_type ctx.widths exp, xs with
           | Option_type _, [value] when name = "Some" -> App ("INR", [value])
           | Option_type _, [value] when name = "None" && exp_type ctx.widths (List.hd args) = Unit ->
               App ("INL", [value])
           | _ -> fail loc "Some/None must construct the standard option type")
      | _, _ when Type_check.Env.is_union_constructor id (Type_check.env_of exp) &&
                  (match exp_type ctx.widths exp with Unit_variant _ -> true | _ -> false) ->
          (* A retirement relation keeps only the constructor of an RV32
             trap cause (hol_type), so EBREAK's E_Breakpoint(Brk_Software)
             becomes E_Breakpoint. The payload has been evaluated. *)
          let cause = match exp_type ctx.widths exp with
            | Unit_variant ("ExceptionType", _) -> !normal_retirement
            | _ -> false in
          if List.length args <> 1 ||
             (exp_type ctx.widths (List.hd args) <> Unit && not cause) then
            fail loc "unit variant constructor requires the singleton unit payload";
          Atom (ctor_symbol name)
      | _, [payload] when Type_check.Env.is_union_constructor id (Type_check.env_of exp) &&
                  (match exp_type ctx.widths exp with Binary_variant _ -> true | _ -> false) ->
          (match exp_type ctx.widths exp with
           | Binary_variant ((left, a), (right, b)) ->
               let constructor, expected =
                 if name = left then "INL", a
                 else if name = right then "INR", b
                 else fail loc "binary union constructor is absent from its declaration" in
               if exp_type ctx.widths payload <> expected then
                 fail loc "binary union payload disagrees with its checked type";
               App (constructor, xs)
           | _ -> assert false)
      | ("Ok" | "Err"), [_] when Type_check.Env.is_union_constructor id (Type_check.env_of exp) ->
          (match exp_type ctx.widths exp with
           | Result _ -> App ((if name = "Ok" then "INL" else "INR"), xs)
           | _ -> fail loc "Ok/Err must construct the standard result type")
      (* Sail resolves overloaded operators to checked primitive names such
         as add_atom and add_bits. Integer operations use HOL int; word
         operations use HOL's fixed-width word library. This correspondence
         is handwritten. Source typechecking helps establish operand types,
         but it does not prove that the selected HOL operation has the source
         primitive's meaning. Review signedness, rounding, overflow and casts. *)
      | ("add_int" | "add_atom"), _ -> binary "+"
      | ("sub_int" | "sub_atom"), _ -> binary "-"
      | ("mult_int" | "mult_atom"), _ -> binary "*"
      | ("negate_int" | "negate_atom"), [_] ->
          if List.map (exp_type ctx.widths) [List.hd args; exp] <> [Int; Int] then
            fail loc "integer negation requires an integer argument and result";
          unary "--"
      | ("abs_int_atom" | "abs_int_plain"), [argument] ->
          if List.map (exp_type ctx.widths) [argument; exp] <> [Int; Int] then
            fail loc "integer absolute value requires an integer argument and result";
          unary "abs"
      | ("min_int" | "max_int"), [left; right] ->
          if List.map (exp_type ctx.widths) [left; right; exp] <> [Int; Int; Int] then
            fail loc "integer minimum/maximum require integer arguments and result";
          App ((if name = "min_int" then "min" else "max"), xs)
      | ("_shl1" | "_shl8" | "_shl32" | "_shl_int" | "_shr32" | "_shr_int"),
          [value; amount] ->
          if List.map (exp_type ctx.widths) [value; amount; exp] <> [Int; Int; Int] then
            fail loc "integer shifts require integer arguments and result";
          require_integer_lower_bound ctx amount (List.nth xs 1) 0
            "integer shifts require a proved nonnegative amount";
          let power = App ("&", [Infix ("EXP", nat 2,
            App ("num_of_int", [pure ctx amount]))]) in
          (* Sail's arbitrary-precision right shift uses mpz_fdiv_q_2exp:
             negative values round down, not towards zero. *)
          Infix ((if String.starts_with ~prefix:"_shl" name then "*" else "div"),
                 pure ctx value, power)
      | "pow2", [amount] ->
          if List.map (exp_type ctx.widths) [amount; exp] <> [Int; Int] then
            fail loc "power of two requires an integer argument and result";
          require_numeric_fact ctx amount (fun n -> nc_lteq (nint 0) n)
            "power of two requires a proved nonnegative exponent";
          App ("&", [Infix ("EXP", nat 2, App ("num_of_int", [pure ctx amount]))])
      | "eq_string", [left; right] ->
          if List.map (exp_type ctx.widths) [left; right; exp] <>
               [String_type; String_type; Bool] then
            fail loc "string equality requires two strings and a Boolean result";
          binary "="
      | ("eq_anything" | "neq_anything"), [left; right]
          when exp_type ctx.widths exp = Bool &&
               exp_type ctx.widths left = exp_type ctx.widths right ->
          let equal = binary "=" in
          if name = "eq_anything" then equal else App ("~", [equal])
      | ("eq_anything" | "neq_anything"), _ ->
          fail loc "generic equality requires matching operand types and Boolean result"
      | ("eq_int" | "eq_atom" | "eq_bits" | "eq_bit" | "eq_bool" | "eq_any"), _ ->
          binary "="
      | ("neq_bits" | "neq_any" | "neq_int"), _ -> App ("~", [binary "="])
      | ("lt_int" | "lt_atom"), _ -> binary "<"
      | ("lteq_int" | "lteq_atom"), _ -> binary "<="
      | ("gt_int" | "gt_atom"), _ -> binary ">"
      | ("gteq_int" | "gteq_atom"), _ -> binary ">="
      | ("not_bool"), _ -> unary "~"
      | ("and_bool"), _ -> binary "/\\"
      | ("or_bool"), _ -> binary "\\/"
      | "not_vec", [argument] when exp_type ctx.widths argument = Dynamic_bits ->
          let env = Type_check.env_of exp in
          (match Type_check.destruct_bitvector env (Type_check.typ_of argument),
                 Type_check.destruct_bitvector env (Type_check.typ_of exp) with
           | Some input, Some output when exp_type ctx.widths exp = Dynamic_bits &&
                 prove_specialized ctx env (nc_eq input output) -> ()
           | _ -> fail loc "dynamic complement requires the same checked source width");
          (* The only variable-width constructors supported here are zeros
             and this complement. Their payload always lies in 0..2^width-1.
             Preserve the evaluated width through helpers and local aliases;
             never substitute a guessed fixed HOL word size. *)
          let value = List.hd xs in
          let width = App ("FST", [value]) in
          let maximum = Infix ("-", Infix ("EXP", nat 2,
            App ("num_of_int", [width])), nat 1) in
          used_primitives := "checked-dynamic-bit-complement" :: !used_primitives;
          Tuple_term [width; Infix ("-", maximum, App ("SND", [value]))]
      | "not_vec", _ -> unary "word_not"
      | ("UInt0" | "unsigned"), _ -> App ("&", [unary "val"])
      | ("SInt0" | "signed"), _ -> unary "ival"
      | "add_bits", _ -> App ("word_add", xs)
      | "add_bits_int", [word; offset] ->
          (match exp_type ctx.widths word, exp_type ctx.widths offset with
           | Word n, Int when exp_type ctx.widths exp = Word n ->
               App ("word_add", [pure ctx word; Typed (App ("iword", [pure ctx offset]), Word n)])
           | _ -> fail loc "mixed addition requires a word and integer of the declared result width")
      | "sub_bits", _ -> App ("word_sub", xs)
      | "sub_vec", _ -> App ("word_sub", xs)
      | "sub_vec_int", [word; offset] ->
          (match exp_type ctx.widths word, exp_type ctx.widths offset with
           | Word n, Int when exp_type ctx.widths exp = Word n ->
               App ("word_sub", [pure ctx word; Typed (App ("iword", [pure ctx offset]), Word n)])
           | _ -> fail loc "mixed subtraction requires a word and integer of the declared result width")
      | "mult_bits", _ -> App ("word_mul", xs)
      | ("and_vec" | "and_bits"), _ -> App ("word_and", xs)
      | ("or_vec" | "or_bits"), _ -> App ("word_or", xs)
      | ("xor_vec" | "xor_bits"), _ -> App ("word_xor", xs)
      | ("shift_bits_left" | "shift_bits_right"), [x; shift] ->
          (match exp_type ctx.widths x, exp_type ctx.widths shift,
                 exp_type ctx.widths exp with
           | Word input, _, Word output when input <> output ->
               fail loc "bitvector shifts require a result of the input width"
           | (Word _ | Poly_word _), (Word _ | Poly_word _), (Word _ | Poly_word _) -> ()
           | _ -> fail loc "bitvector shifts require word operands and result");
          App ((if name = "shift_bits_left" then "word_shl" else "word_ushr"),
               [pure ctx x; App ("val", [pure ctx shift])])
      | ("sail_shiftleft" | "sail_shiftright" | "sail_arith_shiftright" |
         "shiftl" | "shiftr" | "arith_shiftr"), [x; shift] ->
          (match exp_type ctx.widths x, exp_type ctx.widths shift,
                 exp_type ctx.widths exp with
           | Word input_width, Int, Word output_width when input_width = output_width ->
               (* A value position cannot choose the unknown result of a
                  negative amount; see the E_app case of computation. *)
               if not (integer_shift_nonnegative ctx shift (List.nth xs 1)) then
                 fail (exp_loc shift) "integer shifts require a proved nonnegative amount";
               App (integer_shift_operation name,
                    [pure ctx x; App ("num_of_int", [pure ctx shift])])
           | _ -> fail loc "integer shifts require a word, integer amount and matching word result")
      | ("emod_nat" | "ediv_nat" |
         "quot_positive_round_zero" | "rem_positive_round_zero"), [value; divisor] ->
          if List.map (exp_type ctx.widths) [value; divisor; exp] <> [Int; Int; Int] then
            fail loc "nonnegative division and remainder require integer arguments and result";
          require_integer_lower_bound ctx value (List.hd xs) 0
            "nonnegative division and remainder require a proved nonnegative dividend";
          require_integer_lower_bound ctx divisor (List.nth xs 1) 1
            "nonnegative division and remainder require a proved positive divisor";
          (* For nonnegative n and positive d, truncation toward zero agrees
             with HOL's floor quotient/remainder. The checked source and
             evaluated-value guards establish this domain at every call. *)
          Infix ((if List.mem name ["emod_nat"; "rem_positive_round_zero"]
                  then "rem" else "div"), List.hd xs, List.nth xs 1)
      | "ediv_int", [value; divisor] ->
          if List.map (exp_type ctx.widths) [value; divisor; exp] <> [Int; Int; Int] then
            fail loc "Euclidean division requires integer arguments and result";
          (* With a positive divisor, Sail's Euclidean quotient is HOL's
             floor quotient, including for a negative dividend. Reject
             zero/negative divisors rather than guess another convention.
             DecodeBitMasks uses this genuine primitive on fixed widths;
             its defined DIV/Replicate helpers remain in the model. *)
          require_integer_lower_bound ctx divisor (List.nth xs 1) 1
            "Euclidean division requires a proved positive divisor";
          Infix ("div", List.hd xs, List.nth xs 1)
      | "tdiv_int", [value; divisor] ->
          if List.map (exp_type ctx.widths) [value; divisor; exp] <> [Int; Int; Int] then
            fail loc "truncated division requires integer arguments and result";
          require_integer_lower_bound ctx divisor (List.nth xs 1) 1
            "truncated division requires a proved positive divisor";
          (* HOL's integer div rounds down; Sail tdiv_int rounds toward zero.
             For positive d, a negative x therefore needs -( (-x) div d ).
             Use HOL's existing integer operations, not an undeclared quot
             constant. Defined Sail fdiv/fmod bodies are still traversed. *)
          let nonnegative = match integer_bounds (List.hd xs) with
            | Some (low, _) -> Nat_big_num.greater_equal low Nat_big_num.zero
            | None -> false in
          let value = List.hd xs and divisor = List.nth xs 1 in
          if nonnegative then Infix ("div", value, divisor)
          else Cond (Infix ("<", value, integer Nat_big_num.zero),
            App ("--", [Infix ("div", App ("--", [value]), divisor)]),
            Infix ("div", value, divisor))
      | ("quot_round_zero" | "rem_round_zero"), [value; divisor] ->
          if List.map (exp_type ctx.widths) [value; divisor; exp] <> [Int; Int; Int] then
            fail loc "division toward zero requires integer arguments and result";
          require_numeric_fact ctx divisor (fun d -> nc_neq d (nint 0))
            "division toward zero requires a proved nonzero divisor";
          (* Sail rounds the quotient toward zero; the remainder has the
             dividend's sign. HOL's div and rem are Euclidean, with
             0 <= x rem d < abs d, which for x >= 0 is the same for either
             sign of d. For x < 0 negate the dividend and the result. *)
          let operation = if name = "quot_round_zero" then "div" else "rem" in
          let value = List.hd xs and divisor = List.nth xs 1 in
          Cond (Infix ("<", value, integer Nat_big_num.zero),
            App ("--", [Infix (operation, App ("--", [value]), divisor)]),
            Infix (operation, value, divisor))
      (* HOL's word_sx and word_zx truncate to a narrower result type, so
         require a result no narrower than the input: compare static widths
         directly and prove the bound for polymorphic ones. *)
      | ("sail_sign_extend" | "sail_zero_extend"), [x; _] ->
          (match exp_type ctx.widths x, exp_type ctx.widths exp with
           | Word input_width, Word output_width ->
               if output_width < input_width then
                 fail loc "extension requires a result no narrower than its input"
           | (Word _ | Poly_word _), (Word _ | Poly_word _) ->
               let env, input_width = bitvector_argument x in
               let _, output_width = bitvector_argument exp in
               (match input_width, output_width with
                | Some input, Some output
                  when prove_specialized ctx env (nc_lteq input output) -> ()
                | _ -> fail loc "extension requires a result no narrower than its input")
           | _ -> fail loc "extension requires word input and result");
          App ((if name = "sail_sign_extend" then "word_sx" else "word_zx"), [pure ctx x])
      (* truncate(v, m) keeps the m least significant bits, 0 <= m <= length(v).
         HOL's word_zx to a narrower or equal word type does the same. *)
      | "truncate", [x; width] when extended_evaluation () ->
          (match exp_type ctx.widths x, exp_type ctx.widths exp with
           | Word input_width, Word output_width when
                 output_width = constant_index ctx width &&
                 output_width <= input_width ->
               App ("word_zx", [pure ctx x])
           | _ -> fail loc "truncate requires a static result no wider than its input")
      | ("SignExtend0" | "ZeroExtend0"), [x; width] ->
          let result_width = constant_index ctx width in
          (match exp_type ctx.widths x, exp_type ctx.widths exp with
           | Word input_width, Word output_width when output_width = result_width &&
                 output_width >= input_width ->
               App ((if name = "SignExtend0" then "word_sx" else "word_zx"), [pure ctx x])
           | Dynamic_bits, Word output_width when name = "ZeroExtend0" &&
                 output_width = result_width ->
               let env, input_width = bitvector_argument x in
               (match input_width with
                | Some input_width when prove_specialized ctx env
                    (nc_and (nc_lteq (nint 0) input_width)
                      (nc_lteq input_width (nint output_width))) -> ()
                | _ -> fail loc "dynamic zero extension requires a proved bounded source width");
               used_primitives := "checked-dynamic-zero-extension" :: !used_primitives;
               App ("word", [App ("SND", [List.hd xs])])
           | _ -> fail loc "Arm extension requires its declared static output width")
      (* Architecture read contracts. These use the currently threaded state,
         check their source interfaces and, where needed, prove index bounds.
         Canonical HOL register components supply zero-register and narrow-
         register behavior; that is part of the interpretation, not a result
         obtained by translating the cut upstream register-access body. *)
      | "rX_bits", [index] when !state_type = "riscvstate" ->
          if exp_type ctx.widths index <> Word 5 || exp_type ctx.widths exp <> Word 32 then
            fail loc "rX_bits requires RV32 register and value types";
          (match ctx.state with
           | Some s -> App ("read", [App ("riscv_gpr", [pure ctx index]); s])
           | None -> fail loc "rX_bits requires a stateful RV32 root")
      (* shina's read_gpr(width, index) signature, if a selection cuts it.
         REMS's one-argument read_gpr has its own Gpr_access case. *)
      | "read_gpr", [width; index] when x86_shina_registers () ->
          if is_defined_function name then
            fail loc "read_gpr requires its explicit register boundary";
          App ("read", [x86_gpr ctx exp width index None (pure ctx index);
            Option.get ctx.state])
      | "read_gpr", [index] when x86_binds X86.Gpr_access ->
          if ctx.state = None then fail loc "REMS register read requires a stateful instruction";
          App ("read", [x86_rems_gpr ctx exp index None (pure ctx index);
                        Option.get ctx.state])
      | "read_simd", [width; index] when x86_binds X86.Simd_access ->
          if ctx.state = None then fail loc "x86 SIMD read requires a stateful instruction";
          App ("read", [x86_simd ctx exp width index None (pure ctx index);
                        Option.get ctx.state])
      | "X_read", [index; width] when !state_type = "armstate" && !state_computation ->
          if List.map (exp_type ctx.widths) [index; width] <> [Int; Int] then
            fail loc "X_read requires integer index and width";
          let n = constant_index ctx width in
          if not (List.mem n [8; 16; 32; 64]) then
            fail loc "X_read supports only 8/16/32/64-bit general registers";
          if exp_type ctx.widths exp <> Word n then fail loc "X_read width/result mismatch";
          let env = Type_check.env_of index in
          let numeric = match Type_check.destruct_atom_nexp env (Type_check.typ_of index) with
            | Some n -> n | None -> fail loc "X_read requires a bounded register index" in
          if not (prove_specialized ctx env
            (nc_and (nc_lteq (nint 0) numeric) (nc_lteq numeric (nint 31)))) then
            fail loc "X_read index is not proved in 0..31";
          let value = App ("read", [
            App ((if n = 32 then "WREG" else "XREG"),
              [App ("num_of_int", [pure ctx index])]);
            Option.get ctx.state]) in
          if n = 8 || n = 16 then App ("word_zx", [Typed (value, Word 64)])
          else value
      | "SP_read", [argument] when !state_type = "armstate" && !state_computation ->
          if exp_type ctx.widths argument <> Unit || exp_type ctx.widths exp <> Word 64 then
            fail loc "SP_read requires unit -> bits(64)";
          App ("read", [Atom "SP"; Option.get ctx.state])
      | "SCTLR_read__1", [argument] when !state_type = "armstate" && !state_computation ->
          let env = Type_check.env_of exp in
          let named = match Type_check.Env.base_typ_of env (Type_check.typ_of exp) with
            | Typ_aux (Typ_id id, _) -> string_of_id id = "SCTLRType"
            | _ -> false in
          let typ = Record ["bits", Word 64] in
          if not named || exp_type ctx.widths argument <> Unit ||
             exp_type ctx.widths exp <> typ then
            fail loc "SCTLR_read__1 requires unit -> SCTLRType with bits(64)";
          (* Keep the source's SA/SA0 tests. The selected system-control
             register is an explicit component input, not an always-enabled
             alignment check or a fabricated field in armstate. *)
          contract_register loc ctx "SCTLR_read__1" typ
      | ("CreateAccDescGPR" | "CreateAccDescASIMD"), _
          when !state_type = "armstate" && !state_computation ->
          let expected = if name = "CreateAccDescGPR"
            then [Enum "MemOp"; Bool; Bool; Bool]
            else [Enum "MemOp"; Bool; Bool] in
          if List.map (exp_type ctx.widths) args <> expected then
            fail loc (name ^ " requires its original MemOp and Boolean arguments");
          require_arm_memory_enum loc (Type_check.env_of exp) "MemOp"
            ["MemOp_LOAD"; "MemOp_STORE"; "MemOp_PREFETCH"];
          let typ = arm_access_descriptor_type ctx exp in
          used_primitives := "Arm-flat-access-descriptor" :: !used_primitives;
          (* Metadata remains an arbitrary value of the original complete
             record type. The computation path already evaluated each source
             operand in order, including its effects. Retain the captured
             values here too; do not fabricate one favourable descriptor. *)
          Let (Atom (fresh ()), Tuple_term xs,
            Typed (contract_register loc ctx
              (if name = "CreateAccDescGPR" then "FlatAccDescGPR" else "FlatAccDescASIMD")
              typ, typ))
      | "BigEndian", [access_type]
          when !state_type = "armstate" && !state_computation ->
          if exp_type ctx.widths access_type <> Enum "AccessType" ||
             exp_type ctx.widths exp <> Bool then
            fail loc "BigEndian requires the original AccessType -> bool signature";
          require_arm_access_type loc (Type_check.env_of exp);
          used_primitives := "Arm-little-endian-access" :: !used_primitives;
          Let (Atom (fresh ()), List.hd xs, Atom "F")
      | ("Mem_read" | "Mem_read__1"), _
          when !state_type = "armstate" ->
          (* Even a load that changes no registers emits an access event.
             Only computation's flat-memory path can carry that update. *)
          fail loc "Mem_read requires the stateful flat-memory path"
      | "V_read", [index; width] when !state_type = "armstate" && !state_computation ->
          if List.map (exp_type ctx.widths) [index; width] <> [Int; Int] then
            fail loc "V_read requires integer index and width";
          let n = constant_index ctx width in
          if not (List.mem n [8; 16; 32; 64; 128]) ||
             exp_type ctx.widths exp <> Word n then
            fail loc "V_read requires a matching 8/16/32/64/128-bit result";
          require_integer_interval ctx index (List.hd xs) 0 31
            "V_read index is not proved in 0..31";
          let value = App ("read", [App ((if n <= 64 then "DREG" else "QREG"),
            [App ("num_of_int", [pure ctx index])]); Option.get ctx.state]) in
          (* Scalar FP/move forms read only their low bits. This truncates
             the D64 value; V_set separately supplies narrow-write clearing. *)
          if n < 64 then App ("word_zx", [Typed (value, Word 64)]) else value
      (* Feature/control contracts are deliberately limited. Some features
         are disabled; other selections remain explicit HOL state components.
         Their dependency labels describe the assumed platform view. They
         must not silently become a claim about every source configuration. *)
      | "IsFeatureImplemented", [feature]
          when !state_type = "armstate" && !state_computation ->
          let assumed = match literal_key (List.hd xs) with
            | Some ("enum:Feature", constructor) ->
                List.find_opt (function Entry.Feature (name, _) ->
                  constructor = ctor_symbol name | _ -> false)
                  !configured_assumptions
            | _ -> None in
          (match assumed with
           | Some (Entry.Feature (_, value) as fact) ->
               if exp_type ctx.widths feature <> Enum "Feature" ||
                  exp_type ctx.widths exp <> Bool then
                 fail loc "feature assumptions require Feature -> bool";
               used_assumptions := fact :: !used_assumptions;
               Atom (if value then "T" else "F")
           | _ ->
          let constructor = mk_id "FEAT_GCS" in
          if exp_type ctx.widths feature <> Enum "Feature" ||
             exp_type ctx.widths exp <> Bool ||
             not (Type_check.is_enum_member constructor (Type_check.env_of exp)) then
            fail loc "disabled GCS feature query requires the actual FEAT_GCS value and Feature -> bool";
          (match literal_key (List.hd xs) with
           | Some ("enum:Feature", feature) when feature = ctor_symbol "FEAT_GCS" ->
               disabled_extensions := "Arm-GCS" :: !disabled_extensions;
               Atom "F"
           | Some ("enum:Feature", feature) when feature = ctor_symbol "FEAT_LSE2" &&
                 Type_check.is_enum_member (mk_id "FEAT_LSE2") (Type_check.env_of exp) &&
                 !upstream_architecture = Some "aarch64" ->
               (* Pair instructions have two genuine upstream access paths.
                  Retain their selector as an arbitrary configuration input;
                  the flat-memory contract interprets both paths, rather
                  than requiring FEAT_LSE2 to be absent. *)
               used_primitives := "Arm-explicit-LSE2-availability" :: !used_primitives;
               contract_register loc ctx "FlatHaveLSE2" Bool
           | _ -> fail loc "disabled GCS feature query requires the actual FEAT_GCS value and Feature -> bool"))
      | "get_arch_pc", [_] when !state_type = "riscvstate" ->
          if exp_type ctx.widths (List.hd args) <> Unit ||
             exp_type ctx.widths exp <> Word 32 then
            fail loc "get_arch_pc requires unit -> bits(32)";
          (match ctx.entry_state with
           | Some s -> App ("riscv_instruction_pc", [s])
           | None -> fail loc "get_arch_pc requires a stateful RV32 root")
      | "get_next_pc", [_] when !state_type = "riscvstate" ->
          if exp_type ctx.widths (List.hd args) <> Unit ||
             exp_type ctx.widths exp <> Word 32 then
            fail loc "get_next_pc requires unit -> bits(32)";
          App ("read", [Atom "PC"; Option.get ctx.state])
      (* One hart with flat memory: barriers order nothing, and no event
         consumer exists. The argument has been evaluated. *)
      | ("sail_barrier" | "generate_event"), [kind] when !state_type = "riscvstate" ->
          let expected = if name = "sail_barrier" then "barrier_kind" else "Event" in
          if exp_type ctx.widths kind <> Enum expected || exp_type ctx.widths exp <> Unit then
            fail loc (name ^ " requires " ^ expected ^ " -> unit");
          Atom "one"
      (* FENCE's I/O-implies-memory setting, from privilege and envcfg CSRs. *)
      | "is_fiom_active", [_] when !state_type = "riscvstate" ->
          if exp_type ctx.widths (List.hd args) <> Unit || exp_type ctx.widths exp <> Bool then
            fail loc "is_fiom_active requires unit -> bool";
          contract_register loc ctx "is_fiom_active" Bool
      | "currentlyEnabled", [E_aux (E_id extension, _)] when !normal_retirement ->
          let name = string_of_id extension in
          if not (Type_check.is_enum_member extension (Type_check.env_of exp)) ||
             List.mem_assoc name ctx.locals || exp_type ctx.widths exp <> Bool then
            fail loc "disabled extension requires an enumeration constructor and Boolean result";
          if not (List.mem name Rv32.disabled_extensions) then
            fail loc ("no disabled-extension contract for " ^ name);
          disabled_extensions := name :: !disabled_extensions;
          Atom "F"
      (* Retirement relations are RV32 only (export_checked). *)
      | "exception_context", _ when !normal_retirement ->
          (match List.map (exp_type ctx.widths) args, exp_type ctx.widths exp with
           | [Unit_variant ("ExceptionType", _); Word 32],
             Record [("trap", Unit_variant ("ExceptionType", _)); ("excinfo", Word 32)] ->
               Tuple_term xs
           | _ -> fail loc "exception_context must retain its cause and 32-bit address")
      | "trap", [_] when !normal_retirement ->
          (match exp_type ctx.widths (List.hd args), exp_type ctx.widths exp with
           | Record [("trap", Unit_variant ("ExceptionType", _)); ("excinfo", Word 32)],
             Unit_variant ("ExecutionResult", members) when
               List.exists (fun id -> string_of_id id = "Trap") members ->
               Atom (ctor_symbol "Trap")
           | _ -> fail loc "trap requires the explicit exception/retirement variant interface")
      (* Bitvector construction and observation. Check matching widths and
         index/slice bounds before using HOL bit/word operations. Known sizes
         can be computed from types, but runtime operands must still be
         evaluated: type knowledge alone does not erase argument effects. *)
      | "bit_to_bool", [x] ->
          if exp_type ctx.widths x <> Word 1 || exp_type ctx.widths exp <> Bool then
            fail loc "bit_to_bool requires a one-bit word and a Boolean result";
          App ("bit", [nat 0; pure ctx x])
      | "bitvector_update", [x; index; value] ->
          let bit = constant_index ctx index in
          (match exp_type ctx.widths x, exp_type ctx.widths value with
           | Word n, Word 1 when bit >= 0 && bit < n ->
               App ("word_or", [
                 App ("word_and", [pure ctx x; App ("word_not", [
                   App ("word", [Infix ("EXP", nat 2, nat bit)])])]);
                 App ("word_shl", [App ("word_zx", [pure ctx value]); nat bit])])
           | _ -> fail loc "bit update requires an in-bounds static position and a one-bit value")
      | ("sail_zeros" | "zeros" | "sail_ones"), [width] ->
          if exp_type ctx.widths width <> Int then fail loc "bitvector fill requires an integer width";
          if exp_type ctx.widths exp = Dynamic_bits then begin
            if name <> "sail_zeros" && name <> "zeros" then
              fail loc "dynamic ones require the original defined helper body";
            require_integer_lower_bound ctx width (List.hd xs) 0
              "dynamic zeros require a proved nonnegative source width";
            let env, numeric = numeric_argument width in
            (match numeric, Type_check.destruct_bitvector env (Type_check.typ_of exp) with
             | Some width, Some result when prove_specialized ctx env (nc_eq width result) -> ()
             | _ -> fail loc "dynamic zeros require their matching checked source width");
            used_primitives := "checked-dynamic-bit-zeros" :: !used_primitives;
            Tuple_term [List.hd xs; nat 0]
          end else begin
            let n = constant_index ctx width in
            let expected = if n = 0 then Empty_bits else Word n in
            if n < 0 || exp_type ctx.widths exp <> expected then
              fail loc "bitvector fill requires its matching static result width";
            if n = 0 then Atom "one"
            else if name = "sail_ones" then App ("word_not", [App ("word", [nat 0])])
            else App ("word", [nat 0])
          end
      | "bitvector_concat", [left; right] ->
          concat ctx loc left right (List.hd xs) (List.nth xs 1)
      | "replicate_bits", [input; count] ->
          if exp_type ctx.widths count <> Int then
            fail loc "replication requires an integer count";
          let count_expression = count in
          let count = constant_index ctx count in
          (match exp_type ctx.widths input, exp_type ctx.widths exp with
           | (Dynamic_bits, (Dynamic_bits | Word _) |
              Word _, Dynamic_bits) when count = 1 ->
               (* One evaluated copy is an identity even when Sail keeps
                  its intermediate width symbolic. Check equality of the
                  original widths before bridging representations; never
                  truncate a dynamic value to an assumed hardware width.
                  Larger dynamic repetitions remain unsupported. *)
               let input_env, input_width = bitvector_argument input in
               let _, output_width = bitvector_argument exp in
               (* The evaluated argument is exactly one. Its singleton
                  numeric type may still be a witness for an inlined DIV
                  calculation. Relate that same source witness to the
                  established value; do not invent a bitvector width. *)
               let count_env, count_width = numeric_argument count_expression in
               let env = match count_width with
                 | Some count_width -> Type_check.Env.add_constraint
                     (nc_eq count_width (nint count)) count_env
                 | None -> input_env in
               (match input_width, output_width with
                | Some input_width, Some output_width when
                    prove_specialized ctx env (nc_eq input_width output_width) -> ()
                | _ -> fail loc "single dynamic replication requires equal checked source widths");
               used_primitives := "checked-dynamic-single-replication" :: !used_primitives;
               (match exp_type ctx.widths input, exp_type ctx.widths exp with
                | Dynamic_bits, Dynamic_bits -> List.hd xs
                | Dynamic_bits, Word _ -> App ("word", [App ("SND", [List.hd xs])])
                | Word width, Dynamic_bits ->
                    Tuple_term [integer (Nat_big_num.of_int width);
                                App ("val", [List.hd xs])]
                | _ -> assert false)
           | Word width, Word result when count > 0 &&
                 result = width * count ->
               let value = List.hd xs in
               if count = 1 then value
               else if count = 2 then App ("word_join", [value; value])
               else App ("word_duplicate", [value])
           | _ -> fail loc "replication requires a positive static count and its exact word width")
      | "bitvector_access", [x; i] ->
          (match exp_type ctx.widths x, exp_type ctx.widths i,
                 exp_type ctx.widths exp with
           | Word n, Int, Word 1 ->
               let index = try Some (constant_index ctx i)
                 with Reporting.Fatal_error _ -> None in
               let position = match index with
                 | Some index ->
                     if index < 0 || index >= n then fail loc "bit access is out of bounds";
                     nat index
                 | None ->
                     require_numeric_fact ctx i
                       (fun index -> nc_and (nc_lteq (nint 0) index)
                         (nc_lt index (nint n)))
                       "dynamic bit access requires a proved in-bounds index";
                     App ("num_of_int", [pure ctx i]) in
               App ("word", [App ("bitval", [App ("bit", [position; pure ctx x])])])
           | _ -> fail loc "bit access requires a word, integer index and one-bit result")
      | "bitvector_length", [x] ->
          if exp_type ctx.widths exp <> Int then
            fail loc "bitvector_length requires an integer result";
          (match exp_type ctx.widths x with
           | Word n -> integer (Nat_big_num.of_int n)
           | Empty_bits -> integer Nat_big_num.zero
           | _ -> fail loc "bitvector_length on a non-word")
      | "get_slice_int", [width; x; start] ->
          let width = constant_index ctx width and start = constant_index ctx start in
          if start < 0 || exp_type ctx.widths x <> Int ||
             exp_type ctx.widths exp <> Word width then
            fail loc "integer slices require a nonnegative static start and declared result width";
          (* Infinite two's-complement extraction uses floor division,
             including negative signed products. Keep offset zero unchanged. *)
          let shifted = if start = 0 then pure ctx x else
            Infix ("div", pure ctx x, Infix ("pow", integer (Nat_big_num.of_int 2), nat start)) in
          App ("iword", [shifted])
      | "slice", [input; start; length] ->
          let input_width, output_width = match
            exp_type ctx.widths input, exp_type ctx.widths exp with
            | Word input_width, Word output_width -> input_width, output_width
            | _ -> fail loc "slice requires word input and result" in
          if exp_type ctx.widths start <> Int ||
             exp_type ctx.widths length <> Int ||
             constant_index ctx length <> output_width then
            fail loc "slice requires an integer offset and exact static length";
          let known = try Some (constant_index ctx start)
            with Reporting.Fatal_error _ -> None in
          let offset = match known with
            | Some offset ->
                if offset < 0 || offset + output_width > input_width then
                  fail loc "slice positions are out of bounds";
                nat offset
            | None ->
                require_numeric_fact ctx start
                  (fun offset -> nc_and (nc_lteq (nint 0) offset)
                    (nc_lteq offset (nint (input_width - output_width))))
                  "slice requires a proved in-bounds offset";
                App ("num_of_int", [List.nth xs 1]) in
          App ("word_subword", [List.hd xs; Tuple_term [offset; nat output_width]])
      | "set_slice_bits", [base_length; length; input; start; inserted] ->
          let base_width, insert_width = match
            exp_type ctx.widths input, exp_type ctx.widths inserted with
            | Word base_width, Word insert_width -> base_width, insert_width
            | _ -> fail loc "set_slice_bits requires word base and inserted value" in
          if List.exists (fun argument -> exp_type ctx.widths argument <> Int)
               [base_length; length; start] ||
             constant_index ctx base_length <> base_width ||
             constant_index ctx length <> insert_width ||
             exp_type ctx.widths exp <> Word base_width then
            fail loc "set_slice_bits requires exact base, insert and result widths";
          let known = try Some (constant_index ctx start)
            with Reporting.Fatal_error _ -> None in
          let offset = match known with
            | Some offset ->
                if offset < 0 || offset + insert_width > base_width then
                  fail loc "set_slice_bits positions are out of bounds";
                nat offset
            | None ->
                require_numeric_fact ctx start
                  (fun offset -> nc_and (nc_lteq (nint 0) offset)
                    (nc_lteq offset (nint (base_width - insert_width))))
                  "set_slice_bits requires a proved in-bounds offset";
                App ("num_of_int", [List.nth xs 3]) in
          let result, bits = insert_word loc base_width insert_width
            (List.nth xs 2) (List.nth xs 4)
            known offset "set_slice_bits partial-word width mismatch"
            "set_slice_bits partial-word width mismatch"
            "partial set_slice_bits requires a static offset" in
          (match known with Some _ -> tracked_word result base_width bits | None -> result)
      (* Decreasing-order update_subrange_bits(v, high, low, x) replaces bits
         high..low of v by x. Bitfield field updates use it with literal
         positions. Only static positions are supported. *)
      | "update_subrange_bits", [base; high; low; inserted] when extended_evaluation () ->
          let base_width, insert_width = match
            exp_type ctx.widths base, exp_type ctx.widths inserted with
            | Word base_width, Word insert_width -> base_width, insert_width
            | _ -> fail loc "update_subrange_bits requires word base and inserted value" in
          (match Type_check.Env.get_default_order (Type_check.env_of exp) with
           | Ord_aux (Ord_dec, _) -> ()
           | _ -> fail loc "update_subrange_bits requires decreasing bit order");
          let high = constant_index ctx high and low = constant_index ctx low in
          if low < 0 || high < low || high >= base_width ||
             high - low + 1 <> insert_width || exp_type ctx.widths exp <> Word base_width then
            fail loc "update_subrange_bits requires matching in-bounds positions";
          let result, bits = insert_word loc base_width insert_width
            (List.nth xs 0) (List.nth xs 3) (Some low) (nat low)
            "update_subrange_bits partial-word width mismatch"
            "update_subrange_bits partial-word width mismatch"
            "partial update_subrange_bits requires a static offset" in
          tracked_word result base_width bits
      | ("bitvector_subrange" | "subrange_bits"), [x; hi; lo] ->
          let input_width, output_width = match
            exp_type ctx.widths x, exp_type ctx.widths exp with
            | Word input_width, Word output_width -> input_width, output_width
            | _ -> fail loc "bitvector slices require word input and result" in
          let known = try Some (constant_index ctx hi, constant_index ctx lo)
            with Reporting.Fatal_error _ -> None in
          let first = match known with
            | Some (high, low) ->
                if low < 0 || high < low || high >= input_width ||
                   high - low + 1 <> output_width then
                  fail loc "bitvector slices require matching in-bounds positions";
                nat low
            | None ->
                let env = Type_check.env_of exp in
                let high, low = match
                  Type_check.destruct_atom_nexp env (Type_check.typ_of hi),
                  Type_check.destruct_atom_nexp env (Type_check.typ_of lo) with
                  | Some high, Some low -> high, low
                  | _ -> fail loc "dynamic slices require singleton numeric positions" in
                let bounds = nc_and (nc_lteq (nint 0) low)
                  (nc_and (nc_lteq low high)
                    (nc_and (nc_lt high (nint input_width))
                      (nc_eq (nsum (nminus high low) (nint 1))
                             (nint output_width)))) in
                if not (prove_specialized ctx env bounds) then
                  fail loc "dynamic slices require proved bounds and exact result length";
                App ("num_of_int", [pure ctx lo]) in
          App ("word_subword", [pure ctx x; Tuple_term [first; nat output_width]])
      | _ -> fail loc ("unsupported primitive " ^ name) in
      (* An interpreted call, with the interpretation tags its case added. *)
      if List.mem_assoc name contracts then begin
        let rec added names =
          if names == before then [] else match names with
          | tag :: rest -> (if String.contains tag '-' then [tag] else []) @ added rest
          | [] -> [] in
        let sail, placeholders = call_placeholders ctx name args xs in
        (* get_arch_pc reads only the state at the start of the instruction. *)
        let entry = match name, ctx.entry_state with
          | "get_arch_pc", Some entry -> [entry, "s0"] | _ -> [] in
        record_value ctx (name :: added !used_primitives) sail (placeholders @ entry) result
      end;
      result

(* The access argument is omitted only after checking that it is a
   constructor literal, not a same-named helper or a state-dependent value.
   Keep these checks separate from hol_type: the upstream access union is
   polymorphic and is interpreted only at this explicit memory boundary. *)
and require_flat_access_literal ctx expected access =
  let reject () = fail (exp_loc access)
    ("flat access requires the genuine " ^ expected ^
     "(Data) constructor of MemoryAccessType(mem_payload)") in
  let is_payload_type env typ =
    match Type_check.Env.base_typ_of env typ with
    | Typ_aux (Typ_id id, _) -> string_of_id id = "mem_payload"
    | _ -> false in
  match access with
  | E_aux (E_app (constructor, [E_aux (E_id payload, _) as value]), _)
      when string_of_id constructor = expected && string_of_id payload = "Data" &&
           not (is_defined_function expected) &&
           not (List.mem_assoc "Data" ctx.locals) ->
      let env = Type_check.env_of access in
      let payload_env = Type_check.env_of value in
      (match Type_check.Env.union_constructor_info constructor env,
             Type_check.Env.base_typ_of env (Type_check.typ_of access) with
       | Some (_, _, union, _),
         Typ_aux (Typ_app (typ, [A_aux (A_typ argument, _)]), _)
           when string_of_id union = "MemoryAccessType" &&
                string_of_id typ = "MemoryAccessType" &&
                is_payload_type env argument &&
                is_payload_type payload_env (Type_check.typ_of value) &&
                Type_check.is_enum_member payload payload_env -> ()
       | _ -> reject ())
  | _ -> reject ()

(* Access descriptors describe permissions, security state, ordering,
   tagging and other platform properties in the full Arm model. The flat
   memory view keeps their exact source types and every evaluated argument,
   but does not consult metadata when reading/writing ordinary memory.
   The complete field order and enum declarations are checked here before a
   factory result becomes an arbitrary typed component input. A changed
   upstream shape must be reviewed, not silently squeezed into this view. *)
and require_arm_memory_enum loc env name members =
  let id = mk_id name in
  if not (Type_check.Env.is_enum id env) ||
     List.sort String.compare (List.map string_of_id (Type_check.Env.get_enum id env)) <>
       List.sort String.compare members then
    fail loc ("Arm flat memory requires the original " ^ name ^ " enumeration")

and require_arm_access_type loc env =
  require_arm_memory_enum loc env "AccessType" [
    "AccessType_IFETCH"; "AccessType_GPR"; "AccessType_ASIMD"; "AccessType_SVE";
    "AccessType_SME"; "AccessType_IC"; "AccessType_DC"; "AccessType_DCZero";
    "AccessType_AT"; "AccessType_NV2"; "AccessType_SPE"; "AccessType_GCS";
    "AccessType_GPTW"; "AccessType_TTW"
  ]

and arm_access_descriptor_type ctx exp =
  let loc = exp_loc exp and env = Type_check.env_of exp in
  let record = mk_id "AccessDescriptor" in
  (match Type_check.Env.base_typ_of env (Type_check.typ_of exp) with
   | Typ_aux (Typ_id id, _) when Id.compare id record = 0 &&
         Type_check.Env.is_record record env -> ()
   | _ -> fail loc "Arm flat memory requires the original AccessDescriptor record");
  require_arm_access_type loc env;
  List.iter (fun (name, members) -> require_arm_memory_enum loc env name members) [
    "SecurityState", ["SS_NonSecure"; "SS_Root"; "SS_Realm"; "SS_Secure"];
    "MemAtomicOp", ["MemAtomicOp_GCSSS1"; "MemAtomicOp_ADD"; "MemAtomicOp_BIC";
      "MemAtomicOp_EOR"; "MemAtomicOp_ORR"; "MemAtomicOp_SMAX"; "MemAtomicOp_SMIN";
      "MemAtomicOp_UMAX"; "MemAtomicOp_UMIN"; "MemAtomicOp_SWP"; "MemAtomicOp_CAS"];
    "CacheOp", ["CacheOp_Clean"; "CacheOp_Invalidate"; "CacheOp_CleanInvalidate"];
    "CacheOpScope", ["CacheOpScope_SetWay"; "CacheOpScope_PoU"; "CacheOpScope_PoC";
      "CacheOpScope_PoE"; "CacheOpScope_PoP"; "CacheOpScope_PoDP"; "CacheOpScope_PoPA";
      "CacheOpScope_ALLU"; "CacheOpScope_ALLUIS"];
    "CacheType", ["CacheType_Data"; "CacheType_Tag"; "CacheType_Data_Tag";
      "CacheType_Instruction"];
    "VARange", ["VARange_LOWER"; "VARange_UPPER"];
    "PARTIDspaceType", ["PIdSpace_Secure"; "PIdSpace_Root"; "PIdSpace_Realm";
      "PIdSpace_NonSecure"]
  ];
  let expected = Record [
    "acctype", Enum "AccessType"; "el", Word 2; "ss", Enum "SecurityState";
    "acqsc", Bool; "acqpc", Bool; "relsc", Bool; "limitedordered", Bool;
    "exclusive", Bool; "atomicop", Bool; "modop", Enum "MemAtomicOp";
    "nontemporal", Bool; "read", Bool; "write", Bool; "cacheop", Enum "CacheOp";
    "opscope", Enum "CacheOpScope"; "cachetype", Enum "CacheType";
    "pan", Bool; "transactional", Bool; "nonfault", Bool; "firstfault", Bool;
    "first", Bool; "contiguous", Bool; "streamingsve", Bool; "ls64", Bool;
    "mops", Bool; "rcw", Bool; "rcws", Bool; "toplevel", Bool;
    "varange", Enum "VARange"; "a32lsmd", Bool; "tagchecked", Bool; "tagaccess", Bool;
    "mpam", Record ["mpam_sp", Enum "PARTIDspaceType"; "partid", Word 16; "pmg", Word 8]
  ] in
  let fields = snd (Type_check.Env.get_record record env) in
  let mpam = match List.find_opt (fun (_, id) -> string_of_id id = "mpam") fields with
    | Some (typ, _) -> Type_check.Env.base_typ_of env typ
    | None -> fail loc "Arm AccessDescriptor lacks its MPAMinfo field" in
  (match mpam with
   | Typ_aux (Typ_id id, _) when string_of_id id = "MPAMinfo" &&
         Type_check.Env.is_record id env -> ()
   | _ -> fail loc "Arm AccessDescriptor requires its original MPAMinfo record");
  if exp_type ctx.widths exp <> expected then
    fail loc "Arm AccessDescriptor requires its complete original 33-field shape";
  expected

(* Arm and RV32 share one flat-access interpretation. Arm's source address,
   size, complete descriptor and store value have all been evaluated in
   source order before this leaf. Accesses are total and little-endian:
   translation, permissions, tags, aborts and device memory are deliberately
   outside this boundary. The original caller's SP/alignment checks remain.
   Each source access emits its own event; lane accesses are not coalesced.

   The RV32 memory leaf is a handwritten flat-access contract: compute a
   wrapped 32-bit address; if it is aligned to the access width, read/write
   that many little-endian bytes and prepend the matching memory event; if
   not, permit every final state. Return the source-shaped Ok result so its
   actual caller's result match is still translated. Width, flags, access
   constructor and result types are checked before selecting that contract.
   Of Sail's access path only the alignment test depends on state this view
   has; triggers, pointer masking, translation, page splits, PMP and PMA
   depend on CSRs and the platform, and are beyond it. *)
and flat_memory ctx exp continuation =
  let E_aux (aux, (loc, _)) = exp in
  match aux with
  | E_app (id, args) when List.mem (string_of_id id)
        ["Mem_read"; "Mem_read__1"; "Mem_set"; "Mem_set__1"] &&
        !state_type = "armstate" && !state_computation ->
      let name = string_of_id id in
      let load = List.mem name ["Mem_read"; "Mem_read__1"] in
      if is_defined_function name then
        fail loc (name ^ " must be an explicit external flat-memory boundary");
      let address, size, descriptor, flags, data = match name, args with
        | "Mem_read", [address; size; descriptor] -> address, size, descriptor, [], None
        | "Mem_read__1", [address; size; descriptor; ispair] ->
            address, size, descriptor, [ispair], None
        | "Mem_set", [address; size; descriptor; data] ->
            address, size, descriptor, [], Some data
        | "Mem_set__1", [address; size; descriptor; ispair; data] ->
            address, size, descriptor, [ispair], Some data
        | _ -> fail loc ("wrong primitive arity for " ^ name) in
      if exp_type ctx.widths address <> Word 64 || exp_type ctx.widths size <> Int then
        fail loc "Arm flat memory requires a bits(64) address and integer byte size";
      if List.exists (fun flag -> exp_type ctx.widths flag <> Bool) flags then
        fail loc "Arm pair accesses require a Boolean ispair argument";
      let size_bytes = constant_index ctx size in
      if not (List.mem size_bytes [1; 2; 4; 8; 16]) then
        fail loc "Arm flat memory supports only 1/2/4/8/16-byte accesses";
      ignore (arm_access_descriptor_type ctx descriptor);
      let width = 8 * size_bytes in
      let expected_result = if load then Word width else Unit in
      if exp_type ctx.widths exp <> expected_result ||
         Option.fold ~none:false
           ~some:(fun value -> exp_type ctx.widths value <> Word width) data then
        fail loc "Arm flat memory requires its exact size-dependent data/result type";
      (* Mem_read__2 and Mem_set__2 fault on a misaligned access only if
         AArch64_UnalignedAccessFaults holds: alignment checking is enabled
         (SCTLR_ELx.A), or the access is exclusive, atomic, acquire/release,
         GCS, RCW or LS64, which none of the forms here are. s2n-bignum
         assumes alignment checking is off, so this boundary never faults;
         the record states that assumption. *)
      used_primitives := name :: "Arm-total-little-endian-flat-memory" ::
        "Arm-no-alignment-fault" :: !used_primitives;
      successful_checks := "Arm-total-little-endian-flat-memory" :: !successful_checks;
      let state = Option.get ctx.state in
      let addr = fresh () and payload = fresh () and metadata = fresh () and next = fresh () in
      let component = Infix (":>", Atom "memory",
        App ("bytes" ^ string_of_int width, [Atom addr])) in
      let value, memory_state = match data with
        | None -> App ("read", [component; state]), state
        | Some value -> pure ctx value, App ("write", [component; Atom payload; state]) in
      let event = App ((if load then "EventLoad" else "EventStore"),
        [Tuple_term [Atom addr; nat size_bytes]]) in
      let updated = App ("write", [Atom "events"; App ("CONS", [
        event; App ("read", [Atom "events"; state])]); memory_state]) in
      let result = if load then Typed (Atom payload, Word width)
        else Typed (Atom "one", Unit) in
      (* The pair flag does not change ordinary total byte storage. Keep its
         computed value with metadata, rather than dropping the operand or
         constraining it to a convenient false value. *)
      let metadata_value = match flags with
        | [] -> pure ctx descriptor
        | _ -> Tuple_term (pure ctx descriptor :: List.map (pure ctx) flags) in
      let translated = Let (Atom addr, pure ctx address, Let (Atom metadata, metadata_value,
        Let (Atom payload, value, Let (Atom next, updated,
          continuation {ctx with state = Some (Atom next)} result)))) in
      (* The report shows the access with the address a, the descriptor b,
         and the stored value last. *)
      (match translated with
       | Let (_, address_value, Let (_, _, Let (_, accessed, Let (_, update, _)))) ->
           let bind term = Let (Atom addr, address_value, Let (Atom payload, accessed, term)) in
           let stored = Option.map (fun _ -> accessed) data in
           let last = String.make 1 (Char.chr (Char.code 'b' + 1 + List.length flags)) in
           let sail = Printf.sprintf "%s(a, %d, b%s%s)" name size_bytes
             (String.concat "" (List.mapi (fun index _ ->
                ", " ^ String.make 1 (Char.chr (Char.code 'c' + index))) flags))
             (if data = None then "" else ", " ^ last) in
           record_update ctx (name :: ["Arm-total-little-endian-flat-memory";
               "Arm-no-alignment-fault"]) sail
             ([address_value, "a"] @
              Option.fold ~none:[] ~some:(fun value -> [value, last]) stored)
             ?result:(if load then Some (bind result) else None) (bind update)
       | _ -> assert false);
      translated
  | E_app (id, args) when List.mem (string_of_id id) ["vmem_read"; "vmem_write"]
                           && !state_type = "riscvstate" ->
      let name = string_of_id id in
      if is_defined_function name then
        fail loc (name ^ " must be an external primitive");
      let index, offset, width, data, access, flags =
        match name, args with
        | "vmem_read", [index; offset; width; access; aq; rl; res] ->
            index, offset, width, None, access, [aq; rl; res]
        | "vmem_write", [index; offset; width; data; access; aq; rl; res] ->
            index, offset, width, Some data, access, [aq; rl; res]
        | _ -> fail loc ("wrong primitive arity for " ^ name) in
      let size_bytes = constant_index ctx width in
      if not (List.mem size_bytes [1; 2; 4]) then
        fail loc "only 1-, 2- and 4-byte flat accesses are supported";
      let bits = 8 * size_bytes in
      List.iter (fun e ->
        if boolean_literal (pure ctx e) <> Some false then
          fail (exp_loc e) "flat access aq/rl/res flags must be literal false"
      ) flags;
      let expected = if name = "vmem_read" then "Load" else "Store" in
      require_flat_access_literal ctx expected access;
      if exp_type ctx.widths index <> Word 5 || exp_type ctx.widths offset <> Word 32 ||
         Option.fold ~none:false ~some:(fun e -> exp_type ctx.widths e <> Word bits) data then
        fail loc "flat access requires RV32 register/address/data types";
      let expected_result = if name = "vmem_read" then Result (Word bits, Unit)
                            else Result (Bool, Unit) in
      if exp_type ctx.widths exp <> expected_result then
        fail loc "flat access result must retain the success/error payload types";
      used_primitives :=
        name :: "RV32-misaligned-access-any-final-state" :: !used_primitives;
      let state = Option.get ctx.state in
      let addr = fresh () and payload = fresh () and next = fresh () in
      let component = Infix (":>", Atom "memory",
        App ("bytes" ^ string_of_int bits, [Atom addr])) in
      let addr_value = App ("word_add", [
        App ("read", [App ("riscv_gpr", [pure ctx index]); state]); pure ctx offset]) in
      (* vmem_read_addr and vmem_write_addr test is_aligned_addr(vaddr,
         width), that is unsigned(addr) % width == 0, on the address the
         instruction computed. This interpretation copies that test by hand;
         Sail's code is not translated. A misaligned access then goes where
         plat_misaligned_exception and the platform configuration send it:
         memory.misaligned.exceptions, then the PMA regions. That
         configuration is outside this view, so a misaligned access permits
         every final state. *)
      let aligned = Infix ("=",
        Infix ("MOD", App ("val", [Atom addr]), nat size_bytes), nat 0) in
      let value, memory_state = match data with
        | None -> App ("read", [component; state]), state
        | Some data -> pure ctx data, App ("write", [component; Atom payload; state]) in
      let event = App ((if name = "vmem_read" then "EventLoad" else "EventStore"),
                       [Tuple_term [Atom addr; nat size_bytes]]) in
      let updated = App ("write", [Atom "events"; App ("CONS", [
        event; App ("read", [Atom "events"; state])]); memory_state]) in
      let result = Typed (App ("INL", [if name = "vmem_read" then Atom payload else Atom "T"]),
                          expected_result) in
      let translated = Let (Atom addr, addr_value, Cond (aligned,
        Let (Atom payload, value, Let (Atom next, updated,
          continuation {ctx with state = Some (Atom next)} result)),
        Fault)) in
      (* The report shows the access with the register index a, the offset
         b and the stored value c, as the new state and the result where
         the address is aligned. *)
      (match translated with
       | Let (_, address_value, Cond (condition, Let (_, accessed, Let (_, update, _)), _)) ->
           let placeholders = match address_value, data with
             | App (_, [App ("read", [App (_, [index_value]); _]); offset_value]), _ ->
                 [index_value, "a"; offset_value, "b"] @
                 (if data = None then [] else [accessed, "c"])
             | _ -> assert false in
           let text = interpretation_text
             (placeholders @ [Atom addr, "addr"] @ state_placeholders ctx) in
           let bind term = Let (Atom payload, accessed, term) in
           record_interpretation [name; "RV32-misaligned-access-any-final-state"]
             (Printf.sprintf "%s(a, b, %d, %s%s, false, false, false)" name size_bytes
                (if data = None then "" else "c, ")
                (string_of_exp (Type_check.strip_exp access)))
             (Printf.sprintf
                "for addr = %s: if %s (a copy of Sail's is_aligned_addr, not its \
                 translation) then s' = %s, returning %s; else every final state, \
                 in place of Sail's plat_misaligned_exception, whose outcome the \
                 platform chooses"
                (text address_value) (text condition) (text (bind update))
                (text (bind result)))
       | _ -> assert false);
      translated
  | _ -> fail loc "expected an Arm or RV32 flat memory primitive"

(* Ordinary register and RV32 register-file writes. Their arguments have
   already been captured by computation_arguments. *)
let simple_write ctx exp continuation =
  let E_aux (aux, (loc, _)) = exp in
  let state = match ctx.state with Some s -> s | None -> assert false in
  let advance update =
    let next = fresh () in
    Let (Atom next, update, continuation {ctx with state = Some (Atom next)}) in
  match aux with
  | E_assign (LE_aux ((LE_id id | LE_typ (_, id)), _), value) ->
      if not (Type_check.Env.is_register id (Type_check.env_of exp)) then
        fail loc "local mutation is unsupported";
      let name = string_of_id id in
      refuse_bound_gpr loc name;
      (* register reads freeze the instruction PC at entry. An ordinary
         assignment cannot change that value, so accepting it would make a
         later PC read disagree with the sequential source execution. *)
      if !state_type = "riscvstate" && name = "PC" then
        fail loc "source current PC is read-only; use the next-PC interface";
      used_registers := name :: !used_registers;
      let update = App ("write", [Atom (symbol "reg_" name); pure ctx value; state]) in
      (match update with
       | App (_, [_; written; _]) ->
           record_update ctx ["typed-register-component-write"] (name ^ " = a")
             [written, "a"] update
       | _ -> assert false);
      advance update
  | E_app (id, [index; value]) when string_of_id id = "wX_bits"
                                      && !state_type = "riscvstate" ->
      if is_defined_function "wX_bits" then
        fail loc "wX_bits must be an external primitive";
      if List.map (exp_type ctx.widths) [index; value; exp] <> [Word 5; Word 32; Unit] then
        fail loc "wX_bits requires RV32 register/value types and unit result";
      used_primitives := "wX_bits" :: !used_primitives;
      let update = App ("write", [
        App ("riscv_gpr", [pure ctx index]); pure ctx value; state]) in
      (match update with
       | App (_, [App (_, [index_value]); written; _]) ->
           record_update ctx ["wX_bits"] "wX_bits(a, b)" [index_value, "a"; written, "b"] update
       | _ -> assert false);
      advance update
  | _ -> fail loc ("unsupported state AST node: " ^ string_of_exp (Type_check.strip_exp exp))

(* Sail desugars a numeric literal pattern on a bitvector, such as
     match nbytes { 1 => ..., 2 => ..., _ => ... }
   with an overloaded == into a variable pattern with a guard:
     v if eq_bits_nat(v, 1) => ...
   General guards like this have no fixed equality shape. Select clauses
   in source order: a variable or wildcard pattern always matches, so the
   first clause whose guard holds is taken. Guards are pure source
   expressions, translated with the clause's binding. A guard that
   translates to a literal selects or skips its clause; its evaluation is
   kept. Otherwise the clause becomes a HOL conditional. A match with no
   applicable final clause fails rather than invent a default. *)
let rec guarded_clause_pattern (P_aux (aux, _)) =
  match aux with
  | P_typ (_, pattern) -> guarded_clause_pattern pattern
  | P_id id -> Some (Some id)
  | P_wild -> Some None
  | _ -> None

let guarded_variable_clauses clauses =
  List.exists (function Pat_aux (Pat_when _, _) -> true | _ -> false) clauses &&
  List.for_all (fun clause ->
    let pattern, _, _, _ = destruct_pexp clause in
    Option.is_some (guarded_clause_pattern pattern)) clauses

let guarded_match ctx loc clauses value branch =
  let bind pattern =
    match guarded_clause_pattern pattern with
    | Some (Some id) -> {ctx with locals = (string_of_id id, value) :: ctx.locals}
    | Some None -> ctx
    | None -> fail loc "guarded matches require variable or wildcard patterns" in
  let rec select = function
    | [] -> fail loc "guarded match has no clause for every value"
    | clause :: rest ->
        let pattern, guard, body, _ = destruct_pexp clause in
        let inner = bind pattern in
        match guard with
        | None -> branch inner body
        | Some guard ->
            if exp_type inner.widths guard <> Bool then
              fail (exp_loc guard) "match guards must be Boolean";
            let condition = pure inner guard in
            match boolean_literal condition with
            | Some true -> Let (Atom (fresh ()), condition, branch inner body)
            | Some false -> Let (Atom (fresh ()), condition, select rest)
            | None -> Cond (condition, branch inner body, select rest) in
  select clauses

(* Translate an evaluated value together with its sequential state/local
   updates. Used by unit-returning instructions and retirement relations.
   return_cont exits the current helper; continuation carries on normally.
   Keeping them separate prevents an early helper return from exiting its
   caller. Retirement assertions restrict the relation; ordinary computation
   assertions are proved or retained as guards on permitted normal outcomes.

   continuation : context -> term -> term is "continue with this value/state".
   return_cont has the same shape but denotes the current helper's return.
   The OCaml callbacks build the rest of the HOL expression at export time.
   For a defined call, finish resumes its caller with final.state, while the
   callee's parameters/locals/widths remain scoped to the callee.

   Local assignment replaces ctx.locals with a fresh binding. Register
   assignment instead emits write(component,value,current_state). Shadowed
   locals and type facts are restored on lexical exit; outer mutable updates
   and state changes survive. Partial-word masks survive copying and slicing.
   Thus source mutation becomes ordinary HOL binding structure, not mutation
   of a HOL evaluator or of the OCaml exporter's architectural state.

   A dynamic branch emits a conditional (or guarded retirement relation) and
   continues separately from each branch's resulting context. Static branches
   can select one arm only after its condition has a known translated value.
   Finite loops are expanded with the same state/local sequencing; runtime
   unbounded iteration and unsupported exits fail. *)
let rec computation ctx (E_aux (aux, (loc, _)) as exp) return_cont continuation =
  (match aux with E_assign (target, _) ->
     check_assumed_write ctx (Type_check.env_of exp) target | _ -> ());
  let unit = Typed (Atom "one", Unit) in
  let arm_set ctx id index width value continuation =
    let name = string_of_id id in
    if is_defined_function name then
      fail loc (name ^ " must be an explicit external contract");
    if List.map (exp_type ctx.widths) [index; width] <> [Int; Int] then
      fail loc (name ^ " requires integer index and width");
    let n = constant_index ctx width in
    if name = "X_set" && n <> 32 && n <> 64 then
      fail loc "X_set supports only 32/64-bit general registers";
    if name = "V_set" && not (List.mem n [8; 16; 32; 64; 128]) then
      fail loc "V_set supports only 8/16/32/64/128-bit vector values";
    require_integer_interval ctx index (pure ctx index) 0 31
      (name ^ " index is not proved in 0..31");
    used_primitives := name :: !used_primitives;
    let index_value = pure ctx index in
    let component = App (
      (if name = "X_set" then if n = 32 then "WREG" else "XREG"
       else if n = 64 then "DREG" else "QREG"),
      [App ("num_of_int", [index_value])]) in
    let observed = observable_value loc value in
    let value = if name = "V_set" && n < 64 then begin
      used_primitives := "V_set-small-zero-top" :: !used_primitives;
      Typed (App ("word_zx", [Typed (observed, Word n)]), Word 128)
    end else observed in
    record_update ctx
      (name :: if name = "V_set" && n < 64 then ["V_set-small-zero-top"] else [])
      (Printf.sprintf "%s(a, %d, b)" name n) [index_value, "a"; observed, "b"]
      (App ("write", [component; value; Option.get ctx.state]));
    let next = fresh () in
    Let (Atom next, App ("write", [component; value; Option.get ctx.state]),
      continuation {ctx with state = Some (Atom next)}) in
  let rec assign ctx (LE_aux (aux, (lloc, _)) as lexp) value continuation =
    (* armstate has no FPSR or branch-target metadata. Exclude only the
       final write to the named register with its exact declared type,
       not evaluation of its selectors or value.
       E_assign has already threaded those evaluations through computation;
       reads, assertions and writes to other registers remain observable.
       This is an explicit observation boundary, not physical preservation
       of these registers or a claim about later FPSR/BTI checks. Ordinary
       locals never reach this register-only path; reads remain components. *)
    let omit_unrepresented_write id declared =
      if !state_type <> "armstate" || not !state_computation then false
      else match string_of_id id with
      | "FPSR" ->
          (match declared with
           | Word 64 | Record [(_, Word 64)] -> ()
           | _ -> fail lloc "FPSR write exclusion requires its declared 64-bit container");
          used_primitives := "Arm-FPSR-write-exclusion" :: !used_primitives;
          record_interpretation ["Arm-FPSR-write-exclusion"]
            (string_of_lexp (Type_check.strip_lexp lexp) ^ " = a") "s' = s";
          true
      | "BTypeNext" | "BTypeCompatible" as name ->
          let expected = if name = "BTypeNext" then Word 2 else Bool in
          if declared <> expected then
            fail lloc (name ^ " write exclusion requires its declared " ^
              (if name = "BTypeNext" then "two-bit word" else "Boolean") ^ " type");
          used_primitives := "Arm-BType-write-exclusion" :: !used_primitives;
          record_interpretation ["Arm-BType-write-exclusion"]
            (string_of_lexp (Type_check.strip_lexp lexp) ^ " = a") "s' = s";
          true
      | _ -> false in
    (* record: the interpretation names, the Sail assignment, the
       placeholders and the one for the written value, if any. *)
    let advance ?record component value =
      let value = observable_value lloc value in
      Option.iter (fun (names, sail, placeholders, value_placeholder) ->
        record_update ctx names sail
          (placeholders @ Option.fold ~none:[] ~some:(fun name -> [value, name])
             value_placeholder)
          (App ("write", [component; value; Option.get ctx.state]))) record;
      let next = fresh () in
      Let (Atom next, App ("write", [component; value; Option.get ctx.state]),
           continuation {ctx with state = Some (Atom next)}) in
    let without_write () =
      (* A range replacement includes an implicit read of the old packed
         register. Bind that calculated value even though the write is
         omitted, rather than also discarding the read-modify calculation. *)
      Let (Atom (fresh ()), observable_value lloc value, continuation ctx) in
    match aux with
    | LE_vector (base, index) when x86_bank_target ctx base ->
        if hol_type ctx.widths (Type_check.env_of_lexp lexp)
            (Type_check.typ_of_lexp lexp) <> Word 64 then
          fail lloc "x86 raw GPR element write requires bits(64)";
        let index_value = pure ctx index in
        advance ~record:(["x86-raw-GPR-bank"],
            string_of_lexp (Type_check.strip_lexp base) ^ "[a] = b",
            [index_value, "a"], Some "b")
          (x86_bank_component ctx index index_value) value
    | LE_id id | LE_typ (_, id) when not
        (Type_check.Env.is_register id (Type_check.env_of exp)) ->
        let name = string_of_id id in
        if not (List.mem name ctx.mutable_locals) then
          fail lloc ("assignment to a non-mutable local: " ^ name);
        let next = fresh () in
        let binding = alias_value (Atom next) value in
        Let (Atom next, value, continuation {ctx with
          locals = (name, binding) :: List.remove_assoc name ctx.locals;
          uninitialized = (if Option.is_some (partial_word value) then [name] else []) @
            List.filter ((<>) name) ctx.uninitialized})
    | LE_id id | LE_typ (_, id) ->
        let env = Type_check.env_of exp in
        if not (Type_check.Env.is_register id env) then
          fail lloc "normal register writes require a declared source register";
        let name = string_of_id id in
        refuse_bound_gpr lloc name;
        if List.mem name ["PC"; "_PC"; "PSTATE"; "SPESampleInFlight"] then
          fail lloc "projected or frozen source registers require their explicit write interface";
        let declared = hol_type ctx.widths env (Type_check.Env.get_register id env) in
        (match declared with
         | Bool | Word _ -> ()
         | Record [(_, (Bool | Word _))] ->
             (* A source bitfield record is one declared packed field.
                Its HOL representation is that field's type. Preserve the
                checked constructor/helper calculation and write the same
                explicit component, except the named observation boundaries. *)
             ()
         | _ -> fail lloc "normal register writes support only declared words, Booleans and single packed fields");
        if hol_type ctx.widths env (Type_check.typ_of_lexp lexp) <> declared then
          fail lloc "register write type disagrees with the declared source register";
        if omit_unrepresented_write id declared then without_write ()
        else if Option.is_some (x86_flag lloc env id) then
          advance ~record:(["x86-six-Boolean-flags"], name ^ " = a",
              [observable_value lloc value, "a"], None)
            (Atom name) (App ("bit", [nat 0; value]))
        else begin
          used_registers := name :: !used_registers;
          used_primitives := "typed-register-component-write" :: !used_primitives;
          advance ~record:(["typed-register-component-write"], name ^ " = a", [], Some "a")
            (Atom (symbol "reg_" name)) value
        end
    | LE_tuple lexps ->
        if contains_partial value then fail lloc "partial tuple assignment is unsupported";
        let rec split ctx = function
          | [], _ -> continuation ctx
          | [lexp], value -> assign ctx lexp value continuation
          | lexp :: rest, value ->
              assign ctx lexp (App ("FST", [value])) (fun next ->
                split next (rest, App ("SND", [value]))) in
        split ctx (lexps, value)
    | LE_vector_concat lexps ->
        if contains_partial value then fail lloc "partial concatenated assignment is unsupported";
        let widths = List.map (fun lexp ->
          match hol_type ctx.widths (Type_check.env_of exp) (Type_check.typ_of_lexp lexp) with
          | Word n -> n | _ -> fail lloc "concatenated assignments require bitvectors"
        ) lexps in
        let rec split ctx offset = function
          | [], [] -> continuation ctx
          | lexp :: rest, width :: widths ->
              let offset = offset - width in
              let piece = Typed (App ("word_subword", [value;
                Tuple_term [nat offset; nat width]]), Word width) in
              assign ctx lexp piece (fun next -> split next offset (rest, widths))
          | _ -> assert false in
        split ctx (List.fold_left (+) 0 widths) (lexps, widths)
    | LE_vector_range (base, high_expression, low_expression) ->
        let env = Type_check.env_of exp in
        let base_width = match hol_type ctx.widths env (Type_check.typ_of_lexp base) with
          | Word width -> width | _ -> fail lloc "a range write requires a bitvector local" in
        let width = match hol_type ctx.widths env (Type_check.typ_of_lexp lexp) with
          | Word width -> width | _ -> fail lloc "a range write requires a static word length" in
        let static = try Some (constant_index ctx high_expression,
                              constant_index ctx low_expression)
          with Reporting.Fatal_error _ -> None in
        let position = match static with
          | Some (high, low) ->
              if low < 0 || high >= base_width || high - low + 1 <> width then
                fail lloc "a range write requires matching static in-bounds bit positions";
              nat low
          | None ->
              let high_env, high = numeric_argument high_expression
              and _, low = numeric_argument low_expression in
              (match high, low with
               | Some high, Some low when prove_specialized ctx high_env
                   (nc_and (nc_lteq (nint 0) low)
                     (nc_and (nc_lt high (nint base_width))
                       (nc_eq (nsum (nminus high low) (nint 1)) (nint width)))) -> ()
               | _ -> fail lloc "dynamic range write requires proved matching in-bounds positions");
              App ("num_of_int", [pure ctx low_expression]) in
        let old = match base with
          | LE_aux (LE_vector (bank, index), _)
              when x86_bank_target ctx bank ->
              let index_value = pure ctx index in
              let read = App ("read", [x86_bank_component ctx index index_value;
                                       Option.get ctx.state]) in
              record_value ctx ["x86-raw-GPR-bank"]
                (string_of_lexp (Type_check.strip_lexp bank) ^ "[a]") [index_value, "a"] read;
              Typed (read, Word 64)
          | LE_aux (LE_id id, _) when List.mem (string_of_id id) ctx.mutable_locals ->
              (match List.assoc_opt (string_of_id id) ctx.locals with
               | Some old -> old | None -> fail lloc "range-write base is not bound")
          | LE_aux (LE_field (LE_aux (LE_id id, _), field), _) when
              Type_check.Env.is_register id env ->
              let declared = hol_type ctx.widths env (Type_check.Env.get_register id env) in
              (match declared with
               | Record [(declared_field, Word n)] when n = base_width &&
                     declared_field = string_of_id field &&
                     not (List.mem (string_of_id id) ["PC"; "_PC"; "PSTATE"; "SPESampleInFlight"]) ->
                   Typed (register lloc ctx id declared, Word n)
               | _ -> fail lloc "range writes require the sole declared packed register field")
          | _ -> fail lloc "a range write requires a mutable local or packed register field" in
        let updated, known = insert_word lloc base_width width old value
          (Option.map snd static) position "partial range-write width mismatch"
          "partial inserted-value width mismatch"
          "dynamic range writes require fully initialized base and inserted words" in
        assign ctx base (tracked_word updated base_width known) continuation
    | LE_field (LE_aux (LE_id id, _), field)
        when Type_check.Env.is_register id (Type_check.env_of exp) &&
             not (List.mem (string_of_id id) ["PC"; "_PC"; "PSTATE"; "SPESampleInFlight"]) ->
        let env = Type_check.env_of exp in
        (match hol_type ctx.widths env (Type_check.Env.get_register id env),
               hol_type ctx.widths env (Type_check.typ_of_lexp lexp) with
         | Record [(declared_field, Word width)], Word actual when
               declared_field = string_of_id field && width = actual ->
             if omit_unrepresented_write id (Record [(declared_field, Word width)])
             then without_write ()
             else begin
               used_registers := string_of_id id :: !used_registers;
               used_primitives := "typed-packed-register-field-write" :: !used_primitives;
               advance ~record:(["typed-packed-register-field-write"],
                   string_of_lexp (Type_check.strip_lexp lexp) ^ " = a", [], Some "a")
                 (Atom (symbol "reg_" (string_of_id id))) value
             end
         | _ -> fail lloc "field writes require the sole declared packed register field")
    | LE_field (LE_aux (LE_id register, _), field)
        when !state_type = "armstate" && !state_computation &&
             string_of_id register = "PSTATE" &&
             Type_check.Env.is_register register (Type_check.env_of exp) ->
        (match arm_flag (string_of_id field) with
         | Some component ->
             if hol_type ctx.widths (Type_check.env_of exp) (Type_check.typ_of_lexp lexp) <> Word 1 then
               fail lloc "PSTATE flag writes require one-bit fields";
             used_primitives := "PSTATE-NZCV-projection" :: !used_primitives;
             advance ~record:(["PSTATE-NZCV-projection"], "PSTATE." ^ string_of_id field ^ " = a",
                 [observable_value lloc value, "a"], None)
               (Atom component) (App ("bit", [nat 0; value]))
         | None -> fail lloc "unsupported PSTATE field write")
    | _ -> fail lloc ("unsupported computation assignment " ^
                       string_of_lexp (Type_check.strip_lexp lexp)) in
  match aux with
  | E_undef ->
      let typ = exp_type ctx.widths exp in
      let rec concrete = function
        | Dynamic_bits | Poly_word _ -> false
        | Tuple fields -> List.for_all concrete fields
        | Record fields -> List.for_all (fun (_, field) -> concrete field) fields
        | Result (ok, error) -> concrete ok && concrete error
        | Binary_variant ((_, a), (_, b)) -> concrete a && concrete b
        | Option_type payload -> concrete payload
        | _ -> true in
      if not (concrete typ) then
        fail loc "arbitrary values require a concrete supported type";
      (* Refinements of int/bool may describe a proper subset of the HOL
         carrier. Do not weaken those constraints to arbitrary values. The
         upstream __UNKNOWN_integer result is the unconstrained int type. *)
      let env = Type_check.env_of exp in
      let rec check_carrier source_type =
        match Type_check.destruct_bitvector env source_type with
        | Some _ -> ()
        | None ->
        let source_type = Type_check.Env.base_typ_of env source_type in
        match source_type with
        | Typ_aux (Typ_id id, _) when List.mem (string_of_id id)
            ["int"; "bool"; "unit"; "string"] -> ()
        | Typ_aux (Typ_tuple fields, _) -> List.iter check_carrier fields
        | Typ_aux (Typ_id id, _) when Type_check.Env.is_record id env ->
            let _, fields = Type_check.Env.get_record id env in
            List.iter (fun (field, _) -> check_carrier field) fields
        | Typ_aux (Typ_id id, _) when Type_check.Env.is_enum id env -> ()
        | Typ_aux (Typ_id id, _) when Type_check.Env.is_variant id env ->
            List.iter (fun (_, payload) -> check_carrier payload)
              (Type_check.instantiate_variant env id [])
        | Typ_aux (Typ_app (id, arguments), _) when
            List.mem (string_of_id id) ["result"; "option"] ->
            List.iter (function A_aux (A_typ payload, _) -> check_carrier payload
              | _ -> fail loc "arbitrary values require supported type arguments") arguments
        | _ -> fail loc "arbitrary refined values are unsupported" in
      (* An unknown refined integer, such as REMS's undefined nat, chooses
         any integer satisfying the refinement. The choice is existential
         like any other; a value outside the refinement has no outcome:
           ?v. if &0 <= v then <rest> else F
         Only comparisons of the bound variable with constants, and their
         conjunctions, are supported. Plain int keeps the unguarded choice. *)
      let refinement = if not (extended_evaluation ()) then None else
        match typ, Type_check.destruct_numeric
          (Type_check.Env.expand_synonyms env (Type_check.typ_of exp)) with
        | Int, Some ([kid], constraint_, Nexp_aux (Nexp_var bound, _))
            when Kid.compare kid bound = 0 &&
                 (match constraint_ with NC_aux (NC_true, _) -> false | _ -> true) ->
            Some (kid, constraint_)
        | _ -> None in
      (match refinement with
       | None -> check_carrier (Type_check.typ_of exp)
       | Some _ -> ());
      used_primitives := "Sail-undefined-existential" :: !used_primitives;
      let value = Typed (Atom (fresh ()), typ) in
      let sail = "undefined : " ^ type_text typ in
      let chosen = "v, where the whole relation is ?v:" ^ type_text typ ^ ". ..." in
      (match refinement with
       | None ->
           record_interpretation ["Sail-undefined-existential"] sail chosen;
           Choose (value, continuation ctx value)
       | Some (kid, constraint_) ->
           let rec number (Nexp_aux (aux, _)) = match aux with
             | Nexp_var variable when Kid.compare variable kid = 0 -> value
             | Nexp_constant n -> integer n
             | _ -> fail loc "refined unknown integers require constant bounds" in
           let rec condition (NC_aux (aux, _)) = match aux with
             | NC_ge (left, right) -> Infix (">=", number left, number right)
             | NC_gt (left, right) -> Infix (">", number left, number right)
             | NC_le (left, right) -> Infix ("<=", number left, number right)
             | NC_lt (left, right) -> Infix ("<", number left, number right)
             | NC_and (left, right) -> Infix ("/\\", condition left, condition right)
             | NC_true -> Atom "T"
             | _ -> fail loc "unsupported refinement of an unknown integer" in
           used_primitives := "Sail-undefined-refined-integer" :: !used_primitives;
           let condition = Typed (condition constraint_, Bool) in
           record_interpretation
             ["Sail-undefined-existential"; "Sail-undefined-refined-integer"] sail
             ("v, where the whole relation is ?v:" ^ type_text typ ^ ". if " ^
              interpretation_text [value, "v"] condition ^ " then ... else no final state");
           Choose (value, Cond (condition, continuation ctx value, Reject)))
  | E_exit argument ->
      (* Sail can simplify assert(false) to exit(). An abort has no normal
         instruction outcome; it is neither a normal stop nor a fault.
         Retain evaluation of the original unit argument before rejection. *)
      if exp_type ctx.widths argument <> Unit then
        fail loc "source abort requires a unit argument";
      used_primitives := "Sail-exit-no-normal-state" :: !used_primitives;
      record_interpretation ["Sail-exit-no-normal-state"] "exit()" "no final state";
      computation ctx argument return_cont (fun _ value ->
        Let (Atom (fresh ()), value, Reject))
  | E_app (id, [argument]) when string_of_id id = "EndOfInstruction" &&
        !state_type = "armstate" && !upstream_architecture = Some "aarch64" ->
      if is_defined_function "EndOfInstruction" then
        fail loc "EndOfInstruction must be an explicit normal-termination boundary";
      if exp_type ctx.widths argument <> Unit || exp_type ctx.widths exp <> Unit then
        fail loc "EndOfInstruction requires unit -> unit";
      used_primitives := "Arm-normal-instruction-termination" :: !used_primitives;
      record_interpretation ["Arm-normal-instruction-termination"; "EndOfInstruction"]
        "EndOfInstruction()" "the instruction ends, with final state s";
      computation ctx argument return_cont (fun next value ->
        Let (Atom (fresh ()), value, Stop (Option.get next.state)))
  | E_throw thrown when x86_binds X86.Uncaught_exceptions ->
      (* REMS's x86_fault and x86_model_error throw an Emsg message, and the
         translator supports no try/catch, so the throw ends the instruction.
         It has no normal final state; the relation admits none on this path.
         An agreement with a relation that always has a final state therefore
         shows the path unreachable. A reached throw is not given an
         arbitrary final state. Building the message has no effect and is
         not translated; anything else in the thrown expression rejects. *)
      let rec effect_free (E_aux (aux, _) as exp) =
        match aux with
        | E_lit _ -> true
        | E_id id -> not (Type_check.Env.is_register id (Type_check.env_of exp))
        | E_typ (_, value) -> effect_free value
        | E_app (id, values) ->
            Effects.function_is_pure id !effect_info && List.for_all effect_free values
        | _ -> false in
      if not (effect_free thrown) then
        fail loc "x86 exception messages must be effect-free";
      used_primitives := "x86-uncaught-exception-no-normal-state" :: !used_primitives;
      record_interpretation ["x86-uncaught-exception-no-normal-state"] "throw a"
        "no final state";
      Reject
  | E_throw (E_aux (E_app (id, [argument]), _) as thrown)
        when string_of_id id = "Error_Undefined" &&
             !state_type = "armstate" && !upstream_architecture = Some "aarch64" ->
      (* Arm's execution wrapper maps precisely this source constructor to
         AArch64_UndefinedFault. Other throws, including ExceptionTaken used
         by normal termination, are not architectural faults by this rule. *)
      let env = Type_check.env_of thrown in
      let _, constructor_type = Type_check.Env.get_union_id id env in
      let payload = match constructor_type with
        | Typ_aux (Typ_fn ([payload], _), _) -> payload
        | _ -> fail loc "architectural undefined fault requires a unit constructor" in
      let exception_type = Type_check.Env.base_typ_of env (Type_check.typ_of thrown) in
      if exp_type ctx.widths argument <> Unit ||
         hol_type ctx.widths env payload <> Unit ||
         (match exception_type with
          | Typ_aux (Typ_id id, _) -> string_of_id id <> "exception"
          | _ -> true) then
        fail loc "architectural undefined fault requires exception.Error_Undefined(unit)";
      used_primitives := "Arm-undefined-fault-any-final-state" :: !used_primitives;
      record_interpretation ["Arm-undefined-fault-any-final-state"]
        "throw Error_Undefined()" "every final state";
      computation ctx argument return_cont (fun _ value ->
        Let (Atom (fresh ()), value, Fault))
  | E_app (id, [argument]) when !state_type = "armstate" &&
        !upstream_architecture = Some "aarch64" &&
        List.mem (string_of_id id) Arm.faults ->
      let name = string_of_id id in
      if is_defined_function name then
        fail loc (name ^ " must be an explicit architectural-fault boundary");
      if exp_type ctx.widths argument <> Unit || exp_type ctx.widths exp <> Unit then
        fail loc (name ^ " requires unit -> unit");
      used_primitives := "Arm-fault-any-final-state" :: name :: !used_primitives;
      record_interpretation [name; "Arm-fault-any-final-state"] (name ^ "()")
        "every final state";
      computation ctx argument return_cont (fun _ value ->
        Let (Atom (fresh ()), value, Fault))
  | E_typ (_, e) -> computation ctx e return_cont continuation
  | E_block es ->
      let rec sequence ctx = function
        | [] -> continuation ctx unit
        | [e] -> computation ctx e return_cont continuation
        | e :: rest -> computation ctx e return_cont (fun next _ -> sequence next rest)
      in sequence ctx es
  | E_let (pat, initial_expression, body) ->
      transfer_computation ctx initial_expression return_cont (fun next value ->
        let p, locals = pattern next.widths next.locals pat in
        let locals = literal_bindings pat value locals in
        let scoped = hide_uninitialized (static_numeric_binding
          (numeric_binding_scope next pat initial_expression body) pat value) pat in
        Let (p, value, computation {scoped with locals} body return_cont (fun final value ->
          continuation (restore_binding_scope ctx final pat) value)))
  | E_var (LE_aux ((LE_id id | LE_typ (_, id)), _), initial_value, body) ->
      let name = string_of_id id in
      let rec undefined = function
        | E_aux (E_typ (_, e), _) -> undefined e
        | E_aux (E_undef, _) -> true
        | _ -> false in
      let finish final result =
        (* A declaration shadows any outer local with the same name. *)
        let final = {final with locals = List.remove_assoc name final.locals;
          uninitialized = List.filter ((<>) name) final.uninitialized} in
        let final = match List.assoc_opt name ctx.locals with
          | Some value -> {final with locals = (name, value) :: final.locals}
          | None -> final in
        let final = if List.mem name ctx.uninitialized then
            {final with uninitialized = name :: final.uninitialized}
          else final in
        continuation (restore_scope ctx final) result in
      if undefined initial_value && exp_type ctx.widths initial_value = Int then
        computation ctx initial_value return_cont (fun next value ->
          computation {next with mutable_locals = name :: next.mutable_locals;
            locals = (name, value) :: List.remove_assoc name next.locals;
            uninitialized = List.filter ((<>) name) next.uninitialized}
            body return_cont finish)
      else if undefined initial_value then begin
        unobserved_undefined := name :: !unobserved_undefined;
        (* word 0 only backs the bits not yet written: every observation
           of the local must go through observable_value or a mask check,
           which reject uninitialized bits. *)
        let locals = match exp_type ctx.widths initial_value with
          | Word width ->
              (name, tracked_word (App ("word", [nat 0])) width []) ::
                List.remove_assoc name ctx.locals
          | Empty_bits ->
              (name, Typed (Atom "one", Empty_bits)) :: List.remove_assoc name ctx.locals
          | _ -> List.remove_assoc name ctx.locals in
        computation {ctx with mutable_locals = name :: ctx.mutable_locals;
          locals;
          uninitialized = (if exp_type ctx.widths initial_value = Empty_bits then [] else [name]) @
            ctx.uninitialized} body return_cont finish
      end else transfer_computation ctx initial_value return_cont (fun next value ->
        let local = fresh () in
        let binding = alias_value (Atom local) value in
        Let (Atom local, value, computation {next with
          mutable_locals = name :: next.mutable_locals;
          locals = (name, binding) :: List.remove_assoc name next.locals;
          uninitialized = (if Option.is_some (partial_word value) then [name] else []) @
            List.filter ((<>) name) next.uninitialized}
          body return_cont finish))
  | E_return value -> transfer_computation ctx value return_cont return_cont
  | E_for (index, first, last, step, order, body) ->
      (* Sail foreach bounds are inclusive, with an explicit direction and
         positive step. Only static first/last/step values are accepted.
         At most 256 iterations per loop and 4096 expansion steps per root
         bound code generation, not source runtime execution.

         Loops without returns join branch-local state/locals into a tuple
         before expanding the next iteration. This prevents duplicating the
         remaining loop in every branch (exponential code growth). Loops with
         early returns keep the return/normal continuations separate. At each
         join, only bits assigned on every normal exit remain known. *)
      let known expression =
        let value = pure ctx expression in
        let number = match integer_literal value with
          | Some number -> number
          | None ->
              (try Nat_big_num.of_int (constant_index ctx expression)
               with Reporting.Fatal_error _ ->
                 fail (exp_loc expression) "foreach bounds must be statically known integers") in
        value, number in
      let first_term, first = known first and last_term, last = known last
      and step_term, step = known step in
      if not (Nat_big_num.greater step Nat_big_num.zero) then
        fail loc "foreach step must be a positive static integer";
      let ascending = is_order_inc order in
      let distance = if ascending then Nat_big_num.sub last first else Nat_big_num.sub first last in
      let count = if Nat_big_num.less distance Nat_big_num.zero then Nat_big_num.zero
        else Nat_big_num.add (Nat_big_num.div distance step) (Nat_big_num.of_int 1) in
      if Nat_big_num.greater count (Nat_big_num.of_int 256) then
        fail loc "foreach exceeds the 256-iteration static bound";
      let count = Nat_big_num.to_int count in
      unrolled_loops := (string_of_id index ^ " " ^ Nat_big_num.to_string first ^ " " ^
        Nat_big_num.to_string last ^ " " ^ Nat_big_num.to_string step ^ " " ^
        (if ascending then "inc" else "dec")) :: !unrolled_loops;
      let returns = has_source_return body in
      let name = string_of_id index and kid = mk_kid ("loop_" ^ string_of_id index) in
      let enter outer value =
        let bound = try Nat_big_num.to_int value with _ ->
          fail loc "foreach index exceeds the supported static integer range" in
        let old_env = Type_check.env_of exp and new_env = Type_check.env_of body in
        let renamed = if KBindings.mem kid (Type_check.Env.get_typ_vars old_env) &&
            Type_check.Env.shadows kid new_env > Type_check.Env.shadows kid old_env then
            Some (mk_kid (kid_name kid ^ "#" ^
              string_of_int (Type_check.Env.shadows kid old_env))) else None in
        let widths = List.filter_map (fun (old, value) ->
          if old <> kid_name kid then Some (old, value)
          else Option.map (fun renamed -> kid_name renamed, value) renamed
        ) outer.widths in
        let numeric_facts = List.filter_map (fun fact ->
          if not (KidSet.mem kid (tyvars_of_constraint fact)) then Some fact
          else Option.map (fun renamed ->
            constraint_subst kid (arg_nexp (nvar renamed)) fact) renamed
        ) outer.numeric_facts in
        {outer with widths = (kid_name kid, bound) :: widths; numeric_facts;
          locals = (name, Typed (integer value, Int)) :: List.remove_assoc name outer.locals;
          uninitialized = List.filter ((<>) name) outer.uninitialized} in
      let leave outer inner =
        let restored = restore_scope outer inner in
        {restored with widths = outer.widths; numeric_facts = outer.numeric_facts;
          locals = List.filter (fun (local, _) -> local <> name) restored.locals @
                   List.filter (fun (local, _) -> local = name) outer.locals;
          uninitialized = List.filter ((<>) name) restored.uninitialized @
                   List.filter ((=) name) outer.uninitialized} in
      let rec iterate outer value remaining =
        if remaining = 0 then continuation outer unit else begin
          incr loop_budget;
          if !loop_budget > 4096 then fail loc "static loop expansion budget exceeded";
          let scoped = enter outer value in
          let next_index = if ascending then Nat_big_num.add value step else Nat_big_num.sub value step in
          if returns then
            (* HighestSetBit returns on its selected bit and only expands
               the continuation on the other branch: a linear decision tree. *)
            computation scoped body return_cont (fun final _ ->
              iterate (leave outer final) next_index (remaining - 1))
          else begin
            computation_join loc outer
              (fun finish -> computation scoped body return_cont (fun final _ ->
                finish (leave outer final)))
              (fun joined -> iterate joined next_index (remaining - 1))
          end
        end in
      let first_bound = fresh () and last_bound = fresh () and step_bound = fresh () in
      Let (Atom first_bound, first_term, Let (Atom last_bound, last_term,
        Let (Atom step_bound, step_term, iterate ctx first count)))
  | E_if (condition, yes, no) ->
      let source_condition = condition in
      let branches finish =
        computation ctx condition return_cont (fun next condition ->
          (* A condition Sail's checked type proves, such as a bound that
             flow typing established on an earlier branch, is also known. *)
          let known = match term_atom condition with
            | Some "T" -> Some true | Some "F" -> Some false
            | _ when extended_evaluation () ->
                evaluated_boolean_truth next source_condition condition
            | _ -> None in
          match known with
          | Some truth ->
              record_selected_branch next source_condition truth
                ~by_z3:(term_atom condition = None);
              computation next (if truth then yes else no) return_cont finish
          | None -> Cond (condition,
              computation (source_comparison_context next source_condition condition true)
                yes return_cont finish,
              computation (source_comparison_context next source_condition condition false)
                no return_cont finish)) in
      (* Join the complete conditional, including evaluation of its condition.
         A short-circuit Boolean condition may itself have several exits;
         joining only inside its callback would still copy the following
         instruction code into each of those exits.

         Explicit source returns retain their separate handler: unlike
         faults and normal early termination, they are not control markers
         that lower_faults can propagate through an intermediate value. *)
      if !state_computation && Option.is_some ctx.state &&
         exp_type ctx.widths exp = Unit &&
         not (List.exists has_source_return [condition; yes; no]) then
        computation_join loc ctx
          (fun finish -> branches (fun final _ ->
            finish (restore_scope ctx final)))
          (fun joined -> continuation joined unit)
      else branches continuation
  | E_match (scrutinee, clauses) ->
      check_clause_patterns ctx clauses;
      let branches finish =
        computation ctx scrutinee return_cont (fun next value ->
          (* A helper's return can carry a partially assigned word. *)
          let value = observable_value loc value in
          let branch ctx body = computation ctx body return_cont (fun final value ->
            finish (restore_scope next final) value) in
          match exp_type ctx.widths scrutinee with
          | Result _ -> result_match next scrutinee clauses value branch
          | Binary_variant ((left, _), (right, _)) ->
              binary_variant_match next scrutinee clauses value left right branch
          | Option_type _ -> option_match next scrutinee clauses value branch
          | Unit_variant (_, members) -> unit_variant_match next members clauses value branch
          | Enum _ -> enum_match next scrutinee clauses value (branch next)
          | (Int | Word _) when extended_evaluation () &&
                guarded_variable_clauses clauses ->
              guarded_match next loc clauses value branch
          | Bool when extended_evaluation () ->
              boolean_match loc clauses value (branch next)
          | Int -> constant_integer_match loc clauses value (branch next)
          | Word n when n <= 8 -> word_match loc n clauses value (branch next)
          | Tuple types when List.for_all (function Word _ -> true | _ -> false) types ->
              tuple_word_match loc (List.map (function Word n -> n | _ -> 0) types)
                clauses value (branch next)
          | _ -> fail loc "unsupported computation match type") in
      let returns = has_source_return scrutinee || List.exists (function
        | Pat_aux (Pat_exp (_, body), _) -> has_source_return body
        | Pat_aux (Pat_when (_, guard, body), _) ->
            has_source_return guard || has_source_return body) clauses in
      if !state_computation && Option.is_some ctx.state &&
         exp_type ctx.widths exp = Unit && not returns then
        computation_join loc ctx
          (fun finish -> branches (fun final _ ->
            finish (restore_scope ctx final)))
          (fun joined -> continuation joined unit)
      else branches continuation
  | E_assert (condition, message) ->
      (match message with
       | E_aux (E_lit (L_aux (L_string _, _)), _) -> ()
       | _ -> fail loc "assertion messages must be literal strings");
      let env = Type_check.env_of condition in
      (* Evaluate the condition before asking Sail to prove a symbolic fact.
         An already calculated true/false value needs no second solver call.
         Keep the original source context for the remaining proof query. *)
      let proved = lazy (
        match Type_check.destruct_atom_bool env (Type_check.typ_of condition) with
        | Some constraint_ -> prove_specialized ctx env constraint_
        | None -> false) in
      computation ctx condition return_cont (fun next value ->
        if boolean_literal value = Some true ||
           (boolean_literal value <> Some false && Lazy.force proved) then begin
           record_proved_assertion next exp condition
             ~by_z3:(boolean_literal value <> Some true);
           Let (Atom (fresh ()), value, continuation next unit)
        end else begin
           guarded_assertions := assertion_text condition :: !guarded_assertions;
           if !state_computation then Cond (value, continuation next unit, Reject)
           else Infix ("/\\", value, continuation next unit)
        end)
  | E_app (id, operands) when is_and_bool id || is_or_bool id ->
      let left, right = short_circuit_operands ctx exp id operands in
      (* Evaluate the left operand once, retaining its writes and returns.
         Only its value decides whether to evaluate the right operand.
         A taken return on either side uses the enclosing return handler;
         an ordinary right-hand value uses the expression continuation. *)
      computation ctx left return_cont (fun next condition ->
        let truth = evaluated_boolean_truth next left condition in
        let constant value = continuation next (Typed (Atom value, Bool)) in
        let evaluate_right truth =
          computation (source_comparison_context next left condition truth)
            right return_cont continuation in
        (* An unknown left operand otherwise copies the rest of the
           computation into both arms. When the right operand translates as
           a pure value, it has no effects, faults or returns to order, so
           its conditional value is passed to one continuation instead:
             x & y  ~>  if x then y else F
           REMS's signed_byte_p tests a range this way. Sources that keep
           their established exports leave this off. *)
        let joined = if truth <> None || not (extended_evaluation ())
          then None else begin
            let restore = translation_checkpoint () in
            let inner = source_comparison_context next left condition
              (is_and_bool id) in
            try Some (pure inner right) with
            | Reporting.Fatal_error _ -> restore (); None
          end in
        match joined with
        | Some value ->
            continuation next (Typed ((if is_and_bool id
              then Cond (condition, value, Atom "F")
              else Cond (condition, Atom "T", value)), Bool))
        | None ->
        if is_and_bool id then
          match truth with
          | Some true -> evaluate_right true
          | Some false -> constant "F"
          | None -> Cond (condition, evaluate_right true, constant "F")
        else
          match truth with
          | Some true -> constant "T"
          | Some false -> evaluate_right false
          | None -> Cond (condition, constant "T", evaluate_right false))
  | E_app (id, args) when Option.is_some (find_function ctx.functions (string_of_id id)) ->
      computation_arguments ctx args return_cont true (fun ctx args cleanup ->
      let name = string_of_id id in
      let _, body, pat = Option.get (find_function ctx.functions name) in
      let body, pat = specialize_helper_types ctx exp body pat args in
      let callee = specialize_helper ~check_result:(not (generic_widths_active ()))
        ~value_measure:(fun () -> recursion_value_measure ctx name pat args)
        ctx exp name body pat args in
      used_functions := name :: !used_functions;
      definition_sources := name :: !definition_sources;
      (* pure re-translates exp itself; it rejects every construct whose
         computation translation would change state. A failed attempt
         must not leave its report records or shared definitions behind. *)
      let pure_value = if not (List.mem name !faulting_functions) &&
          Effects.function_is_pure id !effect_info then
          let restore = translation_checkpoint () in
          try Some (pure ctx exp) with Reporting.Fatal_error _ -> restore (); None
        else None in
      (match pure_value with
       | Some value -> continuation (cleanup ctx) value
       | None ->
      let shared = if !state_computation then
          !share_source_function ctx exp id body pat args else None in
      (match shared with
       | Some {expression; returns_state = true} ->
           let value = fresh () and state = fresh () in
           let restore = translation_checkpoint () in
           let previous = !computing_shared_facts in
           (* The shared body already contains every source effect/check.
              Revisit it only to recover facts about a non-unit result.
              Unit has exactly one value; traversing an instruction's loops
              again cannot reveal any additional return-value information. *)
           let facts = if exp_type ctx.widths exp = Unit then unit
             else if generic_widths_active () then Atom value else
             Fun.protect ~finally:(fun () ->
             computing_shared_facts := previous; restore ()) (fun () ->
             computing_shared_facts := true;
             let p, locals = pattern callee.widths [] pat in
             let values = match args with
               | [arg] -> transfer_value ctx arg
               | _ -> Tuple_term (List.map (transfer_value ctx) args) in
             let locals = literal_bindings pat values locals in
             (* Keep facts about the returned value, not the whole execution
                tree: an earlier undefined local can be fully initialized
                before return. History is still emitted by the shared call.
                Different exits contribute their common literal or the
                interval covering all exits, never a selected branch. *)
             let exits = ref [] in
             let finish _ value =
               exits := value :: !exits; Atom "one" in
             ignore (computation {callee with locals} body finish finish);
             match !exits with
             | [] -> Atom value
             | [result] -> alias_value (Atom value) result
             | first :: rest ->
                 (match literal_key first with
                  | Some key when List.for_all (fun result ->
                      literal_key result = Some key) rest ->
                      canonical_literal first
                  | _ ->
                      let bounds = List.map value_bounds !exits in
                      if List.for_all Option.is_some bounds then
                        let bounds = List.map Option.get bounds in
                        let low, high = List.fold_left (fun (low, high) (l, h) ->
                          (if Nat_big_num.less l low then l else low),
                          (if Nat_big_num.greater h high then h else high))
                          (List.hd bounds) (List.tl bounds) in
                        Bounded_value (Atom value, low, high)
                      else Atom value)) in
           Let (Tuple_term [Atom value; Atom state], expression,
             continuation { (cleanup ctx) with state = Some (Atom state)}
               (Typed (Shared_value (Atom value, facts), exp_type ctx.widths exp)))
       | _ ->
      let p, locals = pattern callee.widths [] pat in
      let values = match args with
        | [arg] -> transfer_value ctx arg | _ -> Tuple_term (List.map (transfer_value ctx) args) in
      let locals = literal_bindings pat values locals in
      let finish final result =
        continuation { (cleanup ctx) with state = final.state} result in
      Let (p, values, computation {callee with locals} body finish finish))))
  | E_app (id, args) when List.mem (string_of_id id)
        ["Mem_read"; "Mem_read__1"; "Mem_set"; "Mem_set__1"] &&
        !state_type = "armstate" && !state_computation ->
      (* Descriptor metadata is not consulted by the flat leaf, but the
         argument can read/write state, fault or return. Evaluate it together
         with every other operand in the original order before the access. *)
      computation_arguments ctx args return_cont false (fun next args cleanup ->
        let E_aux (_, annotation) = exp in
        let expression = E_aux (E_app (id, args), annotation) in
        flat_memory next expression (fun final value -> continuation (cleanup final) value))
  | E_app (id, ([width; index; value] as args))
      when string_of_id id = "write_gpr" && x86_shina_registers () ->
      if is_defined_function "write_gpr" then
        fail loc "write_gpr requires its explicit register boundary";
      used_primitives := "write_gpr" :: !used_primitives;
      computation_arguments ctx args return_cont false (fun next args cleanup ->
        match args with
        | [width; index; value] ->
            let component = x86_gpr next exp width index (Some value) (pure next index) in
            let state = fresh () in
            let written = Let (Atom state, App ("write", [component; pure next value; Option.get next.state]),
              continuation {(cleanup next) with state = Some (Atom state)} unit) in
            (match written with
             | Let (_, (App (_, [_; stored; _]) as update), _) ->
                 let sail, placeholders = call_placeholders next (string_of_id id) args
                   (List.map (fun argument ->
                      if argument == value then stored else pure next argument) args) in
                 record_update next ["write_gpr"] sail placeholders update
             | _ -> assert false);
            written
        | _ -> assert false)
  | E_app (id, ([index; value] as args))
      when string_of_id id = "write_gpr" && x86_binds X86.Gpr_access ->
      if is_defined_function "write_gpr" then
        fail loc "write_gpr requires its explicit register boundary";
      used_primitives := "write_gpr" :: !used_primitives;
      computation_arguments ctx args return_cont false (fun next args cleanup ->
        match args with
        | [index; value] ->
            let component = x86_rems_gpr next exp index (Some value) (pure next index) in
            let state = fresh () in
            let written = Let (Atom state, App ("write", [component; pure next value; Option.get next.state]),
              continuation {(cleanup next) with state = Some (Atom state)} unit) in
            (match written with
             | Let (_, (App (_, [_; stored; _]) as update), _) ->
                 let sail, placeholders = call_placeholders next (string_of_id id) args
                   (List.map (fun argument ->
                      if argument == value then stored else pure next argument) args) in
                 record_update next ["write_gpr"; "x86-REMS-GPR-access"] sail placeholders update
             | _ -> assert false);
            written
        | _ -> assert false)
  | E_app (id, ([width; index; value] as args))
      when string_of_id id = "write_simd" && x86_binds X86.Simd_access ->
      if is_defined_function "write_simd" then
        fail loc "write_simd requires its explicit SIMD boundary";
      used_primitives := "write_simd" :: !used_primitives;
      computation_arguments ctx args return_cont false (fun next args cleanup ->
        match args with
        | [width; index; value] ->
            let component = x86_simd next exp width index (Some value) (pure next index) in
            let state = fresh () in
            let written = Let (Atom state, App ("write", [component; pure next value; Option.get next.state]),
              continuation {(cleanup next) with state = Some (Atom state)} unit) in
            (match written with
             | Let (_, (App (_, [_; stored; _]) as update), _) ->
                 let sail, placeholders = call_placeholders next (string_of_id id) args
                   (List.map (fun argument ->
                      if argument == value then stored else pure next argument) args) in
                 record_update next ["write_simd"] sail placeholders update
             | _ -> assert false);
            written
        | _ -> assert false)
  | E_app (id, args) when List.mem (string_of_id id) ["vmem_read"; "vmem_write"] &&
        !state_type = "riscvstate" ->
      (* A genuine constructor literal has no effects to evaluate. Check
         its identity and payload before excluding it, then evaluate every
         remaining argument in source order and retain its state effects. *)
      let access_index = if string_of_id id = "vmem_read" then 3 else 4 in
      let access = try List.nth args access_index with Failure _ ->
        fail loc "wrong primitive arity for flat memory access" in
      require_flat_access_literal ctx
        (if string_of_id id = "vmem_read" then "Load" else "Store") access;
      let evaluated = List.filteri (fun index _ -> index <> access_index) args in
      computation_arguments ctx evaluated return_cont false (fun next evaluated cleanup ->
        let before, after =
          let rec split count values = if count = 0 then [], values else
            match values with
            | value :: rest -> let before, after = split (count - 1) rest in
                value :: before, after
            | [] -> fail loc "wrong primitive arity for flat memory access" in
          split access_index evaluated in
        let E_aux (_, annotation) = exp in
        let expression = E_aux (E_app (id, before @ [access] @ after), annotation) in
        flat_memory next expression (fun final value -> continuation (cleanup final) value))
  | E_app (id, [target]) when string_of_id id = "set_next_pc" && !state_type = "riscvstate" ->
      if is_defined_function "set_next_pc" then
        fail loc "set_next_pc must be external or a supported defined helper";
      if exp_type ctx.widths target <> Word 32 || exp_type ctx.widths exp <> Unit then
        fail loc "set_next_pc requires bits(32) -> unit";
      used_primitives := "set_next_pc" :: !used_primitives;
      let next = fresh () in
      let written = Let (Atom next, App ("write", [Atom "PC"; pure ctx target; Option.get ctx.state]),
           continuation {ctx with state = Some (Atom next)} unit) in
      (match written with
       | Let (_, (App (_, [_; stored; _]) as update), _) ->
           record_update ctx ["set_next_pc"] "set_next_pc(a)" [stored, "a"] update
       | _ -> assert false);
      written
  | E_app (id, [value]) when string_of_id id = "SP_set" &&
        !state_type = "armstate" && !state_computation ->
      (* Defined helpers reached the inlining case above. This branch is
         only the explicit external active-SP projection. *)
      if is_defined_function "SP_set" then
        fail loc "SP_set must be external or a supported defined helper";
      if exp_type ctx.widths value <> Word 64 || exp_type ctx.widths exp <> Unit then
        fail loc "SP_set requires bits(64) -> unit";
      used_primitives := "SP_set" :: !used_primitives;
      let next = fresh () in
      let written = Let (Atom next, App ("write", [Atom "SP"; pure ctx value; Option.get ctx.state]),
           continuation {ctx with state = Some (Atom next)} unit) in
      (match written with
       | Let (_, (App (_, [_; stored; _]) as update), _) ->
           record_update ctx ["SP_set"] "SP_set(a)" [stored, "a"] update
       | _ -> assert false);
      written
  | E_app (id, [argument]) when
        List.mem (string_of_id id)
          ["CheckFPEnabled64"; "CheckFPAdvSIMDEnabled64"; "AArch64_CheckFPAdvSIMDEnabled"] &&
        !state_type = "armstate" && !state_computation ->
      let name = string_of_id id in
      if is_defined_function name then
        fail loc (name ^ " must be external or a supported defined helper");
      if exp_type ctx.widths argument <> Unit || exp_type ctx.widths exp <> Unit then
        fail loc (name ^ " requires unit -> unit");
      (* This is the explicit successful-enabled contract, not removal of
         the source call or a claim about exception/permission checks. *)
      used_primitives := name :: !used_primitives;
      let check = if name = "CheckFPEnabled64"
        then "Arm-FP-enabled-access" else "Arm-AdvSIMD-enabled-access" in
      successful_checks := check :: !successful_checks;
      record_interpretation [name; check] (name ^ "()") "s' = s";
      computation ctx argument return_cont (fun next value ->
        let checked = fresh () in
        Let (Atom checked, value, continuation next unit))
  | E_app (id, args) when
        List.mem (string_of_id id) ["BranchTo"; "BranchNotTaken"] &&
        !state_type = "armstate" && !state_computation ->
      let name = string_of_id id in
      if is_defined_function name then
        fail loc (name ^ " must be external or a supported defined helper");
      (match name, args with
       | "BranchTo", [target; branch_type; conditional] ->
           if exp_type ctx.widths target <> Word 64 ||
              exp_type ctx.widths conditional <> Bool || exp_type ctx.widths exp <> Unit then
             fail loc "BranchTo requires (bits(64), BranchType, bool) -> unit";
           arm_branch_type loc ctx branch_type
       | "BranchNotTaken", [branch_type; conditional] ->
           if exp_type ctx.widths conditional <> Bool || exp_type ctx.widths exp <> Unit then
             fail loc "BranchNotTaken requires (BranchType, bool) -> unit";
           arm_branch_type loc ctx branch_type
       | _ -> fail loc ("wrong primitive arity for " ^ name));
      let source_pc = arm_instruction_pc loc ctx (Type_check.env_of exp) in
      used_primitives := name :: !used_primitives;
      successful_checks := "Arm-flat-branch-PC-event" :: !successful_checks;
      computation_arguments ctx args return_cont false (fun next args cleanup ->
        let state = Option.get next.state in
        let target = if name = "BranchTo" then pure next (List.hd args)
          else App ("read", [Atom "PC"; state]) in
        let finish state =
          let event = App ("EventJump", [Tuple_term [source_pc; target]]) in
          let final = fresh () in
          Let (Atom final, App ("write", [Atom "events"; App ("CONS", [
            event; App ("read", [Atom "events"; state])]); state]),
            continuation {(cleanup next) with state = Some (Atom final)} unit) in
        let branched = if name = "BranchTo" then
          let branched = fresh () in
          Let (Atom branched, App ("write", [Atom "PC"; target; state]),
            finish (Atom branched))
        else finish state in
        (* The report shows the branch with the target a. The source PC is
           always read from the state at the start of the instruction, s0,
           even where the current state is still that state. *)
        let entry_pc = source_pc, "(read " ^ symbol "reg_" "_PC" ^ " s0)" in
        (match name, branched with
         | "BranchTo", Let (pc, written, Let (_, update, _)) ->
             record_update next [name; "Arm-flat-branch-PC-event"] "BranchTo(a, b, c)"
               [entry_pc; target, "a"] (Let (pc, written, update))
         | "BranchNotTaken", Let (_, update, _) ->
             record_update next [name; "Arm-flat-branch-PC-event"] "BranchNotTaken(a, b)"
               [entry_pc] update
         | _ -> assert false);
        branched)
  | E_app (id, ([_; width; value] as args)) when
       List.mem (string_of_id id) ["X_set"; "V_set"] &&
       !state_type = "armstate" && !state_computation ->
      let n = constant_index ctx width in
      if exp_type ctx.widths value <> Word n || exp_type ctx.widths exp <> Unit then
        fail loc (string_of_id id ^
          " requires a matching bitvector value and unit result");
      (* A singleton width type gives its number, not permission to skip
         evaluation. Capture index, width and value in Sail's source order:
         later operands can change registers read by earlier ones, perform
         other writes, assert or return before the setter is reached. *)
      computation_arguments ctx args return_cont false (fun next args cleanup ->
        match args with
        | [index; width; value] ->
            arm_set next id index width (pure next value) (fun final ->
              continuation (cleanup final) unit)
        | _ -> assert false)
  | E_assign (LE_aux ((LE_id id | LE_typ (_, id)), _), _) when string_of_id id = "PC" ->
      fail loc "source current PC is read-only; use the next-PC interface"
  | E_assign (LE_aux ((LE_id id | LE_typ (_, id)), _), _) when
        string_of_id id = "_PC" && !state_type = "armstate" && !state_computation ->
      fail loc "source instruction PC is read-only; use the branch interface"
  | E_assign (LE_aux ((LE_id id | LE_typ (_, id)), _), _) when
        string_of_id id = "PSTATE" && !state_type = "armstate" && !state_computation &&
        Type_check.Env.is_register id (Type_check.env_of exp) ->
      fail loc "whole PSTATE writes are unsupported; use the explicit flag projections"
  | E_assign (lexp, value) when !state_computation ->
      (* Sail evaluates assignment indices before the value being assigned.
         Evaluate even statically typed indices: an index helper can write
         registers. Rebuild the assignment target with those captured indices,
         then carry their changes into the assigned value and final write. *)
      let rec selectors (LE_aux (aux, _)) = match aux with
        | LE_vector (base, index) -> selectors base @ [index]
        | LE_vector_range (base, high, low) -> selectors base @ [high; low]
        | LE_field (base, _) -> selectors base
        | LE_tuple bases | LE_vector_concat bases -> List.concat_map selectors bases
        | _ -> [] in
      let rec replace (LE_aux (aux, annotation)) values =
        let rebuild aux values = LE_aux (aux, annotation), values in
        match aux with
        | LE_vector (base, _) ->
            let base, values = replace base values in
            (match values with index :: rest -> rebuild (LE_vector (base, index)) rest
             | _ -> assert false)
        | LE_vector_range (base, _, _) ->
            let base, values = replace base values in
            (match values with high :: low :: rest ->
               rebuild (LE_vector_range (base, high, low)) rest
             | _ -> assert false)
        | LE_field (base, field) ->
            let base, values = replace base values in rebuild (LE_field (base, field)) values
        | LE_tuple bases | LE_vector_concat bases ->
            let bases, values = List.fold_left (fun (bases, values) base ->
              let base, values = replace base values in bases @ [base], values
            ) ([], values) bases in
            rebuild (match aux with LE_tuple _ -> LE_tuple bases
                     | _ -> LE_vector_concat bases) values
        | _ -> rebuild aux values in
      computation_arguments ctx (selectors lexp) return_cont false (fun next selectors cleanup ->
      let lexp, unused = replace lexp selectors in
      assert (unused = []);
      transfer_computation next value return_cont (fun next value ->
        let captured = fresh () in
        let binding = alias_value (Atom captured) value in
        Let (Atom captured, value, assign next lexp binding (fun final ->
          continuation (cleanup final) unit))))
  | E_assign _ ->
      simple_write ctx exp (fun next -> continuation next unit)
  | E_app (id, args) when string_of_id id = "wX_bits" ->
      computation_arguments ctx args return_cont false (fun next args cleanup ->
        let E_aux (_, annotation) = exp in
        let expression = E_aux (E_app (id, args), annotation) in
        simple_write next expression (fun final -> continuation (cleanup final) unit))
  | E_app (id, [base; index]) when x86_bank_read ctx exp id base ->
      (* The vector operand is evaluated before the index. Capture its state
         now, but retain any effects of index evaluation in the continuation. *)
      let bank_state = Option.get ctx.state in
      computation ctx index return_cont (fun next value ->
        let read = App ("read", [x86_bank_component next index value; bank_state]) in
        record_value next ["x86-raw-GPR-bank"]
          (string_of_exp (Type_check.strip_exp base) ^ "[a]") [value, "a"; bank_state, "s"] read;
        continuation next (Typed (read, Word 64)))
  | E_app (id, ([_; _] as args)) when extended_evaluation () &&
      not (generic_widths_active ()) &&
      List.mem (string_of_id id) ["sail_shiftleft"; "sail_shiftright";
        "sail_arith_shiftright"; "shiftl"; "shiftr"; "arith_shiftr"] ->
      (* Sail types an integer shift as total, but its runtimes disagree
         on a negative amount: the OCaml library's shiftr returns its
         input and its shiftl an empty vector, C shifts by the magnitude
         and SMT gives zero. Where the amount is not proved nonnegative, a
         negative amount yields an unknown word of the result width. *)
      computation_arguments ctx args return_cont false (fun next args cleanup ->
        let typ = exp_type next.widths exp in
        match args with
        | [x; shift] when
            (match exp_type next.widths x, exp_type next.widths shift, typ with
             | Word input, Int, Word output -> input = output
             | _ -> false) &&
            not (integer_shift_nonnegative next shift (pure next shift)) ->
            used_primitives := "Sail-negative-shift-unknown" :: !used_primitives;
            let amount = pure next shift
            and unknown = Typed (Atom (fresh ()), typ) in
            let shifted = App (integer_shift_operation (string_of_id id),
              [pure next x; App ("num_of_int", [amount])]) in
            let value = Typed (Cond (
              Typed (Infix ("<=", Typed (integer Nat_big_num.zero, Int), amount), Bool),
              shifted, unknown), typ) in
            (match shifted with
             | App (_, [shifted_value; _]) ->
                 record_interpretation ["Sail-negative-shift-unknown"]
                   (string_of_id id ^ "(a, b)")
                   (interpretation_text [shifted_value, "a"; amount, "b"; unknown, "v"] value ^
                    ", where the whole relation is ?v:" ^ type_text typ ^ ". ...")
             | _ -> assert false);
            Choose (unknown, continuation (cleanup next) value)
        | _ ->
            continuation (cleanup next) (Typed (call next exp id args, typ)))
  | E_app (id, args) ->
      let transfer = List.mem (string_of_id id)
        ["bitvector_subrange"; "subrange_bits"; "bitvector_access";
         "bitvector_length"; "slice"; "set_slice_bits"] in
      computation_arguments ctx args return_cont transfer (fun next args cleanup ->
        let value = call next exp id args in
        continuation (cleanup next) (Typed (value, exp_type next.widths exp)))
  | E_vector_append (left, right) ->
      computation_arguments ctx [left; right] return_cont false (fun next args cleanup ->
        match args with
        | [left; right] ->
            continuation (cleanup next) (Typed (concat next loc left right
              (pure next left) (pure next right), exp_type next.widths exp))
        | _ -> assert false)
  | E_tuple values ->
      computation_arguments ctx values return_cont false (fun next values cleanup ->
        continuation (cleanup next) (Tuple_term (List.map (pure next) values)))
  | E_struct (_, fields) ->
      let order, fields = record_construction_fields ctx exp fields in
      (* Capture every field in source order, including unused fields whose
         helpers can write, assert or return. Only rearrange the captured
         values for the declaration-order product; never rearrange evaluation. *)
      computation_arguments ctx (List.map snd fields) return_cont false
        (fun next values cleanup ->
          let captured = List.map2 (fun (name, _) value ->
            name, pure next value) fields values in
          let packed = Tuple_term (List.map (fun (name, _) -> List.assoc name captured) order) in
          continuation (cleanup next) (Typed (packed, exp_type next.widths exp)))
  | E_struct_update (base, fields) ->
      let order, fields = record_update_fields ctx exp base fields in
      computation_arguments ctx (base :: List.map snd fields) return_cont false
        (fun next values cleanup ->
          match values with
          | base :: values ->
              let base = pure next base in
              let updates = List.map2 (fun (name, _) value ->
                name, pure next value) fields values in
              let packed = Tuple_term (List.map (fun (name, _) ->
                match List.assoc_opt name updates with
                | Some value -> value
                | None -> record_field loc order (mk_id name) base) order) in
              continuation (cleanup next) (Typed (packed, exp_type next.widths exp))
          | _ -> assert false)
  | E_field (E_aux (E_id register, _), field)
      when Option.is_some (assumed_initial_bit ctx (Type_check.env_of exp) register field) ->
      continuation ctx (Option.get
        (assumed_bit_value ctx (Type_check.env_of exp) register field))
  | E_field (E_aux (E_id register, _), field)
      when !upstream_architecture = Some "aarch64" &&
           string_of_id register = "PSTATE" &&
           not (List.mem_assoc "PSTATE" ctx.locals) ->
      continuation ctx (Typed (arm_pstate_field loc ctx (Type_check.env_of exp) field,
                               exp_type ctx.widths exp))
  | E_field (value, field) ->
      (match exp_type ctx.widths value with
       | Record fields ->
           (* Evaluate the base once before projecting. Its state changes and
              enclosing return handler survive even if only one field is used. *)
           computation ctx value return_cont (fun next value ->
             continuation next (Typed (record_field loc fields field value,
                                       exp_type next.widths exp)))
       | _ -> fail loc "field access requires a supported record type")
  | _ -> continuation ctx (pure ctx exp)

(* Bind the state and mutable locals at a normal control-flow join. Each
   branch/iteration retains its own source effects and control markers; only
   the following continuation is emitted once. lower_faults propagates a
   fault, stop or rejection through the intermediate value without running
   that continuation.

   Discover normal exits before choosing the payload shape. A local is
   available only when present at every exit; partial-word masks intersect,
   definite-assignment failures unite, identical literals remain known, and
   numeric bounds widen to include every exit. No branch is selected here.
   emit therefore runs twice, and the first run's output is discarded; its
   report records repeat those of the second, and loop budgets count both. *)
and computation_join loc outer emit continuation =
  let unit = Typed (Atom "one", Unit) in
  let exits = ref [] in
  ignore (emit (fun final -> exits := final :: !exits; unit));
  if !exits = [] then fail loc "a control-flow join requires a normal exit"
  else begin
    let names = List.filter (fun local ->
      List.for_all (fun final -> List.mem_assoc local final.locals) !exits
    ) (List.sort_uniq String.compare outer.mutable_locals) in
    let has_state = Option.is_some outer.state in
    let fields = List.map (fun local -> local, fresh ()) names in
    let state_name = fresh () in
    let pack = function
      | [] -> unit | [value] -> value | values -> Tuple_term values in
    let payload final =
      pack ((if has_state then [Option.get final.state] else []) @
        List.map (fun local ->
          let value = List.assoc local final.locals in
          match partial_word value with
          | Some (backing, _, _) -> backing
          | None -> value) names) in
    let bound = pack ((if has_state then [Atom state_name] else []) @
      List.map (fun (_, variable) -> Atom variable) fields) in
    let locals = List.map (fun (local, variable) ->
      let values = List.map (fun final -> List.assoc local final.locals) !exits in
      let binding = match List.find_map partial_word values with
        | Some (_, width, _) ->
            let known = List.fold_left (fun known value ->
              let bits = match partial_word value with
                | Some (_, n, bits) when n = width -> bits
                | Some _ -> fail loc "control-flow partial-word width mismatch"
                | None -> List.init width Fun.id in
              List.filter (fun bit -> List.mem bit bits) known
            ) (List.init width Fun.id) values in
            tracked_word (Atom variable) width known
        | None ->
            (* The join tracks masks of whole words only. A partial word
               inside a tuple would lose its mask here and print its
               word 0 backing, so refuse it. *)
            if List.exists contains_partial values then
              fail loc "control-flow join of a value with partially initialized fields";
            (match List.map literal_key values with
             | Some key :: rest when List.for_all ((=) (Some key)) rest ->
                 canonical_literal (List.hd values)
             | _ ->
                 let bounds = List.map value_bounds values in
                 if List.for_all Option.is_some bounds then
                   let bounds = List.map Option.get bounds in
                   let low, high = List.fold_left (fun (low, high) (l, h) ->
                     (if Nat_big_num.less l low then l else low),
                     (if Nat_big_num.greater h high then h else high)
                   ) (List.hd bounds) (List.tl bounds) in
                   Bounded_value (Atom variable, low, high)
                 else Atom variable) in
      local, binding) fields in
    let uninitialized = List.sort_uniq String.compare (List.concat_map
      (fun final -> final.uninitialized) !exits) in
    let joined = {outer with
      state = if has_state then Some (Atom state_name) else None;
      locals = locals @ List.filter (fun (local, _) ->
        not (List.mem local outer.mutable_locals)) outer.locals;
      uninitialized} in
    Let (bound, emit payload, continuation joined)
  end

(* Evaluate a transferred value while retaining effects and initialization
   metadata. A tuple can carry partially assigned fields; recursively evaluate
   any helper-producing fields before binding them. This differs from
   observable evaluation, which must reject unknown source bits. *)
and transfer_computation ctx (E_aux (aux, _) as exp) return_cont continuation =
  match aux with
  | E_typ (_, value) -> transfer_computation ctx value return_cont continuation
  | E_id _ -> continuation ctx (transfer_value ctx exp)
  | E_tuple values ->
      computation_arguments ctx values return_cont true (fun next values cleanup ->
        continuation (cleanup next) (Tuple_term (List.map (transfer_value next) values)))
  | _ -> computation ctx exp return_cont continuation

(* Evaluate arguments once, in source order, before entering the callee.
   Synthetic bindings retain the checked types, established bounds and
   initialization masks. Removing those bindings must retain their effects.
   An evaluated string literal or immutable HOL local needs no second
   binding: it cannot change while later arguments execute. In particular,
   do not print every literal in a statically decided string lookup.
   Inspect the emitted backing term, not its known-value facts; a register
   read or a helper calculation still needs to be captured. *)
and computation_arguments ctx args return_cont transfer continuation =
  let rec inert_string = function
    | String_literal _ | Atom _ -> true
    | Typed (value, _) | Shared_value (value, _) -> inert_string value
    | _ -> false in
  let rec bind ctx bound = function
    | [] ->
        let names = List.map (fun (name, _) -> name) bound in
        let args = List.rev_map snd bound in
        (* The aliases retain the compiler's exact argument annotation and
           numeric constraints. Cleanup does not discard argument effects. *)
        let cleanup final = {final with locals = List.filter
          (fun (name, _) -> not (List.mem name names)) final.locals} in
        continuation ctx args cleanup
    | (E_aux (_, annot) as expression) :: rest ->
        let evaluate = if transfer then transfer_computation else computation in
        evaluate ctx expression return_cont (fun next value ->
          let variable = fresh () in
          let name = "!hol-light-argument:" ^ variable in
          let synthetic = match expression with
            | E_aux (E_id id, _) when
                Type_check.is_enum_member id (Type_check.env_of expression) &&
                not (List.mem_assoc (string_of_id id) next.locals) -> expression
            | _ -> E_aux (E_id (mk_id name), annot) in
          let reuse = exp_type next.widths expression = String_type &&
            inert_string value in
          let local = if reuse then value else alias_value (Atom variable) value in
          let extended = {next with locals = (name, local) :: next.locals} in
          let body = bind extended ((name, synthetic) :: bound) rest in
          if reuse then body else Let (Atom variable, value, body)) in
  bind ctx [] args

(* A failed generic attempt must leave no definitions, enum declarations,
   register requirements or dependency evidence behind. Restore heterogeneous
   refs through closures; unexpected compiler errors still escape normally. *)
let rec bit_width_variables env typ =
  match Type_check.destruct_bitvector env typ with
  | Some width -> tyvars_of_nexp width
  | None ->
      match Type_check.Env.base_typ_of env typ with
      | Typ_aux (Typ_tuple types, _) ->
          List.fold_left (fun variables typ ->
            KidSet.union variables (bit_width_variables env typ)) KidSet.empty types
      | Typ_aux (Typ_exist (_, _, typ), _) -> bit_width_variables env typ
      | Typ_aux (Typ_app (_, arguments), _) ->
          List.fold_left (fun variables -> function
            | A_aux (A_typ typ, _) ->
                KidSet.union variables (bit_width_variables env typ)
            | _ -> variables) KidSet.empty arguments
      | _ -> KidSet.empty

(* Widths in intermediate types count too. Static loop bounds are required
   by the current loop translator and therefore join the necessary numeric
   instantiations. Register indices, flags and enum selectors are not added
   merely because a particular caller supplied a constant. *)
let required_width_variables pat body =
  let variables = ref (KidSet.union
    (bit_width_variables (Type_check.env_of_pat pat) (Type_check.typ_of_pat pat))
    (bit_width_variables (Type_check.env_of body) (Type_check.typ_of body))) in
  ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with
    e_aux = (fun (aux, annotation) ->
      let exp = E_aux (aux, annotation) in
      if not (Type_check.is_empty_tannot (snd annotation)) then
        variables := KidSet.union !variables
          (bit_width_variables (Type_check.env_of exp) (Type_check.typ_of exp));
      E_aux (aux, annotation));
    e_for = (fun (id, first, last, step, order, body) ->
      List.iter (fun expression ->
        Option.iter (fun number ->
          variables := KidSet.union !variables (tyvars_of_nexp number))
          (snd (numeric_argument expression))) [first; last; step];
      E_for (id, first, last, step, order, body))
  } body);
  let env = Type_check.env_of_pat pat in
  KidSet.filter (fun kid ->
    KBindings.find_opt kid (Type_check.Env.get_typ_vars env) = Some K_int) !variables

let rec pattern_leaves (P_aux (aux, _) as pat) emitted =
  match aux, emitted with
  | (P_typ (_, pat) | P_var (pat, _)), _ -> pattern_leaves pat emitted
  | P_tuple pats, Tuple_term values when List.length pats = List.length values ->
      List.concat (List.map2 pattern_leaves pats values)
  | _ -> [pat, emitted]

(* Capture the actual tuple shape without importing callee type variables
   into the caller's scope. All actual expressions have already been checked;
   HOL infers each fresh binding's type from those evaluated expressions. *)
let rec capture_pattern (P_aux (aux, _) as pat) =
  match aux with
  | P_typ (_, pat) | P_var (pat, _) -> capture_pattern pat
  | P_tuple pats -> Tuple_term (List.map capture_pattern pats)
  | P_id _ | P_wild | P_lit (L_aux (L_unit, _)) -> Atom (fresh ())
  | _ -> fail (pat_loc pat) "shared functions require supported source binding patterns"

(* Use Sail's existing -dprofile switch to distinguish frontend, preparation
   and individual-root costs. Diagnostics affect stderr, never HOL output. *)
let profiled label run =
  if not !Profile.opt_profile then run () else
  let started = Profile.start () in
  Fun.protect ~finally:(fun () -> Profile.finish ("HOL Light " ^ label) started) run

let shared_function_call ctx exp id body pat args =
  let name = string_of_id id in
  if !computing_shared_facts || List.mem name ctx.stack || !normal_retirement ||
     List.mem name !faulting_functions ||
     List.exists (function
       | E_aux (E_id id, _) ->
           Option.fold ~none:false ~some:contains_partial
             (List.assoc_opt (string_of_id id) ctx.locals)
       | _ -> false) args then None else
  let pure_function = Effects.function_is_pure id !effect_info in
  if not pure_function && not !state_computation then None else
  let caller_generic = generic_widths_active () in
  let needed = required_width_variables pat body in
  (* The compiler already checked symbolic call types. Numeric inference
     still finds constants such as lo=0 without requiring a callee-local
     dimension name to match the caller's HOL dimension name. Concrete calls
     retain the existing result-type check and all caller precondition checks. *)
  let specialized = specialize_helper ~check_result:(not caller_generic)
    ctx exp name body pat args in
  let fixed = List.filter (fun (name, _) ->
    KidSet.mem (mk_kid name) needed) specialized.widths
    |> List.sort_uniq compare in
  let key generic request =
    String.concat "|" [
      request.Entry.source; (if generic then "generic" else "fixed");
      !state_type; string_of_bool pure_function;
      String.concat ";" (List.map assumption_text !configured_assumptions);
      string_of_typ (Type_check.typ_of_pat pat);
      string_of_typ (Type_check.typ_of body);
      String.concat "," (List.map (fun (name, n) ->
        name ^ "=" ^ string_of_int n) request.Entry.type_arguments)] in
  let build generic request =
    let saved_dimensions = !poly_dimensions and saved_fresh = !fresh_index
    and saved_expressions = !poly_width_expressions
    and saved_fixed = !poly_fixed_arguments in
    let saved_registers = !used_registers and saved_contracts = !contract_registers
    and saved_sources = !definition_sources
    and saved_assumptions = !used_assumptions in
    Fun.protect ~finally:(fun () ->
      poly_dimensions := saved_dimensions; poly_width_expressions := saved_expressions;
      poly_fixed_arguments := saved_fixed;
      fresh_index := saved_fresh;
      used_registers := saved_registers; contract_registers := saved_contracts;
      definition_sources := saved_sources;
      used_assumptions := saved_assumptions @ !used_assumptions) (fun () ->
      let env = Type_check.env_of_pat pat in
      let rec interface_widths env typ =
        match Type_check.destruct_bitvector env typ with
        | Some width -> [width]
        | None -> match Type_check.Env.base_typ_of env typ with
          | Typ_aux (Typ_tuple types, _) -> List.concat_map (interface_widths env) types
          | Typ_aux (Typ_exist (_, _, typ), _) -> interface_widths env typ
          | _ -> [] in
      let interface = interface_widths env (Type_check.typ_of_pat pat) @
        interface_widths (Type_check.env_of body) (Type_check.typ_of body) in
      let fixed kid = List.mem_assoc (kid_name kid) request.Entry.type_arguments in
      let simple = List.filter_map (function
        | Nexp_aux (Nexp_var kid, _) when not (fixed kid) -> Some kid
        | _ -> None) interface
        |> List.sort_uniq Kid.compare in
      poly_dimensions := if generic then List.mapi (fun index kid ->
        kid_name kid, kid_stamp env kid, "N" ^ string_of_int index) simple
        else [];
      poly_width_expressions := if generic then
        List.filter (fun expression ->
          let variables = KidSet.filter (fun kid -> not (fixed kid))
            (tyvars_of_nexp expression) in
          not (KidSet.is_empty variables) &&
          not (KidSet.for_all (fun kid -> List.exists (fun simple ->
            Kid.compare kid simple = 0) simple) variables)) interface
        |> List.sort_uniq (fun left right ->
          String.compare (string_of_nexp left) (string_of_nexp right))
        |> List.mapi (fun index expression ->
          expression, (KidSet.elements (tyvars_of_nexp expression) |>
            List.map (fun kid -> kid_name kid, kid_stamp env kid)),
          "N" ^ string_of_int (List.length simple + index))
        else [];
      poly_fixed_arguments := List.map (fun (name, value) ->
        name, kid_stamp env (mk_kid name), value)
        request.Entry.type_arguments;
      fresh_index := 0; used_registers := []; contract_registers := [];
      used_assumptions := [];
      definition_sources := [name];
      let parameters, locals = pattern request.Entry.type_arguments [] pat in
      let leaves = pattern_leaves pat parameters in
      let locals, arguments, parameters = List.fold_left
        (fun (locals, arguments, parameters) (index, (formal, parameter)) ->
          let numeric = Type_check.destruct_atom_nexp (Type_check.env_of_pat formal)
            (Type_check.typ_of_pat formal) in
          let fixed_numeric = Option.bind numeric (fun number ->
            match number with
            | Nexp_aux (Nexp_var kid, _) when
                List.mem_assoc (kid_name kid) request.Entry.type_arguments ||
                Option.is_some (poly_variable (Type_check.env_of_pat formal) kid) ->
                Some (numeric_type_term request.Entry.type_arguments
                  (Type_check.env_of_pat formal) number)
            | _ -> None) in
          match fixed_numeric, formal with
          | Some value, _ ->
              let names = pattern_names formal in
              List.fold_left (fun locals name ->
                (name, value) :: List.remove_assoc name locals) locals names,
              arguments, parameters
          | None, P_aux (P_lit (L_aux (L_unit, _)), _) -> locals, arguments, parameters
          | _ -> locals, arguments @ [index], parameters @ [print_term parameter])
        (locals, [], []) (List.mapi (fun index leaf -> index, leaf) leaves) in
      let returns_state = not pure_function in
      let worker = {ctx with widths = request.Entry.type_arguments; numeric_facts = [];
        locals; stack = name :: ctx.stack; mutable_locals = []; uninitialized = [];
        state = if returns_state then Some (Atom "s") else None;
        entry_state = if returns_state then Some (Atom "entry") else None} in
      let result = if returns_state then
          let finish ctx value = Tuple_term [
            observable_value (exp_loc body) value; Option.get ctx.state] in
          computation worker body finish finish
        else
          let restore = translation_checkpoint () in
          (try observable_value (exp_loc body) (tail worker body) with
           | Reporting.Fatal_error (Reporting.Err_general _) ->
               restore ();
               (* Local assignments/loops do not make a source function
                  stateful. The richer traversal can emit their returned
                  value without adding architectural state parameters. *)
               let finish _ value = observable_value (exp_loc body) value in
               computation worker body finish finish) in
      let registers = List.sort_uniq String.compare !used_registers |>
        List.map (fun name ->
          let typ = match List.assoc_opt name !contract_registers with
            | Some typ -> typ
            | None -> hol_type request.Entry.type_arguments (Type_check.env_of body)
                (Type_check.Env.get_register (mk_id name) (Type_check.env_of body)) in
          name, typ) in
      let register_parameters = List.map (fun (name, typ) ->
        "(" ^ symbol "reg_" name ^ ":(" ^ !state_type ^ "," ^
          type_text typ ^ ")component)") registers in
      let constant = symbol ("sail_hl_shared_" ^ !shared_namespace ^ "_")
        (name ^ "_" ^ string_of_int (List.length !shared_functions)) in
      let states = if returns_state then
          ["(entry:" ^ !state_type ^ ")"; "(s:" ^ !state_type ^ ")"] else [] in
      let sources = !definition_sources in
      let assumptions = List.sort_uniq compare !used_assumptions in
      let text = assumption_comments assumptions ^
        definition_source_comments !source_definitions sources ^
        Printf.sprintf "(* Width policy: %s. Source preconditions apply at every call. *)\n"
          (if generic && generic_widths_active () then "polymorphic" else "specialized") ^
        "let " ^ constant ^ " = new_definition\n `" ^ constant ^ " " ^
        String.concat " " (register_parameters @ parameters @ states) ^
        " =\n    " ^ print_term (simplify_bindings result) ^ "`;;\n" in
      {request; constant; arguments; registers; returns_state; sources; text; assumptions}) in
  let attempt generic request =
    let key = key generic request in
    match List.assoc_opt key !shared_functions with
    | Some worker -> Some worker
    | None when List.mem_assoc key !shared_failures -> None
    | None ->
        let restore = translation_checkpoint () in
        (try
          let worker = build generic request in
          shared_functions := !shared_functions @ [key, worker];
          shared_decisions := (key ^ " => " ^ worker.constant) :: !shared_decisions;
          Some worker
        with Reporting.Fatal_error (Reporting.Err_general (_, message)) ->
          restore ();
          shared_failures := (key, message) :: !shared_failures;
          None) in
  let request arguments = Entry.request ~type_arguments:arguments name in
  let generic arguments =
    KidSet.is_empty needed || not (KidSet.for_all (fun kid ->
      List.mem_assoc (kid_name kid) arguments) needed) in
  let specialize () =
    (* Try individual necessary numeric choices first: integer_subrange
       needs lo=0 here, not the caller's fixed hi. If more than one choice
       is needed, remove each removable argument from a successful full
       instance. Probes restore all output/effect bookkeeping, so unused
       definitions cannot escape. At most linear-many probes are required;
       this finds an irreducible set, not a globally smallest set. *)
    match List.find_map (fun argument ->
      attempt (generic [argument]) (request [argument])) fixed with
    | Some worker -> Some worker
    | None ->
        let supports arguments =
          let request = request arguments in
          if List.mem_assoc (key (generic arguments) request) !shared_failures
          then false else
          let restore = translation_checkpoint () in
          Fun.protect ~finally:restore (fun () ->
            try ignore (build (generic arguments) request); true with
            | Reporting.Fatal_error (Reporting.Err_general _) -> false) in
        if fixed = [] || not (supports fixed) then None else
        let minimal = List.fold_left (fun remaining argument ->
          let reduced = List.filter ((<>) argument) remaining in
          if supports reduced then reduced else remaining) fixed fixed in
        attempt (generic minimal) (request minimal) in
  let worker =
    let rec dynamic = function
      | Dynamic_bits | Empty_bits -> true
      | Tuple types -> List.exists dynamic types
      | Record fields -> List.exists (fun (_, typ) -> dynamic typ) fields
      | Result (ok, error) -> dynamic ok || dynamic error
      | Binary_variant ((_, a), (_, b)) -> dynamic a || dynamic b
      | Option_type payload -> dynamic payload
      | _ -> false in
    let generic = if List.exists (fun argument ->
        dynamic (exp_type ctx.widths argument)) (exp :: args) then None
      else attempt true (Entry.request name) in
    match generic with
    | Some worker -> Some worker
    | None -> specialize () in
  Option.map (fun worker ->
    used_assumptions := worker.assumptions @ !used_assumptions;
    used_registers := List.map fst worker.registers @ !used_registers;
    contract_registers := worker.registers @ !contract_registers;
    definition_sources := worker.sources @ !definition_sources;
    let captured = capture_pattern pat in
    let fields = List.map snd (pattern_leaves pat captured) in
    let values = match args with
      | [arg] -> pure ctx arg
      | _ -> Tuple_term (List.map (pure ctx) args) in
    let states = if worker.returns_state then
        [Option.get ctx.entry_state; Option.get ctx.state] else [] in
    let parameters = List.map (fun (name, _) -> Atom (symbol "reg_" name))
        worker.registers @ List.map (List.nth fields) worker.arguments @ states in
    {expression = Let (captured, values, App (worker.constant, parameters));
     returns_state = worker.returns_state}) worker

let () = share_source_function := shared_function_call

(* A root takes no numeric type arguments, so its declaration's quantifier
   constraints must be closed and provable. *)
let check_root_constraints env id =
  let quant, _ = Type_check.Env.get_val_spec_orig id env in
  List.iter (fun nc ->
    if not (KidSet.is_empty (tyvars_of_constraint nc)) then
      fail (id_loc id) "uninstantiated numeric type variable in root constraint";
    if not (Type_check.prove __POS__ env nc) then
      fail (id_loc id) ("root does not satisfy " ^ string_of_n_constraint nc)
  ) (snd (quant_split quant))

(* Connect the entry catalogue to the loaded model: split RV execute clauses,
   close entry aliases, typecheck new calls, then select upstream dependencies.
   The cut list is a trust boundary, not a compiler optimization: retain each
   cut's genuine declaration but remove its body for the HOL interpretation.
   Effect information remains conservative for the loaded/extended program.

   "Dependency closure" means every function/type/value needed by a root.
   Entry.closure first includes entry-to-entry aliases from the handwritten
   catalogue. Sail's Callgraph.filter_ast_ids then follows upstream program
   dependencies, stopping at the explicitly listed cuts. It is not a list of
   helper calculations we reimplemented. The instruction/helper calculations
   remain in the external checked AST; cuts supply only the chosen boundary. *)
let prepare_upstream (state : Interactive.State.istate) =
  (* Bit access, slices and literals are translated most significant bit
     first, which is Sail's meaning only under decreasing order. *)
  (match Type_check.Env.get_default_order_opt state.env with
   | Some (Ord_aux (Ord_dec, _)) -> ()
   | _ -> fail Parse_ast.Unknown "HOL Light export requires default Order dec");
  match !upstream_architecture with
  | None ->
      if !requested_assumptions <> [] then
        fail Parse_ast.Unknown "source assumptions require an Arm or x86 architecture";
      configured_assumptions := [];
      state, []
  | Some architecture ->
      let state =
        if architecture = "rv32" &&
           List.exists (fun definition -> root_of_def definition = Some "execute") state.ast.defs
        then begin
          let rewrites = Rewrites.instantiate_rewrites
            ["split", [Rewrites.String_arg "execute"]; "recheck_defs", []] in
          let ctx, ast, effect_info, env =
            Rewrites.rewrite state.ctx state.effect_info state.env rewrites state.ast in
          {state with ctx; ast; effect_info; env}
        end else state in
      let catalog, cuts, families = match architecture with
        | "aarch64" -> Arm.entries, Arm.cuts, Arm.family_roots
        | "x86" ->
            let source = x86_source () in
            source.X86.validate state;
            source.X86.entries, X86.cuts source, source.X86.family_roots
        | "rv32" ->
            let families = List.sort_uniq String.compare
              (List.map (fun entry -> entry.Entry.family) Rv32.entries) in
            let families = List.map (fun family ->
              family, List.filter_map (fun entry ->
                if entry.Entry.family = family then Some entry.Entry.name else None)
                Rv32.entries) families in
            Rv32.entries, Rv32.cuts, families
        | _ -> fail Parse_ast.Unknown ("unsupported architecture " ^ architecture) in
      List.iter (fun family ->
        if not (List.mem_assoc family families) then
          fail Parse_ast.Unknown ("unknown upstream instruction family " ^ family))
        !upstream_families;
      let family_roots =
        if !upstream_families = [] then List.map (fun entry -> entry.Entry.name) catalog
        else List.concat_map (fun family -> List.assoc family families) !upstream_families in
      let selected = List.filter (fun entry ->
        List.mem entry.Entry.name family_roots &&
        (!roots = [] || List.mem entry.Entry.name !roots)) catalog in
      if !roots = [] then roots := List.sort_uniq String.compare family_roots;
      let entries = Entry.closure catalog selected in
      let state = if entries = [] then state else begin
        input_boundaries := [];
        Entry.instantiate ~record:record_input_boundary state entries
      end in
      if architecture = "rv32" && !requested_assumptions <> [] then
        fail Parse_ast.Unknown "source assumptions require an Arm or x86 architecture";
      let defaults = if entries = [] then [] else match architecture with
        | "aarch64" -> Arm.assumptions
        | "x86" -> (x86_source ()).X86.assumptions entries
        | _ -> [] in
      configured_assumptions := validate_assumptions state.env
        (defaults @ !requested_assumptions);
      let root_ids = List.fold_left (fun ids name -> IdSet.add (mk_id name) ids)
        IdSet.empty !roots in
      let cut_ids = List.fold_left (fun ids name -> IdSet.add (mk_id name) ids)
        IdSet.empty cuts in
      (* Upstream supplies every declaration. The callgraph computes the
         dependency closure and leaves original signatures at the explicit
         architecture boundaries; no replacement Sail interface is loaded. *)
      let ast = Callgraph.filter_ast_ids root_ids cut_ids state.ast in
      {state with ast}, entries

(* Fully translated output kept in memory before publication. model_text is
   HOL definition source, translation_log_text records the translation
   choices, configuration and interpretations go to the run's context file,
   and the remaining fields populate the output inventory.
   None of these records is a compiler-preservation proof or a kernel result. *)
type exported_artifact = {
  prefix : string;
  model_text : string;
  translation_log_text : string;
  (* For the run's context file: the configuration and the
     interpretations, each a Sail call or construct with its HOL term. *)
  configuration : string list;
  interpretations : (string * string) list;
  exported_roots : (string * string) list;
  enum_names : string list;
  primitive_contracts : string list;
  assumptions : Entry.assumption list;
  input_boundaries : string list;
}

(* Report layout. Text is broken at spaces so that lines end before
   column width + 1, by default 73: the first line starts with
   first_indent, the others with indent. Where a line must break, it breaks at the space with the fewest
   open parentheses, the last such space, so that a HOL term is split
   between its top-level arguments rather than inside one. *)
let report_wrap ?(width = 72) buffer first_indent indent text =
  let words = Array.of_list (List.filter (fun word -> word <> "")
    (String.split_on_char ' '
       (String.map (function '\n' | '\t' -> ' ' | c -> c) text))) in
  let n = Array.length words in
  let depth = Array.make (n + 1) 0 in
  Array.iteri (fun index word ->
    depth.(index + 1) <- String.fold_left (fun depth c ->
      if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth)
      depth.(index) word) words;
  let rec line start prefix =
    if start < n then begin
      let rec fit count column =
        if start + count >= n then count else
        let next = column + (if count = 0 then 0 else 1) +
          String.length words.(start + count) in
        if count = 0 || next <= width then fit (count + 1) next else count in
      let count = fit 0 (String.length prefix) in
      let stop =
        if start + count >= n then n else begin
          let best = ref (start + count) in
          for k = start + count downto start + 1 do
            if depth.(k) < depth.(!best) then best := k
          done;
          !best
        end in
      Buffer.add_string buffer prefix;
      Buffer.add_string buffer
        (String.concat " " (Array.to_list (Array.sub words start (stop - start))));
      Buffer.add_char buffer '\n';
      line stop indent
    end in
  line 0 first_indent

(* A titled section of a report: an optional explanation, then entries.
   An entry is a list of lines: the first starts at column 3, the others at
   column 5, and continuations two columns further in. *)
let report_section buffer ?intro title entries =
  if entries <> [] then begin
    Printf.bprintf buffer "\n%s\n" title;
    Option.iter (fun intro ->
      report_wrap buffer "  " "  " intro; Buffer.add_char buffer '\n') intro;
    List.iter (function
      | [] -> ()
      | first :: rest ->
          report_wrap buffer "  " "      " first;
          List.iter (report_wrap buffer "    " "      ") rest) entries
  end

(* The name of a run's context file, <run>.context: one per architecture
   and x86 source, or the output's own name for a run without one. *)
let run_name prefix = match !upstream_architecture with
  | Some "aarch64" -> "arm"
  | Some "x86" -> "x86-" ^ (x86_source ()).X86.model
  | Some architecture -> architecture
  | None -> Filename.basename prefix

(* The context file of a run: the configuration and every interpretation
   that its models use, each once. *)
let context_text run artifacts =
  let buffer = Buffer.create 4096 in
  let union lists = List.fold_left (fun known line ->
    if List.mem line known then known else known @ [line]) [] (List.concat lists) in
  Printf.bprintf buffer
    "Context of the %s run\n\
     The configuration under which the translator ran, and every\n\
     interpretation that a model of the run uses. The Interpretations\n\
     section of backend/README.md explains each interpretation; a comment\n\
     at the top of a model lists what is specific to it.\n" run;
  report_section buffer "Configuration"
    (List.map (fun line -> [line])
       (union (List.map (fun artifact -> artifact.configuration) artifacts)));
  report_section buffer "Interpretations"
    ~intro:"Each Sail call or construct is replaced by the HOL term below \
            it. a, b, ... stand for its arguments, s for the state before \
            it, s' for the state after it and s0 for the state at the start \
            of the instruction."
    (List.map (fun (sail, text) -> [sail; "~> " ^ text])
       (List.sort_uniq compare
          (List.concat_map (fun artifact -> artifact.interpretations) artifacts)));
  Buffer.contents buffer

(* Translate every requested root to a buffered artifact. Root arguments
   must retain their full exported domain; reject unsupported refinements
   rather than erase their preconditions. Preserve the binding's completion
   conditions and record every used contract/helper/check.
   No canonical output file is opened in this function.

   Every instruction emits parameters -> initial_state -> final_state -> bool.
   A retirement relation additionally checks successful completion and
   requires Retire_Success plus the final jump-event state. This deliberately
   excludes exceptional completion; the instruction proof must state its
   operand/alignment/configuration domain separately.

   HOL int/bool types alone cannot retain arbitrary Sail refinements.
   Reject integer/refined-Boolean root parameters rather than silently export
   a total function with a stronger domain than its source declaration.
   Internal helper refinements still participate in the checked translation.
   Source registers without a fixed canonical interpretation become explicit
   HOL component parameters, not invented architectural state fields. *)
(* What the models rest on beyond the translation of Sail's code is
   checked in at two places. The run's context file (<run>.context) holds
   the configuration fixed for the run and each interpretation with the
   HOL term that replaced the Sail call or construct. A comment at the top
   of a model holds what is specific to it: inputs supplied as parameters,
   and the source code that a z3 decision removed. backend/README.md
   explains each interpretation. The full record of the translation, for debugging and
   the backend tests, is <model>.translation-log, which is not checked in. *)

(* A recorded name must be shown with its replacement term if it is a cut
   of the architecture table or a translator rule (a name with a hyphen),
   except the exact rules named here. Other names are Sail
   library functions and constructors that the translator gives their exact
   meaning (README.md, primitive mapping); they are not assumptions of one
   model, and the report leaves them out, as it does the exact rules named
   here. *)
let exact_primitives = [
  "checked-dynamic-single-replication";
  "unsigned"; "signed"; "sub_atom"; "add_atom"; "mult_atom"; "negate_atom";
  "abs_int_atom"; "and_bool"; "or_bool"; "not_bool"; "eq_bool"; "eq_int";
  "gteq_int"; "lteq_int"; "gt_int"; "lt_int"; "min_int"; "eq_bits"; "eq_any";
  "eq_anything"; "eq_string"; "subrange_bits"; "bitvector_length";
  "bitvector_access"; "bitvector_update"; "bitvector_concat"; "get_slice_int";
  "set_slice_bits"; "slice"; "update_subrange_bits"; "replicate_bits";
  "truncate"; "sail_zeros"; "sail_zero_extend"; "sail_sign_extend"; "add_bits";
  "add_bits_int"; "sub_bits"; "sub_vec"; "sub_vec_int"; "not_vec"; "or_vec";
  "xor_vec"; "and_vec"; "sail_shiftleft"; "sail_shiftright";
  "sail_arith_shiftright"; "shiftl"; "shiftr"; "shift_bits_left";
  "shift_bits_right"; "_shl_int"; "_shr_int"; "_shl8"; "pow2"; "emod_nat";
  "ediv_nat"; "ediv_int"; "tdiv_int"; "quot_round_zero"; "rem_round_zero";
  "quot_positive_round_zero"; "rem_positive_round_zero"; "UInt0"; "SInt0";
  "ZeroExtend0"; "SignExtend0"; "checked-dynamic-zero-extension";
  "checked-dynamic-bit-zeros"; "checked-dynamic-bit-complement";
  "None"; "Some"; "Retire_Success"; "Regidx"; "RM_reg"; "XRM_reg";
  "E_Fetch_Addr_Align"; "E_Breakpoint"; "E_U_EnvCall"; "E_S_EnvCall";
  "E_VS_EnvCall"; "E_M_EnvCall"; "Ext_ControlAddr_Check_Failure";
]

let export_checked out_file (state : Interactive.State.istate) entries =
  (match !upstream_architecture with
   | Some "aarch64" -> state_type := "armstate"
   | Some "rv32" -> state_type := "riscvstate"
   | Some "x86" -> state_type := "x86state"
   | _ -> ());
  let prefix = match out_file with Some name -> name | None -> "hol_light" in
  shared_namespace := symbol "" (Filename.basename prefix);
  let qualified = !upstream_architecture = Some "x86" &&
    (x86_source ()).X86.qualified_names in
  type_namespace := if qualified then !shared_namespace ^ "_" else "";
  let result_case = if qualified
    then symbol ("sail_hl_case_" ^ !shared_namespace ^ "_") "result"
    else "sail_hl_result_case" in
  shared_functions := []; shared_failures := []; shared_decisions := [];
  used_assumptions := []; artifact_assumptions := [];
  Proof_table.reset proved_goals;
  source_definitions := state.ast.defs;
  poly_dimensions := [];
  poly_width_expressions := []; poly_fixed_arguments := [];
  let functions = List.filter_map (fun def ->
    match root_of_def def with
    | Some name -> Some (name, def)
    | None -> None
  ) state.ast.defs in
  if !roots = [] then fail Parse_ast.Unknown "specify at least one --hol-light-root";
  let selected = List.map (fun name ->
    match List.assoc_opt name functions with
    | Some def -> name, def
    | None -> fail Parse_ast.Unknown ("root not found: " ^ name)
  ) !roots in
  let function_bodies = List.filter_map (fun (name, def) ->
    (* Unsupported, unrelated platform functions are not translated. *)
    try let pat, body = function_clause Parse_ast.Unknown def in Some (name, body, pat)
    with Reporting.Fatal_error _ -> None
  ) functions in
  let calls = List.map (fun (name, body, _) ->
    let called = ref [] in
    ignore (Rewriter.fold_exp {Rewriter.id_exp_alg with e_app = (fun (id, args) ->
      called := string_of_id id :: !called; E_app (id, args))} body);
    name, !called) function_bodies in
  let rec fault_closure known =
    let next = List.sort_uniq String.compare (known @ List.filter_map (fun (name, calls) ->
      if List.exists (fun called -> List.mem called known) calls then Some name else None
    ) calls) in
    if next = known then next else fault_closure next in
  let nonlocal_bodies = List.filter_map (fun (name, body, _) ->
    let rec undefined = function
      | E_aux (E_typ (_, body), _) -> undefined body
      | E_aux (E_undef, _) -> true
      | _ -> false in
    let alg = Rewriter.compute_exp_alg false (||) in
    let nonlocal, _ = Rewriter.fold_exp {alg with
      e_undef = true, E_undef;
      e_throw = (fun (_, body) -> true, E_throw body);
      (* Definite-assignment backing is not an observed arbitrary value.
         Leave these common helpers shareable; their existing mask checks
         still reject every source read of an unassigned part. *)
      e_var = (fun ((left, target), (initial, value), (rest, body)) ->
        let integer_choice = undefined value &&
          (match Type_check.Env.base_typ_of (Type_check.env_of value)
              (Type_check.typ_of value) with
           | Typ_aux (Typ_id id, _) -> string_of_id id = "int"
           | _ -> false) in
        left || rest || integer_choice || (initial && not (undefined value)),
        E_var (target, value, body))
    } body in
    if nonlocal then Some name else None) function_bodies in
  value_recursive_functions := if not (extended_evaluation ()) then [] else
    List.filter_map (fun (name, called) ->
    if not (List.mem name called) then None else
    let env = state.env in
    match Type_check.Env.get_val_spec_orig (mk_id name) env with
    | _, Typ_aux (Typ_fn (arguments, result), _) when
        List.for_all (fun typ -> KidSet.is_empty (bit_width_variables env typ))
          (result :: arguments) -> Some name
    | _ -> None) calls;
  faulting_functions := if !upstream_architecture = Some "aarch64"
    then fault_closure (List.sort_uniq String.compare
      (Arm.faults @ ["EndOfInstruction"] @ nonlocal_bodies))
    else fault_closure (List.sort_uniq String.compare nonlocal_bodies);
  effect_info := state.effect_info;
  defined_functions := List.map fst functions;
  used_primitives := []; used_functions := []; used_globals := []; used_enums := [];
  used_case_names := [];
  used_results := false; proved_assertions := []; guarded_assertions := [];
  selected_branches := []; applied_interpretations := [];
  disabled_extensions := []; used_mappings := []; unobserved_undefined := [];
  mapping_definitions := List.filter_map (function
    | DEF_aux (DEF_mapdef (MD_aux (MD_mapping (id, _, clauses), _)), _) ->
        Some (string_of_id id, clauses)
    | _ -> None
  ) state.ast.defs;
  proved_numeric_arguments := Evidence_set.empty;
  successful_checks := []; unrolled_loops := [];
  let globals = List.filter_map (function
    | DEF_aux (DEF_let (pat, body), _) ->
        Option.map (fun name -> name, body) (global_name pat)
    | _ -> None
  ) state.ast.defs in
  let exported_roots = ref [] in
  let definitions = List.map (fun (name, def) ->
    active_root := name;
    let id = mk_id name in
    let entry = List.find_opt (fun entry -> entry.Entry.name = name) entries in
    (* An RV32 instruction is a relation even if its body has no effects,
       as PAUSE's RETIRE_SUCCESS: then it changes no state. *)
    let stateful = not (Effects.function_is_pure id state.effect_info) ||
      (!upstream_architecture = Some "rv32" && entry <> None) in
    (* A root is a retirement relation if its entry, or for a root without
       one --hol-light-normal-retirement, says so; otherwise a state
       computation if it is stateful, and a pure function if not. *)
    normal_retirement := (match entry with
      | Some entry -> entry.Entry.retirement
      | None -> !requested_retirement);
    state_computation := stateful && not !normal_retirement;
    case_name := if !normal_retirement then symbol "sail_hl_case_" "control"
                 else result_case;
    fresh_index := 0; used_registers := []; contract_registers := [];
    used_assumptions := [];
    definition_sources := [name];
    loop_budget := 0; value_recursion_budget := 0;
    let pat, body = function_clause Parse_ast.Unknown def in
    check_root_constraints state.env id;
    let rec check_arguments = function
      | Int -> fail (pat_loc pat) "integer root arguments and their refinements are unsupported"
      | Dynamic_bits -> fail (pat_loc pat) "dynamic bitvectors are internal values, not root arguments"
      | Tuple ts -> List.iter check_arguments ts
      | Record fields -> List.iter (fun (_, ty) -> check_arguments ty) fields
      | Result (ok, err) -> check_arguments ok; check_arguments err
      | Binary_variant ((_, a), (_, b)) -> check_arguments a; check_arguments b
      | Option_type payload -> check_arguments payload
      | _ -> () in
    check_arguments (hol_type [] (Type_check.env_of_pat pat) (Type_check.typ_of_pat pat));
    let rec check_boolean_refinements typ =
      let env = Type_check.env_of_pat pat in
      match Type_check.Env.base_typ_of env typ with
      | Typ_aux (Typ_tuple ts, _) -> List.iter check_boolean_refinements ts
      | Typ_aux (Typ_id id, _) when Type_check.Env.is_record id env ->
          List.iter (fun (ty, _) -> check_boolean_refinements ty)
            (snd (Type_check.Env.get_record id env))
      | Typ_aux (Typ_app (id, args), _) when List.mem (string_of_id id) ["result"; "option"] ->
          List.iter (function A_aux (A_typ ty, _) -> check_boolean_refinements ty
                            | _ -> ()) args
      | typ when Option.is_some (Type_check.destruct_atom_bool env typ) ->
          fail (pat_loc pat) "refined Boolean root arguments are unsupported"
      | _ -> () in
    check_boolean_refinements (Type_check.typ_of_pat pat);
    let p, locals = pattern [] [] pat in
    exported_roots := (name, if !normal_retirement then "normal-retirement"
                             else if stateful then "state-computation" else "pure")
                      :: !exported_roots;
    let ctx = {widths = []; numeric_facts = []; locals; functions = function_bodies; globals;
      stack = [name]; state = if stateful then Some (Atom "s") else None;
      entry_state = if stateful then Some (Atom "s") else None;
      mutable_locals = []; uninitialized = []} in
    let calculate () =
      if !normal_retirement then begin
        if !state_type <> "riscvstate" || not stateful then
          fail (exp_loc body) "normal-retirement roots must be stateful RV32 computations";
        (match exp_type [] body with
         | Unit_variant ("ExecutionResult", members) when
             List.exists (fun id -> string_of_id id = "Retire_Success") members -> ()
         | _ -> fail (exp_loc body) "normal-retirement roots must return the ExecutionResult variant");
        let finish ctx result =
          let state = Option.get ctx.state in
          let jump entry = App ("write", [Atom "events"; App ("CONS", [
            App ("EventJump", [Tuple_term [
              App ("riscv_instruction_pc", [entry]); App ("read", [Atom "PC"; state])]]);
            App ("read", [Atom "events"; state])]); state]) in
          let next = jump (Atom "s") in
          record_interpretation ["successful-root-jump-event"] "return Retire_Success()"
            ("the final state is " ^
             interpretation_text [state, "s"] (jump (Atom "s0")));
          Infix ("/\\", Infix ("=", result, Atom (ctor_symbol "Retire_Success")),
                       Infix ("=", next, Atom "t")) in
        lower_faults (computation ctx body finish finish)
      end else if stateful then begin
        if exp_type [] body <> Unit then
          fail (exp_loc body) "state-computation roots must return unit";
        let finish ctx _ = Infix ("=", Option.get ctx.state, Atom "t") in
        lower_faults (computation ctx body finish finish)
      end else tail ctx body in
    (* An opaque shared result can lose a relation between source numeric
       witnesses that the inline translator retains. Retry the same checked
       body without sharing, not with a weaker assertion or operand domain.
       A genuinely unsupported source path still fails in that traversal.
       Restore all speculative definitions and evidence before the retry. *)
    let restore = translation_checkpoint () in
    let result = profiled name (fun () -> try calculate () with
      | Reporting.Fatal_error (Reporting.Err_general (_, reason)) as problem ->
          if !computing_shared_facts || !normal_retirement then raise problem;
          restore ();
          let previous = !computing_shared_facts in
          let result = Fun.protect
            ~finally:(fun () -> computing_shared_facts := previous)
            (fun () -> computing_shared_facts := true; calculate ()) in
          shared_decisions := ("root " ^ name ^ " => checked inline: " ^ reason) ::
            !shared_decisions;
          result) in
    let regs = List.sort_uniq String.compare !used_registers in
    let params = List.map (fun name ->
      let typ = match List.assoc_opt name !contract_registers with
        | Some typ -> typ
        | None ->
            let typ = Type_check.Env.get_register (mk_id name) state.env in
            hol_type [] state.env typ in
      let rec dynamic = function
        | Dynamic_bits -> true
        | Tuple ts -> List.exists dynamic ts
        | Record fields -> List.exists (fun (_, typ) -> dynamic typ) fields
        | Result (a,b) -> dynamic a || dynamic b
        | Binary_variant ((_, a), (_, b)) -> dynamic a || dynamic b
        | Option_type typ -> dynamic typ
        | _ -> false in
      if dynamic typ then fail (pat_loc pat)
        "dynamic bitvectors cannot be architectural register components";
      "(" ^ symbol "reg_" name ^ ":(" ^ !state_type ^ "," ^
      type_text typ ^ ")component)"
    ) regs in
    let arguments = match p with
      | Tuple_term ps -> List.map print_term ps
      | Typed (Atom "unit_arg", Unit) -> []
      | p -> [print_term p] in
    let constant = symbol "sail_hl_" name in
    artifact_assumptions := !used_assumptions @ !artifact_assumptions;
    let sources = profiled ("source comments " ^ name) (fun () ->
      definition_source_comments state.ast.defs !definition_sources) in
    let printed = profiled ("printing " ^ name) (fun () ->
      print_term (simplify_bindings result)) in
    let selection =
      match List.find_opt (fun entry -> entry.Entry.name = name) entries with
      | Some entry -> entry_comment entry arguments
      | None -> "" in
    assumption_comments !used_assumptions ^
    sources ^ selection ^
    "let " ^ constant ^ " = new_definition\n `" ^ constant ^ " " ^
    String.concat " " (params @ arguments) ^ " =\n    " ^
    (* Even an unconditional fault must have a machine-state final argument:
       its T body alone would leave t polymorphic in HOL. *)
    (if stateful then "\\(s:" ^ !state_type ^ ") (t:" ^ !state_type ^ "). " else "") ^
    printed ^ "`;;\n"
  ) selected in
  (* Buffer all output: a batch validates every family before publishing
     any canonical model, including debug ASTs and dependency records. *)
  let model = Buffer.create 4096 in
  if !Profile.opt_profile then
    Printf.eprintf
      "HOL Light: rendering %s (%d definitions, %d shared, %d primitives, %d numeric facts)\n%!"
      (Filename.basename prefix) (List.length definitions)
      (List.length !shared_functions) (List.length !used_primitives)
      (Evidence_set.cardinal !proved_numeric_arguments);
  Buffer.add_string model "(* Generated by the Sail typed-AST HOL Light target. *)\n";
  if List.mem "Arm-fault-any-final-state" !used_primitives then
    Buffer.add_string model
      "(* A reached architectural fault ends the instruction and permits every\n\
       \   final state. This over-approximation loses exception information and\n\
       \   state-preservation guarantees; normal termination is not a fault. *)\n";
  if List.mem "Arm-FPSR-write-exclusion" !used_primitives then
    Buffer.add_string model
      "(* Arm FPSR writes are excluded from the observed state. Selectors,\n\
       \   values, reads and other effects are retained. Original Sail excerpts\n\
       \   below still show those writes; this is not physical FPSR preservation. *)\n";
  if List.mem "Arm-BType-write-exclusion" !used_primitives then
    Buffer.add_string model
      "(* Arm BTypeNext/BTypeCompatible writes are excluded from the observed\n\
       \   state. Values, reads, checks and other effects are retained. Original\n\
       \   Sail excerpts still show those writes; branch-protection behavior and\n\
       \   later checks using these metadata updates are outside this claim. *)\n";
  List.iter (fun case -> Printf.bprintf model
    "let %s = new_recursive_definition sum_RECURSION\n\
     `(!x. %s f g (INL x:A+B) = f x) /\\\n\
     (!y. %s f g (INR y:A+B) = g y)`;;\n\n" case case case)
    (List.sort_uniq String.compare !used_case_names);
  List.iter (fun (name, members) ->
    let ty = type_symbol name in
    Printf.bprintf model
      "let %s_INDUCT,%s_RECURSION = define_type\n \"%s = %s\";;\n"
      ty ty ty
      (String.concat " | " (List.map (fun id -> ctor_symbol (string_of_id id)) members));
    (* A singleton datatype has no pair of distinct constructors. *)
    if List.length members > 1 then begin
      Printf.bprintf model "let %s_DISTINCT = distinctness \"%s\";;\n" ty ty;
      (* Shared instructions retain operation selectors. After a binding
         selects SUB, its proof must reduce comparisons with ADD and the
         other constructors. These are kernel-proved datatype facts, not
         translation assumptions or new axioms. *)
      Printf.bprintf model "extend_basic_rewrites [%s_DISTINCT];;\n" ty
    end;
    Buffer.add_char model '\n'
  ) (List.sort_uniq (fun (x, _) (y, _) -> String.compare x y) !used_enums);
  let shared = List.map snd !shared_functions in
  List.iter (fun worker ->
    Buffer.add_string model worker.text;
    Buffer.add_char model '\n') shared;
  List.iter (fun text ->
    Buffer.add_string model text; Buffer.add_char model '\n') definitions;
  (* Keep the established instruction rewrite theorems usable by the
     existing proofs, while their actual HOL definitions call shared source
     functions. These are kernel-derived unfoldings, not extra axioms or
     a claim that Sail compilation preserves semantics. *)
  if shared <> [] then begin
    Buffer.add_string model
      "(* Rebind each root's OCaml name to a theorem that the kernel derives\n\
       \   from its definition, with the shared definitions above unfolded and\n\
       \   numerals reduced. Proofs that use the name get this theorem; the\n\
       \   constant is unchanged. *)\n";
    List.iter (fun (name, _) ->
      let constant = symbol "sail_hl_" name in
      Printf.bprintf model
        "let %s = CONV_RULE\n\
         (DEPTH_CONV (DIMINDEX_CONV ORELSEC\n\
          GEN_REWRITE_CONV I [NUM_OF_INT_OF_NUM] ORELSEC\n\
          CHANGED_CONV NUM_RED_CONV ORELSEC INT_RED_CONV))\n\
         (REWRITE_RULE [%s] %s);;\n" constant
        (String.concat "; " (List.rev_map (fun worker -> worker.constant) shared))
        constant) selected
  end;
  (* The translation log records every choice made while translating:
     inlined source bodies versus interpreted primitives, source-prover
     facts versus runtime guards, successful/disabled platform views and
     loop/initialization handling. It is for debugging and the backend
     tests; the checked-in report below is the part that a model rests on. *)
  let dependencies = Buffer.create 1024 in
  if !Profile.opt_profile then
    Printf.eprintf "HOL Light: reporting dependencies for %s\n%!"
      (Filename.basename prefix);
  List.iter (fun fact -> Printf.bprintf dependencies "configured-assumption %s\n"
    (assumption_text fact)) !configured_assumptions;
  List.iter (fun fact -> Printf.bprintf dependencies "used-assumption %s\n"
    (assumption_text fact)) (List.sort_uniq compare !artifact_assumptions);
  let reached_inputs = List.filter_map (fun boundary ->
    if List.mem (Entry.lifted_name boundary.Entry.lift) (!used_functions @ !roots)
    then Some (input_boundary_text boundary) else None) !input_boundaries
    |> List.sort_uniq String.compare in
  List.iter (fun boundary ->
    Printf.bprintf dependencies "source-input-boundary %s\n" boundary) reached_inputs;
  List.iter (fun decision -> Printf.bprintf dependencies "shared-function %s\n" decision)
    (List.rev !shared_decisions);
  List.iter (fun (key, reason) ->
    Printf.bprintf dependencies "specialization-required %s: %s\n" key reason)
    (List.sort_uniq compare !shared_failures);
  List.iter (fun n -> Printf.bprintf dependencies "root %s\n" n) !roots;
  List.iter (fun n -> Printf.bprintf dependencies "inlined %s\n" n)
    (List.sort_uniq String.compare !used_functions);
  List.iter (fun n -> Printf.bprintf dependencies "inlined-global %s\n" n)
    (List.sort_uniq String.compare !used_globals);
  List.iter (fun n -> Printf.bprintf dependencies "inlined-mapping %s\n" n)
    (List.sort_uniq String.compare !used_mappings);
  List.iter (fun n -> Printf.bprintf dependencies "primitive-contract %s\n" n)
    (List.sort_uniq String.compare !used_primitives);
  List.iter (fun assertion -> Printf.bprintf dependencies "statically-proved-assertion %s\n" assertion)
    (List.sort_uniq String.compare
       (List.map (fun (assertion, _, _, _, _) -> assertion) !proved_assertions));
  List.iter (fun assertion -> Printf.bprintf dependencies "guarded-assertion %s\n" assertion)
    (List.sort_uniq String.compare !guarded_assertions);
  Evidence_set.iter (fun fact ->
    Printf.bprintf dependencies "proved-numeric-argument-fact %s\n" fact)
    !proved_numeric_arguments;
  List.iter (fun extension -> Printf.bprintf dependencies "disabled-extension %s\n" extension)
    (List.sort_uniq String.compare !disabled_extensions);
  List.iter (fun check -> Printf.bprintf dependencies "successful-check %s\n" check)
    (List.sort_uniq String.compare !successful_checks);
  List.iter (fun loop -> Printf.bprintf dependencies "unrolled-static-loop %s\n" loop)
    (List.sort_uniq String.compare !unrolled_loops);
  List.iter (fun branch ->
    Printf.bprintf dependencies "statically-selected-branch %s\n" branch)
    (List.sort_uniq String.compare (List.map (fun (location, truth, _, _, _) ->
       location ^ if truth then " then" else " else") !selected_branches));
  List.iter (fun name -> Printf.bprintf dependencies "unobserved-undefined-local %s\n" name)
    (List.sort_uniq String.compare !unobserved_undefined);
  let exported_roots = List.rev !exported_roots in
  List.iter (fun (name, mode) ->
    if mode <> "pure" then Printf.bprintf dependencies "%s-root %s\n" mode name)
    exported_roots;
  if List.for_all (fun (_, mode) -> mode = "state-computation") exported_roots then
    Buffer.add_string dependencies "state-computation\n";
  if List.for_all (fun (_, mode) -> mode = "normal-retirement") exported_roots then
    Buffer.add_string dependencies "normal-retirement-only\n";
  if List.exists (fun (_, mode) -> mode = "normal-retirement") exported_roots then
    Buffer.add_string dependencies "primitive-contract successful-root-jump-event\n";
  (* Every interpretation that translation recorded must be shown with
     the term that replaced it. A retirement root that never retires has
     no jump event to show. *)
  let interpretations =
    List.sort_uniq String.compare (!used_primitives @ !successful_checks) in
  let cuts = match !state_type with
    | "armstate" -> Arm.cuts
    | "x86state" -> X86.cuts (x86_source ())
    | _ -> Rv32.cuts in
  let shown = List.concat_map (fun (names, _, _) -> names) !applied_interpretations in
  List.iter (fun name ->
    if (List.mem name cuts || String.contains name '-') &&
       not (List.mem name exact_primitives) && not (List.mem name shown) then
      fail Parse_ast.Unknown
        ("dependency report: the interpretation " ^ name ^
         " was applied, but no replacement term was recorded for it"))
    interpretations;
  (* What is specific to this model, the part that the run's context
     does not cover, as a comment at the top of the model. Sail source
     text is quoted, as in the model's other comments, so that it cannot
     end the comment. *)
  let innermost context = match List.rev (String.split_on_char ' ' context) with
    | name :: _ -> name | [] -> context in
  let root context = List.hd (String.split_on_char ' ' context) in
  (* One entry per decision, with the roots it was reached from. The
     translator copies code along each path, so a decision applies on the
     paths where it was made, not wherever the source line is reached. *)
  let grouped keyed =
    let keys = List.sort_uniq compare (List.map fst keyed) in
    List.map (fun key ->
      let roots = List.sort_uniq String.compare
        (List.filter_map (fun (k, r) -> if k = key then Some r else None) keyed) in
      key @ ["reached from " ^ String.concat " " roots]) keys in
  let short location = match String.split_on_char ':' location with
    | file :: line :: _ -> file ^ ":" ^ line | _ -> location in
  (* Only z3's decisions: a condition that the translated term already
     evaluates to a constant follows from the entry's fixed arguments and
     the configuration, like any other translated code; the translation
     log records those too. *)
  let decisions =
    grouped (List.filter_map (fun (location, truth, condition, context, by_z3) ->
      if not by_z3 then None else
      Some ([quoted_text "sail_source" condition;
             Printf.sprintf "at %s, in %s" (short location) (innermost context);
             Printf.sprintf "z3 proves the condition %s, so the model keeps only \
                             the %s branch"
               (if truth then "true" else "false") (if truth then "then" else "else")],
            root context)) !selected_branches) @
    grouped (List.filter_map (fun (_, assertion, location, context, by_z3) ->
      if not by_z3 then None else
      Some ([quoted_text "sail_source" assertion;
             Printf.sprintf "at %s, in %s" location (innermost context);
             "z3 proves it, so the model has no check here"],
            root context)) !proved_assertions) in
  let sections = List.filter (fun (_, entries) -> entries <> []) [
    "Supplied inputs", List.map (fun input -> [quoted_text "sail_input" input]) reached_inputs;
    "Removed by a z3 decision (on the paths where each was made)", decisions] in
  (* Every model names its run's context file; one with something
     specific to it lists that too. *)
  let specific = Buffer.create 1024 in
  if sections = [] then
    report_wrap specific "(* " "   "
      (Printf.sprintf "The configuration and the interpretations of this \
                       model's run are in %s.context. Nothing else is specific \
                       to this model. *)" (run_name prefix))
  else begin
    report_wrap specific "(* " "   "
      (Printf.sprintf "Assumptions specific to this model. The configuration \
                       and the interpretations of the whole run are in %s.context."
         (run_name prefix));
    List.iter (fun (title, entries) ->
      Printf.bprintf specific "\n   %s\n" title;
      List.iter (function
        | [] -> ()
        | first :: rest ->
            (* A quoted source stays on one line, as Sail wrote it. *)
            report_wrap ~width:max_int specific "     " "     " first;
            List.iter (report_wrap specific "       " "         ") rest) entries) sections;
    Buffer.add_string specific "*)\n"
  end;
  Buffer.add_char specific '\n';
  let model_text =
    let text = Buffer.contents model in
    match String.index_opt text '\n' with
    | Some line when Buffer.length specific > 0 ->
        String.sub text 0 (line + 1) ^ "\n" ^ Buffer.contents specific ^
        String.sub text (line + 1) (String.length text - line - 1)
    | _ -> text in
  {prefix; model_text;
   translation_log_text = Buffer.contents dependencies;
   configuration = List.map assumption_text !configured_assumptions @
     List.map (fun extension -> "extension " ^ extension ^ "=off")
       (List.sort_uniq String.compare !disabled_extensions);
   interpretations = List.sort_uniq compare
     (List.map (fun (_, sail, text) -> sail, text) !applied_interpretations);
   assumptions = List.sort_uniq compare !artifact_assumptions;
   input_boundaries = reached_inputs;
   exported_roots; enum_names = exported_enum_names ();
   primitive_contracts = exported_primitive_contracts exported_roots}

(* Publish only an already translated artifact. target_inner buffers all
   selected families before this point; an unsupported later family cannot
   publish earlier families from that batch. This is not an atomic update:
   an I/O error can still interrupt the writes. *)
let publish artifact =
  let write suffix text =
    let channel = open_out (artifact.prefix ^ suffix) in
    Fun.protect ~finally:(fun () -> close_out channel)
      (fun () -> output_string channel text) in
  write ".ml" artifact.model_text;
  write ".translation-log" artifact.translation_log_text

(* The context file of a run, written after its models. *)
let publish_context path run artifacts =
  let channel = open_out path in
  Fun.protect ~finally:(fun () -> close_out channel)
    (fun () -> output_string channel (context_text run artifacts))

(* Optional process parallelism for batch exports (--hol-light-jobs).
   Sail has parsed and checked the model, and prepare_upstream has computed
   the dependency closure, before any worker starts. Each family is then
   translated by export, the body of the sequential batch loop, in a forked
   copy of that prepared state. export_checked resets every per-artifact
   global, so an artifact does not depend on which families were translated
   before it in the same process.

   Workers publish nothing. Each returns its artifact, or the error it
   raised, through a temporary file in the output directory, which the
   caller removes after reading it. The caller publishes only after
   every family has succeeded, in the original order. After a failure,
   families later in that order are not started; earlier ones still run, so
   the reported error is the one that the sequential loop would reach first. *)
let export_jobs = ref 1

type worker_outcome =
  | Worker_artifact of exported_artifact
  | Worker_error of Reporting.error
  | Worker_exception of string

(* A Sail z3 memo file holds 16-byte digests, each followed by a result
   byte: 0 unknown, 1 sat, 2 unsat, 3 no unique solution, 4 a unique
   solution and four more bytes. Sail gives z3 one second, so 0 and 3 can
   come from a slow answer under load; merging them could replace a
   definite answer another worker found, so a worker's file keeps only
   1, 2 and 4 before it is merged. *)
let keep_definite_answers path =
  let data = In_channel.with_open_bin path In_channel.input_all in
  let kept = Buffer.create (String.length data) in
  let rec scan position =
    if position + 17 <= String.length data then begin
      let result = Char.code data.[position + 16] in
      let size = if result = 4 then 21 else 17 in
      if position + size <= String.length data && List.mem result [1; 2; 4] then
        Buffer.add_substring kept data position size;
      scan (position + size)
    end in
  scan 0;
  Out_channel.with_open_bin path (fun channel ->
    Out_channel.output_string channel (Buffer.contents kept))

let forked_artifacts directory jobs export groups =
  let tasks = Array.of_list groups in
  let count = Array.length tasks in
  let results = Array.make count None in
  (* Start families with more roots first. This orders work, not output. *)
  let size index = List.length (snd tasks.(index)) in
  let families = List.sort (fun i j ->
    match compare (size j) (size i) with 0 -> compare i j | order -> order)
    (List.init count Fun.id) in
  let pending = ref families in
  let first_failure = ref count in
  let running = ref [] in
  (* A child must not repeat output still buffered in the parent. *)
  let flush_output () =
    Format.pp_print_flush Format.std_formatter ();
    Format.pp_print_flush Format.err_formatter ();
    flush_all () in
  let start index =
    let file = Filename.temp_file ~temp_dir:directory "sail-hol-light-" ".worker" in
    flush_output ();
    match Unix.fork () with
    | 0 ->
        let outcome = try Worker_artifact (export tasks.(index)) with
          | Reporting.Fatal_error error -> Worker_error error
          | Type_error.Type_error (loc, error) ->
              (* Report it as target does after the sequential loop. *)
              let message, hint = Type_error.string_of_type_error error in
              (match Reporting.err_typ ?hint loc
                       ("HOL Light while exporting " ^ !active_root ^ ": " ^ message) with
               | Reporting.Fatal_error error -> Worker_error error
               | problem -> Worker_exception (Printexc.to_string problem))
          | problem -> Worker_exception (Printexc.to_string problem) in
        let status = try
            let channel = open_out_bin file in
            Marshal.to_channel channel outcome [];
            close_out channel;
            (* Hand the solver answers back for Sail's --memo-z3 file. *)
            (try Constraint.save_digests (file ^ ".smt") with Sys_error _ -> ());
            0
          with _ -> 2 in
        flush_output ();
        (* Skip at_exit handlers: the parent alone finishes Sail's run. *)
        Unix._exit status
    | pid -> running := (pid, (index, file)) :: !running in
  let rec wait () =
    try Unix.wait () with Unix.Unix_error (Unix.EINTR, _, _) -> wait () in
  let finish () =
    let pid, status = wait () in
    let merge file =
      (* Sail saves its memo only in the parent. Merging the worker's
         answers there changes no answer; it lets later workers and a
         later run with the same --memo-z3-path file skip those calls. *)
      if Sys.file_exists (file ^ ".smt") then begin
        keep_definite_answers (file ^ ".smt");
        Constraint.load_digests (file ^ ".smt");
        (try Sys.remove (file ^ ".smt") with Sys_error _ -> ())
      end;
      (try Sys.remove file with Sys_error _ -> ()) in
    match List.assoc_opt pid !running with
    | None -> ()
    | Some (index, file) ->
        running := List.remove_assoc pid !running;
        let outcome = match status with
          | Unix.WEXITED 0 ->
              (try
                 let channel = open_in_bin file in
                 Fun.protect ~finally:(fun () -> close_in channel)
                   (fun () -> (Marshal.from_channel channel : worker_outcome))
               with _ -> Worker_exception "HOL Light worker returned no result")
          | Unix.WEXITED code ->
              Worker_exception ("HOL Light worker exited with status " ^ string_of_int code)
          | Unix.WSIGNALED signal | Unix.WSTOPPED signal ->
              Worker_exception ("HOL Light worker stopped by signal " ^ string_of_int signal) in
        merge file;
        (match outcome with
         | Worker_artifact _ -> ()
         | _ -> first_failure := min !first_failure index);
        results.(index) <- Some outcome in
  let rec loop () =
    pending := List.filter (fun index -> index < !first_failure) !pending;
    match !pending with
    | index :: rest when List.length !running < jobs ->
        pending := rest;
        start index; loop ()
    | _ when !running <> [] -> finish (); loop ()
    | _ -> () in
  loop ();
  if !first_failure < count then begin
    match results.(!first_failure) with
    | Some (Worker_error error) -> raise (Reporting.Fatal_error error)
    | Some (Worker_exception message) -> failwith message
    | _ -> assert false
  end;
  Array.to_list (Array.map (function
    | Some (Worker_artifact artifact) -> artifact
    | _ -> assert false) results)

(* Sail's target callback. Select/prepare once, then translate one artifact
   or group roots into architecture-family artifacts. Batch mode buffers all
   groups before publication and writes an inventory of exactly those outputs.
   Loading generated HOL and proving conformance happens in separate scripts. *)
let target_inner out_file (state : Interactive.State.istate) =
  let state, entries = profiled "preparation" (fun () -> prepare_upstream state) in
  match !output_directory with
  | None ->
      let artifact = export_checked out_file state entries in
      publish artifact;
      let run = run_name artifact.prefix in
      publish_context (Filename.concat (Filename.dirname artifact.prefix) (run ^ ".context"))
        run [artifact]
  | Some directory ->
      let requested = !roots in
      let groups = match !upstream_architecture with
        | Some "aarch64" ->
            let families = if !upstream_families = [] then
                List.sort_uniq String.compare
                  (List.filter_map (fun name ->
                    Option.map (fun entry -> entry.Entry.family)
                      (List.find_opt (fun entry -> entry.Entry.name = name) entries)) requested)
              else !upstream_families in
            List.map (fun family -> "arm-" ^ family, List.assoc family Arm.family_roots) families
        | Some "rv32" ->
            let names retirement = List.filter_map (fun entry ->
              if entry.Entry.retirement = retirement then Some entry.Entry.name
              else None) entries in
            ["rv32", names false; "rv32-control", names true]
        | Some "x86" ->
            let source = x86_source () in
            List.map (fun (family, names) -> source.X86.stem family, names)
              source.X86.family_roots
        | _ -> fail Parse_ast.Unknown "--hol-light-output-dir requires an architecture" in
      let groups = List.filter_map (fun (stem, names) ->
        let names = List.filter (fun name -> List.mem name requested) names in
        if names = [] then None else Some (stem, List.sort_uniq String.compare names)) groups in
      List.iter (fun name ->
        if not (List.exists (fun (_, names) -> List.mem name names) groups) then
          fail Parse_ast.Unknown ("batch output has no family for root " ^ name)) requested;
      let export (stem, names) =
        Printf.eprintf "HOL Light: exporting %s (%d roots)\n%!" stem (List.length names);
        roots := names;
        let artifact = profiled stem (fun () ->
          export_checked (Some (Filename.concat directory stem)) state entries) in
        Printf.eprintf "HOL Light: checked %s\n%!" stem;
        artifact in
      if not (Sys.file_exists directory) then Unix.mkdir directory 0o755;
      let artifacts =
        if !export_jobs > 1 && List.length groups > 1
        then forked_artifacts directory !export_jobs export groups
        else List.map export groups in
      roots := requested;
      List.iter publish artifacts;
      let run = run_name directory in
      publish_context (Filename.concat directory (run ^ ".context")) run artifacts;
      let cuts = match !upstream_architecture with
        | Some "aarch64" -> Arm.cuts
        | Some "rv32" -> Rv32.cuts
        | Some "x86" -> X86.cuts (x86_source ())
        | _ -> assert false in
      let inventory = `Assoc ([
        "schema", `Int 1;
        "architecture", `String (Option.get !upstream_architecture)] @
        (if !upstream_architecture = Some "x86" then
           ["x86_source", `String (x86_source ()).X86.model] else []) @ [
        "outputs", `Assoc (List.map (fun artifact ->
          Filename.basename artifact.prefix ^ ".ml", `Assoc ([
            "roots", `List (List.map (fun (name, _) -> `String name) artifact.exported_roots);
            "modes", `Assoc (List.map (fun (name, mode) -> name, `String mode)
              artifact.exported_roots);
            "types", `List (List.map (fun name -> `String name) artifact.enum_names);
            "assumptions", `List (List.map (fun fact -> `String (assumption_text fact))
              artifact.assumptions);
            "cuts", `List (List.filter_map (fun name ->
              if List.mem name cuts then Some (`String name) else None)
              artifact.primitive_contracts);
            "contracts", `List (List.map (fun name -> `String name) artifact.primitive_contracts)
          ] @ (if artifact.input_boundaries = [] then [] else [
            "source_inputs", `List (List.map (fun boundary -> `String boundary)
              artifact.input_boundaries)
          ]))) artifacts)
      ]) in
      let inventory_stem = match !upstream_architecture with
        | Some "x86" -> "x86-" ^ (x86_source ()).X86.model
        | architecture -> Option.get architecture in
      let channel = open_out (Filename.concat directory
        (inventory_stem ^ "-inventory.json")) in
      Fun.protect ~finally:(fun () -> close_out channel)
        (fun () -> output_string channel (Yojson.Basic.pretty_to_string inventory ^ "\n"))

let target out_file state =
  active_root := "upstream preparation";
  try target_inner out_file state with
  | Type_error.Type_error (loc, error) ->
      let message, hint = Type_error.string_of_type_error error in
      raise (Reporting.err_typ ?hint loc
        ("HOL Light while exporting " ^ !active_root ^ ": " ^ message))

(* Register with Sail's target/plugin API. Sail owns parsing/typechecking and
   invokes target with its checked compiler state. These options choose
   entries, source assumptions, completion checks and output location.
   supports_runtime_config allows the RV32 JSON selections to be consumed by
   the frontend; it is not a proof about arbitrary runtime configurations. *)
let _ =
  Target.register ~name:"hol_light"
    ~description:"export typed Sail instruction computations to HOL Light"
    ~supports_runtime_config:true
    ~supports_abstract_types:true
    ~options:[
      (Flag.create ~prefix:["hol_light"] ~arg:"aarch64|rv32|x86" "architecture",
       Arg.Symbol (["aarch64"; "rv32"; "x86"], fun name -> upstream_architecture := Some name),
       "select upstream instruction entries and explicit architecture boundaries");
      (Flag.create ~prefix:["hol_light"] ~arg:"rems|shina" "x86_source",
       Arg.Symbol (["rems"; "shina"], fun name -> x86_model := Some name),
       "select the external x86 model whose bodies and state bindings apply");
      (Flag.create ~prefix:["hol_light"] ~arg:"family" "family",
       Arg.String (fun name -> upstream_families := !upstream_families @ [name]),
       "select an upstream instruction family (repeatable)");
      (Flag.create ~prefix:["hol_light"] ~arg:"feature=true|false" "assume_feature",
       Arg.String (fun text ->
         match String.split_on_char '=' text with
         | [name; ("true" | "false" as value)] ->
             requested_assumptions := !requested_assumptions @
               [Entry.Feature (name, value = "true")]
         | _ -> raise (Arg.Bad "expected feature=true|false")),
       "assume processor feature availability; checked against Sail's Feature enum");
      (Flag.create ~prefix:["hol_light"] ~arg:"register.field=0|1" "assume_bit",
       Arg.String (fun text ->
         match String.split_on_char '=' text with
         | [target; ("0" | "1" as value)] ->
             (match String.split_on_char '.' target with
              | [register; field] -> requested_assumptions := !requested_assumptions @
                  [Entry.Initial_bit (register, field, value = "1")]
              | _ -> raise (Arg.Bad "expected register.field=0|1"))
         | _ -> raise (Arg.Bad "expected register.field=0|1")),
       "assume an initial one-bit source field; reject writes that could invalidate it");
      (Flag.create ~prefix:["hol_light"] ~arg:"register=constructor" "assume_enum",
       Arg.String (fun text ->
         match String.split_on_char '=' text with
         | [register; constructor] -> requested_assumptions := !requested_assumptions @
             [Entry.Initial_enum (register, constructor)]
         | _ -> raise (Arg.Bad "expected register=constructor")),
       "assume an initial enum register; check membership and reject invalidating writes");
      (Flag.create ~prefix:["hol_light"] ~arg:"register=true|false" "assume_bool",
       Arg.String (fun text ->
         match String.split_on_char '=' text with
         | [register; ("true" | "false" as value)] ->
             requested_assumptions := !requested_assumptions @
               [Entry.Initial_bool (register, value = "true")]
         | _ -> raise (Arg.Bad "expected register=true|false")),
       "assume an initial Boolean register; check its type and reject invalidating writes");
      (Flag.create ~prefix:["hol_light"] ~arg:"directory" "output_dir",
       Arg.String (fun directory -> output_directory := Some directory),
       "emit canonical family models and inventory after checking every selected family");
      (Flag.create ~prefix:["hol_light"] ~arg:"count" "jobs",
       Arg.Int (fun count ->
         if count < 1 then raise (Arg.Bad "expected a positive job count");
         export_jobs := count),
       "translate batch families in up to this many forked worker processes");
      (Flag.create ~prefix:["hol_light"] ~arg:"function" "root",
       Arg.String (fun name -> roots := !roots @ [name]),
       "select a typed function for export (repeatable)");
      (Flag.create ~prefix:["hol_light"] "normal_retirement", Arg.Set requested_retirement,
       "export successful RV32 retirement relations with guarded assertions and jump events");
      (Flag.create ~prefix:["hol_light"] "quote_sources", Arg.Set quote_sources,
       "copy the Sail source of each definition into the model, not only its path:line")
    ]
    ~rewrites:[] target
