(* HOL terms as the translator builds them, and the simplification of
   their bindings before printing. This module is part of the trusted
   translator; it is separate so that tests/test_simplify.py can check
   simplify_bindings on its own. *)
open Libsail

(* htyp records the supported HOL representation of a source type. term is
   the translation result, printed only after all selected bodies succeed.
   Neither representation constructs kernel theorems; HOL checks the emitted
   definitions later. Partial_word and Bounded_value are internal evidence
   about a backing term, not additional observable HOL value constructors. *)
type htyp = Word of int | Poly_word of string | Empty_bits | Dynamic_bits | Int | Bool | String_type | Unit | Tuple of htyp list | Enum of string
          | Record of (string * htyp) list | Result of htyp * htyp
          | Option_type of htyp | Unit_variant of string * Ast.id list
          | Binary_variant of (string * htyp) * (string * htyp)

type term =
  (* Non-local architectural fault, not a HOL value. Instruction relations
     may contain this marker; lower_faults interprets it as universal final
     state admission and propagates it through intermediate let bindings. *)
  | Fault
  (* EndOfInstruction preserves the reached state and skips the rest of the
     instruction. A failed source assertion admits no normal outcome. *)
  | Stop of term
  | Reject
  (* Fresh, typed choices denote Sail undefined values, not chosen defaults.
     They are existentially bound when the complete relation is lowered. *)
  | Choose of term * term
  | Exists of term * term
  | Atom of string
  (* Literal source bytes, not text to interpolate into a HOL quotation. *)
  | String_literal of string
  | App of string * term list
  | Infix of string * term * term
  | Cond of term * term * term
  | Tuple_term of term list
  | Let of term * term * term
  | Typed of term * htyp
  | Lambda of term * term
  (* Internal backing terms are not observations of unknown source bits.
     Every source read or externally visible write must discharge the mask. *)
  | Partial_word of term * int * int list
  (* Bounds describe an already evaluated value; printing retains its
     original backing term. They never stand in for evaluation or effects. *)
  | Bounded_value of term * Nat_big_num.num * Nat_big_num.num
  (* Print the shared call, but retain facts computed from the same checked
     source at this actual call. This keeps constant assertions, bounds and
     branch decisions without erasing the call or its argument effects. *)
  | Shared_value of term * term

(* Printing removes bindings that the printed term does not need. Each
   step replaces a HOL term by an equal one:
   - let x = v in b is b if x is not free in b, for every v: HOL terms
     denote values and have no effects, and the state is an explicit
     argument. The same holds for a tuple pattern, since every pair is a
     pair of its components.
   - ?x. b is b if x is not free in b: every HOL type has a value.
   - let x = y in b, for a variable y, is b with y for x. This is done
     only if no binder inside b binds y: y is bound nowhere in the term,
     or only by a binder around this let.
   - let (a,b) = (x,y) in b is let a = x in let b = y in b if neither x
     nor y mentions a or b.
   - (t:ty):ty is t:ty.
   A binding whose value still holds a fault, stop, rejection or choice
   marker is kept: those are not HOL values, and print_term refuses them.
   Internal wrappers that print as their backing term become that term. *)
module Name_set = Set.Make(String)

let rec pattern_variables = function
  | Atom name -> [name]
  | Typed (pattern, _) -> pattern_variables pattern
  | Tuple_term patterns -> List.concat_map pattern_variables patterns
  | _ -> []

(* The immediate subterms that print_term prints, binder patterns
   included; internal wrappers print as their backing term. *)
let children = function
  | Fault | Reject | Atom _ | String_literal _ -> []
  | Stop value | Typed (value, _) | Partial_word (value, _, _)
  | Bounded_value (value, _, _) | Shared_value (value, _) -> [value]
  | Choose (left, right) | Exists (left, right) | Lambda (left, right)
  | Infix (_, left, right) -> [left; right]
  | Let (first, second, third) | Cond (first, second, third) -> [first; second; third]
  | App (_, values) | Tuple_term values -> values

(* The same term with f applied to each immediate subterm other than a
   binder pattern. *)
let map_children f = function
  | (Fault | Reject | Atom _ | String_literal _) as term -> term
  | Stop value -> Stop (f value)
  | Typed (value, typ) -> Typed (f value, typ)
  | Partial_word (value, width, known) -> Partial_word (f value, width, known)
  | Bounded_value (value, low, high) -> Bounded_value (f value, low, high)
  | Shared_value (value, facts) -> Shared_value (f value, facts)
  | Choose (pattern, body) -> Choose (pattern, f body)
  | Exists (pattern, body) -> Exists (pattern, f body)
  | Lambda (pattern, body) -> Lambda (pattern, f body)
  | Infix (operator, left, right) -> Infix (operator, f left, f right)
  | Let (pattern, value, body) -> Let (pattern, f value, f body)
  | Cond (condition, yes, no) -> Cond (f condition, f yes, f no)
  | App (name, values) -> App (name, List.map f values)
  | Tuple_term values -> Tuple_term (List.map f values)

let rec has_marker = function
  | Fault | Stop _ | Reject | Choose _ -> true
  | term -> List.exists has_marker (children term)

(* Whether a name occurs anywhere in a term, bound or free. *)
let rec mentions name = function
  | Atom other -> other = name
  | App (other, _) when other = name -> true
  | term -> List.exists (mentions name) (children term)

let simplify_bindings term =
  (* How often each name is bound anywhere in the term. *)
  let bound = Hashtbl.create 1024 in
  let rec count term =
    (match term with
     | Let (pattern, _, _) | Lambda (pattern, _) | Exists (pattern, _)
     | Choose (pattern, _) ->
         List.iter (fun name ->
           Hashtbl.replace bound name
             (1 + Option.value (Hashtbl.find_opt bound name) ~default:0))
           (pattern_variables pattern)
     | _ -> ());
    List.iter count (match term with
      | Let (_, value, body) -> [value; body]
      | Lambda (_, body) | Exists (_, body) | Choose (_, body) -> [body]
      | term -> children term) in
  count term;
  let binders name = Option.value (Hashtbl.find_opt bound name) ~default:0 in
  (* The steps below rely on two facts about the translator's terms; refuse
     a term without them rather than print a wrong one. A call's head is a
     constant, never a bound name, since rename does not substitute heads.
     An atom is one name or a closed constant, since free names are
     compared as whole atoms; the one composite atom is (dimindex(:N)). *)
  let rec check term =
    (match term with
     | App (name, _) when Hashtbl.mem bound name ->
         failwith ("HOL Light: binding simplification: the call head " ^ name ^
           " is also a bound name")
     | Atom text when String.exists (fun c -> c = ' ' || c = '\n' || c = '\t') text ||
                      (String.contains text '(' &&
                       not (String.starts_with ~prefix:"(dimindex(:" text)) ->
         failwith ("HOL Light: binding simplification: the atom " ^ text ^
           " is not a single name")
     | _ -> ());
    List.iter check (children term) in
  check term;
  (* Top down: replace renamed variables, keeping shadowing. enclosing
     holds the names bound around the current point. *)
  let rec rename enclosing aliases term =
    let go = rename enclosing aliases in
    let under pattern body =
      let names = pattern_variables pattern in
      rename (List.fold_right Name_set.add names enclosing)
        (List.filter (fun (name, _) -> not (List.mem name names)) aliases) body in
    let variable = function
      | Atom name | Typed (Atom name, _) ->
          binders name = 0 || (binders name = 1 && Name_set.mem name enclosing)
      | _ -> false in
    match term with
    | Atom name -> Option.value (List.assoc_opt name aliases) ~default:term
    | Let ((Atom name | Typed (Atom name, _)) as pattern, value, body) ->
        let value = go value in
        if variable value then
          rename (Name_set.add name enclosing)
            ((name, value) :: List.remove_assoc name aliases) body
        else Let (pattern, value, under pattern body)
    | Let (Tuple_term patterns, Tuple_term values, body)
        when List.length patterns = List.length values &&
             not (List.exists (fun value ->
               List.exists (fun name -> mentions name value)
                 (List.concat_map pattern_variables patterns)) values) ->
        (* let (a,b) = (x,y) in b is let a = x in let b = y in b when
           neither x nor y mentions a or b. *)
        go (List.fold_right2 (fun pattern value body -> Let (pattern, value, body))
              patterns values body)
    | Let (pattern, value, body) -> Let (pattern, go value, under pattern body)
    | Lambda (pattern, body) -> Lambda (pattern, under pattern body)
    | Exists (pattern, body) -> Exists (pattern, under pattern body)
    | Typed (value, typ) ->
        (match go value with
         | Typed (inner, inner_typ) when inner_typ = typ -> Typed (inner, typ)
         | value -> Typed (value, typ))
    | Partial_word (value, _, _) | Bounded_value (value, _, _)
    | Shared_value (value, _) -> go value
    | term -> map_children go term in
  (* Bottom up: drop unused bindings; return the free names too. App's
     head counts as an occurrence, to be safe. *)
  let rec prune term = match term with
    | Atom name -> term, Name_set.singleton name
    | String_literal _ | Fault | Reject -> term, Name_set.empty
    | Let (pattern, value, body) ->
        let body, free = prune body in
        let names = pattern_variables pattern in
        if not (List.exists (fun name -> Name_set.mem name free) names) &&
           not (has_marker value) then body, free
        else
          let value, used = prune value in
          Let (pattern, value, body),
          Name_set.union used (List.fold_right Name_set.remove names free)
    | Exists (pattern, body) ->
        let body, free = prune body in
        let names = pattern_variables pattern in
        if List.exists (fun name -> Name_set.mem name free) names
        then Exists (pattern, body), List.fold_right Name_set.remove names free
        else body, free
    | Lambda (pattern, body) ->
        let body, free = prune body in
        Lambda (pattern, body),
        List.fold_right Name_set.remove (pattern_variables pattern) free
    | App (name, values) ->
        let values, free = prune_all values in
        App (name, values), Name_set.add name free
    | Tuple_term values ->
        let values, free = prune_all values in Tuple_term values, free
    | Infix (operator, left, right) ->
        let left, used = prune left and right, free = prune right in
        Infix (operator, left, right), Name_set.union used free
    | Cond (condition, yes, no) ->
        let condition, a = prune condition and yes, b = prune yes and no, c = prune no in
        Cond (condition, yes, no), Name_set.union a (Name_set.union b c)
    | Typed (value, typ) -> let value, free = prune value in Typed (value, typ), free
    | Stop value -> let value, free = prune value in Stop value, free
    | Choose (variable, value) ->
        let value, free = prune value in Choose (variable, value), free
    | Partial_word (value, _, _) | Bounded_value (value, _, _)
    | Shared_value (value, _) -> prune value
  and prune_all values =
    List.fold_right (fun value (values, free) ->
      let value, used = prune value in value :: values, Name_set.union used free)
      values ([], Name_set.empty) in
  fst (prune (rename Name_set.empty [] term))

