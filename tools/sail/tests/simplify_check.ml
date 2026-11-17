(* Differential test of Hol_term.simplify_bindings, run by
   tests/test_simplify.py. Random terms over a small name pool, so that
   shadowing and capture are frequent, are evaluated symbolically before
   and after simplification: free names stand for themselves, let binds by
   value, tuple patterns bind projections, and binders get fresh ids that
   are then renamed by order of appearance. The two values must be equal.
   With variable call heads, which the translator never builds,
   simplify_bindings must refuse the term instead. *)
open Hol_term

type v =
  | Sym of string
  | Ap of string * v list
  | Tup of v list
  | Bv of int
  | Lam of pat * v
  | Ex of pat * v
and pat = PVar of int | PTup of pat list

let counter = ref 0
let fresh_id () = incr counter; !counter

exception Skip

let rec bind_pattern env p value =
  match p with
  | Atom n | Typed (Atom n, _) -> (n, value) :: env
  | Tuple_term ps | Typed (Tuple_term ps, _) ->
      let n = List.length ps in
      let parts = match value with
        | Tup vs when List.length vs = n -> vs
        | _ -> List.mapi (fun i _ -> Ap ("PROJ" ^ string_of_int i ^ "_" ^ string_of_int n, [value])) ps in
      List.fold_left2 bind_pattern env ps parts
  | _ -> raise Skip

let rec abstract_pattern env p =
  match p with
  | Atom n | Typed (Atom n, _) -> let k = fresh_id () in PVar k, (n, Bv k) :: env
  | Tuple_term ps | Typed (Tuple_term ps, _) ->
      let ps', env = List.fold_left (fun (acc, env) p ->
        let p', env = abstract_pattern env p in acc @ [p'], env) ([], env) ps in
      PTup ps', env
  | _ -> raise Skip

let rec pat_ids = function PVar k -> [k] | PTup ps -> List.concat_map pat_ids ps
let rec mentions_id k = function
  | Bv j -> j = k
  | Sym _ -> false
  | Ap (_, vs) | Tup vs -> List.exists (mentions_id k) vs
  | Lam (_, b) | Ex (_, b) -> mentions_id k b

let rec eval env term =
  match term with
  | Atom n -> (match List.assoc_opt n env with Some v -> v | None -> Sym n)
  | String_literal s -> Sym ("\"" ^ s)
  | App (f, args) ->
      let args = List.map (eval env) args in
      (match List.assoc_opt f env with
       | Some fv -> Ap ("@", fv :: args)
       | None -> Ap (f, args))
  | Tuple_term vs -> Tup (List.map (eval env) vs)
  | Infix (op, l, r) -> Ap (op, [eval env l; eval env r])
  | Cond (c, y, n) -> Ap ("COND", [eval env c; eval env y; eval env n])
  | Let (p, value, body) -> eval (bind_pattern env p (eval env value)) body
  | Typed (value, _) -> eval env value
  | Lambda (p, body) ->
      let p', env' = abstract_pattern env p in Lam (p', eval env' body)
  | Exists (p, body) ->
      let p', env' = abstract_pattern env p in
      let b = eval env' body in
      if List.exists (fun k -> mentions_id k b) (pat_ids p') then Ex (p', b) else b
  | Partial_word (v, _, _) | Bounded_value (v, _, _) | Shared_value (v, _) -> eval env v
  | Fault | Reject | Stop _ | Choose _ -> raise Skip

(* Rename binder ids by order of appearance, so that alpha-equivalent
   values compare equal. *)
let canonical value =
  let table = Hashtbl.create 16 and next = ref 0 in
  let rec cp = function
    | PVar k -> incr next; Hashtbl.replace table k !next; PVar !next
    | PTup ps -> PTup (List.map cp ps) in
  let rec go = function
    | Bv k -> Bv (try Hashtbl.find table k with Not_found -> -k)
    | Sym s -> Sym s
    | Ap (f, vs) -> Ap (f, List.map go vs)
    | Tup vs -> Tup (List.map go vs)
    | Lam (p, b) -> let p = cp p in Lam (p, go b)
    | Ex (p, b) -> let p = cp p in Ex (p, go b) in
  go value

(* Random terms over a small name pool, so that shadowing, reuse and
   capture are frequent. *)
let names = [| "a"; "b"; "c"; "x"; "y" |]
let constants = [| "T"; "one"; "k" |]
let heads_const = [| "f"; "g"; "word" |]
let variable_heads = ref false
let pick a = a.(Random.int (Array.length a))

let rec gen_pattern depth =
  match Random.int 6 with
  | 0 when depth > 0 -> Tuple_term (List.init (2 + Random.int 2) (fun _ -> gen_pattern (depth - 1)))
  | 1 -> Typed (Atom (pick names), Bool)
  | _ -> Atom (pick names)

let rec gen depth =
  if depth = 0 then
    (match Random.int 4 with
     | 0 -> Atom (pick constants)
     | 1 -> Typed (Atom (pick names), Bool)
     | _ -> Atom (pick names))
  else
    match Random.int 12 with
    | 0 | 1 | 2 ->
        let p = gen_pattern 1 in
        let value = match p, Random.int 3 with
          | Tuple_term ps, 0 -> Tuple_term (List.map (fun _ -> gen (depth - 1)) ps)
          | _, 1 -> Atom (pick names)
          | _ -> gen (depth - 1) in
        Let (p, value, gen (depth - 1))
    | 3 -> Lambda (gen_pattern 1, gen (depth - 1))
    | 4 -> Exists (gen_pattern 1, gen (depth - 1))
    | 5 -> let h = if !variable_heads && Random.bool () then pick names else pick heads_const in
           App (h, List.init (1 + Random.int 2) (fun _ -> gen (depth - 1)))
    | 6 -> Tuple_term (List.init (2 + Random.int 2) (fun _ -> gen (depth - 1)))
    | 7 -> Infix ("+", gen (depth - 1), gen (depth - 1))
    | 8 -> Cond (gen (depth - 1), gen (depth - 1), gen (depth - 1))
    | 9 -> Typed (gen (depth - 1), Bool)
    | 10 -> Typed (Typed (gen (depth - 1), Bool), Bool)
    | _ -> Atom (pick names)


let () =
  let trials = int_of_string Sys.argv.(1) in
  Random.init 42;
  let run heads =
    variable_heads := heads;
    let checked = ref 0 and refused = ref 0 and mismatches = ref 0 in
    for _ = 1 to trials do
      let term = gen (2 + Random.int 5) in
      match canonical (eval [] term) with
      | exception Skip -> ()
      | before ->
          match simplify_bindings term with
          | exception Failure _ -> incr refused
          | after ->
              incr checked;
              if canonical (eval [] after) <> before then incr mismatches
    done;
    Printf.printf "%s heads: %d checked, %d refused, %d mismatches\n"
      (if heads then "variable" else "constant") !checked !refused !mismatches;
    !mismatches in
  let constant = run false and variable = run true in
  exit (if constant = 0 && variable = 0 then 0 else 1)
