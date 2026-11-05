(* Print a required theorem for the CI log audit: its name, then its
   statement. Every driver prints through this function only. *)

(* A _SAFE_EQ theorem has three conjuncts, about one guard G on the
   fields and the initial state s, s2n-bignum's relation H and the
   generated relation R:

     (exists fields s. G) /\
     (forall fields s t. G ==> (R s t <=> H s t)) /\
     (forall fields s. ~G ==> H s = ASSIGNS entirety s)

   The guard can hold; inside it the relations agree; outside it H
   permits every final state. sail_hl_report checks this shape in the
   kernel's terms, not in the printed text. For Arm memory, R and H are
   compared through sail_hl_arm_memory_observed. *)

let SAIL_HL_UNGUARDED_ENTIRETY = prove
 (`!g (x:A->A->bool) s.
     ~g ==> (if g then x else ASSIGNS entirety) s = ASSIGNS entirety s`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* From |- H s = (if G then X else ASSIGNS entirety) s, the third
   conjunct, quantified over the given variables. *)
let sail_hl_guard_boundary quantified unfolded =
  let conditional,s = dest_comb(rhs(concl unfolded)) in
  let guard,(branch,_) = dest_cond conditional in
  let outside = ASSUME(mk_neg guard) in
  let entirety =
    MP (ISPECL [guard; branch; s] SAIL_HL_UNGUARDED_ENTIRETY) outside in
  GENL quantified (DISCH (mk_neg guard) (TRANS unfolded entirety));;

(* Layout of a reported statement.

   HOL's print_thm puts every argument of a long application on its own
   line, which hides the structure of the statements. sail_hl_layout
   lays the conclusion out for reading within sail_hl_margin columns:

   - A subterm that fits on the rest of its line is printed by HOL's own
     printer, on one line.
   - "forall x y." and "exists x." put their body on the next line,
     indented by 2 more than the binder. Variables that do not fit on
     the binder's line continue after "forall ".
   - An infix operator that does not fit puts each operand on its own
     line at one indentation, with the operator at the end of the line
     of its left operand. A chain of a right associative operator, such
     as /\ and ==>, gives one line per operand.
   - An application that does not fit has its head on one line. Its
     arguments follow, indented by 2 more than the head and packed onto
     lines, so that short arguments such as "s t" stay together.
   - "if c then a else b" that does not fit puts "if c then a" and
     "else b" on lines of their own, at one indentation.
   - Other terms (lambda, let, sets, lists) are printed by HOL on one
     line, even if the line is then longer than the margin.

   An operand is parenthesized where its own operator binds less tightly
   than the operator around it; some operands get parentheses that HOL
   would omit. sail_hl_report parses the layout back with HOL's parser
   and requires the result to be alpha-equivalent to the conclusion, so
   a layout that changes the meaning cannot be reported. *)

let sail_hl_margin = 80;;

(* HOL's one-line text of a term, without parentheses around it. *)
let sail_hl_flat tm =
  let buf = Buffer.create 256 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_margin fmt 100000000;
  pp_print_term fmt tm;
  Format.pp_print_flush fmt ();
  let text = Buffer.contents buf in
  if String.contains text '\n' then
    failwith ("sail_hl_flat: HOL printed a line break in " ^ text);
  text;;

type sail_hl_shape =
    Sail_binder of string * term list * term
  | Sail_cond of term * term * term
  | Sail_infix of string * int * string * term * term
  | Sail_neg of term
  | Sail_app of term * term list
  | Sail_flat;;

let sail_hl_reverse (name,ty) =
  try fst(find (fun (_,(name',ty')) ->
                  name' = name && can (type_match ty' ty) []) (!the_interface))
  with Failure _ -> name;;

(* The operator, its precedence and associativity, and the operands of an
   application that HOL prints as an infix. *)
let sail_hl_dest_infix tm =
  match tm with
    Comb(Comb(op,l),r) when is_const op || is_var op ->
      let s = sail_hl_reverse (name_of op,type_of op) in
      let p,a = get_infix_status s in
      (s,p,a,l,r)
  | _ -> failwith "sail_hl_dest_infix";;

(* Heads that HOL prints in a special way, not as a plain application. *)
let sail_hl_special_heads =
  ["COND"; "LET"; "LET_END"; "_MATCH"; "_FUNCTION"; "_SEQPATTERN";
   "_UNGUARDED_PATTERN"; "_GUARDED_PATTERN"; "_FALSITY_"; "GSPEC"; "SETSPEC";
   "INSERT"; "EMPTY"; "UNIV"; "DECIMAL"; "NUMERAL"];;

let sail_hl_shape tm =
  if can dest_list tm || can dest_numeral tm || is_abs tm || is_gabs tm
  then Sail_flat
  else if is_forall tm || is_exists tm then
    let q,(vs,b) =
      if is_forall tm then "forall",strip_forall tm
      else "exists",strip_exists tm in
    if forall is_var vs then Sail_binder(q,vs,b) else Sail_flat
  else if is_uexists tm then
    let v,b = dest_uexists tm in
    if is_var v then Sail_binder("?!",[v],b) else Sail_flat
  else if is_cond tm then
    let c,(a,b) = dest_cond tm in Sail_cond(c,a,b)
  else if is_neg tm then Sail_neg(dest_neg tm)
  else
    try let s,p,a,l,r = sail_hl_dest_infix tm in Sail_infix(s,p,a,l,r)
    with Failure _ ->
      let hop,args = strip_comb tm in
      if args = [] || not (is_const hop || is_var hop) then Sail_flat else
      let s = sail_hl_reverse (name_of hop,type_of hop) in
      if parses_as_binder s || is_prefix s || mem s sail_hl_special_heads
      then Sail_flat
      (* An infix applied to more than two arguments, such as the relation
         (R ,, E) applied to s and t: its head is the infix term. *)
      else if can get_infix_status s && length args > 2 then
        (match args with
           l :: r :: rest -> Sail_app(list_mk_comb(hop,[l;r]),rest)
         | _ -> Sail_flat)
      else Sail_app(hop,args);;

(* A text that needs no parentheses as an argument: a name, a number or
   a bracketed text such as a pair or a list. *)
let sail_hl_atomic text =
  let n = String.length text in
  let word c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
               (c >= '0' && c <= '9') || c = '_' || c = '\'' || c = '.' in
  let rec all i = i >= n || (word text.[i] && all (i + 1)) in
  let closer = function '(' -> ')' | '[' -> ']' | '{' -> '}' | _ -> ' ' in
  let rec enclosed depth i =
    (* the opening bracket at 0 closes exactly at the last character *)
    if i >= n then false else
    let c = text.[i] in
    let depth' = if c = '(' || c = '[' || c = '{' then depth + 1
                 else if c = ')' || c = ']' || c = '}' then depth - 1
                 else depth in
    if depth' = 0 then i = n - 1 else enclosed depth' (i + 1) in
  n > 0 && (all 0 ||
            (closer text.[0] = text.[n - 1] && closer text.[0] <> ' ' &&
             enclosed 0 0 && not (String.contains text '"')));;

let sail_hl_spaces n = String.make n ' ';;

(* Indent the first line of a layout, whose other lines carry their own
   indentation. *)
let sail_hl_below col lines =
  match lines with
    first :: rest -> (sail_hl_spaces col ^ first) :: rest
  | [] -> [];;

let sail_hl_append lines suffix =
  let rec go = function
      [x] -> [x ^ suffix]
    | x :: rest -> x :: go rest
    | [] -> [suffix] in
  go lines;;

let sail_hl_parens lines =
  match sail_hl_append lines ")" with
    first :: rest -> ("(" ^ first) :: rest
  | [] -> ["()"];;

(* Does an operand of an infix with precedence p and associativity a, on
   the left or the right, need parentheses? *)
let sail_hl_operand_parens p a left tm =
  match sail_hl_shape tm with
    Sail_infix(_,p2,_,_,_) ->
      p2 < p || (p2 = p && ((left && a = "right") || (not left && a = "left")))
  | Sail_binder _ -> left || p > 8
  | Sail_cond _ -> true
  | Sail_neg _ -> p > 8
  | Sail_app _ -> false
  | Sail_flat -> not (sail_hl_atomic (sail_hl_flat tm));;

let sail_hl_arg_parens tm =
  match sail_hl_shape tm with
    Sail_flat -> not (sail_hl_atomic (sail_hl_flat tm))
  | _ -> true;;

(* The operands of a chain of one infix, and which are left operands. *)
let sail_hl_chain op a tm =
  let rec right tm =
    try let s,_,_,l,r = sail_hl_dest_infix tm in
        if s = op then l :: right r else [tm]
    with Failure _ -> [tm] in
  let rec left tm =
    try let s,_,_,l,r = sail_hl_dest_infix tm in
        if s = op then left l @ [r] else [tm]
    with Failure _ -> [tm] in
  match tm with
    Comb(Comb(_,l),r) -> if a = "right" then l :: right r else left l @ [r]
  | _ -> failwith "sail_hl_chain";;

let rec sail_hl_lay tm col tail =
  let text = sail_hl_flat tm in
  if col + String.length text + tail <= sail_hl_margin then [text] else
  match sail_hl_shape tm with
    Sail_binder(q,vs,body) ->
      (* The binder, then its variables from column col + length q + 1. *)
      let names = map (fun v -> fst(dest_var v)) vs in
      let names = (butlast names) @ [last names ^ "."] in
      let start = col + String.length q + 1 in
      let lines = ref [] and current = ref q and room = ref col in
      List.iter (fun name ->
        if !room + String.length !current + 1 + String.length name
           <= sail_hl_margin
        then current := !current ^ " " ^ name
        else (lines := (sail_hl_spaces !room ^ !current) :: !lines;
              room := start; current := name)) names;
      lines := (sail_hl_spaces !room ^ !current) :: !lines;
      let header = match rev !lines with
          first :: rest ->
            String.sub first col (String.length first - col) :: rest
        | [] -> [] in
      header @ sail_hl_below (col + 2) (sail_hl_lay body (col + 2) tail)
  | Sail_cond(c,a,b) ->
      (* "if c then a" and "else b" when the first fits on a line, else
         "if c", "then a" and "else b", each branch from column col + 5. *)
      let short = "if " ^ sail_hl_flat c ^ " then " ^ sail_hl_flat a in
      let first =
        if col + String.length short <= sail_hl_margin then [short]
        else
          (match sail_hl_lay c (col + 3) 0 with
             f :: rest -> ("if " ^ f) :: rest | [] -> []) @
          (match sail_hl_lay a (col + 5) 0 with
             f :: rest -> (sail_hl_spaces col ^ "then " ^ f) :: rest
           | [] -> []) in
      first @
      (match sail_hl_lay b (col + 5) tail with
         f :: rest -> (sail_hl_spaces col ^ "else " ^ f) :: rest | [] -> [])
  | Sail_neg operand ->
      let parens = match sail_hl_shape operand with
          Sail_app _ -> false
        | Sail_flat -> not (sail_hl_atomic (sail_hl_flat operand))
        | _ -> true in
      let lines = sail_hl_lay_operand parens operand (col + 1) tail in
      (match lines with first :: rest -> ("~" ^ first) :: rest | [] -> [])
  | Sail_infix(op,p,a,_,_) ->
      let items = sail_hl_chain op a tm in
      let n = length items in
      let pieces = ref [] in
      List.iteri (fun i item ->
        let left = if a = "right" then i < n - 1 else i = 0 in
        let parens = sail_hl_operand_parens p a left item in
        let last = (i = n - 1) in
        let lines = sail_hl_lay_operand parens item col
                      (if last then tail else String.length op + 1) in
        let lines = if last then lines else sail_hl_append lines (" " ^ op) in
        pieces := (if i = 0 then lines else sail_hl_below col lines) :: !pieces)
        items;
      List.concat (rev !pieces)
  | Sail_app(hop,args) ->
      (* The last two arguments, when both are variables such as the
         states "s t", form one unit that is never split across lines. *)
      let kept = match rev args with
          t :: s :: _ when is_var s && is_var t -> [s; t]
        | _ -> [] in
      let units =
        if length kept < 2 then map (fun arg -> [arg]) args
        else map (fun arg -> [arg])
               (List.filteri (fun i _ -> i < length args - length kept) args)
             @ [kept] in
      let n = length units in
      let col' = col + 2 in
      let head =
        if is_const hop || is_var hop then [sail_hl_flat hop]
        else sail_hl_lay_operand true hop col 0 in
      let lines = ref (rev head) in
      let current = ref "" and is_open = ref false in
      let flush () =
        if !is_open then lines := (sail_hl_spaces col' ^ !current) :: !lines;
        is_open := false in
      List.iteri (fun i unit ->
        let after = if i = n - 1 then tail else 0 in
        let arg = hd unit in
        let parens = length unit = 1 && sail_hl_arg_parens arg in
        let flat = String.concat " " (map sail_hl_flat unit) in
        let piece = if parens then "(" ^ flat ^ ")" else flat in
        if !is_open && col' + String.length !current + 1 +
                         String.length piece + after <= sail_hl_margin
        then current := !current ^ " " ^ piece
        else begin
          flush ();
          if length unit > 1 || col' + String.length piece + after <= sail_hl_margin
          then (current := piece; is_open := true)
          else lines := List.rev_append
                 (sail_hl_below col' (sail_hl_lay_operand parens arg col' after))
                 !lines
        end) units;
      flush ();
      rev !lines
  | Sail_flat -> [text]

and sail_hl_lay_operand parens tm col tail =
  if parens then sail_hl_parens (sail_hl_lay tm (col + 1) (tail + 1))
  else sail_hl_lay tm col tail;;

(* The conclusion of a theorem, laid out, without its "|- ". Parsing this
   text must give back the conclusion. *)
let sail_hl_layout tm = String.concat "\n" (sail_hl_lay tm 3 0);;

let sail_hl_statement name theorem =
  let conclusion = concl theorem in
  let layout = sail_hl_layout conclusion in
  let parsed =
    try parse_term layout
    with e -> failwith (name ^ ": the laid out statement does not parse: " ^
                        Printexc.to_string e ^ "\n|- " ^ layout) in
  (* The text does not determine every type, for example the word size
     in "val (word 0)". Accept a parse that is the conclusion up to a
     substitution of types for its type variables; the parse has no free
     variables, so no term is substituted. *)
  let same =
    frees parsed = [] &&
    (try aconv (instantiate (term_match [] parsed conclusion) parsed)
                conclusion
     with Failure _ -> false) in
  if not same then begin
    let rec difference a b =
      if aconv a b then failwith "same" else
      match a,b with
        Comb(f,x),Comb(g,y) ->
          (try difference f g with Failure _ -> difference x y)
      | Abs(_,s),Abs(_,t) -> difference s t
      | _ -> (a,b) in
    let where =
      try let a,b = difference parsed conclusion in
          "\nfirst difference, parsed: " ^ sail_hl_flat a ^ " : " ^
          string_of_type (type_of a) ^ "\nstatement:  " ^ sail_hl_flat b ^
          " : " ^ string_of_type (type_of b)
      with Failure _ -> "" in
    failwith (name ^ ": the laid out statement parses to another term" ^
              where ^ "\n|- " ^ layout)
  end;
  "|- " ^ layout;;

(* Which side of an iff is generated. In a statement that compares a
   generated relation with s2n-bignum's, the left side is the generated
   one. Its head is a generated root, possibly under the wrappers
   sail_hl_arm_memory_observed and sail_hl_x86_core, or the first
   operand of a sequence "R ,, event". The right side must not mention
   a generated root. A root is a sail_hl_ constant that returns a
   relation, other than the wrappers. *)

let sail_hl_wrappers = ["sail_hl_arm_memory_observed"; "sail_hl_x86_core"];;

let sail_hl_is_root tm =
  match tm with
    Const(name,ty) ->
      let rec result ty =
        try result (snd(dest_fun_ty ty)) with Failure _ -> ty in
      String.length name > 8 && String.sub name 0 8 = "sail_hl_" &&
      not (mem name sail_hl_wrappers) && result ty = bool_ty
  | _ -> false;;

let rec sail_hl_left_root tm =
  match strip_comb tm with
    Const(name,_),relation :: _ when mem name (",," :: sail_hl_wrappers) ->
      sail_hl_left_root relation
  | head,_ when sail_hl_is_root head -> head
  | _ -> failwith "no generated root";;

let sail_hl_check_sides name equivalence =
  let left,right = dest_iff equivalence in
  (try ignore(sail_hl_left_root left)
   with Failure _ ->
     failwith (name ^ ": the left side of <=> is not headed by a generated" ^
               " root"));
  if can (find_term sail_hl_is_root) right then
    failwith (name ^ ": the right side of <=> mentions a generated root");;

let sail_hl_check_safe_eq name theorem =
  let refuse reason =
    failwith (name ^ ": not a _SAFE_EQ theorem: " ^ reason) in
  match conjuncts (concl theorem) with
  | [satisfiable; agreement; boundary] ->
      let guard = snd(strip_exists satisfiable) in
      let inside,equivalence = try dest_imp(snd(strip_forall agreement))
        with Failure _ -> refuse "no guarded agreement" in
      let outside,equation = try dest_imp(snd(strip_forall boundary))
        with Failure _ -> refuse "no boundary" in
      if not (aconv guard inside) ||
         not (is_neg outside && aconv guard (dest_neg outside)) then
        refuse "the three conjuncts do not share one guard";
      sail_hl_check_sides name equivalence;
      let hol = snd(dest_iff equivalence) in
      let relation = match strip_comb hol with
        | Const("sail_hl_arm_memory_observed",_),[relation;_;_] -> relation
        | _ -> rator(rator hol) in
      let applied,entirety = dest_eq equation in
      let unguarded,state = dest_comb applied in
      if unguarded <> relation then
        refuse "the boundary is about another relation";
      (match entirety with
       | Comb(Comb(Const("ASSIGNS",_),Const("entirety",_)),s)
           when s = state -> ()
       | _ -> refuse "the boundary is not ASSIGNS entirety at the same state")
  | _ -> refuse "not three conjuncts";;

let sail_hl_report (name, theorem) =
  if hyp theorem <> [] || frees (concl theorem) <> [] then
    failwith (name ^ ": the theorem has hypotheses or free variables");
  let suffix = "_SAFE_EQ" in
  let n = String.length name and k = String.length suffix in
  if n >= k && String.sub name (n - k) k = suffix then
    sail_hl_check_safe_eq name theorem;
  (let body = snd(strip_forall (concl theorem)) in
   if is_iff body then sail_hl_check_sides name body);
  (* Check and lay out first: parse_term may print a warning, which must
     not come between the name and the statement. *)
  let statement = sail_hl_statement name theorem in
  print_endline name; print_endline statement; print_newline ();;
