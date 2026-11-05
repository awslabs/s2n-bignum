(* Print a required theorem for the CI log audit: its name, then its
   statement. Every driver prints through this function only. *)
let sail_hl_report (name, theorem) =
  if hyp theorem <> [] || frees (concl theorem) <> [] then
    failwith (name ^ ": the theorem has hypotheses or free variables");
  print_endline name; print_thm theorem; print_newline ();;
