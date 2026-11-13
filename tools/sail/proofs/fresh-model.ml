(* Load a large generated model without HOL's benign-redefinition search.
   The kernel still declares exactly the supplied body: the function name
   must be fresh and each left-hand argument must be a variable. Apply the
   checked definition to those arguments to recover its original equation.

   Generated instruction bindings then select fixed branches of shared
   functions. Evaluate their equations by value, retaining symbolic registers
   and state, rather than copying let-bound calculations before selection.
   Cache only the compiled rewrite equations, not conformance results.

   A driver opens this module only inside its generated-model module.
   HOL's usual new_definition and REWRITE_RULE remain unchanged elsewhere. *)
module Sail_hl_fresh_model = struct
  let new_definition term =
    let quantified,body = strip_forall term in
    let left,right = dest_eq body in
    let name,arguments = strip_comb left in
    if not(is_var name && forall is_var arguments) then
      failwith "Sail model definition requires a fresh name and variable arguments";
    let basic = new_basic_definition
      (mk_eq(name,list_mk_abs(arguments,right))) in
    let applied = rev_itlist (fun argument theorem ->
      let application = AP_THM theorem argument in
      TRANS application (BETA_CONV(rand(concl application))))
      arguments basic in
    GEN_ALL(GENL quantified applied);;

  let REWRITE_RULE =
    let cached = ref None in
    fun equations theorem ->
      let computations = match !cached with
        | Some(previous,computations) when equations = previous -> computations
        | _ ->
            let computations = Compute.bool_compset () in
            num_compute_add_convs computations;
            int_compute_add_convs computations;
            Compute.add_thms (LET_END_DEF :: FST :: SND ::
              NUM_OF_INT_OF_NUM :: equations) computations;
            cached := Some(equations,computations);
            computations in
      CONV_RULE (Compute.CBV_CONV computations) theorem;;
end;;
