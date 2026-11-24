(* Build the left side of a vector agreement claim. Exported definitions
   put explicit source configuration components before the encoded fields.
   Retain and universally quantify every such parameter, with
   exactly the type in the generated definition.

   FPSR writes are explicitly excluded by the exporter, not discarded
   by this helper. Any retained FPSR read component is quantified like
   every other component. Encoded operands and HOL states keep their
   original domains. This constructs statements, not instruction effects. *)
let SAIL_HL_ARM_VECTOR_MODEL_APPLICATION encoded_arguments definition =
  let _, body = strip_forall(concl definition) in
  let head, arguments = strip_comb(lhand body) in
  let prefix_length = length arguments - encoded_arguments in
  if prefix_length < 0 then
    failwith "vector export has fewer arguments than its encoded fields";
  let parameters = fst(chop_list prefix_length arguments) in
  if not(forall is_var parameters) then
    failwith "vector export configuration arguments must be variables";
  let bindings = map (fun parameter ->
    let name,typ = dest_var parameter in
    name,typ) parameters in
  let quantifiers =
    if bindings = [] then ""
    else "! " ^ String.concat " " (map (fun (name,typ) ->
      "(" ^ name ^ ":" ^ string_of_type typ ^ ")") bindings) ^ ". " in
  let application = String.concat " " (fst(dest_const head) ::
    map fst bindings) in
  quantifiers,application;;
