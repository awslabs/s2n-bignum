(* Load this file INSIDE the generated-model module. It records the checked
   equations returned by the generated file so memory proof tables can find
   an exact root by name. The kernel still declares precisely each supplied
   source body. This avoids a separate list of 246 OCaml theorem variables.

   Keep the raw instruction and helper equations. Memory proofs rewrite the
   helpers only after assuming the actual HOL instruction's safety guard:
   eager evaluation here would expand every fault or unpredictable branch
   before the proof can select the successful instruction path. No equation
   or instruction effect is replaced. Missing exports or changed encoded
   argument types are errors. *)
let sail_hl_memory_model_equations = ref [];;
let sail_hl_memory_model_helpers = ref [];;
let sail_hl_memory_model_controls = ref [];;

let sail_hl_memory_remember theorem =
  let _,equation = strip_forall(concl theorem) in
  let head,_ = strip_comb(lhand equation) in
  let name = fst(dest_const head) in
  sail_hl_memory_model_equations :=
    (name,theorem) ::
    filter (fun (previous,_) -> previous <> name)
      !sail_hl_memory_model_equations;
  theorem;;

let new_definition term =
  sail_hl_memory_remember(Sail_hl_fresh_model.new_definition term);;

(* Generated control-flow helpers use recursive definitions on HOL's sum
   type. Retain the exact equations returned by the kernel, including their
   constructor cases. They are conjunctions rather than single root
   equations, so they must not pass through sail_hl_memory_remember. *)
let new_recursive_definition recursion equations =
  let theorem = new_recursive_definition recursion equations in
  if hyp theorem <> [] then
    failwith "generated recursive definition has assumptions";
  sail_hl_memory_model_controls :=
    theorem :: !sail_hl_memory_model_controls;
  theorem;;

(* Enum comparisons occur inside instruction branches. Generated modules
   install the kernel's constructor-distinctness equations in HOL's global
   rewrite list. Retain those same equations for the closed CBV engine:
   importing all global rewrites would also import eager let substitution.
   The usual global registration is preserved unchanged. *)
let extend_basic_rewrites equations =
  if exists (fun theorem -> hyp theorem <> []) equations then
    failwith "generated datatype equations have assumptions";
  (* HOL's distinctness theorem lists each constructor pair once. Closed
     CBV also needs the reverse comparison when Sail tests STORE = LOAD
     rather than LOAD = STORE. Derive that orientation with equality
     symmetry; retain the original supplied theorem as well. *)
  let reversed = flat(map (fun original ->
    map (CONV_RULE (RAND_CONV(REWR_CONV EQ_SYM_EQ)))
      (filter (fun theorem ->
        is_neg(concl theorem) && is_eq(rand(concl theorem)))
        (map SPEC_ALL (CONJUNCTS(SPEC_ALL original))))) equations) in
  sail_hl_memory_model_controls :=
    List.rev_append (equations @ reversed) !sail_hl_memory_model_controls;
  extend_basic_rewrites equations;;

let REWRITE_RULE equations theorem =
  let _,equation = strip_forall(concl theorem) in
  let head,_ = strip_comb(lhand equation) in
  let name = fst(dest_const head) in
  sail_hl_memory_model_helpers :=
    (name,equations) ::
    filter (fun (previous,_) -> previous <> name)
      !sail_hl_memory_model_helpers;
  sail_hl_memory_remember theorem;;

(* Generated files also request arithmetic normalization of complete root
   equations. Defer that request for the same reason as helper unfolding:
   the proof should first select its safe path, rather than normalize every
   unselected outcome. The checked raw equation remains exactly unchanged. *)
let CONV_RULE _ theorem = sail_hl_memory_remember theorem;;

let SAIL_HL_ARM_MEMORY_MODEL_BINDING root fields =
  let name = "sail_hl_" ^
    String.concat "_5f" (String.split_on_char '_' root) in
  let theorem = try assoc name !sail_hl_memory_model_equations
    with Failure _ -> failwith("missing actual Sail memory export: " ^ root) in
  let theorem = SPEC_ALL theorem in
  let _,equation = strip_forall(concl theorem) in
  let _,arguments = strip_comb(lhand equation) in
  let prefix_length = length arguments - length fields in
  if prefix_length < 0 || not(forall is_var arguments) then
    failwith("invalid actual Sail memory export parameters: " ^ root);
  let configuration,encoded = chop_list prefix_length arguments in
  let substitutions = map2 (fun (field,typ) argument ->
    if type_of argument <> typ then
      failwith("changed encoded field type in actual Sail export: " ^
               root ^ ":" ^ field);
    mk_var(field,typ),argument) fields encoded in
  let operands = map fst substitutions in
  if exists (fun parameter -> mem parameter operands) configuration then
    failwith("source configuration shadows an encoded memory field: " ^ root);
  let instantiated = INST substitutions theorem in
  let source = lhand(snd(strip_forall(concl instantiated))) in
  if type_of source <> `:armstate->armstate->bool` then
    failwith("actual Sail memory export is not an instruction relation: " ^ root);
  let helpers = try assoc name !sail_hl_memory_model_helpers
    with Failure _ -> [] in
  (* Supply the generated file's checked helper, control and datatype
     equations, without unfolding bodies before the successful-domain
     hypothesis. Both the rewrite tactics and CBV split conjunctions. *)
  end_itlist CONJ
    (instantiated::helpers @ !sail_hl_memory_model_controls),source;;
