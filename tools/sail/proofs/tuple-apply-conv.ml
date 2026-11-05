(* Generated Sail functions contain paired let bindings. Prove the small
   tuple-application equation once with a placeholder for the body, then
   insert the actual body and arguments. By default return an ordinary
   curried application, so Compute can retain its argument closures.
   An eager evaluator can request the direct substituted body instead.
   Contract that application before inserting the supplied arguments,
   when each binder is still its own argument: kernel BETA then avoids
   scanning the large body separately for every tuple field.
   This cache stores kernel theorems, never instruction proof results. *)
type sail_hl_tuple_shape =
  | Sail_hl_tuple_leaf of hol_type
  | Sail_hl_tuple_pair of sail_hl_tuple_shape * sail_hl_tuple_shape;;

let SAIL_HL_TUPLE_APPLY_CONV ?(contract_result=false) () =
  let templates = ref [] in
  let rec shape pattern =
    if is_var pattern then Sail_hl_tuple_leaf(type_of pattern),[pattern] else
    let left,right = dest_pair pattern in
    let left_shape,left_vars = shape left
    and right_shape,right_vars = shape right in
    Sail_hl_tuple_pair(left_shape,right_shape),left_vars @ right_vars in
  let rec make = function
    | Sail_hl_tuple_leaf typ -> let variable = genvar typ in variable,[variable]
    | Sail_hl_tuple_pair(left,right) ->
        let left,left_vars = make left and right,right_vars = make right in
        mk_pair(left,right),left_vars @ right_vars in
  let rec arguments shape argument =
    match shape with
    | Sail_hl_tuple_leaf _ -> [argument]
    | Sail_hl_tuple_pair(left,right) ->
        let first,second = dest_pair argument in
        arguments left first @ arguments right second in
  fun term ->
    let abstraction,argument = dest_comb term in
    let pattern,body = dest_gabs abstraction in
    if is_var pattern then failwith "tuple beta: plain abstraction";
    let pattern_shape,variables = shape pattern in
    if length(setify variables) <> length variables then
      failwith "tuple beta: repeated variable";
    let values = arguments pattern_shape argument in
    let key = pattern_shape,type_of body in
    let placeholder,template_variables,equation =
      try assoc key !templates with Failure _ ->
        let template_pattern,template_variables = make pattern_shape in
        let function_type = itlist (mk_fun_ty o type_of)
          template_variables (type_of body) in
        let placeholder = genvar function_type in
        let template_abstraction = mk_gabs(template_pattern,
          list_mk_comb(placeholder,template_variables)) in
        let equation = GEN_BETA_CONV
          (mk_comb(template_abstraction,template_pattern)) in
        let entry = placeholder,template_variables,equation in
        templates := (key,entry) :: !templates;
        entry in
    (* Align the SMALL schema before inserting the body. Both subsequent
       beta contractions on the LEFT have each binder as its own argument,
       so they use HOL's trivial BETA rule rather than scan the large body
       separately for every tuple field. The default keeps the right-hand
       application; the direct option contracts it before substituting all
       supplied values together. *)
    (* A genvar is already fresh. It is instantiated away below, so it
       never reaches the result; scanning the large term for its free
       variables was most of this conversion's cost. *)
    let function_variable = genvar(type_of placeholder) in
    let renamed = INST
      ((function_variable,placeholder) :: zip variables template_variables)
      equation in
    let aligned_left = mk_comb(mk_gabs(pattern,
      list_mk_comb(function_variable,variables)),pattern) in
    let aligned = TRANS(ALPHA aligned_left (lhand(concl renamed))) renamed in
    let instantiated = INST
      [list_mk_abs(variables,body),function_variable] aligned in
    let reduced = CONV_RULE
      (LAND_CONV(RATOR_CONV(GABS_CONV BETAS_CONV))) instantiated in
    let reduced = if contract_result then
      CONV_RULE (RAND_CONV BETAS_CONV) reduced else reduced in
    let reduced = INST (zip values variables) reduced in
    let left = lhand(concl reduced) in
    if not(aconv left term) || hyp reduced <> [] then
      failwith "tuple beta: mismatched or open equality";
    (* compare, unlike =, stops at physically shared subterms such as the
       body, so the usual identical left side costs only its spine. *)
    if compare left term = 0 then reduced else TRANS(ALPHA term left) reduced;;

(* Check both results with aliases, typed homonyms and a free higher-order
   variable. Compare with stock kernel beta conversion; nonlinear patterns
   must refuse. Repeating a direct conversion also exercises schema reuse. *)
let () =
  List.iter (fun contract_result ->
    let convert = SAIL_HL_TUPLE_APPLY_CONV ~contract_result () in
    List.iter (fun text ->
      let term = parse_term text in
      let converted = convert term in
      let actual = if contract_result then converted else
        CONV_RULE (RAND_CONV BETAS_CONV) converted
      and expected = GEN_BETA_CONV term in
      if not(aconv (concl actual) (concl expected)) || hyp actual <> [] then
        failwith "tuple application fixture differs from kernel beta conversion";
      if contract_result &&
         not(aconv (concl(convert term)) (concl expected)) then
        failwith "direct tuple fixture retained a curried application")
     ["(\\(x:num,y:bool). x,x,y) (a,T)";
      "(\\(x:num,y:bool,z:num). x+z,y,x) (a,T,b)";
      "(\\(x:num,y:num). x+y,y,x) (a,a)";
      "(\\(x:num,y:num). k x y,x) (y,x)";
      "(\\(x:num,y:bool). (f:(num#bool)->num) (x,y)) (y:num,x:bool)";
      "(\\(x:64 word,y:bool,z:64 word). word_add x z,y,x) (a,T,b)";
      "(\\((a:num,b:bool),(c:num,d:bool)). (a+c,b,c,d)) ((x,T),(x,F))"];
    (try
       ignore(convert(parse_term "(\\(x:num,x:num). x) (a,a)"));
       failwith "tuple application fixture accepted a repeated variable"
     with Failure "tuple beta: repeated variable" -> ()))
   [false;true];
  print_endline "SAIL_HOL_TUPLE_APPLY_CONV_OK";;
