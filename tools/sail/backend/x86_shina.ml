(* shina-lab/sail-x86 instruction bindings inside the Sail compiler.

   The table selects arithmetic, shifts and vector register forms.
   docs/X86.md describes the selected instructions and input boundaries;
   vector bodies retain operand decoding after supplied instruction bytes.

   Each binding names a HOL comparison and calls an actual upstream
   instruction body. The scalar bindings select only legal operand widths;
   the arithmetic and all flag calculations remain in exec_alu_reg_rm and
   its helpers. CMP retains both inputs but does not write a destination.
   Logic instructions retain Sail's arbitrary AF result.

   A GPRRef pairs a register number with the presence of a REX prefix.
   RM_reg selects the register alternative of a register-or-memory operand.
   REX byte forms select all sixteen low bytes; no-REX byte forms select
   AL/CL/DL/BL and AH/CH/DH/BH. Both operands share that prefix choice.
   Wider forms range over all sixteen registers, including equal operands.
   These encoding choices do not fix register values or flags.
   The resolved-operand arithmetic bindings do not decode
   bytes or advance RIP. The two decoded multiply bindings below retain
   ModR/M decoding with its fetched byte supplied separately.

   run.sh x86-shina arithmetic loads the external model/x86.sail_project,
   then Entry.instantiate checks these calls against its declarations.
   The common translator follows the checked instruction and helper bodies.
   The upstream register helpers retain their own slices, high-byte choice
   and 32-bit upper clearing. Only direct accesses to their sixteen-element
   GPR array map to the existing HOL register file; the helpers are not cuts.
   Flag reads and writes map to the existing Boolean flag components.
   Neither boundary omits a flag. The separate cur_mode=LongMode assumption
   supplies the mode where a 32-bit write or operand decoder reads it. *)
open Libsail
open Ast
open Ast_defs
open Ast_util
open Entry
open X86

let reference ?(rex = true) name =
  mk_exp (E_struct (SN_id (mk_id "GPRRef"), [
    mk_fexp (mk_id "gpr_idx") (unsigned name);
    mk_fexp (mk_id "has_rex") (bool rex)
  ]))

(* Alongside each binding retain whether its selected source may consume
   LongMode. This comes from the explicit form/decoder choice, not parsing
   a root name or inspecting the generated arithmetic. An unused configured
   assumption remains recorded and does not restrict the HOL definition. *)
let scalar_entry ?(decoded = false) ~family operation form operands
    parameters body =
  make ~family (scalar_name operation form operands) parameters body,
  (decoded || form.width = 32)

let scalar_read form name =
  if form.width = 8 then
    call "read_gpr_ref" [int 8; reference ~rex:form.rex name]
  else call "read_gpr" [int form.width; unsigned name]

let scalar_write form name value =
  if form.width = 8 then
    call "write_gpr_ref" [int 8; reference ~rex:form.rex name; value]
  else call "write_gpr" [int form.width; unsigned name; value]

let alu =
  List.concat_map (fun operation ->
    List.map (fun form ->
      scalar_entry ~family:"arithmetic" operation form "RR"
        (scalar_parameters form ["d";"m"])
        (call "exec_alu_reg_rm"
          [id ("ALU_" ^ operation); reference ~rex:form.rex "d";
           call "RM_reg" [reference ~rex:form.rex "m"]; int form.width])
    ) (scalar_forms [64;32;16;8])
  ) ["ADD"; "ADC"; "SUB"; "SBB"; "CMP"; "AND"; "OR"; "XOR"]

(* INC/DEC's upstream helpers take a resolved operand and return its result
   while changing flags. The binding supplies the architectural register
   read/write surrounding that body; it supplies no arithmetic expression.
   Evaluation order captures the input before any flag or register write. *)
let unary =
  List.concat_map (fun operation ->
    List.map (fun form ->
      scalar_entry ~family:"arithmetic" operation form "R"
        (scalar_parameters form ["d"])
        (scalar_write form "d"
          (call ("exec_" ^ String.lowercase_ascii operation)
            [scalar_read form "d"]))
    ) (scalar_forms [64;32;16;8])
  ) ["INC"; "DEC"]

(* One-operand multiplication has implicit outputs: AX for a byte operand,
   otherwise DX:AX, EDX:EAX or RDX:RAX. Only the encoded source is variable.
   The original body supplies both the output widths and writes.
   Do not generalize the implicit registers to arbitrary HOL components. *)
let multiply =
  List.concat_map (fun (operation, source) ->
    List.map (fun form ->
      scalar_entry ~family:"arithmetic" operation form "R"
        (scalar_parameters form ["m"])
        (call source [int form.width; scalar_read form "m"])
    ) (scalar_forms [64;32;16;8])
  ) ["MUL", "exec_mul"; "IMUL1", "exec_imul_1"]

(* These selectors choose the original group-3 register paths. The upstream
   body supplies NOT's bitwise complement and NEG's subtraction/flag updates;
   unreachable TEST-immediate/MUL/DIV paths are not exported by these calls.
   Bytes use the actual F6 byte dispatcher; wider forms use F7's dispatcher,
   whose declaration permits only 16/32/64. *)
let group3 =
  List.concat_map (fun (operation, selector) ->
    List.map (fun form ->
      let arguments = [int selector; call "RM_reg"
        [reference ~rex:form.rex "d"]] in
      let body = if form.width = 8 then
        call "dispatch_group3_byte" arguments
        else call "dispatch_group3" (arguments @ [int form.width]) in
      scalar_entry ~family:"arithmetic" operation form "R"
        (scalar_parameters form ["d"]) body
    ) (scalar_forms [64;32;16;8])
  ) ["NOT", 2; "NEG", 3]

(* Group-2 execution resolves the destination as a register and receives
   an already acquired byte count. The source masks that count itself.
   The comparison passes val(count) MOD64 at width 64, otherwise MOD32.
   Every count byte remains variable, including zero and excessive counts.
   A 32-bit zero-count write still clears the register's upper half.
   Supplying a count does not claim decoding or a CL register read.
   The narrow RCL/RCR differences are proved as exact relations and
   counterexamples, not hidden by count restrictions or translator repairs. *)
let shifts =
  List.concat_map (fun (operation, selector) ->
    List.map (fun form ->
      scalar_entry ~family:"shift" operation form "RI"
        (scalar_parameters form ["d"] @ ["count",word 8])
        (call "exec_shift_rm"
          [int selector; call "RM_reg" [reference ~rex:form.rex "d"];
           id "count"; int form.width])
    ) (scalar_forms [64;32;16;8])
  ) ["ROL", 0; "ROR", 1; "RCL", 2; "RCR", 3;
     "SHL", 4; "SHR", 5; "SAR", 7]

(* Double shifts return the new destination while updating source flags.
   Read both original operands before invoking that helper, then write its
   result. There is no byte form. No distinct-register condition, restricted
   count domain or replacement math is supplied. *)
let double_shifts =
  List.concat_map (fun operation ->
    List.map (fun form ->
      scalar_entry ~family:"shift" operation form "RRI"
        (scalar_parameters form ["d";"m"] @ ["count",word 8])
        (scalar_write form "d"
          (call ("exec_" ^ String.lowercase_ascii operation) [
            int form.width; scalar_read form "d";
            scalar_read form "m"; id "count"]))
    ) (scalar_forms [64;32;16])
  ) ["SHLD"; "SHRD"]

(* Register-direct VEX inputs still go through the upstream operand decoder.
   ModR/M supplies mod=11 and the low register bits; the prefix supplies the
   high bits. The fetched byte is an explicit supplied-input boundary. *)
let bit name index = mk_exp (vector_access (id name) (int index))

let modrm_field field m =
  mk_exp (E_vector_append (bit_literal 2 3,
    mk_exp (E_vector_append (field, slice (id m) 2 0))))

let modrm d m = modrm_field (slice (id d) 2 0) m

(* These scalar encodings use the original ModR/M helper and its caller
   body. The input boundary removes fetch(1) inside fetch_modrm, not the
   helper's decoding or the caller's arithmetic. Each selected numeric
   opcode has exactly one retained helper call.

   0F AF is the two-operand truncated IMUL: ModR/M.reg is both the first
   input and destination. It compares with HOL IMUL3 D (D,M), not three
   independently encoded registers. MULX has independent high/low outputs
   and implicit RDX input; its original low-then-high writes retain aliases. *)
let legacy_prefix form d m =
  let extension name =
    if form.register_bits = 4 then bit name 3 else bit_literal 1 0 in
  mk_exp (E_struct_update (call "default_prefixes" [unit],
    List.map (fun (name,value) -> mk_fexp (mk_id name) value) [
      "has_opsize",bool (form.width = 16);
      "has_rex",bool form.rex; "rex_w",bool (form.width = 64);
      "rex_r",extension d; "rex_b",extension m
    ]))

let truncated_multiply =
  let lift = input_lift ~fixed_arguments:["op",175] ~through:"fetch_modrm"
    "dispatch_2byte_gpr" "fetch" in
  List.map (fun form ->
    make ~family:"arithmetic" ~input_lifts:[lift]
      (scalar_name "IMUL" form "RR") (scalar_parameters form ["d";"m"])
      (call_lifted lift [legacy_prefix form "d" "m"] (modrm "d" "m")),
    true
  ) (scalar_forms [64;32;16])

(* Some ModR/M.reg fields select an operation rather than a destination.
   This constructs that three-bit encoding field; the upstream decoder
   still extracts and checks it. The r/m source remains variable. *)
let modrm_opcode operation m = modrm_field (bit_literal 3 operation) m

let vex_prefix ?(w = false) ?(opcode_extension = false) width d vvvv m =
  mk_exp (E_struct_update (call "default_prefixes" [unit],
    List.map (fun (name, value) -> mk_fexp (mk_id name) value) [
      "has_opsize", bool true; "has_rex", bool true;
      "vex_present", bool true; "vex_l", bool (width = 256);
      "vex_w", bool w;
      "rex_r", (if opcode_extension then bit_literal 1 0 else bit d 3);
      "rex_b", bit m 3; "vex_vvvv", vvvv
    ]))

(* MULX selects width 32 or 64, L=0 and mandatory F2. The real prefix decoder
   copies W to both vex_w and rex_w, so retain both fields. Its checked
   caller still enforces BMI2 availability; assumptions below state the
   selected processor configuration instead of removing that check. *)
let multiply_extended =
  let lift = input_lift ~fixed_arguments:["op",246] ~through:"fetch_modrm"
    "dispatch_vex_0f38_arith" "fetch" in
  List.map (fun form ->
    let prefix = mk_exp (E_struct_update
      (vex_prefix ~w:(form.width = 64) 128 "hi" (unsigned "lo") "m",
       List.map (fun (name,value) -> mk_fexp (mk_id name) value) [
         "rex_w",bool (form.width = 64);
         "has_opsize",bool false; "has_repne",bool true
       ])) in
    make ~family:"arithmetic" ~input_lifts:[lift]
      (scalar_name "MULX" form "RRR")
      (scalar_parameters form ["hi";"lo";"m"])
      (call_lifted lift [prefix] (modrm "hi" "m")),
    true
  ) (scalar_forms [64;32])

(* ADCX/ADOX and TEST live inside original opcode dispatchers. These nine
   descriptors select their legal forms without inventing execution helpers
   or supplying arithmetic. Entry derives their supplied-input caller and
   rechecks it against the upstream declarations before translation.

   Its acquired call supplies selected fetched information. For ADX the
   third opcode is fixed to F6, while the original fetch_modrm still decodes
   its supplied byte. For TEST scan_prefixes supplies Prefixes and opcode;
   prefix/opcode byte acquisition is excluded, not the selected TEST body.
   The prefix input precedes the ModR/M input in the derived parent.
   The fixed choices and both original call spans must remain in evidence. *)
type acquired_scalar_form = {
  name : string;
  form : scalar_form;
  parameters : (string * typ) list;
  source_function : string;
  fixed_arguments : (string * int) list;
  acquired_callee : string;
  fixed_binding : string * int;
  retained_arguments : untyped_exp list;
  acquired_inputs : untyped_exp list;
  input : untyped_exp;
  features : (string * bool) list;
}

let acquired_scalar_forms =
  List.concat_map (fun operation ->
    List.map (fun form ->
      let prefix = mk_exp (E_struct_update
        (legacy_prefix form "d" "m",
         List.map (fun (name,value) -> mk_fexp (mk_id name) value) [
           "has_opsize",bool (operation = "ADCX");
           "has_rep",bool (operation = "ADOX")
         ])) in
      {name=scalar_name operation form "RR"; form;
       parameters=scalar_parameters form ["d";"m"];
       source_function="dispatch_opcode_2byte";
       fixed_arguments=["opcode",56];
       acquired_callee="fetch"; fixed_binding="opcode3",246;
       retained_arguments=[prefix]; acquired_inputs=[];
       input=modrm "d" "m"; features=["has_adx",true]}
    ) (scalar_forms [64;32])
  ) ["ADCX";"ADOX"] @
  List.map (fun form ->
    {name=scalar_name "TEST" form "RR"; form;
     parameters=scalar_parameters form ["d";"m"];
     source_function="decode_execute"; fixed_arguments=[];
     acquired_callee="scan_prefixes";
     fixed_binding="opcode",(if form.width = 8 then 132 else 133);
     retained_arguments=[unit];
     acquired_inputs=[legacy_prefix form "d" "m"];
     input=modrm "d" "m"; features=[]}
  ) (scalar_forms [64;32;16;8])

let acquired_selections =
  List.map (fun descriptor ->
    let lift = input_lift ~fixed_arguments:descriptor.fixed_arguments
      ~through:"fetch_modrm" ~acquired:{
        callee=descriptor.acquired_callee; fixed_binding=descriptor.fixed_binding}
      descriptor.source_function "fetch" in
    make ~family:"arithmetic" ~input_lifts:[lift] descriptor.name
      descriptor.parameters
      (call_lifted ~acquired_inputs:descriptor.acquired_inputs lift
        descriptor.retained_arguments descriptor.input),
    true
  ) acquired_scalar_forms

let arithmetic_selections = alu @ unary @ multiply @ group3 @
  truncated_multiply @ multiply_extended @ acquired_selections
let arithmetic = List.map fst arithmetic_selections

let vector_binary =
  let lift = input_lift "vex_exec_binop" "fetch" in
  List.concat_map (fun width ->
    List.map (fun (operation, element, source_operation) ->
      make ~family:"vector" ~input_lifts:[lift]
        (Printf.sprintf "X86_%s%d_RRR" operation width)
        ["d", word 4; "n", word 4; "m", word 4]
        (call_lifted lift
          [id source_operation; int element;
           (* The qword variable-shift encoding selects VEX.W=1; other
              listed forms use W=0 or ignore it. Upstream's decode_vex3
              also copies W into rex_w, which vex_exec_binop does not
              read, so this prefix leaves rex_w false. *)
           vex_prefix ~w:(operation = "VPSRLVQ") width "d" (unsigned "n") "m"]
          (modrm "d" "m"))
    ) ["VPADDB", 8, "PB_Add"; "VPADDW", 16, "PB_Add";
       "VPADDD", 32, "PB_Add"; "VPADDQ", 64, "PB_Add";
       "VPSUBB", 8, "PB_Sub"; "VPSUBW", 16, "PB_Sub";
       "VPSUBD", 32, "PB_Sub"; "VPSUBQ", 64, "PB_Sub";
       (* Match the upstream dispatch's element sizes, including 32-bit
          lanes for whole-vector logic. The calculations stay in Sail. *)
       "VPAND", 32, "PB_And"; "VPANDN", 32, "PB_Andn";
       "VPOR", 32, "PB_Or"; "VPXOR", 32, "PB_Xor";
       "VPMULLW", 16, "PB_MulLow"; "VPMULLD", 32, "PB_MulLow";
       "VPMULHW", 16, "PB_MulHighS"; "VPMULHUW", 16, "PB_MulHighU";
       "VPMULHRSW", 16, "PB_MulHRS"; "VPMULDQ", 64, "PB_Pmuldq";
       "VPMADDWD", 32, "PB_Pmaddwd"; "VPMADDUBSW", 16, "PB_Pmaddubsw";
       "VPCMPGTW", 16, "PB_CmpGt"; "VPCMPGTD", 32, "PB_CmpGt";
       "VPSLLVD", 32, "PB_Sll"; "VPSRLVD", 32, "PB_Srl";
       "VPSRLVQ", 64, "PB_Srl"]
  ) [256; 128]

(* Two-operand VEX forms reserve vvvv rather than selecting a third source.
   The upstream Prefixes record stores the decoded (inverted) field, so its
   reserved encoding is represented by zero. Each original body still
   checks that field and decodes the supplied ModR/M byte. Widening reads
   only the required low portion of an XMM source; it does not read a YMM
   source merely because the destination is 256 bits. *)
let vector_unary =
  let absolute = input_lift "vex_exec_unop" "fetch" in
  let widen = input_lift "vex_exec_widen" "fetch" in
  List.concat_map (fun width ->
    List.map (fun (operation, lift, arguments) ->
      make ~family:"vector" ~input_lifts:[lift]
        (Printf.sprintf "X86_%s%d_RR" operation width)
        ["d", word 4; "m", word 4]
        (call_lifted lift
          (arguments @ [vex_prefix width "d" (int 0) "m"])
          (modrm "d" "m"))
    ) ["VPABSD", absolute, [id "PU_Abs"; int 32];
       "VPMOVSXBD", widen, [id "PW_SignExtend"; int 8; int 32];
       "VPMOVZXBD", widen, [id "PW_ZeroExtend"; int 8; int 32];
       "VPMOVZXBW", widen, [id "PW_ZeroExtend"; int 8; int 16]]
  ) [256; 128]

let vector_pack =
  let lift = input_lift "vex_exec_pack" "fetch" in
  List.map (fun width ->
    make ~family:"vector" ~input_lifts:[lift]
      (Printf.sprintf "X86_VPACKUSWB%d_RRR" width)
      ["d", word 4; "n", word 4; "m", word 4]
      (call_lifted lift
        [id "PN_SatSU"; int 16; int 8;
         vex_prefix width "d" (unsigned "n") "m"]
        (modrm "d" "m"))
  ) [256; 128]

(* VPTEST is a flags-only instruction inside an opcode dispatcher rather
   than a standalone execution helper. Select its checked numeric opcode,
   then supply the original fetch(1) input. Both vectors remain unchanged.
   Reserved decoded vvvv=0 and the mandatory 66 prefix remain source checks;
   only the instruction-byte acquisition is outside the core relation. *)
let vector_test =
  let lift = input_lift ~fixed_arguments:["op", 23]
    "dispatch_vex_0f38_arith" "fetch" in
  List.map (fun width ->
    make ~family:"vector" ~input_lifts:[lift]
      (Printf.sprintf "X86_VPTEST%d_RR" width)
      ["n", word 4; "m", word 4]
      (call_lifted lift
        [vex_prefix width "n" (int 0) "m"] (modrm "n" "m"))
  ) [256; 128]

(* Immediate shifts have two original fetches: ModR/M first, then imm8,
   in model/insn_vex_int.sail:150-184. Select op=113/114/115, the original
   0x71/0x72/0x73 dispatcher groups. Supplied-input slot0 is ModR/M and
   slot1 is imm8; these slots follow the two original call spans.
   The original dispatcher keeps both decoding steps and the calculation.
   Its group number is an opcode choice, not a shift formula. ModR/M.reg
   selects the operation, r/m selects the source and decoded vvvv selects
   the destination. All byte counts remain variable, including 255; Sail
   handles lane-width cutoffs and VPSRLDQ's independent 128-bit lanes. *)
let vector_immediate =
  List.concat_map (fun (operation, opcode, selector) ->
    let lift = input_lift ~fixed_arguments:["op", opcode] ~expected_inputs:2
      "dispatch_vex_0f_int" "fetch" in
    List.map (fun width ->
      make ~family:"vector" ~input_lifts:[lift]
        (Printf.sprintf "X86_%s%d_RRI" operation width)
        ["d", word 4; "m", word 4; "count", word 8]
        (call_lifted_inputs lift
          [vex_prefix ~opcode_extension:true width "d" (unsigned "d") "m"]
          [modrm_opcode selector "m"; id "count"])
    ) [256;128]
  ) ["VPSRLW",113,2; "VPSRAW",113,4; "VPSLLW",113,6;
     "VPSRLD",114,2; "VPSRAD",114,4; "VPSLLD",114,6;
     "VPSRLQ",115,2; "VPSLLQ",115,6; "VPSRLDQ",115,3]

let vector = vector_binary @ vector_unary @ vector_pack @ vector_test @
  vector_immediate

let shift_selections = shifts @ double_shifts
let shift = List.map fst shift_selections

let assumptions entries =
  let has name = List.exists (fun (entry : Entry.t) -> entry.name = name) entries in
  let mode_dependent = List.filter_map (fun ((entry : Entry.t), required) ->
    if required then Some entry.name else None)
    (arithmetic_selections @ shift_selections) in
  let acquired = List.filter (fun (form : acquired_scalar_form) -> has form.name)
    acquired_scalar_forms in
  (if List.exists has mode_dependent || acquired <> [] ||
      List.exists (fun (entry : Entry.t) -> entry.family = "vector") entries
   then [Initial_enum ("cur_mode","LongMode")] else []) @
  List.map (fun (name,value) -> Initial_bool (name,value))
    (List.sort_uniq compare
      ((if List.exists (fun ((entry : Entry.t), _) -> has entry.name)
          multiply_extended then ["has_bmi2",true] else []) @
       List.concat_map (fun form -> form.features) acquired))

let entries = arithmetic @ vector @ shift
let family_roots =
  ["arithmetic", List.map (fun (entry : Entry.t) -> entry.name) arithmetic;
   "vector", List.map (fun (entry : Entry.t) -> entry.name) vector;
   "shift", List.map (fun (entry : Entry.t) -> entry.name) shift]
let contracts =
  ["read_simd", true; "write_simd", false]
let cuts = List.map fst contracts

(* The shina outputs keep their established x86-FAMILY stems and X86_
   root names; existing proofs and CI records refer to them. *)
let source = {
  model = "shina";
  stem = (fun family -> "x86-" ^ family);
  qualified_names = false; extended_evaluation = false;
  entries; family_roots; assumptions; contracts;
  bindings = [Gpr_bank "GPR"; Flag_bits ["CF"; "PF"; "AF"; "ZF"; "SF"; "OF"];
              Simd_access];
  (* The translator checks each GPR, flag and SIMD access as it reaches it. *)
  validate = (fun _ -> ());
}
