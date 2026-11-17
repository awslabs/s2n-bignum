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

(* Moves, exchanges, no-operation forms and single-flag instructions.

   All of these live in decode_execute or dispatch_2byte_gpr, so each
   binding selects the original opcode branch and supplies only the
   instruction bytes after the prefixes: the opcode is fixed through the
   acquired scan_prefixes result, the prefix record is a supplied value, and
   a ModR/M byte is supplied where the branch fetches one. For TEST,
   fetch_modrm still decodes that byte; the same holds here. A branch that
   fetches nothing after the opcode (CLC, STC, CMC, CLD, STD, NOP) is lifted
   with zero supplied inputs: its whole body remains. *)
let default_prefix = call "default_prefixes" [unit]

let decoded_selection ~family ?(through = Some "fetch_modrm") name parameters
    opcode prefix inputs =
  let lift = input_lift ~expected_inputs:(List.length inputs) ?through:through
    ~acquired:{callee="scan_prefixes"; fixed_binding="opcode",opcode}
    "decode_execute" "fetch" in
  make ~family ~input_lifts:[lift] name parameters
    (call_lifted_inputs ~acquired_inputs:[prefix] lift [unit] inputs),
  true

(* The no-fetch bodies, where no ModR/M byte is supplied. *)
let flag_selection name opcode =
  let lift = input_lift ~expected_inputs:0
    ~acquired:{callee="scan_prefixes"; fixed_binding="opcode",opcode}
    "decode_execute" "fetch" in
  make ~family:"move" ~input_lifts:[lift] name []
    (call_lifted_inputs ~acquired_inputs:[default_prefix] lift [unit] []),
  true

let move_flags =
  List.map (fun (name, opcode) -> flag_selection name opcode)
    ["X86_CLC", 248; "X86_STC", 249; "X86_CMC", 245;
     "X86_CLD", 252; "X86_STD", 253; "X86_NOP", 144]

(* ENDBR64 is F3 0F 1E FA. Every 0F 18..1E opcode shares one branch of
   dispatch_2byte_gpr that consumes its ModR/M byte and does nothing else;
   the entry selects opcode 0x1E and supplies the byte 0xFA, which is
   register-direct (mod=3) with fixed fields. NOP_N is 0F 1F /r, selected
   as opcode 0x1F, with a register-direct operand. *)
let move_nops =
  let endbr =
    let lift = input_lift ~fixed_arguments:["op",30] "dispatch_2byte_gpr" "fetch" in
    make ~family:"move" ~input_lifts:[lift] "X86_ENDBR64" []
      (call_lifted lift [mk_exp (E_struct_update (default_prefix,
         [mk_fexp (mk_id "has_rep") (bool true)]))]
         (bit_literal 8 0xFA)),
    true in
  let nop_n =
    let lift = input_lift ~fixed_arguments:["op",31] "dispatch_2byte_gpr" "fetch" in
    make ~family:"move" ~input_lifts:[lift] "X86_NOP_N" ["m", word 4]
      (call_lifted lift [mk_exp (E_struct_update (default_prefix,
         [mk_fexp (mk_id "has_rex") (bool true);
          mk_fexp (mk_id "rex_b") (bit "m" 3)]))]
         (mk_exp (E_vector_append (bit_literal 5 0b11000, slice (id "m") 2 0)))),
    true in
  [endbr; nop_n]

(* Register-to-register MOV and XCHG use ModR/M.reg as the second operand
   and ModR/M.r/m as the first, in the same encoding as TEST: MOV r/m, r is
   89 (88 for bytes), XCHG r/m, r is 87 (86 for bytes). *)
let move_exchange =
  List.concat_map (fun (operation, byte_opcode, wide_opcode) ->
    List.map (fun form ->
      decoded_selection ~family:"move" (scalar_name operation form "RR")
        (scalar_parameters form ["d";"m"])
        (if form.width = 8 then byte_opcode else wide_opcode)
        (legacy_prefix form "d" "m") [modrm "d" "m"]
    ) (scalar_forms [64;32;16;8])
  ) ["MOV", 136, 137; "XCHG", 134, 135]

let move_selections = move_flags @ move_nops @ move_exchange
let move = List.map fst move_selections

(* Condition-code, extension and byte-swap forms of dispatch_2byte_gpr.

   Each root fixes the opcode byte, so the condition code (CMOVcc 0F 40+cc,
   SETcc 0F 90+cc) or the bswap register (0F C8+r) is a separate root, as
   the opcode is a dispatcher argument and not a parameter. The branch
   decodes the supplied ModR/M byte and keeps its operand access. The
   condition names are s2n-bignum's Condition_ constructors, in the order
   of decode_condition. *)
let conditions =
  ["O"; "NO"; "B"; "NB"; "Z"; "NZ"; "BE"; "NBE";
   "S"; "NS"; "P"; "NP"; "L"; "NL"; "LE"; "NLE"]

let two_byte_selection ~family ?through name parameters opcode prefix inputs =
  let lift = input_lift ~fixed_arguments:["op",opcode] ?through
    ~expected_inputs:(List.length inputs) "dispatch_2byte_gpr" "fetch" in
  make ~family ~input_lifts:[lift] name parameters
    (call_lifted_inputs lift [prefix] inputs),
  true

let prefix_fields fields =
  mk_exp (E_struct_update (default_prefix,
    List.map (fun (name,value) -> mk_fexp (mk_id name) value) fields))

(* Register-direct ModR/M with reg field zero and a variable r/m field. *)
let modrm_rm_only m =
  mk_exp (E_vector_append (bit_literal 5 0b11000, slice (id m) 2 0))

let select_conditional =
  List.concat (List.mapi (fun cc condition ->
    List.map (fun form ->
      two_byte_selection ~family:"select" ~through:"fetch_modrm"
        (scalar_name ("CMOV" ^ condition) form "RR")
        (scalar_parameters form ["d";"m"]) (64 + cc)
        (legacy_prefix form "d" "m") [modrm "d" "m"]
    ) (scalar_forms [64;32])) conditions)

let select_set =
  List.concat (List.mapi (fun cc condition ->
    List.map (fun form ->
      let extension = if form.register_bits = 4 then bit "m" 3
        else bit_literal 1 0 in
      two_byte_selection ~family:"select"
        (scalar_name ("SET" ^ condition) form "R")
        (scalar_parameters form ["m"]) (144 + cc)
        (prefix_fields ["has_rex",bool form.rex; "rex_b",extension])
        [modrm_rm_only "m"]
    ) (scalar_forms [8])) conditions)

(* MOVZX/MOVSX: the source is a byte or word register, the destination has
   the operand size of the prefix. A byte source without REX uses the
   three-bit legacy encoding for both operands. *)
let extension_forms =
  List.concat_map (fun (source, source_bits, rex) ->
    List.map (fun destination ->
      source, destination,
      {width = destination; register_bits = source_bits; rex}
    ) (if rex then [64;32] else [32])
  ) [8, 4, true; 8, 3, false; 16, 4, true]

let extension_name operation source destination form =
  Printf.sprintf "X86_%s%d_%d%s_RR" operation destination source
    (if form.rex then "" else "_LEGACY")

let select_extend =
  List.concat_map (fun (operation, byte_opcode, word_opcode) ->
    List.map (fun (source, destination, form) ->
      two_byte_selection ~family:"select" ~through:"fetch_modrm"
        (extension_name operation source destination form)
        (scalar_parameters form ["d";"m"])
        (if source = 8 then byte_opcode else word_opcode)
        (legacy_prefix form "d" "m") [modrm "d" "m"]
    ) extension_forms
  ) ["MOVZX", 182, 183; "MOVSX", 190, 191]

(* MOVSXD (63 /r) sign-extends a 32-bit register to 64 bits with REX.W and
   copies it to a 32-bit register without. It lives in decode_execute, which
   also holds ARPL for the other processor modes under the same opcode. *)
let select_movsxd =
  List.map (fun destination ->
    let form = {width = destination; register_bits = 4; rex = true} in
    let name = Printf.sprintf "X86_MOVSXD%d_32_RR" destination in
    (* The branch calls fetch_modrm once per processor mode, in source
       order LongMode first. The lift replaces the LongMode call; the others
       stay original code, dead under the cur_mode=LongMode assumption. *)
    let lift = input_lift ~selected_call:0 ~through:"fetch_modrm"
      ~acquired:{callee="scan_prefixes"; fixed_binding="opcode",99}
      "decode_execute" "fetch" in
    make ~family:"select" ~input_lifts:[lift] name
      (scalar_parameters form ["d";"m"])
      (call_lifted_inputs ~acquired_inputs:[legacy_prefix form "d" "m"] lift
         [unit] [modrm "d" "m"]),
    true
  ) [64;32]

(* BSWAP names its register in the low three opcode bits; REX.B is the
   one-bit parameter. *)
let select_bswap =
  List.concat_map (fun width ->
    List.init 8 (fun low ->
      two_byte_selection ~family:"select"
        (Printf.sprintf "X86_BSWAP%d_R%d" width low)
        ["b", word 1] (200 + low)
        (prefix_fields ["has_rex",bool true; "rex_w",bool (width = 64);
                        "rex_b",id "b"]) []
    )) [64;32]

let select_selections = select_conditional @ select_set @ select_extend @
  select_movsxd @ select_bswap
let select = List.map fst select_selections

(* Bit test and modify, register by register: BT 0F A3, BTS 0F AB,
   BTR 0F B3, BTC 0F BB. ModR/M.reg holds the bit offset and r/m the
   tested register. *)
let bit_tests =
  List.concat_map (fun (operation, opcode) ->
    List.map (fun form ->
      two_byte_selection ~family:"bit" ~through:"fetch_modrm" (scalar_name operation form "RR")
        (scalar_parameters form ["d";"m"]) opcode
        (legacy_prefix form "d" "m") [modrm "d" "m"]
    ) (scalar_forms [64;32])
  ) ["BT", 163; "BTS", 171; "BTR", 179; "BTC", 187]

let bit_selections = bit_tests
let bit_family = List.map fst bit_selections

(* Bit scans and counts on registers: BSF 0F BC, BSR 0F BD, TZCNT F3 0F BC,
   LZCNT F3 0F BD and POPCNT F3 0F B8, at 64, 32 and 16 bits. ModR/M.reg is
   the destination and r/m the source. The F3 forms differ from BSF by the
   repeat prefix and by a feature flag that the body tests, so the
   assumptions below say that the processor has BMI1, LZCNT and POPCNT.
   BSR is 0F BD without the repeat prefix. *)
let count_instructions =
  ["BSF", 188, false, None; "BSR", 189, false, None;
   "TZCNT", 188, true, Some "has_bmi1"; "LZCNT", 189, true, Some "has_lzcnt";
   "POPCNT", 184, true, Some "has_popcnt"]

let count_selections =
  List.concat_map (fun (operation, opcode, repeat, feature) ->
    List.map (fun form ->
      let prefix = mk_exp (E_struct_update (legacy_prefix form "d" "m",
        [mk_fexp (mk_id "has_rep") (bool repeat)])) in
      fst (two_byte_selection ~family:"count" ~through:"fetch_modrm"
        (scalar_name operation form "RR")
        (scalar_parameters form ["d";"m"]) opcode prefix [modrm "d" "m"]),
      feature
    ) (scalar_forms [64;32;16])
  ) count_instructions
let count_family = List.map fst count_selections

(* PEXT is VEX.F3.0F38 F5 /r with VEX.W selecting 32 or 64 bits: ModR/M.reg
   is the destination, VEX.vvvv the source and ModR/M.r/m the mask. The
   dispatcher serves BZHI (no prefix), PDEP (F2) and PEXT (F3) from one
   opcode, so the repeat prefix selects PEXT. As for MULX, the real prefix
   decoder copies W to both vex_w and rex_w. *)
let pext_extended =
  let lift = input_lift ~fixed_arguments:["op",245] ~through:"fetch_modrm"
    "dispatch_vex_0f38_arith" "fetch" in
  List.map (fun form ->
    let prefix = mk_exp (E_struct_update
      (vex_prefix ~w:(form.width = 64) 128 "d" (unsigned "n") "m",
       List.map (fun (name,value) -> mk_fexp (mk_id name) value) [
         "rex_w",bool (form.width = 64);
         "has_opsize",bool false; "has_rep",bool true
       ])) in
    make ~family:"pext" ~input_lifts:[lift]
      (scalar_name "PEXT" form "RRR")
      (scalar_parameters form ["d";"n";"m"])
      (call_lifted lift [prefix] (modrm "d" "m")),
    true
  ) (scalar_forms [64;32])
let pext_family = List.map fst pext_extended

(* AVX2 data movement, shuffles, blends, inserts, extracts and mask
   extracts, in register-direct form. Each entry selects one upstream
   body, either through a helper such as vex_exec_binop or by fixing the
   opcode of a dispatcher, and supplies only the fetched ModR/M and
   immediate bytes. The mandatory prefix (66, F3 or none) is part of the
   supplied prefix record; the bodies check it themselves where they read
   it. Operand registers are four-bit numbers: ModR/M.reg and r/m supply
   the low three bits and the prefix supplies the fourth. A general
   register operand is such a number too; its width follows VEX.W. *)
let avx2_prefix ?(w = false) ?(mp = `P66) ?opcode_extension width d vvvv m =
  mk_exp (E_struct_update
    (vex_prefix ~w ?opcode_extension width d vvvv m,
     List.map (fun (name, value) -> mk_fexp (mk_id name) value) [
       "has_opsize", bool (mp = `P66); "has_rep", bool (mp = `F3)]))

let avx2_name instruction width variant operands =
  Printf.sprintf "X86_%s%d%s_%s" instruction width variant operands

let avx2_registers n =
  List.filteri (fun index _ -> index < n) ["d", word 4; "n", word 4; "m", word 4]

(* Three-register forms through a helper whose only fetch is ModR/M. *)
let avx2_helper =
  let binop = input_lift "vex_exec_binop" "fetch" in
  let unpack = input_lift "vex_exec_unpack" "fetch" in
  List.concat_map (fun width ->
    List.map (fun (instruction, lift, arguments) ->
      make ~family:"avx2" ~input_lifts:[lift]
        (avx2_name instruction width "" "RRR") (avx2_registers 3)
        (call_lifted lift
          (arguments @ [avx2_prefix width "d" (unsigned "n") "m"])
          (modrm "d" "m"))
    ) ["VPSHUFB", binop, [id "PB_Pshufb"; int 128];
       "VPCMPEQW", binop, [id "PB_CmpEq"; int 16];
       "VPUNPCKLQDQ", unpack, [int 64; int 0];
       "VPUNPCKHQDQ", unpack, [int 64; int 64]]
  ) [256; 128]

(* Two-register forms: broadcast reads the low part of an XMM source. *)
let avx2_broadcast =
  let lift = input_lift "vex_exec_broadcast" "fetch" in
  List.concat_map (fun width ->
    List.map (fun (instruction, element) ->
      make ~family:"avx2" ~input_lifts:[lift]
        (avx2_name instruction width "" "RR") ["d", word 4; "m", word 4]
        (call_lifted lift
          [int element; avx2_prefix width "d" (int 0) "m"] (modrm "d" "m"))
    ) ["VPBROADCASTD", 32; "VPBROADCASTQ", 64; "VPBROADCASTW", 16]
  ) [256; 128]

(* Blends with an immediate: ModR/M then imm8 are the two fetches. *)
let avx2_blend =
  let blend = input_lift ~expected_inputs:2 "vex_exec_blend" "fetch" in
  let lanes = input_lift ~expected_inputs:2 "vex_exec_lane_bin_imm" "fetch" in
  List.concat_map (fun width ->
    List.map (fun (instruction, lift, arguments) ->
      make ~family:"avx2" ~input_lifts:[lift]
        (avx2_name instruction width "" "RRRI")
        (avx2_registers 3 @ ["imm", word 8])
        (call_lifted_inputs lift
          (arguments @ [avx2_prefix width "d" (unsigned "n") "m"])
          [modrm "d" "m"; id "imm"])
    ) ["VPBLENDD", blend, [int 32];
       "VPBLENDW", lanes, [id "VLBI_BlendW"];
       "VPCLMULQDQ", lanes, [id "VLBI_Pclmulqdq"]]
  ) [256; 128]

(* Opcode-selected bodies of the 0F3A and 0F38 maps. The 0F3A bodies
   take ModR/M and imm8 through vex_fetch_xrm_imm or two direct fetches. *)
let avx2_opcode =
  let imm_helper opcode = input_lift ~fixed_arguments:["opcode", opcode]
    ~expected_inputs:2 ~through:"vex_fetch_xrm_imm" "dispatch_vex_0f3a" "fetch" in
  let permq = imm_helper 0
  and insert = imm_helper 56 and extract = imm_helper 57
  and perm2 = imm_helper 70 and blendv = imm_helper 76 in
  let mask_byte k =
    mk_exp (E_vector_append (id k, bit_literal 4 0)) in
  let permd = input_lift ~fixed_arguments:["op", 54]
    "dispatch_vex_0f38_arith" "fetch" in
  let on_3a lift prefix inputs =
    call_lifted_inputs lift [prefix] inputs in
  [make ~family:"avx2" ~input_lifts:[permq]
     (avx2_name "VPERMQ" 256 "" "RRI")
     ["d", word 4; "m", word 4; "imm", word 8]
     (on_3a permq (avx2_prefix ~w:true 256 "d" (int 0) "m")
        [modrm "d" "m"; id "imm"]);
   make ~family:"avx2" ~input_lifts:[insert]
     (avx2_name "VINSERTI128" 256 "" "RRRI")
     (avx2_registers 3 @ ["imm", word 8])
     (on_3a insert (avx2_prefix 256 "d" (unsigned "n") "m")
        [modrm "d" "m"; id "imm"]);
   (* The extract source is ModR/M.reg and the destination r/m. *)
   make ~family:"avx2" ~input_lifts:[extract]
     (avx2_name "VEXTRACTI128" 256 "" "RRI")
     ["m", word 4; "s", word 4; "imm", word 8]
     (on_3a extract (avx2_prefix 256 "s" (int 0) "m")
        [modrm "s" "m"; id "imm"]);
   make ~family:"avx2" ~input_lifts:[permd]
     (avx2_name "VPERMD" 256 "" "RRR") (avx2_registers 3)
     (call_lifted permd [avx2_prefix 256 "d" (unsigned "n") "m"]
        (modrm "d" "m"));
   (* Opcode 70 is VPERM2I128; the 0F3A branch for 6 and 70 is shared with
      VPERM2F128. *)
   make ~family:"avx2" ~input_lifts:[perm2]
     (avx2_name "VPERM2I128" 256 "" "RRRI")
     (avx2_registers 3 @ ["imm", word 8])
     (on_3a perm2 (avx2_prefix 256 "d" (unsigned "n") "m")
        [modrm "d" "m"; id "imm"]);
   (* VPBLENDVB takes its mask register from imm8[7:4]; the low four bits
      of imm8 are not used. *)
   make ~family:"avx2" ~input_lifts:[blendv]
     (avx2_name "VPBLENDVB" 256 "" "RRRR")
     (avx2_registers 3 @ ["k", word 4])
     (on_3a blendv (avx2_prefix 256 "d" (unsigned "n") "m")
        [modrm "d" "m"; mask_byte "k"]);
   make ~family:"avx2" ~input_lifts:[blendv]
     (avx2_name "VPBLENDVB" 128 "" "RRRR")
     (avx2_registers 3 @ ["k", word 4])
     (on_3a blendv (avx2_prefix 128 "d" (unsigned "n") "m")
        [modrm "d" "m"; mask_byte "k"])]

(* Moves, mask extracts and element transfers selected by opcode in the
   0F integer and floating-point maps and in 0F3A. A "store" form has the
   destination in ModR/M.r/m and the source in ModR/M.reg; its HOL
   arguments keep s2n-bignum's order, destination first. *)
let avx2_move =
  let int_map opcode = input_lift ~fixed_arguments:["op", opcode]
    "dispatch_vex_0f_int" "fetch" in
  let int_map_imm opcode = input_lift ~fixed_arguments:["op", opcode]
    ~expected_inputs:2 "dispatch_vex_0f_int" "fetch" in
  let fp_map opcode = input_lift ~fixed_arguments:["op", opcode]
    "dispatch_vex_0f_fp" "fetch" in
  let map_3a opcode = input_lift ~fixed_arguments:["opcode", opcode]
    ~expected_inputs:2 "dispatch_vex_0f3a" "fetch" in
  let two = ["d", word 4; "m", word 4] in
  let store = ["m", word 4; "s", word 4] in
  let with_imm parameters = parameters @ ["imm", word 8] in
  (* [reg] is the ModR/M.reg register, [rm] the r/m register. *)
  let move ?w ?mp ?(width = 128) lift name parameters reg rm =
    make ~family:"avx2" ~input_lifts:[lift] name parameters
      (call_lifted lift [avx2_prefix ?w ?mp width reg (int 0) rm]
         (modrm reg rm)) in
  List.concat_map (fun width ->
    List.concat_map (fun (instruction, mp, opcode_load, opcode_store) ->
      [move ~mp ~width (int_map opcode_load)
         (avx2_name instruction width "" "RR") two "d" "m";
       move ~mp ~width (int_map opcode_store)
         (avx2_name instruction width "_STORE" "RR") store "s" "m"]
    ) ["VMOVDQA", `P66, 111, 127; "VMOVDQU", `F3, 111, 127] @
    List.map (fun (instruction, opcode) ->
      move ~mp:`F3 ~width (fp_map opcode)
        (avx2_name instruction width "" "RR") two "d" "m"
    ) ["VMOVSLDUP", 18; "VMOVSHDUP", 22]
  ) [256; 128] @
  [move (int_map 110) (avx2_name "VMOVD" 128 "" "RR") two "d" "m";
   move (int_map 126) (avx2_name "VMOVD" 128 "_STORE" "RR") store "s" "m";
   move ~w:true (int_map 110) (avx2_name "VMOVQ" 128 "" "RR") two "d" "m";
   move ~w:true (int_map 126) (avx2_name "VMOVQ" 128 "_STORE" "RR") store "s" "m";
   move ~mp:`F3 (int_map 126) (avx2_name "VMOVQ" 128 "_F3" "RR") two "d" "m";
   move (int_map 214) (avx2_name "VMOVQ" 128 "_D6" "RR") store "s" "m"] @
  (* Element extracts and inserts take imm8 after ModR/M. *)
  (let extract lift name parameters ?w reg rm =
     make ~family:"avx2" ~input_lifts:[lift] name parameters
       (call_lifted_inputs lift [avx2_prefix ?w 128 reg (int 0) rm]
          [modrm reg rm; id "imm"]) in
   let insert lift name ?w () =
     make ~family:"avx2" ~input_lifts:[lift] name
       (with_imm ["d", word 4; "n", word 4; "m", word 4])
       (call_lifted_inputs lift
          [avx2_prefix ?w 128 "d" (unsigned "n") "m"]
          [modrm "d" "m"; id "imm"]) in
   List.map (fun width ->
     let lift = int_map_imm 112 in
     make ~family:"avx2" ~input_lifts:[lift]
       (avx2_name "VPSHUFD" width "" "RRI") (with_imm two)
       (call_lifted_inputs lift [avx2_prefix width "d" (int 0) "m"]
         [modrm "d" "m"; id "imm"])
   ) [256;128] @
   [extract (int_map_imm 197) (avx2_name "VPEXTRW" 128 "" "RRI")
      (with_imm two) "d" "m";
    insert (int_map_imm 196) (avx2_name "VPINSRW" 128 "" "RRRI") ();
    insert (map_3a 34) (avx2_name "VPINSRD" 128 "" "RRRI") ();
    insert ~w:true (map_3a 34) (avx2_name "VPINSRQ" 128 "" "RRRI") ()] @
   (* Mask extracts write a general register from ModR/M.reg. VMOVMSKPS is
      the no-prefix encoding. *)
   [move ~mp:`NP ~width:256 (fp_map 80)
      (avx2_name "VMOVMSKPS" 256 "" "RR") two "d" "m";
    move ~width:256 (int_map 215)
      (avx2_name "VPMOVMSKB" 256 "" "RR") two "d" "m"])

(* PMOVMSKB r32/r64, xmm (66 0F D7) is a legacy-encoded body of
   dispatch_2byte_sse_int. It reads the XMM register and writes a general
   register only, so no ZMM access arises. REX is present so that both
   register numbers have four bits. *)
let avx2_legacy_mask =
  let lift = input_lift ~fixed_arguments:["op", 215]
    "dispatch_2byte_sse_int" "fetch" in
  List.map (fun width ->
    let prefix = prefix_fields
      ["has_opsize", bool true; "has_rex", bool true;
       "rex_w", bool (width = 64); "rex_r", bit "d" 3; "rex_b", bit "m" 3] in
    make ~family:"avx2" ~input_lifts:[lift]
      (avx2_name "PMOVMSKB" width "" "RR") ["d", word 4; "m", word 4]
      (call_lifted lift [prefix] (modrm "d" "m"))
  ) [64; 32]

let avx2 = avx2_helper @ avx2_broadcast @ avx2_blend @ avx2_opcode @
  avx2_move @ avx2_legacy_mask

(* Legacy-encoded SSE integer instructions, VPEXTRD and VPEXTRQ, and
   VZEROUPPER, in register-direct form.

   A legacy SSE body writes the low 128 bits of a vector register and keeps
   bits 128 to 511 (`ZMM[xreg][127..0] = ...`), where a VEX body zeroes
   them (`write_simd`). Their register file is the raw ZMM bank (Zmm_bank),
   which the translator maps to s2n-bignum's `simdregisters`. VPEXTRD and
   VPEXTRQ read `ZMM[src]` directly; VZEROUPPER assigns `ZMM[i][511..128]`.
   The mandatory prefix 66, F3 or none is part of the supplied prefix
   record; the bodies check it themselves. The ModR/M byte and imm8 are
   supplied inputs, as for the AVX2 forms. The #UD, AES-NI and SSE4.1
   availability checks of `check_legacy_simd` are outside the selected
   bodies and are not compared. *)
let sse_prefix ?(w = false) ?(mp = `P66) reg rm =
  mk_exp (E_struct_update (default_prefix,
    List.map (fun (name, value) -> mk_fexp (mk_id name) value) [
      "has_opsize", bool (mp = `P66); "has_rep", bool (mp = `F3);
      "has_rex", bool true; "rex_w", bool w;
      "rex_r", reg; "rex_b", rm]))

let sse_name instruction variant operands =
  Printf.sprintf "X86_%s128%s_%s" instruction variant operands

let sse =
  let two = ["d", word 4; "m", word 4] in
  let store = ["m", word 4; "x", word 4] in
  let with_imm parameters = parameters @ ["imm", word 8] in
  let dispatch ?through ?(inputs = 1) function_name argument opcode =
    input_lift ~fixed_arguments:[argument, opcode] ~expected_inputs:inputs
      ?through function_name "fetch" in
  (* [reg] is the ModR/M.reg register, [rm] the r/m register. *)
  let move ?w ?mp lift name parameters reg rm =
    make ~family:"sse" ~input_lifts:[lift] name parameters
      (call_lifted lift [sse_prefix ?w ?mp (bit reg 3) (bit rm 3)]
         (modrm reg rm)) in
  let imm_form ?w lift name parameters reg rm =
    make ~family:"sse" ~input_lifts:[lift] name (with_imm parameters)
      (call_lifted_inputs lift [sse_prefix ?w (bit reg 3) (bit rm 3)]
         [modrm reg rm; id "imm"]) in
  let int_map ?through ?inputs opcode =
    dispatch ?through ?inputs "dispatch_2byte_sse_int" "op" opcode in
  let fp_map opcode = dispatch "dispatch_2byte_sse_fp" "op" opcode in
  (* Two-operand arithmetic and logic: sse_exec_binop retains the fetch. *)
  List.map (fun (instruction, opcode) ->
    move (int_map ~through:"sse_exec_binop" opcode)
      (sse_name instruction "" "RR") two "d" "m"
  ) ["PADDD", 254; "PADDQ", 212; "PAND", 219; "PXOR", 239] @
  List.map (fun (instruction, opcode) ->
    move (int_map opcode) (sse_name instruction "" "RR") two "d" "m"
  ) ["PCMPGTW", 101; "PCMPGTD", 102] @
  [move (dispatch "dispatch_3byte_38_sse_int" "opcode" 0)
     (sse_name "PSHUFB" "" "RR") two "d" "m";
   imm_form (int_map ~inputs:2 112) (sse_name "PSHUFD" "" "RRI") two "d" "m";
   imm_form (dispatch ~inputs:2 "dispatch_3byte_3a_sse_int" "opcode" 14)
     (sse_name "PBLENDW" "" "RRI") two "d" "m";
   imm_form (dispatch ~inputs:2 "dispatch_3byte_3a_sse_int" "opcode" 68)
     (sse_name "PCLMULQDQ" "" "RRI") two "d" "m";
   imm_form (dispatch ~inputs:2 "dispatch_3byte_3a_sse_int" "opcode" 34)
     (sse_name "PINSRD" "" "RRI") two "d" "m";
   (* REX.W selects the quadword form of the same opcode. *)
   imm_form ~w:true
     (dispatch ~inputs:2 "dispatch_3byte_3a_sse_int" "opcode" 34)
     (sse_name "PINSRQ" "" "RRI") two "d" "m"] @
  (* Shifts by an immediate: ModR/M.reg selects the operation, r/m the
     register, as for VPSRLW. *)
  List.map (fun (instruction, opcode, selector) ->
    let lift = int_map ~inputs:2 opcode in
    make ~family:"sse" ~input_lifts:[lift]
      (sse_name instruction "" "RI") ["d", word 4; "imm", word 8]
      (call_lifted_inputs lift
         [sse_prefix (bit_literal 1 0) (bit "d" 3)]
         [modrm_opcode selector "d"; id "imm"])
  ) ["PSRLW", 113, 2; "PSRAD", 114, 4;
     "PSLLDQ", 115, 7; "PSRLDQ", 115, 3] @
  (* Register moves: the load has the destination in ModR/M.reg, the
     store ("_STORE") in ModR/M.r/m. *)
  List.concat_map (fun (instruction, mp, load, store_opcode, fp) ->
    let lift opcode = if fp then fp_map opcode else int_map opcode in
    [move ~mp (lift load) (sse_name instruction "" "RR") two "d" "m";
     move ~mp (lift store_opcode) (sse_name instruction "_STORE" "RR")
       store "x" "m"]
  ) ["MOVAPS", `None, 40, 41, true; "MOVUPS", `None, 16, 17, true;
     "MOVDQA", `P66, 111, 127, false; "MOVDQU", `F3, 111, 127, false] @
  (* Transfers between a vector register and a general register or the
     vector register's low quadword. *)
  [move (int_map 110) (sse_name "MOVD" "" "RR") two "d" "m";
   move (int_map 126) (sse_name "MOVD" "_STORE" "RR") store "x" "m";
   move ~w:true (int_map 110) (sse_name "MOVQ" "" "RR") two "d" "m";
   move ~w:true (int_map 126) (sse_name "MOVQ" "_STORE" "RR") store "x" "m";
   move ~mp:`F3 (int_map 126) (sse_name "MOVQ" "_F3" "RR") two "d" "m"] @
  (* VEX-encoded: VPEXTRD and VPEXTRQ read ZMM[src] directly. The
     destination is ModR/M.r/m, the source ModR/M.reg. *)
  (let lift = dispatch ~inputs:2 "dispatch_vex_0f3a" "opcode" 22 in
   List.map (fun (instruction, w) ->
     make ~family:"sse" ~input_lifts:[lift]
       (sse_name instruction "" "RRI") (with_imm store)
       (call_lifted_inputs lift [avx2_prefix ~w 128 "x" (int 0) "m"]
          [modrm "x" "m"; id "imm"])
   ) ["VPEXTRD", false; "VPEXTRQ", true]) @
  (* VZEROUPPER is VEX.128 0F 77, selected by the opcode; it has no operand
     and fetches nothing after the opcode. *)
  (let lift = dispatch ~inputs:0 "dispatch_vex_0f_int" "op" 119 in
   [make ~family:"sse" ~input_lifts:[lift] "X86_VZEROUPPER" []
      (call_lifted_inputs lift
         [mk_exp (E_struct_update (default_prefix,
            List.map (fun (name, value) -> mk_fexp (mk_id name) value) [
              "vex_present", bool true; "vex_l", bool false;
              "vex_vvvv", int 0]))] [])])

(* AES-NI. AESENC, AESENCLAST, AESDEC and AESDECLAST are 66 0F 38 DC to DF
   and AESKEYGENASSIST is 66 0F 3A DF. Each is legacy-encoded: the
   destination keeps bits 128 to 511 of its register, as for the SSE
   suite. The selected branch of dispatch_3byte_38_sse_int and
   dispatch_3byte_3a_sse_int calls the upstream `aesenc`, `aesdec` and
   `aeskeygenassist`, and their S-box and MixColumns calculations are
   translated, not supplied. The AES-NI availability check of
   check_legacy_simd is outside the selected bodies and is not
   compared. *)
let aes =
  let two = ["d", word 4; "m", word 4] in
  let lift function_name argument opcode inputs =
    input_lift ~fixed_arguments:[argument, opcode] ~expected_inputs:inputs
      function_name "fetch" in
  List.map (fun (instruction, opcode) ->
    let lift = lift "dispatch_3byte_38_sse_int" "opcode" opcode 1 in
    make ~family:"aes" ~input_lifts:[lift] (sse_name instruction "" "RR") two
      (call_lifted lift [sse_prefix (bit "d" 3) (bit "m" 3)] (modrm "d" "m"))
  ) ["AESENC", 220; "AESENCLAST", 221; "AESDEC", 222; "AESDECLAST", 223] @
  (let lift = lift "dispatch_3byte_3a_sse_int" "opcode" 223 2 in
   [make ~family:"aes" ~input_lifts:[lift] (sse_name "AESKEYGENASSIST" "" "RRI")
      (two @ ["imm", word 8])
      (call_lifted_inputs lift [sse_prefix (bit "d" 3) (bit "m" 3)]
         [modrm "d" "m"; id "imm"])])

let shift_selections = shifts @ double_shifts
let shift = List.map fst shift_selections

let assumptions entries =
  let has name = List.exists (fun (entry : Entry.t) -> entry.name = name) entries in
  let mode_dependent = List.filter_map (fun ((entry : Entry.t), required) ->
    if required then Some entry.name else None)
    (arithmetic_selections @ shift_selections @ move_selections @
     select_selections @ bit_selections @ pext_extended @
     List.map (fun (entry, _) -> entry, true) count_selections) in
  let acquired = List.filter (fun (form : acquired_scalar_form) -> has form.name)
    acquired_scalar_forms in
  (if List.exists has mode_dependent || acquired <> [] ||
      List.exists (fun (entry : Entry.t) ->
        entry.family = "vector" || entry.family = "avx2" ||
        entry.family = "sse" || entry.family = "aes" ||
        entry.family = "stack") entries
   then [Initial_enum ("cur_mode","LongMode")] else []) @
  List.map (fun (name,value) -> Initial_bool (name,value))
    (List.sort_uniq compare
      ((if List.exists (fun ((entry : Entry.t), _) -> has entry.name)
          (multiply_extended @ pext_extended) then ["has_bmi2",true] else []) @
       List.filter_map (fun ((entry : Entry.t), feature) ->
         match feature with
         | Some name when has entry.name -> Some (name,true)
         | _ -> None) count_selections @
       List.concat_map (fun form -> form.features) acquired))

(* LEAVE's original C9 branch retains operand-size selection and pop.
   Only instruction acquisition and the declared data-read boundary are
   supplied; the register updates and stack-address calculation stay in Sail. *)
let stack =
  [fst (decoded_selection ~family:"stack" ~through:None "X86_LEAVE64" []
    201 default_prefix [])]

let entries = arithmetic @ vector @ avx2 @ shift @ move @ select @ bit_family @
  sse @ aes @ count_family @ pext_family @ stack
let family_roots =
  ["arithmetic", List.map (fun (entry : Entry.t) -> entry.name) arithmetic;
   "vector", List.map (fun (entry : Entry.t) -> entry.name) vector;
   "avx2", List.map (fun (entry : Entry.t) -> entry.name) avx2;
   "shift", List.map (fun (entry : Entry.t) -> entry.name) shift;
   "move", List.map (fun (entry : Entry.t) -> entry.name) move;
   "select", List.map (fun (entry : Entry.t) -> entry.name) select;
   "bit", List.map (fun (entry : Entry.t) -> entry.name) bit_family;
   "sse", List.map (fun (entry : Entry.t) -> entry.name) sse;
   "aes", List.map (fun (entry : Entry.t) -> entry.name) aes;
   "count", List.map (fun (entry : Entry.t) -> entry.name) count_family;
   "pext", List.map (fun (entry : Entry.t) -> entry.name) pext_family;
   "stack", List.map (fun (entry : Entry.t) -> entry.name) stack]
let contracts =
  ["read_simd", true; "write_simd", false; "read_mem_data", false]
let cuts = List.map fst contracts

(* The shina outputs keep their established x86-FAMILY stems and X86_
   root names; existing proofs and CI records refer to them. *)
let source = {
  model = "shina";
  stem = (fun family -> "x86-" ^ family);
  qualified_names = false; extended_evaluation = false;
  entries; family_roots; assumptions; contracts;
  bindings = [Gpr_bank "GPR"; Zmm_bank "ZMM";
              Flag_bits ["CF"; "PF"; "AF"; "ZF"; "SF"; "OF"; "DF"];
              Simd_access; Flat_data_read];
  (* The translator checks each GPR, flag and SIMD access as it reaches it. *)
  validate = (fun _ -> ());
}
