(* rems-project/sail-x86-from-acl2 instruction bindings.

   REMS translates the ACL2 X86isa model to Sail. Its instruction bodies
   take the decoded instruction as arguments: processor mode, the start and
   current instruction pointers, the prefix record, the REX byte, the
   opcode, and the ModR/M and SIB bytes. Each binding below calls one such
   body with a register-direct encoding. The arithmetic, the flag
   calculation, operand decoding and the RIP update remain in the body.

   Each binding supplies only encoding choices:
     proc_mode   Mode_64bit, the 64-bit submode of IA-32e mode;
     start_rip   0, the start of a synthetic instruction;
     temp_rip    the address just past its ModR/M byte;
     prefixes    the record get_prefixes builds for the encoding;
     rex_byte    0100WRXB, or 0 for a legacy byte form;
     opcode      the one-byte opcode;
     modr_m      mod=11 with the reg and r/m register fields;
     sib         0, unused for mod=11.
   The span start_rip..temp_rip is a valid instruction location: the body's
   length and canonical-address checks pass for it. It does not fix the HOL
   RIP; the body's final write of temp_rip to RIP is retained in the export
   and excluded only by the proof-side core observation. Register numbers,
   register values and flags stay variable; operands may alias.

   For example, ADD64 calls
     x86_add_adc_sub_sbb_or_and_xor_cmp_g_e(0, Mode_64bit, 0, 3,
       Mk_prefixes(0x03 @ ... @ 0x1), 0b0100 @ 0b1 @ d[3..3] @ 0b0 @ m[3..3],
       0x03, Mk_modr_m(0b11 @ d[2..0] @ m[2..0]), Mk_sib(0x00))
   which encodes ADD r64, r/m64 (REX.W 03 /r) with destination d and
   source m. The dispatcher's LOCK-prefix check is outside the body; the
   chosen prefixes contain no LOCK prefix.

   State bindings: read_gpr/write_gpr are cuts with REMS's own signatures,
   rflags is the low half of HOL rflags and rip is HOL RIP. Cutting
   write_gpr removes its log_gpr_write instrumentation; the
   log_register_writes=false assumption removes the same instrumentation
   from write_rip. Both are recorded in the generated evidence. *)
open Libsail
open Ast
open Ast_util
open Entry
open X86

let prefix = "X86_REMS_"

let append values =
  match List.rev values with
  | [] -> invalid_arg "append"
  | last :: rest ->
      List.fold_left (fun right left -> mk_exp (E_vector_append (left, right)))
        last rest

(* A ModR/M field is a register parameter or a fixed opcode extension.
   A three-bit legacy register field has no REX extension bit. *)
type field = Register of string | Extension of int

let low_bits form = function
  | Register name -> slice (id name) 2 0
  | Extension value -> ignore form; bit_literal 3 value

let extension form = function
  | Register name when form.register_bits = 4 -> slice (id name) 3 3
  | _ -> bit_literal 1 0

(* REX is 0100WRXB: R extends ModR/M.reg and B extends ModR/M.r/m. *)
let rex form reg rm =
  if not form.rex then bit_literal 8 0 else
  append [bit_literal 4 4; bit_literal 1 (if form.width = 64 then 1 else 0);
          extension form reg; bit_literal 1 0; extension form rm]

let modrm form reg rm =
  call "Mk_modr_m" [append [bit_literal 2 3; low_bits form reg; low_bits form rm]]

(* get_prefixes records the first opcode byte in nxt and the number of
   prefix bytes, including REX, in num. Only the operand-size prefix is
   used here; no LOCK, REP, segment or address-size prefix. *)
let prefix_count form =
  (if form.width = 16 then 1 else 0) + (if form.rex then 1 else 0)

let prefixes form first_opcode =
  call "Mk_prefixes" [append [
    bit_literal 8 first_opcode; bit_literal 8 0;
    bit_literal 8 (if form.width = 16 then 0x66 else 0);
    bit_literal 8 0; bit_literal 8 0; bit_literal 8 0;
    bit_literal 4 (prefix_count form)]]

(* The decoded-instruction arguments of a body. temp_rip is just past the
   ModR/M byte, after the prefixes and one or two opcode bytes; the bodies
   add any immediate bytes. *)
let decoded_arguments ~opcode_bytes form opcode reg rm = [
  id "Mode_64bit"; bit_literal 48 0;
  bit_literal 48 (prefix_count form + opcode_bytes + 1);
  prefixes form (if opcode_bytes = 2 then 0x0f else opcode);
  rex form reg rm; bit_literal 8 opcode;
  modrm form reg rm; call "Mk_sib" [bit_literal 8 0]]

let decoded_call ?(operation = []) ?(opcode_bytes = 1) body form opcode reg rm =
  call body (operation @ decoded_arguments ~opcode_bytes form opcode reg rm)

let entry family operation form operands names body =
  make ~family (scalar_name ~prefix operation form operands)
    (scalar_parameters form names) body

(* x86_add_adc_sub_sbb_or_and_xor_cmp_g_e (arith_and_logic.sail:73)
   decodes OP r, r/m: ModR/M.reg is the destination and first operand.
   REMS numbers the operations 0 ADD, 1 OR, 2 ADC, 3 AND, 4 SUB, 5 XOR,
   6 SBB and 8 CMP; CMP writes only flags. The byte opcode is one less
   than the wider opcode. *)
let alu =
  List.concat_map (fun (operation, number, opcode) ->
    List.map (fun form ->
      let opcode = if form.width = 8 then opcode - 1 else opcode in
      entry "arithmetic" operation form "RR" ["d"; "m"]
        (decoded_call "x86_add_adc_sub_sbb_or_and_xor_cmp_g_e"
          ~operation:[int number] form opcode (Register "d") (Register "m"))
    ) (scalar_forms [64; 32; 16; 8])
  ) ["ADD", 0, 0x03; "OR", 1, 0x0b; "ADC", 2, 0x13; "AND", 3, 0x23;
     "SUB", 4, 0x2b; "XOR", 5, 0x33; "SBB", 6, 0x1b; "CMP", 8, 0x3b]

(* TEST r/m, r (84/85 /r) uses the E,G body with operation 7, which writes
   only flags. As for the shina form, ModR/M.reg holds d and r/m holds m. *)
let test =
  List.map (fun form ->
    entry "arithmetic" "TEST" form "RR" ["d"; "m"]
      (decoded_call "x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g"
        ~operation:[int 7] form (if form.width = 8 then 0x84 else 0x85)
        (Register "d") (Register "m"))
  ) (scalar_forms [64; 32; 16; 8])

(* Group bodies take their operation from ModR/M.reg and one register
   operand from r/m: FE/FF /0 INC, /1 DEC; F6/F7 /2 NOT, /3 NEG, /4 MUL,
   /5 one-operand IMUL. The byte opcode is one less than the wider one.
   MUL and IMUL1 have the implicit outputs of the s2n-bignum forms. *)
let group =
  List.concat_map (fun (operation, body, opcode, selector, name) ->
    List.map (fun form ->
      entry "arithmetic" operation form "R" [name]
        (decoded_call body form (if form.width = 8 then opcode - 1 else opcode)
          (Extension selector) (Register name))
    ) (scalar_forms [64; 32; 16; 8])
  ) ["INC", "x86_inc_dec_fe_ff", 0xff, 0, "d";
     "DEC", "x86_inc_dec_fe_ff", 0xff, 1, "d";
     "NOT", "x86_not_neg_f6_f7", 0xf7, 2, "d";
     "NEG", "x86_not_neg_f6_f7", 0xf7, 3, "d";
     "MUL", "x86_mul", 0xf7, 4, "m";
     "IMUL1", "x86_imul_op_en_m", 0xf7, 5, "m"]

(* 0F AF /r is the two-operand truncated IMUL r, r/m. ModR/M.reg is both
   the first input and the destination, as in the shina form. *)
let truncated_multiply =
  List.map (fun form ->
    entry "arithmetic" "IMUL" form "RR" ["d"; "m"]
      (decoded_call ~opcode_bytes:2 "x86_imul_op_en_rm" form 0xaf
        (Register "d") (Register "m"))
  ) (scalar_forms [64; 32; 16])

(* Group-2 shifts with an imm8 count (C0/C1 /n ib). The body fetches the
   immediate with rme_size at temp_rip in two match arms, one for each of
   the opcodes 192 and 193 (rotate_and_shift.sail:79-80). Both fetches
   become supplied inputs, in source order; the binding passes the same
   count byte, zero-extended to the fetched 128 bits, for both. Only the
   arm of the selected opcode is reached. The body still evaluates each
   fetch's address arguments, masks the count and advances temp_rip past
   the immediate. Every count byte is admitted. *)
let immediate_lift source =
  input_lift ~expected_inputs:2 ~evaluate_arguments:true source "rme_size"

let immediate_call lift form ~opcode_bytes opcode reg rm =
  let count = call "sail_zero_extend" [id "count"; int 128] in
  call_lifted_inputs lift (decoded_arguments ~opcode_bytes form opcode reg rm)
    [count; count]

let shift_lift = immediate_lift "x86_sal_sar_shl_shr_rcl_rcr_rol_ror"

(* The 8- and 16-bit rotates pass the masked count, up to 31, unreduced
   to rotate_left_bits/rotate_right_bits (prelude.sail:510-532), which
   shift by width - count. For counts above the width that amount is
   negative, and the translated shift yields an unknown word there
   (rems-rotate-wide-count in docs/X86-DIVERGENCES.md). *)
let rotate_widths = [64; 32; 16; 8]

let shifts =
  List.concat_map (fun (operation, selector, widths) ->
    List.map (fun form ->
      make ~family:"shift" ~input_lifts:[shift_lift]
        (scalar_name ~prefix operation form "RI")
        (scalar_parameters form ["d"] @ ["count", word 8])
        (immediate_call shift_lift form ~opcode_bytes:1
          (if form.width = 8 then 0xc0 else 0xc1)
          (Extension selector) (Register "d"))
    ) (scalar_forms widths)
  ) ["ROL", 0, rotate_widths; "ROR", 1, rotate_widths;
     "RCL", 2, rotate_widths; "RCR", 3, rotate_widths;
     "SHL", 4, [64; 32; 16; 8]; "SHR", 5, [64; 32; 16; 8];
     "SAR", 7, [64; 32; 16; 8]]

(* SHLD/SHRD r/m, r, imm8 (0F A4 /r ib, 0F AC /r ib). The destination is
   ModR/M.r/m and the source ModR/M.reg, so d is r/m and m is reg here.
   The imm8 count is supplied like the group-2 count; the two fetches are
   the arms for opcodes 164 and 172 (rotate_and_shift.sail:160-161). *)
let double_shift_lift = immediate_lift "x86_shld_shrd"

let double_shifts =
  List.concat_map (fun (operation, opcode) ->
    List.map (fun form ->
      make ~family:"shift" ~input_lifts:[double_shift_lift]
        (scalar_name ~prefix operation form "RRI")
        (scalar_parameters form ["d"; "m"] @ ["count", word 8])
        (immediate_call double_shift_lift form ~opcode_bytes:2 opcode
          (Register "m") (Register "d"))
    ) (scalar_forms [64; 32; 16])
  ) ["SHLD", 0xa4; "SHRD", 0xac]

let arithmetic = alu @ test @ group @ truncated_multiply
let shift = shifts @ double_shifts
let entries = arithmetic @ shift
let family_roots =
  ["arithmetic", List.map (fun (entry : Entry.t) -> entry.name) arithmetic;
   "shift", List.map (fun (entry : Entry.t) -> entry.name) shift]

(* read_gpr and write_gpr are cuts with a fixed HOL interpretation:
   index i is registers :> element (word i). That is correct only if the
   removed bodies use the x86 register numbering, which HOL also uses:
     0 rax, 1 rcx, 2 rdx, 3 rbx, 4 rsp, 5 rbp, 6 rsi, 7 rdi, 8..15 r8..r15.
   Check the declarations and the bodies before they are cut. write_gpr
   may additionally only call log_gpr_write under log_register_writes; that
   logging is the excluded instrumentation. *)
let registers =
  ["rax"; "rcx"; "rdx"; "rbx"; "rsp"; "rbp"; "rsi"; "rdi"] @
  List.init 8 (fun index -> "r" ^ string_of_int (index + 8))

let validate (state : Interactive.State.istate) =
  let fail message =
    raise (Reporting.err_general Parse_ast.Unknown ("HOL Light: REMS registers: " ^ message)) in
  let env = state.env in
  let clause name =
    match List.find_map (function
      | DEF_aux (DEF_fundef (FD_aux (FD_function (_, _, [
          FCL_aux (FCL_funcl (id, Pat_aux (Pat_exp (pat, body), _)), _)]), _)), _)
          when string_of_id id = name -> Some (pat, body)
      | _ -> None) state.ast.defs with
    | Some clause -> clause
    | None -> fail (name ^ " requires one source clause") in
  let rec strip (E_aux (aux, _) as exp) = match aux with
    | E_typ (_, exp) | E_block [exp] -> strip exp
    | _ -> exp in
  let rec variable (P_aux (aux, _)) = match aux with
    | P_typ (_, pat) | P_var (pat, _) -> variable pat
    | P_id id -> Some (string_of_id id)
    | _ -> None in
  let rec literal (P_aux (aux, _)) = match aux with
    | P_typ (_, pat) -> literal pat
    | P_lit (L_aux (L_num n, _)) -> Some (Big_int.to_int n)
    | _ -> None in
  let rec wildcard (P_aux (aux, _)) = match aux with
    | P_typ (_, pat) -> wildcard pat
    | P_wild -> true
    | _ -> false in
  let identifier exp = match strip exp with
    | E_aux (E_id id, _) -> Some (string_of_id id)
    | _ -> None in
  let register name = Type_check.Env.is_register (mk_id name) env in
  let check_cases name selector body arm =
    match strip body with
    | E_aux (E_match (scrutinee, cases), _) when identifier scrutinee = Some selector ->
        if List.length cases <> 16 then fail (name ^ " requires sixteen cases");
        List.iteri (fun index case ->
          match case with
          (* Sail turns the final literal of a complete range(0, 15) match
             into a wildcard; with the signature checked, it is index 15. *)
          | Pat_aux (Pat_exp (pattern, result), _) when literal pattern = Some index ||
              (index = 15 && wildcard pattern) ->
              if not (arm (List.nth registers index) result) then
                fail (Printf.sprintf "%s case %d does not access %s"
                  name index (List.nth registers index))
          | case -> fail (name ^ " cases must be the literals 0..15 in order: " ^
              string_of_pexp (Type_check.strip_pexp case))) cases
    | _ -> fail (name ^ " requires a match on its index") in
  let read_pattern, read_body = clause "read_gpr" in
  (match variable read_pattern with
   | Some index -> check_cases "read_gpr" index read_body (fun name result ->
       register name && identifier result = Some name)
   | None -> fail "read_gpr requires one index parameter");
  let write_pattern, write_body = clause "write_gpr" in
  let index, value = match write_pattern with
    | P_aux (P_tuple [index; value], _) ->
        (match variable index, variable value with
         | Some index, Some value -> index, value
         | _ -> fail "write_gpr requires index and value parameters")
    | _ -> fail "write_gpr requires index and value parameters" in
  let statements = match write_body with
    | E_aux (E_block statements, _) -> statements
    | statement -> [statement] in
  (match statements with
   | update :: instrumentation ->
       check_cases "write_gpr" index update (fun name result ->
         register name && match strip result with
         | E_aux (E_assign (LE_aux (LE_id id, _), assigned), _) ->
             string_of_id id = name && identifier assigned = Some value
         | _ -> false);
       List.iter (fun statement -> match strip statement with
         | E_aux (E_if (condition, E_aux (E_app (logger, [argument]), _), otherwise), _)
             when identifier condition = Some "log_register_writes" &&
                  string_of_id logger = "log_gpr_write" &&
                  identifier argument = Some index &&
                  (match strip otherwise with
                   | E_aux (E_lit (L_aux (L_unit, _)), _) -> true | _ -> false) -> ()
         | _ -> fail "write_gpr has an effect other than its update and logging")
         instrumentation
   | [] -> fail "write_gpr requires a body");
  (* The cut declarations keep these exact source signatures. *)
  (* The environment represents a range parameter by a quantified atom;
     the checked declaration keeps the written range. *)
  let signature name =
    match List.find_map (function
      | DEF_aux (DEF_val (VS_aux (VS_val_spec (
          TypSchm_aux (TypSchm_ts (_, signature), _), id, _), _)), _)
          when string_of_id id = name -> Some signature
      | _ -> None) state.ast.defs with
    | Some signature -> signature
    | None -> fail (name ^ " requires a declaration") in
  let constant value (A_aux (argument, _)) = match argument with
    | A_nexp nexp -> nexp_identical (nexp_simp nexp) (nconstant (Big_int.of_int value))
    | _ -> false in
  let index_range typ = match Type_check.Env.expand_synonyms env typ with
    | Typ_aux (Typ_app (id, [low; high]), _) ->
        string_of_id id = "range" && constant 0 low && constant 15 high
    | _ -> false in
  let word64 typ = match Type_check.Env.expand_synonyms env typ with
    | Typ_aux (Typ_app (id, [width]), _) ->
        string_of_id id = "bitvector" && constant 64 width
    | _ -> false in
  (match signature "read_gpr" with
   | Typ_aux (Typ_fn ([index], result), _) when index_range index && word64 result -> ()
   | typ -> fail ("read_gpr must have type range(0, 15) -> bits(64): " ^ string_of_typ typ));
  (match signature "write_gpr" with
   | Typ_aux (Typ_fn ([index; value], result), _)
       when index_range index && word64 value && is_unit_typ result -> ()
   | _ -> fail "write_gpr must have type (range(0, 15), bits(64)) -> unit")

(* Every body writes RIP through write_iptr, and write_rip then tests
   log_register_writes. *)
let assumptions entries =
  if entries = [] then [] else [Initial_bool ("log_register_writes", false)]

let source = {
  model = "rems";
  stem = (fun family -> "x86-rems-" ^ family);
  qualified_names = true; extended_evaluation = true;
  entries; family_roots; assumptions;
  contracts = ["read_gpr", true; "write_gpr", false];
  bindings = [Gpr_access; Uncaught_exceptions]; validate;
}
