(* Instruction bindings for AArch64, inside the Sail compiler plugin.

   Each binding is an Entry.t record: an export name, symbolic operand
   parameters and a Sail call selecting an upstream instruction form.
   Constant arguments choose widths and operation flags; register indices
   and immediate fields remain symbolic. These records describe functions
   to generate, rather than executing an instruction.

   The family lists below, such as carry, construct these records. entries
   combines them into the complete catalogue. family_roots maps a group
   name such as "carry" to the export names requested by that group.

   ci/check.py generate, or run.sh arm carry after build.sh, starts Sail
   with the external Arm model, this plugin and a family selection such as
   "carry". After Sail checks the upstream model,
   prepare_upstream looks up the family names and selects their records
   from entries. Entry.instantiate creates and checks the corresponding
   Sail functions in memory, including any entry aliases they call.
   The translator infers separate source-function requests from their checked
   calls: those requests name upstream functions and fix only necessary type
   arguments. Their HOL operands are inferred from Sail. Shared execution
   functions keep flags/selectors variable; these bindings select instructions.
   The translator follows their upstream bodies and writes
   _build/arm-carry.ml; check-proof.sh runs the separate HOL Light
   agreement proofs.

   cuts names upstream operations whose bodies are replaced by the
   translator's explicit HOL interpretations.

   Parameter choices and cut lists are trusted: a well-typed call can still
   select the wrong instruction. entry.ml documents the shared syntax
   constructors.
   Some entries call execution bodies with expanded operands, others call
   specific decoders with encoded fields. This table is not a proof that the
   complete Sail and s2n-bignum instruction decoders agree. *)

open Libsail
open Ast
open Ast_util
open Entry

(* The configured processor supports AArch64, PMULL, alternate FP controls
   and SME. Instructions start in non-streaming AArch64 mode. These are
   source-state conditions, not additional fields of s2n-bignum's armstate.
   The translator validates every fact, rejects invalidating source writes,
   and records the facts each definition actually uses. Other features and
   FPCR/NZCV/register operands remain governed by their existing interpretation. *)
let assumptions = [
  Feature ("FEAT_AA64EL0", true);
  Feature ("FEAT_PMULL", true);
  Feature ("FEAT_AFP", true);
  Feature ("FEAT_SME", true);
  Initial_bit ("PSTATE", "nRW", false);
  Initial_bit ("PSTATE", "SM", false);
]

let number = int
let boolean = bool
let bits = word
(* A field is a symbolic bitvector parameter, not its register contents.
   uint constructs a call to Sail's UInt, which converts that field to the
   numeric register index expected by many Arm instruction functions. *)
let field name width = name, bits width
let uint name = call "UInt" [id name]
let entry family name parameters body = make ~family name parameters body
let unsigned name = call "unsigned" [id name]
let named_type name = mk_id_typ (mk_id name)
(* These five-bit fields can name either general or vector registers: the
   selected upstream function determines the register bank. No read occurs
   here. Names/types/constant operands below are the handwritten choices
   an auditor must compare with the corresponding upstream declaration. *)
let gprs names = List.map (fun name -> field name 5) names
let operator name args = mk_exp (E_app (mk_operator name, args))
let if_equal left right yes no =
  mk_exp (E_if (operator "==" [left; right], yes, no))
let both_widths f = List.concat_map f [32; 64]
let scalar_name operation width = Printf.sprintf "arm_%s%d" operation width
let arm_name operation width = Printf.sprintf "ARM_%s%d" operation width

(* Six operations at two widths give twelve export requests.

   Each row is (export operation, setflags, sub_op, zero-left-operand).
   The last setting selects the NGC/NGCS aliases of SBC/SBCS, which keep
   only d and m and read register 31 (the zero register under the X_read
   interpretation) as n. Width and operation flags are literal Sail
   arguments, while register indices remain symbolic and range over all
   32 encodings.

   This table supplies no arithmetic formula: the upstream body reads the
   operands and PSTATE.C, complements operand2 for subtraction, calls
   AddWithCarry, optionally writes NZCV and writes the destination. *)
let carry =
  List.concat_map (fun (operation, flags, subtract, alias) ->
    List.map (fun width ->
      let name = Printf.sprintf "ARM_%s%d" operation width in
      let parameters =
        if alias then [field "d" 5; field "m" 5]
        else [field "d" 5; field "n" 5; field "m" 5] in
      let source = "execute_aarch64_instrs_integer_arithmetic_add_sub_carry" in
      let n = if alias then number 31 else uint "n" in
      entry "carry" name parameters
        (call source [uint "d"; number width; uint "m"; n;
                      boolean flags; boolean subtract])
    ) [32; 64]
  ) ["ADC", false, false, false; "ADCS", true, false, false;
     "SBC", false, true, false; "SBCS", true, true, false;
     "NGC", false, true, true; "NGCS", true, true, true]

(* Conditional-select forms at both widths. The increment/invert booleans
   distinguish CSEL/CSINC/CSINV/CSNEG. Aliases invert the condition's low bit
   and repeat a source register; CSET/CSETM use register 31 for both sources.
   Alias calls target another entry, so Entry.closure must retain that entry. *)
let select = both_widths (fun width ->
  let source = "execute_aarch64_instrs_integer_conditional_select" in
  let operation operation increment invert =
    entry "select" (scalar_name operation width)
      (field "condition" 4 :: gprs ["d"; "n"; "m"])
      (call source [id "condition"; unsigned "d"; number width;
                    boolean increment; boolean invert; unsigned "m"; unsigned "n"]) in
  let alias operation base constant =
    let operands = if constant then [] else gprs ["n"] in
    let value = if constant then bit_literal 5 31 else id "n" in
    entry "select" (scalar_name operation width)
      (field "condition" 4 :: field "d" 5 :: operands)
      (call (scalar_name base width)
        [call "xor_vec" [id "condition"; bit_literal 4 1]; id "d"; value; value]) in
  [operation "CSEL" false false; operation "CSINC" true false;
   operation "CSINV" false true; operation "CSNEG" true true;
   alias "CINC" "CSINC" false; alias "CINV" "CSINV" false;
   alias "CNEG" "CSNEG" false; alias "CSET" "CSINC" true;
   alias "CSETM" "CSINV" true])

(* Same-width multiply-add/subtract, with destination, two multiplicands and
   accumulator kept symbolic. MUL/MNEG call MADD/MSUB with accumulator 31.
   The upstream argument order starts with the accumulator, not destination. *)
let multiply = both_widths (fun width ->
  let source = "execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub" in
  let operation operation subtract =
    entry "multiply" (scalar_name operation width) (gprs ["d"; "n"; "m"; "a"])
      (call source [unsigned "a"; unsigned "d"; number width; number width;
                    unsigned "m"; unsigned "n"; boolean subtract]) in
  let alias operation base =
    entry "multiply" (scalar_name operation width) (gprs ["d"; "n"; "m"])
      (call (scalar_name base width) [id "d"; id "n"; id "m"; bit_literal 5 31]) in
  [operation "MADD" false; operation "MSUB" true;
   alias "MUL" "MADD"; alias "MNEG" "MSUB"])

(* Unsigned 32-bit multiplicands and 64-bit destination/accumulator. The last
   literal selects unsigned arithmetic; the preceding one selects subtraction.
   UMULL/UMNEGL replace the accumulator with register 31 through an entry alias. *)
let multiply_long =
  let source = "execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64" in
  let operation operation subtract =
    entry "multiply-long" (scalar_name operation 64) (gprs ["d"; "n"; "m"; "a"])
      (call source [unsigned "a"; unsigned "d"; number 32; number 64;
                    unsigned "m"; unsigned "n"; boolean subtract; boolean true]) in
  let alias operation base =
    entry "multiply-long" (scalar_name operation 64) (gprs ["d"; "n"; "m"])
      (call (scalar_name base 64) [id "d"; id "n"; id "m"; bit_literal 5 31]) in
  [operation "UMADDL" false; operation "UMSUBL" true;
   alias "UMULL" "UMADDL"; alias "UMNEGL" "UMSUBL"]

(* High half of a 64-by-64 multiply. The final boolean selects unsigned
   (UMULH) or signed (SMULH); both use the upstream 64-to-128-high helper. *)
let multiply_high =
  List.map (fun (operation, is_unsigned) ->
    entry "multiply-high" (scalar_name operation 64) (gprs ["d"; "n"; "m"])
      (call "execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi"
        [unsigned "d"; number 64; unsigned "m"; unsigned "n"; boolean is_unsigned])
  ) ["SMULH", false; "UMULH", true]

(* Conditional compare with flags-only output. use_immediate selects either
   a zero-extended five-bit immediate or a register index from the same field.
   condition and fallback nzcv stay symbolic; subtract distinguishes CCMP
   from CCMN. Both branches call their genuine upstream instruction bodies. *)
let compare = both_widths (fun width ->
  List.map (fun (operation, subtract) ->
    let call_compare form operand =
      call ("execute_aarch64_instrs_integer_conditional_compare_" ^ form)
        [id "condition"; number width; id "nzcv"; operand; unsigned "n";
         boolean subtract] in
    entry "compare" (scalar_name operation width)
      [field "use_immediate" 1; field "operand" 5; field "n" 5;
       field "nzcv" 4; field "condition" 4]
      (if_equal (id "use_immediate") (bit_literal 1 1)
        (call_compare "immediate" (call "sail_zero_extend" [id "operand"; number width]))
        (call_compare "register" (unsigned "operand")))
  ) ["CCMN", false; "CCMP", true])

(* ADR/ADRP enter through their decoders: split the symbolic 21-bit immediate
   into immhi/immlo positions and fix the page-selector bit. The upstream
   decoder performs the address expansion; no PC arithmetic is supplied here. *)
let address =
  List.map (fun (operation, page) ->
    entry "address" (scalar_name operation 64) [field "d" 5; field "immediate" 21]
      (call ("decode_" ^ String.lowercase_ascii operation ^
             "_aarch64_instrs_integer_arithmetic_address_pc_rel")
        [id "d"; slice (id "immediate") 20 2; slice (id "immediate") 1 0;
         bit_literal 1 page])
  ) ["ADR", 0; "ADRP", 1]

(* Register-controlled shifts/rotate at both widths. Fix the ShiftType enum
   per mnemonic; destination, value register and amount register stay symbolic.
   The source call takes the amount register before the value register. *)
let shift = both_widths (fun width ->
  List.map (fun (operation, kind) ->
    entry "shift" (scalar_name operation width) (gprs ["d"; "n"; "m"])
      (call "execute_aarch64_instrs_integer_shift_variable"
        [uint "d"; number width; uint "m"; uint "n"; id ("ShiftType_" ^ kind)])
  ) ["LSLV", "LSL"; "LSRV", "LSR"; "ASRV", "ASR"; "RORV", "ROR"])

(* Full-word byte reversal: choose both register width and reversal-container
   width to be 32 or 64, leaving source and destination indices symbolic. *)
let reverse = both_widths (fun width ->
  [entry "reverse" (scalar_name "REV" width) (gprs ["d"; "n"])
    (call "execute_aarch64_instrs_integer_arithmetic_rev"
      [number width; unsigned "d"; number width; unsigned "n"])])

(* CLZ at both widths. Select CountOp_CLZ rather than another operation in
   the shared upstream counting function. *)
let count = both_widths (fun width ->
  [entry "count" (scalar_name "CLZ" width) (gprs ["d"; "n"])
    (call "execute_aarch64_instrs_integer_arithmetic_cnt"
      [unsigned "d"; number width; unsigned "n"; id "CountOp_CLZ"])])

(* EXTR keeps two source registers; immediate ROR repeats n in both source
   positions. A five-/six-bit lsb field covers exactly 0..width-1. *)
let extract = both_widths (fun width ->
  List.map (fun (operation, alias) ->
    let operands = if alias then gprs ["d"; "n"] else gprs ["d"; "n"; "m"] in
    entry "extract" (scalar_name operation width)
      (operands @ [field "lsb" (if width = 32 then 5 else 6)])
      (call "execute_aarch64_instrs_integer_ins_ext_extract_immediate"
        [unsigned "d"; number width; unsigned "lsb";
         unsigned (if alias then "n" else "m"); unsigned "n"])
  ) ["EXTR", false; "ROR", true])

(* MOVK/MOVN/MOVZ select their MoveWideOp enum. The 16-bit immediate remains
   symbolic; hw chooses positions 0/16 for W forms or 0/16/32/48 for X forms.
   Enumerate those positions as literal calls so their width constraints can
   be checked and specialized, rather than inventing a dynamic slice width. *)
let move = both_widths (fun width ->
  List.map (fun operation ->
    let call_move position =
      call "execute_aarch64_instrs_integer_ins_ext_insert_movewide"
        [unsigned "d"; number width; id "imm"; id ("MoveWideOp_" ^ operation);
         number position] in
    let body = if width = 32 then
      if_equal (id "hw") (bit_literal 1 0) (call_move 0) (call_move 16)
    else
      mk_exp (E_match (id "hw", List.init 4 (fun halfword ->
        let pattern = mk_pat (P_lit (mk_lit (L_bin (binary_digits 2 halfword)))) in
        mk_pexp (Pat_exp (pattern, call_move (16 * halfword)))))) in
    entry "move" (scalar_name ("MOV" ^ operation) width)
      [field "d" 5; field "imm" 16; field "hw" (if width = 32 then 1 else 2)] body
  ) ["K"; "N"; "Z"])

(* Logical immediate and shifted-register forms. Immediate entries receive
   the already expanded word-sized mask, not the original instruction encoding.
   Shifted entries retain a bounded amount and ShiftType enum; operation,
   flag update and operand inversion are fixed per row. MOV/MVN use a zero
   left register; TST uses destination 31 while retaining flag updates. *)
let logical = both_widths (fun width ->
  let amount = field "amount" (if width = 32 then 5 else 6) in
  let kind = "kind", named_type "ShiftType" in
  let root operation form = arm_name operation width ^ "_" ^ form in
  let immediate operation kind flags =
    entry "logical" (root operation "IMM") [field "d" 5; field "n" 5; field "imm" width]
      (call "execute_aarch64_instrs_integer_logical_immediate"
        [uint "d"; number width; id "imm"; uint "n"; id ("LogicalOp_" ^ kind);
         boolean flags]) in
  let shifted operation op flags invert =
    entry "logical" (root operation "SHIFT") (gprs ["d"; "n"; "m"] @ [amount; kind])
      (call "execute_aarch64_instrs_integer_logical_shiftedreg"
        [uint "d"; number width; boolean invert; uint "m"; uint "n";
         id ("LogicalOp_" ^ op); boolean flags; uint "amount"; id "kind"]) in
  let alias_imm operation base parameters arguments =
    entry "logical" (root operation "IMM") parameters
      (call (root base "IMM") arguments) in
  let alias_shift operation base parameters arguments =
    entry "logical" (root operation "SHIFT") parameters
      (call (root base "SHIFT") arguments) in
  [immediate "AND" "AND" false; immediate "ANDS" "AND" true;
   immediate "ORR" "ORR" false; immediate "EOR" "EOR" false;
   shifted "AND" "AND" false false; shifted "ANDS" "AND" true false;
   shifted "BIC" "AND" false true; shifted "BICS" "AND" true true;
   shifted "ORR" "ORR" false false; shifted "ORN" "ORR" false true;
   shifted "EOR" "EOR" false false; shifted "EON" "EOR" false true;
   alias_imm "MOV" "ORR" [field "d" 5; field "imm" width]
     [id "d"; bit_literal 5 31; id "imm"];
   alias_shift "MOV" "ORR" (gprs ["d"; "m"] @ [amount; kind])
     [id "d"; bit_literal 5 31; id "m"; id "amount"; id "kind"];
   alias_shift "MVN" "ORN" (gprs ["d"; "m"] @ [amount; kind])
     [id "d"; bit_literal 5 31; id "m"; id "amount"; id "kind"];
   alias_imm "TST" "ANDS" [field "n" 5; field "imm" width]
     [bit_literal 5 31; id "n"; id "imm"];
   alias_shift "TST" "ANDS" (gprs ["n"; "m"] @ [amount; kind])
     [bit_literal 5 31; id "n"; id "m"; id "amount"; id "kind"]])

(* Four 128-bit SHA3-family bitwise operations. Each selects its own upstream
   body; EOR3/BCAX pass accumulator a first, while XAR additionally keeps a
   six-bit rotation immediate. These fields index vector registers. *)
let crypto_bitwise =
  let root operation parameters args =
    entry "crypto-bitwise" (arm_name operation 128) parameters
      (call ("execute_aarch64_instrs_vector_crypto_sha3_" ^
             String.lowercase_ascii operation) args) in
  [root "EOR3" (gprs ["d"; "n"; "m"; "a"])
     [unsigned "a"; unsigned "d"; unsigned "m"; unsigned "n"];
   root "BCAX" (gprs ["d"; "n"; "m"; "a"])
     [unsigned "a"; unsigned "d"; unsigned "m"; unsigned "n"];
   root "RAX1" (gprs ["d"; "n"; "m"]) [unsigned "d"; unsigned "m"; unsigned "n"];
   root "XAR" (gprs ["d"; "n"; "m"] @ [field "imm6" 6])
     [unsigned "d"; id "imm6"; unsigned "m"; unsigned "n"]]

(* AES round and MixColumns forms on 128-bit vector registers. form chooses
   the round/mix body; decrypt distinguishes forward and inverse operations. *)
let aes =
  List.map (fun (operation, form, decrypt) ->
    entry "aes" (arm_name operation 128) (gprs ["d"; "n"])
      (call ("execute_aarch64_instrs_vector_crypto_aes_" ^ form)
        [unsigned "d"; boolean decrypt; unsigned "n"])
  ) ["AESE", "round", false; "AESD", "round", true;
     "AESMC", "mix", false; "AESIMC", "mix", true]

(* A geometry is (register width, element width), both in bits. The quotient
   is the lane count passed to the upstream instruction. D64E64, one 64-bit
   lane, is the scalar form, which among these instructions only SHL has;
   the common list omits it. vector_small
   also omits 64-bit elements; reductions omit the 64-bit/two-32-bit-lane form.
   This is an instruction-form selection, not an automatic encoding decoder. *)
let vector_geometries =
  [64, 8; 64, 16; 64, 32; 128, 8; 128, 16; 128, 32; 128, 64]
let vector_small = List.filter (fun (_, element) -> element <> 64) vector_geometries
let vector_reductions =
  List.filter (fun (width, element) -> width <> 64 || element <> 32) vector_small
let vector_name operation width element =
  Printf.sprintf "arm_%s%dE%d" operation width element
(* The name records the chosen form; arguments, not the name, select Sail
   behavior. Long/narrow forms below can use a different source/result width.
   vector_forms shares only geometry iteration. Each family still states the
   exact upstream function and argument order. lane_arguments supplies the
   common destination/width/lane-count/element-width prefix; use it only for
   upstream signatures that take those four arguments in that order. *)
let vector_entry family operation width element parameters source args =
  entry family (vector_name operation width element) parameters (call source args)
let lane_arguments width element =
  [unsigned "d"; number width; number (width / element); number element]
let vector_forms geometries family operation parameters source args =
  List.map (fun (width, element) ->
    vector_entry family operation width element parameters source (args width element)
  ) geometries
let vector_binary family operations source args =
  List.concat_map (fun operation ->
    vector_forms vector_geometries family operation (gprs ["d"; "n"; "m"])
      source (args operation)
  ) operations

(* Whole-vector logical operations at widths 64/128. Fixed enum/inversion
   choices distinguish register forms; MOV repeats n in an ORR entry call.
   Immediate BIC/ORR receive an already expanded full-vector mask. *)
let vector_logical =
  List.concat_map (fun width ->
    let root operation form = Printf.sprintf "arm_%s%d_%s" operation width form in
    let and_orr operation invert op =
      entry "vector-logical" (root operation "REG") (gprs ["d"; "n"; "m"])
        (call "execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr"
          [unsigned "d"; number width; boolean invert; unsigned "m"; unsigned "n";
           id ("LogicalOp_" ^ op)]) in
    let bitop operation op =
      entry "vector-logical" (root operation "REG") (gprs ["d"; "n"; "m"])
        (call "execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor"
          [unsigned "d"; number width; unsigned "m"; unsigned "n";
           id ("VBitOp_" ^ op)]) in
    let immediate operation =
      entry "vector-logical" (root (operation ^ "_VEC") "IMM")
        [field "d" 5; field "imm" width]
        (call "execute_aarch64_instrs_vector_logical"
          [number width; id "imm"; id ("ImmediateOp_" ^ operation); unsigned "d"]) in
    [and_orr "AND_VEC" false "AND"; and_orr "BIC_VEC" true "AND";
     and_orr "ORR_VEC" false "ORR"; bitop "EOR_VEC" "VEOR";
     bitop "BIT" "VBIT"; bitop "BIF" "VBIF";
     entry "vector-logical" (root "MOV_VEC" "REG") (gprs ["d"; "n"])
       (call (root "ORR_VEC" "REG") [id "d"; id "n"; id "n"]);
     immediate "BIC"; immediate "ORR"]
  ) [64; 128]

(* Per-lane wrapping ADD/SUB over the common geometries. The final boolean
   selects subtraction; widths and lane count are literal source arguments. *)
let vector_addsub =
  vector_binary "vector-addsub" ["ADD_VEC"; "SUB_VEC"]
    "execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd"
    (fun operation width element ->
      lane_arguments width element @
      [unsigned "m"; unsigned "n"; boolean (operation = "SUB_VEC")])

(* ABS uses the shared vector negate/absolute-value body with negation false.
   Source/destination fields stay symbolic over every common geometry. *)
let vector_abs =
  vector_forms vector_geometries "vector-abs" "ABS_VEC" (gprs ["d"; "n"])
    "execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd"
    (fun width element -> lane_arguments width element @ [unsigned "n"; boolean false])

(* Signed greater-than/greater-or-equal and unsigned higher-than compare two
   vectors; the row fixes equality and unsigned selectors. CMLE-zero uses
   the separate unary body with CompareOp_LE, not a synthetic zero register. *)
let vector_compare =
  vector_binary "vector-compare" ["CMGT_VEC"; "CMGE_VEC"; "CMHI_VEC"]
    "execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd"
    (fun operation width element ->
      [boolean (operation = "CMGE_VEC"); unsigned "d"; number width;
       number (width / element); number element; unsigned "m"; unsigned "n";
       boolean (operation = "CMHI_VEC")]) @
  vector_forms vector_geometries "vector-compare" "CMLE_VEC_ZERO" (gprs ["d"; "n"])
    "execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd"
    (fun width element ->
      [id "CompareOp_LE"; unsigned "d"; number width; number (width / element);
       number element; unsigned "n"])

(* CNT counts bits in byte lanes: fix element width 8 and width/8 lanes for
   each 64/128-bit register form. *)
let vector_count =
  List.map (fun width ->
    entry "vector-count" (scalar_name "CNT" width) (gprs ["d"; "n"])
      (call "execute_aarch64_instrs_vector_arithmetic_unary_cnt"
        [unsigned "d"; number width; number (width / 8); number 8; unsigned "n"])
  ) [64; 128]

(* EXT takes a byte-position field (0..7 or 0..15). Construct a Sail multiply
   by 8 to pass a bit position to the upstream vector-extract function. *)
let vector_extract =
  List.map (fun width ->
    entry "vector-extract" (scalar_name "EXT" width)
      (gprs ["d"; "n"; "m"] @ [field "position" (if width = 64 then 3 else 4)])
      (call "execute_aarch64_instrs_vector_transfer_vector_extract"
        [unsigned "d"; number width; unsigned "m"; unsigned "n";
         operator "*" [unsigned "position"; number 8]])
  ) [64; 128]

(* XTN/XTN2 keep the low half of each wider source lane. Fix output-half width
   64 and output element widths 8/16/32; part 0/1 selects the destination half.
   The upstream body supplies narrowing and preservation of the other half. *)
let vector_narrow =
  List.concat_map (fun part ->
    List.map (fun element ->
      vector_entry "vector-narrow" (if part = 0 then "XTN" else "XTN2") 64 element
        (gprs ["d"; "n"])
        "execute_aarch64_instrs_vector_arithmetic_unary_extract_nosat"
        [unsigned "d"; number 64; number (64 / element); number element;
         unsigned "n"; number part]
    ) [8; 16; 32]
  ) [0; 1]

(* MOVI receives an already expanded 64-bit immediate. Build a checked Sail
   Replicate call and bind its explicitly sized result before the vector
   logical instruction, duplicating it twice only for the 128-bit form. *)
let vector_move =
  List.map (fun width ->
    let expanded = mk_pat (P_typ (bits width, mk_pat (P_id (mk_id "expanded")))) in
    let body = mk_exp (E_let (expanded,
      call "Replicate" [id "imm"; number (width / 64)],
      call "execute_aarch64_instrs_vector_logical"
        [number width; id "expanded"; id "ImmediateOp_MOVI"; unsigned "d"])) in
    entry "vector-move" (scalar_name "MOVI" width) [field "d" 5; field "imm" 64] body
  ) [64; 128]

(* REV32/REV64 on Q128: reverse within 32-/64-bit containers, respectively.
   Only listed element widths divide those containers; pass container count,
   elements per container and element width separately to the source body. *)
let vector_reverse =
  List.concat_map (fun (operation, container, elements) ->
    List.map (fun element ->
      vector_entry "vector-reverse" operation 128 element (gprs ["d"; "n"])
        "execute_aarch64_instrs_vector_arithmetic_unary_rev"
        [number (128 / container); unsigned "d"; number 128;
         number (container / element); number element; unsigned "n"]
    ) elements
  ) ["REV32_VEC", 32, [8; 16]; "REV64_VEC", 64, [8; 16; 32]]

(* Move one 32-/64-bit vector lane to a general register of the same width.
   The encoded index chooses a 64-bit source view for its lower half, or a
   128-bit view for upper lanes. Keep that selection as checked Sail control
   flow so every value of the exported index has the appropriate source type. *)
let vector_umov =
  List.map (fun width ->
    let body_for datasize =
      call "execute_aarch64_instrs_vector_transfer_integer_move_unsigned"
        [unsigned "d"; number width; number width; number datasize; id "i"; unsigned "n"] in
    let condition = operator (if width = 32 then "<" else "==")
      [id "i"; number (if width = 32 then 2 else 0)] in
    let body = mk_exp (E_let (mk_pat (P_id (mk_id "i")), unsigned "index",
      mk_exp (E_if (condition, body_for 64, body_for 128)))) in
    entry "vector-umov" (vector_name "UMOV" width width)
      (gprs ["d"; "n"] @ [field "index" (if width = 32 then 2 else 1)]) body
  ) [32; 64]

(* ADDV, unsigned widening UADDLV and unsigned UMAXV use the restricted
   reduction geometries. Each calls its own reduction body with literal widths,
   lane counts and operation/signedness selectors. *)
let vector_reduce =
  List.concat_map (fun (width, element) ->
    [vector_entry "vector-add-reduce" "ADDV" width element (gprs ["d"; "n"])
       "execute_aarch64_instrs_vector_reduce_add_simd"
       [unsigned "d"; number width; number element; unsigned "n"; id "ReduceOp_ADD"];
     vector_entry "vector-add-long-reduce" "UADDLV" width element (gprs ["d"; "n"])
       "execute_aarch64_instrs_vector_reduce_add_long"
       (lane_arguments width element @ [unsigned "n"; boolean true]);
     vector_entry "vector-max-reduce" "UMAXV" width element (gprs ["d"; "n"])
       "execute_aarch64_instrs_vector_reduce_int_max"
       (lane_arguments width element @ [boolean false; unsigned "n"; boolean true])]
  ) vector_reductions

(* Signed maximum, unsigned maximum and unsigned minimum over vector_small.
   minimum and is_unsigned select the shared max/min body independently. *)
let vector_minmax =
  List.concat_map (fun (operation, minimum, is_unsigned) ->
    vector_forms vector_small "vector-minmax" operation (gprs ["d"; "n"; "m"])
      "execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single"
      (fun width element -> lane_arguments width element @
        [unsigned "m"; boolean minimum; unsigned "n"; boolean is_unsigned])
  ) ["SMAX_VEC", false, false; "UMAX_VEC", false, true; "UMIN_VEC", true, true]

(* Unsigned widening pairwise add, optionally accumulated into destination.
   Pass width/(2*element) output lanes. Non-accumulating UADDLP is selected
   only at width 128 here; UADALP uses vector_small and accumulate=true. *)
let vector_pair =
  List.concat_map (fun (operation, accumulate, geometries) ->
    vector_forms geometries
      (if accumulate then "vector-pair-add-accumulate-long" else "vector-pair-add-long")
      operation (gprs ["d"; "n"])
      "execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise"
      (fun width element ->
        [boolean accumulate; unsigned "d"; number width; number (width / (2 * element));
         number element; unsigned "n"; boolean true])
  ) ["UADDLP", false, [128, 8; 128, 16; 128, 32];
     "UADALP", true, vector_small]

(* UZP/ZIP/TRN fix part 0/1 for their first/second forms. UZP is selected only
   for Q128; ZIP/TRN use all common geometries. The unzip interface takes total
   lane count, while zip/transpose take half-count in a different position. *)
let vector_permute =
  List.concat_map (fun (operation, source, geometries) ->
    List.concat_map (fun part ->
      List.map (fun (width, element) ->
        let args = if operation = "UZP" then
          lane_arguments width element @ [unsigned "m"; unsigned "n"; number part]
        else
          [unsigned "d"; number width; number element; unsigned "m"; unsigned "n";
           number (width / (2 * element)); number part] in
        vector_entry ("vector-" ^ String.lowercase_ascii operation)
          (operation ^ string_of_int (part + 1)) width element (gprs ["d"; "n"; "m"])
          ("execute_aarch64_instrs_vector_transfer_vector_permute_" ^ source) args
      ) geometries
    ) [0; 1]
  ) ["UZP", "unzip", List.filter (fun (width, _) -> width = 128) vector_geometries;
     "ZIP", "zip", vector_geometries; "TRN", "transpose", vector_geometries]

(* SHA256/SHA512 hash and schedule operations select distinct upstream bodies.
   SHA256H/H2 share a body with a fixed part1 selector. SU0 forms
   have only d,n; the three-register forms preserve the source body's d,m,n
   order even though the exported parameters are d,n,m. *)
let sha2 =
  let root operation source parameters args =
    entry "sha2" (arm_name operation 128) parameters
      (call ("execute_aarch64_instrs_vector_crypto_" ^ source) args) in
  let binary = gprs ["d"; "n"] in
  let ternary = gprs ["d"; "n"; "m"] in
  let args = [unsigned "d"; unsigned "m"; unsigned "n"] in
  [root "SHA256H" "sha3op_sha256_hash" ternary (args @ [boolean true]);
   root "SHA256H2" "sha3op_sha256_hash" ternary (args @ [boolean false]);
   root "SHA256SU0" "sha2op_sha256_sched0" binary [unsigned "d"; unsigned "n"];
   root "SHA256SU1" "sha3op_sha256_sched1" ternary args;
   root "SHA512H" "sha512_sha512h" ternary args;
   root "SHA512H2" "sha512_sha512h2" ternary args;
   root "SHA512SU0" "sha512_sha512su0" binary [unsigned "d"; unsigned "n"];
   root "SHA512SU1" "sha512_sha512su1" ternary args]

(* Encoded field sizes and lane offsets are host-side catalogue arithmetic.
   plus still builds a Sail addition node; it does not evaluate an operand.
   A source lane is the low-half index field, plus the lanes of one half for
   the high half. 64-bit lanes have no field: the lane is literal 0 or 1. *)
let log2 = function
  | 1 -> 0 | 2 -> 1 | 4 -> 2 | 8 -> 3 | 16 -> 4 | 32 -> 5 | 64 -> 6
  | _ -> invalid_arg "AArch64 field width must be a power of two"
let plus left right = operator "+" [left; right]
let index_field element =
  if element = 64 then [] else [field "index" (log2 (64 / element))]
let encoded_index element high =
  if element = 64 then number (if high then 1 else 0)
  else if high then plus (unsigned "index") (number (64 / element))
  else unsigned "index"

(* DUP from a general register: each geometry fixes output lanes and element
   width. The upstream body chooses the corresponding part of the GPR value. *)
let vector_duplicate_general =
  vector_forms vector_geometries "vector-duplicate-general" "DUP_GEN" (gprs ["d"; "n"])
    "execute_aarch64_instrs_vector_transfer_integer_dup"
    (fun width element -> lane_arguments width element @ [unsigned "n"])

(* DUP from a vector lane; LO/HI entries select the source half. The scalar
   form, such as MOV D0, V1.D[1], calls the same upstream body with one
   element and a destination as wide as the element. *)
let duplicate_element family name width element high =
  entry family name (gprs ["d"; "n"] @ index_field element)
    (call "execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd"
      (lane_arguments width element @
       [number (if high then 128 else 64); encoded_index element high; unsigned "n"]))

let vector_duplicate_element =
  List.concat_map (fun (width, element) ->
    List.map (fun high ->
      duplicate_element "vector-duplicate-element"
        (vector_name "DUP_ELEM" width element ^ if high then "_HI" else "_LO")
        width element high
    ) [false; true]
  ) vector_geometries

let vector_duplicate_element_scalar =
  List.concat_map (fun element ->
    List.map (fun high ->
      duplicate_element "vector-duplicate-element-scalar"
        (Printf.sprintf "arm_DUP_ELEM_SCALAR_E%d_%s" element (if high then "HI" else "LO"))
        element element high
    ) [false; true]
  ) [8; 16; 32; 64]

(* SHL encodes amount in log2(element) bits, covering 0..element-1.
   The table fixes geometry; the source body performs the per-lane shift. *)
(* SHL also has a scalar D64E64 form, SHL Dd, Dn, #amount, which the same
   upstream body executes with one 64-bit lane. *)
let vector_left_shift =
  List.map (fun (width, element) ->
    vector_entry "vector-left-shift" "SHL_VEC" width element
      (field "amount" (log2 element) :: gprs ["d"; "n"])
      "execute_aarch64_instrs_vector_shift_left_sisd"
      (lane_arguments width element @ [unsigned "n"; unsigned "amount"])
  ) (vector_geometries @ [64, 64])

(* Right shifts encode amount-1, so the constructed +1 yields 1..element.
   Row booleans select accumulation, rounding and signed/unsigned arithmetic.
   The addition is a Sail expression and remains part of the checked entry. *)
let vector_right_shift =
  List.concat_map (fun (operation, accumulate, round, is_unsigned) ->
    List.map (fun (width, element) ->
      vector_entry "vector-right-shift" operation width element
        (field "amount" (log2 element) :: gprs ["d"; "n"])
        "execute_aarch64_instrs_vector_shift_right_sisd"
        [boolean accumulate; unsigned "d"; number width; number (width / element);
         number element; unsigned "n"; boolean round;
         plus (unsigned "amount") (number 1); boolean is_unsigned]
    ) vector_geometries
  ) ["USHR_VEC", false, false, true; "SSHR_VEC", false, false, false;
     "SRSHR_VEC", false, true, false; "USRA_VEC", true, false, true]

(* SLI uses shifts 0..element-1; SRI uses 1..element via the same +1 convention.
   Separate left/right upstream bodies supply insertion into the destination. *)
let vector_shift_insert =
  List.concat_map (fun (operation, direction, right) ->
    List.map (fun (width, element) ->
      let amount = if right then plus (unsigned "amount") (number 1)
        else unsigned "amount" in
      vector_entry "vector-shift-insert" operation width element
        (field "amount" (log2 element) :: gprs ["d"; "n"])
        ("execute_aarch64_instrs_vector_shift_" ^ direction ^ "_insert_sisd")
        (lane_arguments width element @ [unsigned "n"; amount])
    ) vector_geometries
  ) ["SLI_VEC", "left", false; "SRI_VEC", "right", true]

(* Signed/unsigned widening left shifts consume one 64-bit source half and
   produce Q128. part selects its lower/upper half; element is the source lane
   width (8/16/32) and the amount field covers 0..element-1. *)
let vector_widen_shift =
  List.concat_map (fun (operation, part, is_unsigned) ->
    List.map (fun element ->
      vector_entry "vector-widen-shift" operation 128 element
        (field "amount" (log2 element) :: gprs ["d"; "n"])
        "execute_aarch64_instrs_vector_shift_left_long"
        [unsigned "d"; number 64; number (64 / element); number element;
         unsigned "n"; number part; unsigned "amount"; boolean is_unsigned]
    ) [8; 16; 32]
  ) ["USHLL_VEC", 0, true; "USHLL2_VEC", 1, true;
     "SSHLL_VEC", 0, false; "SSHLL2_VEC", 1, false]

(* SHRN/RSHRN and their second-half forms fix a 64-bit result-half view and
   result element widths 8/16/32. part chooses the destination half, round
   chooses rounding, and the encoded amount+1 covers 1..result-element-width. *)
let vector_shift_narrow =
  List.concat_map (fun (operation, part, round) ->
    List.map (fun element ->
      vector_entry "vector-shift-narrow" operation 64 element
        (field "amount" (log2 element) :: gprs ["d"; "n"])
        "execute_aarch64_instrs_vector_shift_right_narrow_logical"
        [unsigned "d"; number 64; number (64 / element); number element;
         unsigned "n"; number part; boolean round; plus (unsigned "amount") (number 1)]
    ) [8; 16; 32]
  ) ["SHRN", 0, false; "SHRN2", 1, false; "RSHRN", 0, true; "RSHRN2", 1, true]

(* Shared indexed-multiply argument layout. A 16-bit element form has only
   four register-number bits (m0..m15) and two low-half lane bits; 32-bit
   elements have five register bits and one lane bit. high selects a source
   view/offset. suffix appends the instruction-specific flags/part selector. *)
let indexed_multiply family operation width element source suffix high =
  let parameters = gprs ["d"; "n"] @
    [field "m" (if element = 16 then 4 else 5);
     field "index" (if element = 16 then 2 else 1)] in
  entry family
    (vector_name operation width element ^ if high then "_HI" else "_LO")
    parameters
    (call source
      (lane_arguments width element @
       [number (if high then 128 else 64); encoded_index element high;
        unsigned "m"; unsigned "n"] @ suffix))

(* MUL/MLA/MLS have ordinary vector_small forms and indexed 16-/32-bit forms.
   accumulate chooses the product versus accumulating source body; subtract
   distinguishes MLS. Indexed forms enumerate both destination widths and
   both source halves using indexed_multiply's bounded operand fields. *)
let vector_multiply =
  List.concat_map (fun (operation, accumulate, subtract) ->
    let source = "execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_" ^
      if accumulate then "accum" else "product" in
    vector_forms vector_small "vector-multiply" operation (gprs ["d"; "n"; "m"])
      source (fun width element ->
        (* The product body's last parameter is poly (PMUL), not sub_op. *)
        lane_arguments width element @
        [unsigned "m"; unsigned "n"; boolean (if accumulate then subtract else false)]) @
    List.concat_map (fun width ->
      List.concat_map (fun element ->
        List.map (fun high ->
          let source = "execute_aarch64_instrs_vector_arithmetic_binary_element_mul_" ^
            if accumulate then "acc_int" else "int" in
          indexed_multiply "vector-multiply" operation width element source
            (if accumulate then [boolean subtract] else []) high
        ) [false; true]
      ) [16; 32]
    ) [64; 128]
  ) ["MUL_VEC", false, false; "MLA_VEC", true, false; "MLS_VEC", true, true]

(* Signed/unsigned widening products take 64-bit source halves and produce
   Q128. part selects lower/upper lanes; unsigned forms additionally have
   indexed 16-/32-bit versions. Adjust only their export names to reflect
   the 128-bit result: the constructed source call retains its 64-bit width. *)
let vector_multiply_long =
  List.concat_map (fun (operation, part, is_unsigned) ->
    List.map (fun element ->
      vector_entry "vector-multiply-long" operation 128 element (gprs ["d"; "n"; "m"])
        "execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product"
        [unsigned "d"; number 64; number (64 / element); number element;
         unsigned "m"; unsigned "n"; number part; boolean is_unsigned]
    ) [8; 16; 32] @
    (if not is_unsigned then [] else
      List.concat_map (fun element ->
        List.map (fun high ->
          let e = indexed_multiply "vector-multiply-long" operation 64 element
            "execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long"
            [number part; boolean true] high in
          {e with name = vector_name operation 128 element ^
             if high then "_HI" else "_LO"}
        ) [false; true]
      ) [16; 32])
  ) ["SMULL_VEC", 0, false; "SMULL2_VEC", 1, false;
     "UMULL_VEC", 0, true; "UMULL2_VEC", 1, true]

(* Widening multiply-add/subtract: fix source part, subtract and signedness
   independently. The last row flag controls catalogue inclusion of indexed
   forms, not a Sail instruction flag. Listed indexed forms reuse the same
   field restrictions and name/result-width convention as widening products. *)
let vector_multiply_accumulate_long =
  List.concat_map (fun (operation, part, subtract, is_unsigned, indexed) ->
    List.map (fun element ->
      vector_entry "vector-multiply-accumulate-long" operation 128 element
        (gprs ["d"; "n"; "m"])
        "execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum"
        [unsigned "d"; number 64; number (64 / element); number element;
         unsigned "m"; unsigned "n"; number part; boolean subtract; boolean is_unsigned]
    ) [8; 16; 32] @
    (if not indexed then [] else
      List.concat_map (fun element ->
        List.map (fun high ->
          let e = indexed_multiply "vector-multiply-accumulate-long" operation 64 element
            "execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long"
            [number part; boolean subtract; boolean is_unsigned] high in
          {e with name = vector_name operation 128 element ^
             if high then "_HI" else "_LO"}
        ) [false; true]
      ) [16; 32])
  ) ["SMLAL_VEC", 0, false, false, true; "SMLAL2_VEC", 1, false, false, true;
     "SMLSL_VEC", 0, true, false, false; "SMLSL2_VEC", 1, true, false, false;
     "UMLAL_VEC", 0, false, true, false; "UMLAL2_VEC", 1, false, true, false;
     "UMLSL_VEC", 0, true, true, true; "UMLSL2_VEC", 1, true, true, true]

(* Integer ADD/SUB and flag-setting/compare aliases at both widths. Compare
   forms have no d parameter: destination 31 keeps only the flag result.
   Immediate entries take an expanded word-sized value; shifted entries retain
   amount/ShiftType; extended entries enumerate all eight ExtendType values
   and amounts 0..4. NEG/NEGS fix the left source to 31 and subtraction=true,
   providing both unshifted and parameterized shifted forms. *)
let addsub =
  List.concat_map (fun (operation, subtract, flags, compare) ->
    both_widths (fun width ->
      let root = scalar_name operation width in
      let destination = if compare then number 31 else uint "d" in
      let operands = (if compare then [] else gprs ["d"]) @ gprs ["n"] in
      let shifted_operands = operands @ gprs ["m"] in
      let immediate =
        entry "addsub" (root ^ "_IMM") (operands @ [field "imm" width])
          (call "execute_aarch64_instrs_integer_arithmetic_add_sub_immediate"
            [destination; number width; id "imm"; uint "n"; boolean flags; boolean subtract]) in
      let shifted =
        entry "addsub" (root ^ "_SHIFT")
          (shifted_operands @ [field "amount" (if width = 32 then 5 else 6);
                               "kind", named_type "ShiftType"])
          (call "execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg"
            [destination; number width; uint "m"; uint "n"; boolean flags;
             uint "amount"; id "kind"; boolean subtract]) in
      let extended =
        List.concat_map (fun kind ->
          List.init 5 (fun amount ->
            entry "addsub" (Printf.sprintf "%s_EXT_%s_%d" root kind amount)
              shifted_operands
              (call "execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg"
                [destination; number width; id ("ExtendType_" ^ kind);
                 uint "m"; uint "n"; boolean flags; number amount; boolean subtract]))
        ) ["UXTB"; "UXTH"; "UXTW"; "UXTX"; "SXTB"; "SXTH"; "SXTW"; "SXTX"] in
      immediate :: shifted :: extended)
  ) ["ADD", false, false, false; "ADDS", false, true, false;
     "SUB", true, false, false; "SUBS", true, true, false;
     "CMN", false, true, true; "CMP", true, true, true] @
  List.concat_map (fun (operation, flags) ->
    both_widths (fun width ->
      let root = scalar_name operation width in
      let call_shift amount kind =
        call "execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg"
          [uint "d"; number width; uint "m"; number 31; boolean flags;
           amount; kind; boolean true] in
      [entry "addsub" root (gprs ["d"; "m"]) (call_shift (number 0) (id "ShiftType_LSL"));
       entry "addsub" (root ^ "_SHIFT")
         (gprs ["d"; "m"] @ [field "amount" (if width = 32 then 5 else 6);
                              "kind", named_type "ShiftType"])
         (call_shift (uint "amount") (id "kind"))])
  ) ["NEG", false; "NEGS", true]

(* Enter BFM/SBFM/UBFM through their decoders with width-specific N/sf bits
   and opcode1/0/2. W immediates are five-bit fields padded to the decoder's
   six-bit inputs. ASR/LSR fix imms=width-1; LSL builds wrapping bitvector
   expressions imms=(width-1)-amount and immr=0-amount before decoding. *)
let bitfield = both_widths (fun width ->
  let index_width = if width = 32 then 5 else 6 in
  let flag = bit_literal 1 (if width = 32 then 0 else 1) in
  let encoded value =
    if width = 32 then mk_exp (E_vector_append (bit_literal 1 0, value)) else value in
  let decoder operation =
    "decode_" ^ String.lowercase_ascii operation ^ "_aarch64_instrs_integer_bitfield" in
  let root operation opcode =
    entry "bitfield" (scalar_name operation width)
      (gprs ["d"; "n"] @ [field "immr" index_width; field "imms" index_width])
      (call (decoder operation)
        [id "d"; id "n"; encoded (id "imms"); encoded (id "immr"); flag;
         bit_literal 2 opcode; flag]) in
  let maximum = bit_literal index_width (width - 1) in
  let zero = bit_literal index_width 0 in
  let alias operation base opcode imms immr =
    entry "bitfield" (scalar_name operation width)
      (gprs ["d"; "n"] @ [field "amount" index_width])
      (call (decoder base)
        [id "d"; id "n"; encoded imms; encoded immr; flag; bit_literal 2 opcode; flag]) in
  [root "BFM" 1; root "SBFM" 0; root "UBFM" 2;
   alias "ASR" "SBFM" 0 maximum (id "amount");
   alias "LSR" "UBFM" 2 maximum (id "amount");
   alias "LSL" "UBFM" 2
     (operator "-" [maximum; id "amount"]) (operator "-" [zero; id "amount"])])

(* Conditional branch decoders retain encoded displacements for upstream
   sign-extension/scaling. BCOND exports a four-bit condition; named aliases
   fix it, including BCS/BHS and BCC/BLO synonyms. CBZ/CBNZ choose W/X via sf.
   TBZ/TBNZ fix the high position bit: the W group covers bits 0..31 and the
   X _HI group covers 32..63, with five low position bits kept symbolic. *)
let branch_conditional =
  let conditional = "decode_b_cond_aarch64_instrs_branch_conditional_cond" in
  [entry "branch-conditional" "arm_BCOND"
     [field "condition" 4; field "immediate" 19]
     (call conditional [id "condition"; id "immediate"])] @
  List.map (fun (operation, condition) ->
    entry "branch-conditional" ("arm_" ^ operation) [field "immediate" 19]
      (call conditional [bit_literal 4 condition; id "immediate"])
  ) ["BEQ", 0; "BNE", 1; "BCS", 2; "BHS", 2; "BCC", 3; "BLO", 3;
     "BMI", 4; "BPL", 5; "BVS", 6; "BVC", 7; "BHI", 8; "BLS", 9;
     "BGE", 10; "BLT", 11; "BGT", 12; "BLE", 13; "BAL", 14; "BNV", 15] @
  both_widths (fun width ->
    let high_bit = bit_literal 1 (if width = 32 then 0 else 1) in
    List.map (fun (operation, opcode) ->
      entry "branch-conditional" (scalar_name operation width)
        [field "t" 5; field "immediate" 19]
        (call ("decode_" ^ String.lowercase_ascii operation ^
               "_aarch64_instrs_branch_conditional_compare")
          [id "t"; id "immediate"; bit_literal 1 opcode; high_bit])
    ) ["CBZ", 0; "CBNZ", 1] @
    List.map (fun (operation, opcode) ->
      entry "branch-conditional" ("arm_" ^ operation ^ if width = 32 then "32" else "64_HI")
        [field "t" 5; field "bit_position" 5; field "immediate" 14]
        (call ("decode_" ^ String.lowercase_ascii operation ^
               "_aarch64_instrs_branch_conditional_test")
          [id "t"; id "immediate"; id "bit_position"; bit_literal 1 opcode; high_bit])
    ) ["TBZ", 0; "TBNZ", 1])

(* Immediate B/BL and register RET enter their decoders with fixed opcode
   fields. NOP/BTI_C are zero-parameter hint entries. BL_ABSOLUTE_EXECUTE
   directly selects the execution body with a 64-bit offset; its proof
   covers that helper, not the B decoder. *)
let branch_unconditional =
  List.map (fun (operation, opcode) ->
    entry "branch-basic" ("arm_" ^ operation) [field "immediate" 26]
      (call ("decode_" ^ (if operation = "B" then "b_uncond" else "bl") ^
             "_aarch64_instrs_branch_unconditional_immediate")
        [id "immediate"; bit_literal 1 opcode])
  ) ["B", 0; "BL", 1] @
  List.map (fun (operation, decoder, opcode) ->
    entry "branch-basic" ("arm_" ^ operation) (gprs ["n"])
      (call ("decode_" ^ decoder ^ "_aarch64_instrs_branch_unconditional_register")
        [bit_literal 5 0; id "n"; bit_literal 1 0; bit_literal 1 0;
         bit_literal 2 opcode; bit_literal 1 0])
  ) ["RET", "ret", 2] @
  (* The hint decoders take (op2 : bits(3), CRm : bits(4)); BTI c is
     CRm:op2 = 0b0100:0b010, hint 34. *)
  List.map (fun (operation, op2, crm) ->
    entry "hints" ("arm_" ^ operation) []
      (call ("decode_" ^ (if operation = "NOP" then "nop" else "bti") ^
             "_aarch64_instrs_system_hints")
        [bit_literal 3 op2; bit_literal 4 crm])
  ) ["NOP", 0, 0; "BTI_C", 2, 4] @
  [entry "branch-absolute-execute" "arm_BL_ABSOLUTE_EXECUTE" [field "offset" 64]
     (call "execute_aarch64_instrs_branch_unconditional_immediate"
       [id "BranchType_DIRCALL"; id "offset"])]

(* Multiple-register transfers use the original LD1/ST1/LD2/ST2/LD3/ST3
   decoders, not a sequence of independently chosen memory operations.
   The four-bit opcode selects the number of whole registers (LD1/ST1) or
   the interleaved structure (LD2/ST2/LD3/ST3). size chooses the lane width;
   Q chooses D64 or Q128. The source decoder derives the register count,
   lane count, immediate increment and consecutive indices modulo 32.

   The root names describe the corresponding HOL instruction: for example,
   arm_LDP128_SIMD_LD1_E16_POSTR is HOL's two-Q-register LDP through the
   LD1 encoding, with 16-bit lanes and register post-increment. Its operands
   t,n,m are encoded Rt,Rn,Rm, in HOL destination/base/offset order. POSTI
   fixes Rm=31; POSTR keeps every five-bit Rm, including 31. Neither form
   assumes distinct registers or replaces source overlap/fault checks.
   NO retains the no-writeback decoder's unobserved unknown offset value.

   These are encoded-instruction claims. Ordinary pair instructions below
   have two independent destinations; LD1/ST1 structures have consecutive
   destinations. Agreement proofs must preserve that distinction and show
   that little-endian lane transfers give HOL's whole-register effects. *)
let is_load operation = String.starts_with ~prefix:"LD" operation

let memory_multiple family operation width mnemonic opcode element mode =
  let load = is_load operation in
  let registers = gprs ["t"; "n"] in
  let size = bit_literal 2 (log2 element - 3) in
  let l = bit_literal 1 (if load then 1 else 0) in
  let q = bit_literal 1 (if width = 128 then 1 else 0) in
  let parameters, suffix, arguments = match mode with
    | "NO" -> registers, "no_wb",
        [id "t"; id "n"; size; bit_literal 4 opcode; l; q]
    | "POSTI" -> registers, "post_inc",
        [id "t"; id "n"; size; bit_literal 4 opcode; bit_literal 5 31; l; q]
    | "POSTR" -> registers @ gprs ["m"], "post_inc",
        [id "t"; id "n"; size; bit_literal 4 opcode; id "m"; l; q]
    | _ -> invalid_arg "unsupported AArch64 multiple-transfer addressing mode" in
  let name = Printf.sprintf "arm_%s%d_SIMD_%s_E%d_%s"
    operation width ("LD" ^ mnemonic) element mode in
  entry family name parameters
    (call ("decode_" ^ (if load then "ld" else "st") ^ mnemonic ^
      "_advsimd_mult_aarch64_instrs_memory_vector_multiple_" ^ suffix) arguments)

(* Single GPR/SIMD transfers and one-register LD1/ST1 structure forms.
   Keep encoded immediates symbolic: nine bits for signed pre/post/unscaled
   forms, twelve for unsigned immediate forms. Register-offset entries fix
   option=3 and choose scaled/unscaled S. opcode/size distinguish load/store,
   byte/GPR/SIMD width, including the special Q128 opcode.

   Structure forms enumerate element sizes and no-writeback/immediate-post/
   register-post modes. Immediate post-increment uses index31 in its decoder.
   The upstream decoder supplies immediate expansion and instruction checks.
   Catalogue inclusion is not execution support: unsupported memory/platform
   leaves below retain their bodies, and exporting a reached unsupported
   operation fails rather than assuming a successful transfer. *)
let memory_single =
  let byte operation = operation = "LDRB" || operation = "STRB" in
  let opcode operation vector width =
    bit_literal 2 (if vector && width = 128 then (if is_load operation then 3 else 2)
                   else if is_load operation then 1 else 0) in
  let size width = bit_literal 2 (match width with 128 | 8 -> 0 | 32 -> 2 | 64 -> 3
    | _ -> invalid_arg "unsupported AArch64 memory transfer width") in
  let root operation width vector form parameters decoder arguments =
    let name = Printf.sprintf "arm_%s%d_%s_%s" operation width
      (if vector then "SIMD" else "GPR") form in
    entry "memory-single" name parameters (call decoder arguments) in
  let immediate operation width vector mode =
    let mnemonic = String.lowercase_ascii operation ^
      (if byte operation then "_imm" else "_imm_" ^ if vector then "fpsimd" else "gen") in
    let suffix = match mode with "POST" -> "immediate_signed_post_idx"
      | "PRE" -> "immediate_signed_pre_idx" | "UIMM" -> "immediate_unsigned"
      | _ -> assert false in
    root operation width vector mode
      (gprs ["t"; "n"] @ [field "imm" (if mode = "UIMM" then 12 else 9)])
      ("decode_" ^ mnemonic ^ "_aarch64_instrs_memory_single_" ^
       (if vector then "simdfp_" else "general_") ^ suffix)
      [id "t"; id "n"; id "imm"; opcode operation vector width;
       size (if byte operation then 8 else width)] in
  let register operation width vector shifted =
    let mnemonic = String.lowercase_ascii operation ^
      (if byte operation then "_reg" else "_reg_" ^ if vector then "fpsimd" else "gen") in
    root operation width vector (if shifted then "REGS" else "REG0") (gprs ["t"; "n"; "m"])
      ("decode_" ^ mnemonic ^ "_aarch64_instrs_memory_single_" ^
       (if vector then "simdfp" else "general") ^ "_register")
      [id "t"; id "n"; bit_literal 1 (if shifted then 1 else 0); bit_literal 3 3;
       id "m"; opcode operation vector width; size (if byte operation then 8 else width)] in
  let unscaled operation width vector =
    let mnemonic = if byte operation then (if is_load operation then "ldurb" else "sturb")
      else (if is_load operation then "ldur_" else "stur_") ^ (if vector then "fpsimd" else "gen") in
    root operation width vector "UNSCALED" (gprs ["t"; "n"] @ [field "imm" 9])
      ("decode_" ^ mnemonic ^ "_aarch64_instrs_memory_single_" ^
       (if vector then "simdfp" else "general") ^ "_immediate_signed_offset_normal")
      [id "t"; id "n"; id "imm"; opcode operation vector width;
       size (if byte operation then 8 else width)] in
  let structure operation width element mode =
    memory_multiple "memory-single" operation width "1" 7 element mode in
  let scalar operation width =
    List.map (immediate operation width false) ["POST"; "PRE"; "UIMM"] @
    [register operation width false false] @
    (if byte operation then [] else [register operation width false true]) @
    [unscaled operation width false] in
  let vector operation width =
    List.map (immediate operation width true) ["POST"; "PRE"; "UIMM"] @
    (if width = 128 then
       [register operation width true false; register operation width true true;
        unscaled operation width true] else []) @
    List.concat_map (fun element ->
      List.map (structure operation width element) ["NO"; "POSTI"; "POSTR"]
    ) [8; 16; 32; 64] in
  List.concat_map (fun operation ->
    List.concat_map (scalar operation) [32; 64] @
    List.concat_map (vector operation) [64; 128]
  ) ["LDR"; "STR"] @
  List.concat_map (fun operation -> scalar operation 32) ["LDRB"; "STRB"]

(* LDP/STP: W32/X64 GPR pairs and D64/Q128 SIMD pairs, plus the two-Q
   LD1/ST1 encodings represented by the same HOL definitions.
   GPR opc=0/2 selects unsigned W32/X64; SIMD opc=1/2 selects D64/Q128.
   Rt,Rt2,Rn and signed imm7 remain symbolic, so index 31, all offsets,
   writeback overlap and duplicate destinations reach the original checks.
   Our parameter order t,t2,n,imm matches HOL's two destinations, base and
   encoded offset; the Sail decoder expects t,n,t2,imm,L,opc. *)
let memory_pair =
  let pair operation width vector mode =
    let suffix = match mode with
      | "POST" -> "post_idx" | "PRE" -> "pre_idx" | "OFFSET" -> "offset"
      | _ -> assert false in
    let view, model = if vector then "SIMD", "simdfp" else "GPR", "general" in
    let opc = if vector then (if width = 64 then 1 else 2)
      else if width = 32 then 0 else 2 in
    let source = "decode_" ^ String.lowercase_ascii operation ^
      (if vector then "_fpsimd" else "_gen") ^
      "_aarch64_instrs_memory_pair_" ^ model ^ "_" ^ suffix in
    entry "memory-pair"
      (Printf.sprintf "arm_%s%d_%s_%s" operation width view mode)
      (gprs ["t"; "t2"; "n"] @ [field "imm" 7])
      (call source [id "t"; id "n"; id "t2"; id "imm";
        bit_literal 1 (if is_load operation then 1 else 0); bit_literal 2 opc]) in
  List.concat_map (fun operation ->
    List.concat_map (fun (width, vector) ->
      List.map (pair operation width vector) ["POST"; "PRE"; "OFFSET"]
    ) [32, false; 64, false; 64, true; 128, true] @
    List.concat_map (fun element ->
      List.map (memory_multiple "memory-pair" operation 128 "1" 10 element)
        ["NO"; "POSTI"; "POSTR"]
    ) [8; 16; 32; 64]
  ) ["LDP"; "STP"]

(* HOL's LDP4/STP4 are LD1/ST1 with opcode=2: four whole registers.
   Every size encoding is retained, including D64 with 64-bit lanes.
   The decoder admits that case because this is one structure element,
   not four-way interleaving. NO/POSTI/POSTR give increments 0/32/64 or
   the selected X register; the source computes the exact byte count. *)
let memory_four =
  List.concat_map (fun operation ->
    List.concat_map (fun width ->
      List.concat_map (fun element ->
        List.map (memory_multiple "memory-four" operation width "1" 2 element)
          ["NO"; "POSTI"; "POSTR"]
      ) [8; 16; 32; 64]
    ) [64; 128]
  ) ["LDP4"; "STP4"]

(* LD2/ST2 use opcode=8, LD3/ST3 opcode=4. These are lane-interleaved
   structures, with consecutive registers modulo 32. D64 with 64-bit
   lanes is reserved in both Sail and HOL's decoder and is not requested.
   HOL decodes LD2/ST2 only with immediate post-increment. LD3/ST3 also
   accept a register offset. All other encoded operands remain symbolic. *)
let memory_interleaved family mnemonic opcode operations modes =
  List.concat_map (fun operation ->
    List.concat_map (fun width ->
      List.concat_map (fun element ->
        List.map (memory_multiple family operation width mnemonic opcode element) modes
      ) (if width = 64 then [8; 16; 32] else [8; 16; 32; 64])
    ) [64; 128]
  ) operations

let memory_structure2 =
  memory_interleaved "memory-structure2" "2" 8 ["LD2"; "ST2"] ["POSTI"]

let memory_structure3 =
  memory_interleaved "memory-structure3" "3" 4 ["LD3"; "ST3"] ["POSTI"; "POSTR"]

(* LD1R loads one lane and replicates it through D64/Q128. HOL's decoder
   uses only immediate post-increment: Rm=31, increment=element width/8.
   opcode=6, R=0, L=1 and S=0 select replication of one structure element.
   The original decoder's undefined lane index remains in its body; the
   replicate execution path never observes that index. Selecting a fixed
   index ourselves would disguise this required source-dataflow property. *)
let memory_replicate =
  List.concat_map (fun width ->
    List.map (fun element ->
      entry "memory-replicate"
        (Printf.sprintf "arm_LD1R%d_SIMD_LD1R_E%d_POSTI" width element)
        (gprs ["t"; "n"])
        (call "decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc"
          [id "t"; id "n"; bit_literal 2 (log2 element - 3); bit_literal 1 0;
           bit_literal 3 6; bit_literal 5 31; bit_literal 1 0;
           bit_literal 1 1; bit_literal 1 (if width = 128 then 1 else 0)])
    ) [8; 16; 32; 64]
  ) [64; 128]

(* Long subtraction reads the selected 64-bit half of both source vectors.
   Wide add/subtract reads a complete Q128 first operand and one narrow half
   of the second. Both produce Q128 with double-width lanes. Widths, source
   half, signed interpretation and subtraction are the only fixed selectors;
   all five-bit register fields, including every overlap, remain symbolic. *)
let vector_addsub_widen =
  List.concat_map (fun (operation, wide, part, subtract, is_unsigned) ->
    List.map (fun element ->
      vector_entry "vector-addsub-widen" operation 128 element
        (gprs ["d"; "n"; "m"])
        ("execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_" ^
         if wide then "wide" else "long")
        [unsigned "d"; number 64; number (64 / element); number element;
         unsigned "m"; unsigned "n"; number part; boolean subtract;
         boolean is_unsigned]
    ) [8; 16; 32]
  ) ["SSUBL", false, 0, true, false; "SSUBL2", false, 1, true, false;
     "USUBL", false, 0, true, true; "USUBL2", false, 1, true, true;
     "SADDW", true, 0, false, false; "SADDW2", true, 1, false, false;
     "SSUBW", true, 0, true, false; "SSUBW2", true, 1, true, false;
     "USUBW", true, 0, true, true; "USUBW2", true, 1, true, true]

(* INS preserves every destination lane except the selected Q128 lane.
   LO/HI entries follow the actual source view chosen by the decoder:
   the source is D64 below lane 64/esize and Q128 above it. The destination
   field covers every lane of Q128; the source index covers every lane of
   the selected half. For esize 64 that index is implicit 0 or 1.
   INS_GEN uses the same complete destination-lane field and calls the
   upstream integer-source body, which reads esize low bits of the GPR. *)
let vector_insert =
  List.concat_map (fun element ->
    List.map (fun high ->
      entry "vector-insert"
        (vector_name "INS" 128 element ^ if high then "_HI" else "_LO")
        (gprs ["d"; "n"] @ [field "dest" (log2 (128 / element))] @ index_field element)
        (call "execute_aarch64_instrs_vector_transfer_vector_insert"
          [unsigned "d"; unsigned "dest"; number element;
           number (if high then 128 else 64); unsigned "n"; encoded_index element high])
    ) [false; true] @
    [vector_entry "vector-insert" "INS_GEN" 128 element
       (gprs ["d"; "n"] @ [field "dest" (log2 (128 / element))])
       "execute_aarch64_instrs_vector_transfer_integer_insert"
       [unsigned "d"; number 128; number element; unsigned "dest"; unsigned "n"]]
  ) [8; 16; 32; 64]

(* Unsigned rounding halving add: six non-64-bit-lane geometries. The actual
   upstream body adds the two unsigned lane values and one before shifting
   right by one. No rounded-sum formula is constructed in this table. *)
let vector_round_halving =
  vector_forms vector_small "vector-round-halving" "URHADD_VEC" (gprs ["d"; "n"; "m"])
    "execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding"
    (fun width element -> lane_arguments width element @
      [unsigned "m"; unsigned "n"; boolean true])

(* USHL interprets the low byte of each amount lane as a signed shift.
   All lane values remain symbolic. Fix rounding=false, saturation=false
   and unsigned=true; positive/negative shifts remain in the source body. *)
let vector_variable_shift =
  vector_forms vector_geometries "vector-variable-shift" "USHL_VEC" (gprs ["d"; "n"; "m"])
    "execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd"
    (fun width element -> lane_arguments width element @
      [unsigned "m"; unsigned "n"; boolean false; boolean false; boolean true])

(* FPBITS entries select or transfer bit patterns, not numerical conversion.
   FCSEL32/64 retains every condition and vector field. Move entries select
   only MOV_FtoI/MOV_ItoF arms; their common enable and FPCR/IsMerging reads
   remain in the source closure. The move arms do not inspect rounding or
   is_unsigned; explicit literals make those otherwise irrelevant arguments
   well typed. For the high half, the decoder sets part to 1 and fltsize
   from 128 to 64 before calling this execute function, as these entries do. *)
let vector_fpbits =
  List.map (fun width ->
    entry "fp-select" (scalar_name "FCSEL" width)
      (field "condition" 4 :: gprs ["d"; "n"; "m"])
      (call "execute_aarch64_instrs_float_move_fp_select"
        [id "condition"; unsigned "d"; number width; unsigned "m"; unsigned "n"])
  ) [32; 64] @
  List.map (fun (operation, fltsize, intsize, part) ->
    entry "vector-fpbits"
      (Printf.sprintf "arm_%s%d_%s" operation intsize
         (if part = 0 then "LO" else "HI"))
      (gprs ["d"; "n"])
      (call "execute_aarch64_instrs_float_convert_int"
        [unsigned "d"; number fltsize; number intsize; unsigned "n";
         id ("FPConvOp_MOV_" ^ if operation = "FMOV_FtoI" then "FtoI" else "ItoF");
         number part; id "FPRounding_TIEEVEN"; boolean false])
  ) ["FMOV_FtoI", 32, 32, 0; "FMOV_FtoI", 64, 64, 0;
     "FMOV_FtoI", 64, 64, 1; "FMOV_ItoF", 64, 64, 0;
     "FMOV_ItoF", 64, 64, 1]

(* Byte-table lookup reads one, two or three consecutive complete Q128
   registers, with source register wrapping supplied by the upstream body.
   Keep the first table index and every byte index symbolic; out-of-range
   handling is source control flow. D64/Q128 destination widths are both
   exported. HOL TBL2/TBL3 claims must instantiate the consecutive layout;
   these entries do not claim agreement for arbitrary independent tables. *)
let vector_table =
  List.concat_map (fun regs ->
    List.map (fun width ->
      entry "vector-table"
        (scalar_name ("TBL" ^ if regs = 1 then "" else string_of_int regs) width)
        (gprs ["d"; "n"; "m"])
        (call "execute_aarch64_instrs_vector_transfer_vector_table"
          [unsigned "d"; number width; number (width / 8); boolean true;
           unsigned "m"; unsigned "n"; number regs])
    ) [64; 128]
  ) [1; 2; 3]

(* Signed-to-unsigned narrowing saturation uses the actual UnsignedSatQ
   helper and source FPSR.QC update. Low/high result halves have distinct
   entries; the high half preserves old low64 through Vpart_set. Amount
   fields cover the complete decoded 1..esize range. The common translator
   excludes FPSR writes from the observation because armstate omits FPSR;
   it retains saturation calculations, reads and all other effects. *)
let vector_saturating_narrow =
  List.concat_map (fun (operation, part, round) ->
    List.map (fun element ->
      vector_entry "vector-saturating-narrow" operation 64 element
        (field "amount" (log2 element) :: gprs ["d"; "n"])
        "execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd"
        [unsigned "d"; number 64; number (64 / element); number element;
         unsigned "n"; number part; boolean round;
         plus (unsigned "amount") (number 1)]
    ) [8; 16; 32]
  ) ["SQSHRUN", 0, false; "SQSHRUN2", 1, false;
     "SQRSHRUN", 0, true; "SQRSHRUN2", 1, true]

(* Saturating signed doubled-product high halves, rounded or unrounded.
   Ordinary vector forms use 16-/32-bit lanes at both data widths. Indexed
   forms reuse the decoder's four-/five-bit source register and bounded
   LO/HI lane fields. SignedSatQ remains a translated source dependency.
   The common translator explicitly excludes FPSR writes, not their value
   evaluation or other effects. Agreement does not cover physical FPSR. *)
let vector_doubling =
  List.concat_map (fun (operation, round) ->
    List.concat_map (fun width ->
      List.concat_map (fun element ->
        vector_entry "vector-doubling" operation width element
          (gprs ["d"; "n"; "m"])
          "execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd"
          (lane_arguments width element @ [unsigned "m"; unsigned "n"; boolean round]) ::
        List.map (fun high ->
          indexed_multiply "vector-doubling" operation width element
            "execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd"
            [boolean round] high
        ) [false; true]
      ) [16; 32]
    ) [64; 128]
  ) ["SQDMULH_VEC", false; "SQRDMULH_VEC", true]

(* Polynomial products use PolynomialMult from the upstream helper closure.
   PMUL has byte lanes at both data widths. PMULL/PMULL2 enter the genuine
   decoder for 8- or 64-bit source lanes and source half 0 or 1; this keeps its
   HaveBit128PMULLExt guard for 64-bit lanes, rather than reconstructing a check
   or assuming a decoded execute call silently includes the feature guard. *)
let vector_poly =
  List.map (fun width ->
    vector_entry "vector-polynomial-multiply" "PMUL_VEC" width 8 (gprs ["d"; "n"; "m"])
      "execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product"
      [unsigned "d"; number width; number (width / 8); number 8;
       unsigned "m"; unsigned "n"; boolean true]
  ) [64; 128] @
  List.concat_map (fun (operation, part) ->
    List.map (fun element ->
      entry "vector-poly" (vector_name operation 128 element) (gprs ["d"; "n"; "m"])
        (call "decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly"
          [id "d"; id "n"; id "m"; bit_literal 2 (if element = 8 then 0 else 3);
           bit_literal 1 part])
    ) [8; 64]
  ) ["PMULL_VEC", 0; "PMULL2_VEC", 1]

(* Complete constructed requests. Catalogue membership and Sail
   typechecking do not show that a form is supported or proved.
   The catalogue test fixes every name, operand domain, mode and source call
   in one reviewed fingerprint; selected risks also have independent checks. *)
let entries =
  carry @ select @ multiply @ multiply_long @ multiply_high @ compare @ address @
  shift @ reverse @ count @ extract @ move @ logical @ crypto_bitwise @ aes @
  vector_logical @ vector_addsub @ vector_abs @ vector_compare @ vector_count @
  vector_extract @ vector_narrow @ vector_move @ vector_reverse @ vector_umov @
  vector_reduce @ vector_minmax @ vector_pair @ vector_permute @ sha2 @
  vector_duplicate_general @ vector_duplicate_element @
  vector_duplicate_element_scalar @ vector_left_shift @
  vector_right_shift @ vector_shift_insert @ vector_widen_shift @ vector_shift_narrow @
  vector_multiply @ vector_multiply_long @ vector_multiply_accumulate_long @
  addsub @ bitfield @ branch_conditional @ branch_unconditional @ memory_single @
  memory_pair @ memory_four @ memory_structure2 @ memory_structure3 @ memory_replicate @
  vector_addsub_widen @ vector_insert @ vector_round_halving @
  vector_variable_shift @ vector_fpbits @ vector_table @
  vector_saturating_narrow @ vector_doubling @ vector_poly

(* Each family's roots are its entries, in table order; every entry belongs
   to exactly one family, so each model holds only the forms its suite
   proves. *)
let family_roots =
  let families = List.sort_uniq String.compare (List.map (fun e -> e.family) entries) in
  let roots_for family =
    List.filter_map (fun e -> if e.family = family then Some e.name else None) entries in
  List.map (fun family -> family, roots_for family) families

(* Deliberate flat-state boundaries with existing HOL interpretations.
   The frontend retains the original upstream declarations and types.
   Arithmetic helpers such as AddWithCarry remain upstream bodies.

   A true row permits an impure value-producing call at that boundary.
   A false row is not an effect permission: its implementation must use
   the statement path or a pure call. The translator still checks each
   boundary's actual signature, argument bounds and computation context. *)
(* A fault boundary ends the whole instruction, including calls inside
   helpers and loops. Its source caller and reachability conditions remain.
   These are architectural exception-entry routines, not generic Sail
   throws or EndOfInstruction (which also ends normal NOP outcomes).
   Currently only SP-alignment fault entry is interpreted. *)
let faults = ["AArch64_SPAlignmentFault"]

let contracts = [
  "X_read", true; "X_set", false; "SP_read", true; "SP_set", false;
  "V_read", true; "V_set", false;
  "CheckFPAdvSIMDEnabled64", false; "CheckFPEnabled64", false;
  "AArch64_CheckFPAdvSIMDEnabled", false; "BranchTo", false; "BranchNotTaken", false;
  "IsFeatureImplemented", true; "SCTLR_read__1", true;
  "CreateAccDescGPR", true; "CreateAccDescASIMD", true;
  "Mem_read", true; "Mem_set", false; "Mem_read__1", true; "Mem_set__1", false;
  "BigEndian", true; "EndOfInstruction", false
]
let cuts = List.map fst contracts @ faults

(* The fields of ProcState that the HOL view of PSTATE keeps, in order. *)
let pstate_fields = ["N"; "Z"; "C"; "V"; "EL"; "BTYPE"; "nRW"]

(* Source names that sail_plugin_hol_light.ml interprets without a cut,
   after checking their declared types, with the translator case:
     _PC                read as the instruction's entry PC, never written:
                        register, computation (E_assign);
     PSTATE             N/Z/C/V are the NF/ZF/CF/VF flags, the other
                        pstate_fields come from reg_PSTATE and the remaining
                        ProcState fields are dropped: hol_type, register,
                        arm_pstate_field, assign; whole writes are refused;
     SPESampleInFlight  reads as false: register;
     FPSR, BTypeNext, BTypeCompatible
                        writes are omitted: assign (omit_unrepresented_write);
     Error_Undefined    throw(Error_Undefined()) is a fault: computation (E_throw);
     FEAT_GCS           IsFeatureImplemented answers false: call;
     FEAT_LSE2          IsFeatureImplemented reads FlatHaveLSE2: call.
   BranchType, AccessDescriptor and the access enums must keep their
   declared shapes: arm_branch_type, arm_access_descriptor_type. *)
