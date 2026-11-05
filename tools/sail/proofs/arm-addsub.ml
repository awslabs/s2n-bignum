(* Actual immediate, shifted-register and extended-register execute bodies.
   Arithmetic flags, SP versus ZR, overlapping operands and all legal shifts
   are included. Immediate values are full-width predecoded operands.
   W32 UXTX/SXTX and shifted ROR are stronger execute-domain claims, not a
   claim that the architectural decoder admits those parameter choices. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
(* Declare the 512 supplied bodies with fresh-model.ml, which skips HOL's
   search for an earlier equivalent definition and unfolds the selected
   helper branches by value. With HOL's own commands this suite runs
   several times longer. *)
loadt "tools/sail/proofs/fresh-model.ml";;
module Sail_addsub_model = struct
open Sail_hl_fresh_model;;
loadt "tools/sail/_build/arm-addsub.ml";;
end;;
include Sail_addsub_model;;
needs "tools/sail/proofs/arm-lemmas.ml";;
needs "tools/sail/proofs/arm-logical-lemmas.ml";;
needs "tools/sail/proofs/tuple-apply-conv.ml";;
needs "tools/sail/proofs/proof-fork.ml";;

let SAIL_HL_ARM_ADDSUB_SP_LOW32 = prove
 (`!x:64 word. word_subword x (0,32):32 word = word_zx x`,
  CONV_TAC WORD_BLAST);;

let SAIL_HL_ARM_ADDSUB_FULL_LOW32 = prove
 (`!x:32 word. word_subword x (0,32):32 word = x`,
  CONV_TAC WORD_BLAST);;
let SAIL_HL_ARM_ADDSUB_FULL_LOW64 = prove
 (`!x:64 word. word_subword x (0,64):64 word = x`,
  CONV_TAC WORD_BLAST);;

let SAIL_HL_ARM_ADDSUB_READ_EXTENDED = prove
 (`!r:(armstate,N word)component. !kind s.
   read (Extendedreg r kind) s = extendreg_operation kind (read r s)`,
  REWRITE_TAC[Extendedreg_DEF; read]);;

let SAIL_HL_ARM_ADDSUB_SUB_SIGNED_SUM = prove
 (`!x y:N word.
   (ival x + ival(word_not y)) + &1 = ival x - ival y`,
  REWRITE_TAC[IVAL_WORD_NOT] THEN INT_ARITH_TAC);;

let SAIL_HL_ARM_ADDSUB_READ_WREG = prove
 (`!m:5 word. !s:armstate.
   read (WREG' m) s = word_zx(read (XREG' m) s)`,
  REWRITE_TAC[WREG'; XREG'; WREG; READ_ZEROTOP_32]);;

(* Truncating back to 32 bits makes word/doubleword extension an identity.
   Several ExtendReg source expressions therefore share the same left side
   after same-width casts are simplified. Keep their proved right sides in
   one canonical form as well, rather than introducing nested cast chains. *)
let SAIL_HL_ARM_ADDSUB_EXTEND32_ID_LEMMAS = map (fun kind ->
  let statement = parse_term (Printf.sprintf
    "!x:32 word. (extendreg_operation %s x:32 word) = x" kind) in
  REWRITE_RULE[extendreg_operation]
    (prove(statement,
       REWRITE_TAC[extendreg_operation] THEN CONV_TAC WORD_BLAST))
 ) ["UXTW";"UXTX";"SXTW";"SXTX"];;

(* The 64-bit decoder uses W registers for byte/halfword/word extension,
   whereas actual ExtendReg reads X and then extracts only those low bits.
   Do not replace the decoder's component choices with different claims. *)
let SAIL_HL_ARM_ADDSUB_EXTEND_LOW32_LEMMAS = map (fun kind ->
  let statement = parse_term (Printf.sprintf
    "!x:64 word. (extendreg_operation %s x:64 word) = \
     (extendreg_operation %s (word_zx x:32 word):64 word)" kind kind) in
  REWRITE_RULE[extendreg_operation]
    (prove(statement,
       REWRITE_TAC[extendreg_operation] THEN CONV_TAC WORD_BLAST))
 ) ["UXTB";"UXTH";"UXTW";"SXTB";"SXTH";"SXTW"];;

(* All eight extension kinds and five legal shifts at each arithmetic width.
   These are mathematical identities between extract/concatenate/extend
   expressions and extend-then-shift. The source expression remains in each
   generated definition and must rewrite to these identities to prove the
   instruction claim. For shift zero there is no fictitious HOL 0 word. *)
let SAIL_HL_ARM_ADDSUB_EXTEND_KINDS =
 ["UXTB",8; "UXTH",16; "UXTW",32; "UXTX",64;
  "SXTB",8; "SXTH",16; "SXTW",32; "SXTX",64];;

let SAIL_HL_ARM_ADDSUB_EXTEND_LEMMAS = flat(map
 (fun width -> flat(map (fun (kind,size) ->
   map (fun shift ->
     let len = min size (width - shift) in
     let extension = if kind.[0] = 'U' then "word_zx" else "word_sx" in
     let low = Printf.sprintf "(word_subword x (0,%d):%d word)" len len in
     let source = if shift = 0 then low else Printf.sprintf
       "(word_join %s (word 0:%d word):%d word)" low shift (len+shift) in
     let statement = parse_term (Printf.sprintf
       "!x:%d word. (%s %s:%d word) = \
        word_shl (extendreg_operation %s x:%d word) %d"
       width extension source width kind width shift) in
     let theorem = prove(statement,
       GEN_TAC THEN REWRITE_TAC[extendreg_operation; WORD_EQ_BITS_ALT] THEN
       CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
       CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
       REWRITE_TAC[BIT_WORD_ZX; BIT_WORD_SX; BIT_WORD_JOIN;
                   BIT_WORD_SUBWORD; BIT_WORD_SHL; BIT_WORD_0] THEN
       CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
       CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]) in
     (* The instruction normalizer removes same-width casts and whole-word
        extracts before applying these facts. Canonicalize the proved fact
        in exactly that way so its left side still matches source terms. *)
     REWRITE_RULE
       ([extendreg_operation; WORD_ZX_TRIVIAL; WORD_SX_TRIVIAL;
        SAIL_HL_ARM_ADDSUB_FULL_LOW32; SAIL_HL_ARM_ADDSUB_FULL_LOW64;
        SAIL_HL_ARM_ADDSUB_SP_LOW32] @
        SAIL_HL_ARM_ADDSUB_EXTEND32_ID_LEMMAS) theorem
   ) [0;1;2;3;4]
 ) SAIL_HL_ARM_ADDSUB_EXTEND_KINDS)) [32;64]);;
assert(length SAIL_HL_ARM_ADDSUB_EXTEND_LEMMAS = 80);;

(* ASM_REWRITE_TAC with one basic conversion replaced. HOL's basic
   GEN_BETA_CONV reduces a paired-let application by substituting
   projections through the whole body, once per tuple field. The
   unfolded instruction relations here consist mostly of such bodies.
   SAIL_HL_TUPLE_APPLY_CONV proves the same reduction from a small
   schema, up to bound-variable names, and falls back to GEN_BETA_CONV.
   Every rewrite and every other basic conversion is unchanged. *)
let SAIL_HL_ARM_ADDSUB_ASM_REWRITE_TAC =
  let tuple = SAIL_HL_TUPLE_APPLY_CONV ~contract_result:true () in
  let beta term = try tuple term with Failure _ -> GEN_BETA_CONV term in
  let cache = ref None in
  let basic_net () =
    let rewrites = basic_rewrites() and conversions = basic_convs() in
    match !cache with
    | Some(rewrites',conversions',net)
        when rewrites' == rewrites && conversions' == conversions -> net
    | _ ->
        let net = itlist (net_of_thm true) rewrites
          (itlist (fun (name,(pattern,conversion)) ->
             net_of_conv pattern
               (if name = "GEN_BETA_CONV" then beta else conversion))
             conversions empty_net) in
        cache := Some(rewrites,conversions,net);
        net in
  ASM(fun theorems ->
    CONV_TAC(GENERAL_REWRITE_CONV true TOP_DEPTH_CONV (basic_net()) theorems));;

let SAIL_HL_ARM_ADDSUB_NORM definition =
  SAIL_HL_ARM_ADDSUB_ASM_REWRITE_TAC
    [definition; BETA_THM; arm_ADD; arm_ADDS; arm_SUB; arm_SUBS;
     arm_CMN; arm_CMP; arm_NEG; arm_NEGS;
     LET_DEF; LET_END_DEF; FST; SND; NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ;
     INT_OF_NUM_REM; WORD_ZX_TRIVIAL; WORD_SX_TRIVIAL;
     SAIL_HL_ARM_LOGICAL_KIND; sail_hl_type_ShiftType_DISTINCT;
     SAIL_HL_ARM_LOGICAL_READ_SHIFT; regshift_operation;
     SAIL_HL_ARM_ADDSUB_READ_EXTENDED; extendreg_operation;
     SAIL_HL_ARM_LOGICAL_SP_DEST; GSYM SAIL_HL_ARM_LOGICAL_FIELD31;
     XREG'; WREG'; WSP; READ_ZEROTOP_32; READ_RVALUE;
     SAIL_HL_ARM_ADDSUB_SP_LOW32;
     SAIL_HL_ARM_ADDSUB_FULL_LOW32; SAIL_HL_ARM_ADDSUB_FULL_LOW64] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ; INT_OF_NUM_REM] THEN
  REWRITE_TAC[REWRITE_RULE[WREG';XREG'] SAIL_HL_ARM_ADDSUB_READ_WREG] THEN
  ASM_REWRITE_TAC SAIL_HL_ARM_ADDSUB_EXTEND_LEMMAS THEN
  ASM_REWRITE_TAC SAIL_HL_ARM_ADDSUB_EXTEND32_ID_LEMMAS THEN
  ASM_REWRITE_TAC SAIL_HL_ARM_ADDSUB_EXTEND_LOW32_LEMMAS THEN
  ASM_SIMP_TAC[MOD_LT; SAIL_HL_ARM_LOGICAL_ROTATE32;
               SAIL_HL_ARM_LOGICAL_ROTATE64] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC
    [IWORD_INT_ADD; GSYM WORD_IWORD; WORD_VAL; WORD_ADD_0;
     SAIL_HL_ARM_NOT_FLAG; GSYM WORD_BITVAL;
     GSYM VAL_EQ; VAL_WORD_0; INT_OF_NUM_ADD; INT_OF_NUM_EQ;
     INT_ADD_LID; INT_ADD_RID; ADD_CLAUSES;
     SAIL_HL_ARM_ADDSUB_SUB_SIGNED_SUM;
     SAIL_HL_ARM_SUB_RESULT;
     SAIL_HL_ARM_MSB32; SAIL_HL_ARM_MSB64] THEN
  REWRITE_TAC[WORD_ADD_AC; ADD_AC; INT_ADD_AC; EQ_SYM_EQ;
     SAIL_HL_ARM_PACKED_REWRITES;
     SAIL_HL_ARM_SUB_FLAGS] THEN
  REWRITE_TAC[assign; SEQ] THEN
  ASM_SIMP_TAC[SAIL_HL_ARM_XFLAG_COMMUTE;
               SAIL_HL_ARM_WFLAG_COMMUTE] THEN
  ASM_REWRITE_TAC[WRITE_ZEROTOP_32; ARM_ZERO_REGISTER;
     READ_RVALUE; WRITE_RVALUE; WORD_SHL_ZERO; WORD_SX_TRIVIAL] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_AC; ADD_AC; INT_ADD_AC; EQ_SYM_EQ;
                  ARM_ZERO_REGISTER; READ_RVALUE; WRITE_RVALUE] THEN
  PRINT_GOAL_TAC;;

(* Claim assembly is only bookkeeping. Each statement is proved by the
   kernel against its own generated definition; absent source constants
   cause refusal rather than a replacement model or a vacuous claim. *)
let SAIL_HL_ARM_ADDSUB_SHARED = filter (fun theorem ->
  let left = lhand(concl theorem) in
  is_const left && String.starts_with
    ~prefix:"sail_hl_shared_arm_2daddsub_" (fst(dest_const left)))
  (definitions());;

let SAIL_HL_ARM_ADDSUB_SOURCE name =
  let definition = find (fun theorem ->
    let left = lhand(concl theorem) in
    is_const left && fst(dest_const left) = name) (definitions()) in
  (* definitions() contains the kernel's original definition, rather than
     the exporter’s unfolded OCaml theorem binding. Derive that unfolding
     here from the actual shared helper definitions, without changing the
     source constant or the instruction claim. *)
  REWRITE_RULE SAIL_HL_ARM_ADDSUB_SHARED definition;;

let SAIL_HL_ARM_ADDSUB_CLAIM instruction width form =
  let reg = if width = 32 then "WREG'" else "XREG'" in
  let spreg = if width = 32 then "WREG_SP" else "XREG_SP" in
  let compare = mem instruction ["CMN"; "CMP"] in
  let negate = mem instruction ["NEG"; "NEGS"] in
  let flags = mem instruction ["ADDS"; "SUBS"; "CMN"; "CMP"; "NEGS"] in
  let shifted = form = "SHIFT" in
  let extended = String.length form > 4 && String.sub form 0 4 = "EXT_" in
  let suffix = if form = "" then "" else "_5f" ^
    String.concat "_5f" (String.split_on_char '_' form) in
  let source_name = Printf.sprintf "sail_hl_arm_5f%s%d%s"
    instruction width suffix in
  let definition = SAIL_HL_ARM_ADDSUB_SOURCE source_name in
  let fields = if negate then "d m"
    else if compare then (if form = "IMM" then "n" else "n m")
    else if form = "IMM" then "d n" else "d n m" in
  let parameters = fields ^
    (if form = "IMM" then " imm" else if shifted then " amount kind" else "") in
  let amount_width = if width = 32 then 5 else 6 in
  let quantifiers = "!" ^ fields ^ ":5 word. " ^
    (if form = "IMM" then Printf.sprintf "!imm:%d word. " width
     else if shifted then Printf.sprintf
       "!amount:%d word. !kind:sail_hl_type_ShiftType. " amount_width
     else "") ^ "!s t:armstate. " in
  let first = (if shifted || negate then reg else spreg) ^ " n" in
  let second = if form = "IMM" then "rvalue imm"
    else if shifted then "Shiftedreg (" ^ reg ^
      " m) (sail_hl_arm_logical_kind kind) (val amount)"
    else if extended then
      let kind, shift = match String.split_on_char '_' form with
        | ["EXT";kind;shift] -> kind,shift | _ -> failwith "extend profile" in
      let input_reg = if width = 64 && not(mem kind ["UXTX";"SXTX"])
        then "WREG'" else reg in
      "Shiftedreg (Extendedreg (" ^ input_reg ^ " m) " ^ kind ^ ") LSL " ^ shift
    else reg ^ " m" in
  let destination = (if shifted || negate || flags then reg else spreg) ^ " d" in
  let target = "arm_" ^ instruction ^
    (if compare then " (" ^ first ^ ") (" ^ second ^ ")"
     else if negate then " (" ^ destination ^ ") (" ^ second ^ ")"
     else " (" ^ destination ^ ") (" ^ first ^ ") (" ^ second ^ ")") in
  let statement = parse_term (quantifiers ^ source_name ^ " " ^ parameters ^
    " s t <=> " ^ target ^ " s t") in
  let prepare = if shifted then
    STRUCT_CASES_TAC
      (SPEC `kind:sail_hl_type_ShiftType` (cases "sail_hl_type_ShiftType")) THEN
    MP_TAC(ISPEC (parse_term(Printf.sprintf "amount:%d word" amount_width)) VAL_BOUND) THEN
    CONV_TAC (DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC
    else ALL_TAC in
  let source_cases = if shifted || negate then ALL_TAC else
    ASM_CASES_TAC `n:5 word = word 31` in
  let destination_cases = if compare
    then ALL_TAC else ASM_CASES_TAC `d:5 word = word 31` in
  let theorem = prove(statement,
    REPEAT GEN_TAC THEN prepare THEN source_cases THEN destination_cases THEN
    SAIL_HL_ARM_ADDSUB_NORM definition) in
  let marker = Printf.sprintf "SAIL_HL_ARM_%s%d%s_EQ" instruction width
    (if form = "" then "" else "_" ^ form) in
  sail_hl_report (marker, theorem);
  marker,theorem;;

(* The claimed forms. When the claims are split across forked processes
   (proof-fork.ml), each form is proved by exactly one of them. *)
let SAIL_HL_ARM_ADDSUB_BASIC_FORMS = flat(map
 (fun instruction -> flat(map (fun width -> map
   (fun form -> instruction,width,form) ["IMM";"SHIFT"])
   [32;64])) ["ADD";"ADDS";"SUB";"SUBS";"CMN";"CMP"]);;

let SAIL_HL_ARM_ADDSUB_EXTENDED_FORMS = flat(map
 (fun instruction -> flat(map (fun width -> flat(map
   (fun (kind,_) -> map (fun shift ->
     instruction,width,Printf.sprintf "EXT_%s_%d" kind shift) [0;1;2;3;4])
   SAIL_HL_ARM_ADDSUB_EXTEND_KINDS)) [32;64]))
 ["ADD";"ADDS";"SUB";"SUBS";"CMN";"CMP"]);;

let SAIL_HL_ARM_ADDSUB_NEGATE_FORMS = flat(map
 (fun instruction -> flat(map (fun width -> map
   (fun form -> instruction,width,form) ["";"SHIFT"]) [32;64]))
 ["NEG";"NEGS"]);;

assert(length SAIL_HL_ARM_ADDSUB_BASIC_FORMS = 24);;
assert(length SAIL_HL_ARM_ADDSUB_EXTENDED_FORMS = 480);;
assert(length SAIL_HL_ARM_ADDSUB_NEGATE_FORMS = 8);;

sail_hl_proof_fork "SAIL_HOL_LIGHT_ARM_ADDSUB_PROOFS_OK";;

let SAIL_HL_ARM_ADDSUB_CLAIMS = map
  (fun (instruction,width,form) ->
    SAIL_HL_ARM_ADDSUB_CLAIM instruction width form)
  (filter (fun (instruction,width,form) ->
     sail_hl_proof_shard (Printf.sprintf "%s%d_%s" instruction width form))
   (SAIL_HL_ARM_ADDSUB_BASIC_FORMS @ SAIL_HL_ARM_ADDSUB_EXTENDED_FORMS @
    SAIL_HL_ARM_ADDSUB_NEGATE_FORMS));;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_ADDSUB_PROOFS_OK";;
