(* AES-NI: AESENC, AESENCLAST, AESDEC, AESDECLAST and AESKEYGENASSIST in
   register form, under the documented supplied-byte and LongMode
   boundary. Each theorem compares complete states. All five are
   legacy-encoded, so the statements use SIMD128_SSE and the destination
   keeps bits 128 to 511 of its register. The AES-NI availability check of
   check_legacy_simd is outside the selected bodies and is not compared.

   shina's functions (S-box from field arithmetic, ShiftRows, MixColumns
   and their inverses) are equal to s2n-bignum's, which look the bytes up
   in tables, for every byte value; x86-aes-lemmas.ml says how. The
   instruction roots are then compared as in the SSE suite, with those
   functions rewritten. The unexpanded root definitions are used, so that
   the generated functions are rewritten before they are unfolded. *)
needs "x86/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
needs "tools/sail/proofs/x86-vector-lemmas.ml";;
needs "tools/sail/proofs/x86-sse-lemmas.ml";;
needs "tools/sail/proofs/x86-aes-lemmas.ml";;
needs "tools/sail/proofs/fresh-model.ml";;

let sail_hl_aes_standard_new_definition = new_definition;;
let sail_hl_aes_before = definitions ();;
module Sail_hl_x86_aes_model = struct
let new_definition = Sail_hl_fresh_model.new_definition;;
loadt "tools/sail/_build/x86-aes.ml";;
end;;
open Sail_hl_x86_aes_model;;
let new_definition = sail_hl_aes_standard_new_definition;;

(* The definitions that the model added: its roots and its shared
   functions, each as `name = \args. body`. *)
let sail_hl_aes_definitions =
  filter (fun theorem -> not(mem theorem sail_hl_aes_before))
    (definitions ());;

let sail_hl_aes_name theorem =
  fst(dest_const(fst(strip_comb(lhand(snd(strip_forall(concl theorem)))))));;

let sail_hl_aes_definition name =
  find (fun theorem -> sail_hl_aes_name theorem = name)
    sail_hl_aes_definitions;;

let sail_hl_aes_shared name =
  sail_hl_aes_definition ("sail_hl_shared_x86_2daes_" ^ name);;

let SAIL_HL_X86_AES_UNFOLD =
  GEN_REWRITE_CONV TOP_DEPTH_CONV
    (map sail_hl_aes_shared
      ["aes_5fsbox_5f21"; "aes_5finv_5fsbox_5f14"; "gf2p8_5finv_5f13";
       "gf2p8_5fmul_5f7"; "rotr_5f12"; "sign_5fextend_5f6";
       "zero_5fextend_5f5"; "zeros_5f4"]);;

let SAIL_HL_X86_AES_EVALUATE =
  SAIL_HL_X86_AES_UNFOLD THENC SAIL_HL_X86_AES_EVAL;;

(* The table lookup that s2n-bignum's S-box and MixColumns bytes perform. *)
let SAIL_HL_X86_AES_TABLE_CONV table =
  REWRITE_CONV[aes_sub_byte; FFmul02; FFmul03; FFmul09; FFmul0B; FFmul0D;
               FFmul0E; FFmul; table] THENC
  DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let SAIL_HL_X86_AES_SBOX = SAIL_HL_X86_AES_BYTE_TABLE_PROVE
  `!x:8 word. sail_hl_shared_x86_2daes_aes_5fsbox_5f21 x =
              aes_sub_byte joined_GF2 x`
  SAIL_HL_X86_AES_EVALUATE (SAIL_HL_X86_AES_TABLE_CONV JOINED_GF2_CLAUSE);;

let SAIL_HL_X86_AES_INV_SBOX = SAIL_HL_X86_AES_BYTE_TABLE_PROVE
  `!x:8 word. sail_hl_shared_x86_2daes_aes_5finv_5fsbox_5f14 x =
              aes_sub_byte joined_GF2_inv x`
  (GEN_REWRITE_CONV TOP_DEPTH_CONV
     [sail_hl_aes_shared "aes_5finv_5fsbox_5f14";
      sail_hl_aes_shared "gf2p8_5finv_5f13";
      sail_hl_aes_shared "gf2p8_5fmul_5f7"; sail_hl_aes_shared "rotr_5f12";
      sail_hl_aes_shared "sign_5fextend_5f6";
      sail_hl_aes_shared "zero_5fextend_5f5"; sail_hl_aes_shared "zeros_5f4"]
   THENC SAIL_HL_X86_AES_EVAL)
  (SAIL_HL_X86_AES_TABLE_CONV JOINED_GF2_INV_CLAUSE);;

(* gf2p8_mul by the constants of (Inv)MixColumns is s2n-bignum's table
   function of the same constant. *)
let SAIL_HL_X86_AES_MUL constant table clause =
  SAIL_HL_X86_AES_BYTE_TABLE_PROVE
   (mk_forall(`x:8 word`, mk_eq(
     list_mk_comb(`sail_hl_shared_x86_2daes_gf2p8_5fmul_5f7`,
       [`x:8 word`; mk_comb(`word:num->8 word`, mk_small_numeral constant)]),
     mk_comb(table, `x:8 word`))))
   SAIL_HL_X86_AES_EVALUATE (SAIL_HL_X86_AES_TABLE_CONV clause);;

let SAIL_HL_X86_AES_MUL02 = SAIL_HL_X86_AES_MUL 2 `FFmul02` JOINED_FFMUL_02_CLAUSE;;
let SAIL_HL_X86_AES_MUL03 = SAIL_HL_X86_AES_MUL 3 `FFmul03` JOINED_FFMUL_03_CLAUSE;;
let SAIL_HL_X86_AES_MUL09 = SAIL_HL_X86_AES_MUL 9 `FFmul09` JOINED_FFMUL_09_CLAUSE;;
let SAIL_HL_X86_AES_MUL0B = SAIL_HL_X86_AES_MUL 11 `FFmul0B` JOINED_FFMUL_0B_CLAUSE;;
let SAIL_HL_X86_AES_MUL0D = SAIL_HL_X86_AES_MUL 13 `FFmul0D` JOINED_FFMUL_0D_CLAUSE;;
let SAIL_HL_X86_AES_MUL0E = SAIL_HL_X86_AES_MUL 14 `FFmul0E` JOINED_FFMUL_0E_CLAUSE;;

(* Rewriting the bytes' sources, a shared function's body becomes a join
   of bytes that s2n-bignum joins in a list. *)
let SAIL_HL_X86_AES_VELEM = sail_hl_aes_shared "velem_5fnat_5f11";;

let SAIL_HL_X86_AES_UNPACK =
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  CONV_TAC SAIL_HL_X86_AES_ALL_RED THEN
  REWRITE_TAC[SAIL_HL_X86_SHIFTED_SUBWORD];;

let SAIL_HL_X86_AES_SHIFT_ROWS = prove
 (`!x:128 word. sail_hl_shared_x86_2daes_aes_5fshift_5frows_5f23 x =
                aes_shift_rows x`,
  GEN_TAC THEN
  REWRITE_TAC[sail_hl_aes_shared "aes_5fshift_5frows_5f23";
              SAIL_HL_X86_AES_VELEM; aes_shift_rows] THEN
  SAIL_HL_X86_AES_UNPACK THEN
  CONV_TAC WORD_JOIN_LIST_16_8_CONV THEN
  CONV_TAC SAIL_HL_X86_AES_ALL_RED THEN CONV_TAC WORD_BLAST);;

let SAIL_HL_X86_AES_INV_SHIFT_ROWS = prove
 (`!x:128 word. sail_hl_shared_x86_2daes_aes_5finv_5fshift_5frows_5f16 x =
                aes_inv_shift_rows x`,
  GEN_TAC THEN
  REWRITE_TAC[sail_hl_aes_shared "aes_5finv_5fshift_5frows_5f16";
              SAIL_HL_X86_AES_VELEM; aes_inv_shift_rows] THEN
  SAIL_HL_X86_AES_UNPACK THEN
  CONV_TAC WORD_JOIN_LIST_16_8_CONV THEN
  CONV_TAC SAIL_HL_X86_AES_ALL_RED THEN CONV_TAC WORD_BLAST);;

let SAIL_HL_X86_AES_SUB_BYTES_TAC definition box =
  GEN_TAC THEN
  REWRITE_TAC[definition; SAIL_HL_X86_AES_VELEM; aes_sub_bytes;
              aes_sub_bytes_select; box] THEN
  SAIL_HL_X86_AES_UNPACK THEN
  CONV_TAC WORD_JOIN_LIST_16_8_CONV THEN
  REWRITE_TAC[SAIL_HL_X86_AES_INSERT16];;

let SAIL_HL_X86_AES_SUB_BYTES = prove
 (`!x:128 word. sail_hl_shared_x86_2daes_aes_5fsub_5fbytes_5f22 x =
                aes_sub_bytes joined_GF2 x`,
  SAIL_HL_X86_AES_SUB_BYTES_TAC (sail_hl_aes_shared "aes_5fsub_5fbytes_5f22")
    SAIL_HL_X86_AES_SBOX);;

let SAIL_HL_X86_AES_INV_SUB_BYTES = prove
 (`!x:128 word. sail_hl_shared_x86_2daes_aes_5finv_5fsub_5fbytes_5f15 x =
                aes_sub_bytes joined_GF2_inv x`,
  SAIL_HL_X86_AES_SUB_BYTES_TAC
    (sail_hl_aes_shared "aes_5finv_5fsub_5fbytes_5f15")
    SAIL_HL_X86_AES_INV_SBOX);;

(* MixColumns: with the multiplications replaced by s2n-bignum's table
   functions, which become variables, both sides are the same sixteen
   xor-sums of bytes, joined in the same order up to the order of the
   summands. *)
let SAIL_HL_X86_AES_MIX_COLUMNS = prove
 (`!x:128 word. sail_hl_shared_x86_2daes_aes_5fmix_5fcolumns_5f20 x =
                aes_mix_columns x`,
  GEN_TAC THEN
  REWRITE_TAC[sail_hl_aes_shared "aes_5fmix_5fcolumns_5f20";
              sail_hl_aes_shared "aes_5fmix_5fcolumn_5f19";
              aes_mix_columns; aes_mix_word] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  CONV_TAC SAIL_HL_X86_AES_ALL_RED THEN
  REWRITE_TAC[SAIL_HL_X86_AES_MUL02; SAIL_HL_X86_AES_MUL03] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC SAIL_HL_X86_AES_ALL_RED THEN
  CONV_TAC WORD_JOIN_LIST_16_8_CONV THEN
  CONV_TAC SAIL_HL_X86_AES_ALL_RED THEN
  SPEC_TAC(`FFmul02`,`f2:8 word->8 word`) THEN
  SPEC_TAC(`FFmul03`,`f3:8 word->8 word`) THEN
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let SAIL_HL_X86_AES_INV_MIX_COLUMNS = prove
 (`!x:128 word. sail_hl_shared_x86_2daes_aes_5finv_5fmix_5fcolumns_5f9 x =
                aes_inv_mix_columns x`,
  GEN_TAC THEN
  REWRITE_TAC[sail_hl_aes_shared "aes_5finv_5fmix_5fcolumns_5f9";
              sail_hl_aes_shared "aes_5finv_5fmix_5fcolumn_5f8";
              aes_inv_mix_columns; aes_inv_mix_word] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  CONV_TAC SAIL_HL_X86_AES_ALL_RED THEN
  REWRITE_TAC[SAIL_HL_X86_AES_MUL09; SAIL_HL_X86_AES_MUL0B;
              SAIL_HL_X86_AES_MUL0D; SAIL_HL_X86_AES_MUL0E] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC SAIL_HL_X86_AES_ALL_RED THEN
  CONV_TAC WORD_JOIN_LIST_16_8_CONV THEN
  CONV_TAC SAIL_HL_X86_AES_ALL_RED THEN
  SPEC_TAC(`FFmul09`,`f9:8 word->8 word`) THEN
  SPEC_TAC(`FFmul0B`,`fb:8 word->8 word`) THEN
  SPEC_TAC(`FFmul0D`,`fd:8 word->8 word`) THEN
  SPEC_TAC(`FFmul0E`,`fe:8 word->8 word`) THEN
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let SAIL_HL_X86_AES_SUB_WORD = prove
 (`!w:32 word. sail_hl_shared_x86_2daes_aes_5fsub_5fword_5f27 w =
               aes_subword w`,
  GEN_TAC THEN
  REWRITE_TAC[sail_hl_aes_shared "aes_5fsub_5fword_5f27"; aes_subword;
              SAIL_HL_X86_AES_SBOX; aes_sub_byte] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN REFL_TAC);;

let SAIL_HL_X86_AES_ROT_WORD = prove
 (`!w:32 word. sail_hl_shared_x86_2daes_aes_5frot_5fword_5f28 w =
               aes_rotword w`,
  GEN_TAC THEN
  REWRITE_TAC[sail_hl_aes_shared "aes_5frot_5fword_5f28"; aes_rotword] THEN
  CONV_TAC SAIL_HL_X86_AES_ALL_RED THEN CONV_TAC WORD_BLAST);;

(* The instruction functions: the same steps as s2n-bignum's in the same
   order, now in terms of the lemmas above. *)
let SAIL_HL_X86_AES_AESENC = prove
 (`!s k:128 word. sail_hl_shared_x86_2daes_aesenc_5f24 s k = aesenc s k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sail_hl_aes_shared "aesenc_5f24"; aesenc;
              SAIL_HL_X86_AES_SHIFT_ROWS; SAIL_HL_X86_AES_SUB_BYTES;
              SAIL_HL_X86_AES_MIX_COLUMNS] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN REFL_TAC);;

let SAIL_HL_X86_AES_AESENCLAST = prove
 (`!s k:128 word. sail_hl_shared_x86_2daes_aesenclast_5f25 s k =
                  aesenclast s k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sail_hl_aes_shared "aesenclast_5f25"; aesenclast;
              SAIL_HL_X86_AES_SHIFT_ROWS; SAIL_HL_X86_AES_SUB_BYTES] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN REFL_TAC);;

let SAIL_HL_X86_AES_AESDEC = prove
 (`!s k:128 word. sail_hl_shared_x86_2daes_aesdec_5f17 s k = aesdec s k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sail_hl_aes_shared "aesdec_5f17"; aesdec;
              SAIL_HL_X86_AES_INV_SHIFT_ROWS; SAIL_HL_X86_AES_INV_SUB_BYTES;
              SAIL_HL_X86_AES_INV_MIX_COLUMNS] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN REFL_TAC);;

let SAIL_HL_X86_AES_AESDECLAST = prove
 (`!s k:128 word. sail_hl_shared_x86_2daes_aesdeclast_5f18 s k =
                  aesdeclast s k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sail_hl_aes_shared "aesdeclast_5f18"; aesdeclast;
              SAIL_HL_X86_AES_INV_SHIFT_ROWS; SAIL_HL_X86_AES_INV_SUB_BYTES] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN REFL_TAC);;

let SAIL_HL_X86_AES_KEYGENASSIST = prove
 (`!x:128 word. !imm:8 word.
    sail_hl_shared_x86_2daes_aeskeygenassist_5f29 x imm =
    aeskeygenassist x imm`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sail_hl_aes_shared "aeskeygenassist_5f29"; aeskeygenassist;
              SAIL_HL_X86_AES_SUB_WORD; SAIL_HL_X86_AES_ROT_WORD;
              sail_hl_aes_shared "zero_5fextend_5f5"] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN CONV_TAC SAIL_HL_X86_AES_ALL_RED THEN
  REFL_TAC);;

let SAIL_HL_X86_AES_LEMMAS =
  [SAIL_HL_X86_AES_AESENC; SAIL_HL_X86_AES_AESENCLAST;
   SAIL_HL_X86_AES_AESDEC; SAIL_HL_X86_AES_AESDECLAST;
   SAIL_HL_X86_AES_KEYGENASSIST];;

(* The shared functions that decode the prefix and the registers. The
   AES functions stay folded, to be rewritten by the lemmas. *)
let SAIL_HL_X86_AES_DECODER_DEFINITIONS =
  filter (fun theorem ->
    let name = sail_hl_aes_name theorem in
    let has part =
      let n = String.length part in
      let rec search i = i + n <= String.length name &&
        (String.sub name i n = part || search (i + 1)) in search 0 in
    not (exists has ["aes_5f"; "gf2p8"; "rotr"; "velem"; "aesenc"; "aesdec";
                     "aeskeygen"]))
    (filter (fun theorem ->
       let name = sail_hl_aes_name theorem in
       String.length name > 24 &&
       String.sub name 0 24 = "sail_hl_shared_x86_2daes")
      sail_hl_aes_definitions);;

let SAIL_HL_X86_AES_CLAIM (root, instruction, target, parameters, operands) =
  let constant = "sail_hl_" ^ String.concat "_5f" (String.split_on_char '_' root) in
  let definition = sail_hl_aes_definition constant in
  let statement = SAIL_HL_X86_SSE_STATEMENT
    (root, definition, instruction, target, parameters, operands) in
  let name = "SAIL_HL_" ^ root ^ "_EQ" in
  let started = Sys.time() in
  print_endline("Starting complete-state proof: " ^ name);
  let theorem = prove(statement,
    SAIL_HL_X86_VECTOR_TAC_WITH
      ([COMPONENT_COMPOSE_ASSOC; READ_ZEROTOP_32; WRITE_ZEROTOP_32] @
       SAIL_HL_X86_SSE_REWRITES @ SAIL_HL_X86_AES_LEMMAS)
      (definition :: target :: SIMD128_SSE ::
       SAIL_HL_X86_AES_DECODER_DEFINITIONS)) in
  Printf.printf "CPU: %.3fs\n%!" (Sys.time() -. started);
  name, theorem;;

let SAIL_HL_X86_AES_CLAIMS = map SAIL_HL_X86_AES_CLAIM [
  "X86_AESENC128_RR","AESENC",x86_AESENC,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_AESENCLAST128_RR","AESENCLAST",x86_AESENCLAST,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_AESDEC128_RR","AESDEC",x86_AESDEC,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_AESDECLAST128_RR","AESDECLAST",x86_AESDECLAST,["d",4;"m",4],["S",128,"d";"S",128,"m"];
  "X86_AESKEYGENASSIST128_RRI","AESKEYGENASSIST",x86_AESKEYGENASSIST,["d",4;"m",4;"imm",8],["S",128,"d";"S",128,"m";"I",0,"imm"];
];;
if length SAIL_HL_X86_AES_CLAIMS <> 5 then failwith "aes claim count";;
List.iter sail_hl_report SAIL_HL_X86_AES_CLAIMS;;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_X86_AES_PROOFS_OK";;
