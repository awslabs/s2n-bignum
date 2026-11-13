(* Agreement of the original Sail AES calculations with the four HOL
   instructions. Register parameters are unrestricted five-bit values,
   including Q31 and every overlap. The enabled AdvSIMD access projection
   is the same explicit boundary used by the other vector exports; decoder
   agreement and full platform access checks are separate obligations. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-aes.ml";;

(* Pure packing facts use sixteen independent bytes. In particular, the
   initial word in INSERT16 is arbitrary: all its bits are overwritten.
   These terms describe packing, not copied instruction or table bodies. *)
let SAIL_HL_AES_BYTES =
  List.init 16 (fun i -> "b" ^ string_of_int i);;

let SAIL_HL_AES_BYTE_LIST =
  "[" ^ String.concat ";" (List.rev SAIL_HL_AES_BYTES) ^ "]";;

let SAIL_HL_AES_INSERT16 =
  let packed = List.fold_left (fun old (i,byte) ->
    "(word_insert " ^ old ^ " (" ^ string_of_int (8 * i) ^
    ",8) (" ^ byte ^ ":8 word):128 word)")
    "(seed:128 word)" (List.mapi (fun i byte -> i,byte) SAIL_HL_AES_BYTES) in
  prove(parse_term
    ("!seed:128 word. !" ^ String.concat " " SAIL_HL_AES_BYTES ^
     ":8 word. " ^ packed ^ " = word_join_list_16_8 " ^
     SAIL_HL_AES_BYTE_LIST),
    REPEAT GEN_TAC THEN REWRITE_TAC[word_join_list_16_8] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC WORD_BLAST);;

let SAIL_HL_AES_JOIN16 =
  let descending = List.rev SAIL_HL_AES_BYTES in
  let packed = List.fold_left (fun (old,width) byte ->
    let width' = width + 8 in
    "(word_join " ^ old ^ " (" ^ byte ^ ":8 word):" ^
    string_of_int width' ^ " word)",width')
    ("(" ^ List.hd descending ^ ":8 word)",8) (List.tl descending) |> fst in
  prove(parse_term
    ("!" ^ String.concat " " SAIL_HL_AES_BYTES ^ ":8 word. " ^
     packed ^ " = word_join_list_16_8 " ^ SAIL_HL_AES_BYTE_LIST),
    REPEAT GEN_TAC THEN REWRITE_TAC[word_join_list_16_8] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC WORD_BLAST);;

(* Each clause is already a kernel-computed equality between a HOL table
   and its full 2048-bit value. Reducing the original source's closed joins
   and rewriting with these clauses checks every table bit without expanding
   a symbolic table lookup into a 2048-way case split. *)
let SAIL_HL_AES_TABLES = [
  JOINED_GF2_CLAUSE; JOINED_GF2_INV_CLAUSE;
  JOINED_FFMUL_02_CLAUSE; JOINED_FFMUL_03_CLAUSE;
  JOINED_FFMUL_09_CLAUSE; JOINED_FFMUL_0B_CLAUSE;
  JOINED_FFMUL_0D_CLAUSE; JOINED_FFMUL_0E_CLAUSE
];;

(* The inverse mix source sums the same four bytes in a different order.
   Ordered associative/commutative rewriting normalizes both expressions;
   it does not evaluate or assume anything about the symbolic table lookups. *)
let SAIL_HL_AES_XOR_LEFT_COMM = prove
 (`!x y z:N word.
     word_xor x (word_xor y z) = word_xor y (word_xor x z)`,
  CONV_TAC WORD_BITWISE_RULE);;

let SAIL_HL_ARM_AES_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC(definitions @
    [assign; LET_DEF; LET_END_DEF; FST; SND; QREG'; NUM_OF_INT_OF_NUM;
     aese; aesd; aesmc; aesimc; aes_sub_bytes; aes_sub_bytes_select;
     aes_sub_byte; aes_mix_columns; aes_inv_mix_columns;
     aes_mix_word; aes_inv_mix_word;
     FFmul02; FFmul03; FFmul09; FFmul0B; FFmul0D; FFmul0E; FFmul;
     INT_OF_NUM_MUL]) THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC(map SYM SAIL_HL_AES_TABLES) THEN
  REWRITE_TAC[SAIL_HL_AES_INSERT16; SAIL_HL_AES_JOIN16] THEN
  REWRITE_TAC[GSYM aes_shift_rows; GSYM aes_inv_shift_rows] THEN
  CONV_TAC(REDEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[SAIL_HL_AES_JOIN16; GSYM WORD_XOR_ASSOC;
    WORD_XOR_SYM; SAIL_HL_AES_XOR_LEFT_COMM; EQ_SYM_EQ];;

let SAIL_HL_ARM_AESE128_EQ = prove
 (`!d n:5 word. !s t:armstate.
    sail_hl_ARM_5fAESE128 d n s t <=>
    arm_AESE (QREG' d) (QREG' n) s t`,
  SAIL_HL_ARM_AES_TAC [sail_hl_ARM_5fAESE128; arm_AESE]);;

let SAIL_HL_ARM_AESD128_EQ = prove
 (`!d n:5 word. !s t:armstate.
    sail_hl_ARM_5fAESD128 d n s t <=>
    arm_AESD (QREG' d) (QREG' n) s t`,
  SAIL_HL_ARM_AES_TAC [sail_hl_ARM_5fAESD128; arm_AESD]);;

let SAIL_HL_ARM_AESMC128_EQ = prove
 (`!d n:5 word. !s t:armstate.
    sail_hl_ARM_5fAESMC128 d n s t <=>
    arm_AESMC (QREG' d) (QREG' n) s t`,
  SAIL_HL_ARM_AES_TAC [sail_hl_ARM_5fAESMC128; arm_AESMC]);;

let SAIL_HL_ARM_AESIMC128_EQ = prove
 (`!d n:5 word. !s t:armstate.
    sail_hl_ARM_5fAESIMC128 d n s t <=>
    arm_AESIMC (QREG' d) (QREG' n) s t`,
  SAIL_HL_ARM_AES_TAC [sail_hl_ARM_5fAESIMC128; arm_AESIMC]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_AESE128_EQ", SAIL_HL_ARM_AESE128_EQ;
  "SAIL_HL_ARM_AESD128_EQ", SAIL_HL_ARM_AESD128_EQ;
  "SAIL_HL_ARM_AESMC128_EQ", SAIL_HL_ARM_AESMC128_EQ;
  "SAIL_HL_ARM_AESIMC128_EQ", SAIL_HL_ARM_AESIMC128_EQ
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_AES_PROOFS_OK";;
