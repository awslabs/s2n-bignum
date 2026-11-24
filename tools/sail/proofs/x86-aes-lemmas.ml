(* Evaluation and wiring facts for the AES-NI suite.

   shina computes the S-box from GF(2^8) arithmetic, as 8-step loops that
   the translator unrolls, where s2n-bignum's `aesenc` and its relatives
   look each byte up in the tables of common/aes.ml. The suite relates the
   two in three steps, none of which supplies an instruction's calculation:

   - Each byte function (the two S-boxes and the six multiplications by a
     constant of MixColumns) of the generated model equals the table
     lookup for every one of the 256 inputs. BYTE_TABLE_PROVE proves such
     a lemma case by case, evaluating the generated definition on a
     numeral with SEVAL and the table clause on the other side.
   - The vector functions (SubBytes, ShiftRows, MixColumns and their
     inverses) then differ from s2n-bignum's only in how the sixteen
     bytes are packed. The table lookups stay opaque; the packing is
     compared by bit-blasting, with the lookups as variables.
   - The instruction relation is rewritten with these lemmas.

   This file holds the evaluator and the packing lemma; the lemmas about
   the generated functions are in x86-aes.ml. *)
needs "x86/proofs/base.ml";;
needs "x86/proofs/aes.ml";;
needs "tools/sail/proofs/x86-vector-lemmas.ml";;

let SAIL_HL_X86_AES_BETA_APP =
  let rec beta_app tm =
    (BETA_CONV ORELSEC (RATOR_CONV beta_app THENC BETA_CONV)) tm in
  beta_app;;

(* Closed-term reductions on words, integers and the one-bit values. *)
let SAIL_HL_X86_AES_RED_CONV =
  WORD_RED_CONV ORELSEC NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
  DIMINDEX_CONV ORELSEC
  GEN_REWRITE_CONV I (NUM_OF_INT_OF_NUM :: CONJUNCTS BITVAL_CLAUSES);;

(* Reduce a term in which every free variable has been replaced by a
   numeral. A `let` is substituted only after its value is a numeral:
   substituting the expression would copy it into every use, and the
   chain of products in the field inverse then grows exponentially.
   Applications of lambdas evaluate their arguments first, and a
   conditional evaluates its condition. *)
let rec SAIL_HL_X86_AES_EVAL tm =
  match tm with
  | Abs(_,_) -> REFL tm
  | Comb(Comb(Const("LET",_),_),_) ->
      (RAND_CONV SAIL_HL_X86_AES_EVAL THENC let_CONV THENC
       SAIL_HL_X86_AES_EVAL) tm
  | Comb(Comb(Comb(Const("COND",_),_),_),_) ->
      (RATOR_CONV(RATOR_CONV(RAND_CONV SAIL_HL_X86_AES_EVAL)) THENC
       ((REWR_CONV (CONJUNCT1 COND_CLAUSES) THENC SAIL_HL_X86_AES_EVAL) ORELSEC
        (REWR_CONV (CONJUNCT2 COND_CLAUSES) THENC SAIL_HL_X86_AES_EVAL))) tm
  | _ ->
    let head,args = strip_comb tm in
    if is_abs head && args <> [] then
      let rec arguments tm =
        match tm with
        | Comb(f,_) when is_comb f || is_abs f ->
            (RATOR_CONV arguments THENC RAND_CONV SAIL_HL_X86_AES_EVAL) tm
        | Comb(_,_) -> RAND_CONV SAIL_HL_X86_AES_EVAL tm
        | _ -> REFL tm in
      (arguments THENC SAIL_HL_X86_AES_BETA_APP THENC
       SAIL_HL_X86_AES_EVAL) tm
    else
      (SUB_CONV SAIL_HL_X86_AES_EVAL THENC
       TRY_CONV (SAIL_HL_X86_AES_RED_CONV THENC SAIL_HL_X86_AES_EVAL)) tm;;

let SAIL_HL_X86_AES_ALL_RED = DEPTH_CONV SAIL_HL_X86_AES_RED_CONV;;

(* A proof of  !x:8 word. L x = R x  by its 256 cases. [lconv] evaluates
   the left side of one case and [rconv] the right side; both must end
   in the same numeral. *)
let SAIL_HL_X86_AES_BYTE_TABLE_PROVE tm lconv rconv =
  let x,body = dest_forall tm in
  let case n =
    let inst = vsubst [mk_comb(`word:num->8 word`, mk_small_numeral n), x] body in
    prove(inst, CONV_TAC(LAND_CONV lconv THENC RAND_CONV rconv) THEN REFL_TAC) in
  let thms = map case (0--255) in
  let n = `n:num` in
  prove(tm, GEN_TAC THEN
    SUBGOAL_THEN (mk_forall(n, mk_imp(`n < 256`,
      vsubst [mk_comb(`word:num->8 word`, n), x] body))) ASSUME_TAC THENL
     [CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC thms; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `val(x:8 word)`) THEN
    REWRITE_TAC[WORD_VAL] THEN
    MP_TAC(ISPEC `x:8 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* Sail builds a vector by inserting its sixteen bytes one after the other
   into zero; s2n-bignum joins them. The bytes are arbitrary here, so the
   table lookups in them stay opaque. *)
let SAIL_HL_X86_AES_INSERT16 =
  let names = List.init 16 (fun i -> "b" ^ string_of_int i) in
  let packed = List.fold_left (fun old (i,byte) ->
    "(word_insert " ^ old ^ " (" ^ string_of_int (8 * i) ^ ",8) (" ^ byte ^
    ":8 word):128 word)")
    "(word 0:128 word)" (List.mapi (fun i b -> i,b) names) in
  let joined = fst(List.fold_left (fun (acc,width) byte ->
      "(word_join (" ^ byte ^ ":8 word) " ^ acc ^ ":" ^
      string_of_int (width + 8) ^ " word)", width + 8)
    ("(" ^ List.hd names ^ ":8 word)",8) (List.tl names)) in
  prove(parse_term ("!" ^ String.concat " " names ^ ":8 word. " ^ packed ^
                    " = " ^ joined),
    REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;
