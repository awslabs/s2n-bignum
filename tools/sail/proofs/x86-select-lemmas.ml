(* Facts for the condition-code, extension and byte-swap forms of x86-select.

   Sail's blend(a, b, sel) is (a & ~m) | (b & m) with m the sign extension
   of the one-bit select. Prove once per operand width that this is the
   conditional it implements. *)
needs "tools/sail/proofs/x86-scalar-lemmas.ml";;

let SAIL_HL_X86_BLEND_FACTS = map (fun width ->
  prove(parse_term(Printf.sprintf
    "!a b:%d word. !c. \
     word_or (word_and a (word_not (word_sx (word(bitval c):1 word)))) \
             (word_and b (word_sx (word(bitval c):1 word))) = \
     if c then b else a" width),
    REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    BITBLAST_TAC)) [64;32;16];;

(* SETcc writes the zero extension of the one-bit condition. *)
let SAIL_HL_X86_BITVAL_WORD = prove
 (`!c. word(bitval c):8 word = if c then word 1 else word 0`,
  GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BITVAL_CLAUSES]);;

(* Sail's bswap concatenates the bytes of its operand in reverse order.
   After the generated body is normalized, a 64-bit operand appears with a
   byte-sized zero extension first; a 32-bit one is read through the low
   half of the register and written back zero-extended. *)
let SAIL_HL_X86_BSWAP_FACTS =
  [prove
   (`!x:64 word.
     word_join (word_zx x:8 word)
       (word_join (word_subword x (8,8):8 word)
       (word_join (word_subword x (16,8):8 word)
       (word_join (word_subword x (24,8):8 word)
       (word_join (word_subword x (32,8):8 word)
       (word_join (word_subword x (40,8):8 word)
       (word_join (word_subword x (48,8):8 word)
          (word_subword x (56,8):8 word):16 word):24 word):32 word):40 word)
       :48 word):56 word):64 word = word_bytereverse x`,
    GEN_TAC THEN BITBLAST_TAC);
   prove
   (`!x:64 word.
     (word_zx
       (word_join (word_zx (word_zx x:32 word):8 word)
         (word_join (word_subword (word_zx x:32 word) (8,8):8 word)
         (word_join (word_subword (word_zx x:32 word) (16,8):8 word)
            (word_subword (word_zx x:32 word) (24,8):8 word):16 word):24 word)
       :32 word):64 word) =
     word_zx (word_bytereverse (word_zx x:32 word):32 word)`,
    GEN_TAC THEN BITBLAST_TAC)];;

(* Sign extension to 64 bits followed by truncation to 32 bits. *)
let SAIL_HL_X86_SX_TRUNCATE = map (fun source -> prove(parse_term
  (Printf.sprintf "!x:%d word. word_zx(word_sx x:64 word):32 word = word_sx x"
   source), GEN_TAC THEN BITBLAST_TAC)) [8;16];;

(* eval_cc indexes a 16-bit word built from the flags; with a literal
   condition code, reading that bit selects one flag expression. *)
let SAIL_HL_X86_CONDITION_BIT_TAC =
  REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_NOT; BIT_WORD_AND; BIT_WORD_OR;
              BIT_WORD_XOR; BIT_WORD_BITVAL; BIT_WORD_0; BIT_WORD_1] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BIT_WORD_NOT; BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_XOR;
              BIT_WORD_BITVAL; BIT_WORD_JOIN; BIT_WORD_0] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV;;


(* The select suite's tactic: after the register fields are normalized,
   read the selected condition bit, replace blend by its conditional, and
   turn the zero-extended bit into 0 or 1; at the end, put the Boolean
   condition in the order of s2n-bignum's definition. *)
let SAIL_HL_X86_SELECT_TAC =
  SAIL_HL_X86_SCALAR_TAC_WITH
    (SAIL_HL_X86_CONDITION_BIT_TAC THEN
     REWRITE_TAC (WORD_ZX_BITVAL :: SAIL_HL_X86_BITVAL_WORD ::
                  SAIL_HL_X86_BLEND_FACTS))
    (REWRITE_TAC[DE_MORGAN_THM; DISJ_SYM; CONJ_SYM; NOT_IMP]);;
