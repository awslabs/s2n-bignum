(* Flag and register-view facts for 8/16/32/64-bit arithmetic.
   Sail calculates carry and signed overflow in one extra bit. The
   existing 64-bit proof uses the same argument; instantiate it here at
   the narrower widths rather than bit-blasting instruction operands.

   These facts describe word arithmetic and HOL state components. They do
   not replace a Sail calculation or count as instruction agreement. *)
needs "tools/sail/proofs/x86-arithmetic-lemmas.ml";;

let SAIL_HL_X86_GPR_FLAG_REWRITES width =
  if not (mem width [8;16;32;64]) then
    failwith "x86 GPR flag facts require width 8, 16, 32 or 64";
  let source = mk_finty(num width) in
  let wide = mk_finty(num(width + 1)) in
  let dims = map (fun ty -> DIMINDEX_CONV(inst [ty,`:N`] `dimindex(:N)`))
    [source;wide] @ SAIL_HL_X86_DIMS in
  let reduce = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) in
  let msb ty = reduce(INST_TYPE [ty,`:N`] MSB_VAL) in
  let carry = prove
    (parse_term(Printf.sprintf
      "!x y:%d word. !c. \
       bit %d (word_add (word_add (word_zx x:%d word) (word_zx y)) \
         (word(bitval c))) <=> \
       ~(val x + val y + bitval c = \
         val(word_add (word_add x y) (word(bitval c))))"
      width width (width + 1)),
     SIMP_TAC(msb wide :: SAIL_HL_X86_UNSIGNED_AT source wide ::
       CARRY_WORD_ADC :: dims) THEN CONV_TAC NUM_REDUCE_CONV) in
  let aux = prove
    (parse_term(Printf.sprintf
      "!x y:%d word. !c. \
       bit 4 (word_add (word_add \
         (word_zx(word_subword x (0,4):4 word):5 word) \
         (word_zx(word_subword y (0,4):4 word))) (word(bitval c))) <=> \
       ~(val(word_zx x:4 word) + val(word_zx y:4 word) + bitval c = \
         val(word_zx(word_add (word_add x y) (word(bitval c))):4 word))"
      width),
     SIMP_TAC(SAIL_HL_X86_LOW_SUBWORD `:4` ::
       SAIL_HL_X86_LOW_ADD source `:4` :: WORD_ZX_BITVAL ::
       SAIL_HL_X86_MSB5 :: SAIL_HL_X86_UNSIGNED_AT `:4` `:5` ::
       CARRY_WORD_ADC :: dims) THEN CONV_TAC NUM_REDUCE_CONV) in
  let overflow_add = prove
    (parse_term(Printf.sprintf
      "!x y:%d word. \
       ((bit %d x <=> bit %d y) /\\ \
        ~(bit %d (word_add x y) <=> bit %d x)) <=> \
       ~(ival x + ival y = ival(word_add x y))"
      width (width - 1) (width - 1) (width - 1) (width - 1)),
     REPEAT GEN_TAC THEN REWRITE_TAC[msb source] THEN WORD_ARITH_TAC) in
  let signed_wide = prove
    (parse_term(Printf.sprintf
      "!x:%d word. !y:%d word. !c. \
       ival(word_add (word_add (word_sx x:%d word) (word_sx y)) \
         (word(bitval c))) = ival x + ival y + &(bitval c)"
      width width (width + 1)),
     REPEAT GEN_TAC THEN
     REWRITE_TAC[word_sx; WORD_IWORD; GSYM IWORD_INT_ADD; INT_ADD_ASSOC] THEN
     MATCH_MP_TAC IVAL_IWORD THEN
     MP_TAC(ISPEC (parse_term(Printf.sprintf "x:%d word" width)) IVAL_BOUND) THEN
     MP_TAC(ISPEC (parse_term(Printf.sprintf "y:%d word" width)) IVAL_BOUND) THEN
     MP_TAC(SPEC `c:bool` BITVAL_BOUND) THEN
     REWRITE_TAC(GSYM INT_OF_NUM_LE :: dims) THEN
     CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN INT_ARITH_TAC) in
  let sx_low = prove
    (parse_term(Printf.sprintf
      "!x:%d word. word_zx(word_sx x:%d word):%d word = x"
      width (width + 1) width), BITBLAST_TAC) in
  let wide_overflow =
    let sign_extension = reduce
      (INST_TYPE [source,`:M`;wide,`:N`] IVAL_WORD_SX) in
    prove
      (parse_term(Printf.sprintf
        "!z:%d word. ~(bit %d z <=> bit %d z) <=> \
         ~(ival z = ival(word_zx z:%d word))"
        (width + 1) width (width - 1) width),
       GEN_TAC THEN GEN_REWRITE_TAC
         (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM sign_extension] THEN
       REWRITE_TAC[IVAL_EQ] THEN BITBLAST_TAC) in
  let overflow_adc = prove
    (parse_term(Printf.sprintf
      "!x y:%d word. !c. \
       ~(bit %d (word_add (word_add (word_sx x:%d word) (word_sx y)) \
           (word(bitval c))) <=> \
         bit %d (word_add (word_add (word_sx x:%d word) (word_sx y)) \
           (word(bitval c)))) <=> \
       ~(ival x + ival y + &(bitval c) = \
         ival(word_add (word_add x y) (word(bitval c))))"
      width width (width + 1) (width - 1) (width + 1)),
     SIMP_TAC(wide_overflow :: signed_wide ::
       SAIL_HL_X86_LOW_ADD wide source :: WORD_ZX_BITVAL :: sx_low :: dims)) in
  let zero =
    let widen = reduce(INST_TYPE [source,`:M`;wide,`:N`] VAL_WORD_ZX) in
    prove
      (parse_term(Printf.sprintf
        "!z:%d word. bit %d (word_sub (word_zx z:%d word) (word 1)) <=> \
         val z = 0" width width (width + 1)),
       GEN_TAC THEN
       REWRITE_TAC(msb wide :: VAL_WORD_SUB_CASES :: widen ::
         VAL_WORD_1 :: dims) THEN CONV_TAC NUM_REDUCE_CONV THEN
       MP_TAC(ISPEC (parse_term(Printf.sprintf "z:%d word" width)) VAL_BOUND) THEN
       REWRITE_TAC dims THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC) in
  let sign = reduce(INST_TYPE [source,`:N`] MSB_IVAL) in
  let full = `w:64 word` in
  let sign_read = GEN full (reduce(REWRITE_RULE[BIT_WORD_ZX]
    (SPEC (parse_term(Printf.sprintf "word_zx(w:64 word):%d word" width))
      sign))) in
  let high_byte_sign = prove
   (`!w:64 word.
     bit 15 w <=> ival(word_subword w (8,8):8 word) < &0`,
    REWRITE_TAC[GSYM(CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
      (INST_TYPE [`:8`,`:N`] MSB_IVAL));BIT_WORD_SUBWORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV) in
  let parity = reduce(REWRITE_RULE
    [LET_DEF; LET_END_DEF; BIT_WORD_0; BIT_WORD_BITVAL; BIT_WORD_NOT;
     BIT_WORD_XOR; BIT_WORD_SUBWORD; BIT_WORD_ZX]
    (GEN (parse_term(Printf.sprintf "z:%d word" width))
      (SPEC (parse_term(Printf.sprintf "word_zx(z:%d word):8 word" width))
        SAIL_HL_X86_PARITY8))) in
  let no_carry theorem =
    let x = parse_term(Printf.sprintf "x:%d word" width)
    and y = parse_term(Printf.sprintf "y:%d word" width) in
    GENL [x;y]
      (REWRITE_RULE[BITVAL_CLAUSES; ADD_CLAUSES; WORD_ADD_0; WORD_SUBWORD_0]
        (SPECL [x;y;`F`] theorem)) in
  (* Bit 15 of a full register is both the sign of its low 16-bit word and
     the sign of its legacy high byte. Use the latter interpretation only
     for byte instructions; otherwise it hides the word overflow fact. *)
  [carry;no_carry carry;aux;no_carry aux;
   overflow_add;REWRITE_RULE[sign] overflow_add;
   overflow_adc;zero;sign;sign_read] @
  (if width = 8 then [high_byte_sign] else []) @ [parity];;

(* The core register components are right-associated compositions. Apply
   READ_SHORT/WRITE_SHORT to the complete 64-bit register first, then put
   their components in that same canonical association. Applying the raw
   theorem to a chain starting at the entire register bank would not match.
   Low reads are zero extensions; upper-byte reads retain their slice.
   Writes below 32 bits preserve the entire surrounding register. *)
let SAIL_HL_X86_GPR_SHORT_REWRITES =
  let d = `d:4 word` in
  let register = `registers :> element (d:4 word)` in
  let canonical theorem =
    GEN d (CONV_RULE(TOP_DEPTH_CONV(CHANGED_CONV COMPONENT_CANON_CONV))
      (ISPEC register theorem)) in
  let mods = map (fun width ->
    CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
      (INST_TYPE [mk_finty(num width),`:N`] WORD_MOD_SIZE)) [8;16] in
  let reads = REWRITE_RULE (GSYM word_zx :: mods)
    (canonical READ_SHORT) in
  let high = prove
   (`!d:4 word. !s:x86state.
     read (registers :> element d :> bottom_32 :> bottom_16 :> top_8) s =
     word_subword (read (registers :> element d) s) (8,8):8 word`,
    REWRITE_TAC(reads :: word_subword :: mods) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mods) in
  let zero_top theorem =
    canonical (GEN (mk_var("c",type_of register))
      (INST_TYPE [`:x86state`,`:A`] theorem)) in
  [reads;high;canonical WRITE_SHORT;
   zero_top READ_ZEROTOP_32;zero_top WRITE_ZEROTOP_32];;

(* HOL's narrow GPR components preserve the surrounding register bits,
   except GPR32_Z, which zeroes them. Relate the partial-write expression
   emitted from Sail's array slice to WRITE_SHORT's existing component
   interpretation. This observes the entire 64-bit register, not a low-bit
   projection of the final state. *)
let SAIL_HL_X86_GPR_INSERT_REWRITES =
  map (fun statement -> prove(statement,
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[BIT_WORD_INSERT; BIT_WORD_JOIN; BIT_WORD_SUBWORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV))
  [`!x:64 word. !y:8 word.
     (word_insert x (0,8) y:64 word) =
     word_join (word_subword x (8,56):56 word) y`;
   `!x:64 word. !y:16 word.
     (word_insert x (0,16) y:64 word) =
     word_join (word_subword x (16,48):48 word) y`;
   `!x:64 word. !y:8 word.
     (word_insert x (8,8) y:64 word) =
     word_join (word_subword x (16,48):48 word)
       (word_join y (word_subword x (0,8):8 word):16 word)`];;

(* Subtraction uses the same extra-bit argument as addition. Its sign is
   the unsigned borrow; adjacent sign bits detect signed overflow. These
   width instances retain every incoming carry value and both operands.
   Literal specializations at the end relate 1 and 0-x to the unary flag
   calculations without expanding symbolic operands into individual bits. *)
let SAIL_HL_X86_GPR_SUB_REWRITES width =
  let source = mk_finty(num width)
  and wide = mk_finty(num(width + 1)) in
  let reduce = CONV_RULE
    (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) in
  let dims = map (fun ty -> DIMINDEX_CONV(inst [ty,`:N`] `dimindex(:N)`))
    [source;wide] @ SAIL_HL_X86_DIMS in
  let sign ty = reduce(INST_TYPE [ty,`:N`] MSB_IVAL) in
  let unsigned = prove
   (parse_term(Printf.sprintf
     "!x y:%d word. !c. \
      bit %d (word_sub (word_sub (word_zx x:%d word) (word_zx y)) \
                (word(bitval c))) <=> \
      ~(&(val x) - (&(val y) + &(bitval c)):int = \
        &(val(word_sub x (word_add y (word(bitval c))))))"
     width width (width + 1)),
    REPEAT GEN_TAC THEN REWRITE_TAC(sign wide :: dims) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SAIL_HL_X86_DIFFERENCE_AT source wide;CARRY_WORD_SBB] THEN
    ASM_CASES_TAC `c:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES;INT_OF_NUM_CLAUSES] THEN ARITH_TAC) in
  let aux = prove
   (parse_term(Printf.sprintf
     "!x y:%d word. !c. \
      bit 4 (word_sub (word_sub \
        (word_zx(word_subword x (0,4):4 word):5 word) \
        (word_zx(word_subword y (0,4):4 word))) (word(bitval c))) <=> \
      ~(&(val(word_zx x:4 word)) - \
        (&(val(word_zx y:4 word)) + &(bitval c)):int = \
        &(val(word_zx(word_sub x (word_add y (word(bitval c)))):4 word)))"
     width),
    REPEAT GEN_TAC THEN
    REWRITE_TAC[SAIL_HL_X86_LOW_SUBWORD `:4`;
      SAIL_HL_X86_LOW_SUB source `:4`;SAIL_HL_X86_LOW_ADD source `:4`;
      WORD_ZX_BITVAL;SAIL_HL_X86_SIGN5] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SAIL_HL_X86_DIFFERENCE_AT `:4` `:5`;CARRY_WORD_SBB] THEN
    ASM_CASES_TAC `c:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES;INT_OF_NUM_CLAUSES] THEN ARITH_TAC) in
  let overflow = prove
   (parse_term(Printf.sprintf
     "!x y:%d word. \
      (~(bit %d x <=> bit %d y) /\\ \
       ~(bit %d (word_sub x y) <=> bit %d x)) <=> \
      ~(ival x - ival y = ival(word_sub x y))"
     width (width - 1) (width - 1) (width - 1) (width - 1)),
    REPEAT GEN_TAC THEN
    REWRITE_TAC[reduce(INST_TYPE[source,`:N`] MSB_VAL)] THEN WORD_ARITH_TAC) in
  let signed = prove
   (parse_term(Printf.sprintf
     "!x:%d word. !y:%d word. !c. \
      ival(word_sub (word_sub (word_sx x:%d word) (word_sx y)) \
             (word(bitval c))) = ival x - (ival y + &(bitval c))"
     width width (width + 1)),
    REPEAT GEN_TAC THEN
    REWRITE_TAC[word_sx;WORD_IWORD;GSYM IWORD_INT_SUB;
      INT_ARITH `x - y - z:int = x - (y + z)`] THEN
    MATCH_MP_TAC IVAL_IWORD THEN
    MP_TAC(ISPEC (parse_term(Printf.sprintf "x:%d word" width)) IVAL_BOUND) THEN
    MP_TAC(ISPEC (parse_term(Printf.sprintf "y:%d word" width)) IVAL_BOUND) THEN
    MP_TAC(SPEC `c:bool` BITVAL_BOUND) THEN
    REWRITE_TAC(GSYM INT_OF_NUM_LE :: dims) THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN INT_ARITH_TAC) in
  let wide_overflow = prove
   (parse_term(Printf.sprintf
     "!z:%d word. ~(bit %d z <=> bit %d z) <=> \
      ~(ival z = ival(word_zx z:%d word))"
     (width + 1) width (width - 1) width),
    GEN_TAC THEN GEN_REWRITE_TAC
      (RAND_CONV o RAND_CONV o RAND_CONV)
      [GSYM(reduce(INST_TYPE[source,`:M`;wide,`:N`] IVAL_WORD_SX))] THEN
    REWRITE_TAC[IVAL_EQ] THEN BITBLAST_TAC) in
  let sx_low = prove
   (parse_term(Printf.sprintf
     "!x:%d word. word_zx(word_sx x:%d word):%d word = x"
     width (width + 1) width),BITBLAST_TAC) in
  let overflow_sbb = prove
   (parse_term(Printf.sprintf
     "!x y:%d word. !c. \
      ~(bit %d (word_sub (word_sub (word_sx x:%d word) (word_sx y)) \
          (word(bitval c))) <=> \
        bit %d (word_sub (word_sub (word_sx x:%d word) (word_sx y)) \
          (word(bitval c)))) <=> \
      ~(ival x - (ival y + &(bitval c)) = \
        ival(word_sub x (word_add y (word(bitval c)))))"
     width width (width + 1) (width - 1) (width + 1)),
    SIMP_TAC(wide_overflow :: signed ::
      SAIL_HL_X86_LOW_SUB wide source :: WORD_ZX_BITVAL :: sx_low :: dims) THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub x y) z:N word = word_sub x (word_add y z)`]) in
  let no_borrow theorem =
    let x = parse_term(Printf.sprintf "x:%d word" width)
    and y = parse_term(Printf.sprintf "y:%d word" width) in
    GENL [x;y] (REWRITE_RULE
      [BITVAL_CLAUSES;INT_OF_NUM_CLAUSES;INT_ADD_RID;WORD_ADD_0;WORD_SUB_0]
      (SPECL [x;y;`F`] theorem)) in
  let basic = [unsigned;no_borrow unsigned;aux;no_borrow aux;
    overflow;REWRITE_RULE[sign source] overflow;overflow_sbb] in
  let x = parse_term(Printf.sprintf "x:%d word" width)
  and y = parse_term(Printf.sprintf "y:%d word" width)
  and zero = parse_term(Printf.sprintf "word 0:%d word" width)
  and one = parse_term(Printf.sprintf "word 1:%d word" width) in
  let unary = map
    (CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC WORD_REDUCE_CONV
      THENC NUM_REDUCE_CONV))
    [GEN x (SPECL [x;one] (no_borrow aux));
     GEN x (SPECL [x;one] overflow);
     GEN y (SPECL [zero;y] (no_borrow unsigned));
     GEN y (SPECL [zero;y] (no_borrow aux));
     GEN y (SPECL [zero;y] overflow)] in
  basic @ unary;;

(* The s2n-bignum register component of a field name at one width. A
   legacy byte field d selects AH/CH/DH/BH for 4 <= val d. *)
let SAIL_HL_X86_GPR_COMPONENT width legacy name =
  if legacy then Printf.sprintf
    "(if 4 <= val(%s:3 word) then \
       GPR8(Gpr (iword(&(val %s) - &4):4 word) Upper_8) \
     else GPR8(Gpr (word_zx %s:4 word) Lower_8))" name name name
  else if width = 64 then "(registers :> element " ^ name ^ ")"
  else if width = 32 then "(GPR32_Z(Gpr " ^ name ^ " Lower_32))"
  else Printf.sprintf "(GPR%d(Gpr %s %s))" width name
    (if width = 8 then "Lower_8" else "Lower_16");;

(* x86/proofs/x86.ml guards the undefined CF of SHL and SHR with
   dimindex(:N) <= c. The shift proofs expect c < dimindex(:N) with the
   defined branch first; these restatements differ only in that order. *)
let SAIL_HL_X86_SHL_DEF, SAIL_HL_X86_SHR_DEF =
  let reorder = REWRITE_RULE[GSYM NOT_LT; COND_SWAP] in
  reorder x86_SHL, reorder x86_SHR;;

(* For a 16-bit SHLD/SHRD with a count above 16, the same definitions
   leave the destination and then CF, OF, SF, ZF, PF and AF undefined. The
   proofs expect the flags in the order ZF, SF, PF, CF, OF, AF. The
   flags are orthogonal components, so their ASSIGNS commute; sort them by
   kernel-proved swaps and restate both definitions in that order. *)
let SAIL_HL_X86_SHLD_DEF, SAIL_HL_X86_SHRD_DEF =
  let flags = [`ZF`; `SF`; `PF`; `CF`; `OF`; `AF`] in
  let rank tm = match tm with
    | Comb(Const("ASSIGNS",_),flag) -> (try index flag flags with Failure _ -> -1)
    | _ -> -1 in
  let swap tm = match tm with
    | Comb(Comb(Const(",,",_),a),Comb(Comb(Const(",,",_),b),_))
        when rank b >= 0 && rank a > rank b ->
        (REWR_CONV SEQ_ASSOC THENC LAND_CONV ASSIGNS_SWAP_CONV THENC
         REWR_CONV(GSYM SEQ_ASSOC)) tm
    | Comb(Comb(Const(",,",_),a),b) when rank b >= 0 && rank a > rank b ->
        ASSIGNS_SWAP_CONV tm
    | _ -> failwith "flag order" in
  let order = prove
   (`!dest:(x86state,N word)component.
       UNDEFINED_VALUES[dest] ,, UNDEFINED_VALUES[CF;OF;SF;ZF;PF;AF] =
       ASSIGNS dest ,, UNDEFINED_VALUES[ZF;SF;PF;CF;OF;AF]`,
    GEN_TAC THEN REWRITE_TAC[UNDEFINED_VALUES; SEQ_ID] THEN
    CONV_TAC(LAND_CONV(REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV swap)))) THEN
    REFL_TAC) in
  let reorder = REWRITE_RULE[order] in
  reorder x86_SHLD, reorder x86_SHRD;;
