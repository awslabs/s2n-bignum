(* Word, flag and state-component facts used by several Arm suites. They
   are identities about HOL terms; none describes an instruction. *)

(* One-bit words built from a condition. *)
let SAIL_HL_ARM_BIT_WORD = prove
 (`!p. ((word(bitval p):1 word) = word 0 <=> ~p) /\
       ((word(bitval p):1 word) = word 1 <=> p)`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let SAIL_HL_ARM_BIT_WORD_ONE = prove
 (`!p. (word(bitval p):1 word) = word 1 <=> p`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let SAIL_HL_ARM_BIT_WORD_EQ = prove
 (`!p q. (word(bitval p):1 word) = word(bitval q) <=> (p <=> q)`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let SAIL_HL_ARM_NOT_FLAG = prove
 (`!p. (if p then word 0 else word 1):1 word = word(bitval(~p))`,
  GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN REWRITE_TAC[WORD_BITVAL]);;

let SAIL_HL_ARM_ODD_BITVAL = prove
 (`!p. ODD(bitval p) <=> p`,
  REWRITE_TAC[FORALL_BOOL_THM; BITVAL_CLAUSES; ARITH_ODD]);;

(* The NZCV word that the exporter packs from four flags. *)
let SAIL_HL_ARM_PACKED_BITS = prove
 (`!n z c v.
   let w:4 word = word_join
     (word_join (word_join (word(bitval n):1 word)
       (word(bitval z):1 word):2 word) (word(bitval c):1 word):3 word)
       (word(bitval v):1 word) in
   (bit 0 (word_subword w (3,1):1 word) <=> n) /\
   (bit 0 (word_subword w (2,1):1 word) <=> z) /\
   (bit 0 (word_subword w (1,1):1 word) <=> c) /\
   (bit 0 (word_subword w (0,1):1 word) <=> v)`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; BIT_WORD_SUBWORD; BIT_WORD_JOIN;
              DIMINDEX_1; DIMINDEX_2; DIMINDEX_3; DIMINDEX_4;
              BIT_WORD_BITVAL] THEN CONV_TAC NUM_REDUCE_CONV);;
let SAIL_HL_ARM_PACKED_REWRITES =
  REWRITE_RULE[LET_DEF; LET_END_DEF] SAIL_HL_ARM_PACKED_BITS;;

(* Subtraction with carry, and its carry and overflow flags; SUB_RESULT
   and SUB_FLAGS are the instances with the carry set. *)
let SAIL_HL_ARM_SBB_RESULT = prove
 (`!x y:N word. !c.
   word_add (word_add x (word_not y)) (word(bitval c)) =
   word_sub x (word_add y (word(bitval(~c))))`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_RULE);;

let SAIL_HL_ARM_SBB_FLAGS = prove
 (`!x y:N word. !c.
   let d = word_sub x (word_add y (word(bitval(~c)))) in
   (~(val x + val(word_not y) + bitval c = val d) <=>
      &(val x) - (&(val y) + &(bitval(~c))):int = &(val d)) /\
   (ival x + ival(word_not y) + &(bitval c) =
      ival x - (ival y + &(bitval(~c))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONJ_TAC THENL [
    ONCE_REWRITE_TAC[GSYM SAIL_HL_ARM_SBB_RESULT] THEN
    REWRITE_TAC[CARRY_WORD_ADC; SAIL_HL_ARM_SBB_RESULT;
                NOCARRY_WORD_SBB; VAL_WORD_NOT] THEN
    BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
    MP_TAC(SPEC `y:N word` VAL_BOUND) THEN ARITH_TAC;
    REWRITE_TAC[IVAL_WORD_NOT] THEN
    BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN INT_ARITH_TAC
  ]);;

let SAIL_HL_ARM_SUB_RESULT = prove
 (`!x y:N word.
   word_add (word_add x (word_not y)) (word 1) = word_sub x y`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`x:N word`; `y:N word`; `T`] SAIL_HL_ARM_SBB_RESULT) THEN
  REWRITE_TAC[BITVAL_CLAUSES; WORD_ADD_0]);;

let SAIL_HL_ARM_SUB_FLAGS =
  REWRITE_RULE[LET_DEF; LET_END_DEF; BITVAL_CLAUSES; WORD_ADD_0;
    ADD_CLAUSES; INT_ADD_RID; INT_OF_NUM_ADD; INT_OF_NUM_EQ;
    WORD_ADD_AC; ADD_AC; INT_ADD_AC; EQ_SYM_EQ]
  (SPECL [`x:N word`; `y:N word`; `T`] SAIL_HL_ARM_SBB_FLAGS);;

let SAIL_HL_ARM_MSB32 =
  CONV_RULE NUM_REDUCE_CONV
    (REWRITE_RULE[DIMINDEX_32] (INST_TYPE [`:32`,`:N`] MSB_IVAL));;
let SAIL_HL_ARM_MSB64 =
  CONV_RULE NUM_REDUCE_CONV
    (REWRITE_RULE[DIMINDEX_64] (INST_TYPE [`:64`,`:N`] MSB_IVAL));;

(* General registers and flags are separate components, so their writes
   commute. *)
let SAIL_HL_ARM_GPR_FLAGS = prove
 (`!d. orthogonal_components (XREG d) NF /\
       orthogonal_components (XREG d) ZF /\
       orthogonal_components (XREG d) CF /\
       orthogonal_components (XREG d) VF /\
       orthogonal_components (WREG d) NF /\
       orthogonal_components (WREG d) ZF /\
       orthogonal_components (WREG d) CF /\
       orthogonal_components (WREG d) VF`,
  GEN_TAC THEN REWRITE_TAC[WREG; XREG] THEN COND_CASES_TAC THEN
  REPEAT CONJ_TAC THEN CONV_TAC ORTHOGONAL_COMPONENTS_CONV);;

let SAIL_HL_ARM_XFLAG_COMMUTE = prove
 (`!d f x b. !s:armstate.
   (f = NF \/ f = ZF \/ f = CF \/ f = VF)
   ==> write (XREG d) x (write f b s) =
       write f b (write (XREG d) x s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `d:num` SAIL_HL_ARM_GPR_FLAGS) THEN
  REWRITE_TAC[orthogonal_components] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SAIL_HL_ARM_WFLAG_COMMUTE = prove
 (`!d f x b. !s:armstate.
   (f = NF \/ f = ZF \/ f = CF \/ f = VF)
   ==> write (WREG d) x (write f b s) =
       write f b (write (WREG d) x s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `d:num` SAIL_HL_ARM_GPR_FLAGS) THEN
  REWRITE_TAC[orthogonal_components] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* Generated control-flow joins return tuples and conditional words.
   These move a condition into a tuple, a lane insertion, a bit or an
   iword, keeping both outcomes. CONDITIONAL_BIT distributes only a bit
   observation, so the rest of a calculation is not copied into every
   branch. *)
let SAIL_HL_ARM_CONDITIONAL_PAIR = prove
 (`!condition (x:A) (y:B) u v.
   (if condition then (x,y) else (u,v)) =
   ((if condition then x else u),(if condition then y else v))`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `condition:bool` THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_CONDITIONAL_INSERT = prove
 (`!condition (old:N word) position (x:M word) y.
   (if condition
    then (word_insert old position x:P word)
    else word_insert old position y) =
   word_insert old position (if condition then x else y)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `condition:bool` THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_INSERT_IF = prove
 (`!p (original:N word) pos len (x:M word) y.
   (if p then word_insert original (pos,len) x
         else word_insert original (pos,len) y) =
   word_insert original (pos,len) (if p then x else y)`,
  REWRITE_TAC[FORALL_BOOL_THM]);;

let SAIL_HL_ARM_CONDITIONAL_BIT = prove
 (`!condition (x:N word) y i.
   bit i (if condition then x else y) =
   (if condition then bit i x else bit i y)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `condition:bool` THEN REWRITE_TAC[]);;

let SAIL_HL_ARM_IWORD_IF = prove
 (`!p (x:int) y.
   (if p then (iword x:N word) else iword y) =
   iword(if p then x else y)`,
  REWRITE_TAC[FORALL_BOOL_THM]);;

(* A conditional XOR step of a polynomial-multiply loop. The word form
   keeps one copy of the old accumulator instead of copying the earlier
   updates into both branches; the bit form turns the step into one
   parity term. *)
let SAIL_HL_ARM_WORD_XOR_STEP = prove
 (`!condition (previous:N word) value.
   (if condition then word_xor previous value else previous) =
   word_xor previous (if condition then value else word 0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `condition:bool` THEN
  REWRITE_TAC[WORD_XOR_0]);;

let SAIL_HL_ARM_XOR_STEP = TAUT
 `(if condition then ~(previous <=> value) else previous) <=>
  ~(previous <=> (condition /\ value))`;;

let SAIL_HL_ARM_PREDECESSOR = prove
 (`!n:num. (&(n + 1):int) - &1 = &n`,
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;
