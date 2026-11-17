(* The actual Sail ROR helper rotates by two logical shifts after masking
   its integer count. Keep this bitvector lemma independent of any exported
   instruction so shifted-register families can share the kernel proof. *)

let SAIL_HL_ARM_SHIFT_ROTATE = prove
 (`!x:N word. !count:num.
    (if count MOD dimindex(:N) = 0 then x else
     word_or (word_ushr x (count MOD dimindex(:N)))
       (word_shl x
         (num_of_int (&(dimindex(:N)) - &(count MOD dimindex(:N)))))) =
    word_ror x count`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `count MOD dimindex(:N) < dimindex(:N)` ASSUME_TAC THENL
   [SIMP_TAC[MOD_LT_EQ; DIMINDEX_NONZERO]; ALL_TAC] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; LT_IMP_LE; NUM_OF_INT_OF_NUM] THEN
  GEN_REWRITE_TAC RAND_CONV [WORD_ROR_MOD] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[WORD_ROR_ZERO];
    ASM_SIMP_TAC[WORD_ROR_SHIFTS; LT_IMP_LE]]);;

let SAIL_HL_ARM_SHIFT_ROTATE32 =
  REWRITE_RULE[DIMINDEX_32]
    (INST_TYPE[`:32`,`:N`] SAIL_HL_ARM_SHIFT_ROTATE);;

let SAIL_HL_ARM_SHIFT_ROTATE64 =
  REWRITE_RULE[DIMINDEX_64]
    (INST_TYPE[`:64`,`:N`] SAIL_HL_ARM_SHIFT_ROTATE);;
