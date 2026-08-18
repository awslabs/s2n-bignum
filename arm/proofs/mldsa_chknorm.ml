(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness of poly_chknorm:                                   *)
(* Check if any polynomial coefficient has absolute value >= bound           *)
(* Returns 1 if norm check fails (|coeff| >= bound), 0 otherwise             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "arm/mldsa/mldsa_chknorm.o";;
 ****)

let mldsa_chknorm_mc = define_assert_from_elf "mldsa_chknorm_mc" "arm/mldsa/mldsa_chknorm.o"
(*** BYTECODE START ***)
[
  0x4e040c34;       (* arm_DUP_GEN Q20 X1 32 128 *)
  0x6e351eb5;       (* arm_EOR_VEC Q21 Q21 Q21 128 *)
  0xd2800202;       (* arm_MOV X2 (rvalue (word 16)) *)
  0x3dc00401;       (* arm_LDR Q1 X0 (Immediate_Offset (word 16)) *)
  0x3dc00802;       (* arm_LDR Q2 X0 (Immediate_Offset (word 32)) *)
  0x3dc00c03;       (* arm_LDR Q3 X0 (Immediate_Offset (word 48)) *)
  0x3cc40400;       (* arm_LDR Q0 X0 (Postimmediate_Offset (word 64)) *)
  0x4ea0b821;       (* arm_ABS_VEC Q1 Q1 32 128 *)
  0x4eb43c21;       (* arm_CMGE_VEC Q1 Q1 Q20 32 128 *)
  0x4ea11eb5;       (* arm_ORR_VEC Q21 Q21 Q1 128 *)
  0x4ea0b842;       (* arm_ABS_VEC Q2 Q2 32 128 *)
  0x4eb43c42;       (* arm_CMGE_VEC Q2 Q2 Q20 32 128 *)
  0x4ea21eb5;       (* arm_ORR_VEC Q21 Q21 Q2 128 *)
  0x4ea0b863;       (* arm_ABS_VEC Q3 Q3 32 128 *)
  0x4eb43c63;       (* arm_CMGE_VEC Q3 Q3 Q20 32 128 *)
  0x4ea31eb5;       (* arm_ORR_VEC Q21 Q21 Q3 128 *)
  0x4ea0b800;       (* arm_ABS_VEC Q0 Q0 32 128 *)
  0x4eb43c00;       (* arm_CMGE_VEC Q0 Q0 Q20 32 128 *)
  0x4ea01eb5;       (* arm_ORR_VEC Q21 Q21 Q0 128 *)
  0xf1000442;       (* arm_SUBS X2 X2 (rvalue (word 1)) *)
  0x54fffde1;       (* arm_BNE (word 2097084) *)
  0x6eb0aab5;       (* arm_UMAXV Q21 Q21 4 32 *)
  0x1e2602a0;       (* arm_FMOV_FtoI W0 Q21 0 32 *)
  0x12000000;       (* arm_AND W0 W0 (rvalue (word 1)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLDSA_CHKNORM_EXEC = ARM_MK_EXEC_RULE mldsa_chknorm_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLDSA_CHKNORM_MC =
  REWRITE_CONV[mldsa_chknorm_mc] `LENGTH mldsa_chknorm_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLDSA_CHKNORM_PREAMBLE_LENGTH = new_definition
  `MLDSA_CHKNORM_PREAMBLE_LENGTH = 0`;;

let MLDSA_CHKNORM_POSTAMBLE_LENGTH = new_definition
  `MLDSA_CHKNORM_POSTAMBLE_LENGTH = 4`;;

let MLDSA_CHKNORM_CORE_START = new_definition
  `MLDSA_CHKNORM_CORE_START = MLDSA_CHKNORM_PREAMBLE_LENGTH`;;

let MLDSA_CHKNORM_CORE_END = new_definition
  `MLDSA_CHKNORM_CORE_END = LENGTH mldsa_chknorm_mc - MLDSA_CHKNORM_POSTAMBLE_LENGTH`;;

let CHKNORM_LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLDSA_CHKNORM_MC;
              MLDSA_CHKNORM_CORE_START; MLDSA_CHKNORM_CORE_END;
              MLDSA_CHKNORM_PREAMBLE_LENGTH; MLDSA_CHKNORM_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas                                                             *)
(* ------------------------------------------------------------------------- *)

(* Expression emerging from the AVX2 code converting bit to 32-bit mask *)
let bit_to_mask32 = new_definition `bit_to_mask32 (b : bool) : 32 word = word_neg (word (bitval b) : 32 word)`;;

(* Expression used for bounds check itself *)
let bd = new_definition `bd (v : int32) (b: int32) : bool =
    (ival (iword (abs (ival v)) : 32 word) >= ival (word_zx (word_zx b : 64 word) : 32 word))`;;

let MAX_VAL_BIT_TO_MASK32 = prove(
  `MAX (val (bit_to_mask32 b0)) (val (bit_to_mask32 b1)) = val (bit_to_mask32 (b0 \/ b1))`,
  REWRITE_TAC[bit_to_mask32] THEN
  BOOL_CASES_TAC `b0:bool` THEN BOOL_CASES_TAC `b1:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC);;

let BD_SIMP = prove(
  `abs(ival(x : int32)) < &2 pow 31 ==> (bd x b <=> abs (ival x) >= ival b)`,
  REWRITE_TAC[bd] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ival(iword(abs(ival(x:32 word))) : 32 word) = abs(ival x)` SUBST1_TAC THENL
  [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
   FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[INT_ABS_POS] THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(word_zx:64 word -> 32 word) ((word_zx:32 word -> 64 word) b) = b` SUBST1_TAC THENL
  [MATCH_MP_TAC WORD_ZX_ZX THEN REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN ARITH_TAC;
   REFL_TAC]);;

let BIT_TO_MASK32_OR = prove(
  `word_or (bit_to_mask32 b0) (bit_to_mask32 b1) = bit_to_mask32 (b0 \/ b1)`,
  REWRITE_TAC[bit_to_mask32] THEN
  BOOL_CASES_TAC `b0:bool` THEN BOOL_CASES_TAC `b1:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV);;

let MASK32_TO_BIT = prove(
  `(word_zx:32 word -> 64 word) (word_and ((word_zx:64 word -> 32 word)
     ((word_zx:32 word -> 64 word) (word_subword (word (val (bit_to_mask32 b)) : 128 word) (0,32))))
     (word 1)) = word (bitval b) : 64 word`,
  REWRITE_TAC[bit_to_mask32] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let WORD_JOIN_OR_TYBIT0 = prove(
  `word_or (word_join (a:N word) (b:N word) : (N tybit0) word) (word_join (c:N word) (d:N word)) =
   word_join (word_or a c) (word_or b d)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OR; BIT_WORD_JOIN; DIMINDEX_TYBIT0] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < 2 * dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p ==> (q <=> p /\ q)`) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_CHKNORM_CORRECT = prove(
 `!a (x:num->int32) (bound:int32) pc.
        nonoverlapping (word pc, LENGTH mldsa_chknorm_mc) (a, 1024)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_chknorm_mc /\
                  read PC s = word(pc + MLDSA_CHKNORM_CORE_START) /\
                  C_ARGUMENTS [a; word_zx bound] s /\
                  (!i. i < 256 ==>
                     read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &2 pow 31))
             (\s. read PC s = word(pc + MLDSA_CHKNORM_CORE_END) /\
                  read X0 s = word(bitval(?i. i < 256 /\ abs(ival(x i)) >= ival bound)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  CONV_TAC CHKNORM_LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int32`; `bound:int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (* Expand bounded foralls in precondition to 256 explicit cases *)
  ENSURES_INIT_TAC "s0" THEN
  UNDISCH_TAC `forall i. i < 256 ==> read (memory :> bytes32 (word_add a (word (4 * i)))) s0 = x i` THEN
  CONV_TAC(ONCE_DEPTH_CONV (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN REPEAT STRIP_TAC THEN
  (* Merge bytes32 reads into bytes128 reads (64 merges for 256 coefficients) *)
  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 2
            (subst[mk_small_numeral(16*n),`n:num`]
                  `read (memory :> bytes128(word_add a (word n))) s0`))
            (0--63))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  STRIP_TAC THEN
  (* Symbolically execute all instructions until target PC *)
  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLDSA_CHKNORM_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_OR; GSYM bit_to_mask32; WORD_JOIN_OR_TYBIT0; SYM (SPEC_ALL bd); BIT_TO_MASK32_OR;
      WORD_BLAST `val(word_subword (x:32 word) (0,32) : 128 word) = val x`;
      MAX_VAL_BIT_TO_MASK32; MASK32_TO_BIT])) 1 THEN

  (* Close the state relation *)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read t s = x`] THEN

  RULE_ASSUM_TAC (CONV_RULE (ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)) THEN
  IMP_REWRITE_TAC [BD_SIMP] THEN
  POP_ASSUM_LIST (K ALL_TAC) THEN

  (* Convert to ! instead of ? and split *)
  GEN_REWRITE_TAC (BINOP_CONV o ONCE_DEPTH_CONV) [prove (`b = ~ (~ (b : bool))`, REWRITE_TAC[])] THEN
  GEN_REWRITE_TAC TOP_SWEEP_CONV [MESON[] `~(?i. i < n /\ P i) <=> (!i. i < n ==> ~P i)`; DE_MORGAN_THM] THEN
  CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  REPEAT AP_TERM_TAC THEN EQ_TAC THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness theorem (includes return)                          *)
(* ------------------------------------------------------------------------- *)

(* NOTE: This must be kept in sync with the CBMC specification
 * in mldsa/src/native/aarch64/src/arith_native_aarch64.h *)

let MLDSA_CHKNORM_SUBROUTINE_CORRECT = prove(
 `!a (x:num->int32) (bound:int32) pc returnaddress.
        nonoverlapping (word pc, LENGTH mldsa_chknorm_mc) (a, 1024)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_chknorm_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; word_zx bound] s /\
                  (!i. i < 256 ==>
                     read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &2 pow 31))
             (\s. read PC s = returnaddress /\
                  read X0 s = word(bitval(?i. i < 256 /\ abs(ival(x i)) >= ival bound)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  CONV_TAC CHKNORM_LENGTH_SIMPLIFY_CONV THEN
  let TWEAK_CONV =
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0] in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLDSA_CHKNORM_EXEC
   (CONV_RULE TWEAK_CONV
     (CONV_RULE CHKNORM_LENGTH_SIMPLIFY_CONV MLDSA_CHKNORM_CORRECT)));;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mldsa_chknorm" subroutine_signatures)
    MLDSA_CHKNORM_SUBROUTINE_CORRECT
    MLDSA_CHKNORM_EXEC;;

let MLDSA_CHKNORM_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a (bound:int32) pc returnaddress.
           nonoverlapping (word pc,LENGTH mldsa_chknorm_mc) (a,1024)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mldsa_chknorm_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; word_zx bound] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc returnaddress /\
                         memaccess_inbounds e2 [a,1024] []))
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLDSA_CHKNORM_EXEC);;
