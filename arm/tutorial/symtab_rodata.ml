(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
          Verifying a program that reads constant data from .rodata
******************************************************************************)

needs "arm/proofs/base.ml";;

(* The following command will print the assertion checker fn of
   "arm/tutorial/symtab_rodata.o":

   print_literal_relocs_from_elf "arm/tutorial/symtab_rodata.o";;
*)

let a_mc,a_constants_data = define_assert_relocs_from_elf "a_mc"
    "arm/tutorial/symtab_rodata.o"
(fun w BL ADR ADRP ADD_rri64 -> [
  w 0xaa0003e3;         (* arm_MOV X3 X0 *)
  ADRP (mk_var("x",`:num`),0,4,0);
  ADD_rri64 (mk_var("x",`:num`),0,0,0);
  w 0xaa0303e1;         (* arm_MOV X1 X3 *)
  w 0xb8617801;         (* arm_LDR W1 X0 (Shiftreg_Offset X1 2) *)
  ADRP (mk_var("y",`:num`),0,20,0);
  ADD_rri64 (mk_var("y",`:num`),0,0,0);
  w 0xaa0303e2;         (* arm_MOV X2 X3 *)
  w 0xb8627800;         (* arm_LDR W0 X0 (Shiftreg_Offset X2 2) *)
  w 0x0b000020;         (* arm_ADD W0 W1 W0 *)
  w 0xd65f03c0          (* arm_RET X30 *)
]);;

(* Compared to the result of define_asserts_from_elf, the return value of
    define_assert_relocs_from_elf has the following differences:

    1. It returns a_constants_data, which is a list of thm.
      Each thm describes a definition of an object in a read-only section:

      # a_constants_data;;

      - : thm list =
      [|- y_data = [word 1; word 0; word 0; word 0; ...];
       |- x_data = [word 2; word 0; word 0; word 0; ...]]

    2. The returned a_mc is a function that takes the addresses of pc, x, y and
       (x and y are the addresses of the two constant arrays) and returns
       the corresponding machine code.

      # a_mc;;

      - : thm =
      |- forall x pc y. b_mc pc x y = CONS (word 227) (...)
*)

let EXEC = ARM_MK_EXEC_RULE a_mc;;

let A_SPEC = prove(`forall pc retpc x y i.
  // These two assumptions state that the distance between symbol x and pc+4
  // (which is the first adrp) do not overflow, and so does symbol y and
  // pc+20.
  adrp_within_bounds (word x) (word (pc + 4)) /\
  adrp_within_bounds (word y) (word (pc + 20)) /\
  i < 10
  ==>
  ensures arm
    (\s. aligned_bytes_loaded s (word pc) (a_mc pc x y) /\
         bytes_loaded s (word x) x_data /\
         bytes_loaded s (word y) y_data /\
         read PC s = word pc /\
         read X0 s = word i /\
         read X30 s = word retpc)
    (\s. read W0 s = word (3 * (1 + i)) /\
         read PC s = word retpc)
    (MAYCHANGE [X0; X1; X2; X3; PC] ,, MAYCHANGE [events])`,

  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Let's prove the constant array is storing some structured int sequence. *)
  SUBGOAL_THEN
      `read (memory :> bytes32 (word_add (word x) (word (4 * i)))) s0 = word (2 * (i+1)) /\
       read (memory :> bytes32 (word_add (word y) (word (4 * i)))) s0 = word (i+1)`
      MP_TAC THENL [

    (* Explode the 40-byte constant memory reads into 40 1-bytes!
       Do it twice, one for x and one for y. *)
    REPEAT_N 2 (
      FIRST_X_ASSUM (fun th ->
        (* Unfold the constant arrays! *)
        let unfolded_bytes_loaded = REWRITE_RULE(bytes_loaded::a_constants_data) th in
        (* Fold LENGTH array, and explode arr using BYTELIST_EXPAND_CONV *)
        MP_TAC (CONV_RULE (ONCE_DEPTH_CONV LENGTH_CONV THENC
                          LAND_CONV BYTELIST_EXPAND_CONV)
                unfolded_bytes_loaded)) THEN
      (* [a;b;..] = [x;y;..] is a = x /\ b = y /\ ... *)
      REWRITE_TAC [CONS_11] THEN
      STRIP_TAC) THEN

    (* For each case where i < 10, concretely evaluate the values from the
       exploded bytes, proving the equality. *)
    UNDISCH_TAC `i < 10` THEN
    SPEC_TAC (`i:num`,`i:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN

    (* Convert the goal into word_joins of 1-byte reads as well. *)
    REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT] THEN
    (* Offset canonicalization, and then rewrite using assumptions *)
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS;WORD_ADD_0;ARITH] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;

    ALL_TAC
  ] THEN

  STRIP_TAC THEN
  (* An extra equality that helps ARM_STEPS_TAC pick the right
     memory read equation. "arm_print_log := true;;" will help you what
     happens when this rule does not exist. *)
  ASSUME_TAC (WORD_RULE `word (4 * val (word i:int64)):int64 = word (4 * i)`) THEN

  REWRITE_TAC[ARITH] THEN
  REPEAT STRIP_TAC THEN
  ARM_STEPS_TAC EXEC (1--3) THEN
  FIRST_X_ASSUM (fun th -> MP_TAC th THEN IMP_REWRITE_TAC[ADRP_ADD_FOLD] THEN DISCH_TAC) THEN

  ARM_STEPS_TAC EXEC (4--7) THEN
  FIRST_X_ASSUM (fun th -> MP_TAC th THEN IMP_REWRITE_TAC[ADRP_ADD_FOLD] THEN DISCH_TAC) THEN

  ARM_STEPS_TAC EXEC (8--11) THEN

  (* Prove the postcondition. *)
  ENSURES_FINAL_STATE_TAC THEN

  ASM_REWRITE_TAC[WREG_EXPAND_CLAUSES;READ_ZEROTOP_32] THEN
  REWRITE_TAC[WORD_BLAST`word_zx (word_zx (x:(32)word):(64)word):(32)word = x`] THEN
  CONV_TAC WORD_RULE);;
