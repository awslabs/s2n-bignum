(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
          Verifying a program that reads constant data from .rodata
                            and calls a function.
******************************************************************************)

needs "x86/proofs/base.ml";;

(* Note: this example will not work on MacOS (x86) because MacOS compiler
   creates a relocation entry for calls to local functions as well.
*)

(* The following command will print the assertion checker fn of
   "x86/tutorial/rodata.o":

   print_literal_relocs_from_elf "x86/tutorial/rodata.o";;

   Or, you can also use

   save_literal_relocs_from_elf "out.txt" "x86/tutorial/rodata.o";;
*)

let a_mc,a_constants_data = define_assert_relocs_from_elf "a_mc"
    "x86/tutorial/rodata.o"
(fun b ADDR -> [b[
  0x48; 0x8d; 0x0d]; ADDR "x"; b[
                            (* LEA (% rcx) (Riprel (word_sx (iword (&x - &(pc + 7))))) *)
  0x48; 0x8d; 0x05]; ADDR "y"; b[
                            (* LEA (% rax) (Riprel (word_sx (iword (&y - &(pc + 14))))) *)
  0x8b; 0x04; 0xb8;        (* MOV (% eax) (Memop Doubleword (%%% (rax,2,rdi))) *)
  0x03; 0x04; 0xb9;        (* ADD (% eax) (Memop Doubleword (%%% (rcx,2,rdi))) *)
  0xc3;                    (* RET *)
  0x48; 0x8d; 0x05]; ADDR "z"; b[
                            (* LEA (% rax) (Riprel (word_sx (iword (&z - &(pc + 28))))) *)
  0x8b; 0x10;              (* MOV (% edx) (Memop Doubleword (%% (rax,0))) *)
  0x48; 0x63; 0xd2;        (* MOVSX (% rdx) (% edx) *)
  0x48; 0x01; 0xd7;        (* ADD (% rdi) (% rdx) *)
  0xe8; 0xd7; 0xff; 0xff; 0xff;
                            (* CALL (Imm32 (word 4294967255)) *)
  0xc3                     (* RET *)
]]);;

(* Compared to the result of define_asserts_from_elf, the return value of
    define_assert_relocs_from_elf has the following differences:

    1. It returns a_constants_data, which is a list of thm.
      Each thm describes a definition of an object in a read-only section:

      # a_constants_data;;

      - : thm list =
      [|- z_data = [word 1; word 0; word 0; word 0];
       |- y_data = [word 1; word 0; word 0; word 0; ...];
       |- x_data = [word 2; word 0; word 0; word 0; ...]]

    2. The returned a_mc is a function that takes the addresses of pc, x, y, z
       and returns the corresponding machine code.
       x, y and z are the addresses of the constant arrays.

      # a_mc;;

      - : thm =
      |- forall pc x y z. a_mc pc x y z = CONS (word 72) (...)
*)

let EXEC = X86_MK_EXEC_RULE a_mc;;

(* Two helper tactics.
   1. INTRO_READ_MEMORY_FROM_BYTES8_TAC t:
      If t is `read (memory :> bytesN ...) sM`, prove a theorem
      `read (memory :> bytesN ...) sM = <some expr>` and introduce it
      as an assumption, from the existing `read (memory :> bytes8 ..) sM = ..`
      assumptions.

   2. EXPLODE_BYTELIST_ASSUM_TAC:
      Find assumption `read (memory :> bytelist (...)) s = ..` and explode
      it to a list of `read (memory :> bytes8 (...)) s = ..` and reintroduce
      them as assumptions.
*)
let INTRO_READ_MEMORY_FROM_BYTES8_TAC (t:term) =
  (* Convert t into word_joins of 1-byte reads. *)
  let r = REWRITE_CONV [READ_MEMORY_BYTESIZED_SPLIT] t in
  (* Offset canonicalization, and then rewrite using assumptions *)
  let r = REWRITE_RULE[WORD_ADD_ASSOC_CONSTS;WORD_ADD_0;ARITH] r in
  MP_TAC r THEN
  ASM (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)) [] THEN
  CONV_TAC (LAND_CONV WORD_REDUCE_CONV) THEN
  DISCH_TAC;;

let EXPLODE_BYTELIST_ASSUM_TAC (ptr_name:string) =
  FIRST_X_ASSUM (fun th ->
  let _ = find_term (fun t -> name_of t = "bytelist") (concl th) in
  let _ = find_term (fun t -> name_of t = ptr_name) (concl th) in
  (* Unfold the constant arrays! *)
    let unfolded_bytes_loaded = REWRITE_RULE a_constants_data th in
    (* Fold LENGTH array, and explode arr using BYTELIST_EXPAND_CONV *)
    MP_TAC (CONV_RULE (ONCE_DEPTH_CONV LENGTH_CONV THENC
                      LAND_CONV BYTELIST_EXPAND_CONV)
            unfolded_bytes_loaded)) THEN
  (* [a;b;..] = [x;y;..] is a = x /\ b = y /\ ... *)
  REWRITE_TAC [CONS_11] THEN
  STRIP_TAC;;

(* A helper lemma to expand EAX to RAX *)

let READ_BOTTOM_32 = prove
  (`!s:A. read (c :> bottom_32) s = word_subword (read c s) (0, 32)`,
   REWRITE_TAC[READ_COMPONENT_COMPOSE; bottom_32; bottomhalf;
               DIMINDEX_32; READ_SUBWORD; through; read]);;

let F_SPEC = prove(
  `forall x y z i pc stackpointer returnaddress.
    riprel32_within_bounds x (pc+7) /\
    riprel32_within_bounds y (pc+14) /\
    val i < 10
    ==>
    ensures x86
      (\s. bytes_loaded s (word pc) (a_mc pc x y z) /\
          read (memory :> bytelist (word x, LENGTH x_data)) s = x_data /\
          read (memory :> bytelist (word y, LENGTH y_data)) s = y_data /\
          read RIP s = word pc /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          C_ARGUMENTS [i] s)
      (\s. read EAX s = word (3 * (1 + val i)) /\
          read RIP s = returnaddress /\
          read RSP s = word_add stackpointer (word 8))
      (MAYCHANGE [RSP; RAX; RCX; RIP],, MAYCHANGE SOME_FLAGS)`,

  REPEAT STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN

  (* Let's prove the constant array is storing some structured int sequence. *)
  SUBGOAL_THEN
      `read (memory :> bytes32 (word_add (word x) (word (4 * val (i:int64))))) s0 = word (2 * (val i+1)) /\
       read (memory :> bytes32 (word_add (word y) (word (4 * val i)))) s0 = word (val i+1)`
      MP_TAC THENL [

    (* Explode the 40-byte constant memory reads into 40 1-bytes!
       Do it twice, one for x and one for y. *)
    EXPLODE_BYTELIST_ASSUM_TAC "x" THEN
    EXPLODE_BYTELIST_ASSUM_TAC "y" THEN

    (* For each case where i < 10, concretely evaluate the values from the
       exploded bytes, proving the equality. *)
    ABBREV_TAC `i' = val (i:int64)` THEN
    UNDISCH_TAC `i' < 10` THEN
    SPEC_TAC (`i':num`,`i':num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[ARITH;WORD_ADD_0] THEN

    REPEAT CONJ_TAC THEN (fun (asl,w) ->
      INTRO_READ_MEMORY_FROM_BYTES8_TAC (lhs w) (asl,w)
    ) THEN ASM_REWRITE_TAC[];

    ALL_TAC
  ] THEN

  STRIP_TAC THEN

  X86_STEPS_TAC EXEC (1--1) THEN
  FIRST_X_ASSUM (fun th -> MP_TAC th THEN IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD]
    THEN DISCH_TAC) THEN

  X86_STEPS_TAC EXEC (2--2) THEN
  FIRST_X_ASSUM (fun th -> MP_TAC th THEN IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD]
    THEN DISCH_TAC) THEN

  X86_STEPS_TAC EXEC (3--5) THEN

  (* Prove the postcondition. *)
  ENSURES_FINAL_STATE_TAC THEN

  ASM_REWRITE_TAC[EAX;READ_BOTTOM_32] THEN
  REWRITE_TAC[
    WORD_BLAST`word_zx (word_zx (x:(32)word):(64)word):(32)word = x`;
    WORD_BLAST`word_subword(word_zx (y:(32)word):(64)word) (0,32)=y`] THEN
  CONV_TAC WORD_RULE);;


(* Proving the specification of function g(i) that calls f(i + z). *)

let G_SPEC = prove(
  `forall x y z i pc stackpointer returnaddress.
    riprel32_within_bounds x (pc+7) /\
    riprel32_within_bounds y (pc+14) /\
    riprel32_within_bounds z (pc+28) /\
    val i < 9 /\
    ALL (nonoverlapping (word_sub stackpointer (word 8),8))
        [(word pc,LENGTH (a_mc pc x y z));
        (word x, LENGTH x_data); (word y, LENGTH y_data)]
    ==>
    ensures x86
      (\s. bytes_loaded s (word pc) (a_mc pc x y z) /\
          read (memory :> bytelist (word x, LENGTH x_data)) s = x_data /\
          read (memory :> bytelist (word y, LENGTH y_data)) s = y_data /\
          read (memory :> bytelist (word z, LENGTH z_data)) s = z_data /\
          read RIP s = word (pc + 0x15) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          C_ARGUMENTS [i] s)
      (\s. read EAX s = word (3 * (2 + val i)) /\
          read RIP s = returnaddress /\
          read RSP s = word_add stackpointer (word 8))
      (MAYCHANGE [RSP; RAX; RDX; RDI; RIP; RCX],, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [memory :> bytes64 (word_sub stackpointer (word 8))])`,

  REPEAT_N 5 GEN_TAC THEN
  (* rebase stackpointer so that 'word_sub' does not appear in nonoverlapping.
     This helps nonoverlapping reasoning. *)
  WORD_FORALL_OFFSET_TAC 8 THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL] THEN
  REWRITE_TAC[fst EXEC] THEN (* unfold LENGTH (a_mc ...) *)
  STRIP_TAC THEN

  ENSURES_INIT_TAC "s0" THEN

  X86_STEPS_TAC EXEC (1--1) THEN
  FIRST_X_ASSUM (fun th -> MP_TAC th THEN IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD]
      THEN DISCH_TAC) THEN

  (* Prepare load z. *)
  EXPLODE_BYTELIST_ASSUM_TAC "z" THEN
  INTRO_READ_MEMORY_FROM_BYTES8_TAC
    `read (memory :> bytes32 (word z)) s1` THEN

  (* load z and add *)
  X86_STEPS_TAC EXEC (2--4) THEN

  SUBGOAL_THEN `val (word_add i (word 1):int64) < 10` ASSUME_TAC THENL [
    REWRITE_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64] THEN
    UNDISCH_TAC `val (i:int64) < 9` THEN ARITH_TAC;
    ALL_TAC
  ] THEN

  (* Run the actual call instruction *)
  X86_STEPS_TAC EXEC [5] THEN

  (* Call X86_SUBROUTINE_SIM_TAC with its arguments. *)
  X86_SUBROUTINE_SIM_TAC
   (SPEC_ALL a_mc,EXEC,0,SPEC_ALL a_mc,F_SPEC)
   [`x:num`;`y:num`;`z:num`;`read RDI s`;
    `pc:num`; `stackpointer:int64`; `word (pc + 41):int64`] 6 THEN

  (* RET *)
  X86_STEPS_TAC EXEC [7] THEN

  (* Prove the postcondition. *)
  ENSURES_FINAL_STATE_TAC THEN

  ASM_REWRITE_TAC[VAL_WORD_ADD;DIMINDEX_64] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN
  IMP_REWRITE_TAC[MOD_LT] THEN ASM_ARITH_TAC);;
