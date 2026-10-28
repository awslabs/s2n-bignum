(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of polynomial coefficients to Montgomery form.                 *)
(* This is the code for mlkem_poly_tomont from mlkem-native's portable C     *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which the compiler has vectorized. It reads its own vectors of constants  *)
(* from the read-only data.                                                  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;

(**** print_literal_relocs_from_elf
        ~map_symbol_name:(fun _ ->
          "mlkem_native_poly_tomont_gcc12_O2_data")
        "arm/mlkem_native/mlkem_native_poly_tomont_gcc12_O2.o";;
 ****)

let mlkem_native_poly_tomont_gcc12_O2_mc,
    mlkem_native_poly_tomont_gcc12_O2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "WHOLE_READONLY" | "ltmp1"
      | "mlkem_native_poly_tomont_gcc12_O2_constants" ->
          "mlkem_native_poly_tomont_gcc12_O2_data"
      | s -> failwith ("unknown symbol: " ^ s))
    "mlkem_native_poly_tomont_gcc12_O2_mc"
    "arm/mlkem_native/mlkem_native_poly_tomont_gcc12_O2.o"
(fun w BL ADR ADRP ADD_rri64 LDR_Q_rri -> [
  ADRP (mk_var("mlkem_native_poly_tomont_gcc12_O2_data",`:num`),16,0,2);
  ADRP (mk_var("mlkem_native_poly_tomont_gcc12_O2_data",`:num`),0,4,1);
  w 0x6f00a5a3;         (* arm_MOVI Q3 (word 17509981057347220223) *)
  LDR_Q_rri (mk_var("mlkem_native_poly_tomont_gcc12_O2_data",`:num`),16,5,2);
  LDR_Q_rri (mk_var("mlkem_native_poly_tomont_gcc12_O2_data",`:num`),0,4,1);
  w 0x91080001;         (* arm_ADD X1 X0 (rvalue (word 512)) *)
  w 0x3dc00000;         (* arm_LDR Q0 X0 (Immediate_Offset (word 0)) *)
  w 0x0e64c001;         (* arm_SMULL_VEC Q1 Q0 Q4 16 *)
  w 0x4e64c000;         (* arm_SMULL2_VEC Q0 Q0 Q4 16 *)
  w 0x4e401822;         (* arm_UZP1 Q2 Q1 Q0 16 *)
  w 0x4e659c42;         (* arm_MUL_VEC Q2 Q2 Q5 16 128 *)
  w 0x0e638041;         (* arm_SMLAL_VEC Q1 Q2 Q3 16 *)
  w 0x4e638040;         (* arm_SMLAL2_VEC Q0 Q2 Q3 16 *)
  w 0x4e405821;         (* arm_UZP2 Q1 Q1 Q0 16 *)
  w 0x3c810401;         (* arm_STR Q1 X0 (Postimmediate_Offset (word 16)) *)
  w 0xeb00003f;         (* arm_CMP X1 X0 *)
  w 0x54fffec1;         (* arm_BNE (word 2097112) *)
  w 0xd65f03c0          (* arm_RET X30 *)
]);;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_poly_tomont_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* The vectors of constants in the read-only data.                           *)
(* ------------------------------------------------------------------------- *)

let TOMONT_CONSTANTS_LOADED = prove
 (`!c s. bytes_loaded s (word c) mlkem_native_poly_tomont_gcc12_O2_data
         ==> read(memory :> bytes128(word c)) s =
             word 0x05490549054905490549054905490549 /\
             read(memory :> bytes128(word(c + 16))) s =
             word 0xf301f301f301f301f301f301f301f301`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
              CONV_RULE(RAND_CONV LENGTH_CONV)
               (AP_TERM `LENGTH:byte list->num`
                  (hd mlkem_native_poly_tomont_gcc12_O2_data))] THEN
  REWRITE_TAC[hd mlkem_native_poly_tomont_gcc12_O2_data; num_of_bytelist] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN
  DISCH_TAC THEN
  REWRITE_TAC[bytes128; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  REWRITE_TAC[WORD_ADD] THEN
  MP_TAC(ISPECL [`word c:int64`; `32`; `16`; `read memory s`]
         READ_BYTES_MOD) THEN
  MP_TAC(ISPECL [`word c:int64`; `32`; `16`; `read memory s`]
         READ_BYTES_DIV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The value computed in each lane.                                          *)
(* ------------------------------------------------------------------------- *)

let TOMONT_LANE = prove
 (`!x:int16.
     (ival(montred_neon(word_mul (word_sx x) (word 1353))) ==
      (&2 pow 16 * ival x) rem &3329) (mod &3329) /\
     abs(ival(montred_neon(word_mul (word_sx x) (word 1353)))) <= &3328`,
  GEN_TAC THEN REWRITE_TAC[MONTRED_NEON_SCALAR; INT_CONG_RREM] THEN
  MP_TAC(MLKEM_NATIVE_CONGBOUND_RULE undefined
   `montred_scalar(word_mul (word_sx (x:int16)) (word 1353))`) THEN
  MATCH_MP_TAC(TAUT `(p ==> p') /\ (q ==> q') ==> p /\ q ==> p' /\ q'`) THEN
  CONJ_TAC THENL [ALL_TAC; INT_ARITH_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(a * b:int == c) (mod n)
    ==> (x == a * y * b) (mod n) ==> (x == c * y) (mod n)`) THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_CORRECT = prove
 (`!a consts x pc.
    adrp_within_bounds (word(consts + 16)) (word pc) /\
    adrp_within_bounds (word consts) (word(pc + 4)) /\
    aligned 16 (word consts:int64) /\
    ALL (nonoverlapping (a,512)) [(word pc,0x48); (word consts,32)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
           read PC s = word pc /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word consts)
             mlkem_native_poly_tomont_gcc12_O2_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word (2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + 0x44) /\
           !i. i < 256
               ==> let z_i = read(memory :> bytes16
                                (word_add a (word (2 * i)))) s in
                   (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `consts:num`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x18` `pc + 0x3c`
   `\i s. read X0 s = word_add a (word(16 * i)) /\
          read X1 s = word_add a (word 512) /\
          read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
          read Q4 s = word 0x05490549054905490549054905490549 /\
          read Q5 s = word 0xf301f301f301f301f301f301f301f301 /\
          (!j. 8 * i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          (!j. j < 8 * i
               ==> let z_j = read(memory :> bytes16
                                (word_add a (word(2 * j)))) s in
                   (ival z_j == (tomont_3329 (ival o x)) j) (mod &3329) /\
                   abs(ival z_j) <= &3328)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, loading the constants from their addresses ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TOMONT_CONSTANTS_LOADED) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (1--3) THEN
    SUBGOAL_THEN `aligned 16 (word(consts + 16):int64)` ASSUME_TAC THENL
     [REWRITE_TAC[WORD_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`word pc:int64`; `word(consts + 16):int64`]
           ADRP_LDR_Q_FOLD) THEN
    MP_TAC(SPECL [`word(pc + 4):int64`; `word consts:int64`]
           ADRP_LDR_Q_FOLD) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (4--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[];

    (*** The loop body, for 8 coefficients loaded as one 128-bit word ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [MATCH_MP CHUNK8_INPUT_SPLIT (ASSUME `i < 32`)]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add a (word(16 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[montred_neon]) (1--9) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
             concl)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[tomont_3329; o_THM; TOMONT_LANE];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `tomont_3329` (concl th)))]);;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!a consts x pc returnaddress.
    adrp_within_bounds (word(consts + 16)) (word pc) /\
    adrp_within_bounds (word consts) (word(pc + 4)) /\
    aligned 16 (word consts:int64) /\
    ALL (nonoverlapping (a,512)) [(word pc,0x48); (word consts,32)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word consts)
             mlkem_native_poly_tomont_gcc12_O2_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word (2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 256
               ==> let z_i = read(memory :> bytes16
                                (word_add a (word (2 * i)))) s in
                   (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,512)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The signature is the same as for mlkem_tomont, and the vectors of ***)
(*** constants are a read-only object.                                 ***)

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word consts:int64`,`32`]
    ~keep_maychanges:false
    (assoc "mlkem_tomont" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a consts pc returnaddress.
           adrp_within_bounds (word (consts + 16)) (word pc) /\
           adrp_within_bounds (word consts) (word (pc + 4)) /\
           aligned 16 (word consts:int64) /\
           ALL (nonoverlapping (a,512)) [word pc,72; word consts,32]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
                    read PC s = word pc /\
                    bytes_loaded s (word consts)
                     mlkem_native_poly_tomont_gcc12_O2_data /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events a consts pc returnaddress /\
                        memaccess_inbounds e2
                         [a,512; word consts,32] [a,512])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (consts:num) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a consts pc returnaddress)
        (APPEND
          (ENUMERATEL 32 (\i. f_ev_loop a consts pc returnaddress i))
          (f_ev_prol a consts pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              fst MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x18` `pc + 0x44`
    `\i s. read X30 s = returnaddress /\
           read X0 s = word_add a (word(16 * i)) /\
           read X1 s = word_add a (word 512)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (1--3) THEN
    SUBGOAL_THEN `aligned 16 (word(consts + 16):int64)` ASSUME_TAC THENL
     [REWRITE_TAC[WORD_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`word pc:int64`; `word(consts + 16):int64`]
           ADRP_LDR_Q_FOLD) THEN
    MP_TAC(SPECL [`word(pc + 4):int64`; `word consts:int64`]
           ADRP_LDR_Q_FOLD) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (4--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (1--11) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add a (word 512))
                   (word_add (word_add a (word (16 * i))) (word 16)):int64) =
      0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
      word_sub x (word_add y z)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 16 * i + 16 < 18446744073709551616`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
