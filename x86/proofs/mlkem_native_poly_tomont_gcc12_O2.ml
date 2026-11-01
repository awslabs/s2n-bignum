(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of polynomial coefficients to Montgomery form.                 *)
(* This is the code for mlkem_poly_tomont from mlkem-native's portable C     *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which the compiler has vectorized using SSE2.                             *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;

(**** print_literal_relocs_from_elf
        ~map_symbol_name:(fun _ ->
          "mlkem_native_poly_tomont_gcc12_O2_data")
        "x86/mlkem_native/mlkem_native_poly_tomont_gcc12_O2.o";;
 ****)

let mlkem_native_poly_tomont_gcc12_O2_mc,
    mlkem_native_poly_tomont_gcc12_O2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "WHOLE_READONLY" | "mlkem_native_poly_tomont_gcc12_O2_constants" ->
          "mlkem_native_poly_tomont_gcc12_O2_data"
      | s -> failwith ("unknown symbol: " ^ s))
    "mlkem_native_poly_tomont_gcc12_O2_mc"
    "x86/mlkem_native/mlkem_native_poly_tomont_gcc12_O2.o"
(fun b ADDR -> [b[
  0x66; 0x0f; 0x6f; 0x2d];
  ADDR ("mlkem_native_poly_tomont_gcc12_O2_data",(-4)); b[
                           (* MOVDQA (%_% xmm5) (Memop Word128 (Riprel (word_sx
                                     (iword
                                     (&mlkem_native_poly_tomont_gcc12_O2_data -
                                     (&pc + &8)))))) *)
  0x66; 0x0f; 0x6f; 0x35];
  ADDR ("mlkem_native_poly_tomont_gcc12_O2_data",(12)); b[
                           (* MOVDQA (%_% xmm6) (Memop Word128 (Riprel (word_sx
                                     (iword
                                     (&mlkem_native_poly_tomont_gcc12_O2_data -
                                     (&pc + -- &0)))))) *)
  0x48; 0x8d; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* LEA (% rax) (%% (rdi,512)) *)
  0x66; 0x0f; 0x6f; 0x25];
  ADDR ("mlkem_native_poly_tomont_gcc12_O2_data",(28)); b[
                           (* MOVDQA (%_% xmm4) (Memop Word128 (Riprel (word_sx
                                     (iword
                                     (&mlkem_native_poly_tomont_gcc12_O2_data -
                                     (&pc + -- &1)))))) *)
  0x90;                    (* NOP *)
  0x66; 0x0f; 0x6f; 0x1f;  (* MOVDQA (%_% xmm3) (Memop Word128 (%% (rdi,0))) *)
  0x66; 0x0f; 0x6f; 0xc5;  (* MOVDQA (%_% xmm0) (%_% xmm5) *)
  0x66; 0x0f; 0xe5; 0x07;  (* PMULHW (%_% xmm0) (Memop Word128 (%% (rdi,0))) *)
  0x48; 0x83; 0xc7; 0x10;  (* ADD (% rdi) (Imm8 (word 16)) *)
  0x66; 0x0f; 0xd5; 0xdd;  (* PMULLW (%_% xmm3) (%_% xmm5) *)
  0x66; 0x0f; 0x6f; 0xfb;  (* MOVDQA (%_% xmm7) (%_% xmm3) *)
  0x66; 0x0f; 0x69; 0xd8;  (* PUNPCKHWD (%_% xmm3) (%_% xmm0) *)
  0x66; 0x0f; 0x61; 0xf8;  (* PUNPCKLWD (%_% xmm7) (%_% xmm0) *)
  0x66; 0x0f; 0x6f; 0xc7;  (* MOVDQA (%_% xmm0) (%_% xmm7) *)
  0x66; 0x0f; 0x6f; 0xcf;  (* MOVDQA (%_% xmm1) (%_% xmm7) *)
  0x66; 0x0f; 0x61; 0xc3;  (* PUNPCKLWD (%_% xmm0) (%_% xmm3) *)
  0x66; 0x0f; 0x69; 0xcb;  (* PUNPCKHWD (%_% xmm1) (%_% xmm3) *)
  0x66; 0x0f; 0x6f; 0xd0;  (* MOVDQA (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x61; 0xc1;  (* PUNPCKLWD (%_% xmm0) (%_% xmm1) *)
  0x66; 0x0f; 0x69; 0xd1;  (* PUNPCKHWD (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x61; 0xc2;  (* PUNPCKLWD (%_% xmm0) (%_% xmm2) *)
  0x66; 0x0f; 0xd5; 0xc6;  (* PMULLW (%_% xmm0) (%_% xmm6) *)
  0x66; 0x0f; 0x6f; 0xd0;  (* MOVDQA (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x6f; 0xc8;  (* MOVDQA (%_% xmm1) (%_% xmm0) *)
  0x66; 0x0f; 0xe5; 0xcc;  (* PMULHW (%_% xmm1) (%_% xmm4) *)
  0x66; 0x0f; 0xd5; 0xd4;  (* PMULLW (%_% xmm2) (%_% xmm4) *)
  0x66; 0x0f; 0x6f; 0xc2;  (* MOVDQA (%_% xmm0) (%_% xmm2) *)
  0x66; 0x0f; 0x69; 0xd1;  (* PUNPCKHWD (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x61; 0xc1;  (* PUNPCKLWD (%_% xmm0) (%_% xmm1) *)
  0x66; 0x0f; 0x6f; 0xca;  (* MOVDQA (%_% xmm1) (%_% xmm2) *)
  0x66; 0x0f; 0xfe; 0xc7;  (* PADDD (%_% xmm0) (%_% xmm7) *)
  0x66; 0x0f; 0xfe; 0xcb;  (* PADDD (%_% xmm1) (%_% xmm3) *)
  0x66; 0x0f; 0x72; 0xe1; 0x10;
                           (* PSRAD (%_% xmm1) (Imm8 (word 16)) *)
  0x66; 0x0f; 0x72; 0xe0; 0x10;
                           (* PSRAD (%_% xmm0) (Imm8 (word 16)) *)
  0x66; 0x0f; 0x6f; 0xd0;  (* MOVDQA (%_% xmm2) (%_% xmm0) *)
  0x66; 0x0f; 0x61; 0xc1;  (* PUNPCKLWD (%_% xmm0) (%_% xmm1) *)
  0x66; 0x0f; 0x69; 0xd1;  (* PUNPCKHWD (%_% xmm2) (%_% xmm1) *)
  0x66; 0x0f; 0x6f; 0xc8;  (* MOVDQA (%_% xmm1) (%_% xmm0) *)
  0x66; 0x0f; 0x69; 0xca;  (* PUNPCKHWD (%_% xmm1) (%_% xmm2) *)
  0x66; 0x0f; 0x61; 0xc2;  (* PUNPCKLWD (%_% xmm0) (%_% xmm2) *)
  0x66; 0x0f; 0x61; 0xc1;  (* PUNPCKLWD (%_% xmm0) (%_% xmm1) *)
  0x0f; 0x29; 0x47; 0xf0;  (* MOVAPS (Memop Word128 (%%
                                     (rdi,18446744073709551600))) (%_% xmm0) *)
  0x48; 0x39; 0xf8;        (* CMP (% rax) (% rdi) *)
  0x0f; 0x85; 0x61; 0xff; 0xff; 0xff;
                           (* JNE (Imm32 (word 4294967137)) *)
  0xc3                     (* RET *)
]]);;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_poly_tomont_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* The vectors of constants in the read-only data.                           *)
(* ------------------------------------------------------------------------- *)

let TOMONT_CONSTANTS_LOADED = prove
 (`!c s. bytes_loaded s (word c) mlkem_native_poly_tomont_gcc12_O2_data
         ==> read(memory :> bytes128(word c)) s =
             word 0x05490549054905490549054905490549 /\
             read(memory :> bytes128(word(c + 16))) s =
             word 0xf301f301f301f301f301f301f301f301 /\
             read(memory :> bytes128(word(c + 32))) s =
             word 0xf2fff2fff2fff2fff2fff2fff2fff2ff`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[WORD_ADD_0]
   `word c:int64 = word_add (word c) (word 0)`] THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC; WORD_ADD_0] THEN
  MAP_EVERY (fun k ->
     MP_TAC(SPECL [`word c:int64`; `mlkem_native_poly_tomont_gcc12_O2_data`;
                   k; `s:x86state`] BYTES_LOADED_BYTES128))
   [`0`; `16`; `32`] THEN
  ASM_REWRITE_TAC[CONV_RULE(RAND_CONV LENGTH_CONV)
               (AP_TERM `LENGTH:byte list->num`
                  (hd mlkem_native_poly_tomont_gcc12_O2_data))] THEN
  REWRITE_TAC[hd mlkem_native_poly_tomont_gcc12_O2_data; num_of_bytelist] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The value computed in each lane. The compiler forms the 32-bit products   *)
(* from the 16-bit high and low halves given by PMULHW and PMULLW, which it  *)
(* interleaves and later de-interleaves with PUNPCKLWD and PUNPCKHWD.        *)
(* ------------------------------------------------------------------------- *)

let TOMONT_LANE_FORM = prove
 (`!x:int16.
     word_subword
      (word_ishr
        (word_add
          (word_join
            (word_subword
              (word_mul (word_sx (word_mul (word_mul x (word 1353))
                                           (word 62209)):int32)
                        (word 4294963967))
              (16,16):int16)
            (word_mul (word_mul (word_mul x (word 1353)) (word 62209))
                      (word 62207)):int32)
          (word_join
            (word_subword (word_mul (word 1353) (word_sx x:int32))
                          (16,16):int16)
            (word_mul x (word 1353)):int32))
        16)
      (0,16):int16 =
     montred_x86 (word_mul (word_sx x) (word 1353))`,
  GEN_TAC THEN
  MP_TAC(ISPECL
   [`word_mul (word_mul (x:int16) (word 1353)) (word 62209):int16`;
    `word 62207:int16`] WORD_JOIN_MULHI_MULLO) THEN
  MP_TAC(ISPECL [`word 1353:int16`; `x:int16`] WORD_JOIN_MULHI_MULLO) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[ISPECL [`x:int16`; `word 1353:int16`] WORD_MUL_SYM] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[montred_x86] THEN
  SIMP_TAC[WORD_ZX_MUL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  REWRITE_TAC[WORD_BLAST `word_zx(word_sx (x:int16):int32) = x`] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[ISPECL [`word_sx (x:int16):int32`; `word 1353:int32`]
               WORD_MUL_SYM] THEN
  REWRITE_TAC[ISPECL [`word 1353:int16`; `x:int16`] WORD_MUL_SYM] THEN
  REWRITE_TAC[WORD_BLAST `word_subword (y:int32) (0,16):int16 = word_zx y`]);;

let TOMONT_LANE = prove
 (`!x:int16.
     (ival(montred_x86(word_mul (word_sx x) (word 1353))) ==
      (&2 pow 16 * ival x) rem &3329) (mod &3329) /\
     abs(ival(montred_x86(word_mul (word_sx x) (word 1353)))) <= &3328`,
  GEN_TAC THEN REWRITE_TAC[MONTRED_X86_SCALAR; INT_CONG_RREM] THEN
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
    aligned 16 a /\ aligned 16 (word consts:int64) /\
    riprel32_within_bounds consts (pc + 8) /\
    riprel32_within_bounds (consts + 16) (pc + 16) /\
    riprel32_within_bounds (consts + 32) (pc + 31) /\
    ALL (nonoverlapping (a,512)) [(word pc,0xc0); (word consts,48)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
           read RIP s = word pc /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word consts)
             mlkem_native_poly_tomont_gcc12_O2_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word (2 * i)))) s =
                    x i))
      (\s. read RIP s = word(pc + 0xbf) /\
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

  ENSURES_WHILE_UP_TAC `32` `pc + 0x20` `pc + 0xb6`
   `\i s. read RDI s = word_add a (word(16 * i)) /\
          read RAX s = word_add a (word 512) /\
          read XMM5 s = word 0x05490549054905490549054905490549 /\
          read XMM6 s = word 0xf301f301f301f301f301f301f301f301 /\
          read XMM4 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
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

    RIPREL_FOLD_TAC `consts:num` `8` `&8:int` `0` THEN
    RIPREL_FOLD_TAC `consts:num` `16` `&0:int` `16` THEN
    RIPREL_FOLD_TAC `consts:num` `31` `-- &1:int` `32` THEN
    SUBGOAL_THEN `aligned 16 (word(consts + 16):int64) /\
                  aligned 16 (word(consts + 32):int64)` STRIP_ASSUME_TAC
    THENL
     [REWRITE_TAC[WORD_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TOMONT_CONSTANTS_LOADED) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[XMM4; XMM5; XMM6; READ_ZEROTOP_128] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[];

    (*** The loop body, for 8 coefficients loaded as one 128-bit word ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm7_init:int256` `read YMM7` THEN
    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    XMM_EXISTSTOP_TAC "top5" `YMM5` THEN
    XMM_EXISTSTOP_TAC "top6" `YMM6` THEN
    SUBGOAL_THEN `aligned 16 (word_add a (word (16 * i)):int64)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC ALIGNED_WORD_ADD THEN
      ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
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
      X86_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[]) (1--37) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
             concl)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[XMM4; XMM5; XMM6; READ_ZEROTOP_128] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
    REWRITE_TAC[CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TOMONT_LANE_FORM] THEN
    REWRITE_TAC[tomont_3329; o_THM; TOMONT_LANE];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word 512))
                     (word_add a (word (16 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y) = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 16 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `tomont_3329` (concl th)))]);;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!a consts x pc stackpointer returnaddress.
    aligned 16 a /\ aligned 16 (word consts:int64) /\
    riprel32_within_bounds consts (pc + 8) /\
    riprel32_within_bounds (consts + 16) (pc + 16) /\
    riprel32_within_bounds (consts + 32) (pc + 31) /\
    ALL (nonoverlapping (a,512))
        [(word pc,0xc0); (word consts,48); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [a] s /\
           bytes_loaded s (word consts)
             mlkem_native_poly_tomont_gcc12_O2_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word (2 * i)))) s =
                    x i))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 256
               ==> let z_i = read(memory :> bytes16
                                (word_add a (word (2 * i)))) s in
                   (ival z_i == (tomont_3329 (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(a,512)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** The signature is the same as for mlkem_tomont, and the vectors of ***)
(*** constants are a read-only object.                                 ***)

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word consts:int64`,`48`]
    ~keep_maychanges:true
    (assoc "mlkem_tomont" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_CORRECT
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SAFE = time prove
 (`exists f_events.
       forall e a consts pc.
           aligned 16 a /\ aligned 16 (word consts:int64) /\
           riprel32_within_bounds consts (pc + 8) /\
           riprel32_within_bounds (consts + 16) (pc + 16) /\
           riprel32_within_bounds (consts + 32) (pc + 31) /\
           ALL (nonoverlapping (a,512)) [word pc,0xc0; word consts,48]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                     (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
                    read RIP s = word pc /\
                    bytes_loaded s (word consts)
                     mlkem_native_poly_tomont_gcc12_O2_data /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0xbf) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a consts pc /\
                         memaccess_inbounds e2
                          [a,512; word consts,48] [a,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (consts:num) (pc:num).
      APPEND
        (f_ev_epil a consts pc)
        (APPEND
          (ENUMERATEL 32 (\i. f_ev_loop a consts pc i))
          (f_ev_prol a consts pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x20` `pc + 0xbf`
    `\i s. read RDI s = word_add a (word(16 * i)) /\
           read RAX s = word_add a (word 512)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    RIPREL_FOLD_TAC `consts:num` `8` `&8:int` `0` THEN
    RIPREL_FOLD_TAC `consts:num` `16` `&0:int` `16` THEN
    RIPREL_FOLD_TAC `consts:num` `31` `-- &1:int` `32` THEN
    SUBGOAL_THEN `aligned 16 (word(consts + 16):int64) /\
                  aligned 16 (word(consts + 32):int64)` STRIP_ASSUME_TAC
    THENL
     [REWRITE_TAC[WORD_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `aligned 16 (word_add a (word (16 * i)):int64)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ALIGNED_WORD_ADD THEN
    ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC (1--39) THEN
  SUBGOAL_THEN
   `~(val(word_add a (word 512):int64) =
      val(word_add (word_add a (word (16 * i))) (word 16):int64)) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 16 * i + 16 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a consts pc stackpointer returnaddress.
           aligned 16 a /\ aligned 16 (word consts:int64) /\
           riprel32_within_bounds consts (pc + 8) /\
           riprel32_within_bounds (consts + 16) (pc + 16) /\
           riprel32_within_bounds (consts + 32) (pc + 31) /\
           ALL (nonoverlapping (a,512))
               [word pc,0xc0; word consts,48; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                     (mlkem_native_poly_tomont_gcc12_O2_mc pc consts) /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    bytes_loaded s (word consts)
                     mlkem_native_poly_tomont_gcc12_O2_data /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a consts pc stackpointer
                                       returnaddress /\
                         memaccess_inbounds e2
                          [a,512; word consts,48; stackpointer,8] [a,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(a,512)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_TOMONT_GCC12_O2_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
