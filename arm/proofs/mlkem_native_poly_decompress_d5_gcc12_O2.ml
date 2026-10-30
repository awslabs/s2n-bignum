(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 5 bits per coefficient.                *)
(* This is the code for mlkem_poly_decompress_d5 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). It is verified in the whole image (see           *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x20b0, with a *)
(* vector of constants at 0x6210.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    20b0: mov     x6, x0
    20b4: adrp    x0, 6000 <mlkem768_polyvec_mulcache_compute+0x10>
    20b8: movi    v2.4s, #0x10
    20bc: add     x9, x1, #0xa0
    20c0: ldr     q3, [x0, #528]
    20c4: nop
    20c8: add     x1, x1, #0x5
    20cc: ldurb   w0, [x1, #-4]
    20d0: ldurb   w2, [x1, #-5]
    20d4: mov     v4.16b, v2.16b
    20d8: ldurb   w3, [x1, #-3]
    20dc: lsl     w4, w0, #3
    20e0: and     w5, w2, #0x1f
    20e4: orr     w2, w4, w2, lsr #5
    20e8: fmov    s0, w5
    20ec: and     w4, w2, #0x1f
    20f0: ubfx    x7, x0, #2, #5
    20f4: lsl     w2, w3, #1
    20f8: ldurb   w5, [x1, #-1]
    20fc: mov     v0.b[1], w4
    2100: orr     w2, w2, w0, lsr #7
    2104: ldurb   w0, [x1, #-2]
    2108: and     w2, w2, #0x1f
    210c: fmov    s1, w5
    2110: mov     v0.b[2], w7
    2114: lsl     w8, w0, #4
    2118: orr     w3, w8, w3, lsr #4
    211c: ubfx    x4, x0, #1, #5
    2120: and     w3, w3, #0x1f
    2124: lsl     w8, w5, #2
    2128: orr     w0, w8, w0, lsr #6
    212c: ushr    v1.2s, v1.2s, #3
    2130: mov     v0.b[3], w2
    2134: and     w0, w0, #0x1f
    2138: mov     v0.b[4], w3
    213c: mov     v0.b[5], w4
    2140: mov     v0.b[6], w0
    2144: mov     v0.b[7], v1.b[0]
    2148: mov     v1.16b, v2.16b
    214c: uxtl    v0.8h, v0.8b
    2150: umlal   v1.4s, v0.4h, v3.4h
    2154: umlal2  v4.4s, v0.8h, v3.8h
    2158: shrn    v0.4h, v1.4s, #5
    215c: shrn2   v0.8h, v4.4s, #5
    2160: str     q0, [x6], #16
    2164: cmp     x1, x9
    2168: b.ne    20c8 <mlkem_poly_decompress_d5+0x18>
    216c: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x20b0,0x2170];;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_CONSTANTS =
  MLKEM_NATIVE_IMAGE_CONST_RULE 0x6210 128;;

(* ------------------------------------------------------------------------- *)
(* The five bytes for eight coefficients, as parts of a 40-bit word.         *)
(* ------------------------------------------------------------------------- *)

let D5_BYTES = prove
 (`!a n i s j.
        read (memory :> bytes(a,160)) s = n /\ i < 32 /\ j < 5
        ==> read (memory :> bytes8(word_add a (word(5 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (40 * i)):40 word) (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `160`; `n:num`; `5 * i + j`; `s:armstate`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (5 * i + j) = 40 * i + 8 * j`]);;

(* ------------------------------------------------------------------------- *)
(* The computation for each coefficient, with its 5-bit field f in the 40    *)
(* bits, and the field as part of the number for the input bytes. The        *)
(* stored lanes are found in the 128-bit store by bit-blasting.              *)
(* ------------------------------------------------------------------------- *)

let D5D_LANE = prove
 (`!f:5 word.
     word_subword
      (word_ushr
        (word_add
          (word_mul (word_zx (word_shl (word_zx (word_zx f:byte):int16) 0):
                     int32)
                    (word 3329))
          (word 16)) 5) (0,16):int16 =
     word((3329 * val f + 16) DIV 32)`,
  GEN_TAC THEN REWRITE_TAC[WORD_SHL_ZERO] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_USHR; VAL_WORD_ADD;
              VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1] THEN
  MP_TAC(ISPEC `f:5 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:5 word)`,`v:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let D5D_FIELD = prove
 (`!n i k. k < 8
     ==> val(word_subword (word(n DIV 2 EXP (40 * i)):40 word)
                          (5 * k,5):5 word) =
         (n DIV 2 EXP (5 * (8 * i + k))) MOD 32`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 5 5 = 5`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 8 ==> 5 * k + 5 <= 40`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `32 = 2 EXP 5`] THEN
  REWRITE_TAC[ARITH_RULE `40 * i + 5 * k = 5 * (8 * i + k)`]);;

let d5d_lanepat =
  `word_subword
    (word_ushr
      (word_add
        (word_mul (word_zx (word_shl (word_zx (t:byte):int16) 0):int32)
                  (word 3329))
        (word 16)) 5) (0,16):int16`;;

let D5D_LANE_RULE th =
  let v = rand(concl th) in
  let ls = find_terms (fun t -> can (term_match [] d5d_lanepat) t) v in
  let gs = map (fun t -> genvar(type_of t)) ls in
  let v' = subst (zip gs ls) v in
  let bth = tryfind (fun g -> BITBLAST_RULE(mk_eq(v',g))) gs in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th (INST (zip ls gs) bth));;

let D5D_FIELD_TAC k =
  W(fun (asl,w) ->
     let lk = lhs w in
     let _,tmins,_ = term_match [] d5d_lanepat lk in
     let tk = rev_assoc `t:byte` tmins in
     let fth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D5D_FIELD)
          (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                         (mk_small_numeral k) `8`)))) in
     let st = rand(lhand(concl fth)) in
     let st' = subst [`w:40 word`,`word(n DIV 2 EXP (40 * i)):40 word`] st in
     SUBGOAL_THEN (mk_eq(tk,mk_comb(`word_zx:5 word->byte`,st')))
       SUBST1_TAC THENL
      [W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)); ALL_TAC] THEN
     REWRITE_TAC[D5D_LANE] THEN EXPAND_TAC "w" THEN REWRITE_TAC[fth] THEN
     REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 5 in common/fips203.ml, the    *)
(* result for a 5-bit field y is the integer closest to 3329 * y / 32,       *)
(* rounding up on ties, i.e. (3329 * y + 16) DIV 32.                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,0x6480); (a,160)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x20b0) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,160)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (5 * i)) MOD 2 EXP 5 +
                                16) DIV 32))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x20c8` `pc + 0x2164`
   `\i s. read X1 s = word_add a (word(5 * i)) /\
          read X6 s = word_add r (word(16 * i)) /\
          read X9 s = word_add a (word 160) /\
          read Q2 s = word 0x00000010000000100000001000000010 /\
          read Q3 s = word 0x0d010d010d010d010d010d010d010d01 /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,160)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (5 * j)) MOD 2 EXP 5 + 16)
                        DIV 32))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vector of constants from the image ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o
      MATCH_MP MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_CONSTANTS) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (3--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for five bytes and eight coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun j ->
      MP_TAC(REWRITE_RULE[ADD_CLAUSES]
       (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
         (SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`;
                 mk_small_numeral j] D5_BYTES))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) (0--4) THEN
    ABBREV_TAC `w:40 word = word(n DIV 2 EXP (40 * i))` THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--39) THEN
    FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
             concl)) THEN
    DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o D5D_LANE_RULE o
                         CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])))
                         (CONJUNCTS th)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 8 * (i + 1) <=>
      j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
      j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
      j = 8 * i + 7`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * 8 * i = 16 * i`;
                ARITH_RULE `2 * (8 * i + 1) = 16 * i + 2`;
                ARITH_RULE `2 * (8 * i + 2) = 16 * i + 4`;
                ARITH_RULE `2 * (8 * i + 3) = 16 * i + 6`;
                ARITH_RULE `2 * (8 * i + 4) = 16 * i + 8`;
                ARITH_RULE `2 * (8 * i + 5) = 16 * i + 10`;
                ARITH_RULE `2 * (8 * i + 6) = 16 * i + 12`;
                ARITH_RULE `2 * (8 * i + 7) = 16 * i + 14`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL (map D5D_FIELD_TAC (0--7));

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_decompress_d5_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 160]", "true")],
   "void",
   [("a", "160", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + 0x6210):int64`,`16`]
    ~keep_maychanges:true
    mlkem_native_poly_decompress_d5_signature
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,0x6480; a,160]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x20b0) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2
                         [a,160; r,512; word (pc + 0x6210),16]
                         [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc returnaddress)
        (APPEND
          (ENUMERATEL 32 (\i. f_ev_loop a r pc returnaddress i))
          (f_ev_prol a r pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x20c8` `pc + 0x216c`
    `\i s. read X30 s = returnaddress /\
           read X1 s = word_add a (word(5 * i)) /\
           read X6 s = word_add r (word(16 * i)) /\
           read X9 s = word_add a (word 160)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (3--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O2_EXEC (1--41) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add (word_add a (word (5 * i))) (word 5))
                   (word_add a (word 160)):int64) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add (word_add a y) z) (word_add a x):int64 =
      word_sub (word_add y z) x`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 5 * i + 5 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`;
                ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
