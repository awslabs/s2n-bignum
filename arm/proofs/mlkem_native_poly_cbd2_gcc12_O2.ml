(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of a polynomial from the centered binomial distribution with     *)
(* eta = 2. This is the code for mlkem_poly_cbd2 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which the compiler has partly vectorized. It is  *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x4e40, with vectors of shift amounts at 0x6250.   *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    4e40: mov     x5, x0
    4e44: adrp    x0, 6000 <mlkem768_polyvec_mulcache_compute+0x10>
    4e48: adrp    x2, 6000 <mlkem768_polyvec_mulcache_compute+0x10>
    4e4c: mov     x4, x1
    4e50: ldr     q7, [x0, #608]
    4e54: adrp    x0, 6000 <mlkem768_polyvec_mulcache_compute+0x10>
    4e58: ldr     q16, [x2, #592]
    4e5c: mov     x1, #0x0
    4e60: ldr     q6, [x0, #624]
    4e64: adrp    x0, 6000 <mlkem768_polyvec_mulcache_compute+0x10>
    4e68: movi    v3.8h, #0x3
    4e6c: ldr     q5, [x0, #640]
    4e70: lsl     x2, x1, #4
    4e74: ldr     w0, [x4, x1, lsl #2]
    4e78: add     x1, x1, #0x1
    4e7c: and     w3, w0, #0x55555555
    4e80: lsr     w0, w0, #1
    4e84: and     w0, w0, #0x55555555
    4e88: add     w0, w0, w3
    4e8c: dup     v0.4s, w0
    4e90: ushl    v1.4s, v0.4s, v16.4s
    4e94: ushl    v4.4s, v0.4s, v7.4s
    4e98: ushl    v2.4s, v0.4s, v6.4s
    4e9c: ushl    v0.4s, v0.4s, v5.4s
    4ea0: uzp1    v1.8h, v1.8h, v4.8h
    4ea4: uzp1    v2.8h, v2.8h, v0.8h
    4ea8: and     v0.16b, v1.16b, v3.16b
    4eac: and     v1.16b, v2.16b, v3.16b
    4eb0: sub     v0.8h, v0.8h, v1.8h
    4eb4: str     q0, [x5, x2]
    4eb8: cmp     x1, #0x20
    4ebc: b.ne    4e70 <mlkem_poly_cbd2+0x30>
    4ec0: ret
 ***)

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x4e40,0x4ec4];;

(*** The vectors of 32-bit shifts, negative for right shifts ***)

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_CONSTANTS =
  map (fun d -> MLKEM_NATIVE_IMAGE_CONST_RULE d 128)
      [0x6250; 0x6260; 0x6270; 0x6280];;

(* ------------------------------------------------------------------------- *)
(* Each iteration loads a 32-bit word t of the input and adds its pairs of   *)
(* bits. Coefficient j of 8 is computed from the sum shifted right by 4 * j  *)
(* and 4 * j + 2, which depends only on the 4-bit field j of t. Below, the   *)
(* computation on a 4-bit field is checked for all its values and related    *)
(* to the bits of the number for the input bytes.                            *)
(* ------------------------------------------------------------------------- *)

let NIBBLE_BIT = prove
 (`!n m k. k < 4
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 16) DIV 2 EXP k) MOD 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP m`,`x:num`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM(SPEC `2` EXP_1)] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; ARITH_RULE `16 = 2 EXP 4`;
              MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k < 4 ==> MIN 4 (k + 1) = k + 1`]);;

let CBD2_NIBBLE = prove
 (`!m. m < 16
       ==> word_sub
            (word_zx (word_add (word_and (word m:4 word) (word 1))
                               (word_and (word_ushr (word m) 1) (word 1))))
            (word_zx (word_add (word_and (word_ushr (word m:4 word) 2)
                                         (word 1))
                               (word_ushr (word m) 3))):int16 =
           iword(&(m MOD 2 + (m DIV 2) MOD 2) -
                 &((m DIV 4) MOD 2 + (m DIV 8) MOD 2))`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)));;

let CBD2_LANE = prove
 (`!n i j t:int32.
      j < 8 /\ word((n DIV 2 EXP (32 * i)) MOD 4294967296) = t
      ==> let x:4 word = word_subword t (4 * j,4) in
          word_sub
            (word_zx (word_add (word_and x (word 1))
                               (word_and (word_ushr x 1) (word 1))))
            (word_zx (word_add (word_and (word_ushr x 2) (word 1))
                               (word_ushr x 3))):int16 =
          iword(&((n DIV 2 EXP (4 * (8 * i + j))) MOD 2 +
                  (n DIV 2 EXP (4 * (8 * i + j) + 1)) MOD 2) -
                &((n DIV 2 EXP (4 * (8 * i + j) + 2)) MOD 2 +
                  (n DIV 2 EXP (4 * (8 * i + j) + 3)) MOD 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `word_subword (word((n DIV 2 EXP (32 * i)) MOD 4294967296):int32)
                 (4 * j,4):4 word =
    word((n DIV 2 EXP (4 * (8 * i + j))) MOD 16)`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
    ANTS_TAC THENL
     [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`] THEN
    ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `j < 8 ==> 4 * j + 4 <= 32`] THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 4 = 16`] THEN
    REWRITE_TAC[ARITH_RULE `32 * i + 4 * j = 4 * (8 * i + j)`];
    ALL_TAC] THEN
  SIMP_TAC[CBD2_NIBBLE; MOD_LT_EQ; ARITH_EQ] THEN
  SIMP_TAC[NIBBLE_BIT; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GEN_ALL(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`x:num`; `2`; `8`] MOD_MOD))]);;

(*** Lane j of the 128-bit store, for t as given by tth ***)

let CBD2_LANE_RULE tth th =
  let addr = rand(rand(rand(rator(lhand(concl th))))) in
  let j = match addr with
      Comb(Comb(Const("word_add",_),Comb(Comb(Const("word_add",_),_),_)),
           Comb(Const("word",_),k)) -> dest_small_numeral k / 2
    | _ -> 0 in
  let jt = mk_small_numeral j in
  let lth = CONV_RULE(TOP_DEPTH_CONV let_CONV THENC
                      ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                      REWRITE_CONV[ADD_CLAUSES])
   (MP (SPECL [`n:num`; `i:num`; jt; `t:int32`] CBD2_LANE)
       (CONJ (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` jt `8`)))
             tth)) in
  let eq = mk_eq(rand(concl th),lhs(concl lth)) in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th (TRANS (BITBLAST_RULE eq) lth));;

(*** The first step of the loop body, normalizing the offset 16 * i ***)

let CBD2_INDEX_TAC =
  SUBGOAL_THEN `val(word i:int64) = i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `i < 32` THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC [1] THEN
  FIRST_X_ASSUM(ASSUME_TAC o
    CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_SHL_WORD] THENC
                        ONCE_DEPTH_CONV NUM_REDUCE_CONV)) o
    check (can (term_match [] `read X2 s = x`) o concl));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_cbd 2 in common/fips203.ml, coefficient i *)
(* of the result is the number of 1 bits among bits 4 * i and 4 * i + 1 of   *)
(* the 128 bytes as a number n, minus the number among bits 4 * i + 2 and    *)
(* 4 * i + 3, here as a 16-bit integer rather than modulo 3329.              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,0x6480); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x4e40) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + 0x4e70` `pc + 0x4eb8`
   `\i s. read X1 s = word i /\
          read X4 s = a /\
          read X5 s = r /\
          read Q3 s = word 0x00030003000300030003000300030003 /\
          read Q5 s = word 0xffffffe2ffffffe6ffffffeaffffffee /\
          read Q6 s = word 0xfffffff2fffffff6fffffffafffffffe /\
          read Q7 s = word 0xffffffe4ffffffe8ffffffecfffffff0 /\
          read Q16 s = word 0xfffffff4fffffff8fffffffc00000000 /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,128)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   iword(&((n DIV 2 EXP (4 * j)) MOD 2 +
                           (n DIV 2 EXP (4 * j + 1)) MOD 2) -
                         &((n DIV 2 EXP (4 * j + 2)) MOD 2 +
                           (n DIV 2 EXP (4 * j + 3)) MOD 2)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vectors of shifts from the image ***)

    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
      MLKEM_NATIVE_POLY_CBD2_GCC12_O2_CONSTANTS THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (4--6) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (7--10) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (11--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for four bytes and eight coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `128`; `n:num`; `4 * i`; `s0:armstate`]
                 READ_MEMORY_BYTES32_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `8 * 4 * i = 32 * i`]) THEN
    ABBREV_TAC `t:int32 = word((n DIV 2 EXP (32 * i)) MOD 4294967296)` THEN
    CBD2_INDEX_TAC THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (2--18) THEN
    FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
             concl)) THEN
    FIRST_ASSUM(fun tth ->
      if can (term_match []
               `word((n DIV 2 EXP (32 * i)) MOD 4294967296):int32 = t`)
             (concl tth)
      then DISCH_THEN(fun th ->
             MAP_EVERY (ASSUME_TAC o CBD2_LANE_RULE tth o
                        CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])))
                       (CONJUNCTS th))
      else failwith "CBD2_LANE_RULE") THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 8 * (i + 1) <=>
      j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
      j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
      j = 8 * i + 7`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * 8 * i = 16 * i`] THEN
    REWRITE_TAC(map (fun k ->
      ARITH_RULE(subst [mk_small_numeral k,`k:num`;
                        mk_small_numeral(2 * k),`l:num`]
                       `2 * (8 * i + k) = 16 * i + l`)) (1--7)) THEN
    ASM_REWRITE_TAC[];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (2--3) THEN
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

let mlkem_native_poly_cbd2_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 128]", "true")],
   "void",
   [("a", "128", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + 0x6250):int64`,`64`]
    ~keep_maychanges:true
    mlkem_native_poly_cbd2_signature
    MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,0x6480; a,128]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x4e40) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2
                         [a,128; r,512; word (pc + 0x6250),64]
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
              fst MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + 0x4e70` `pc + 0x4ec0`
    `\i s. read X30 s = returnaddress /\
           read X1 s = word i /\
           read X4 s = a /\
           read X5 s = r` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (4--6) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (7--10) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (11--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  CBD2_INDEX_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (2--20) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(val(word_add (word i) (word 18446744073709551585):int64) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    ASM_CASES_TAC `i = 31` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 /\ ~(i = 31)
      ==> i + 18446744073709551585 < 18446744073709551616`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
