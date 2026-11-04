(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a 32-byte message to a polynomial. This is the code for     *)
(* mlkem_poly_frommsg from mlkem-native's portable C implementation compiled *)
(* by clang 17 with -O3 (see mlkem_native/README.md), where the inner loop   *)
(* over the bits of a byte is unrolled. It is verified in the whole image    *)
(* (see libmlkem.ml).                                                        *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image, where the pattern of +0x18 to +0x2c is repeated
 *** for the other bits, with the mask in w12 and the stores at offsets -6,
 *** -4, -2, 0, 2 and 4 from x9:

    mlkem_poly_frommsg:
       +0x0: mov     x8, xzr
       +0x4: add     x9, x0, #0x8
       +0x8: mov     w10, #0x681
       +0xc: mov     w11, #0x1
      +0x10: ldrb    w12, [x1, x8]
      +0x14: and     w11, w11, w12
      +0x18: mov     w12, #0x2
      +0x1c: neg     w11, w11
      +0x20: and     w11, w10, w11, lsr #16
      +0x24: sturh   w11, [x9, #-8]
      +0x28: ldrb    w11, [x1, x8]
      +0x2c: and     w11, w12, w11
      ...
      +0xb8: ldrb    w11, [x1, x8]
      +0xbc: add     x8, x8, #0x1
      +0xc0: cmp     x8, #0x20
      +0xc4: and     w11, w12, w11
      +0xc8: neg     w11, w11
      +0xcc: and     w11, w10, w11, lsr #16
      +0xd0: strh    w11, [x9, #6]
      +0xd4: add     x9, x9, #0x10
      +0xd8: b.ne    <mlkem_poly_frommsg+0xc>
      +0xdc: ret
 ***)

let MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_frommsg"];;

(* ------------------------------------------------------------------------- *)
(* The bits of a byte of an array given as a number.                         *)
(* ------------------------------------------------------------------------- *)

let BYTE_BIT = prove
 (`!n m k. k < 8
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 256) DIV 2 EXP k) MOD 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP m`,`x:num`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM(SPEC `2` EXP_1)] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; ARITH_RULE `256 = 2 EXP 8`;
              MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k < 8 ==> MIN 8 (k + 1) = k + 1`]);;

(* ------------------------------------------------------------------------- *)
(* The stores are at offsets from -8 to 6 from x9, which is 16 * i + 8 bytes *)
(* after r in iteration i. So that the simulation can tell that the stores   *)
(* at negative offsets are inside the output, x9 is given in the invariants  *)
(* as word_sub (word_add r (word(16 * i + 16))) (word 8), and the addresses  *)
(* that the simulation produces from it are put in the form                  *)
(* word_add r (word(16 * i + k)) for 0 <= k < 16 before they are used: in    *)
(* the state, word_add r (word_sub (word(16 * i + 16)) (word c)), by         *)
(* FROMMSG_ADDR_CONV, and in the events, by FROMMSG_EVENT_ADDR_CONV.         *)
(* ------------------------------------------------------------------------- *)

let FROMMSG_ADDR = prove
 (`!i c. c <= 16
         ==> word_sub (word (16 * i + 16)) (word c):int64 =
             word(16 * i + (16 - c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`16 * i + 16`; `c:num`]
    (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
  ASM_SIMP_TAC[ARITH_RULE `c <= 16 ==> c <= 16 * i + 16`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let FROMMSG_ADDR_CONV t =
  let th = PART_MATCH (lhand o rand) FROMMSG_ADDR t in
  let th' = MP th (EQT_ELIM(NUM_LE_CONV (lhand(concl th)))) in
  CONV_RULE (RAND_CONV(RAND_CONV(RAND_CONV NUM_SUB_CONV))) th';;

let FROMMSG_EVENT_ADDR_CONV =
  let pat1 =
    `word_add (word_sub (word_add r (word (16 * i + 16))) (word 8))
              (word c):int64`
  and pat2 = `word_sub (word_add r (word (16 * i + 16))) (word 8):int64`
  and rv,iv,cv,kv = `r:int64`,`i:num`,`c:num`,`k:num`
  and two63 = Num.power_num (Num.num_of_int 2) (Num.num_of_int 63)
  and two64 = Num.power_num (Num.num_of_int 2) (Num.num_of_int 64) in
  fun t ->
    let ins,k,negths =
      try let ins = term_match [] pat1 t in
          let c = dest_numeral (instantiate ins cv) in
          let k = Num.mod_num (Num.add_num (Num.num_of_int 8) c) two64 in
          let negths =
            if Num.lt_num c two63 then [] else
            [SYM(WORD_REDUCE_CONV
              (mk_comb(`word_neg:int64->int64`,
                       mk_comb(`word:num->int64`,
                               mk_numeral(Num.sub_num two64 c)))))] in
          ins,k,negths
      with Failure _ -> term_match [] pat2 t,Num.num_of_int 8,[] in
    let rhs = subst [instantiate ins rv,rv; instantiate ins iv,iv;
                     mk_numeral k,kv]
               `word_add r (word(16 * i + k)):int64` in
    prove(mk_eq(t,rhs),
          REWRITE_TAC negths THEN REWRITE_TAC[WORD_ADD] THEN
          CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 1 in common/fips203.ml, the    *)
(* result for a bit y is the integer closest to 3329 * y / 2, rounding up on *)
(* ties, i.e. (3329 * y + 1) DIV 2.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_frommsg) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,32)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP i) MOD 2 + 1) DIV 2))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop over the bytes, with the test at the end of the body ***)

  ENSURES_WHILE_UP2_TAC `32` `pc + mlkem_poly_frommsg_loop1`
   `pc + mlkem_poly_frommsg_loop1_exit`
   `\i s. read X0 s = r /\
          read X1 s = a /\
          read X8 s = word i /\
          read X9 s = word_sub (word_add r (word(16 * i + 16))) (word 8) /\
          read X10 s = word 1665 /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,32)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP j) MOD 2 + 1) DIV 2))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    CONV_TAC WORD_RULE;

    (*** The loop body, for one byte and eight coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `32`; `n:num`; `i:num`; `s0:armstate`]
                 READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_EXEC (1--52) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES] o
                   CONV_RULE(ONCE_DEPTH_CONV FROMMSG_ADDR_CONV)) THEN
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
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 16 = (16 * i + 16) + 16`] THEN
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
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[BYTE_BIT; ARITH] THEN
    REWRITE_TAC[GSYM(CONV_RULE NUM_REDUCE_CONV
     (SPECL [`n DIV 2 EXP (8 * i)`; `2`; `128`] MOD_MOD))] THEN

    (*** Check all values of the byte ***)

    MP_TAC(SPECL [`n DIV 2 EXP (8 * i)`; `256`] MOD_LT_EQ) THEN
    REWRITE_TAC[ARITH_EQ] THEN
    SPEC_TAC(`(n DIV 2 EXP (8 * i)) MOD 256`,`m:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));

    (*** The return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_EXEC (1--1) THEN
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

let mlkem_native_poly_frommsg_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 32]", "true")],
   "void",
   [("a", "32", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_frommsg_signature
    MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,32]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_frommsg) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,32; r,512] [r,512]))
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
              fst MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_frommsg_loop1`
   `pc + mlkem_poly_frommsg_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = r /\
           read X1 s = a /\
           read X8 s = word i /\
           read X9 s = word_sub (word_add r (word(16 * i + 16))) (word 8)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_EXEC (1--3) THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O3_EXEC (1--52) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES] o
                 CONV_RULE(ONCE_DEPTH_CONV FROMMSG_ADDR_CONV)) THEN
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
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) + 16 = (16 * i + 16) + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV FROMMSG_EVENT_ADDR_CONV) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
