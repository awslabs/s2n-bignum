(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Precomputation of the mulcache for polynomial multiplication. This is     *)
(* the code for mlk_poly_mulcache_compute_c from mlkem-native's portable C   *)
(* implementation compiled by gcc 12 with -O2 as one translation unit (see   *)
(* mlkem_native/README.md). It is the same as mlkem_poly_mulcache_compute    *)
(* of the separate -O2 build up to the allocation of some registers, a NOP   *)
(* before the loop and the order of the factors in one multiplication.       *)
(* Unlike the hand-written kernel, it reads its own table of zetas from      *)
(* the read-only data rather than taking tables as arguments. It is          *)
(* verified in the whole image (see libmlkem.ml), with the proof for the     *)
(* separate -O2 build adapted to the image, whose table of zetas is at pc    *)
(* + rodata_mlk_zetas.                                                       *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_ZETAS_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data (layout "rodata_mlk_zetas");;

(*** The code in the image:

    mlk_poly_mulcache_compute_c:
       +0x0: adrp    x8, <page>
       +0x4: add     x8, x8, #0xd20
       +0x8: add     x5, x8, #0x80
       +0xc: add     x4, x0, #0x2
      +0x10: add     x3, x1, #0x2
      +0x14: add     x8, x8, #0x100
      +0x18: mov     w7, #0xfffff301
      +0x1c: mov     w6, #0xfffff2ff
      +0x20: nop
      +0x24: ldrsh   w0, [x5], #2
      +0x28: add     x3, x3, #0x8
      +0x2c: ldursh  w2, [x3, #-8]
      +0x30: neg     w1, w0
      +0x34: sxth    w1, w1
      +0x38: mul     w2, w2, w0
      +0x3c: mul     w0, w2, w7
      +0x40: sxth    w0, w0
      +0x44: madd    w0, w0, w6, w2
      +0x48: asr     w0, w0, #16
      +0x4c: sturh   w0, [x4, #-2]
      +0x50: ldursh  w0, [x3, #-4]
      +0x54: mul     w1, w1, w0
      +0x58: mul     w0, w1, w7
      +0x5c: sxth    w0, w0
      +0x60: madd    w0, w0, w6, w1
      +0x64: asr     w0, w0, #16
      +0x68: strh    w0, [x4], #4
      +0x6c: cmp     x8, x5
      +0x70: b.ne    <mlk_poly_mulcache_compute_c+0x24>
      +0x74: ret
 ***)

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlk_poly_mulcache_compute_c"];;

(* ------------------------------------------------------------------------- *)
(* Properties of the zetas (see utils/mlkem_native.ml for the table).        *)
(* ------------------------------------------------------------------------- *)

(*** The zetas used for the mulcache are those in the second half ***)

let MLK_ZETAS_MULCACHE = prove
 (`!i. i < 64
       ==> abs(EL (64 + i) mlk_zetas) <= &1664 /\
           (&169 * EL (64 + i) mlk_zetas ==
            &17 pow (2 * bitreverse7 (2 * i) + 1)) (mod &3329) /\
           (&169 * --(EL (64 + i) mlk_zetas) ==
            &17 pow (2 * bitreverse7 (2 * i + 1) + 1)) (mod &3329)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[mlk_zetas] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[BITREVERSE7_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let MLK_ZETAS_MULCACHE_IVAL = prove
 (`!i. i < 64
       ==> ival(iword(EL (64 + i) mlk_zetas):int16) = EL (64 + i) mlk_zetas /\
           abs(ival(iword(EL (64 + i) mlk_zetas):int16)) <= &1664 /\
           (&169 * ival(iword(EL (64 + i) mlk_zetas):int16) ==
            &17 pow (2 * bitreverse7 (2 * i) + 1)) (mod &3329) /\
           (&169 * --ival(iword(EL (64 + i) mlk_zetas):int16) ==
            &17 pow (2 * bitreverse7 (2 * i + 1) + 1)) (mod &3329)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLK_ZETAS_MULCACHE) THEN
  SUBGOAL_THEN
   `ival(iword(EL (64 + i) mlk_zetas):int16) = EL (64 + i) mlk_zetas`
  SUBST1_TAC THENL [MATCH_MP_TAC IVAL_IWORD; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some lemmas, tactics etc.                                                 *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_NEG_SX = prove
 (`!z:int16. word_zx(word_sub (word 0) (word_sx z:int32)):int16 = word_neg z`,
  BITBLAST_TAC);;

let CONG_MONT_ZETA = INTEGER_RULE
 `!n a z p x r:int. (r == a * (x * z)) (mod n) /\ (a * z == p) (mod n)
                    ==> (r == x * p) (mod n)`;;

let MULCACHE_ADDR_NORM_RULES =
  map ARITH_RULE
   [`2 * (64 + i) = 2 * i + 128`; `2 * (4 * i + 1) = 8 * i + 2`;
    `2 * (4 * i + 3) = 8 * i + 6`];;

(*** Instantiate a quantified input fact at a particular index ***)

let MSPEC_TAC (f,idx) =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_forall c &&
       (let b = snd(dest_forall c) in
        is_imp b && is_eq(rand b) && can (find_term ((=) f)) (rhs(rand b)))
    then MP_TAC(SPEC idx th) else failwith "MSPEC_TAC") THEN
  ANTS_TAC THENL
   [W(fun (asl,w) -> MP_TAC(ARITH_RULE (mk_imp(`i < 64`,w)))) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE MULCACHE_ADDR_NORM_RULES)];;

(*** The compiler multiplies by the negated zeta with the factors swapped  ***)
(*** compared to gcc12_O2, so put the negated zeta second as there         ***)

let COMMUTE_NEG_MUL_CONV tm =
  match tm with
    Comb(Comb(Const("word_mul",_),a),b)
      when can (find_term (fun t -> is_const t &&
                                    fst(dest_const t) = "word_neg")) a
      -> ISPECL [a;b] WORD_MUL_SYM
  | _ -> failwith "COMMUTE_NEG_MUL_CONV";;

(*** Prove the result for one output coefficient ***)

let MULCACHE_OUTPUT_TAC =
  UNDISCH_THEN `i < 64` (fun th ->
    ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(MATCH_MP MLK_ZETAS_MULCACHE_IVAL th)) THEN
  ASSUM_LIST(fun ths -> W(fun (asl,w) ->
    let tm = rand(rand(lhand(rator(lhand w)))) in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE ths tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = CONV_RULE(ONCE_DEPTH_CONV INVERSE_MOD_CONV)
               (MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2))))) in
    let cth,bth = CONJ_PAIR th3 in
    let zz = rand(rand(rand(rator(concl cth)))) in
    CONJ_TAC THENL
     [REWRITE_TAC[mulcache; o_THM; INT_CONG_RREM;
                  ARITH_RULE `2 * 2 * i + 1 = 4 * i + 1`;
                  ARITH_RULE `2 * (2 * i + 1) + 1 = 4 * i + 3`] THEN
      MATCH_MP_TAC CONG_MONT_ZETA THEN
      MAP_EVERY EXISTS_TAC [`&169:int`; zz] THEN
      CONJ_TAC THENL
       [FIRST [ACCEPT_TAC cth; MP_TAC cth THEN CONV_TAC INTEGER_RULE];
        ASM_REWRITE_TAC[]];
      MP_TAC bth THEN CONV_TAC(LAND_CONV INT_REDUCE_CONV) THEN
      INT_ARITH_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_CORRECT = prove
 (`!dst src x pc.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    ALL (nonoverlapping (dst,256))
        [(word pc,libmlkem_size); (src,512)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mono_mc /\
           read PC s = word (pc + mlk_poly_mulcache_compute_c) /\
           C_ARGUMENTS [dst; src] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + mlk_poly_mulcache_compute_c_ret) /\
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dst,256)])`,
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The output is disjoint from the table of zetas in the image ***)

  SUBGOAL_THEN `nonoverlapping (dst:int64,256)
                  (word(pc + rodata_mlk_zetas),256)` MP_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN DISCH_TAC THEN

  (*** The loop invariant, with the loop test as a separate step. The ***)
  (*** constant parts of the pointers are kept apart so that address  ***)
  (*** offsets in loads and stores are simplified.                    ***)

  ENSURES_WHILE_UP_TAC `64` `pc + mlk_poly_mulcache_compute_c_loop1`
   `pc + mlk_poly_mulcache_compute_c_loop1_test`
   `\i s. read X5 s = word_add (word_add (word (pc + rodata_mlk_zetas)) (word(2 * i)))
                               (word 128) /\
          read X8 s = word_add (word (pc + rodata_mlk_zetas)) (word 256) /\
          read X3 s = word_add (word_add src (word(8 * i))) (word 2) /\
          read X4 s = word_add (word_add dst (word(4 * i))) (word 2) /\
          read X7 s = word 4294963969 /\ read X6 s = word 4294963967 /\
          (!k. k < 128
               ==> read(memory :> bytes16(word_add (word (pc + rodata_mlk_zetas))
                                                   (word(2 * k)))) s =
                   iword(EL k mlk_zetas)) /\
          (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i) /\
          (!j. j < 2 * i
               ==> let z_j = read(memory :> bytes16
                                (word_add dst (word (2 * j)))) s in
                   (ival z_j == (mulcache (ival o x)) j) (mod &3329) /\
                   abs(ival z_j) <= &3328)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, including the address of the table ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED o
                MATCH_MP MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_ZETAS_IN_IMAGE) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC (2--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
    REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE;

    (*** The loop body, computing two output coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY MSPEC_TAC
     [`mlk_zetas`,`64 + i`; `x:num->int16`,`4 * i + 1`;
      `x:num->int16`,`4 * i + 3`] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC (1--18) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`;
                  ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                  ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE
     `j < 2 * (i + 1) <=> j < 2 * i \/ j = 2 * i \/ j = 2 * i + 1`] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check
       (fun th -> is_forall(concl th) &&
                  can (find_term (fun t -> try fst(dest_const t) = "mulcache"
                                           with _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * 2 * i = 4 * i`;
                ARITH_RULE `2 * (2 * i + 1) = 4 * i + 2`] THEN
    ASM_REWRITE_TAC[] THEN MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[WORD_ADD_0; SXFROM_15_SUBWORD; WORD_ZX_NEG_SX] THEN
    REWRITE_TAC[GSYM SXFROM_15_SUBWORD] THEN
    REWRITE_TAC[GSYM montred_scalar] THEN
    CONV_TAC(DEPTH_CONV COMMUTE_NEG_MUL_CONV) THEN MULCACHE_OUTPUT_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add (word (pc + rodata_mlk_zetas)) (word 256))
                     (word_add (word_add (word (pc + rodata_mlk_zetas)) (word (2 * i)))
                               (word 128)):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
        word_sub x (word_add y z)`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 64 ==> 2 * i + 128 < 18446744073709551616`] THEN
      ASM_ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                can (find_term (fun t -> try fst(dest_const t) = "mulcache"
                                         with _ -> false)) (concl th)))]);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (`!dst src x pc returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    ALL (nonoverlapping (dst,256))
        [(word pc,libmlkem_size); (src,512)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mono_mc /\
           read PC s = word (pc + mlk_poly_mulcache_compute_c) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [dst; src] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(dst,256)])`,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** Unlike mlkem_mulcache_compute, this has just two arguments, and the ***)
(*** table of zetas is a read-only object.                               ***)

let mlkem_native_poly_mulcache_compute_signature =
  ([("x", "int16_t[static 128]", "false");
    ("a", "int16_t[static 256]", "true")],
   "void",
   [("a", "256", 2)],
   [("x", "128", 2)],
   []);;
let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + rodata_mlk_zetas):int64`,`256`]
    ~keep_maychanges:true
    mlkem_native_poly_mulcache_compute_signature
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e dst src pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
                  ALL (nonoverlapping (dst,256))
           [word pc,libmlkem_size; src,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlk_poly_mulcache_compute_c) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events src dst pc returnaddress /\
                        memaccess_inbounds e2
                         [src,512; dst,256; word (pc + rodata_mlk_zetas),256]
                         [dst,256])
               (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8] ,,
                MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
                MAYCHANGE [memory :> bytes(dst,256)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(src:int64) (dst:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil src dst pc returnaddress)
        (APPEND
          (ENUMERATEL 64 (\i. f_ev_loop src dst pc returnaddress i))
          (f_ev_prol src dst pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              SOME_FLAGS; ALL;
              fst MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC] THEN
  REPEAT STRIP_TAC THEN

  (*** The output is disjoint from the table of zetas in the image ***)

  SUBGOAL_THEN `nonoverlapping (dst:int64,256)
                  (word(pc + rodata_mlk_zetas),256)` MP_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN DISCH_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mlk_poly_mulcache_compute_c_loop1`
   `pc + mlk_poly_mulcache_compute_c_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X5 s = word_add (word_add (word (pc + rodata_mlk_zetas)) (word(2 * i)))
                                (word 128) /\
           read X8 s = word_add (word (pc + rodata_mlk_zetas)) (word 256) /\
           read X3 s = word_add (word_add src (word(8 * i))) (word 2) /\
           read X4 s = word_add (word_add dst (word(4 * i))) (word 2)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC (2--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_EXEC (1--20) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add (word (pc + rodata_mlk_zetas)) (word 256))
                   (word_add (word_add (word (pc + rodata_mlk_zetas)) (word (2 * i))) (word 130))
          :int64) = 0) <=>
    i + 1 < 64`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
      word_sub x (word_add y z)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 64 ==> 2 * i + 130 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`;
                ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

