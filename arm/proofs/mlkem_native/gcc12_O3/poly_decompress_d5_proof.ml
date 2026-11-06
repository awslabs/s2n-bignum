(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 5 bits per coefficient. This is the    *)
(* code for mlkem_poly_decompress_d5 from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md),  *)
(* which the compiler has partly vectorized. It is verified in the whole     *)
(* image (see libmlkem.ml).                                                  *)
(*                                                                           *)
(* Unlike at -O2, the code loads no constants from the read-only data: the   *)
(* products by 3329 are scalar MULs. So the safety theorem has no read-only  *)
(* region for them, unlike that of gcc12_O2.                                 *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d5:
       +0x0: mov     x6, x1
       +0x4: mov     x8, x0
       +0x8: add     x9, x1, #0xa0
       +0xc: mov     w7, #0xd01
      +0x10: ldrb    w2, [x6, #1]
      +0x14: add     x6, x6, #0x5
      +0x18: ldurb   w0, [x6, #-5]
      +0x1c: ldurb   w3, [x6, #-2]
      +0x20: ldurb   w12, [x6, #-3]
      +0x24: lsl     w4, w2, #3
      +0x28: orr     w4, w4, w0, lsr #5
      +0x2c: and     w0, w0, #0x1f
      +0x30: lsl     w1, w3, #4
      +0x34: and     w4, w4, #0x1f
      +0x38: orr     w1, w1, w12, lsr #4
      +0x3c: ubfx    x11, x3, #1, #5
      +0x40: and     w1, w1, #0x1f
      +0x44: ldurb   w5, [x6, #-1]
      +0x48: mul     w4, w4, w7
      +0x4c: lsl     w12, w12, #1
      +0x50: mul     w0, w0, w7
      +0x54: add     w4, w4, #0x10
      +0x58: mul     w1, w1, w7
      +0x5c: fmov    s0, w4
      +0x60: mul     w11, w11, w7
      +0x64: lsl     w10, w5, #2
      +0x68: add     w0, w0, #0x10
      +0x6c: ushr    v2.2s, v0.2s, #5
      +0x70: orr     w3, w10, w3, lsr #6
      +0x74: add     w1, w1, #0x10
      +0x78: fmov    s0, w0
      +0x7c: fmov    s1, w1
      +0x80: add     w11, w11, #0x10
      +0x84: fmov    s3, w11
      +0x88: ubfx    x10, x2, #2, #5
      +0x8c: and     w3, w3, #0x1f
      +0x90: ushr    v0.2s, v0.2s, #5
      +0x94: ushr    v3.2s, v3.2s, #5
      +0x98: ushr    v1.2s, v1.2s, #5
      +0x9c: mul     w4, w10, w7
      +0xa0: orr     w0, w12, w2, lsr #7
      +0xa4: mul     w1, w3, w7
      +0xa8: and     w0, w0, #0x1f
      +0xac: mov     v0.s[1], v2.s[0]
      +0xb0: add     w2, w4, #0x10
      +0xb4: mov     v1.s[1], v3.s[0]
      +0xb8: add     w1, w1, #0x10
      +0xbc: fmov    s2, w2
      +0xc0: fmov    s3, w1
      +0xc4: lsr     w5, w5, #3
      +0xc8: mul     w0, w0, w7
      +0xcc: ushr    v2.2s, v2.2s, #5
      +0xd0: ushr    v3.2s, v3.2s, #5
      +0xd4: add     w0, w0, #0x10
      +0xd8: mul     w1, w5, w7
      +0xdc: mov     v0.s[2], v2.s[0]
      +0xe0: add     w1, w1, #0x10
      +0xe4: mov     v1.s[2], v3.s[0]
      +0xe8: fmov    s2, w0
      +0xec: fmov    s3, w1
      +0xf0: ushr    v2.2s, v2.2s, #5
      +0xf4: ushr    v3.2s, v3.2s, #5
      +0xf8: mov     v0.s[3], v2.s[0]
      +0xfc: mov     v1.s[3], v3.s[0]
     +0x100: uzp1    v0.8h, v0.8h, v1.8h
     +0x104: str     q0, [x8], #16
     +0x108: cmp     x9, x6
     +0x10c: b.ne    <mlkem_poly_decompress_d5+0x10>
     +0x110: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_decompress_d5"];;

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
(* The 5-bit field k of the 40 bits as part of the number for the input.     *)
(* ------------------------------------------------------------------------- *)

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


(* ------------------------------------------------------------------------- *)
(* The stored coefficients. Each 16-bit part of the 128-bit store is the    *)
(* low half of (y * 3329 + 16) >> 5 for a 32-bit value y made from the input *)
(* bytes, after SIMD_SIMPLIFY_CONV (LANE_RULE would find it by bit-blasting  *)
(* if it were part of a larger term). The lane is shown to be                *)
(* (3329 * f + 16) DIV 32 for the 5-bit field f of the 40 bits by            *)
(* bit-blasting y into the zero extension of f and then by arithmetic on the *)
(* small values involved (DECOMPRESS_LANE_TAC), whatever the nesting of the  *)
(* zero extensions from the moves between registers.                         *)
(* ------------------------------------------------------------------------- *)

let LANE_RULE pats th =
  let v = rand(concl th) in
  if not(exists (fun p -> can (find_term (can (term_match [] p))) v) pats)
  then CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
        th else
  let ls = setify(find_terms (fun t -> exists (fun p -> can (term_match [] p) t) pats) v) in
  let gs = map (fun t -> genvar(type_of t)) ls in
  let v' = subst (zip gs ls) v in
  let bth = tryfind (fun g -> BITBLAST_RULE(mk_eq(v',g))) gs in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th (INST (zip ls gs) bth));;

let DECOMPRESS_LANE_TAC fieldth fieldk nk d c q =
  let fty = mk_type("word",[mk_finty(Num.num_of_int d)]) in
  let fv = mk_var("f",fty) in
  let valf = mk_comb(inst [mk_finty(Num.num_of_int d),`:N`]
                          `val:N word->num`,fv) in
  let rhs = subst [mk_small_numeral c,`c:num`; mk_small_numeral q,`q:num`;
                   valf,`v:num`]
                  `word((3329 * v + c) DIV q):int16` in
  W(fun (asl,w) ->
     let lk = lhs w in
     let tk = rand(find_term (fun t -> match t with
                  Comb(Const("val",_),_) -> true | _ -> false) lk) in
     let fth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
      (MP (SPEC (mk_small_numeral fieldk) fieldth)
          (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                         (mk_small_numeral fieldk) (mk_small_numeral nk))))) in
     let st = rand(lhand(concl fth)) in
     let wt = rand(rator st) in
     let st' = subst [mk_var("w",type_of wt),wt] st in
     let zx t = mk_comb(inst [mk_finty(Num.num_of_int d),`:A`;
                              hd(snd(dest_type(type_of tk))),`:B`]
                             `word_zx:A word->B word`, t) in
     let lth = GEN fv (prove(mk_eq(subst [zx fv,tk] lk,rhs),
       REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_USHR;
                   VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
       CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
       REWRITE_TAC[DIV_1] THEN
       MP_TAC(ISPEC fv VAL_BOUND) THEN
       CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
       SPEC_TAC(valf,`v:num`) THEN
       REPEAT STRIP_TAC THEN REPEAT MOD_LT_ASM_TAC THEN
       AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC)) in
     SUBGOAL_THEN (mk_eq(tk,zx st')) SUBST1_TAC THENL
       [BITBLAST_TAC; ALL_TAC] THEN
     REWRITE_TAC[lth] THEN EXPAND_TAC "w" THEN REWRITE_TAC[fth] THEN
     REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV);;

let d5_lanepats =
 [`word_subword (word_ushr (x:int32) 5) (0,16):int16`;
  `word_subword (x:int32) (5,16):int16`];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 5 in common/fips203.ml, the    *)
(* result for a 5-bit field y is the integer closest to 3329 * y / 32,       *)
(* rounding up on ties, i.e. (3329 * y + 16) DIV 32.                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,160)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_poly_decompress_d5) /\
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

  ENSURES_WHILE_UP_TAC `32` `pc + mlkem_poly_decompress_d5_loop1`
   `pc + mlkem_poly_decompress_d5_loop1_test`
   `\i s. read X6 s = word_add a (word(5 * i)) /\
          read X8 s = word_add r (word(16 * i)) /\
          read X9 s = word_add a (word 160) /\
          read X7 s = word 3329 /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,160)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (5 * j)) MOD 2 EXP 5 + 16)
                        DIV 32))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC (1--4) THEN
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
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--62) THEN
    FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
             concl)) THEN
    DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o LANE_RULE d5_lanepats o
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
    REPEAT CONJ_TAC THENL
     (map (fun k -> DECOMPRESS_LANE_TAC
                     (SPECL [`n:num`; `i:num`] D5D_FIELD) k 8 5 16 32)
          (0--7));

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC (2--3) THEN
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
    ~keep_maychanges:true
    mlkem_native_poly_decompress_d5_signature
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,160]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_decompress_d5) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,160; r,512] [r,512]))
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
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_decompress_d5_loop1`
   `pc + mlkem_poly_decompress_d5_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X6 s = word_add a (word(5 * i)) /\
           read X8 s = word_add r (word(16 * i)) /\
           read X9 s = word_add a (word 160)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC (1--4) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_GCC12_O3_EXEC (1--64) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add a (word 160))
                   (word_add (word_add a (word (5 * i))) (word 5)):int64) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add (word_add a y) z) (word_add a x):int64 =
      word_sub (word_add y z) x`;
     WORD_RULE
     `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
      word_sub x (word_add y z)`] THEN
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
