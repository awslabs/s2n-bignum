(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Computation of the multiplication cache of a polynomial.                  *)
(* This is the code for mlkem_poly_mulcache_compute from mlkem-native's      *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md).                                                  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;

(**** print_literal_relocs_from_elf
        "x86/mlkem_native/mlkem_native_poly_mulcache_compute_gcc12_O2.o";;
 ****)

let mlkem_native_poly_mulcache_compute_gcc12_O2_mc,
    mlkem_native_poly_mulcache_compute_gcc12_O2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "WHOLE_READONLY" | "mlk_zetas" -> "mlk_zetas_data"
      | s -> failwith ("unknown symbol: " ^ s))
    "mlkem_native_poly_mulcache_compute_gcc12_O2_mc"
    "x86/mlkem_native/mlkem_native_poly_mulcache_compute_gcc12_O2.o"
(fun b ADDR -> [b[
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x8d; 0x05]; ADDR ("mlk_zetas_data",(124)); b[
                           (* LEA (% r8) (Riprel (word_sx (iword
                                  (&mlk_zetas_data - (&pc + -- &119))))) *)
  0x0f; 0x1f; 0x80; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x41; 0x0f; 0xbf; 0x04; 0x08;
                           (* MOVSX (% eax) (Memop Word (%%% (r8,0,rcx))) *)
  0x44; 0x0f; 0xbf; 0x4c; 0x8e; 0x02;
                           (* MOVSX (% r9d) (Memop Word (%%%% (rsi,2,rcx,&2)))
                                    *)
  0x44; 0x0f; 0xaf; 0xc8;  (* IMUL (% r9d) (% eax) *)
  0x89; 0xc2;              (* MOV (% edx) (% eax) *)
  0xf7; 0xda;              (* NEG (% edx) *)
  0x0f; 0xbf; 0xd2;        (* MOVSX (% edx) (% dx) *)
  0x66; 0x41; 0x69; 0xc1; 0x01; 0xf3;
                           (* IMUL3 (% ax) (% r9w,Imm16 (word 62209)) *)
  0x98;                    (* MOVSX (% eax) (% ax) *)
  0x69; 0xc0; 0xff; 0xf2; 0xff; 0xff;
                           (* IMUL3 (% eax) (% eax,Imm32 (word 4294963967)) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0xc1; 0xf8; 0x10;        (* SAR (% eax) (Imm8 (word 16)) *)
  0x66; 0x89; 0x04; 0x4f;  (* MOV (Memop Word (%%% (rdi,1,rcx))) (% ax) *)
  0x0f; 0xbf; 0x44; 0x8e; 0x06;
                           (* MOVSX (% eax) (Memop Word (%%%% (rsi,2,rcx,&6)))
                                    *)
  0x0f; 0xaf; 0xd0;        (* IMUL (% edx) (% eax) *)
  0x66; 0x69; 0xc2; 0x01; 0xf3;
                           (* IMUL3 (% ax) (% dx,Imm16 (word 62209)) *)
  0x98;                    (* MOVSX (% eax) (% ax) *)
  0x69; 0xc0; 0xff; 0xf2; 0xff; 0xff;
                           (* IMUL3 (% eax) (% eax,Imm32 (word 4294963967)) *)
  0x01; 0xd0;              (* ADD (% eax) (% edx) *)
  0xc1; 0xf8; 0x10;        (* SAR (% eax) (Imm8 (word 16)) *)
  0x66; 0x89; 0x44; 0x4f; 0x02;
                           (* MOV (Memop Word (%%%% (rdi,1,rcx,&2))) (% ax) *)
  0x48; 0x83; 0xc1; 0x02;  (* ADD (% rcx) (Imm8 (word 2)) *)
  0x48; 0x81; 0xf9; 0x80; 0x00; 0x00; 0x00;
                           (* CMP (% rcx) (Imm32 (word 128)) *)
  0x75; 0xa8;              (* JNE (Imm8 (word 168)) *)
  0xc3                     (* RET *)
]]);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_poly_mulcache_compute_gcc12_O2_mc;;

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
 (`!z:int16. word_zx(word_neg (word_sx z:int32)):int16 = word_neg z`,
  BITBLAST_TAC);;

let CONG_MONT_ZETA = INTEGER_RULE
 `!n a z p x r:int. (r == a * (x * z)) (mod n) /\ (a * z == p) (mod n)
                    ==> (r == x * p) (mod n)`;;

let CONG_MONT_ZETA_ALT = INTEGER_RULE
 `!n a z p x r:int. (r == a * (z * x)) (mod n) /\ (a * z == p) (mod n)
                    ==> (r == x * p) (mod n)`;;

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
    let prod = rand(rand(rator(concl cth))) in
    let ZETA_TAC lemma zz =
      MATCH_MP_TAC lemma THEN MAP_EVERY EXISTS_TAC [`&169:int`; zz] THEN
      CONJ_TAC THENL [ACCEPT_TAC cth; ASM_REWRITE_TAC[]] in
    CONJ_TAC THENL
     [REWRITE_TAC[mulcache; o_THM; INT_CONG_RREM;
                  ARITH_RULE `2 * 2 * i + 1 = 4 * i + 1`;
                  ARITH_RULE `2 * (2 * i + 1) + 1 = 4 * i + 3`] THEN
      (ZETA_TAC CONG_MONT_ZETA (rand prod) ORELSE
       ZETA_TAC CONG_MONT_ZETA_ALT (lhand prod));
      MP_TAC bth THEN CONV_TAC(LAND_CONV INT_REDUCE_CONV) THEN
      INT_ARITH_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT = prove
 (`!dst src zetas x pc.
    riprel32_within_bounds (zetas + 128) (pc + 9) /\
    ALL (nonoverlapping (dst,256))
        [(word pc,0x69); (src,512); (word zetas,256)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_mulcache_compute_gcc12_O2_mc pc zetas) /\
           read RIP s = word pc /\
           C_ARGUMENTS [dst; src] s /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read RIP s = word(pc + 0x68) /\
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst,256)])`,
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `zetas:num`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `64` `pc + 0x10` `pc + 0x5f`
   `\i s. read RCX s = word(2 * i) /\
          read R8 s = word(zetas + 128) /\
          read RSI s = src /\ read RDI s = dst /\
          (!k. k < 128
               ==> read(memory :> bytes16(word_add (word zetas)
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
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--3) THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(SPECL [`pc:num`; `9`; `119`; `zetas:num`]
      RIP_REL_ADDR_FOLD))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, computing two output coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    VAL_INT64_TAC `2 * i` THEN
    READ_INSTANCE_TAC
     `read (memory :> bytes16
             (word_add (word (zetas + 128)) (word (1 * 2 * i)))) s0 =
      iword(EL (64 + i) mlk_zetas)` THEN
    READ_INSTANCE_TAC
     `read (memory :> bytes16 (word_add src (word (4 * 2 * i + 2)))) s0 =
      x(4 * i + 1)` THEN
    READ_INSTANCE_TAC
     `read (memory :> bytes16 (word_add src (word (4 * 2 * i + 6)))) s0 =
      x(4 * i + 3)` THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
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
    REWRITE_TAC[ARITH_RULE `2 * (2 * i + 1) = 2 * 2 * i + 2`] THEN
    ASM_REWRITE_TAC[] THEN MLKEM_NATIVE_WORD_SIMP_TAC THEN
    REWRITE_TAC[WORD_ZX_NEG_SX] THEN
    REWRITE_TAC[GSYM montred_x86; MONTRED_X86_SCALAR] THEN
    MULCACHE_OUTPUT_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word(2 * i)) (word 128):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 64 ==> 2 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 64` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                can (find_term (fun t -> try fst(dest_const t) = "mulcache"
                                         with _ -> false)) (concl th)))]);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!dst src zetas x pc stackpointer returnaddress.
    riprel32_within_bounds (zetas + 128) (pc + 9) /\
    ALL (nonoverlapping (dst,256))
        [(word pc,0x69); (src,512); (word zetas,256); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_mulcache_compute_gcc12_O2_mc pc zetas) /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [dst; src] s /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst,256)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

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
    ~readonly_objects:[`word zetas:int64`,`256`]
    ~keep_maychanges:true
    mlkem_native_poly_mulcache_compute_signature
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SAFE = time prove
 (`exists f_events.
       forall e dst src zetas pc.
           riprel32_within_bounds (zetas + 128) (pc + 9) /\
           ALL (nonoverlapping (dst,256))
           [word pc,0x69; src,512; word zetas,256]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                     (mlkem_native_poly_mulcache_compute_gcc12_O2_mc
                        pc zetas) /\
                    read RIP s = word pc /\
                    bytes_loaded s (word zetas) mlk_zetas_data /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0x68) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events src dst zetas pc /\
                         memaccess_inbounds e2
                          [src,512; dst,256; word zetas,256]
                          [dst,256]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst,256)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(src:int64) (dst:int64) (zetas:num) (pc:num).
      APPEND
        (f_ev_epil src dst zetas pc)
        (APPEND
          (ENUMERATEL 64 (\i. f_ev_loop src dst zetas pc i))
          (f_ev_prol src dst zetas pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + 0x10` `pc + 0x68`
    `\i s. read RCX s = word(2 * i) /\
           read R8 s = word(zetas + 128) /\
           read RSI s = src /\ read RDI s = dst` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--3) THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(SPECL [`pc:num`; `9`; `119`; `zetas:num`]
      RIP_REL_ADDR_FOLD))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN VAL_INT64_TAC `2 * i` THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--23) THEN
  SUBGOAL_THEN
   `~(val(word_add (word(2 * i)) (word 18446744073709551490):int64) = 0) <=>
    i + 1 < 64`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 64 ==> 2 * i < 18446744073709551616`] THEN
    ASM_CASES_TAC `i = 63` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o
      lhand o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `i < 64` THEN UNDISCH_TAC `~(i = 63)` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `i < 64` THEN UNDISCH_TAC `~(i = 63)` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e dst src zetas pc stackpointer returnaddress.
           riprel32_within_bounds (zetas + 128) (pc + 9) /\
           ALL (nonoverlapping (dst,256))
           [word pc,0x69; src,512; word zetas,256; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                     (mlkem_native_poly_mulcache_compute_gcc12_O2_mc
                        pc zetas) /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    bytes_loaded s (word zetas) mlk_zetas_data /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events src dst zetas pc stackpointer
                                       returnaddress /\
                         memaccess_inbounds e2
                          [src,512; dst,256; word zetas,256; stackpointer,8]
                          [dst,256]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst,256)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
