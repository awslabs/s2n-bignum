(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Region lemmas for the loops that clang 23 -O3 inlines into the ML-DSA-65  *)
(* and ML-DSA-87 versions of verify_internal and signature_internal, in the  *)
(* form of inline_sign.ml (from the head of the code to its exit, the frame *)
(* at fixed offsets from rsp0, the value of RSP).                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_verify.ml";;

(* ------------------------------------------------------------------------- *)
(* mld_polyz_unpack_c with gamma1 = 2^19 (ML-DSA-65 and -87): 5 bytes of the *)
(* input a become 2 coefficients of 32 bits, 128 iterations of 8 bytes of    *)
(* output at rsp0 + ob. The output is addressed as [rsp + rcx * 8 + k], RCX *)
(* being the index rcx0 + i (so ob = k + 8 rcx0), and RAX is the input       *)
(* pointer a + 4 + 5 i, used at negative displacements. The scratch        *)
(* registers are EDX, ESI and R8D or EDI, depending on the instance.        *)
(* ------------------------------------------------------------------------- *)

let UNPACKZ19_STMT fn loop exit k rcx0 sc =
  let ob = k + 8 * rcx0 in
  parse_term(Printf.sprintf
  "exists f_events.
  forall e a rsp0 pc (b:num->byte).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(a,640); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\
              read RAX s = word_add a (word 4) /\\ read RCX s = word %d /\\
              (!j. j < 640 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\
              read RAX s = word_add a (word 644) /\\ read RCX s = word %d /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s =
                               mld_polyz_unpack_19 b i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a rsp0 pc /\\
                 memaccess_inbounds e2 [a,640; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; %s] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob image_mc fn loop rcx0 fn exit (rcx0+128) ob ob ob sc ob);;

(* The two coefficients of the 5 bytes y0..y4 as the code computes them *)
let UNPACKZ19_LANES = prove
 (`!(b:num->byte) i.
     mld_polyz_unpack_19 b (2 * i) =
     word_sub (word 524288)
      (word_or (word_shl (word_and (word_zx (b(5 * i + 2))) (word 15)) 16)
               (word_zx (word_join (b(5 * i + 1)) (b(5 * i)):int16))) /\
     mld_polyz_unpack_19 b (2 * i + 1) =
     word_sub (word 524288)
      (word_or (word_shl (word_zx (b(5 * i + 4))) 12)
               (word_or (word_shl (word_zx (b(5 * i + 3))) 4)
                        (word_ushr (word_zx (b(5 * i + 2))) 4)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_polyz_unpack_19] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REWRITE_RULE[ADD_CLAUSES]
               (MP (SPECL [`2`; `i:num`; `0`] DIVMOD_CHUNK) (ARITH_RULE `0 < 2`));
              MP (SPECL [`2`; `i:num`; `1`] DIVMOD_CHUNK) (ARITH_RULE `1 < 2`)] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
  CONJ_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_BLAST);;

(* The end of the body: the loop test, the pointers and the two new
   coefficients, at rsp0 + ob + 8 i and + 4, against the lane lemma by
   bit-blasting with the input bytes as variables. *)
(* The loop test, cmp rcx, rcx0 + 128 after inc rcx, as the simulation
   leaves it: val (word_add (word (rcx0 + i)) (word K)) = 0, K = 2^64 -
   (rcx0 + 127), for i < 128, as a comparison of i *)
let UNPACKZ19_TEST_LEMMA rcx0 =
  let k = Num.sub_num (Num.power_num (Num.num_of_int 2) (Num.num_of_int 64))
                      (Num.num_of_int (rcx0 + 127)) in
  let tm = subst [mk_small_numeral rcx0,`c:num`; mk_numeral k,`k:num`]
   `!i. i < 128
        ==> (val(word_add (word (c + i)) (word k):int64) = 0 <=> ~(i + 1 < 128))` in
  prove(tm, CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
            CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let UNPACKZ19_FINAL_TAC rcx0 ob =
  let lth = UNPACKZ19_TEST_LEMMA rcx0 in
  let obt = mk_small_numeral ob in
  let arith1 = ARITH_RULE(subst [obt,`ob:num`] `ob + 4 * (2 * i + 0) = ob + 8 * i`)
  and arith2 = ARITH_RULE(subst [obt,`ob:num`]
                 `ob + 4 * (2 * i + 1) = ob + (8 * i + 4)`) in
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` lth) (ASSUME `i < 128`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  ADDR_MUL1_TAC ob THEN ADDR_NORMALIZE_TAC THEN ADDR_MUL1_TAC ob THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT_N 2] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[arith1; arith2; ADD_CLAUSES] THEN
      REWRITE_TAC[REWRITE_RULE[ADD_CLAUSES] UNPACKZ19_LANES; UNPACKZ19_LANES] THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN APP_BLAST_TAC `b:num->byte` THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
let UNPACKZ19_TAC exec fn loop exit k rcx0 =
  let ob = k + 8 * rcx0 in
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil a rsp0 pc)
       (APPEND (ENUMERATEL 128 (\i. f_ev_loop a rsp0 pc i)) (f_ev_prol a rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `rsp0:int64`; `pc:num`; `b:num->byte`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word_add (word_add a (word(5 * i))) (word 4) /\\
          read RCX s = word(%d + i) /\\
          (!j. j < 640
               ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
          (!j. j < 2 * i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s =
                   mld_polyz_unpack_19 b j)" rcx0 ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `b:num->byte` 5 THEN
    INPUT_ALT_ADDR_TAC `a:int64` THEN
    VAL_INT64_TAC (parse_term(Printf.sprintf "%d + i" rcx0)) THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 1 `read(memory :> bytes16(word_add a (word(5 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X86_STEPS_TAC exec (1--23) THEN
    UNPACKZ19_FINAL_TAC rcx0 ob;
    FULL_EXIT0_TAC];;

(* fn: the function; loop, exit: the labels of the loop; k: the displacement
   of the stores; rcx0: the index at the head (128 m for polynomial m); sc:
   the scratch register besides EDX and ESI (R8 or RDI; the caller keeps the
   address of the signature in the other). *)
let PROVE_UNPACKZ19 fn loop exit k rcx0 sc =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))] in
  prove(UNPACKZ19_STMT fn loop exit k rcx0 sc, UNPACKZ19_TAC exec fn loop exit k rcx0);;

(* ------------------------------------------------------------------------- *)
(* mld_poly_use_hint (gamma2 = (q - 1) / 32) as clang -O3 has inlined it    *)
(* into the ML-DSA-65/87 functions: one coefficient per iteration, in place, *)
(* a[i] := use_hint(a[i], h[i]), with a at rsp0 + ob (4 * RAX + ob) and h at *)
(* rsp0 + hb. The loop head is the first load (head, join12 in              *)
(* mldsa65_verify_internal), entered with RAX = 0; the high part is in ESI  *)
(* (masked) and ECX (unmasked), the low part a0 in EDX, then the hint test; *)
(* a nonzero hint selects the low part with q subtracted (ESI) and          *)
(* increments or decrements ECX by its sign, masked to 4 bits at join10.    *)
(* The loop is left at the offset exit of the function, after the test of   *)
(* RAX at the store.                                                         *)
(* ------------------------------------------------------------------------- *)

let USEHINT32_STMT fn head exitoff ob hb =
  parse_term(Printf.sprintf
  "exists f_events.
  forall e rsp0 pc (x:num->int32) (y:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rsp0 (word %d),1024))
        [(word_add rsp0 (word %d),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) %s /\\
              read RIP s = word (pc + %s_%s) /\\
              read RSP s = rsp0 /\\ read RAX s = word 0 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = x i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + %d) /\\
              read RSP s = rsp0 /\\ read RAX s = word 256 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = mld_poly_use_hint_32 x y i) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (%d + 4*i)))) s = y i) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc x y /\\
                 memaccess_inbounds e2 [word_add rsp0 (word %d),1024; word_add rsp0 (word %d),1024]
                                       [word_add rsp0 (word %d),1024]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add rsp0 (word %d),1024)])"
  ob hb image_mc fn head ob hb (layout fn + exitoff) ob hb ob hb ob ob);;

(*** a0 = a + a1 * (-2 * gamma2), as IMUL with 0xfff80200 and ADD ***)

let DECOMPOSE_LO_32_CLANG = prove
 (`!a:int32. mld_decompose_lo_32 a =
     let a0 = word_add a (word_mul (mld_decompose_hi_32 a)
                                   (word 4294443520)) in
     mld_ct_sel (word_sub a0 (word 8380417)) a0
                (mld_ct_cmask_neg (word_sub (word 4190208) a0))`,
  SUBGOAL_THEN
   `!a h:int32. word_sub a (word_mul (word_mul h (word 2)) (word 261888)) =
                word_add a (word_mul h (word 4294443520))`
   (fun th -> REWRITE_TAC[mld_decompose_lo_32; th]) THEN
  REWRITE_TAC[GSYM(WORD_REDUCE_CONV `word_neg(word 523776):int32`)] THEN
  CONV_TAC WORD_RULE);;

let USEHINT32_TAC exec fn head exitoff ob hb =
  let path_end addr =
    SCALAR_LANE2_TAC addr `(x:num->int32) i` `(y:num->int32) i` `mld_use_hint_32`
      [mld_use_hint_32; DECOMPOSE_HI_32_ALT; DECOMPOSE_LO_32_CLANG; mld_ct_sel] THEN
    ADDR_LINEAR_BASES_TAC [hb; ob] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    PATH_DISCHARGE_TAC in
  let addr = parse_term(Printf.sprintf "word_add (rsp0:int64) (word (4 * i + %d))" ob) in
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num) (x:num->int32) (y:num->int32).
      APPEND (f_ev_epil rsp0 pc x y)
       (APPEND (ENUMERATEL 256
          (\i. if y i = word 0 then f_ev_zero rsp0 pc x y i
               else if &0 < ival(mld_decompose_lo_32 (x i)) then f_ev_pos rsp0 pc x y i
               else f_ev_neg rsp0 pc x y i))
          (f_ev_prol rsp0 pc x y))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`; `x:num->int32`; `y:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec; mld_poly_use_hint_32] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` (parse_term(Printf.sprintf "pc + %s_%s" fn head))
   (parse_term(Printf.sprintf "pc + %d" (layout fn + exitoff)))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\ read RAX s = word i /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = y j) /\\
          (!j. i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. j < i
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = mld_use_hint_32 (x j) (y j))" hb ob ob)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    VAL_INT64_TAC `i:num` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) && free_in `x:num->int32` (concl th) &&
        not(free_in `mld_use_hint_32` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < 256`) o SPEC `i:num` o
      check (fun th -> is_forall(concl th) && free_in `y:num->int32` (concl th) &&
        not(free_in `x:num->int32` (concl th)))) THEN DISCH_TAC THEN
    ASSUME_TAC(REWRITE_RULE[ARITH_RULE (parse_term(Printf.sprintf "%d + 4 * i = 4 * i + %d" ob ob))]
      (ASSUME (parse_term(Printf.sprintf "read(memory :> bytes32(word_add rsp0 (word(%d + 4 * i)))) s0 = (x:num->int32) i" ob)))) THEN
    ASSUME_TAC(REWRITE_RULE[ARITH_RULE (parse_term(Printf.sprintf "%d + 4 * i = 4 * i + %d" hb hb))]
      (ASSUME (parse_term(Printf.sprintf "read(memory :> bytes32(word_add rsp0 (word(%d + 4 * i)))) s0 = (y:num->int32) i" hb)))) THEN
    X86_STEPS_TAC exec (1--10) THEN
    REG_LANE_TAC `RSI` `(x:num->int32) i` `mld_decompose_hi_32` [DECOMPOSE_HI_32_ALT] THEN
    X86_STEPS_TAC exec (11--19) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0]) THEN BRANCH_CASES_TAC THENL
     [X86_STEPS_TAC exec (20--23) THEN path_end addr;
      X86_STEPS_TAC exec (20--23) THEN
      REG32_LANE_TAC `RSI` `(x:num->int32) i` `mld_decompose_lo_32`
        [DECOMPOSE_LO_32_CLANG; DECOMPOSE_HI_32_ALT; mld_ct_sel] THEN
      X86_STEPS_TAC exec (24--24) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[USE_HINT_GT_COND]) THEN BRANCH_CASES_TAC THENL
       [X86_STEPS_TAC exec (25--31) THEN path_end addr;
        X86_STEPS_TAC exec (25--32) THEN path_end addr]];
    FULL_EXIT0_TAC];;

(* fn: the function; head: the label of the first load of the loop; exitoff:
   the offset in the function of the exit; join9: the first label of the
   code of the loop (the increment of the high part); ob, hb: the offsets
   of the coefficients and of the hints. *)
let PROVE_USEHINT32 fn head exitoff ob hb join9 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^join9), layout fn + exitoff)] in
  prove(USEHINT32_STMT fn head exitoff ob hb, USEHINT32_TAC exec fn head exitoff ob hb);;

(* ------------------------------------------------------------------------- *)
(* tr = SHAKE256(pk) as in TR44 (inline_verify.ml), for a key of len bytes   *)
(* (1952 for ML-DSA-65), the state at a = rsp0 + ao and its address in the  *)
(* register sr: the state zeroed, nb = len DIV 136 full blocks XORed in and  *)
(* permuted, then the last len MOD 136 bytes, the padding and the last       *)
(* permutation. The frame is stated from fb = rsp0 - 296 as for 44. The     *)
(* block tactics are those of TR44 with the offset of the state and the      *)
(* length of the key as parameters.                                          *)
(* ------------------------------------------------------------------------- *)

let TRG_HI_ZERO = prove
 (`!L PK k p n. PK < 2 EXP L /\ L <= 1088 * k + p
        ==> (word_subword (word((PK DIV 2 EXP (1088 * k)) MOD 2 EXP 1088):1600 word)
                          (p,n):N word) = word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(MESON[MOD_0] `!x n. x = 0 ==> x MOD n = 0`) THEN
  SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  TRANS_TAC LET_TRANS `PK DIV 2 EXP (1088 * k)` THEN CONJ_TAC THENL
   [MESON_TAC[MOD_LE; LE_TRANS];
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    TRANS_TAC LTE_TRANS `2 EXP L` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC]);;

(*** The facts for the loads of block k of the key at pk (len bytes) ***)

let TRG_PK_TAC (len:int) (k:int) (chunks:int list) (lanes:int list) =
  let wb = tr_wb k in
  let pat = subst [mk_small_numeral len,`n:num`]
              `read (memory :> bytes(pk,n)) (s:x86state)` in
  let one bits off pos =
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && can (term_match [] pat) (lhs c)
      then
        let s = rand(lhs c) in
        let lem = if bits = 128 then TR_CHUNK128_OF_NUM else TR_CHUNK64_OF_NUM in
        let th1 = TR_NORM_RULE(tr_mp_conj
                    (SPECL [`pk:int64`; mk_small_numeral len; `PK:num`; mk_small_numeral off; s] lem) th) in
        let ty = if bits = 128 then `:128` else `:64` in
        let th2 = TR_NORM_RULE(tr_mp_num (INST_TYPE [ty,`:N`]
                    (SPECL [`PK:num`; mk_small_numeral k; mk_small_numeral pos; mk_small_numeral bits]
                     TR_BLK_SUB))) in
        ASSUME_TAC(TRANS th1 (SYM th2))
      else NO_TAC) in
  ignore wb;
  MAP_EVERY (fun j -> one 128 (136 * k + 16 * j) (128 * j)) chunks THEN
  MAP_EVERY (fun n -> one 64 (136 * k + 8 * n) (64 * n)) lanes;;

(*** The antecedents of the merge lemmas, with the bound of the key ***)

let TRG_ANTE_TAC (len:int) =
  let hz = ISPEC (mk_small_numeral (8 * len)) TRG_HI_ZERO in
  REPEAT CONJ_TAC THEN
  CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(TR_NORM_CONV THENC ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REPEAT CONJ_TAC THEN
  FIRST [ASM_REWRITE_TAC[WORD_SUBWORD_0; WORD_XOR_0; VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI] THEN NO_TAC;
         MATCH_MP_TAC TR_WB_HI THEN CONV_TAC NUM_REDUCE_CONV;
         MATCH_MP_TAC hz THEN
         ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];;

(*** One full block k, as TR_BLOCK_TAC, the state at fb + fo ***)

let TRG_BLOCK_TAC execth fo len k0n k n0 =
  let a = tr_fb_add fo in
  let nsteps = if k = 0 then k0n else 28 in
  let ncall = n0 + nsteps + 1 in
  let sn = mk_var("s"^string_of_int(n0 + nsteps),`:x86state`) in
  let sv = if k = 0 then tr_st 0 else mk_var("st"^string_of_int k,`:1600 word`)
  and wv = mk_var("wb"^string_of_int k,`:1600 word`) in
  TR_STATE_CHUNKS_TAC a (0--7) (16--24) THEN
  TRG_PK_TAC len k (0--7) [16] THEN
  (if k = 0 then ALL_TAC else TR_NAME_TAC (tr_st k) ("st"^string_of_int k)) THEN
  TR_NAME_TAC (tr_wb k) ("wb"^string_of_int k) THEN
  X86_STEPS_TAC execth ((n0+1)--(n0+nsteps)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI]) THEN
  MP_TAC(SPECL [a; sv; wv; sn] TR_BLK_MERGE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL
     [ALL_TAC; TR_UNNAME_GOAL_TAC ("wb"^string_of_int k)]]] THEN
    TRG_ANTE_TAC len;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; mk_comb(mk_comb(`word_xor:1600 word->1600 word->1600 word`,sv),wv);
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pk:int64`; `pc:num`] ncall THEN
  (if k = 0 then ALL_TAC else TR_UNNAME_TAC ("st"^string_of_int k)) THEN
  TR_UNNAME_TAC ("wb"^string_of_int k) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TR_BLOCKS_STEP k]) THEN
  YMM_GHOST_TAC (mk_var("s"^string_of_int ncall,`:x86state`))
   ["YMM0","y0_"^string_of_int k; "YMM1","y1_"^string_of_int k];;

(*** The state after the last 48 bytes W (three 128-bit chunks) and the ***)
(*** padding bytes                                                       ***)

let TR_FIN48_MERGE = prove
 (`!(a:int64) (S:1600 word) (W:1600 word) (s:x86state).
  (!j. j < 3
       ==> read (memory :> bytes128 (word_add a (word (16 * j)))) s =
           word_xor (word_subword W (128 * j,128)) (word_subword S (128 * j,128))) /\
  read (memory :> bytes8 (word_add a (word 48))) s =
  word_xor (word_subword S (384,8)) (word 31) /\
  (!m. m < 7 ==> read (memory :> bytes8 (word_add a (word (49 + m)))) s =
                 word_subword S (392 + 8 * m,8)) /\
  (!n. n < 9 ==> read (memory :> bytes64 (word_add a (word (56 + 8 * n)))) s =
                 word_subword S (448 + 64 * n,64)) /\
  (!m. m < 7 ==> read (memory :> bytes8 (word_add a (word (128 + m)))) s =
                 word_subword S (1024 + 8 * m,8)) /\
  read (memory :> bytes8 (word_add a (word 135))) s =
  word_xor (word_subword S (1080,8)) (word 128) /\
  (!n. n < 8 ==> read (memory :> bytes64 (word_add a (word (136 + 8 * n)))) s =
                 word_subword S (1088 + 64 * n,64)) /\
  (!n. n < 19 ==> word_subword W (384 + 64 * n,64) = (word 0:int64))
  ==> read (memory :> wbytes a) s =
      word_xor (word_xor (word_xor S W) (word(2 EXP 384 * 31)))
               (word(2 EXP 1080 * 128))`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV) THENC
                     REWRITE_CONV[WORD_ADD_0])) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC READ_MEMORY_WBYTES_OF_LANES THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  MAP_EVERY (fun j ->
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && can (term_match [] `read (memory :> bytes128 x) (s:x86state)`) (lhs c) &&
         (let ad = rand(rand(rand(rator(lhs c)))) in
          ad = (if j = 0 then `a:int64` else
                subst [mk_small_numeral(16 * j),`n:num`] `word_add (a:int64) (word n)`))
      then let th' = MATCH_MP READ_MEMORY_BYTES64_OF_BYTES128 th in
           STRIP_ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th')
      else NO_TAC)) (0--2) THEN
  MAP_EVERY (fun k ->
    let t = subst [mk_small_numeral k,`k:num`]
              `read (memory :> bytes64 (word_add (a:int64) (word k))) (s:x86state)` in
    GEN_REWRITE_TAC (ONCE_DEPTH_CONV o LAND_CONV)
     [CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
                 (READ_MEMORY_MERGE_CONV 3 t)]) [48; 128] THEN
  ASM_REWRITE_TAC[WORD_SUBWORD_XOR; WORD_XOR_0] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(*** mld_shake256_state of a key of len bytes as the code computes it ***)

let TRG_STATE_EQ len =
  let nb = len / 136 and r = len mod 136 in
  prove(subst [mk_small_numeral len,`len:num`; mk_small_numeral nb,`nb:num`;
               mk_small_numeral (1088 * nb),`bb:num`; mk_small_numeral (8 * r),`rr:num`]
   `!PK. mld_shake256_state len PK =
         word_xor (word_xor (word_xor (mld_keccak_absorb_blocks 136 (word 0) PK nb)
                                      (word((PK DIV 2 EXP bb) MOD 2 EXP 1088)))
                            (word(2 EXP rr * 31)))
                  (word(2 EXP 1080 * 128))`,
   REWRITE_TAC[mld_shake256_state; mld_keccak_absorb; mld_keccak_finalize] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV ORELSEC NUM_DIV_CONV ORELSEC
                       NUM_MOD_CONV ORELSEC NUM_SUB_CONV)) THEN
   REWRITE_TAC[CONJUNCT1 EXP; MULT_CLAUSES] THEN
   CONV_TAC NUM_REDUCE_CONV);;

(*** The statement: the code from the offset start of fn to the return of ***)
(*** the permutation nb + 1, the state at rsp0 + ao, its address in sr    ***)

(* sv: Some (r,off) if the code also saves the register r (the pointer to the
   prefix, ML-DSA-87) to the stack slot at rsp0 + off in the first block *)
let TRG_STMT fn start ao len sr (sv:(string*int) option) =
  let nb = len / 136 in
  let fr = 296 + ao + 208 in
  let toks = ["@FN@",fn; "@MC@",image_mc;
              "@START@",string_of_int(layout fn + start);
              "@AO@",string_of_int ao; "@LEN@",string_of_int len;
              "@FR@",string_of_int fr; "@SR@",sr;
              "@NB1@",string_of_int (nb + 1)] @
             (match sv with
                None -> ["@XV@",""; "@XNO@",""; "@XPRE@",""; "@XPOST@","";
                         "@XR@",""; "@XMC@",""]
              | Some(r,off) ->
                 let os = string_of_int off in
                 ["@XV@"," (pre:int64)";
                  "@XNO@"," /\\ ALL (nonoverlapping (word_add rsp0 (word "^os^"),8)) [(word pc,libmldsa_size); (pk,@LEN@)]";
                  "@XPRE@"," /\\ read "^r^" s = pre";
                  "@XPOST@"," /\\ read (memory :> bytes64 (word_add rsp0 (word "^os^"))) s = pre";
                  "@XR@","; word_add rsp0 (word "^os^"),8";
                  "@XMC@","; memory :> bytes(word_add rsp0 (word "^os^"),8)"]) in
  parse_term(subst_tokens toks (subst_tokens toks
  "exists f_events.
   forall e rsp0 pk pc PK@XV@.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     aligned 32 (rsp0:int64) /\\
     ALL (nonoverlapping (word_sub rsp0 (word 296),@FR@))
         [(word pc,libmldsa_size); (pk,@LEN@)]@XNO@
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @START@) /\\
               read RSP s = rsp0 /\\ read RBX s = pk /\\
               read (memory :> bytes(pk,@LEN@)) s = PK@XPRE@ /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @FN@_after_mldsa_keccakf1600_permute_@NB1@) /\\
               read RSP s = rsp0 /\\ read RBX s = pk /\\
               read @SR@ s = word_add rsp0 (word @AO@) /\\
               read (memory :> wbytes (word_add rsp0 (word @AO@))) s =
               keccak_f1600 (mld_shake256_state @LEN@ PK)@XPOST@ /\\
               (exists e2. read events s = APPEND e2 e /\\
                  e2 = f_events (word_sub rsp0 (word 296)) pk pc /\\
                  memaccess_inbounds e2
                   [pk,@LEN@; word_sub rsp0 (word 296),@FR@;
                    word(pc + rodata_mld_KeccakF_RoundConstants),192@XR@]
                   [word_sub rsp0 (word 296),@FR@@XR@]))
          (MAYCHANGE [RSP; @SR@] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),296);
                      memory :> bytes(word_add rsp0 (word @AO@),208)@XMC@])"));;

(*** The last 48 bytes, the padding and the last permutation, from the ***)
(*** state after the call at step n0                                   ***)

let TRG_FINAL48_TAC execth fo len n0 =
  let nb = len / 136 in
  let a = tr_fb_add fo in
  let stn = "st"^string_of_int nb and wbn = "wb"^string_of_int nb in
  let sv = mk_var(stn,`:1600 word`) and wv = mk_var(wbn,`:1600 word`) in
  let sn = mk_var("s"^string_of_int(n0 + 14),`:x86state`) in
  let fin = list_mk_icomb "word_xor"
             [list_mk_icomb "word_xor"
               [list_mk_icomb "word_xor" [sv; wv]; `word(2 EXP 384 * 31):1600 word`];
              `word(2 EXP 1080 * 128):1600 word`] in
  let pat = subst [mk_small_numeral len,`n:num`]
              `read (memory :> bytes(pk,n)) (s:x86state) = PK` in
  let hz = TR_NORM_RULE(SPECL [mk_small_numeral (8 * len); `PK:num`; mk_small_numeral nb]
                         TRG_HI_ZERO) in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then let st = rand(lhs(concl th)) in
         let b = ISPECL [`pk:int64`; mk_small_numeral len;
                         mk_comb(`read memory:x86state->int64->byte`,st)] READ_BYTES_BOUND in
         ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
                     (REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE; th] b))
    else NO_TAC) THEN
  TR_STATE_CHUNKS_TAC a [0;1;2] ((7--15) @ (17--24)) THEN
  TR_STATE_BYTES_TAC a ((48--55) @ (128--135)) THEN
  TRG_PK_TAC len nb [0;1;2] [] THEN
  TR_NAME_TAC (tr_st nb) stn THEN TR_NAME_TAC (tr_wb nb) wbn THEN
  X86_STEPS_TAC execth ((n0+1)--(n0+14)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI]) THEN
  MP_TAC(SPECL [a; sv; wv; sn] TR_FIN48_MERGE) THEN
  ANTS_TAC THENL
   [REPEAT(CONJ_TAC THENL [TRG_ANTE_TAC len; ALL_TAC]) THEN
    TR_UNNAME_GOAL_TAC wbn THEN
    CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC TR_NORM_CONV THEN
    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC hz THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; fin; `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pk:int64`; `pc:num`] (n0 + 15) THEN
  TR_UNNAME_TAC stn THEN TR_UNNAME_TAC wbn THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM (TRG_STATE_EQ len)]);;

(*** The same for the last 8 bytes (one lane, ML-DSA-87) ***)

let TR_FIN8_MERGE = prove
 (`!(a:int64) (S:1600 word) (W:1600 word) (s:x86state).
  read (memory :> bytes64 a) s =
  word_xor (word_subword S (0,64)) (word_subword W (0,64)) /\
  read (memory :> bytes8 (word_add a (word 8))) s =
  word_xor (word_subword S (64,8)) (word 31) /\
  (!m. m < 7 ==> read (memory :> bytes8 (word_add a (word (9 + m)))) s =
                 word_subword S (72 + 8 * m,8)) /\
  (!n. n < 14 ==> read (memory :> bytes64 (word_add a (word (16 + 8 * n)))) s =
                  word_subword S (128 + 64 * n,64)) /\
  (!m. m < 7 ==> read (memory :> bytes8 (word_add a (word (128 + m)))) s =
                 word_subword S (1024 + 8 * m,8)) /\
  read (memory :> bytes8 (word_add a (word 135))) s =
  word_xor (word_subword S (1080,8)) (word 128) /\
  (!n. n < 8 ==> read (memory :> bytes64 (word_add a (word (136 + 8 * n)))) s =
                 word_subword S (1088 + 64 * n,64)) /\
  (!n. n < 24 ==> word_subword W (64 + 64 * n,64) = (word 0:int64))
  ==> read (memory :> wbytes a) s =
      word_xor (word_xor (word_xor S W) (word(2 EXP 64 * 31)))
               (word(2 EXP 1080 * 128))`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV) THENC
                     REWRITE_CONV[WORD_ADD_0])) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC READ_MEMORY_WBYTES_OF_LANES THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  MAP_EVERY (fun k ->
    let t = subst [mk_small_numeral k,`k:num`]
              `read (memory :> bytes64 (word_add (a:int64) (word k))) (s:x86state)` in
    GEN_REWRITE_TAC (ONCE_DEPTH_CONV o LAND_CONV)
     [CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
                 (READ_MEMORY_MERGE_CONV 3 t)]) [8; 128] THEN
  ASM_REWRITE_TAC[WORD_SUBWORD_XOR; WORD_XOR_0] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let TRG_FINAL8_TAC execth fo len n0 =
  let nb = len / 136 in
  let a = tr_fb_add fo in
  let stn = "st"^string_of_int nb and wbn = "wb"^string_of_int nb in
  let sv = mk_var(stn,`:1600 word`) and wv = mk_var(wbn,`:1600 word`) in
  let sn = mk_var("s"^string_of_int(n0 + 7),`:x86state`) in
  let fin = list_mk_icomb "word_xor"
             [list_mk_icomb "word_xor"
               [list_mk_icomb "word_xor" [sv; wv]; `word(2 EXP 64 * 31):1600 word`];
              `word(2 EXP 1080 * 128):1600 word`] in
  let pat = subst [mk_small_numeral len,`n:num`]
              `read (memory :> bytes(pk,n)) (s:x86state) = PK` in
  let hz = TR_NORM_RULE(SPECL [mk_small_numeral (8 * len); `PK:num`; mk_small_numeral nb]
                         TRG_HI_ZERO) in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pat) (concl th)
    then let st = rand(lhs(concl th)) in
         let b = ISPECL [`pk:int64`; mk_small_numeral len;
                         mk_comb(`read memory:x86state->int64->byte`,st)] READ_BYTES_BOUND in
         ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
                     (REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE; th] b))
    else NO_TAC) THEN
  TR_STATE_CHUNKS_TAC a [] ((0::(2--15)) @ (17--24)) THEN
  TR_STATE_BYTES_TAC a ((8--15) @ (128--135)) THEN
  TRG_PK_TAC len nb [] [0] THEN
  TR_NAME_TAC (tr_st nb) stn THEN TR_NAME_TAC (tr_wb nb) wbn THEN
  X86_STEPS_TAC execth ((n0+1)--(n0+7)) THEN
  MP_TAC(SPECL [a; sv; wv; sn] TR_FIN8_MERGE) THEN
  ANTS_TAC THENL
   [REPEAT(CONJ_TAC THENL [TRG_ANTE_TAC len; ALL_TAC]) THEN
    TR_UNNAME_GOAL_TAC wbn THEN
    CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC TR_NORM_CONV THEN
    REPEAT CONJ_TAC THEN
    MATCH_MP_TAC hz THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; fin; `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `pk:int64`; `pc:num`] (n0 + 8) THEN
  TR_UNNAME_TAC stn THEN TR_UNNAME_TAC wbn THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM (TRG_STATE_EQ len)]);;

(* fn, start: the function and the offset of the zeroing of the state;
   ao: the offset of the state from rsp0; len: the length of the key; sr: the
   register with the address of the state; zoffs: the offsets from rsp0 of the
   aligned stores that zero it (the unaligned one is at ao + 188). *)
let TRG_TAC fn start ao len sr (sv:(string*int) option) =
  let nb = len / 136 in
  let fo = 296 + ao in
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout fn + start,
       layout (fn^"_after_mldsa_keccakf1600_permute_"^string_of_int(nb + 1)))] in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fb:int64) (pk:int64) (pc:num). f_ev_all fb pk pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN WORD_FORALL_OFFSET_TAC 296 THEN
  MAP_EVERY X_GEN_TAC ([`fb:int64`; `pk:int64`; `pc:num`; `PK:num`] @
                       (if sv = None then [] else [`pre:int64`])) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  TR_ALIGNED_TAC 296 (map (fun j -> ao + 16 * j) (0--11)) THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC execth (1--2) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] (subst [mk_small_numeral (fo + 188),`n:num`]
              `read (memory :> bytes128 (word_add fb (word n))) s2 = x`))
           (concl th)
    then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th) else NO_TAC) THEN
  ADDR_NORMALIZE_TAC THEN
  X86_STEPS_TAC execth (3--14) THEN
  MP_TAC(SPECL [tr_fb_add fo; `s14:x86state`] TR_ZERO_MERGE) THEN
  ANTS_TAC THENL [TRG_ANTE_TAC len; DISCH_TAC] THEN
  let k0n = if sv = None then 25 else 26 in
  TRG_BLOCK_TAC execth fo len k0n 0 14 THEN
  MAP_EVERY (fun k -> TRG_BLOCK_TAC execth fo len k0n k (15 + k0n + 29 * (k - 1))) (1--(nb-1)) THEN
  (if len mod 136 = 48 then TRG_FINAL48_TAC else TRG_FINAL8_TAC)
    execth fo len (15 + k0n + 29 * (nb - 1)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PROVE_TR65 fn =
  prove(TRG_STMT fn 0x412 64 1952 "R15" None, TRG_TAC fn 0x412 64 1952 "R15" None);;

let PROVE_TR87 fn =
  prove(TRG_STMT fn 0x527 256 2592 "R13" (Some("R13",1336)),
        TRG_TAC fn 0x527 256 2592 "R13" (Some("R13",1336)));;

(* ------------------------------------------------------------------------- *)
(* mld_polyw1_pack_32 (two coefficients of 4 bits per byte, ML-DSA-65/87) of *)
(* the polynomial at rsp0 + ob to the 128 bytes at op, as clang -O3 has      *)
(* vectorised it (SSE2): 16 iterations of 16 coefficients, four aligned      *)
(* loads at [rsp + rax * 8 + ob + 16 g] (RAX = 8 i), SHUFPS of the even and  *)
(* odd lanes, PSLLD by 4 and POR, the mask of the low byte of each lane      *)
(* (XMM5) and two PACKUSWB, and two 32-bit stores at [r15 + rax - 4] and     *)
(* [r15 + rax], R15 = op + 4. From the offset start of the function (the end *)
(* of the use-hint loop, where RAX is set to 0) to the exit of the loop. The *)
(* values of the vector registers are abbreviated after each step (the       *)
(* PACKUSWB terms grow quickly otherwise); each output byte is then shown    *)
(* by unfolding them, PACKUSWB_JOIN, SIMD_SIMPLIFY_CONV and bit-blasting.    *)
(* ------------------------------------------------------------------------- *)

(* ABBREV_STATE_TAC for the vector registers only (the general registers
   hold the addresses) *)
let ABBREV_YMM_STATE_TAC (s:term) =
  let is_small t = is_var t ||
    (is_comb t && is_const(rator t) && fst(dest_const(rator t)) = "word" &&
     is_numeral(rand t)) in
  let one th =
    let c = concl th in
    if not (is_eq c) then ALL_TAC else
    let l = lhs c and r = rhs c in
    match l with
      Comb(Comb(Const("read",_),Const(reg,_)),st)
        when st = s && String.length reg >= 3 && String.sub reg 0 3 = "YMM" ->
        (match r with
           Comb(Comb(Const("word_join",_),_),lo) when not (is_small lo) ->
             incr (abbrev_ctr ());
             let v = mk_var("ab"^string_of_int (!(abbrev_ctr ())), type_of lo) in
             let ex = mk_exists(v,mk_eq(lo,v)) in
             MP_TAC(EXISTS (ex,lo) (REFL lo)) THEN
             DISCH_THEN(X_CHOOSE_THEN v (fun eth ->
               FIRST_X_ASSUM(fun th' -> if concl th' = c then
                   ASSUME_TAC(CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV
                     (fun t' -> if t' = lo then eth else failwith ""))) th')
                 else NO_TAC) THEN
               ASSUME_TAC(EQ_MP (SYM(ISPECL [v;lo] abbrev_def)) (SYM eth))))
         | _ -> ALL_TAC)
    | _ -> ALL_TAC in
  W(fun (asl,w) -> MAP_EVERY (fun (_,th) -> one th) asl);;

let ABBREV_YMM_STEPS_TAC execth ns =
  MAP_EVERY (fun n ->
    X86_STEPS_TAC execth [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO; VERIF_SUBWORD_JOIN_HI]) THEN
    ABBREV_YMM_STATE_TAC (mk_var("s"^string_of_int n,`:x86state`))) ns;;

(* PACKUSWB_JOIN of x86/proofs/utils/mlkem_native_image.ml *)
let PACKUSWB_JOIN = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte) (b4:byte) (b5:byte) (b6:byte)
    (b7:byte) (b8:byte) (b9:byte) (b10:byte) (b11:byte) (b12:byte)
    (b13:byte) (b14:byte) (b15:byte).
     word((val b0 * 1 + val b1 * 256 + val b2 * 65536 + val b3 * 16777216 +
           val b4 * 4294967296 + val b5 * 1099511627776 +
           val b6 * 281474976710656 + val b7 * 72057594037927936) +
          val b8 * 2 EXP 64 + val b9 * 4722366482869645213696 +
          val b10 * 1208925819614629174706176 +
          val b11 * 309485009821345068724781056 +
          val b12 * 79228162514264337593543950336 +
          val b13 * 20282409603651670423947251286016 +
          val b14 * 5192296858534827628530496329220096 +
          val b15 * 1329227995784915872903807060280344576):int128 =
     word_join
      (word_join (word_join (word_join b15 b14:int16)
                            (word_join b13 b12:int16):int32)
                 (word_join (word_join b11 b10:int16)
                            (word_join b9 b8:int16):int32):int64)
      (word_join (word_join (word_join b7 b6:int16)
                            (word_join b5 b4:int16):int32)
                 (word_join (word_join b3 b2:int16)
                            (word_join b1 b0:int16):int32):int64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32;
           DIMINDEX_64; DIMINDEX_128; ARITH] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_128] THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   (map (fun k -> mk_var("b"^string_of_int k,`:byte`)) (0--15)) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun k ->
    SPEC_TAC(mk_comb(`val:byte->num`,mk_var("b"^string_of_int k,`:byte`)),
             mk_var("n"^string_of_int k,`:num`))) (0--15) THEN
  REPEAT STRIP_TAC THEN
  W(fun (_,w) -> MP_TAC(SPECL [lhand(lhand w);
    `340282366920938463463374607431768211456`] MOD_LT)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ARITH_TAC);;

(* the saturation of PACKUSWB as word operations, for bit-blasting *)
let PACKUSWB_SAT_WORD = prove
 (`!w:int16. word(MIN (if bit 15 w then 0 else val w) 255):byte =
             if bit 15 w then word 0
             else if word_ule w (word 255) then word_zx w else word 255`,
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[MIN] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ULE; VAL_WORD; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[word_zx] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let UNFOLD_ALL_ABBREVS_TAC =
  W(fun (asl,w) ->
    let eqs = mapfilter (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("abbrev_def",_),v),t) -> EQ_MP (ISPECL [v;t] abbrev_def) th
      | _ -> failwith "") asl in
    REWRITE_TAC eqs);;

let W1P_ZX_JOIN = WORD_BLAST `word_zx (word_join (x:int128) (y:int128):int256):int128 = y`;;

let W1PACK32_STMT fn loop start exit ob =
  parse_term(subst_tokens ["@FN@",fn; "@MC@",image_mc; "@START@",string_of_int(layout fn + start);
                           "@EXIT@",exit; "@OB@",string_of_int ob]
  "exists f_events.
  forall e rsp0 op pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word @OB@)) /\\
    ALL (nonoverlapping (op,128)) [(word_add rsp0 (word @OB@),1024); (word pc,libmldsa_size)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) @MC@ /\\
              read RIP s = word (pc + @START@) /\\
              read RSP s = rsp0 /\\ read R15 s = word_add op (word 4) /\\
              read XMM5 s = word 0x000000ff000000ff000000ff000000ff /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@OB@ + 4*i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + @FN@_@EXIT@) /\\
              read RSP s = rsp0 /\\ read RAX s = word 128 /\\ read R15 s = word_add op (word 4) /\\
              read XMM5 s = word 0x000000ff000000ff000000ff000000ff /\\
              (!j. j < 128 ==> read (memory :> bytes8 (word_add op (word j))) s = mld_polyw1_pack_32 x j) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 op pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word @OB@),1024; op,128] [op,128]))
         (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(op,128)])");;

let W1PACK32_ALIASES =
  ["word_add (word_add op (word 4)) (word (1 * (8 * i) + 18446744073709551612)):int64 = word_add op (word (8 * i))";
   "word_add (word_add (word_add op (word 4)) (word (1 * (8 * i)))) (word 18446744073709551612):int64 = word_add op (word (8 * i))";
   "word_add (word_add op (word 4)) (word (1 * (8 * i))):int64 = word_add op (word (8 * i + 4))"];;

let W1PACK32_SETUP_TAC exec fn loop exit ob =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (op:int64) (pc:num).
      APPEND (f_ev_epil rsp0 op pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop rsp0 op pc i)) (f_ev_prol rsp0 op pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `op:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (parse_term(Printf.sprintf
   "\\i s. read RSP s = rsp0 /\\
          read RAX s = word (8 * i) /\\ read R15 s = word_add op (word 4) /\\
          read XMM5 s = word 0x000000ff000000ff000000ff000000ff /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * j)))) s = x j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes8(word_add op (word j))) s = mld_polyw1_pack_32 x j)" ob));;

let W1PACK32_PRE_TAC exec =
  FULL_INIT_TAC THEN X86_STEPS_TAC exec (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let W1PACK32_BODY_TAC exec ob =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
  FULL_INIT_TAC THEN
  XMM_EXISTSTOP_TAC "top5" `YMM5` THEN
  VAL_INT64_TAC `8 * i` THEN
  MAP_EVERY (fun k -> ALIGN16_IDX_TAC `rsp0:int64`
      (parse_term(Printf.sprintf "8 * (8 * i) + %d" (ob + k)))) [0; 16; 32; 48] THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "!k. k < 16 ==> read(memory :> bytes32(word_add rsp0 (word(%d + 4 * (16 * i + k))))) s0 = (x:num->int32)(16 * i + k)" ob)) MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  STRIP_TAC THEN ADDR_LINEAR_BASES_TAC [ob] THEN
  MAP_EVERY (fun g ->
    MERGE_LIN_TAC_B 2 [ob]
      (parse_term(Printf.sprintf "read(memory :> bytes128(word_add rsp0 (word (8 * (8 * i) + %d)))) s0" (ob + 16 * g))))
    [0;1;2;3] THEN
  ALIAS_ASSUME_TAC W1PACK32_ALIASES THEN
  (fun g -> abbrev_ctr () := 0; ALL_TAC g) THEN
  ABBREV_YMM_STEPS_TAC exec (1--22) THEN X86_STEPS_TAC exec (23--25);;


let W1PACK32_FIN_TAC =
  let abbr th = match concl th with
      Comb(Comb(Const("abbrev_def",_),_),_) -> true | _ -> false in
  RULE_ASSUM_TAC(fun th -> if abbr th then REWRITE_RULE[PACKUSWB_JOIN; PACKUSWB_SAT_WORD] th
                           else th) THEN
  MAP_EVERY (fun t ->
     FIRST_X_ASSUM(fun th ->
       if can (term_match [] (subst [t,`a:int64`] `read (memory :> bytes32 a) s = v`)) (concl th)
       then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th) else NO_TAC))
   [`word_add op (word (8 * i)):int64`; `word_add op (word (8 * i + 4)):int64`] THEN
  RULE_ASSUM_TAC(fun th -> if can (term_match [] `read (memory :> bytes8 a) s = v`) (concl th)
     then CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THENC
                    REWRITE_CONV[GSYM ADD_ASSOC] THENC NUM_REDUCE_CONV) th else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[XMM5; READ_COMPONENT_COMPOSE; READ_ZEROTOP_128] THEN
      ASM_REWRITE_TAC[W1P_ZX_JOIN] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT_N 8] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[mld_polyw1_pack_32] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      UNFOLD_ALL_ABBREVS_TAC THEN REPEAT CONJ_TAC THEN
      CONV_TAC(SIMD_SIMPLIFY_CONV []) THEN APP_BLAST_TAC `x:num->int32` THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let W1PACK32_TAC exec fn loop exit ob =
  W1PACK32_SETUP_TAC exec fn loop exit ob THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    W1PACK32_PRE_TAC exec;
    W1PACK32_BODY_TAC exec ob THEN W1PACK32_FIN_TAC;
    FULL_EXIT0_TAC];;

(* fn: the function; loop, exit: the labels of the loop; start: the offset of
   the code before the loop; ob: the offset of the coefficients from rsp0 *)
let PROVE_W1PACK32 fn loop start exit ob =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout fn + start, layout (fn^"_"^exit))] in
  prove(W1PACK32_STMT fn loop start exit ob, W1PACK32_TAC exec fn loop exit ob);;

(* ------------------------------------------------------------------------- *)
(* The comparison of c~ (cc0, cc1, cc2 at rsp0 + 1120, + 1136, + 1152) with  *)
(* c2 (dd0, dd1, dd2 at rsp0 + 1184, ...), 48 bytes, as clang 23 vectorizes  *)
(* mld_ct_memcmp for ML-DSA-65: as CMP44 (inline_verify.ml), with the last   *)
(* chunk read as two 64-bit words and a 32-bit word, part of the XOR fold   *)
(* going through a 16-byte stack slot at rsp0 + 48.                          *)
(* ------------------------------------------------------------------------- *)


let CMP65_STMT fn =
  parse_term(subst_tokens ["@FN@",fn; "@MC@",image_mc]
  "exists f_events.
  forall e rsp0 pc (cc0:int128) (cc1:int128) (cc2:int128) (dd0:int128) (dd1:int128) (dd2:int128).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    aligned 16 (word_add rsp0 (word 48)) /\\
    aligned 16 (word_add rsp0 (word 1120)) /\\ aligned 16 (word_add rsp0 (word 1184)) /\\
    nonoverlapping (word_add rsp0 (word 48),16) (word pc,libmldsa_size)
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) @MC@ /\\
              read RIP s = word (pc + @FN@_after_mld_H65_2) /\\
              read RSP s = rsp0 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1120))) s = cc0 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1136))) s = cc1 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1152))) s = cc2 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1184))) s = dd0 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1200))) s = dd1 /\\
              read (memory :> bytes128 (word_add rsp0 (word 1216))) s = dd2 /\\
              read events s = e)
         (\\s. read RIP s = word (pc + @FN@_join2) /\\
              read RSP s = rsp0 /\\
              read R14 s = (if cc0 = dd0 /\\ cc1 = dd1 /\\ cc2 = dd2 then word 0 else word 4294967290) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word 1120),48; word_add rsp0 (word 1184),48;
                                        word_add rsp0 (word 48),16]
                                       [word_add rsp0 (word 48),16]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; R14] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(word_add rsp0 (word 48),16)])");;

let CMP65_SETUP_TAC execth =
  CONCRETIZE_F_EVENTS_TAC
   `\(rsp0:int64) (pc:num). f_ev_all rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`;
    `cc0:int128`; `cc1:int128`; `cc2:int128`; `dd0:int128`; `dd1:int128`; `dd2:int128`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
  GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun a ->
    FIRST_ASSUM(fun th ->
      if can (term_match [] (subst [mk_small_numeral a,`k:num`]
           `read (memory :> bytes128 (word_add rsp0 (word k))) s = x`)) (concl th)
      then MAP_EVERY STRIP_ASSUME_TAC [CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th;
                                       CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th]
      else NO_TAC)) [1152; 1216] THEN
  ADDR_NORMALIZE_TAC THEN
  (fun g -> abbrev_ctr () := 0; ALL_TAC g);;

let CMP65_TAC execth =
  CMP65_SETUP_TAC execth THEN
  ABBREV_STEPS_TAC execth (1--32) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes128 (word_add rsp0 (word 48))) s32 = x`) (concl th)
    then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 4) th) else NO_TAC) THEN
  ADDR_NORMALIZE_TAC THEN
  ABBREV_STEPS_TAC execth (33--63) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ab50:int64 = if word_zx (ab43:int128):byte = word 0
                             then word 0 else word 4294967290` SUBST1_TAC THENL
   [UNFOLD_ABBREVS_TAC (abn [50;49;48;47;46;45]) THEN REWRITE_TAC[WORD_VAL_MOD_256] THEN
    CONV_TAC BITBLAST_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `(word_zx (ab43:int128):byte = word 0) <=> (ab35:int128 = word 0)`
   SUBST1_TAC THENL
   [UNFOLD_ABBREVS_TAC (abn [43;42;41;40;39;38;37;36]) THEN
    REWRITE_TAC[WORD_VAL_MOD_256] THEN CONV_TAC BITBLAST_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ab35:int128 = word 0) <=>
                (cc0:int128) = dd0 /\ (cc1:int128) = dd1 /\ (cc2:int128) = dd2`
   SUBST1_TAC THENL
   [UNFOLD_ABBREVS_TAC (abn [35;34;33;32;31;30;25;24;23;8;7;6;5;4;3;2;1]) THEN
    CONV_TAC BITBLAST_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let PROVE_CMP65 fn =
  let execth = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_after_mld_H65_2"), layout fn + 0x1ca6)] in
  prove(CMP65_STMT fn, CMP65_TAC execth);;
