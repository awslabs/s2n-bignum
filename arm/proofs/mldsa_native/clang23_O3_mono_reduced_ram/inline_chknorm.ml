(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The norm check of one polynomial, as clang 23 -O3 has inlined it into     *)
(* mldsa{44,65,87}_polyvecl_chknorm (4, 5 and 7 instances, one per           *)
(* polynomial): a lemma from the head of the loop to its exit, generated for *)
(* the labels and registers of an instance, as in inline_sponge.ml. The      *)
(* loop reads one coefficient per iteration and ORs a mask (all ones if the  *)
(* coefficient is not below the bound in absolute value) into an             *)
(* accumulator, which is zero at the head. The registers are, in the order   *)
(* of the list:                                                              *)
(*   T = temporary, BASE = polynomial, IDX = byte offset (from 0),           *)
(*   C, N = temporaries, ACC = accumulator, BND = bound (low 32 bits)        *)
(*     ldrsw T, [BASE, IDX]; add IDX, IDX, #4; cmp IDX, #0x400;              *)
(*     mov w.C, w.T; lsr T, T, #31; neg w.N, w.C; bic w.C, w.C, w.T;         *)
(*     and w.T, w.N, w.T; eon w.T, w.T, w.C; add w.T, w.BND, w.T;            *)
(*     sxtw T, w.T; lsr T, T, #31; orr w.ACC, w.ACC, w.T; b.ne              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "common/mldsa_native_poly.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

let CHKNORM_LOOP_TERM mc loop exit (rs:string list) =
  let r k = List.nth rs k in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e a (x:num->int32) bnd pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = a /\\ read %s s = word 0 /\\
                  read %s s = word 0 /\\ read %s s = bnd /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = a /\\ read %s s = word 1024 /\\
                  read %s s = bnd /\\
                  read %s s = word_zx(mld_poly_chknorm x (word_zx bnd)) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2 [a,1024] []))
             (MAYCHANGE [PC; %s; %s; %s; %s; %s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events])"
   mc loop (r 1) (r 2) (r 5) (r 6) exit (r 1) (r 2) (r 6) (r 5)
   (r 0) (r 2) (r 3) (r 4) (r 5));;

(*** The absolute value as the code selects it, with the mask of the sign ***)

let MLD_CT_ABS_SELECT = prove
 (`!y:int32. mld_ct_abs y =
             word_xor (word_and (word_xor (word_sub (word 0) y) y)
                                (word_ishr y 31)) y`,
  REWRITE_TAC[mld_ct_abs; GSYM MSB_IVAL; DIMINDEX_32;
              WORD_RULE `word_neg(y:N word) = word_sub (word 0) y`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC);;

let EXISTS_LT_SUC_SPLIT = prove
 (`!P i. (?j. j < i + 1 /\ P j) <=> (?j. j < i /\ P j) \/ P i`,
  REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN MESON_TAC[]);;

let CHKNORM_INV rs =
  let r k = List.nth rs k in
  parse_term(Printf.sprintf
   "\\i s. read %s s = a /\\ read %s s = word(4 * i) /\\
          read %s s = bnd /\\
          read %s s =
          word_zx(if ?j. j < i /\\
                         ival(word_sub (word_sub (word_zx bnd) (word 1))
                                       (mld_ct_abs((x:num->int32) j))) < &0
                  then word 4294967295 else word 0:int32) /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j)" (r 1) (r 2) (r 6) (r 5));;

(*** The loop test: IDX = 4 * i + 4 - 1024 is zero exactly in the last pass ***)

let CHK_TEST = prove
 (`!i. i < 256
       ==> (val (word_add (word (4 * i)) (word 18446744073709550596):int64) = 0 <=>
            ~(i + 1 < 256))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(*** The accumulator after one more coefficient: this is proved with the ***)
(*** context cleared, as BITBLAST_TAC uses the assumptions               ***)

let CHKNORM_MASK_TAC =
  REWRITE_TAC[EXISTS_LT_SUC_SPLIT] THEN
  SPEC_TAC(`?j. j < i /\
                ival (word_sub (word_sub (word_zx (bnd:int64)) (word 1))
                               (mld_ct_abs ((x:num->int32) j))) < &0`,
           `p:bool`) THEN
  SPEC_TAC(`(x:num->int32) i`,`y:int32`) THEN
  SPEC_TAC(`bnd:int64`,`bnd:int64`) THEN
  REPEAT GEN_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  ASM_CASES_TAC `p:bool` THEN ASM_REWRITE_TAC[] THENL
   [BITBLAST_TAC;
    POP_ASSUM(K ALL_TAC) THEN
    REWRITE_TAC[GSYM WORD_ISHR_31_COND; MLD_CT_ABS_SELECT] THEN
    BITBLAST_TAC];;

let CHKNORM_LOOP mc exec loop exit (rs:string list) =
  let tm = CHKNORM_LOOP_TERM mc loop exit rs in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_epil a pc)
       (APPEND (ENUMERATEL 256 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `x:num->int32`;
                       `bnd:int64`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) (CHKNORM_INV rs) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The head of the loop: the precondition is the invariant for i = 0 ***)

    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; NOT_EXISTS_THM;
                COND_ID; WORD_ZX_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body: one coefficient, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `x:num->int32` (concl th))) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    ARM_STEPS_TAC exec (1--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REWRITE_TAC[MP (SPEC `i:num` CHK_TEST) (ASSUME `i < 256`)] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONJ_TAC THENL [CHKNORM_MASK_TAC; DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The exit: the invariant for i = 256 is the postcondition ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[mld_poly_chknorm] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The proof of mldsa{44,65,87}_polyvecl_chknorm from the lemmas for its n   *)
(* loops. Loop k (from 1) is in the registers                                *)
(*   T = X(10+k), BASE = X(9+k), IDX = X(8+k), C = X(11+k), N = X(12+k)      *)
(*   (X0 for k = 7), ACC = X(7+k), BND = X1; loop 1 is in T = X10, BASE = X0, *)
(*   IDX = X9, C = X11, N = X12, ACC = X8,                                   *)
(* and is entered after 2 instructions (k = 1), 3 (k = 2 to 5) or 4 (k = 6,  *)
(* 7; the offset of the polynomial does not fit in an immediate) from the    *)
(* exit of the previous loop. The accumulators are ORed and the scratch      *)
(* registers cleared in the last `final' instructions, with the return.      *)
(* ------------------------------------------------------------------------- *)

let CHKNORM_REGS k =
  let x j = Printf.sprintf "X%d" j in
  if k = 1 then ["X10"; "X0"; "X9"; "X11"; "X12"; "X8"; "X1"]
  else [x(10+k); x(9+k); x(8+k); x(11+k);
        (if k = 7 then "X0" else x(12+k)); x(7+k); "X1"];;

let CHKNORM_PRE k = if k = 1 then 2 else if k <= 5 then 3 else 4;;

let CHKNORM_APPEND_CONG = prove
 (`!(a:(A)list) b c d. a = c /\ b = d ==> APPEND a b = APPEND c d`,
  MESON_TAC[]);;

(*** The events of the whole: those of the loops, in their order ***)

let CHKNORM_EVENTS_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND; GSYM APPEND_ASSOC] THEN
    REPEAT(MATCH_MP_TAC CHKNORM_APPEND_CONG THEN CONJ_TAC THENL
            [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
    FULL_UNIFY_F_EVENTS_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND; GSYM APPEND_ASSOC] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(*** The coefficients 256 * k + i of the vector at the polynomial k ***)

let CHKNORM_SLICE_TAC n k sname =
  let off = if k = 0 then "4 * j" else Printf.sprintf "%d + 4 * j" (1024*k) in
  let tm = parse_term(Printf.sprintf
    "!j. j < 256 ==> read (memory :> bytes32 (word_add v (word (%s)))) %s = (x:num->int32) (%d + j)" off sname (256*k)) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + j" (256*k))) o
      check (fun th -> let c = concl th in is_forall c &&
                       can (find_term (fun t -> t = parse_term(Printf.sprintf "i < %d" (256 * n)))) c)) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0];
    ALL_TAC];;

(*** The ORed masks of the n polynomials as the mask of the vector ***)

let CHKNORM_MASK_VEC_TAC n =
  let poly k =
    if k = 0 then `mld_poly_chknorm (x:num->int32) (word_zx (bnd:int64))`
    else parse_term(Printf.sprintf
      "mld_poly_chknorm (\\j. (x:num->int32) (%d + j)) (word_zx (bnd:int64))"
      (256 * k)) in
  let nums = map (fun k -> num_CONV (mk_small_numeral k)) (1 -- n) in
  REWRITE_TAC([mld_polyvec_chknorm; mld_poly_of] @ nums) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; ETA_AX] THEN
  MAP_EVERY (fun k -> SPEC_TAC(poly k,mk_var("p"^string_of_int k,`:int32`)))
            (rev (0 -- (n-1))) THEN
  REPEAT GEN_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;;

let CHKNORM_FULL_TAC mc exec lname n final =
  let loops = map (fun k ->
    let l = Printf.sprintf "%s_loop%d" lname k in
    CHKNORM_LOOP "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
       exec l (l^"_exit") (CHKNORM_REGS k)) (1 -- n) in
  let hname k = "H_L"^string_of_int k in
  let args = "v bnd pc stackpointer returnaddress" in
  let template = parse_term(Printf.sprintf
   "\\(v:int64) (bnd:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND (f_ev_tail %s) %s :(uarch_event)list"
    args
    (let rec build k =
       if k = 1 then Printf.sprintf "(f_ev_l1 %s)" args
       else Printf.sprintf "(APPEND (f_ev_l%d %s) %s)" k args (build (k-1)) in
     build n)) in
  let rec sk_pre k =
    if k = 1 then 2 else sk_pre (k-1) + 1 + CHKNORM_PRE k in
  let call k s_pre =
    let reg = List.nth (CHKNORM_REGS k) 1 in
    let a = parse_term(Printf.sprintf "read %s s" reg) in
    let x = if k = 1 then `x:num->int32`
            else parse_term(Printf.sprintf "\\j. (x:num->int32)(%d + j)" (256*(k-1))) in
    FULL_CALL_TAC mc exec (hname k)
     [a; x; `read X1 s`; `pc:num`]
     [`pc:num`; `v:int64`; `bnd:int64`; `stackpointer:int64`;
      `returnaddress:int64`] (s_pre + 1) in
  MAP_EVERY (fun k -> ASSUME_CALLEE_SAFETY_TAILED_TAC (el (k-1) loops) (hname k))
            (1 -- n) THEN
  CONCRETIZE_F_EVENTS_TAC template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC exec (1--2) THEN
  VEC_REST_TAC `!i. i < 256 ==> read (memory :> bytes32 (word_add v (word (4 * i)))) s2 = (x:num->int32) i` THEN
  call 1 2 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 APPEND]) THEN
  MAP_EVERY (fun k ->
     let s0 = sk_pre (k-1) + 1 in
     let s1 = sk_pre k in
     ARM_STEPS_TAC exec (s0 + 1 -- s1) THEN
     CHKNORM_SLICE_TAC n (k-1) ("s"^string_of_int s1) THEN
     call k s1) (2 -- n) THEN
  (let s0 = sk_pre n + 1 in
   ARM_STEPS_TAC exec (s0 + 1 -- (s0 + final))) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [CHKNORM_MASK_VEC_TAC n; ALL_TAC] THEN
  CONJ_TAC THENL [CHKNORM_EVENTS_TAC; REWRITE_TAC[WORD_ADD_0]];;
