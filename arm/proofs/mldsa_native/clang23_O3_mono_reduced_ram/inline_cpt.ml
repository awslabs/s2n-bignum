(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the code that clang 23 -O3 has inlined into                    *)
(* mld_compute_pack_t0_t1{44,65,87} of mldsa-native's monolithic reduced-RAM *)
(* build, stated from the start of each region or loop to its end with the   *)
(* registers and addresses as parameters (see inline_sign.ml for the form):  *)
(*                                                                           *)
(* - CPT_ADD_STMT: the sum t + s2 of row k (poly_add), straight-line code    *)
(*   that also sets x8 = 0, q4 = 2^22 and q5 = -q in each lane for the       *)
(*   reduce loop that follows (INLINE_MAP_STMT of inline_sign_map.ml);       *)
(* - CPT_P2R_LOOP: power2round, 8 coefficients per iteration, t0 in place    *)
(*   and t1 to a second buffer;                                              *)
(* - CPT_T1_LOOP: polyt1_pack of t1, 64 coefficients per iteration with LD4, *)
(*   shifts, UZP1, TBL with index tables that the function spills to its     *)
(*   frame, and BSL.                                                         *)
(*                                                                           *)
(* The reduction and the addition of q are INLINE_REDUCE_LOOP "9"            *)
(* (inline_sign_arith.ml) and INLINE_CADDQ_LOOP (inline_sign.ml).            *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_arith.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_map.ml";;

let PTR_ADD_G = prove(`!b:int64 n k. word_add (word_add b (word n)) (word k) = word_add b (word (n + k))`, REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The sum of the polynomial of t at fp + toff and that of s2 at fp + soff,  *)
(* into the first, with -q in each lane at fp + qoff (as INLINE_SUB_STMT).   *)
(* ------------------------------------------------------------------------- *)

let CPT_ADD_STMT mc start stop toff soff qoff (mods:string list) =
  let lo = min soff qoff and hi = max (toff + 1024) (soff + 1024) in
  INLINE_MAP_STMT mc start stop ["x",toff; "y",soff] toff "mld_poly_add x y i"
   lo (hi - lo) mods
   (Printf.sprintf "read (memory :> bytes128 (word_add fp (word %d))) s =
      word 0xff801fffff801fffff801fffff801fff /\\" qoff)
   "read X8 s = word 0 /\\
    read Q4 s = word 0x00400000004000000040000000400000 /\\
    read Q5 s = word 0xff801fffff801fffff801fffff801fff /\\";;

let CPT_ADD_PROVE tm exec toff soff n =
  INLINE_MAP_PROVE tm exec ["x",toff; "y",soff] n [mld_poly_add] [WORD_ADD_SYM];;

(* ------------------------------------------------------------------------- *)
(* power2round: a[i] := lo(a[i]), b[i] := hi(a[i]) with                      *)
(*   hi(x) = (x + 0xfff) >> 13 (arithmetic), lo(x) = x - ((x + 0xfff) & ~0x1fff), *)
(* in 32 iterations of 8 coefficients, with the registers                    *)
(*   R0 = temporary (a + offset), R1 = a, R2 = byte offset (from 0),         *)
(*   R3 = temporary (b + offset), R4 = b, R5 = splat 0xfff, R6 = splat ~0x1fff *)
(*     add R0, R1, R2; add R3, R4, R2; add R2, R2, #0x20; ldp q0, q1, [R0];  *)
(*     cmp R2, #0x400; add v2, v0, R5; add v3, v1, R5; and v4, v2, R6;       *)
(*     and v5, v3, R6; sshr v2, #13; sshr v3, #13; sub v0, v0, v4;           *)
(*     sub v1, v1, v5; stp q2, q3, [R3]; stp q0, q1, [R0]; b.ne              *)
(* ------------------------------------------------------------------------- *)

let CPT_P2R_TERM mc loop exit (rs:string list) =
  let r k = List.nth rs k in
  parse_term(INLINE_FILL
   "exists f_events.
      forall e a b (x:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        nonoverlapping (a,1024) (b,1024) /\\
        ALL (nonoverlapping (word pc,libmldsa_size)) [(a,1024); (b,1024)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) @mc@ /\\
                  read PC s = word (pc + @loop@) /\\
                  read @R1@ s = a /\\ read @R4@ s = b /\\ read @R2@ s = word 0 /\\
                  read @R5@ s = word 0x00000fff00000fff00000fff00000fff /\\
                  read @R6@ s = word 0xffffe000ffffe000ffffe000ffffe000 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + @exit@) /\\
                  read @R2@ s = word 1024 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_power2round_lo x i) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add b (word(4 * i))))
                             s = mld_poly_power2round_hi x i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a b pc /\\
                     memaccess_inbounds e2 [a,1024; b,1024] [a,1024; b,1024]))
             (MAYCHANGE [PC; @R0@; @R2@; @R3@] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024); memory :> bytes(b,1024)])"
   ["mc",mc; "loop",loop; "exit",exit; "R0",r 0; "R1",r 1; "R2",r 2;
    "R3",r 3; "R4",r 4; "R5",r 5; "R6",r 6]);;

(*** The body of a loop with 8 coefficients of x per iteration, as        ***)
(*** INLINE_VEC8_BODY_TAC, with the constants excl that mark the facts    ***)
(*** about the outputs                                                    ***)

let CPT_VEC8_BODY_TAC exec (bases:string*string*string) (excl:term list) n =
  let (_,a0,a1) = bases in
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
    [MATCH_MP INLINE_CHUNK8_INPUT_SPLIT (ASSUME `i < 32`)] o
    check (fun th -> is_forall(concl th) &&
                     free_in `x:num->int32` (concl th) &&
                     is_conj(lhand(snd(dest_forall(concl th)))) &&
                     not(exists (fun c -> free_in c (concl th)) excl))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC(INLINE_LANE_ADDRS bases) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MP_TAC(READ_MEMORY_MERGE_CONV 2 (parse_term(Printf.sprintf
    "read (memory :> bytes128 (%s)) s0" a0))) THEN
  MP_TAC(READ_MEMORY_MERGE_CONV 2 (parse_term(Printf.sprintf
    "read (memory :> bytes128 (%s)) s0" a1))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  MAP_EVERY (fun k -> ARM_STEPS_TAC exec [k] THEN SIMD_SIMPLIFY_TAC[])
            (1--n) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (fun th ->
      can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
      not(free_in `s0:armstate` (concl th)))));;

let CPT_VEC8_FINAL_TAC (addrs:thm list) (fin:tactic) =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[INLINE_CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC addrs THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN fin THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT_P2R_FIN_TAC =
  REWRITE_TAC[mld_power2round_lo; mld_power2round_hi] THEN
  APP_BLAST_TAC `x:num->int32`;;

let CPT_P2R_LOOP mc exec loop exit (rs:string list) =
  let r k = List.nth rs k in
  let tm = CPT_P2R_TERM mc loop exit rs in
  let inv = parse_term(INLINE_FILL
   "\\i s. read @R1@ s = a /\\ read @R4@ s = b /\\ read @R2@ s = word(32 * i) /\\
          read @R5@ s = word 0x00000fff00000fff00000fff00000fff /\\
          read @R6@ s = word 0xffffe000ffffe000ffffe000ffffe000 /\\
          (!j. 8 * i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   (x:num->int32) j) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_power2round_lo (x j)) /\\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   mld_power2round_hi (x j))"
   ["R1",r 1; "R2",r 2; "R4",r 4; "R5",r 5; "R6",r 6]) in
  let abases = INLINE_BASES "9" 0
  and bbases = ("b", "word_add b (word (32 * i))",
                     "word_add b (word (32 * i + 16))") in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (b:int64) (pc:num).
      APPEND (f_ev_epil a b pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a b pc i)) (f_ev_prol a b pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `b:int64`;
                       `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS;
              mld_poly_power2round_lo; mld_poly_power2round_hi; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; CONJUNCT1 LT; LE_0;
                WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CPT_VEC8_BODY_TAC exec abases [`mld_power2round_lo`; `mld_power2round_hi`]
      15 THEN
    ARM_STEPS_TAC exec [16] THEN
    CPT_VEC8_FINAL_TAC (INLINE_LANE_ADDRS abases @ INLINE_LANE_ADDRS bbases)
      CPT_P2R_FIN_TAC;

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* polyt1_pack of the 256 coefficients x at b into the 320 bytes at op, in   *)
(* 4 iterations of 64 coefficients (four LD4 of 16 coefficients each) to 80  *)
(* bytes (STR, STP, STP), with the registers                                 *)
(*   R0 = b, R1 = byte offset (from 0, by 256), R2 = output pointer (by 80), *)
(*   R3, R4 = temporaries,                                                   *)
(* the TBL index vectors in q12 to q15 and 13 more at fp + 112 .. fp + 319,  *)
(* fp the stack pointer (the function spills the 17 vectors of its          *)
(* constants there, CPT_TBL_CONSTS).                                         *)
(* ------------------------------------------------------------------------- *)

let CPT_TBL_REGS =
  ["Q12","0x0f120d0c0b0a11080706051003020100";
   "Q13","0x3c3834302c2824201c1814100c080400";
   "Q14","0x03ffffff1202ffffff1101ffffff1000";
   "Q15","0x0fff1a120b0aff19110605ff18100100"];;

let CPT_TBL_STACK =
  [304,"0x1606ffffff1505ffffff1404ffffff13";
   288,"0x0f0eff1d150a09ff1c140504ff1b1300";
   272,"0x0f0e150c0b0a09140706050413020100";
   256,"0xffff1c0cffffff1b0bffffff1a0affff";
   240,"0x1c140d0cff1b130807ff1a120302ff19";
   224,"0x0f0e0d0c1b0a0908071a050403021900";
   208,"0xffffff1f0fffffff1e0effffff1d0dff";
   192,"0xff1f170c0bff1e160706ff1d150201ff";
   176,"0x1f0e0d0c0b1e090807061d040302011c";
   160,"0x09ffffff1808ffffff1707ffffff1606";
   144,"0xff1909ffffff1808ffffff1707ffffff";
   128,"0x00ffffff0000ffffff0000ffffff0000";
   112,"0x0f0e0d180b0a09081706050403160100"];;

let CPT_T1_CONST_PRE =
  String.concat " /\\\n" (map (fun (q,v) -> Printf.sprintf "read %s s = word %s" q v) CPT_TBL_REGS @
   map (fun (k,v) -> Printf.sprintf
     "read (memory :> bytes128 (word_add fp (word %d))) s = word %s" k v) CPT_TBL_STACK);;

let CPT_T1_TERM mc loop exit (rs:string list) =
  let r k = List.nth rs k in
  parse_term(INLINE_FILL
   "exists f_events.
      forall e (fp:int64) b op (x:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 fp /\\
        ALL (nonoverlapping (op,320))
            [(b,1024); (word_add fp (word 112),208); (word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) @mc@ /\\
                  read PC s = word (pc + @loop@) /\\
                  read SP s = fp /\\ read @R0@ s = b /\\ read @R1@ s = word 0 /\\
                  read @R2@ s = op /\\
                  @consts@ /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add b (word(4 * i))))
                             s = x i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + @exit@) /\\
                  read @R1@ s = word 1024 /\\ read @R2@ s = word_add op (word 320) /\\
                  (!j. j < 320
                       ==> read(memory :> bytes8(word_add op (word j))) s =
                           mld_polyt1_pack x j) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events fp b op pc /\\
                     memaccess_inbounds e2
                      [b,1024; word_add fp (word 112),208; op,320] [op,320]))
             (MAYCHANGE [PC; @R1@; @R2@; @R3@; @R4@] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11;
                         Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25;
                         Q26; Q27; Q28; Q29; Q30; Q31] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(op,320)])"
   ["mc",mc; "loop",loop; "exit",exit; "consts",CPT_T1_CONST_PRE;
    "R0",r 0; "R1",r 1; "R2",r 2; "R3",r 3; "R4",r 4]);;

(*** The 16 vectors of the 64 coefficients of iteration i ***)

let CPT_LD16 =
  let lane c = if c = 0 then "x (64 * i)" else Printf.sprintf "x (64 * i + %d)" c in
  let addr m = if m = 0 then "word_add b (word (256 * i))"
               else Printf.sprintf "word_add b (word (256 * i + %d))" (16 * m) in
  let conj m = Printf.sprintf
    "read (memory :> bytes128 (%s)) s =
       word_join (word_join (%s) (%s):int64) (word_join (%s) (%s):int64)"
    (addr m) (lane(4*m+3)) (lane(4*m+2)) (lane(4*m+1)) (lane(4*m)) in
  prove(parse_term(
   "!(b:int64) (x:num->int32) i (s:armstate).
      (!j. j < 64 ==> read (memory :> bytes32 (word_add b (word (256 * i + 4 * j)))) s =
                      x (64 * i + j))
      ==> " ^ String.concat " /\\\n" (map conj (0--15))),
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o CONV_RULE(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
              el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); PTR_ADD_G;
              GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let CPT_LD16_TAC =
  SUBGOAL_THEN
   `!j. j < 64 ==> read (memory :> bytes32 (word_add b (word (256 * i + 4 * j)))) s0 =
                   (x:num->int32) (64 * i + j)`
   (fun th ->
      let ths = CONJUNCTS(MATCH_MP CPT_LD16 th) in
      let alt c d =
        let n = mk_small_numeral(c + d) in
        let eq = ARITH_RULE(subst [n,`n:num`; mk_small_numeral c,`c:num`;
                                   mk_small_numeral d,`d:num`]
                  `256 * i + n = (256 * i + c) + d`) in
        let th1 = find (fun t -> free_in n (lhand(concl t))) ths in
        GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [eq] th1 in
      MAP_EVERY ASSUME_TAC
       (ths @ map (fun (c,d) -> alt c d)
                  (allpairs (fun c d -> (c,d)) [64;128;192] [16;32;48]))) THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `256 * i + 4 * j = 4 * (64 * i + j)`] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && free_in `x:num->int32` (concl th) &&
      not(free_in `mld_polyt1_pack` (concl th)))) THEN
    UNDISCH_TAC `j < 64` THEN UNDISCH_TAC `i < 4` THEN ARITH_TAC;
    ALL_TAC];;

(*** LD4 of 32-bit elements: lane k of vector j is element 4 * k + j ***)

let CPT_DEIL_GEN = prove
 (`!z:512 word j. j < 4 ==> (word_subdeinterleave 4 32 z j : int128 =
     word_join (word_join (word_subword z ((12 + j) * 32, 32):int32) (word_subword z ((8 + j) * 32, 32):int32):int64)
               (word_join (word_subword z ((4 + j) * 32, 32):int32) (word_subword z (j * 32, 32):int32):int64))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j = 0 \/ j = 1 \/ j = 2 \/ j = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[word_subdeinterleave] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; BIT_WORD_JOIN; BIT_WORD_SUBWORD; IN_ELIM_THM; DIMINDEX_128; DIMINDEX_64; DIMINDEX_32; DIMINDEX_512] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[LET_DEF; LET_END_DEF; MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let CPT_DEILS = map (fun j ->
  CONV_RULE NUM_REDUCE_CONV
   (MP (SPECL [`z:512 word`; mk_small_numeral j] CPT_DEIL_GEN)
       (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral j,`4`))))))
  (0--3);;

let CPT_SUBWORD_OOR = prove
 (`!(x:N word) p l. dimindex(:N) <= p ==> (word_subword x (p,l):M word) = word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword] THEN
  SUBGOAL_THEN `(val (x:N word) DIV 2 EXP p) = 0` (fun th -> REWRITE_TAC[th; ARITH_RULE `0 MOD n = 0`]) THEN
  MATCH_MP_TAC DIV_LT THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP dimindex(:N)` THEN REWRITE_TAC[VAL_BOUND] THEN
  REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC);;

let CPT_OOR_CONV tm =
  match tm with
    Comb(Comb(Const("word_subword",_),x),Comb(Comb(Const(",",_),p),l)) when is_numeral p ->
      let tyN = hd(snd(dest_type(type_of x))) and tyM = hd(snd(dest_type(type_of tm))) in
      let th = SPECL [x;p;l] (INST_TYPE [tyN,`:N`;tyM,`:M`] CPT_SUBWORD_OOR) in
      let h = fst(dest_imp(concl th)) in
      MP th (EQT_ELIM((DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) h))
  | _ -> failwith "CPT_OOR_CONV";;

let CPT_NORM_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE CPT_DEILS) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV (CPT_OOR_CONV ORELSEC WORD_SIMPLE_SUBWORD_CONV)));;

(*** The bytes of iteration i of the packing ***)

let CPT_T1_IDX = prove
 (`!(x:num->int32) i k.
     k < 80 ==> mld_polyt1_pack x (80 * i + k) =
                mld_polyt1_pack (\m. x (64 * i + m)) k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyt1_pack] THEN
  SUBGOAL_THEN `(80 * i + k) DIV 5 = 16 * i + k DIV 5 /\
                (80 * i + k) MOD 5 = k MOD 5`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `k MOD 5`;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `16 * i + k DIV 5`] THEN
    MP_TAC(SPECL [`k:num`; `5`] DIVISION) THEN ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[ARITH_RULE `4 * (16 * i + q) + m = 64 * i + 4 * q + m`]]);;

let CPT_T1_SPLIT = prove
 (`!P i. (!j. j < 80 * (i + 1) ==> P j) <=>
         (!j. j < 80 * i ==> P j) /\ (!k. k < 80 ==> P(80 * i + k))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j < 80 * i` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 80 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < 80 * i) ==> 80 * i + (j - 80 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CPT_T1_BYTE_TAC =
  W(fun (asl,w) ->
    let l = lhand w in
    FIRST_ASSUM(fun th -> if lhand(concl th) = l then GEN_REWRITE_TAC LAND_CONV [th]
                          else NO_TAC)) THEN
  W(fun (asl,w) ->
    let n = rand(rand w) in
    let k = if is_binary "+" n then rand n else `0` in
    let th = MP (SPECL [`x:num->int32`; `i:num`; k] CPT_T1_IDX)
                (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (k,`80`)))) in
    GEN_REWRITE_TAC RAND_CONV [REWRITE_RULE[ADD_CLAUSES] th]) THEN
  REWRITE_TAC[mld_polyt1_pack] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  APP_BLAST_TAC `x:num->int32`;;

(*** A byte of a value built by word_or, word_and and word_join: pushed down ***)
(*** to the subwords of the operands (as W1P_EXTRACT_CONV of arm-C)          ***)

let rec CPT_EXTRACT_CONV tm =
  let isop name t = try fst(dest_const(fst(strip_comb t))) = name
                    with Failure _ -> false in
  if not(isop "word_subword" tm) then REFL tm else
  let x = lhand tm in
  if isop "word_or" x then
    (REWR_CONV WORD_SUBWORD_OR THENC BINOP_CONV CPT_EXTRACT_CONV) tm
  else if isop "word_and" x then
    (REWR_CONV WORD_SUBWORD_AND THENC BINOP_CONV CPT_EXTRACT_CONV) tm
  else
    (try (WORD_SIMPLE_SUBWORD_CONV THENC
          (fun t -> if isop "word_subword" t && not(t = tm)
                    then CPT_EXTRACT_CONV t else REFL t)) tm
     with Failure _ -> REFL tm);;

let CPT_BYTES_EXTRACT_TAC (base:term) =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && free_in base (lhand c) &&
       can (term_match [] `read (memory :> bytes8 a) s = x`) c
    then CONV_RULE(RAND_CONV(DEPTH_CONV CPT_OOR_CONV THENC CPT_EXTRACT_CONV)) th
    else th);;

let CPT_STEP_NORM_TAC n =
  let sv = mk_var("s"^string_of_int n,`:armstate`) in
  RULE_ASSUM_TAC(fun th ->
    if free_in sv (concl th)
    then CONV_RULE(DEPTH_CONV (CPT_OOR_CONV ORELSEC WORD_SIMPLE_SUBWORD_CONV))
          (REWRITE_RULE (PTR_ADD_G::CPT_DEILS) th)
    else th);;

let CPT_T1_LOOP mc exec loop exit (rs:string list) =
  let r k = List.nth rs k in
  let tm = CPT_T1_TERM mc loop exit rs in
  let inv = parse_term(INLINE_FILL
   "\\i s. read SP s = fp /\\ read @R0@ s = b /\\ read @R1@ s = word(256 * i) /\\
          read @R2@ s = word_add op (word(80 * i)) /\\
          @consts@ /\\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   (x:num->int32) j) /\\
          (!j. j < 80 * i
               ==> read(memory :> bytes8(word_add op (word j))) s =
                   mld_polyt1_pack x j)"
   ["R0",r 0; "R1",r 1; "R2",r 2; "consts",CPT_T1_CONST_PRE]) in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (b:int64) (op:int64) (pc:num).
      APPEND (f_ev_epil fp b op pc)
       (APPEND (ENUMERATEL 4 (\i. f_ev_loop fp b op pc i)) (f_ev_prol fp b op pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `b:int64`;
                       `op:int64`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `4` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN CPT_LD16_TAC THEN
    MAP_EVERY (fun k -> ARM_STEPS_TAC exec [k] THEN CPT_STEP_NORM_TAC k)
              (1--95) THEN
    WIDE_STORE_SPLIT_TAC `op:int64` 8 THEN CPT_BYTES_EXTRACT_TAC `op:int64` THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[CPT_T1_SPLIT] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
        REWRITE_TAC[ADD_CLAUSES] THEN
        REPEAT CONJ_TAC THEN CPT_T1_BYTE_TAC THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The five lemmas of the row of mld_compute_pack_t0_t144 and _t187 (the     *)
(* same code): the sum (from in_poly_add to loop2, 237 instructions) of t at *)
(* fp + 1344 and s2 at fp + 320, with -q at fp + 96; the reduction (loop2)   *)
(* and the addition of q (loop3) of t at x24 = fp + 1344, with q in w27;     *)
(* power2round (loop4) of t at x24 into t1 at x26 = fp + 320; the packing    *)
(* of t1 (loop5) to x9.                                                      *)
(* ------------------------------------------------------------------------- *)

let CPT_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

let CPT_ADD_TERM fn =
  CPT_ADD_STMT CPT_MC (fn ^ "_in_poly_add") (fn ^ "_loop2") 1344 320 96
   ("X8"::INLINE_MAP_QMODS);;

let CPT_ADD_LEMMA fn =
  CPT_ADD_PROVE (CPT_ADD_TERM fn)
   (INLINE_LOOP_EXEC (fn ^ "_in_poly_add") (fn ^ "_loop2")) 1344 320
   ((layout (fn ^ "_loop2") - layout (fn ^ "_in_poly_add")) / 4);;

let CPT_LOOP_LEMMA gen fn loop =
  let l = fn ^ "_" ^ loop and e = fn ^ "_" ^ loop ^ "_exit" in
  gen (INLINE_LOOP_EXEC l e) l e;;

let CPT_RED_LEMMA fn =
  CPT_LOOP_LEMMA (fun ex l e ->
    INLINE_REDUCE_LOOP "9" CPT_MC ex l e 0
     ["X9";"X24";"X8";"Q0";"Q1";"Q2";"Q4";"Q3";"Q5"]) fn "loop2";;

let CPT_CADDQ_LEMMA fn =
  CPT_LOOP_LEMMA (fun ex l e ->
    INLINE_CADDQ_LOOP CPT_MC ex l e ["X9";"X24";"X8";"X10";"X11";"X27"])
   fn "loop3";;

let CPT_P2R_LEMMA fn =
  CPT_LOOP_LEMMA (fun ex l e ->
    CPT_P2R_LOOP CPT_MC ex l e ["X9";"X24";"X8";"X10";"X26";"Q6";"Q7"])
   fn "loop4";;

let CPT_T1_LEMMA fn =
  CPT_LOOP_LEMMA (fun ex l e ->
    CPT_T1_LOOP CPT_MC ex l e ["X26";"X8";"X9";"X10";"X11"]) fn "loop5";;

(*** The pointer that MADD computes, x + k * i ***)

let CPT_MADD = prove
 (`!(x:int64) i k. word (val x + val (word i:int64) * k):int64 = word_add x (word (k * i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_MUL; WORD_VAL] THEN
  CONV_TAC WORD_RULE);;

(*** The inputs of the lemmas whose addresses are fp + (off + 4 * i), as   ***)
(*** the simulation forms them with fp = stackpointer + b:                 ***)
(*** stackpointer + (b + off + 4 * i); and the folding of the outputs back ***)
(*** to stackpointer + N + 4 * i (as VI44_UNFOLD_TAC and VI44_FOLD_TAC of  ***)
(*** verify_internal_44_proof.ml)                                          ***)

let CPT_UNFOLD_TAC b off =
  let n = b + off in
  let eq = ARITH_RULE(parse_term(Printf.sprintf
    "!i. %d + 4 * i = %d + %d + 4 * i" n b off)) in
  let pat = parse_term(Printf.sprintf
    "word_add (stackpointer:int64) (word (%d + 4 * i))" n) in
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_forall c && can (find_term (fun t -> can (term_match [] pat) t)) c
      then REWRITE_RULE[eq] th else fail()) asl in
    MAP_EVERY ASSUME_TAC ths);;

let CPT_FOLD_CONV tm =
  match tm with
    Comb(Const("word",_),Comb(Comb(Const("+",_),m),
           Comb(Comb(Const("+",_),n),t))) when is_numeral m && is_numeral n ->
      let th = SPECL [m;n;t] ADD_ASSOC in
      CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV NUM_ADD_CONV))) (AP_TERM (rator tm) th)
  | _ -> failwith "CPT_FOLD_CONV";;

let CPT_FOLD_TAC =
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  RULE_ASSUM_TAC(fun th ->
    if is_forall(concl th) && free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV CPT_FOLD_CONV) th else th);;

(*** The restored d8-d15 through the 128-bit registers ***)

let CPT_ZX128 = WORD_BLAST `!x:int64. word_zx(word_zx x:int128):int64 = x`;;

(* ------------------------------------------------------------------------- *)
(* mld_compute_pack_t0_t165: the unpacking of row i of s2 (eta = 4, 128      *)
(* bytes at a = s2 + 128 i, with s2 spilled at F + 104) into the buffer at   *)
(* F + 320 (with ST2 through x24 = F + 320, x26 = F + 832, x19 = F + 960,    *)
(* x27 = F + 1088, x20 = F + 1216) and the sum with the polynomial of t at   *)
(* F + 1344, straight-line code (from after the call of the inverse NTT to   *)
(* loop2, 415 instructions) that also sets x8 = 0 and q5 = 2^22 in each      *)
(* lane for the reduction that follows.                                      *)
(* ------------------------------------------------------------------------- *)

let CPT65_ADD_TERM fn =
  parse_term(INLINE_FILL
   "exists f_events.
      forall e (fp:int64) s2 k a (x:num->int32) (b:num->byte) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 fp /\\ word_add s2 (word(128 * k)) = a /\\
        nonoverlapping (word_add fp (word 320),2048) (word pc,libmldsa_size) /\\
        nonoverlapping (word_add fp (word 320),2048) (a,128)
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) @mc@ /\\
                  read PC s = word (pc + @start@) /\\
                  read SP s = fp /\\ read X23 s = word k /\\
                  read X24 s = word_add fp (word 320) /\\
                  read X26 s = word_add fp (word 832) /\\
                  read X19 s = word_add fp (word 960) /\\
                  read X27 s = word_add fp (word 1088) /\\
                  read X20 s = word_add fp (word 1216) /\\
                  read (memory :> bytes64 (word_add fp (word 104))) s = s2 /\\
                  (!j. j < 128
                       ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add fp (word(1344 + 4 * i))))
                             s = x i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + @stop@) /\\
                  read X8 s = word 0 /\\
                  read Q5 s = word 0x00400000004000000040000000400000 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add fp (word(1344 + 4 * i))))
                             s = mld_poly_add x (mld_polyeta_unpack_4 b) i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events fp s2 k pc /\\
                     memaccess_inbounds e2
                      [word_add fp (word 104),8; a,128; word_add fp (word 320),2048]
                      [word_add fp (word 320),2048]))
             (MAYCHANGE [PC; X8; X9; X10; X11] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add fp (word 320),2048)])"
   ["mc",CPT_MC; "start",fn ^ "_after_mldsa_poly_invntt_tomont";
    "stop",fn ^ "_loop2"]);;

(*** The 16 bytes of b at a + 16 m as a 128-bit word of the bytes ***)

let CPT_B128_FACT m =
  let hth = ASSUME `!j. j < 128 ==> read (memory :> bytes8 (word_add a (word j))) s0 = (b:num->byte) j` in
  let insts = map (fun k ->
    let j = 16 * m + k in
    let th = MP (SPEC (mk_small_numeral j) hth)
                (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral j,`128`)))) in
    REWRITE_RULE[WORD_ADD_0] th) (0--15) in
  let lhs = if m = 0 then `read (memory :> bytes128 (a:int64)) s0` else
    parse_term(Printf.sprintf "read (memory :> bytes128 (word_add (a:int64) (word %d))) s0" (16 * m)) in
  let conv = REWRITE_CONV[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 3 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          PTR_ADD_G; GSYM ADD_ASSOC] THENC
             DEPTH_CONV NUM_ADD_CONV in
  REWRITE_RULE (WORD_ADD_0 :: insts) (conv lhs);;

let CPT_B128_TAC =
  FIRST_ASSUM(fun skf ->
    if can (term_match [] `!j. j < 128 ==> read (memory :> bytes8 (word_add a (word j))) s0 = (b:num->byte) j`) (concl skf)
    then MAP_EVERY (fun m -> ASSUME_TAC (PROVE_HYP skf (CPT_B128_FACT m))) (0--7)
    else NO_TAC);;

(*** Bit-blasting with the values x k and b j as variables ***)

let CPT_BLAST2_TAC (fs:term list) =
  W(fun (asl,w) ->
    let apps = setify (find_terms (fun t -> is_comb t && mem (rator t) fs) w) in
    let vs = map (fun t -> genvar(type_of t)) apps in
    let th = BITBLAST_RULE (subst (zip vs apps) w) in
    ACCEPT_TAC (INST (zip apps vs) th));;

let CPT_SHL7 = prove
 (`!(s2:int64) i. word_add s2 (word_shl (word i) 7) = word_add s2 (word(128 * i))`,
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_BLAST `!x:int64. word_shl x 7 = word_mul x (word 128)`] THEN
  REWRITE_TAC[GSYM WORD_MUL] THEN AP_TERM_TAC THEN ARITH_TAC);;

(*** The input row of s2 does not overlap the buffers of the frame ***)

let CPT_NOV_ROW = prove
 (`!(p:int64) (q:int64) n m i k.
     nonoverlapping (p,5312) (q,m) /\ n + 2048 <= 5312 /\ k * i + k <= m
     ==> nonoverlapping (word_add p (word n),2048) (word_add q (word(k * i)),k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NONOVERLAPPING_SUBREGIONS THEN
  MAP_EVERY EXISTS_TAC [`p:int64`; `5312`; `q:int64`; `m:num`] THEN
  ASM_REWRITE_TAC[contained; contained_modulo] THEN CONJ_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THENL
   [EXISTS_TAC `n + j:num`; EXISTS_TAC `k * i + j:num`] THEN
  (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; CONG; MOD_MOD_REFL] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* poly_reduce as mld_compute_pack_t0_t165 has it (13 instructions): as the  *)
(* kind "9" of INLINE_REDUCE_LOOP, but with -q put in each lane of q4 from   *)
(* w28 by DUP in every iteration:                                            *)
(*   add x9, x25, x8; dup v4.4s, w28; add x8, x8, #0x20; ldp q0, q1, [x9];  *)
(*   cmp x8, #0x400; ...; mla v0.4s, v2.4s, v4.4s; ...; stp q0, q1, [x9]     *)
(* ------------------------------------------------------------------------- *)

let CPT_REDDUP_TERM mc loop exit =
  parse_term(INLINE_FILL
   "exists f_events.
      forall e a (x:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) @mc@ /\\
                  read PC s = word (pc + @loop@) /\\
                  read X25 s = a /\\ read X8 s = word 0 /\\
                  read X28 s = word 4286586879 /\\
                  read Q5 s = word 0x00400000004000000040000000400000 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + @exit@) /\\
                  read X8 s = word 1024 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_reduce x i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2 [a,1024] [a,1024]))
             (MAYCHANGE [PC; X9; X8] ,, MAYCHANGE [Q0; Q1; Q2; Q3; Q4] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024)])"
   ["mc",mc; "loop",loop; "exit",exit]);;

let CPT_REDDUP_LOOP mc exec loop exit =
  let tm = CPT_REDDUP_TERM mc loop exit in
  let inv =
   `\i s. read X25 s = a /\ read X8 s = word(32 * i) /\
          read X28 s = word 4286586879 /\
          read Q5 s = word 0x00400000004000000040000000400000 /\
          (!j. 8 * i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   (x:num->int32) j) /\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_reduce32 (x j))` in
  let bases = INLINE_BASES "9" 0 in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_epil a pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `x:num->int32`;
                       `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; mld_poly_reduce;
              fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; CONJUNCT1 LT; LE_0;
                WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CPT_VEC8_BODY_TAC exec bases [`mld_reduce32`] 12 THEN
    ARM_STEPS_TAC exec [13] THEN
    CPT_VEC8_FINAL_TAC (INLINE_LANE_ADDRS bases)
      ((REWRITE_TAC[INLINE_REDUCE32_LANE] THEN NO_TAC) ORELSE
       (REWRITE_TAC[GSYM INLINE_REDUCE32_LANE] THEN APP_BLAST_TAC `x:num->int32`));

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC]);;

(*** The proof of CPT65_ADD_TERM: the inputs as 128-bit words of their lanes ***)
(*** or bytes, the simulation with the vector values normalized after each  ***)
(*** step, and each output lane by bit-blasting on its inputs               ***)

(*** The two halves of a 256-bit store (ST2), so that the 128-bit loads ***)
(*** that read them back find their values                                ***)

let CPT_SPLIT256 = prove
 (`!(a:int64) (v:256 word) (s:armstate).
     read (memory :> bytes256 a) s = v
     ==> read (memory :> bytes128 a) s = word_subword v (0,128) /\
         read (memory :> bytes128 (word_add a (word 16))) s =
         word_subword v (128,128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[]);;

let CPT65_STEP_NORM_TAC n =
  let sv = mk_var("s"^string_of_int n,`:armstate`) in
  RULE_ASSUM_TAC(fun th ->
    if free_in sv (concl th)
    then CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)
          (REWRITE_RULE [CPT_SHL7; PTR_ADD_G] th)
    else th) THEN
  W(fun (asl,w) ->
    let st256 = mapfilter (fun (_,th) ->
      let c = concl th in
      if free_in sv c &&
         can (term_match [] `read (memory :> bytes256 a) s = x`) c
      then th else fail()) asl in
    let lhss = mapfilter (fun (_,th) -> lhs(concl th)) asl in
    MAP_EVERY (fun th ->
      let hs = CONJUNCTS
       (CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
         (MATCH_MP CPT_SPLIT256 th)) in
      MAP_EVERY (fun h -> if mem (lhs(concl h)) lhss then ALL_TAC
                          else ASSUME_TAC h) hs) st256);;

let CPT65_LANE_TAC =
  REWRITE_TAC[mld_polyeta_unpack_4] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CPT_BLAST2_TAC [`x:num->int32`; `b:num->byte`];;

(*** Before the outputs are split into lanes: drop the facts about the     ***)
(*** vector registers and the unpacked s2 below F + 1344, which the result ***)
(*** does not need                                                         ***)

let CPT65_CLEAN_TAC =
  let useless th =
    let c = concl th in
    is_eq c &&
    (match lhs c with
       Comb(Comb(Const("read",_),Const(q,_)),_) ->
         String.length q > 1 && q.[0] = 'Q' && q <> "Q5"
     | Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),Comb(_,addr))),_) ->
         (try let b,off = dest_binop `word_add:int64->int64->int64` addr in
              b = `fp:int64` &&
              (let n = dest_small_numeral(rand off) in n < 1344)
          with Failure _ -> false)
     | _ -> false) in
  REPEAT(FIRST_X_ASSUM(fun th -> if useless th then ALL_TAC else NO_TAC));;

let CPT65_ADD_PROVE fn =
  let st = fn ^ "_after_mldsa_poly_invntt_tomont" and sp = fn ^ "_loop2" in
  let n = (layout sp - layout st) / 4 in
  let exec = INLINE_LOOP_EXEC st sp in
  prove(CPT65_ADD_TERM fn,
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (s2:int64) (k:num) (pc:num). f_ev_add fp s2 k pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst exec] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  INLINE_MAP_INPUT_TAC 1344 `x:num->int32` THEN CPT_B128_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `a:int64`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PTR_ADD_G]) THEN
  MAP_EVERY (fun k -> ARM_STEPS_TAC exec [k] THEN CPT65_STEP_NORM_TAC k) (1--n) THEN
  CPT65_CLEAN_TAC THEN
  WIDE_STORE_SPLIT_TAC `fp:int64` 32 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    ASM_REWRITE_TAC[mld_poly_add] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REPEAT CONJ_TAC THEN CPT65_LANE_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
