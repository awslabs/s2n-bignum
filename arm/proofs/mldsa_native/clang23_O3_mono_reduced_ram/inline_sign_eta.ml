(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* polyeta_unpack (eta = 2) as clang 23 -O3 has inlined it into the z loop   *)
(* and the row loop of mldsa44_signature_internal (and mldsa87): s1_i or     *)
(* s2_j, 96 bytes at a + k in the secret key (k = 96 i), unpacked into a     *)
(* polynomial r in the frame. As in mldsa44_polyeta_unpack (see             *)
(* inline_polyeta.ml), the code first tests whether the input and the output *)
(* overlap: if not, a straight-line vector block unpacks the first 128       *)
(* coefficients and a scalar loop the other 128 (16 iterations from group    *)
(* 16); otherwise the scalar loop does all 256 (32 iterations from group 0). *)
(* The block is the one of the function with another schedule and other     *)
(* registers, so it is simulated in full with the normalization of           *)
(* inline_polyeta.ml after each step.                                        *)
(*                                                                           *)
(* SI_ETA_L2_TERM / SI_ETA_L2_PROVE: the scalar loop from group g0, with the *)
(* pointer register x8 = a + 3 g, the counter x9 = 32 g + 16, the offset     *)
(* register (k) and the output register (r) as parameters.                   *)
(*                                                                           *)
(* SI_ETA_TERM / SI_ETA_PROVE: the whole region, from the head of the z or   *)
(* row loop, for polynomial i (i < L) at a + 96 i with a read from the frame *)
(* and the output at F + roff. Its events are those of one of the two paths, *)
(* selected by the overlap test OV as the code computes it. The proof names  *)
(* the input pointer ap = a + 96 i (the loads of the block need their facts *)
(* at ap + k), splits on OV, simulates the block (about 5 minutes), proves   *)
(* the 128 lanes of its stores by bit-blasting, and calls the loop lemmas.   *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_polyeta.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_pack.ml";;

(* ------------------------------------------------------------------------- *)
(* The scalar loop: 3 bytes and 8 words per iteration, groups g0 to 31.      *)
(* ------------------------------------------------------------------------- *)

let SI_ETA_L2_TERM mc loop exit g0 (kreg,rreg) =
  let n = 32 - g0 in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (r:int64) (a:int64) k (b:num->byte) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (word_add r (word %d),%d))
            [(word pc,libmldsa_size); (word_add a (word k),96)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read X8 s = %s /\\
                  read X9 s = word %d /\\
                  read %s s = word k /\\ read %s s = r /\\
                  read X24 s = word 2 /\\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word(k + j)))) s = b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  (!j. %sj < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                           mld_polyeta_unpack_2 b j) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events r a k pc /\\
                     memaccess_inbounds e2 [word_add a (word k),96]
                                           [word_add r (word %d),%d]))
             (MAYCHANGE [PC; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17;
                         X18] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add r (word %d),%d)])"
   (32 * g0) (32 * n) mc loop
   (if g0 = 0 then "a" else Printf.sprintf "word_add a (word %d)" (3 * g0))
   (32 * g0 + 16) kreg rreg exit
   (if g0 = 0 then "" else Printf.sprintf "%d <= j /\\ " (8 * g0))
   (32 * g0) (32 * n) (32 * g0) (32 * n));;


(* ------------------------------------------------------------------------- *)
(* The whole inlined polyeta_unpack, from the head of the z or row loop to   *)
(* the end of the scalar loop: polynomial i of s1 or s2 (its 96 bytes at     *)
(* a + 96 i, a read from the frame at F + aslot) into r = F + roff. The      *)
(* parameters (record eta_inst): the labels, the registers of the index i    *)
(* and of the offset 96 i, the output register, the slot of a, the extra     *)
(* precondition (the end of r for the overlap test, saved registers) and     *)
(* postcondition, the spill area, the general registers written.            *)
(* ------------------------------------------------------------------------- *)

type eta_inst =
  { et_start : string; et_stop : string; et_loop : string;
    et_ireg : string; et_kreg : string; et_rreg : string; et_roff : int;
    et_aslot : int; et_l : int;
    et_pre : string; et_post : string; et_bind : string;
    et_spill : (int * int) list; et_mods : string list };;

let SI_ETA_TERM mc p =
  let regs = (p.et_roff,1024) :: p.et_spill in
  let rl = String.concat "; " (map (fun (oo,l) ->
             Printf.sprintf "(word_add fp (word %d),%d)" oo l) regs) in
  let ml = String.concat "; " (map (fun (oo,l) ->
             Printf.sprintf "word_add fp (word %d),%d" oo l) regs) in
  let mcs = String.concat "; " (map (fun (oo,l) ->
             Printf.sprintf "memory :> bytes(word_add fp (word %d),%d)" oo l) regs) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (fp:int64) (a:int64) i (b:num->byte) %s pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 fp /\\ i < %d /\\
        ALL (nonoverlapping (word_add a (word (96 * i)),96)) [%s] /\\
        ALL (nonoverlapping (word pc,libmldsa_size)) [%s]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read SP s = fp /\\
                  read %s s = word i /\\ read %s s = word (96 * i) /\\
                  read %s s = word_add fp (word %d) /\\
                  read X24 s = word 2 /\\
                  read (memory :> bytes64 (word_add fp (word %d))) s = a /\\
                  read (memory :> bytes128 (word_add fp (word 288))) s =
                    word 0xffffff07ffffff06ffffff05ffffff04 /\\
                  read (memory :> bytes128 (word_add fp (word 304))) s =
                    word 0xffffff03ffffff02ffffff01ffffff00 /\\ %s
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word(96 * i + j)))) s =
                           b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ %s
                  (!j. j < 256
                       ==> read(memory :> bytes32(word_add fp (word(%d + 4 * j)))) s =
                           mld_polyeta_unpack_2 b j) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events fp a i pc /\\
                     memaccess_inbounds e2
                      [word_add a (word (96 * i)),96; word_add fp (word 56),%d;
                       word (pc + mldsa44_signature_internal_consts),128]
                      [%s]))
             (MAYCHANGE [PC; %s] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12;
                         Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                         Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [%s])"
   p.et_bind p.et_l rl rl mc p.et_start
   p.et_ireg p.et_kreg p.et_rreg p.et_roff p.et_aslot p.et_pre
   p.et_stop p.et_post p.et_roff (p.et_roff + 1024 - 56) ml
   (String.concat "; " p.et_mods) mcs);;

(*** The outputs of the groups g0 to g0 + i + 1, from those up to g0 + i ***)

let SI_ETA_OUT_SPLIT = prove
 (`!P (a:num) n. a <= n
     ==> ((!j. a <= j /\ j < n + 8 ==> P j) <=>
          (!j. a <= j /\ j < n ==> P j) /\ (!m. m < 8 ==> P(n + m)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_CASES_TAC `j < n:num` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < n) ==> n + (j - n) = j`]]);;

(*** The loads of group g0 + i, at the addresses that the simulation forms ***)
(*** from x8 + k (two forms for the offsets 1 and 2)                      ***)

let SI_ETA_L2_INPUT_TAC g0 =
  let gi = if g0 = 0 then "3 * i" else Printf.sprintf "(3 * i + %d)" (3 * g0) in
  let facts = map (fun m ->
    let v = if 3 * g0 + m = 0 then "(b:num->byte) (3 * i)"
            else Printf.sprintf "(b:num->byte) (3 * i + %d)" (3 * g0 + m) in
    if m = 0 then
      Printf.sprintf "read (memory :> bytes8 (word_add a (word (%s + k)))) s0 = %s" gi v
    else
      Printf.sprintf "read (memory :> bytes8 (word_add a (word (%s + k + %d)))) s0 = %s"
        gi m v) (0--2) in
  MAP_EVERY (fun f ->
    SUBGOAL_THEN (parse_term f) ASSUME_TAC THENL
     [W(fun (asl,w) ->
        let addr = rand(rand(lhand(lhs w))) in
        let j = rand(rhs w) in
        let tgt = mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
                          mk_comb(`word:num->int64`,
                            mk_binop `(+):num->num->num` `k:num` j)) in
        SUBST1_TAC(WORD_RULE(mk_eq(addr,tgt)))) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && free_in `b:num->byte` (concl th) &&
        free_in `k:num` (concl th))) THEN
      UNDISCH_TAC (parse_term(Printf.sprintf "i < %d" (32 - g0))) THEN ARITH_TAC;
      ALL_TAC]) facts;;

let SI_ETA_X12_EQ g0 = WORD_RULE (parse_term(Printf.sprintf
  "word_add (r:int64) (word (32 * i + %d)) =
   word_add (word_add r (word (32 * i%s))) (word 16)"
  (32 * g0 + 16) (if g0 = 0 then "" else Printf.sprintf " + %d" (32 * g0))));;

(*** The loop test as LOOP_TEST_TAC leaves it, e + c1 = c2, as i + 1 = n ***)

let SI_ETA_TEST_TAC n =
  W(fun (asl,w) ->
    let tms = find_terms (fun t -> is_eq t && is_numeral(rhs t) &&
                 (try is_numeral(rand(lhs t)) &&
                      fst(dest_const(rator(rator(lhs t)))) = "+"
                  with Failure _ -> false)) w in
    MAP_EVERY (fun t ->
      let ilt = parse_term(Printf.sprintf "i < %d" n) in
      let th = prove(mk_imp(ilt,mk_eq(t,parse_term(Printf.sprintf "~(i + 1 < %d)" n))),
                     ARITH_TAC) in
      REWRITE_TAC[MP th (ASSUME ilt)]) (setify tms));;

let SI_ETA_L2_FINAL_TAC g0 =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN SI_ETA_TEST_TAC (32 - g0) THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(W(fun (_,w) -> if is_eq w && type_of(lhs w) = `:int64`
                     then CONV_TAC WORD_RULE else NO_TAC) THEN NO_TAC) THEN
  TRY((if g0 = 0 then
        REWRITE_TAC[CHUNK_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC[mld_polyeta_unpack_2]
      else
        REWRITE_TAC[ARITH_RULE (parse_term(Printf.sprintf
          "8 * (i + 1) + %d = (8 * i + %d) + 8" (8 * g0) (8 * g0)))] THEN
        SIMP_TAC[SI_ETA_OUT_SPLIT; ARITH_RULE (parse_term(Printf.sprintf
          "%d <= 8 * i + %d" (8 * g0) (8 * g0)))] THEN
        ASM_REWRITE_TAC[] THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC[mld_polyeta_unpack_2] THEN
        REWRITE_TAC[ARITH_RULE (parse_term(Printf.sprintf
          "(8 * i + %d) + m = 8 * (i + %d) + m" (8 * g0) g0))]) THEN
      SIMP_TAC[DIVMOD_CHUNK; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_ASSOC] THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
      RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(REWRITE_CONV[PTR_ADD_G; GSYM ADD_ASSOC]) THENC
                               DEPTH_CONV NUM_ADD_CONV)) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN APP_BLAST_TAC `b:num->byte` THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let SI_ETA_L2_INV g0 (kreg,rreg) =
  Printf.sprintf
   "\\i s. read X8 s = word_add a (word (3 * i%s)) /\\
          read X9 s = word (32 * i + %d) /\\
          read %s s = word k /\\ read %s s = r /\\ read X24 s = word 2 /\\
          (!j. j < 96
               ==> read(memory :> bytes8(word_add a (word(k + j)))) s =
                   (b:num->byte) j) /\\
          (!j. %sj < 8 * i%s
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   mld_polyeta_unpack_2 b j)"
   (if g0 = 0 then "" else Printf.sprintf " + %d" (3 * g0)) (32 * g0 + 16) kreg rreg
   (if g0 = 0 then "" else Printf.sprintf "%d <= j /\\ " (8 * g0))
   (if g0 = 0 then "" else Printf.sprintf " + %d" (8 * g0));;

let SI_ETA_L2_PROVE mc loop exit g0 regs =
  let n = 32 - g0 in
  let ex = INLINE_LOOP_EXEC loop exit in
  prove(SI_ETA_L2_TERM mc loop exit g0 regs,
  CONCRETIZE_F_EVENTS_TAC
   (parse_term(Printf.sprintf
     "\\(r:int64) (a:int64) (k:num) (pc:num).
        APPEND (f_ev_epil r a k pc)
         (APPEND (ENUMERATEL %d (\\i. f_ev_loop r a k pc i))
                 (f_ev_prol r a k pc)) :(uarch_event)list" n)) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `r:int64`; `a:int64`; `k:num`;
                       `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst ex] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (mk_small_numeral n) (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) (parse_term(SI_ETA_L2_INV g0 regs)) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `!n j. ~(n <= j /\ j < n)`; WORD_ADD_0; CONJUNCT1 LT] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    SI_ETA_L2_INPUT_TAC g0 THEN
    ARM_STEPS_TAC ex (1--2) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SI_ETA_X12_EQ g0]) THEN
    ARM_STEPS_TAC ex (3--44) THEN
    SI_ETA_L2_FINAL_TAC g0;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The proof of the region: the two paths of the overlap test (OV, as the    *)
(* simulation gives it with ap = a + 96 i), V the vector block and the loop *)
(* from group 16, S the loop from group 0. The step numbers of an instance:  *)
(* the adrp steps, the madd that computes ap for the test, the branch, the   *)
(* step that computes ap for the loads, the last step of the vector block,   *)
(* and the calls of the loop in the two paths.                               *)
(* ------------------------------------------------------------------------- *)

type eta_steps =
  { es_adrp : int list; es_madd : int; es_branch : int; es_ap : int;
    es_block_end : int; es_call_v : int; es_call_s : int };;

let SI_ETA_OV_STR roff =
  Printf.sprintf
   "val (word_add (a:int64) (word (96 * i))) < val (word_add (fp:int64) (word %d)) /\\
    val (word_add fp (word %d)) < val (word_add (word_add a (word (96 * i))) (word 96))"
   (roff + 1024) roff;;

let SI_ETA_TEMPLATE roff =
  parse_term(Printf.sprintf
   "\\(fp:int64) (a:int64) (i:num) (pc:num).
      if %s
      then APPEND (f_ev_l2S fp a i pc) (f_ev_proS fp a i pc)
      else APPEND (f_ev_l2V fp a i pc) (f_ev_proV fp a i pc)
      :(uarch_event)list" (SI_ETA_OV_STR roff));;

let SI_ETA_MADD = prove
 (`!(a:int64) i. i < 2 EXP 64
     ==> word (val a + val (word i:int64) * 96):int64 = word_add a (word (96 * i))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  REWRITE_TAC[WORD_ADD; WORD_VAL] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let SI_ETA_CF = prove
 (`!(u:int64) (v:int64) (w:int64) (x:int64).
     (if val u < val v then &(val w) - &(val x):int = &(val(word_sub w x)) else T) <=>
     ~(val u < val v /\ val w < val x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_64] THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LE] THEN
  TRY(ASM_SIMP_TAC[INT_OF_NUM_SUB] THEN NO_TAC) THEN
  REWRITE_TAC[INT_ARITH `a - b:int = c <=> a = c + b`; INT_OF_NUM_ADD;
              INT_OF_NUM_EQ] THEN
  ASM_ARITH_TAC);;

(*** Rewriting the assumptions with ap = a + 96 i, keeping the equation ***)

let SI_ETA_AB asl = snd(find (fun (_,th) ->
  concl th = `word_add (a:int64) (word (96 * i)) = ap`) asl);;

let SI_ETA_IS_REG t =
  try let l,_ = dest_eq t in
      (match l with
         Comb(Comb(Const("read",_),Const(r,_)),_) -> true
       | _ -> false)
  with Failure _ -> false;;

let SI_ETA_AP_TAC = W(fun (asl,w) ->
  let ab = SI_ETA_AB asl in
  RULE_ASSUM_TAC(fun th -> if SI_ETA_IS_REG(concl th) || is_iff(concl th)
                           then REWRITE_RULE[ab] th else th));;

(*** Copies of the nonoverlapping facts about a + 96 i in terms of ap ***)

let SI_ETA_NOV_AP_TAC = W(fun (asl,w) ->
  let ab = SI_ETA_AB asl in
  let novs = filter (fun (_,th) -> free_in (lhs(concl ab)) (concl th) &&
                       not(concl th = concl ab) &&
                       not(is_forall(concl th))) asl in
  MAP_EVERY (fun (_,th) -> ASSUME_TAC(REWRITE_RULE[ab] th)) novs);;

let SI_ETA_LANES_TAC roff sname =
  let is_store t =
    try let l,_ = dest_eq t in
        (match l with
           Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),Comb(Const(bn,_),addr))),_)
             when bn = "bytes128" || bn = "bytes256" ->
             (match addr with
                Comb(Comb(Const("word_add",_),f),Comb(Const("word",_),n)) ->
                  f = `fp:int64` && is_numeral n &&
                  let v = dest_small_numeral n in v >= roff && v < roff + 512
              | _ -> false)
         | _ -> false)
    with _ -> false in
  W(fun (asl,w) ->
    let sts = filter (fun (_,th) -> is_store(concl th) &&
                        free_in (parse_term sname) (concl th)) asl in
    MAP_EVERY (fun (_,th) ->
      let th1 = REWRITE_RULE ETA_UNSPLIT th in
      let th2 = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th1 in
      let th3 = map (CONV_RULE(DEPTH_CONV (ETA_OOR_CONV ORELSEC
                                           WORD_SIMPLE_SUBWORD_CONV)))
                    (CONJUNCTS th2) in
      MAP_EVERY ASSUME_TAC th3) sts);;

let SI_ETA_LANE_TAC =
  CONV_TAC(LAND_CONV(DEPTH_CONV NUM_RED_CONV)) THEN
  W(fun (asl,w) ->
    let l = lhs w in
    FIRST_ASSUM(fun th -> if lhs(concl th) = l then REWRITE_TAC[th] else NO_TAC)) THEN
  REWRITE_TAC[mld_polyeta_unpack_2] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN APP_BLAST_TAC `b:num->byte`;;

(*** The start: the lemmas of the loop, the input at ap, the constants and ***)
(*** the loads of the block, and the steps to the branch of the test       ***)

let SI_ETA_SETUP_TAC p st ex (l16,l0) =
  ASSUME_CALLEE_SAFETY_TAILED_TAC l16 "H16" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC l0 "H0" THEN
  CONCRETIZE_F_EVENTS_TAC (SI_ETA_TEMPLATE p.et_roff) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   ([`e:(uarch_event)list`; `fp:int64`; `a:int64`; `i:num`; `b:num->byte`] @
    (if p.et_bind = "" then [] else [parse_term p.et_bind]) @ [`pc:num`]) THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; fst ex] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN
   `!j. j < 96 ==> read (memory :> bytes8 (word_add (word_add a (word (96 * i))) (word j))) s0 =
                   (b:num->byte) j` MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[WORD_RULE `word_add (word_add (a:int64) (word (96 * i))) (word j) =
                           word_add a (word (96 * i + j))`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `ap = word_add (a:int64) (word (96 * i))` THEN DISCH_TAC THEN
  SI_ETA_NOV_AP_TAC THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(fun a ->
    if concl a = hd(hyp (UNDISCH th)) then ASSUME_TAC(MP th a) else NO_TAC))
   (ETA_CONST_FACTS "mldsa44" `s0:armstate`) THEN
  MAP_EVERY (fun (sz,k) ->
    let th = INST [`ap:int64`,`a:int64`] (ETA_LD_FACT sz k) in
    FIRST_ASSUM(fun a -> if concl a = fst(dest_imp(concl th))
                         then ASSUME_TAC(MP th a) else NO_TAC))
   [16,0; 16,16; 16,32; 16,17; 16,1; 8,33; 4,41; 2,45] THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC ex [k] THEN
    (if k = st.es_madd then
       RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`a:int64`;`i:num`] SI_ETA_MADD)
         (MP (ARITH_RULE (parse_term(Printf.sprintf "i < %d ==> i < 2 EXP 64" p.et_l)))
             (ASSUME (parse_term(Printf.sprintf "i < %d" p.et_l))))]) THEN
       SI_ETA_AP_TAC
     else if mem k st.es_adrp then MLKEM_NATIVE_ADRP_TAC else ALL_TAC))
   (1--st.es_branch) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SI_ETA_CF]);;

(*** The path V: the steps to the block with x12 = ap, the block, its 128 ***)
(*** lanes, the setup and the call of the loop from group 16             ***)

let SI_ETA_V_TAC p st ex =
  let roff = p.et_roff and be = st.es_block_end in
  let sb = "s" ^ string_of_int be in
  let lowt = parse_term(Printf.sprintf
    "!j. j < 128 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * j)))) %s =
                     mld_polyeta_unpack_2 b j" roff sb) in
  MAP_EVERY (fun k -> ARM_STEPS_TAC ex [k] THEN
                      (if k = st.es_ap then SI_ETA_AP_TAC else ALL_TAC))
   ((st.es_branch + 1)--(st.es_ap + 1)) THEN
  MAP_EVERY (fun k -> ARM_STEPS_TAC ex [k] THEN ETA_NORM)
   ((st.es_ap + 2)--be) THEN
  SI_ETA_LANES_TAC roff (sb ^ ":armstate") THEN
  MAP_EVERY (fun j ->
    SUBGOAL_THEN (parse_term(Printf.sprintf
      "read (memory :> bytes32 (word_add fp (word (%d + 4 * %d)))) %s =
       mld_polyeta_unpack_2 b %d" roff j sb j)) ASSUME_TAC THENL
     [SI_ETA_LANE_TAC; ALL_TAC]) (0--127) THEN
  SUBGOAL_THEN lowt ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if ETA_IS_LANE (concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if ETA_BIG_FACT (concl th) then ALL_TAC else NO_TAC)) THEN
  ARM_STEPS_TAC ex ((be + 1)--(st.es_call_v - 1));;

(*** The input in the form of the loop lemma (a + 96 i + j), from the facts ***)
(*** about ap, in the state sn before the call                              ***)

let SI_ETA_AFORM_TAC n =
  W(fun (asl,w) ->
    let ab = SI_ETA_AB asl in
    SUBGOAL_THEN (parse_term(Printf.sprintf
      "!j. j < 96 ==> read (memory :> bytes8 (word_add a (word (96 * i + j)))) s%d =
                      (b:num->byte) j" n)) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      REWRITE_TAC[WORD_RULE `word_add (a:int64) (word (96 * i + j)) =
                             word_add (word_add a (word (96 * i))) (word j)`] THEN
      REWRITE_TAC[ab] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC]);;

let SI_ETA_UNAB0_TAC =
  W(fun (asl,w) -> let ab = SI_ETA_AB asl in
    RULE_ASSUM_TAC(fun th ->
      let c = concl th in
      if is_eq c && free_in `ap:int64` c &&
         can (term_match [] `read events s`) (lhs c)
      then REWRITE_RULE[SYM ab] th else th));;

let SI_ETA_CALL_TAC p ex name n =
  SI_ETA_AFORM_TAC (n - 1) THEN SI_ETA_UNAB0_TAC THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc ex name
   [parse_term(Printf.sprintf "word_add fp (word %d):int64" p.et_roff);
    `a:int64`; `96 * i`; `b:num->byte`; `pc:num`]
   [`fp:int64`; `a:int64`; `i:num`; `pc:num`; `ap:int64`] n;;

(*** The end of a path: the output from the facts of the path, ap expanded ***)
(*** again, and the events                                                ***)

let SI_ETA_UNAB_TAC =
  W(fun (asl,w) -> let ab = SI_ETA_AB asl in
    RULE_ASSUM_TAC(fun th -> if concl th = concl ab ||
                                not(free_in `ap:int64` (concl th)) then th
                             else REWRITE_RULE[SYM ab] th) THEN
    REWRITE_TAC[SYM ab]);;

let SI_ETA_S_TAC p st ex =
  ARM_STEPS_TAC ex ((st.es_branch + 1)--(st.es_call_s - 1)) THEN
  SI_ETA_CALL_TAC p ex "H0" st.es_call_s THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SI_ETA_UNAB_TAC THEN ETA_EVENTS_TAC;;

(*** The end of the path V: the call from group 16, and the output from    ***)
(*** the two halves                                                         ***)

let SI_ETA_V_END_TAC p st ex =
  let roff = p.et_roff in
  SI_ETA_CALL_TAC p ex "H16" st.es_call_v THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j < 128` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        let c = concl th in is_forall c &&
        (try lhand(snd(dest_forall c)) = `j < 128` with Failure _ -> false))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        let c = concl th in is_forall c &&
        (try lhand(snd(dest_forall c)) = `128 <= j /\ j < 256`
         with Failure _ -> false))) THEN
      ASM_ARITH_TAC];
    SI_ETA_UNAB_TAC THEN ETA_EVENTS_TAC] ;;

let SI_ETA_PROVE mc p st (l16,l0) =
  let ex = INLINE_LOOP_EXEC p.et_start p.et_stop in
  let ov = parse_term(Printf.sprintf
    "val (ap:int64) < val (word_add fp (word %d):int64) /\\
     val (word_add fp (word %d):int64) < val (word_add ap (word 96):int64)"
    (p.et_roff + 1024) p.et_roff) in
  prove(SI_ETA_TERM mc p,
    SI_ETA_SETUP_TAC p st ex (l16,l0) THEN
    ASM_CASES_TAC ov THEN
    FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                            REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
     [SI_ETA_S_TAC p st ex;
      SI_ETA_V_TAC p st ex THEN SI_ETA_V_END_TAC p st ex]);;
