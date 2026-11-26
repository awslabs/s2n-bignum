(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of mldsa{44,87}_polyeta_unpack of the clang 23 -O3  *)
(* build. The function tests whether the input (96 bytes at a) and the       *)
(* output (1024 bytes at r) overlap. If not, a straight-line vector block of *)
(* 351 instructions (ld3, ld1 lanes, tbl with up to four registers, orr,     *)
(* bif, zip, uzp, trn) unpacks the first 128 coefficients from 48 bytes,     *)
(* with 8 vectors of constants that the code loads from the image (128 bytes *)
(* at mldsa{44,87}_polyeta_unpack_consts) and spills to the stack; then a    *)
(* scalar loop (loop2: 3 bytes and 8 words per iteration) does the other 128 *)
(* (16 iterations), or all 256 (32 iterations) if the buffers overlap. The   *)
(* frame is 560 bytes (80 for d8-d15 and x29, and 480).                      *)
(*                                                                           *)
(* The proof simulates the vector block in full (about 6 minutes), which     *)
(* leaves for each of the 32 stores at r a 128-bit value that is a function  *)
(* of the 48 input bytes. The loads of the input at the offsets 0, 1, 16,    *)
(* 17, 32 (128 bits), 33 (64), 41 (32) and 45 (16) need the facts of         *)
(* ETA_LD_FACT, the 8 constants those of ETA_CONST_FACTS; the results of     *)
(* ld3 need ETA_DEILS, and the lookups of tbl with an index that is out of   *)
(* range ETA_OOR_CONV. After this normalization the 32-bit lanes are small,  *)
(* and each of the 128 lanes is equal to mld_polyeta_unpack_2 by a           *)
(* bit-blast with the input bytes as variables (ETA_LANE_TAC). The loop is   *)
(* a lemma (ETA_L2_TM, proved by ETA_L2_TAC) that the proof of the function  *)
(* calls with the input shifted by 48 bytes and the output at r + 512        *)
(* (ETA_SHIFT relates the specification). ETA_FULL_TAC is the proof of the   *)
(* function, with the two paths (ETA_V_TAC and ETA_S_TAC) of the overlap     *)
(* test, whose condition is an if-then-else on val that the proof case       *)
(* splits on.                                                                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;

let PTR_ADD_G = prove(`!b:int64 n k. word_add (word_add b (word n)) (word k) = word_add b (word (n + k))`, REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

let ETA_CHUNK = prove
 (`!(a:int64) (s:armstate) n k.
     k < 8 /\ read (memory :> bytes(a,128)) s = n
     ==> read (memory :> bytes128 (word_add a (word (16 * k)))) s =
         word ((n DIV 2 EXP (128 * k)) MOD 2 EXP 128)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bytes128; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. (x DIV 2 EXP (8 * (16 * k))) MOD 2 EXP (8 * 16)`) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (128 - 16 * k) 16 = 16` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * 16 * k = 128 * k /\ 8 * 16 = 128`] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[WORD_VAL]);;

(*** The 128 bytes of constants in the image, as 128-bit vectors ***)

let ETA_CONSTS_IN_IMAGE fn =
  let d = layout (fn ^ "_polyeta_unpack_consts") in
  let l = mk_list(fst(chop_list 128 (snd(chop_list d
            (dest_list(rhs(concl
              mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc)))))),
                  `:byte`) in
  let lth = MLDSA_NATIVE_IMAGE_DATA_RULE (REFL l) d
  and lenth = LENGTH_CONV(mk_comb(`LENGTH:byte list->num`,l)) in
  let nth = (REWRITE_CONV[num_of_bytelist] THENC DEPTH_CONV WORD_RED_CONV THENC
             REWRITE_CONV[DIMINDEX_8] THENC NUM_REDUCE_CONV)
            (mk_comb(`num_of_bytelist`,l)) in
  let n = rand(concl nth) in
  prove
   (mk_forall(`s:armstate`,mk_forall(`pc:num`,
      mk_imp(`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc`,
        mk_eq(parse_term(Printf.sprintf "read (memory :> bytes(word(pc + %d),128)) s" d),n)))),
    REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP lth) THEN
    REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; lenth; nth]);;

(*** The eight vectors of constants, at the addresses of the simulator ***)

let ETA_CONST_FACTS fn s0 =
  let d = layout (fn ^ "_polyeta_unpack_consts") in
  let th = UNDISCH(SPECL [s0; `pc:num`] (ETA_CONSTS_IN_IMAGE fn)) in
  let n = rand(concl th) in
  let wd = parse_term(Printf.sprintf "word(pc + %d):int64" d) in
  map (fun k ->
    let ch = SPECL [wd; s0; n; mk_small_numeral k] ETA_CHUNK in
    let hy = CONJ (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral k,`8`))))
                   th in
    let ch = MP ch hy in
    let ch = CONV_RULE NUM_REDUCE_CONV ch in
    let ax = prove(mk_eq(mk_comb(mk_comb(`word_add:int64->int64->int64`,wd),
                                 mk_comb(`word:num->int64`,mk_small_numeral(16*k))),
                         mk_comb(mk_comb(`word_add:int64->int64->int64`,`word pc:int64`),
                                 mk_comb(`word:num->int64`,mk_small_numeral(d + 16*k)))),
                   CONV_TAC WORD_RULE) in
    DISCH (hd(hyp th)) (REWRITE_RULE[ax] ch)) (0--7);;

(*** Loads of 2, 4, 8 and 16 bytes of the input at any offset, from its bytes ***)

let ETA_LD_FACT sz k =
  let a = `a:int64` and s0 = `s0:armstate` in
  let hyp = `!j. j < 96 ==> read (memory :> bytes8 (word_add a (word j))) s0 = (b:num->byte) j` in
  let hth = ASSUME hyp in
  let insts = map (fun i ->
    let j = k + i in
    let th = MP (SPEC (mk_small_numeral j) hth)
                (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral j,`96`)))) in
    REWRITE_RULE[WORD_ADD_0] th) (0--(sz-1)) in
  let addr = if k = 0 then "a" else Printf.sprintf "word_add a (word %d)" k in
  let lhs = parse_term(Printf.sprintf "read (memory :> bytes%d (%s)) s0" (8 * sz) addr) in
  let conv = REWRITE_CONV[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 3 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          PTR_ADD_G; GSYM ADD_ASSOC] THENC
             DEPTH_CONV NUM_ADD_CONV in
  let th = conv lhs in
  let th2 = REWRITE_RULE (WORD_ADD_0 :: insts) th in
  DISCH hyp th2;;

(*** ld3 of bytes: the deinterleaving of 3 ***)

let ETA_DEIL3 j =
  let elt m = Printf.sprintf "(word_subword z (%d,8):byte)" ((3 * m + j) * 8) in
  let rec jn lo n =   (* the n lanes lo .. lo+n-1, highest first *)
    if n = 1 then elt lo else
    let h = n / 2 in
    let ty = (match n with 2 -> "int16" | 4 -> "int32" | 8 -> "int64" | _ -> "int128") in
    Printf.sprintf "(word_join %s %s:%s)" (jn (lo + h) h) (jn lo h) ty in
  let rhs = jn 0 16 in
  prove(parse_term(Printf.sprintf "!z:384 word. (word_subdeinterleave 3 8 z %d : int128) = %s" j rhs),
    GEN_TAC THEN REWRITE_TAC[word_subdeinterleave] THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; BIT_WORD_JOIN; BIT_WORD_SUBWORD; IN_ELIM_THM; DIMINDEX_128; DIMINDEX_64; DIMINDEX_32; DIMINDEX_16; DIMINDEX_8] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[LET_DEF; LET_END_DEF; MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
let ETA_DEILS = map ETA_DEIL3 [0;1;2];;

(*** Lookups with an index that is out of range read 0 ***)

let SUBWORD_OOR = prove(`!(x:N word) p l. dimindex(:N) <= p ==> (word_subword x (p,l):M word) = word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword] THEN
  SUBGOAL_THEN `(val (x:N word) DIV 2 EXP p) = 0` (fun th -> REWRITE_TAC[th; ARITH_RULE `0 MOD n = 0`]) THEN
  MATCH_MP_TAC DIV_LT THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP dimindex(:N)` THEN REWRITE_TAC[VAL_BOUND] THEN
  REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC);;

let ETA_OOR_CONV tm =
  match tm with
    Comb(Comb(Const("word_subword",_),x),Comb(Comb(Const(",",_),p),l)) when is_numeral p ->
      let tyN = hd(snd(dest_type(type_of x))) and tyM = hd(snd(dest_type(type_of tm))) in
      let th = SPECL [x;p;l] (INST_TYPE [tyN,`:N`;tyM,`:M`] SUBWORD_OOR) in
      let h = fst(dest_imp(concl th)) in
      MP th (EQT_ELIM((DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) h))
  | _ -> failwith "ETA_OOR_CONV";;

(*** The step of the scalar loop ***)

(* The scalar loop of mldsa44_polyeta_unpack: one group of 3 bytes and 8 words per iteration *)

let ETA_STEP = prove
 (`!(f:num->int32) (m:num->int32) (mem:num->int32) g0 g.
        g0 <= g /\ g < 32 /\
        (!k. k < 8 ==> mem (8 * g + k) = f (8 * g + k)) /\
        (!j. j < 256 /\ ~(8 * g <= j /\ j < 8 * g + 8)
             ==> mem j = (if 8 * g0 <= j /\ j < 8 * g then f j else m j))
        ==> !j. j < 256 ==> mem j = (if 8 * g0 <= j /\ j < 8 * (g + 1) then f j else m j)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `8 * g <= j /\ j < 8 * g + 8` THENL
   [SUBGOAL_THEN `?k. k < 8 /\ j = 8 * g + k` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `j - 8 * g` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> try fst(dest_imp(snd(dest_forall(concl th)))) = `k < 8` with _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `8 * g0 <= 8 * g + k /\ 8 * g + k < 8 * (g + 1)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> try fst(dest_imp(snd(dest_forall(concl th)))) = `j < 256 /\ ~(8 * g <= j /\ j < 8 * g + 8)` with _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(8 * g0 <= j /\ j < 8 * g) <=> (8 * g0 <= j /\ j < 8 * (g + 1))` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The scalar loop (loop2): 3 bytes and 8 words per iteration, n iterations  *)
(* from the pointers a and r (the code adds 1 and 16 to them for the         *)
(* offsets of its loads and stores); fn is mldsa44 or mldsa87.               *)
(* ------------------------------------------------------------------------- *)

let ETA_L2_TM fn n =
  let neg = Num.string_of_num (Num.sub_num (Num.power_num (Num.num_of_int 2) (Num.num_of_int 64)) (Num.num_of_int n)) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (r:int64) (a:int64) (b:num->byte) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (r,%d)) [(word pc,libmldsa_size); (a,%d)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                  read PC s = word (pc + %s_polyeta_unpack_loop2) /\\
                  read X8 s = word %s /\\
                  read X9 s = word_add a (word 1) /\\
                  read X10 s = word_add r (word 16) /\\
                  read X11 s = word 2 /\\
                  (!j. j < %d
                       ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s_polyeta_unpack_loop2_exit) /\\
                  (!j. j < %d
                       ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                           mld_polyeta_unpack_2 b j) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events r a pc /\\
                     memaccess_inbounds e2 [a,%d] [r,%d]))
             (MAYCHANGE [PC; X0; X8; X9; X10; X12; X13; X14; X15; X16; X17; X18] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r,%d)])"
   (32 * n) (3 * n) fn neg (3 * n) fn (8 * n) (3 * n) (32 * n) (32 * n));;

let ETA_L2_HEAD fn exec n =
  let neg = Num.string_of_num (Num.sub_num (Num.power_num (Num.num_of_int 2) (Num.num_of_int 64)) (Num.num_of_int n)) in
  CONCRETIZE_F_EVENTS_TAC
   (parse_term(Printf.sprintf
     "\\(r:int64) (a:int64) (pc:num).
        APPEND (f_ev_epil r a pc)
         (APPEND (ENUMERATEL %d (\\i. f_ev_loop r a pc i)) (f_ev_prol r a pc))
      :(uarch_event)list" n)) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `r:int64`; `a:int64`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (parse_term (string_of_int n))
   (parse_term (Printf.sprintf "pc + %s_polyeta_unpack_loop2" fn))
   (parse_term (Printf.sprintf "pc + %s_polyeta_unpack_loop2_exit" fn))
   (parse_term(Printf.sprintf
    "\\i s. read X8 s = word (%s + i) /\\
           read X9 s = word_add (word_add a (word (3 * i))) (word 1) /\\
           read X10 s = word_add (word_add r (word (32 * i))) (word 16) /\\
           read X11 s = word 2 /\\
           (!j. j < %d ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
           (!j. j < 8 * i
                ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                    mld_polyeta_unpack_2 b j)" neg (3 * n))) THEN
  REPEAT CONJ_TAC;;

let ETA_CNT n =
  let neg = Num.string_of_num (Num.sub_num (Num.power_num (Num.num_of_int 2) (Num.num_of_int 64)) (Num.num_of_int n)) in
  prove(parse_term(Printf.sprintf
    "!i. i < %d ==> (val (word (%s + i):int64) + 1 < 2 EXP 64 <=> i + 1 < %d)" n neg n),
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let ETA_L2_FINAL n =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MP (SPEC `i:num` (ETA_CNT n)) (ASSUME (parse_term(Printf.sprintf "i < %d" n)))] THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT; CHUNK_OUTPUT_SPLIT_1] THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[mld_polyeta_unpack_2] THEN
      SIMP_TAC[DIVMOD_CHUNK; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN APP_BLAST_TAC `b:num->byte` THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let ETA_L2_TAC fn exec n =
  ETA_L2_HEAD fn exec n THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `b:num->byte` 3 THEN
    ARM_STEPS_TAC exec (1--42) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PTR_ADD_G]) THEN
    ETA_L2_FINAL n;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* The proof of the function from the scalar loop (loop2).                   *)
(*                                                                           *)
(* The function tests whether the input and the output overlap. If not (the  *)
(* path V, for vector) it runs the vector block, which unpacks the first 128 *)
(* coefficients from 48 bytes, and calls loop2 for the other 128 (16         *)
(* iterations); otherwise (the path S, for scalar) it calls loop2 for all    *)
(* 256 (32 iterations). The events of the function are the events of the     *)
(* path that was taken, which the template with ETA_COND selects; each path  *)
(* case splits on ETA_COND and rewrites the goal with the case.              *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/mldsa_native_full.ml";;

let ETA_NORM =
  RULE_ASSUM_TAC(REWRITE_RULE ETA_DEILS) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV (ETA_OOR_CONV ORELSEC WORD_SIMPLE_SUBWORD_CONV)));;

(*** The steps with an adrp (page address) instruction: the page of the    ***)
(*** address of a constant is normalized after the step of the adrp.       ***)

let ETA_ADRPS = [12;13;14;16;20;23;26;32];;
let rec eta_stepto exec lo hi =
  if lo > hi then ALL_TAC else
  match filter (fun k -> k >= lo && k <= hi) ETA_ADRPS with
    [] -> MAP_EVERY (fun k -> ARM_STEPS_TAC exec (k--k) THEN ETA_NORM) (lo--hi)
  | k::_ -> MAP_EVERY (fun j -> ARM_STEPS_TAC exec (j--j) THEN ETA_NORM) (lo--k) THEN
            MLKEM_NATIVE_ADRP_TAC THEN eta_stepto exec (k+1) hi;;

let ETA_COND =
 `(if val (a:int64) < val (word_add r (word 1024):int64)
    then (&(val (r:int64)):int) - &(val (word_add a (word 96):int64)) =
         &(val (word_sub r (word_add a (word 96)):int64))
    else true)`;;

let ETA_TEMPLATE = `\(r:int64) (a:int64) (pc:num) (sp:int64) (ra:int64).
   if (if val a < val (word_add r (word 1024):int64)
       then (&(val r):int) - &(val (word_add a (word 96):int64)) =
            &(val (word_sub r (word_add a (word 96)):int64))
       else true)
   then APPEND (f_ev_epiV r a pc sp ra)
         (APPEND (f_ev_l2V r a pc sp ra) (f_ev_proV r a pc sp ra))
   else APPEND (f_ev_epiS r a pc sp ra)
         (APPEND (f_ev_l2S r a pc sp ra) (f_ev_proS r a pc sp ra))
   :(uarch_event)list`;;

(*** The start: the lemmas of the loop, the preserved registers, the facts ***)
(*** about the constants and the input, and the 11 steps to the branch.     ***)

let ETA_SETUP fn exec l16 l32 =
  ASSUME_CALLEE_SAFETY_TAILED_TAC l16 "H16" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC l32 "H32" THEN
  CONCRETIZE_F_EVENTS_TAC ETA_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; C_RETURN;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  MAP_EVERY (fun k -> ENSURES_PRESERVED_DREG_TAC (Printf.sprintf "d%d_init" k) (parse_term (Printf.sprintf "D%d" k))) (8--15) THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(fun a -> if concl a = hd(hyp (UNDISCH th)) then ASSUME_TAC(MP th a) else NO_TAC)) (ETA_CONST_FACTS fn `s0:armstate`) THEN
  MAP_EVERY (fun (sz,k) -> let th = ETA_LD_FACT sz k in FIRST_ASSUM(fun a -> if concl a = fst(dest_imp(concl th)) then ASSUME_TAC(MP th a) else NO_TAC)) [16,0; 16,16; 16,32; 16,17; 16,1; 8,33; 4,41; 2,45] THEN
  ARM_STEPS_TAC exec (1--11);;

(*** The 128 lanes of the 32 stores of the vector block, as facts about    ***)
(*** 32-bit words, and their proofs against the specification              ***)

let ETA_UNSPLIT = [el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT); el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT); el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT); PTR_ADD_G; GSYM ADD_ASSOC; WORD_ADD_0];;

let ETA_LANES_TAC sname =
  let is_store t =
    try let l,_ = dest_eq t in
        (match l with
           Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),Comb(Const(bn,_),addr))),_)
             when bn = "bytes128" || bn = "bytes256" ->
             addr = `r:int64` ||
             (match addr with
                Comb(Comb(Const("word_add",_),r0),_) -> r0 = `r:int64`
              | _ -> false)
         | _ -> false)
    with _ -> false in
  W(fun (asl,w) ->
    let sts = filter (fun (_,th) -> is_store(concl th) && free_in (parse_term sname) (concl th)) asl in
    MAP_EVERY (fun (_,th) ->
      let th1 = REWRITE_RULE ETA_UNSPLIT th in
      let th2 = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th1 in
      let th3 = map (CONV_RULE(DEPTH_CONV (ETA_OOR_CONV ORELSEC WORD_SIMPLE_SUBWORD_CONV))) (CONJUNCTS th2) in
      MAP_EVERY ASSUME_TAC th3) sts);;

let ETA_LANE_TAC =
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  W(fun (asl,w) ->
    let l = lhand w in
    FIRST_ASSUM(fun th -> if lhand(concl th) = l then REWRITE_TAC[th] else NO_TAC)) THEN
  REWRITE_TAC[mld_polyeta_unpack_2] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
  APP_BLAST_TAC `b:num->byte`;;

(*** The lanes in the second half of the output are those of the first    ***)
(*** half with the input shifted by 48 bytes                              ***)

let ETA_SHIFT = prove
 (`!(b:num->byte) j. mld_polyeta_unpack_2 b (128 + j) =
                     mld_polyeta_unpack_2 (\m. b(48 + m)) j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_polyeta_unpack_2] THEN
  SUBGOAL_THEN `(128 + j) DIV 8 = 16 + j DIV 8 /\ (128 + j) MOD 8 = j MOD 8`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ARITH_TAC;
      ONCE_REWRITE_TAC[ARITH_RULE `128 + j = 16 * 8 + j`] THEN
      REWRITE_TAC[MOD_MULT_ADD]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `3 * (16 + x) + m = 48 + (3 * x + m)`] THEN
  REWRITE_TAC[]);;

let ETA_APPEND_CONG = prove
 (`!(a:(A)list) b c d. a = c /\ b = d ==> APPEND a b = APPEND c d`,
  MESON_TAC[]);;

(*** The events of the function, from the events of the paths ***)

let ETA_EVENTS_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND; GSYM APPEND_ASSOC] THEN
    REPEAT(MATCH_MP_TAC ETA_APPEND_CONG THEN CONJ_TAC THENL
            [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
    FULL_UNIFY_F_EVENTS_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[APPEND_NIL; CONJUNCT1 APPEND; GSYM APPEND_ASSOC] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(*** The path V: the vector block (steps 12 to 362, to the branch back     ***)
(*** that is not taken), the lanes, the setup of loop2 (363 to 369), the   ***)
(*** call for 16 iterations from the input at a + 48 and the output at     ***)
(*** r + 512, and the return (371 to 390)                                  ***)

let ETA_LOW362 = `!j. j < 128 ==> read (memory :> bytes32 (word_add r (word (4 * j)))) s362 = mld_polyeta_unpack_2 b j`;;
let ETA_LOWT = `!j. j < 128 ==> read (memory :> bytes32 (word_add r (word (4 * j)))) s390 = mld_polyeta_unpack_2 b j`;;
let ETA_HIGHT = `!j. j < 128 ==> read (memory :> bytes32 (word_add r (word (512 + 4 * j)))) s390 = mld_polyeta_unpack_2 (\m. (b:num->byte) (48 + m)) j`;;

(*** The facts about vector registers and stores of 128 or 256 bits are   ***)
(*** not needed after the lanes; dropping them keeps the simulation fast  ***)

let ETA_BIG_FACT t =
  try let l,_ = dest_eq t in
   (match l with
      Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),Comb(Const(bn,_),_))),st) ->
        (bn = "bytes128" || bn = "bytes256") &&
        (let n = name_of st in
         String.length n > 1 && n.[0] = 's' &&
         (try int_of_string (String.sub n 1 (String.length n - 1)) >= 12
          with _ -> false))
    | Comb(Comb(Const("read",_),Const(q,_)),st) ->
        String.length q > 1 && q.[0] = 'Q' &&
        can int_of_string (String.sub q 1 (String.length q - 1))
    | _ -> false)
  with _ -> false;;

let ETA_IS_LANE t =
  try let l,_ = dest_eq t in
   (match l with
      Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),Comb(Const(bn,_),_))),_) ->
        bn = "bytes32"
    | _ -> false)
  with _ -> false;;

let ETA_FIN_TAC =
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < 128` THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = ETA_LOWT)) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `?k. i = 128 + k` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `i - 128` THEN UNDISCH_TAC `~(i < 128)` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `k < 128` ASSUME_TAC THENL
     [UNDISCH_TAC `i < 256` THEN UNDISCH_TAC `i = 128 + k` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[ETA_SHIFT; ARITH_RULE `4 * (128 + k) = 512 + 4 * k`] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = ETA_HIGHT)) THEN
    ASM_REWRITE_TAC[]];;

let ETA_V_TAC exec =
  FIRST_X_ASSUM(fun th ->
    if concl th = ETA_COND then
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th
    else NO_TAC) THEN
  eta_stepto exec 12 362 THEN
  ETA_LANES_TAC "s362:armstate" THEN
  MAP_EVERY (fun j ->
    SUBGOAL_THEN (parse_term(Printf.sprintf "read (memory :> bytes32 (word_add r (word (4 * %d)))) s362 = mld_polyeta_unpack_2 b %d" j j)) ASSUME_TAC THENL
     [ETA_LANE_TAC; ALL_TAC]) (0--127) THEN
  SUBGOAL_THEN ETA_LOW362 ASSUME_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if ETA_IS_LANE (concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if ETA_BIG_FACT (concl th) then ALL_TAC else NO_TAC)) THEN
  ARM_STEPS_TAC exec (363--369) THEN
  SUBGOAL_THEN `!j. j < 48 ==> read (memory :> bytes8 (word_add a (word (48 + j)))) s369 = (b:num->byte) (48 + j)` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `48 + j` o
      check (fun th -> is_forall (concl th) &&
                       can (find_term (fun t -> t = `bytes8`)) (concl th) &&
                       can (find_term (fun t -> name_of t = "s369")) (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `j < 48` THEN ARITH_TAC; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_add (word 48) (a:int64)) (word 1) = word_add a (word 49)`]) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H16"
   [`word_add r (word 512):int64`; `word_add a (word 48):int64`;
    `\m. (b:num->byte) (48 + m)`; `pc:num`]
   [`r:int64`; `a:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`] 370 THEN
  ARM_STEPS_TAC exec (371--390) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  TRY(ETA_FIN_TAC THEN NO_TAC) THEN
  ETA_EVENTS_TAC;;

(*** The path S: the 2 steps that clear x9 and branch, the setup of loop2   ***)
(*** (14 to 20), the call for 32 iterations and the return (22 to 41)       ***)

let ETA_S_TAC exec =
  FIRST_X_ASSUM(fun th ->
    if concl th = mk_neg ETA_COND then
      RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th
    else NO_TAC) THEN
  ARM_STEPS_TAC exec (12--20) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec "H32"
   [`r:int64`; `a:int64`; `b:num->byte`; `pc:num`]
   [`r:int64`; `a:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`] 21 THEN
  ARM_STEPS_TAC exec (22--41) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  ETA_EVENTS_TAC;;

let ETA_FULL_TAC fn exec l16 l32 =
  ETA_SETUP fn exec l16 l32 THEN
  ASM_CASES_TAC ETA_COND THENL [ETA_V_TAC exec; ETA_S_TAC exec];;
