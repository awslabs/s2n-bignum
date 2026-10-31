(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tactics for the proofs of the K-PKE functions of mlkem-native in the gcc  *)
(* 12 -O2 image, such as mlkem768_indcpa_enc, which call many of the other   *)
(* functions on buffers in their stack frames. Most callees specify their    *)
(* results only up to congruence modulo q and bounds, so after a call the    *)
(* 16-bit values in a buffer are named by a new function (a ghost), with a   *)
(* fact giving the memory in terms of it, which the simulation carries over  *)
(* later calls, and facts about the ghost without the state, derived from    *)
(* the postcondition of the call. Those facts are then combined by lemmas in *)
(* terms of FIPS 203 (see mlkem_native_fips203.ml).                          *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/utils/mlkem_native_fips203.ml";;

(* ------------------------------------------------------------------------- *)
(* Arithmetic using only the bounds on the variables in the goal.            *)
(* ------------------------------------------------------------------------- *)

let INDCPA_ARITH_TAC =
  W(fun (asl,w) ->
    let vs = frees w in
    let ok th =
      let c = concl th in
      (is_binary "<" c || is_binary "<=" c) &&
      type_of(lhand c) = `:num` && is_var(lhand c) &&
      mem (lhand c) vs && is_numeral(rand c) in
    MAP_EVERY (MP_TAC o snd) (filter (ok o snd) asl) THEN ARITH_TAC);;

let INDCPA_HAS_CONST c tm =
  can (find_term (fun t -> match t with Const(c',_) -> c' = c | _ -> false))
      tm;;

(* ------------------------------------------------------------------------- *)
(* Ghost functions for the 16-bit contents of buffers on the stack.          *)
(* ------------------------------------------------------------------------- *)

let INDCPA_GHOST_TAC v base n s =
  let vt = mk_var(v,`:num->int16`) in
  let fact = parse_term(Printf.sprintf
    "!i. i < %d ==> read (memory :> bytes16 (word_add stackpointer \
     (word(%d + 2 * i)))) (%s:armstate) = (%s:num->int16) i" n base s v) in
  let rd = parse_term(Printf.sprintf
    "\\i. read (memory :> bytes16 (word_add stackpointer \
     (word(%d + 2 * i)))) (%s:armstate)" base s) in
  SUBGOAL_THEN (mk_exists(vt,fact)) (X_CHOOSE_TAC vt) THENL
   [EXISTS_TAC rd THEN REWRITE_TAC[]; ALL_TAC];;

let INDCPA_GHOST_SPEC_TAC v idx =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(_,Comb(Comb(Const("==>",_),_),
        Comb(Comb(Const("=",_),_),Comb(Var(v',_),_))))) when v' = v ->
        MP_TAC(SPEC idx th) THEN ANTS_TAC THENL
         [INDCPA_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]
    | _ -> NO_TAC);;

let INDCPA_CANON_CONV tm =
  match tm with
    Comb(Comb(Const("word_add",_),Var("stackpointer",_)),
         Comb(Const("word",_),t)) when not (is_numeral t) ->
      RAND_CONV(RAND_CONV NUM_NORMALIZE_CONV) tm
  | _ -> failwith "INDCPA_CANON_CONV";;

let INDCPA_UNGHOST_TAC v =
  W(fun (_,w) ->
    let tms = find_terms (fun t -> is_comb t &&
                 (match rator t with Var(v',_) -> v' = v | _ -> false)) w in
    MAP_EVERY (fun t -> INDCPA_GHOST_SPEC_TAC v (rand t)) tms);;

(*** The postcondition of a call in state st, mentioning cn and src ***)

let INDCPA_IS_POST st cn src th =
  let c = concl th in
  mem st (frees c) && INDCPA_HAS_CONST cn c && mem src (frees c);;

let INDCPA_POST_TAC st cn src f =
  FIRST_ASSUM(f o check (INDCPA_IS_POST st cn src));;

let INDCPA_DROP_POST_TAC st cn src =
  FIRST_X_ASSUM(fun th ->
    if INDCPA_IS_POST st cn src th then ALL_TAC else NO_TAC);;

let INDCPA_POST_SIMP_TAC s =
  W(fun (asl,_) ->
    let ths = filter (fun th -> mem s (frees(concl th)) &&
                               is_let(concl th)) (map snd asl) in
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    ASM_SIMP_TAC(map (fun th -> CONV_RULE(ONCE_DEPTH_CONV INDCPA_CANON_CONV)
                                 (CONV_RULE(TOP_DEPTH_CONV let_CONV) th))
                     ths));;

let INDCPA_DISCARD_LETS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_let(concl th) then ALL_TAC else NO_TAC));;

(*** A fact read(...) = g idx, in the form of a precondition, from a ghost ***)

let INDCPA_MEMFACT_TAC tm =
  let g = rand(rand(snd(dest_forall tm))) in
  let v = match strip_comb g with
            (Var(v,_),_) -> v | _ -> failwith "INDCPA_MEMFACT_TAC" in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC v THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The stages: noise polynomials from SamplePolyCBD and PRF (eta = 2), their *)
(* NTTs, the multiplication cache, inverse NTTs and reductions. In each case *)
(* a ghost v names the result of the call in state s at stackpointer + base, *)
(* and its properties are derived from the postcondition.                    *)
(* ------------------------------------------------------------------------- *)

let INDCPA_NOISE_TAC v base k seed nonce s =
  let goal = parse_term(Printf.sprintf
   "!j i. j < %d /\\ i < 256 \
    ==> (ival((%s:num->int16)(256 * j + i)) == \
         coeff i (mlkem_cbd 2 (mlkem_prf 2 %s (%s)))) (mod &3329) /\\ \
        abs(ival((%s:num->int16)(256 * j + i))) <= &2" k v seed nonce v) in
  INDCPA_GHOST_TAC v base (256 * k) s THEN
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD_CLAUSES] THEN REPEAT CONJ_TAC THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC v THEN
    INDCPA_POST_SIMP_TAC (mk_var(s,`:armstate`)) THEN
    MATCH_MP_TAC MLKEM_NATIVE_CBD2_CONG THEN ASM_REWRITE_TAC[mlkem_prf] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let INDCPA_NOISE1_TAC v base seed nonce s =
  let goal = parse_term(Printf.sprintf
   "!i. i < 256 \
    ==> (ival((%s:num->int16) i) == \
         coeff i (mlkem_cbd 2 (mlkem_prf 2 %s (%s)))) (mod &3329) /\\ \
        abs(ival((%s:num->int16) i)) <= &2" v seed nonce v) in
  INDCPA_GHOST_TAC v base 256 s THEN
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC v THEN
    INDCPA_POST_SIMP_TAC (mk_var(s,`:armstate`)) THEN
    MATCH_MP_TAC MLKEM_NATIVE_CBD2_CONG THEN ASM_REWRITE_TAC[mlkem_prf] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let INDCPA_NTT_TAC v base k src seed nonce s =
  let goal = parse_term(Printf.sprintf
   "!j i. j < %d /\\ i < 256 \
    ==> (ival((%s:num->int16)(256 * j + i)) == \
         mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 %s (%s))) i) (mod &3329) /\\ \
        abs(ival((%s:num->int16)(256 * j + i))) <= &23594" k v seed nonce v) in
  let xs = parse_term
    (Printf.sprintf "\\n. (%s:num->int16)(256 * j + n)" src) in
  let st = mk_var(s,`:armstate`) and srct = mk_var(src,`:num->int16`) in
  INDCPA_GHOST_TAC v base (256 * k) s THEN
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN INDCPA_UNGHOST_TAC v THEN
    INDCPA_POST_TAC st "forward_ntt" srct (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(INT_ARITH `abs(x:int) <= &2 ==> abs x <= &8191`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLKEM_NATIVE_NTT_CONG THEN
    EXISTS_TAC xs THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[MLKEM_CBD_IN_RQ];
    INDCPA_DROP_POST_TAC st "forward_ntt" srct];;

let INDCPA_MULCACHE_TAC v base k src s =
  let st = mk_var(s,`:armstate`) and srct = mk_var(src,`:num->int16`) in
  INDCPA_GHOST_TAC v base (128 * k) s THEN
  SUBGOAL_THEN
   (parse_term(Printf.sprintf
     "!j p. j < %d /\\ p < 128 \
      ==> (ival((%s:num->int16)(128 * j + p)) == \
           ival((%s:num->int16)(256 * j + 2 * p + 1)) * \
           &17 pow (2 * bitreverse7 p + 1)) (mod &3329)" k v src))
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN INDCPA_UNGHOST_TAC v THEN
    INDCPA_POST_TAC st "mulcache" srct (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `p:num`)] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    REWRITE_TAC[mulcache; INT_CONG_RREM] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[];
    INDCPA_DROP_POST_TAC st "mulcache" srct];;

(*** The inverse NTT of k polynomials, or of one ***)

let INDCPA_INVNTT_TAC v base k src s =
  let st = mk_var(s,`:armstate`) and srct = mk_var(src,`:num->int16`) in
  INDCPA_GHOST_TAC v base (256 * k) s THEN
  SUBGOAL_THEN
   (parse_term(Printf.sprintf
     "!j i. j < %d /\\ i < 256 \
      ==> (ival((%s:num->int16)(256 * j + i)) == \
           inverse_ntt (\\n. ival((%s:num->int16)(256 * j + n))) i) \
          (mod &3329) /\\ \
          abs(ival(%s(256 * j + i))) <= &26624" k v src v))
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN INDCPA_UNGHOST_TAC v THEN
    INDCPA_POST_TAC st "inverse_ntt" srct (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `i:num`)] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    INDCPA_DROP_POST_TAC st "inverse_ntt" srct];;

let INDCPA_INVNTT1_TAC v base src s =
  let st = mk_var(s,`:armstate`) and srct = mk_var(src,`:num->int16`) in
  INDCPA_GHOST_TAC v base 256 s THEN
  SUBGOAL_THEN
   (parse_term(Printf.sprintf
     "!i. i < 256 \
      ==> (ival((%s:num->int16) i) == \
           inverse_ntt (\\n. ival((%s:num->int16) n)) i) (mod &3329) /\\ \
          abs(ival(%s i)) <= &26624" v src v))
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC v THEN
    INDCPA_POST_TAC st "inverse_ntt" srct (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    REWRITE_TAC[o_DEF] THEN SIMP_TAC[];
    INDCPA_DROP_POST_TAC st "inverse_ntt" srct];;

(*** Montgomery conversion and Barrett reduction of n coefficients ***)

let INDCPA_TOMONT_TAC v base n src s =
  let st = mk_var(s,`:armstate`) and srct = mk_var(src,`:num->int16`) in
  INDCPA_GHOST_TAC v base n s THEN
  SUBGOAL_THEN
   (parse_term(Printf.sprintf
     "!i. i < %d \
      ==> (ival((%s:num->int16) i) == &65536 * ival((%s:num->int16) i)) \
          (mod &3329) /\\ abs(ival(%s i)) <= &3328" n v src v))
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC v THEN
    INDCPA_POST_TAC st "tomont_3329" srct (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    REWRITE_TAC[tomont_3329; o_THM; INT_CONG_RREM] THEN
    CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN SIMP_TAC[];
    INDCPA_DROP_POST_TAC st "tomont_3329" srct];;

let INDCPA_REDUCE_TAC v base n rhs s =
  let st = mk_var(s,`:armstate`) in
  INDCPA_GHOST_TAC v base n s THEN
  SUBGOAL_THEN
   (parse_term(Printf.sprintf
     "!i. i < %d ==> ival((%s:num->int16) i) = ival(%s) rem &3329" n v rhs))
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC v THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      let c = concl th in
      mem st (frees c) && INDCPA_HAS_CONST "rem" c &&
      can (find_term (fun t -> t = mk_small_numeral base)) c)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Encodings, zeroing with memset, and the fourth nonce of getnoise.         *)
(* ------------------------------------------------------------------------- *)

let INDCPA_SP n =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral n));;

let INDCPA_TOBYTES_PRE_TAC v base n s =
  MP_TAC(SPECL [INDCPA_SP base; mk_small_numeral n; mk_var(v,`:num->int16`);
                mk_var(s,`:armstate`)] READ_MEMORY_BYTES16_LIST_OF_SEQ) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV))];;

let INDCPA_TOBYTES_POST_TAC v n g =
  let l = mk_comb(mk_comb(`list_of_seq:(num->int16)->num->int16 list`,
                          mk_var(v,`:num->int16`)),mk_small_numeral n) in
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) &&
    can (find_term (fun t -> t = l)) (concl th) &&
    INDCPA_HAS_CONST "num_of_wordlist" (concl th))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LIST_OF_SEQ_REDUCED THEN EXISTS_TAC g THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[];
    DISCH_TAC];;

let INDCPA_MEMSET_LABEL_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_contract mf ea el ev`) (concl th)
    then LABEL_TAC "H_MEMSET" (REWRITE_RULE[memset_contract] th)
    else NO_TAC);;

let INDCPA_DROP_MEMSET_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(_,Comb(Comb(Const("==>",_),_),
        Comb(Comb(Const("=",_),l),Comb(Const("word_zx",_),_)))))
      when INDCPA_HAS_CONST "bytes8" l -> ALL_TAC
    | _ -> NO_TAC));;

let INDCPA_MEMSETS_TAC execth calls =
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC execth (k0--k) THEN LIBC_PLT_TAC execth k THEN
    LIBC_CALL_TAC "H_MEMSET" execth
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] (k + 5) THEN
    INDCPA_DROP_MEMSET_TAC) calls;;

let INDCPA_NONCE_TAC n =
  ASSUME_TAC(WORD_REDUCE_CONV
   (mk_comb(`word_zx:int64->byte`,mk_comb(`word:num->int64`,
                                         mk_small_numeral n))));;

(* ------------------------------------------------------------------------- *)
(* Specializations of the theorems for the matrix generation (transposed or  *)
(* not) and for getnoise_eta1_4x with a null fourth output.                  *)
(* ------------------------------------------------------------------------- *)

let INDCPA_GEN_MATRIX_SPEC th tr =
  let th1 = INST [tr,`transposed:int64`] (SPEC_ALL th) in
  let eq = mk_eq(mk_comb(`word_zx:int64->int32`,tr),`word 0:int32`) in
  let th2 = REWRITE_RULE[WORD_REDUCE_CONV eq] th1 in
  GENL [`a:int64`; `seed:int64`; `rho:byte list`; `k:num`; `guard:int64`;
        `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`] th2;;

let MAYCHANGE_DROP_BYTES_0 = prove
 (`!(c1:(armstate,num)component) c2 c3 c5 a:int64.
        MAYCHANGE [c1; c2; c3; memory :> bytes(a,0); c5] =
        MAYCHANGE [c1; c2; c3; c5]`,
  REWRITE_TAC[MAYCHANGE; ASSIGNS_MEMORY_BYTES_0; SEQ_ID]);;

let INDCPA_GETNOISE_NULL th =
  let th1 = INST [`word 0:int64`,`r3:int64`] (SPEC_ALL th) in
  let th2 = REWRITE_RULE[PAIRWISE; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES;
                         VAL_WORD_0; NONOVERLAPPING_MODULO_ZERO_LEN;
                         MAYCHANGE_DROP_BYTES_0] th1 in
  GENL [`r0:int64`; `r1:int64`; `r2:int64`; `seed:int64`; `sd:byte list`;
        `nonce0:int64`; `nonce1:int64`; `nonce2:int64`; `nonce3:int64`;
        `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`;
        `ev:num`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`] th2;;

(*** The GOT entries for the guard and memset, in the form used by callees ***)

let INDCPA_GOT_TAC =
  let pat n = subst [mk_small_numeral n,`n:num`]
   `read (memory :> bytes64 (word_add (word pc) (word n):int64)) s =
    (g:int64)` in
  MAP_EVERY (fun n ->
    FIRST_ASSUM(fun th ->
      if can (term_match [] (pat n)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC))
   [131064; 131048];;

(*** A buffer in a stack frame not containing address 0 is not null ***)

let INDCPA_NONZERO_TAC frame off =
  MP_TAC(SPECL [`stackpointer:int64`; mk_small_numeral frame;
                mk_small_numeral off] NONOVERLAPPING_ZERO_NONZERO) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_CLAUSES; VAL_WORD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* The multiplications of a row of a matrix by a vector in the NTT domain    *)
(* for ML-KEM-768, by mlkem768_polyvec_basemul_acc_montgomery_cached. The    *)
(* facts about the inputs are restated in the form of the precondition of    *)
(* the callee, (abase,aname,aoff) giving the row as aname(aoff + i) at       *)
(* stackpointer + abase, and similarly for the vector and its cache. After   *)
(* the call, those facts are removed, and INDCPA_BASEMUL3_ROW_TAC derives    *)
(* the congruence for the coefficients 2 * p and 2 * p + 1 of the result     *)
(* from the postcondition, the definitions defs of the arithmetic of the     *)
(* callee, and rewrites arws for the entries of the row.                     *)
(* ------------------------------------------------------------------------- *)

let INDCPA_BASEMUL3_PRE_TERMS
      (abase,aname,aoff) (bbase,bname) (tbase,tname) s =
  let off base k = if k = 0 then Printf.sprintf "%d + 2 * i" base
                   else Printf.sprintf "%d + %d + 2 * i" base k in
  let gapp g c = if c = 0 then g^" i" else Printf.sprintf "%s(%d + i)" g c in
  let facts =
   [abase,0,256,gapp aname aoff; abase,512,256,gapp aname (aoff + 256);
    abase,1024,256,gapp aname (aoff + 512);
    bbase,0,256,gapp bname 0; bbase,512,256,gapp bname 256;
    bbase,1024,256,gapp bname 512;
    tbase,0,128,gapp tname 0; tbase,256,128,gapp tname 128;
    tbase,512,128,gapp tname 256] in
  map (fun (base,k,n,rhs) ->
    parse_term(Printf.sprintf
      "!i. i < %d ==> read (memory :> bytes16 (word_add stackpointer \
       (word(%s)))) (%s:armstate) = (%s:int16)" n (off base k) s rhs))
   facts;;

let INDCPA_BASEMUL3_PRE_TAC a b t s =
  MAP_EVERY INDCPA_MEMFACT_TAC (INDCPA_BASEMUL3_PRE_TERMS a b t s);;

(*** Drop the restricted facts for a call, carried to later states ***)

let INDCPA_BASEMUL3_DROP_PRE_TAC a b t =
  let tms = INDCPA_BASEMUL3_PRE_TERMS a b t "ss" in
  let sv = `ss:armstate` in
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if exists (fun p -> can (term_match (subtract (frees p) [sv]) p) c) tms
    then ALL_TAC else NO_TAC));;

let INDCPA_BASEMUL3_ARGS (aname,aoff) bname tname =
  let g v c = if c = 0 then parse_term(v^":num->int16") else
    parse_term(Printf.sprintf "\\i. (%s:num->int16)(%d + i)" v c) in
  [`read X1 s`; `read X2 s`; `read X3 s`; `read X0 s`;
   g aname aoff; g bname 0; g tname 0;
   g aname (aoff + 256); g bname 256; g tname 128;
   g aname (aoff + 512); g bname 512; g tname 256;
   `pc:num`; `read X30 s`];;

let INDCPA_BASEMUL3_ROW_TAC v dst blabel arws defs =
  let isrow th =
    match concl th with
      Comb(Comb(Const("==>",_),_),c) ->
        can (find_term (fun t -> t = mk_small_numeral dst)) c &&
        INDCPA_HAS_CONST "basemul3_even" c
    | _ -> false in
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
   [INDCPA_ARITH_TAC; ALL_TAC] THEN
  INDCPA_UNGHOST_TAC v THEN
  FIRST_ASSUM(MP_TAC o check isrow) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
    REMOVE_THEN blabel (fun th -> LABEL_TAC blabel th THEN
      MATCH_MP_TAC th) THEN INDCPA_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC(defs @ [o_THM; INT_CONG_RREM]) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
  ASM_SIMP_TAC arws;;
