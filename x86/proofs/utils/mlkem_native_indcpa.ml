(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tactics for the proofs of the K-PKE functions of mlkem-native in the gcc  *)
(* 12 -O2 image, such as mlkem768_indcpa_dec, which call many of the other   *)
(* functions on buffers in their stack frames, as in                         *)
(* arm/proofs/utils/mlkem_native_indcpa.ml. Most callees specify their       *)
(* results only up to congruence modulo q and bounds, so after a call the    *)
(* 16-bit values in a buffer are named by a new function (a ghost), with a   *)
(* fact giving the memory in terms of it, which the simulation carries over  *)
(* later calls, and facts about the ghost without the state, derived from    *)
(* the postcondition of the call. Those facts are then combined by lemmas in *)
(* terms of FIPS 203 (see mlkem_native_fips203.ml). On x86 the buffers are   *)
(* at offsets from a frame variable bot, since the frames are aligned to 32  *)
(* bytes by AND.                                                             *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native_fips203.ml";;

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
(* Ghost functions for the 16-bit contents of buffers in the frame.          *)
(* ------------------------------------------------------------------------- *)

let INDCPA_GHOST_TAC v base n s =
  let vt = mk_var(v,`:num->int16`) in
  let fact = parse_term(Printf.sprintf
    "!i. i < %d ==> read (memory :> bytes16 (word_add bot \
     (word(%d + 2 * i)))) (%s:x86state) = (%s:num->int16) i" n base s v) in
  let rd = parse_term(Printf.sprintf
    "\\i. read (memory :> bytes16 (word_add bot \
     (word(%d + 2 * i)))) (%s:x86state)" base s) in
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
    Comb(Comb(Const("word_add",_),Var("bot",_)),
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
(* The stages: noise polynomials from SamplePolyCBD and PRF with eta = 2 or  *)
(* 3 (2 for INDCPA_NOISE_TAC, INDCPA_NOISE1_TAC and INDCPA_NTT_TAC), their   *)
(* NTTs, the multiplication cache, inverse NTTs and reductions. In each case *)
(* a ghost v names the result of the call in state s at bot + base, and its  *)
(* properties are derived from the postcondition.                            *)
(* ------------------------------------------------------------------------- *)

let INDCPA_NOISE_ETA_TAC eta v base k seed nonce s =
  let goal = parse_term(Printf.sprintf
   "!j i. j < %d /\\ i < 256 \
    ==> (ival((%s:num->int16)(256 * j + i)) == \
         coeff i (mlkem_cbd %d (mlkem_prf %d %s (%s)))) (mod &3329) /\\ \
        abs(ival((%s:num->int16)(256 * j + i))) <= &%d"
   k v eta eta seed nonce v eta) in
  let cong = if eta = 2 then MLKEM_NATIVE_CBD2_CONG
             else MLKEM_NATIVE_CBD3_CONG in
  INDCPA_GHOST_TAC v base (256 * k) s THEN
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD_CLAUSES] THEN REPEAT CONJ_TAC THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC v THEN
    INDCPA_POST_SIMP_TAC (mk_var(s,`:x86state`)) THEN
    MATCH_MP_TAC cong THEN ASM_REWRITE_TAC[mlkem_prf] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let INDCPA_NOISE_TAC = INDCPA_NOISE_ETA_TAC 2;;

let INDCPA_NOISE1_TAC v base seed nonce s =
  let goal = parse_term(Printf.sprintf
   "!i. i < 256 \
    ==> (ival((%s:num->int16) i) == \
         coeff i (mlkem_cbd 2 (mlkem_prf 2 %s (%s)))) (mod &3329) /\\ \
        abs(ival((%s:num->int16) i)) <= &2" v seed nonce v) in
  INDCPA_GHOST_TAC v base 256 s THEN
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC v THEN
    INDCPA_POST_SIMP_TAC (mk_var(s,`:x86state`)) THEN
    MATCH_MP_TAC MLKEM_NATIVE_CBD2_CONG THEN ASM_REWRITE_TAC[mlkem_prf] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let INDCPA_NTT_ETA_TAC eta v base k src seed nonce s =
  let goal = parse_term(Printf.sprintf
   "!j i. j < %d /\\ i < 256 \
    ==> (ival((%s:num->int16)(256 * j + i)) == \
         mlkem_ntt (mlkem_cbd %d (mlkem_prf %d %s (%s))) i) (mod &3329) /\\ \
        abs(ival((%s:num->int16)(256 * j + i))) <= &23594"
   k v eta eta seed nonce v) in
  let xs = parse_term
    (Printf.sprintf "\\n. (%s:num->int16)(256 * j + n)" src) in
  let bnd = parse_term(Printf.sprintf
    "abs(x:int) <= &%d ==> abs x <= &8191" eta) in
  let st = mk_var(s,`:x86state`) and srct = mk_var(src,`:num->int16`) in
  INDCPA_GHOST_TAC v base (256 * k) s THEN
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN INDCPA_UNGHOST_TAC v THEN
    INDCPA_POST_TAC st "forward_ntt" srct (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(INT_ARITH bnd) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLKEM_NATIVE_NTT_CONG THEN
    EXISTS_TAC xs THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[MLKEM_CBD_IN_RQ];
    INDCPA_DROP_POST_TAC st "forward_ntt" srct];;

let INDCPA_NTT_TAC = INDCPA_NTT_ETA_TAC 2;;

let INDCPA_MULCACHE_TAC v base k src s =
  let st = mk_var(s,`:x86state`) and srct = mk_var(src,`:num->int16`) in
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
  let st = mk_var(s,`:x86state`) and srct = mk_var(src,`:num->int16`) in
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
  let st = mk_var(s,`:x86state`) and srct = mk_var(src,`:num->int16`) in
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
  let st = mk_var(s,`:x86state`) and srct = mk_var(src,`:num->int16`) in
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
  let st = mk_var(s,`:x86state`) in
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
(* Encodings and the fourth nonce of getnoise.                               *)
(* ------------------------------------------------------------------------- *)

let INDCPA_SP n =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`bot:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral n));;

let INDCPA_TOBYTES_PRE_TAC v base n s =
  MP_TAC(SPECL [INDCPA_SP base; mk_small_numeral n; mk_var(v,`:num->int16`);
                mk_var(s,`:x86state`)] READ_MEMORY_BYTES16_LIST_OF_SEQ) THEN
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

let INDCPA_NONCE_TAC n =
  ASSUME_TAC(WORD_REDUCE_CONV
   (mk_comb(`word_zx:int64->byte`,mk_comb(`word:num->int64`,
                                         mk_small_numeral n))));;

(* ------------------------------------------------------------------------- *)
(* The multiplications of a row of a matrix by a vector of k polynomials in  *)
(* the NTT domain, by the polyvec_basemul_acc_montgomery_cached functions    *)
(* for k = 2, 3 and 4 (ML-KEM-512, ML-KEM-768 and ML-KEM-1024). The facts    *)
(* about the inputs are restated in the form of the precondition of the      *)
(* callee, (abase,aname,aoff) giving the row as aname(aoff + i) at bot +     *)
(* abase, and similarly for the vector and its cache. After the call, those  *)
(* facts are removed, and INDCPA_BASEMULK_ROW_TAC derives the congruence for *)
(* the coefficients 2 * p and 2 * p + 1 of the result from the               *)
(* postcondition, the definitions defs of the arithmetic of the callee, and  *)
(* rewrites arws for the entries of the row. The tactics with 3 in their     *)
(* names are those for k = 3.                                                *)
(* ------------------------------------------------------------------------- *)

let INDCPA_BASEMULK_PRE_TERMS k
      (abase,aname,aoff) (bbase,bname) (tbase,tname) s =
  let off base c = if c = 0 then Printf.sprintf "%d + 2 * i" base
                   else Printf.sprintf "%d + %d + 2 * i" base c in
  let gapp g c = if c = 0 then g^" i" else Printf.sprintf "%s(%d + i)" g c in
  let facts =
    map (fun j -> abase,512 * j,256,gapp aname (aoff + 256 * j)) (0--(k-1)) @
    map (fun j -> bbase,512 * j,256,gapp bname (256 * j)) (0--(k-1)) @
    map (fun j -> tbase,256 * j,128,gapp tname (128 * j)) (0--(k-1)) in
  map (fun (base,c,n,rhs) ->
    parse_term(Printf.sprintf
      "!i. i < %d ==> read (memory :> bytes16 (word_add bot \
       (word(%s)))) (%s:x86state) = (%s:int16)" n (off base c) s rhs))
   facts;;

let INDCPA_BASEMULK_PRE_TAC k a b t s =
  MAP_EVERY INDCPA_MEMFACT_TAC (INDCPA_BASEMULK_PRE_TERMS k a b t s);;

let INDCPA_BASEMULK_DROP_PRE_TAC k a b t =
  let tms = INDCPA_BASEMULK_PRE_TERMS k a b t "ss" in
  let sv = `ss:x86state` in
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if exists (fun p -> can (term_match (subtract (frees p) [sv]) p) c) tms
    then ALL_TAC else NO_TAC));;

let INDCPA_BASEMULK_ARGS k (aname,aoff) bname tname =
  let g v c = if c = 0 then parse_term(v^":num->int16") else
    parse_term(Printf.sprintf "\\i. (%s:num->int16)(%d + i)" v c) in
  [`read RSI s`; `read RDX s`; `read RCX s`; `read RDI s`] @
  itlist (fun j l -> g aname (aoff + 256 * j) :: g bname (256 * j) ::
                     g tname (128 * j) :: l) (0--(k-1)) [] @
  [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`];;

let INDCPA_BASEMULK_ROW_TAC k v dst blabel arws defs =
  let cn = Printf.sprintf "basemul%d_even" k in
  let isrow th =
    match concl th with
      Comb(Comb(Const("==>",_),_),c) ->
        can (find_term (fun t -> t = mk_small_numeral dst)) c &&
        INDCPA_HAS_CONST cn c
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

let INDCPA_BASEMUL3_PRE_TAC = INDCPA_BASEMULK_PRE_TAC 3;;

let INDCPA_BASEMUL3_DROP_PRE_TAC = INDCPA_BASEMULK_DROP_PRE_TAC 3;;

let INDCPA_BASEMUL3_ARGS = INDCPA_BASEMULK_ARGS 3;;

let INDCPA_BASEMUL3_ROW_TAC = INDCPA_BASEMULK_ROW_TAC 3;;

(* ------------------------------------------------------------------------- *)
(* The frame. The buffers of f bytes are aligned to 32 below the p bytes of  *)
(* the pushes, by AND with -32, and the callees use up to d bytes below      *)
(* them. With stackpointer the bottom of the n = p + 32 + f + d bytes below  *)
(* the return address, the frame variable bot of INDCPA_BOT_TAC is the       *)
(* bottom of the stacks of the callees, stackpointer + delta for             *)
(* delta = 32 - val(stackpointer + (n - p)) MOD 32, and the facts about the  *)
(* frame, its position and the alignment of buffers in it, are proved by     *)
(* BITBLAST through the form of delta as a word, INDCPA_DELTA.               *)
(* INDCPA_FRAME_TAC restricts the frame of the goal to the buffers and the   *)
(* pushes, INDCPA_NORM_TAC puts the addresses in assumptions in the form of  *)
(* the simulation, INDCPA_RSP_TAC gives the stack pointer after the AND in   *)
(* terms of bot, and INDCPA_UNBOT_TAC expands the frame variables, for the   *)
(* events.                                                                   *)
(* ------------------------------------------------------------------------- *)

let INDCPA_ALIGNED_16 = prove
 (`!x:int64. aligned 16 x <=> word_and x (word 15) = word 0`,
  GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`]);;

let INDCPA_DELTA = prove
 (`!x:int64. 32 - val x MOD 32 =
             val(word_sub (word 32) (word_and x (word 31)):int64)`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(word_and (x:int64) (word 31)) = val x MOD 32`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `31 = 2 EXP 5 - 1`] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 5 = 32`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`val(x:int64)`; `32`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let INDCPA_BOT_TAC (n,p,d,f) aligns =
  if n <> p + 32 + f + d then failwith "INDCPA_BOT_TAC" else
  let num = mk_small_numeral in
  let dtm = vsubst [num(n - p),`k:num`]
    `delta = 32 - val(word_add (stackpointer:int64) (word k)) MOD 32`
  and etm = vsubst [num(n - p),`k:num`; num(d + f),`l:num`]
    `word_and (word_add stackpointer (word k))
              (word 18446744073709551584):int64 =
     word_add bot (word l)`
  and atms = map (fun c -> vsubst [num c,`c:num`]
                    `aligned 16 (word_add bot (word c):int64)`) aligns in
  ABBREV_TAC dtm THEN
  SUBGOAL_THEN `delta <= 32` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `bot = word_add (stackpointer:int64) (word delta)` THEN
  SUBGOAL_THEN (list_mk_conj(etm::atms)) STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INDCPA_ALIGNED_16] THEN
    MAP_EVERY EXPAND_TAC ["bot"; "delta"] THEN
    REWRITE_TAC[INDCPA_DELTA] THEN CONV_TAC BITBLAST_RULE;
    ALL_TAC];;

let INDCPA_NONOV_TAC size regions =
  FIRST_ASSUM(fun bth ->
    if is_eq(concl bth) && rhs(concl bth) = `bot:int64`
    then
      MAP_EVERY (fun r ->
        SUBGOAL_THEN
         (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                          mk_pair(`bot:int64`,mk_small_numeral size)),r))
         ASSUME_TAC THENL
         [REWRITE_TAC[SYM bth] THEN NONOVERLAPPING_TAC; ALL_TAC])
       regions
    else NO_TAC);;

let INDCPA_FRAME_TAC extra (n,p,d,f) =
  let mems = String.concat "; " (extra @
    [Printf.sprintf "memory :> bytes(bot:int64,%d)" (d + f)] @
    (if p = 0 then [] else
     [Printf.sprintf "memory :> bytes(word_add stackpointer (word %d),%d)"
        (n - p) p])) in
  let tm = parse_term(Printf.sprintf
   "MAYCHANGE [RSP] ,,
    (MAYCHANGE [RIP] ,,
     MAYCHANGE [RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11] ,,
     MAYCHANGE
      [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10;
       ZMM11; ZMM12; ZMM13; ZMM14; ZMM15; ZMM16; ZMM17; ZMM18; ZMM19; ZMM20;
       ZMM21; ZMM22; ZMM23; ZMM24; ZMM25; ZMM26; ZMM27; ZMM28; ZMM29; ZMM30;
       ZMM31] ,,
     MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
     MAYCHANGE [events]) ,,
    MAYCHANGE [%s]" mems) in
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC tm THEN
  CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["bot"; "delta"] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC];;

let INDCPA_NORM_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `bot:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let INDCPA_RSP_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `word_and (word_add stackpointer (word k))
                            (word 18446744073709551584):int64 = x`)
           (concl th)
    then RULE_ASSUM_TAC(fun th' ->
           if free_in `RSP` (concl th') then REWRITE_RULE[th] th' else th')
    else NO_TAC);;

let INDCPA_UNBOT_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `bot:int64`
    then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rhs(concl th) = `delta:num`
    then SUBST_ALL_TAC(SYM th) else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some other forms in the simulation: the values of YMM registers in a      *)
(* state, such as after a call, are named by INDCPA_YMMS_TAC (YMM1 and YMM2  *)
(* by INDCPA_YMM_TAC), so that the legacy SSE moves through the XMM          *)
(* registers, which keep their upper halves, have known results; a buffer at *)
(* bot + off is not null if the stack does not contain address 0             *)
(* (INDCPA_NONZERO_TAC, with n the size of the stack region in that          *)
(* hypothesis); and INDCPA_PTR_TAC evaluates the comparisons of two          *)
(* addresses in the frame, which decide the branches of the loops.           *)
(* ------------------------------------------------------------------------- *)

let INDCPA_YMMS_TAC st ns =
  MAP_EVERY (fun n ->
    let v = "ymm"^string_of_int n and r = parse_term("YMM"^string_of_int n) in
    ABBREV_TAC(mk_eq(mk_var(v,`:int256`),
      list_mk_comb(`read:(x86state,int256)component->x86state->int256`,
                   [r; mk_var(st,`:x86state`)])))) ns;;

let INDCPA_YMM_TAC st = INDCPA_YMMS_TAC st [1; 2];;

let INDCPA_NONZERO_TAC n off =
  MP_TAC(SPECL [`stackpointer:int64`; mk_small_numeral n;
                mk_binop `(+):num->num->num` `delta:num`
                 (mk_small_numeral off)] NONOVERLAPPING_ZERO_NONZERO) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `delta <= 32` THEN ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o
      REWRITE_RULE[ASSUME `word_add stackpointer (word delta):int64 = bot`] o
      REWRITE_RULE[WORD_ADD; WORD_ADD_ASSOC])];;

let INDCPA_PTR_SUB = prove
 (`!x:int64 a b. word_sub (word_add x (word a)) (word_add x (word b)) =
                 word_sub (word a) (word b)`,
  CONV_TAC WORD_RULE);;

let INDCPA_PTR_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `bot:int64` (concl th) &&
       can (find_term (fun t -> is_const t && name_of t = "word_sub"))
           (concl th)
    then CONV_RULE(REWRITE_CONV[INDCPA_PTR_SUB] THENC
                   DEPTH_CONV WORD_NUM_RED_CONV THENC NUM_REDUCE_CONV) th
    else th);;

(* ------------------------------------------------------------------------- *)
(* Specializations of the theorems for the matrix generation (transposed or  *)
(* not) and for getnoise_eta1_4x with a null fourth output.                  *)
(* ------------------------------------------------------------------------- *)

let INDCPA_GEN_MATRIX_SPEC th tr =
  let th1 = INST [tr,`transposed:int64`] (SPEC_ALL th) in
  let eq = mk_eq(mk_comb(`word_zx:int64->int32`,tr),`word 0:int32`) in
  let th2 = REWRITE_RULE[WORD_REDUCE_CONV eq] th1 in
  GENL [`a:int64`; `seed:int64`; `rho:byte list`; `k:num`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`] th2;;

let MAYCHANGE_DROP_BYTES_0 = prove
 (`!(c1:(x86state,num)component) c2 c3 c5 a:int64.
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
        `pc:num`; `stackpointer:int64`; `returnaddress:int64`] th2;;

(* ------------------------------------------------------------------------- *)
(* For the proofs of constant time and memory safety: the specializations of *)
(* the theorems of constant time and memory safety for the matrix generation *)
(* and for getnoise_eta1_4x with a null fourth output, as above, and the     *)
(* removal of the empty regions that the latter then has from the lists of   *)
(* the memory accesses of the calls.                                         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let SAFE_EXISTS_RULE rule th =
  let fe,body = dest_exists(concl th) in
  let bth = rule (ASSUME body) in
  CHOOSE (fe,th) (EXISTS (mk_exists(fe,concl bth),fe) bth);;

let INDCPA_GEN_MATRIX_SAFE_SPEC th tr =
  SAFE_EXISTS_RULE (fun bth ->
    let th1 = INST [tr,`transposed:int64`] (SPEC_ALL bth) in
    let eq = mk_eq(mk_comb(`word_zx:int64->int32`,tr),`word 0:int32`) in
    let th2 = REWRITE_RULE[WORD_REDUCE_CONV eq] th1 in
    GENL [`e:(uarch_event)list`; `a:int64`; `seed:int64`; `rho:byte list`;
          `k:num`; `pc:num`; `stackpointer:int64`;
          `returnaddress:int64`] th2) th;;

let INDCPA_GETNOISE_NULL_SAFE th =
  SAFE_EXISTS_RULE (fun bth ->
    let th1 = INST [`word 0:int64`,`r3:int64`] (SPEC_ALL bth) in
    let th2 = REWRITE_RULE[PAIRWISE; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES;
                           VAL_WORD_0; NONOVERLAPPING_MODULO_ZERO_LEN;
                           MAYCHANGE_DROP_BYTES_0] th1 in
    GENL [`e:(uarch_event)list`; `r0:int64`; `r1:int64`; `r2:int64`;
          `seed:int64`; `pc:num`; `stackpointer:int64`;
          `returnaddress:int64`] th2) th;;

let CONTAINED_REFL_64 = prove
 (`!(a:int64) n. contained (a,n) (a,n)`,
  REWRITE_TAC[contained; CONTAINED_MODULO_REFL; LE_REFL]);;

let CONTAINED_EMPTY_64 = prove
 (`!(a:int64) b n. contained (a,0) (b,n)`,
  REWRITE_TAC[contained; contained_modulo; LT]);;

let MEMACCESS_DROP_ZERO_RULE th =
  match strip_comb (concl th) with
    Const("memaccess_inbounds",_),[e;rl;wl] ->
      let keep l =
        let ps = dest_list l in
        mk_list(filter (fun p -> not (rand p = `0`)) ps,type_of(hd ps)) in
      let rl' = keep rl and wl' = keep wl in
      if rl' = rl && wl' = wl then th else
      let lem = ISPECL [e; rl; rl'; wl; wl'] MEMACCESS_INBOUNDS_CONTAINED in
      let side = prove(lhand(concl lem),
        REWRITE_TAC[ALL; EX; CONTAINED_REFL_64; CONTAINED_EMPTY_64]) in
      MP (MP lem side) th
  | _ -> failwith "MEMACCESS_DROP_ZERO_RULE";;

let MEMACCESS_DROP_ZERO_TAC =
  RULE_ASSUM_TAC(fun th ->
    try MEMACCESS_DROP_ZERO_RULE th with Failure _ -> th);;

(* ------------------------------------------------------------------------- *)
(* ASSUME_CALLEE_SAFETY_TAILED_TAC with the arguments of the theorem rotated *)
(* by specialization rather than by MESON, which is too slow for the general *)
(* theorems for getnoise.                                                    *)
(* ------------------------------------------------------------------------- *)

let ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC =
  let append_lemma = MESON[SAFETY_APPEND_EXISTS]
    `(forall (e:((A)address_uarch_event)list). P e) <=>
      (forall e_tail e. P (APPEND e_tail e))` in
  fun (safety_th:thm) (name:string) ->
    let safety_th' = ONCE_REWRITE_RULE[append_lemma] safety_th in
    let safety_th'' = SAFE_EXISTS_RULE (fun bth ->
      let args,_ = strip_forall(concl bth) in
      GENL ((tl args) @ [hd args]) (SPECL args bth)) safety_th' in
    ASSUME_CALLEE_SAFETY_TAC safety_th'' name;;
