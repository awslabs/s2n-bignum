(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tactics for the K-PKE and ML-KEM functions of a build in which the        *)
(* polyvec wrappers are inlined, so that the function calls the kernel for   *)
(* each polynomial itself (see polyvec_inline.ml). The proofs of these       *)
(* functions in the gcc 12 -O2 build (with utils/mlkem_native_indcpa.ml)     *)
(* use the postconditions of the polyvec functions; here they are proved     *)
(* from those of the calls of the kernels, at the state after the last call, *)
(* so that the rest of the proof is unchanged. The buffers are on the stack, *)
(* at numeric offsets from the stack pointer:                                *)
(*                                                                           *)
(*  - POLYVEC_GHOST_SPLIT_TAC v base k s: from the ghost v for the contents  *)
(*    of the 256 * k coefficients at stackpointer + base, the inputs of the  *)
(*    k calls, polynomial j at base + 512 * j being \i. v(256 * j + i);      *)
(*  - POLYVEC_INLINE_JOIN_TAC k tm: the postcondition tm of the polyvec      *)
(*    function (one of the PV_*_POST terms below) from those of the calls.   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/polyvec_inline.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** Offsets of the stack pointer in one normal form: word_add (word_add
     stackpointer (word m)) (word n) is word_add stackpointer (word(m + n)),
     and the offset is in the normal form of NUM_NORMALIZE_CONV ***)

let POLYVEC_SP_CANON_CONV =
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [WORD_RULE `word_add (word_add (stackpointer:int64) (word m)) (word n) =
               word_add stackpointer (word(m + n))`] THENC
  ONCE_DEPTH_CONV INDCPA_CANON_CONV;;

(*** The addresses at offsets from the stack pointer in the assumptions as
     the simulation gives them (e.g. after a split of a byte array) ***)

let INLINE_SP_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

(*** After a lemma for a loop that addresses a polynomial with a base and an
     offset, its result is at word_add (word_add stackpointer (word m))
     (word(n + t)) for numerals m and n; fold it into word_add stackpointer
     (word((m + n) + t)), the form of the preconditions of the kernels ***)

let INLINE_SP_FOLD_TAC =
  let th = WORD_RULE
   `word_add (word_add (stackpointer:int64) (word m)) (word(n + t)) =
    word_add stackpointer (word((m + n) + t))` in
  RULE_ASSUM_TAC(fun th' ->
    if free_in `stackpointer:int64` (concl th')
    then CONV_RULE(GEN_REWRITE_CONV TOP_DEPTH_CONV [th] THENC
                   DEPTH_CONV NUM_ADD_CONV) th'
    else th');;

(*** The inputs of the calls, from a ghost ***)

let POLYVEC_GHOST_SPLIT_TAC v base k s =
  MAP_EVERY (fun j ->
    let idx = if j = 0 then "i" else Printf.sprintf "%d + i" (256 * j) in
    INDCPA_MEMFACT_TAC(parse_term(Printf.sprintf
     "!i. i < 256 ==> read (memory :> bytes16 (word_add stackpointer \
      (word(%d + 2 * i)))) (%s:armstate) = (%s:num->int16)(%s)"
     (base + 512 * j) s v idx))) (0--(k-1));;

(*** The input of polynomial j as a lemma for a loop that addresses it with
     a base and an offset, e.g. T + 512 + 2 * i, expects it after the
     normalization of the simulation: word_add (word_add stackpointer
     (word base)) (word(off + 2 * i)) ***)

let POLYVEC_GHOST_OFF_TAC v base off j s =
  let idx = if j = 0 then "i" else Printf.sprintf "%d + i" (256 * j) in
  let tm = parse_term(Printf.sprintf
   "!i. i < 256 ==> read (memory :> bytes16 (word_add (word_add stackpointer \
    (word %d)) (word(%d + 2 * i)))) (%s:armstate) = (%s:num->int16)(%s)"
   base off s v idx) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC v THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

(*** Drop all the facts !i. i < m ==> read ... = v(...) other than the ghost
     itself, for which m = n, after the calls that use them ***)

let POLYVEC_GHOST_DROP_ALL_TAC v n =
  let nt = mk_small_numeral n in
  REPEAT(FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(i,Comb(Comb(Const("==>",_),
        Comb(Comb(Const("<",_),i'),m)),
        Comb(Comb(Const("=",_),l),r))))
      when i' = i && m <> nt &&
           (match strip_comb r with (Var(v',_),_) -> v' = v | _ -> false) &&
           can (find_term (fun t -> match t with Const("bytes16",_) -> true
                                               | _ -> false)) l
      -> ALL_TAC
    | _ -> NO_TAC));;

(*** Drop those facts after the calls (in whichever state they have been
     carried to), since they would be found by the tactics that look for
     the ghost itself ***)

let POLYVEC_GHOST_DROP_TAC v base k =
  let tms = map (fun j ->
    let idx = if j = 0 then "i" else Printf.sprintf "%d + i" (256 * j) in
    parse_term(Printf.sprintf
     "!i. i < 256 ==> read (memory :> bytes16 (word_add stackpointer \
      (word(%d + 2 * i)))) (ss:armstate) = (%s:num->int16)(%s)"
     (base + 512 * j) v idx)) (0--(k-1)) in
  let sv = `ss:armstate` in
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if exists (fun p -> can (term_match (subtract (frees p) [sv]) p) c) tms
    then ALL_TAC else NO_TAC));;

(*** 32-byte seeds as two 128-bit words, as loaded and stored with LDP and
     STP of Q registers ***)

let INLINE_BYTES128_HALVES = prove
 (`!a:int64 n s:armstate.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let INLINE_BYTES_32_OF_HALVES = prove
 (`!a:int64 n s:armstate.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `32 = 16 + 16`; READ_BYTES_COMBINE] THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory s`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`word_add a (word 16):int64`; `16`; `read memory s`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n DIV 340282366920938463463374607431768211456 <
                340282366920938463463374607431768211456`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [UNDISCH_TAC `n < 2 EXP 256` THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MESON_TAC[DIVISION_SIMP; ADD_SYM; MULT_SYM]]);;

(*** The 33 bytes of a seed followed by one byte, as the input of SHA3-512
     (the seed and k) or of SHAKE256 (the seed and a nonce) ***)

let INLINE_SEED_INPUT = prove
 (`!a:int64 (d:byte list) c s:armstate.
        LENGTH d = 32 /\ c < 256 /\
        read (memory :> bytes128 a) s =
        word(num_of_bytelist d MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(num_of_bytelist d DIV 2 EXP 128) /\
        read (memory :> bytes8(word_add a (word 32))) s = word c
        ==> LENGTH(APPEND d [word c:byte]) = 33 /\
            read (memory :> bytes(a,33)) s =
            num_of_bytelist(APPEND d [word c])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes(a,32)) s = num_of_bytelist d`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INLINE_BYTES_32_OF_HALVES THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `d:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; NUM_OF_BYTELIST_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `33 = 32 + 1`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
  ASM_REWRITE_TAC[num_of_bytelist; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

(*** The GOT entries in the form of the preconditions of callees, by the
     names of the layout ***)

let INLINE_GOT_TAC =
  let pat n = subst [n,`n:num`]
   `read (memory :> bytes64 (word_add (word pc) (word n):int64)) s =
    (g:int64)` in
  MAP_EVERY (fun n ->
    TRY(FIRST_ASSUM(fun th ->
      if can (term_match [] (pat n)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC)))
   [`got_stack_chk_guard:num`; `got_memset:num`; `got_memcpy:num`];;

(*** The postcondition of the polyvec function from those of the calls ***)

let POLYVEC_INLINE_JOIN_TAC k ths tm =
  let jvar = fst(dest_forall tm) in
  let byj = (jvar = mk_var("j",`:num`)) in
  let conv = REWRITE_CONV(o_DEF::ths) THENC DEPTH_CONV BETA_CONV THENC
             POLYVEC_SP_CANON_CONV in
  SUBGOAL_THEN tm (ASSUME_TAC o CONV_RULE POLYVEC_SP_CANON_CONV) THENL
   [(if byj then REWRITE_TAC[IMP_CONJ] THEN POLYVEC_CASES_TAC
     else POLYVEC_JOIN_TAC k THEN REPEAT CONJ_TAC THEN
          X_GEN_TAC (mk_var("i",`:num`)) THEN DISCH_TAC) THEN
    RULE_ASSUM_TAC(CONV_RULE conv) THEN CONV_TAC conv THEN
    (if byj then ASM_REWRITE_TAC[] else ASM_SIMP_TAC ths);
    ALL_TAC];;

(*** The postcondition of polyvec_tobytes for k polynomials, from the list
     l (a term) at r (a term), from those of the calls with the parts
     SUB_LIST(256 * j,256) l of l ***)

let POLYVEC_TOBYTES_JOIN_TAC k r l s =
  let kt = mk_small_numeral k in
  let tm = list_mk_comb(`\(k:num) (r:int64) (l:int16 list) (s:armstate).
     LENGTH l = 256 * k /\ ALL (\x. val x < 4096) l
     ==> read(memory :> bytes(r,384 * k)) s =
         num_of_wordlist (MAP word_zx l:(12 word)list)`,[kt; r; l; s]) in
  let is_part th =
    is_imp(concl th) &&
    can (find_term (fun t -> t = l)) (lhand(concl th)) &&
    can (find_term (fun t -> match t with Const("SUB_LIST",_) -> true
                                        | _ -> false)) (lhand(concl th)) in
  let tm' = rhs(concl((TOP_DEPTH_CONV BETA_CONV THENC
                       ONCE_DEPTH_CONV NUM_MULT_CONV) tm)) in
  SUBGOAL_THEN tm' ASSUME_TAC THENL
   [STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(fun th ->
      if is_part th then
        MP_TAC th THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN CONV_TAC NUM_REDUCE_CONV THEN
          MATCH_MP_TAC ALL_SUB_LIST_GEN THEN ASM_REWRITE_TAC[];
          DISCH_TAC]
      else NO_TAC)) THEN
    MP_TAC(ISPECL [r; kt; l; s] POLYVEC_TOBYTES_JOIN_GEN) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    RULE_ASSUM_TAC(CONV_RULE POLYVEC_SP_CANON_CONV) THEN
    CONV_TAC POLYVEC_SP_CANON_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The postconditions of the gcc 12 -O2 polyvec functions, for k
     polynomials at the address a (a term as a string), the input x, in the
     state s ***)

let PV_FROMBYTES_POST k a n s =
  parse_term(Printf.sprintf
   "!i. i < %d
        ==> read(memory :> bytes16(word_add (%s:int64) (word(2 * i))))
             (%s:armstate) =
            word((%s DIV 2 EXP (12 * i)) MOD 2 EXP 12)" (256 * k) a s n);;

let PV_NTT_POST k a x s =
  parse_term(Printf.sprintf
   "!j. j < %d /\\
        (!i. i < 256 ==> abs(ival((%s:num->int16)(256 * j + i))) <= &8191)
        ==> !i. i < 256
                ==> let zi =
                      read(memory :> bytes16
                       (word_add (%s:int64) (word(512 * j + 2 * i))))
                       (%s:armstate)
                    in (ival zi ==
                        forward_ntt (\\n. ival(%s(256 * j + n))) i)
                       (mod &3329) /\\
                       abs(ival zi) <= &23594" k x a s x);;

let PV_MULCACHE_POST k dst x s =
  parse_term(Printf.sprintf
   "!j. j < %d
        ==> !i. i < 128
                ==> let z_i =
                      read(memory :> bytes16
                       (word_add (%s:int64) (word(256 * j + 2 * i))))
                       (%s:armstate)
                    in (ival z_i ==
                        mulcache (\\n. ival((%s:num->int16)(256 * j + n))) i)
                       (mod &3329) /\\
                       abs(ival z_i) <= &3328" k dst s x);;

let PV_INVNTT_POST k a x s =
  parse_term(Printf.sprintf
   "!j. j < %d
        ==> !i. i < 256
                ==> let zi =
                      read(memory :> bytes16
                       (word_add (%s:int64) (word(512 * j + 2 * i))))
                       (%s:armstate)
                    in (ival zi ==
                        inverse_ntt (\\n. ival((%s:num->int16)(256 * j + n))) i)
                       (mod &3329) /\\
                       abs(ival zi) <= &26624" k a s x);;

let PV_REDUCE_POST k a x s =
  parse_term(Printf.sprintf
   "!i. i < %d
        ==> ival(read(memory :> bytes16
                  (word_add (%s:int64) (word(2 * i)))) (%s:armstate)) =
            ival(((%s):num->int16) i) rem &3329" (256 * k) a s x);;

let PV_TOMONT_POST k a x s =
  parse_term(Printf.sprintf
   "!i. i < %d
        ==> let z_i = read(memory :> bytes16
                       (word_add (%s:int64) (word(2 * i)))) (%s:armstate) in
            (ival z_i == tomont_3329 (ival o (%s:num->int16)) i) (mod &3329) /\\
            abs(ival z_i) <= &3328" (256 * k) a s x);;

let PV_ADD_POST k r x y s =
  parse_term(Printf.sprintf
   "!i. i < %d
        ==> read(memory :> bytes16(word_add (%s:int64) (word(2 * i))))
             (%s:armstate) =
            word_add ((%s:num->int16) i) ((%s:num->int16) i)"
   (256 * k) r s x y);;
