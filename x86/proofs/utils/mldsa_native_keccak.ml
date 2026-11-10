(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of mldsa-native's Keccak code that do not depend on *)
(* the build, as in arm/proofs/utils/mldsa_native_keccak.ml, with the tools  *)
(* for byte arrays, Keccak states as 1600-bit words and 32-bit arguments     *)
(* that the AArch64 proofs take from arm/proofs/utils/mlkem_native_image.ml, *)
(* here for the x86 state, as in the x86 proofs of mlkem-native, and those   *)
(* of the x86 proofs of mlkem-native for the memset that gcc inlines with    *)
(* REP STOSQ, which the AArch64 code does not use.                           *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native.ml";;

let READ_MEMORY_BYTES_SNOC = prove
 (`!x:int64 n s:x86state.
        read (memory :> bytes(x,n + 1)) s =
        read (memory :> bytes(x,n)) s +
        2 EXP (8 * n) * val(read (memory :> bytes8(word_add x (word n))) s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; READ_BYTES_BYTES8]);;

(* ------------------------------------------------------------------------- *)
(* Byte arrays. As in common/fips202.ml, the contents of a byte array are    *)
(* given as a number n, and READ_MEMORY_BYTES8_OF_NUM gives its bytes;       *)
(* READ_MEMORY_BYTES_OF_BYTES8 gives the array from its bytes.               *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES8_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k < m
        ==> read (memory :> bytes8(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 256)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP (8 * 1)`; READ_BYTES_DIV;
              READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_OF_BYTES8 = prove
 (`!a:int64 n x s:x86state.
        (!j. j < n
             ==> read (memory :> bytes8(word_add a (word j))) s =
                 word((x DIV 2 EXP (8 * j)) MOD 256))
        ==> read (memory :> bytes(a,n)) s = x MOD 2 EXP (8 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ADD1; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
              READ_BYTES_BYTES8] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:x86state`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `j < n ==> j < SUC n`];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[LT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL; LEFT_ADD_DISTRIB; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; MOD_MULT_MOD] THEN ARITH_TAC);;

let WORD_VAL_MOD_256 = prove
 (`!x:N word. word (val x MOD 256):byte = word_zx x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[GSYM DIMINDEX_8; WORD_MOD_SIZE; word_zx]);;

(* ------------------------------------------------------------------------- *)
(* A word in memory as the number of its bytes, and the case of a Keccak     *)
(* state of 200 bytes. KECCAK_STATE_WBYTES_TAC sv restates the fact that the *)
(* bytes of a state are val sv in the wbytes form, for a call.               *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_WBYTES_VAL = prove
 (`!a:int64 (x:N word) s:x86state.
        read (memory :> wbytes a) s = x <=>
        read (memory :> bytes(a,dimindex(:N) DIV 8)) s = val x`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM VAL_EQ] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES]);;

let READ_MEMORY_WBYTES_1600 =
  CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC ONCE_DEPTH_CONV NUM_DIV_CONV)
   (INST_TYPE [`:1600`,`:N`] READ_MEMORY_WBYTES_VAL);;

let KECCAK_STATE_WBYTES_TAC sv =
  let pat = subst [sv,`S:1600 word`]
   `read (memory :> bytes (a,200)) s = val(S:1600 word)` in
  FIRST_ASSUM(fun th ->
    if can (term_match [sv] pat) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Unsigned 32-bit arguments word n, as the code zero-extends them, and a    *)
(* 32-bit argument on the stack, which the caller stores as a 64-bit word:   *)
(* STACK_ARG32_TAC a gives the bytes32 at a from the fact for its bytes64.   *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_32_SMALL = prove
 (`!n. n < 2 EXP 32
       ==> word_zx(word_zx(word n:int64):int32):int64 = word n /\
           val(word_zx(word n:int64):int32) = n /\
           word_zx(word n:int32):int64 = word n`,
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN TRY(ONCE_REWRITE_TAC[GSYM VAL_EQ]) THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `n < 4294967296 ==> n < 18446744073709551616`]);;

let ARGS_32_TAC ns =
  MAP_EVERY (fun n ->
    MP_TAC(SPEC n WORD_ZX_32_SMALL) THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) ns;;

let READ_MEMORY_BYTES32_OF_BYTES64 = prove
 (`!a:int64 n s:x86state.
        read (memory :> bytes64 a) s = word n /\ n < 2 EXP 32
        ==> read (memory :> bytes32 a) s = word n`,
  REPEAT GEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[BYTES64_WBYTES; BYTES32_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; VAL_WORD; DIMINDEX_64; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `n < 4294967296 ==> n < 18446744073709551616`] THEN
  DISCH_THEN(MP_TAC o C AP_THM `2 EXP (8 * 4)` o AP_TERM `(MOD)`) THEN
  REWRITE_TAC[READ_BYTES_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT]);;

let STACK_ARG32_TAC a =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes64",_),aa))),_)),
           Comb(Const("word",_),n)) when aa = a ->
        SUBGOAL_THEN (mk_binop `(<):num->num->bool` n `2 EXP 32`)
         (fun lth -> ASSUME_TAC
            (MATCH_MP READ_MEMORY_BYTES32_OF_BYTES64 (CONJ th lth))) THENL
         [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC]
    | _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Memory cleared by REP STOSQ, as in the x86 proofs of mlkem-native. When   *)
(* st is not known to be aligned, gcc inlines a memset of n bytes at st, for *)
(* n a multiple of 8, as zero quadword stores at st and st + n - 8 and a REP *)
(* STOSQ of n DIV 8 - 1 quadwords from the first multiple of 8 above st,     *)
(* which is st + (8 - val st MOD 8) by MEMSET_ALIGN_ADDR. Before the REP     *)
(* STOSQ, MEMSET_PREP_TAC evaluates the count, which is the same for any st, *)
(* puts the address in that form, and splits the two quadwords into their    *)
(* parts outside the memory that it clears, so that the simulation keeps     *)
(* them. MEMSET_STEP_TAC then steps the REP STOSQ, keeping the fact for the  *)
(* memory that it clears, which the simulation does not simplify, and        *)
(* MEMSET_DONE_TAC puts the three parts together. As the ABI requires on     *)
(* entry, the direction flag DF must be clear.                               *)
(* ------------------------------------------------------------------------- *)

let MEMSET_ALIGN_ADDR = prove
 (`!st:int64.
        word_and (word_add st (word 8)) (word 18446744073709551608) =
        word_add st (word (8 - val st MOD 8))`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(st:int64) MOD 8 = val(word_and st (word 7):int64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `7 = 2 EXP 3 - 1`] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 3 = 8`];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_and st (word 7):int64) <= 8` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`st:int64`; `word 7:int64`]
      (CONJUNCT2 VAL_WORD_AND_LE)) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (INST_TYPE [`:64`,`:N`] WORD_SUB2) o
    INST [`8`,`x:num`] o
    check (fun th -> concl th = `val(word_and st (word 7):int64) <= 8`)) THEN
  REWRITE_TAC[WORD_VAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

(*** Parts of bytes in memory, and of a quadword that is zero ***)

let READ_MEMORY_BYTES_SUB = prove
 (`!a:int64 n x k l s:x86state.
        read (memory :> bytes(a,n)) s = x /\ k + l <= n
        ==> read (memory :> bytes(word_add a (word k),l)) s =
            (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES64_ZERO_SPLIT = prove
 (`!a:int64 k s:x86state.
        read (memory :> bytes64 a) s = word 0 /\ k <= 8
        ==> read (memory :> bytes(a,k)) s = 0 /\
            read (memory :> bytes(word_add a (word k),8 - k)) s = 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; BYTES64_WBYTES] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`a:int64`; `8`; `0`; `0`; `k:num`; `s:x86state`]
      READ_MEMORY_BYTES_SUB);
    MP_TAC(SPECL [`a:int64`; `8`; `0`; `k:num`; `8 - k`; `s:x86state`]
      READ_MEMORY_BYTES_SUB)] THEN
  ASM_REWRITE_TAC[WORD_ADD_0; DIV_0; MOD_0] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;
(*** The three parts of the n bytes, and the address of the last ***)

let MEMSET_COMBINE = prove
 (`!st:int64 n k s:x86state.
        k < 8 /\ 8 <= n /\
        read (memory :> bytes(st,8 - k)) s = 0 /\
        read (memory :> bytes(word_add st (word(8 - k)),n - 8)) s = 0 /\
        read (memory :> bytes(word_add st (word(n - k)),k)) s = 0
        ==> read (memory :> bytes(st,n)) s = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n = (8 - k) + (n - 8) + k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; GSYM WORD_ADD_ASSOC;
              GSYM WORD_ADD] THEN
  SUBGOAL_THEN `(8 - k) + (n - 8) = n - k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let MEMSET_HIGH_ADDR = prove
 (`!st:int64 n k.
        k < 8 /\ 8 <= n
        ==> word_add (word_add st (word(n - 8))) (word(8 - k)) =
            word_add st (word(n - k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(*** The count of quadwords, the same for any st, by bit-blasting ***)

let MEMSET_COUNT_RULE th =
  let e = rand(concl th) in
  let st = lhand(lhand(find_term (can (term_match []
             `word_and (word_add x (word 8))
                       (word 18446744073709551608):int64`))
             e)) in
  let c = rhs(concl(WORD_REDUCE_CONV(subst [`word 0:int64`,st] e))) in
  TRANS th (BITBLAST_RULE(mk_eq(e,c)));;
(*** The preparation for the REP STOSQ, in the state before it ***)

let MEMSET_PREP_TAC (asl,w) =
  let mask = `word 18446744073709551608:int64` in
  let is_rcx th = can (term_match [] `read RCX s = x`) (concl th) &&
                  free_in mask (concl th)
  and is_rdi th = can (term_match []
    `read RDI s = word_and (word_add x (word 8)) (word 18446744073709551608)`)
    (concl th) in
  let rdi = snd(find (is_rdi o snd) asl) in
  let st = lhand(lhand(rand(concl rdi))) in
  let kt = mk_binop `MOD` (mk_comb(`val:int64->num`,st)) `8` in
  let dt = mk_binop `(-):num->num->num` `8` kt in
  let ltth = SPECL [mk_comb(`val:int64->num`,st); `8`] MOD_LT_EQ in
  let kth = REWRITE_RULE[ARITH_EQ] ltth in
  let dleth = ARITH_RULE(mk_binop `(<=):num->num->bool` dt `8`) in
  let split th =
    if can (term_match [] `read (memory :> bytes64 a) s = word 0`) (concl th)
    then
      let a = rand(rand(lhand(lhand(concl th)))) in
      let spl = MATCH_MP READ_MEMORY_BYTES64_ZERO_SPLIT (CONJ th dleth) in
      if a = st then [CONJUNCT1 spl]
      else if is_comb a && is_comb(rator a) && lhand a = st then
        let m = dest_small_numeral(rand(rand a)) in
        let hth = MP (SPECL [st; mk_small_numeral(m + 8); kt] MEMSET_HIGH_ADDR)
                     (CONJ kth (ARITH_RULE(mk_binop `(<=):num->num->bool`
                                  `8` (mk_small_numeral(m + 8))))) in
        let hth' = CONV_RULE(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
                     NUM_REDUCE_CONV)))) hth in
        let lth = ARITH_RULE(mk_eq(mk_binop `(-):num->num->num` `8` dt,kt)) in
        [REWRITE_RULE[hth'; lth] (CONJUNCT2 spl)]
      else []
    else [] in
  let news = itlist (fun (_,th) l -> split th @ l) asl [] in
  (RULE_ASSUM_TAC
    (fun th -> if is_rcx th then MEMSET_COUNT_RULE th else th) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[MEMSET_ALIGN_ADDR]) THEN
   ASSUME_TAC kth THEN MAP_EVERY ASSUME_TAC news) (asl,w);;

(*** The memory cleared, from the fact that the simulation leaves ***)

let MEMSET_RW_CONV =
  let memth = REWRITE_RULE[VALID_COMPONENT_CONV `valid_component memory`]
   (ISPEC `memory:(x86state,int64->byte)component`
     READ_WRITE_VALID_COMPONENT) in
  let bth = REWRITE_RULE[DIMINDEX_64]
   (INST_TYPE [`:64`,`:A`] READ_WRITE_BYTES) in
  REWRITE_CONV[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE; memth] THENC
  (fun tm -> let th = PART_MATCH (lhand o rand) bth tm in
             MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) THENC
  REWRITE_CONV[MULT_CLAUSES; NSUM_0; MOD_0];;

(*** Step the REP STOSQ instruction n, keeping the fact for the memory it
 *** clears, which the simulation does not simplify
 ***)

let MEMSET_STEP_TAC execth n =
  let sname = "s" ^ string_of_int n in
  let sv = mk_var(sname,`:x86state`) in
  X86_VSTEPS_TAC execth [n] THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read (memory :> bytes(a,k)) s`) (lhand c)
       && rand(lhand c) = sv &&
       can (term_match [] `read (memory :> bytes(a,k)) (write c y s)`) (rand c)
    then CONV_RULE(RAND_CONV MEMSET_RW_CONV) th else th) THEN
  DISCARD_OLDSTATE_TAC sname;;

(*** The n bytes at st cleared in state sname, from the three parts ***)

let MEMSET_DONE_TAC st n sname =
  let sv = mk_var(sname,`:x86state`) in
  let kt = mk_binop `MOD` (mk_comb(`val:int64->num`,st)) `8` in
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
    (SPECL [st; mk_small_numeral n; kt; sv] MEMSET_COMBINE)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;
