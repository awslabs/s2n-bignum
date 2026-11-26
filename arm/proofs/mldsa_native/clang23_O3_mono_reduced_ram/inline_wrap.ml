(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the API wrappers of mldsa-native in the clang 23  *)
(* -O3 image (see utils/mldsa_native_wrap.ml for those of the gcc images).   *)
(* Clang aligns the stack pointer itself, to 32 bytes, after saving its      *)
(* registers, and inlines the prefix 0 || ctxlen || ctx of pure ML-DSA into  *)
(* the wrappers of signature and verify as two byte stores and a call of     *)
(* memcpy, and the zeroing of its buffers as stores of zero vectors.         *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native_wrap.ml";;
needs "arm/proofs/utils/mldsa_native_prefix.ml";;

(* ------------------------------------------------------------------------- *)
(* The ORR of the address of the buffer with 2 is an addition if the address *)
(* is a multiple of 32.                                                      *)
(* ------------------------------------------------------------------------- *)

let MLD_CLANG_OR2 = prove
 (`!x:int64. aligned 32 x ==> word_or x (word 2) = word_add x (word 2)`,
  GEN_TAC THEN REWRITE_TAC[MLD_WRAP_ALIGNED_16_32] THEN
  DISCH_THEN(fun th -> MP_TAC th) THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;


(* ------------------------------------------------------------------------- *)
(* The bytes 0, ctxlen and ctx at b are the prefix of pure ML-DSA, which the *)
(* callees read as a number (see prepare_domain_separation_prefix).          *)
(* ------------------------------------------------------------------------- *)

let MLD_CLANG_PREFIX_MEM = prove
 (`!(b:int64) ctxlen C (s:armstate).
        ctxlen <= 255 /\
        read (memory :> bytes8 b) s = word 0 /\
        read (memory :> bytes8 (word_add b (word 1))) s = word ctxlen /\
        read (memory :> bytes(word_add b (word 2),ctxlen)) s = C
        ==> read (memory :> bytes(b,2 + ctxlen)) s =
            num_of_bytelist
             (mld_domain_separation_prefix 0 (bytelist_of_num ctxlen C) [])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `ctxlen:num` MLD_PREFIX_VAL_BYTE) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  REWRITE_TAC[mld_domain_separation_prefix; LENGTH_BYTELIST_OF_NUM;
              num_of_bytelist] THEN
  REWRITE_TAC[MLD_PREFIX_BYTES_COMBINE; MLD_PREFIX_BYTES2] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `C < 256 EXP ctxlen` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`word_add (b:int64) (word 2)`; `ctxlen:num`; `s:armstate`; `C:num`] MLD_PREFIX_READ_BYTES_BOUND) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_MULT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NUM_OF_BYTELIST_OF_NUM_EQ; VAL_WORD_0] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The test CMP x4, #0xff; B.LS on the length ctxlen of the context, which   *)
(* the simulation leaves as a condition on the flags, becomes ctxlen > 255.  *)
(* ------------------------------------------------------------------------- *)

let MLD_CLANG_CTX_CMP = prove
 (`!c. c < 2 EXP 64
       ==> val(word c:int64) = c /\
           ((val(word_sub (word c:int64) (word 255)) = 0) <=> c = 255) /\
           (255 <= c /\ ~(c = 255) <=> 255 < c)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word c:int64) = c` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN EQ_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    ARITH_TAC]);;

let MLD_CLANG_CTX_TAC =
  MP_TAC(SPEC `ctxlen:num` MLD_CLANG_CTX_CMP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

(* ------------------------------------------------------------------------- *)
(* The prefix at the stack pointer of the state s in the assumption          *)
(* read SP s = stackpointer + K (K a numeral) is that of pure ML-DSA, as the *)
(* callees read it: the bytes 0 and ctxlen and the context at sp + 2. The    *)
(* three facts about the memory must be assumptions in the form with         *)
(* stackpointer + K, + (K + 1) and + (K + 2).                                *)
(* ------------------------------------------------------------------------- *)

let MLD_CLANG_PREFIX_MEM2 = prove
 (`!(b:int64) b1 b2 ctxlen C (s:armstate).
        ctxlen <= 255 /\ b1 = word_add b (word 1) /\ b2 = word_add b (word 2) /\
        read (memory :> bytes8 b) s = word 0 /\
        read (memory :> bytes8 b1) s = word ctxlen /\
        (ctxlen = 0 \/ read (memory :> bytes(b2,ctxlen)) s = C)
        ==> read (memory :> bytes(b,2 + ctxlen)) s =
            num_of_bytelist
             (mld_domain_separation_prefix 0 (bytelist_of_num ctxlen C) [])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `b1:int64`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `b2:int64`)) THENL
   [MP_TAC(SPECL [`b:int64`; `0`; `0`; `s:armstate`] MLD_CLANG_PREFIX_MEM) THEN
    ASM_REWRITE_TAC[CONJUNCT1 bytelist_of_num; READ_MEMORY_BYTES_TRIVIAL] THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] ;
    MATCH_MP_TAC MLD_CLANG_PREFIX_MEM THEN ASM_REWRITE_TAC[]]);;

(*** The byte that STRB stores for the length ctxlen in x4 ***)

let MLD_CLANG_BYTE_ZX = prove
 (`!n. word_zx(word_zx(word n:int64):int32):byte = word n`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8;
              DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLD_CLANG_PREFIX_OFS_TAC d =
  let pat = `read SP (s:armstate) = word_add stackpointer (word (k:num))` in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(is_eq c && can (term_match [] pat) c) then failwith "no" else
    let s = rand(lhand c) and k = dest_small_numeral(rand(rand(rhs c))) + d in
    let addr n = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                         mk_comb(`word:num->int64`,mk_small_numeral n)) in
    MP_TAC(ISPECL [addr k; addr (k + 1); addr (k + 2); `ctxlen:num`; `C:num`; s]
                  MLD_CLANG_PREFIX_MEM2) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; CONV_TAC WORD_RULE; CONV_TAC WORD_RULE;
        ASM_REWRITE_TAC[MLD_CLANG_BYTE_ZX]; ASM_REWRITE_TAC[MLD_CLANG_BYTE_ZX];
        ASM_REWRITE_TAC[MLD_CLANG_BYTE_ZX]];
      DISCH_THEN ASSUME_TAC]);;

let MLD_CLANG_PREFIX_TAC = MLD_CLANG_PREFIX_OFS_TAC 0;;

(* ------------------------------------------------------------------------- *)
(* The bounds on the stack pointer that the callees that probe the stack     *)
(* assume, nc <= val sp /\ val sp < 2 EXP 63 for the stack pointer          *)
(* sp = stackpointer + k inside the frame of n bytes, from those of the      *)
(* caller for stackpointer + n (MLD_CLANG_SPVAL_TAC n k nc).                  *)
(* ------------------------------------------------------------------------- *)

let MLD_CLANG_VAL_ADD = prove
 (`!(sp:int64) n m. n <= val(word_add sp (word n):int64) /\ val(word_add sp (word n):int64) < 2 EXP 63 /\ m <= n
    ==> val(word_add sp (word m):int64) = val sp + m /\ val sp + m < 2 EXP 63`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n < 2 EXP 63` ASSUME_TAC THENL [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `m < 2 EXP 63` ASSUME_TAC THENL [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word n:int64) = n /\ val(word m:int64) = m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`sp:int64`; `word n:int64`] VAL_WORD_ADD_CASES) THEN
  MP_TAC(ISPECL [`sp:int64`; `word m:int64`] VAL_WORD_ADD_CASES) THEN
  MP_TAC(SPEC `sp:int64` VAL_BOUND_64) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_64]) THEN
  REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `val(sp:int64) + n < 2 EXP 64` THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    UNDISCH_TAC `n <= val(word_add sp (word n):int64)` THEN
    UNDISCH_TAC `val(word_add sp (word n):int64) < 2 EXP 63` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let MLD_CLANG_SPVAL_TAC n k nc =
  let tn = mk_small_numeral n and tk = mk_small_numeral k
  and tc = mk_small_numeral nc in
  SUBGOAL_THEN
   (subst [tc,`nc:num`; tk,`k:num`]
     `nc <= val(word_add stackpointer (word k):int64) /\
      val(word_add stackpointer (word k):int64) < 2 EXP 63`)
   ASSUME_TAC THENL
   [SUBGOAL_THEN
     (subst [tn,`n:num`] `n <= val(word_add stackpointer (word n):int64)`)
     ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`stackpointer:int64`; tn; tk] MLD_CLANG_VAL_ADD) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC; CONV_TAC NUM_REDUCE_CONV];
      ALL_TAC] THEN
    MP_TAC(SPECL [`stackpointer:int64`; tn; tn] MLD_CLANG_VAL_ADD) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC; CONV_TAC NUM_REDUCE_CONV];
      ALL_TAC] THEN
    STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC];;

let MLD_CLANG_CALL_FACTS_TAC n nc =
  let pat = `read SP (s:armstate) = word_add stackpointer (word (k:num))` in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(is_eq c && can (term_match [] pat) c) then failwith "no" else
    let k = dest_small_numeral(rand(rand(rhs c))) in
    MLD_CLANG_SPVAL_TAC n k 32768 THEN MLD_CLANG_SPVAL_TAC n (k - nc) 0);;

(* ------------------------------------------------------------------------- *)
(* The end of a path of a wrapper: the postcondition, whose result may still *)
(* have the length 2 + 0 of an empty context or the conversion of 0.        *)
(* ------------------------------------------------------------------------- *)

let MLD_CLANG_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[ADD_CLAUSES; WORD_ZX_0] THEN NO_TAC) THEN
  TRY(MLD_WRAP_RET_TAC THEN NO_TAC) THEN MLD_WRAP_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* After the ORR of the address stackpointer + K of the buffer with 2, which  *)
(* the simulation leaves as word_or, in the state of the assumption          *)
(* read SP s = stackpointer + K: the address is a sum, as K is a multiple of *)
(* 32 more or less than that of the stackpointer, by the case assumption.    *)
(* ------------------------------------------------------------------------- *)

let MLD_CLANG_OR_OFS_TAC d =
  let pat = `read SP (s:armstate) = word_add stackpointer (word (k:num))` in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(is_eq c && can (term_match [] pat) c) then failwith "no" else
    let k = mk_small_numeral(dest_small_numeral(rand(rand(rhs c))) + d) in
    let sp1 = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                      mk_comb(`word:num->int64`,k)) in
    SUBGOAL_THEN (mk_comb(`aligned 32:int64->bool`,sp1)) ASSUME_TAC THENL
     [W(fun (asl,w) ->
        let hs = filter (fun th -> mem (concl th)
          [`aligned 32 (stackpointer:int64)`;
           `~aligned 32 (stackpointer:int64)`;
           `aligned 16 (stackpointer:int64)`]) (map snd asl) in
        MAP_EVERY MP_TAC hs THEN REWRITE_TAC[MLD_WRAP_ALIGNED_16_32] THEN
        W(fun (_,w') -> ACCEPT_TAC(BITBLAST_RULE w')));
      ALL_TAC] THEN
    FIRST_ASSUM(fun a ->
      RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP MLD_CLANG_OR2 a])) THEN
    MLD_WRAP_NORM_TAC);;

let MLD_CLANG_OR_TAC = MLD_CLANG_OR_OFS_TAC 0;;

(* ------------------------------------------------------------------------- *)
(* The proofs split on the alignment of the stack pointer first, so each     *)
(* later case split gives two goals, one for each alignment, and the tactic  *)
(* of a case is chosen by the assumption c rather than by THENL:             *)
(* MLD_CLANG_IF c t1 t2 is t1 if c is an assumption and t2 otherwise.        *)
(* ------------------------------------------------------------------------- *)

let MLD_CLANG_IF c t1 t2 =
  W(fun (asl,_) -> if exists (fun (_,th) -> concl th = c) asl then t1 else t2);;

(* ------------------------------------------------------------------------- *)
(* For a buffer of length plen <= 332 (bth: plen <= 332) at the stack        *)
(* pointer sp = stackpointer + K of the state in the assumption, which has   *)
(* the prefix: the facts that it does not overlap the stack of a callee of   *)
(* nc bytes, at stackpointer + (K - nc), and the other regions of regs, for  *)
(* the preconditions of the callee (MLD_WRAP_DRIVER_TAC for each).           *)
(* ------------------------------------------------------------------------- *)

let MLD_CLANG_DRIVER_TAC nc regs bth =
  let pat = `read SP (s:armstate) = word_add stackpointer (word (k:num))` in
  let plen = lhand(concl bth) in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(is_eq c && can (term_match [] pat) c) then failwith "no" else
    let k = dest_small_numeral(rand(rand(rhs c))) in
    let addr n = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                         mk_comb(`word:num->int64`,mk_small_numeral n)) in
    let stk = mk_pair(addr (k - nc),mk_small_numeral nc)
    and buf = mk_pair(addr k,plen) in
    MAP_EVERY (fun r -> MLD_WRAP_DRIVER_TAC
      (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,r),buf)) bth)
     (stk :: regs));;

(*** After the call: the region of the prefix of plen <= 332 bytes in the
     memaccess_inbounds assumptions is widened to the 332 bytes of the buffer ***)

let MLD_CLANG_WIDEN_TAC bth =
  let pat = `read SP (s:armstate) = word_add stackpointer (word (k:num))` in
  let plen = lhand(concl bth) in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(is_eq c && can (term_match [] pat) c) then failwith "no" else
    let a = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                    rand(rhs c)) in
    MLD_WRAP_WIDEN_TAC
     [prove(mk_comb(mk_comb(`contained:int64#num->int64#num->bool`,
                            mk_pair(a,plen)),
                    mk_pair(a,`332`)),
            REWRITE_TAC[contained; CONTAINED_MODULO_REFL;
                        MLD_WRAP_PREFIX_LENGTH_LE])]);;
