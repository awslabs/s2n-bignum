(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of mldsa44_signature_internal,          *)
(* mldsa65_signature_internal and mldsa87_signature_internal (sign.c) for    *)
(* x86-64, as for AArch64 (see arm/proofs/utils/mldsa_native_signing.ml,     *)
(* whose lemmas and tactics these are, for the x86 model), whose FULL        *)
(* theorems are proved from lemmas for the parts of the code: the start of   *)
(* an attempt, the loop over z with its early exit, the loop over the rows   *)
(* of w0 with its two early exits, the packing of c~ and the hints, the      *)
(* cleanup of an attempt, and the whole attempt from them. The events of the *)
(* attempts are a function of what the C code declassifies (mld_sign_declass *)
(* of common/mldsa_native_sign.ml), from which also the number of attempts   *)
(* made follows (mld_sign_natt).                                             *)
(* ========================================================================= *)

needs "common/mldsa_native_sign.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/utils/mldsa_native_memset.ml";;
needs "common/fips204/properties/mldsa_native_signing.ml";;

(* ------------------------------------------------------------------------- *)
(* Bytes in memory: the bytes of n bytes as a number, and the converse, at a *)
(* (with the offset off from a base B in the _OFF forms, as the addresses of *)
(* the buffers in the frame are written).                                    *)
(* ------------------------------------------------------------------------- *)

let SIGN_READ_BYTES_LIST_OF_SEQ = prove
 (`!(a:int64) n (s:x86state).
        read (memory :> bytes(a,n)) s =
        num_of_bytelist
         (list_of_seq (\j. read (memory :> bytes8 (word_add a (word j))) s) n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[list_of_seq; num_of_bytelist; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL];
    ALL_TAC] THEN
  GEN_TAC THEN
  REWRITE_TAC[ADD1; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; GSYM ADD1; list_of_seq;
              NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[num_of_bytelist; READ_MEMORY_BYTES_BYTES8; MULT_CLAUSES;
              ADD_CLAUSES]);;

let SIGN_BYTES8_OF_READ_BYTES = prove
 (`!(a:int64) n (f:num->byte) (s:x86state).
        read (memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n)
        ==> !j. j < n
                ==> read (memory :> bytes8 (word_add a (word j))) s = f j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SIGN_READ_BYTES_LIST_OF_SEQ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SIGN_NUM_OF_BYTELIST_INJ) THEN
  REWRITE_TAC[]);;

let SIGN_READ_BYTES_OF_BYTES8 = prove
 (`!(a:int64) n (f:num->byte) (s:x86state).
        (!j. j < n
             ==> read (memory :> bytes8 (word_add a (word j))) s = f j)
        ==> read (memory :> bytes(a,n)) s = num_of_bytelist(list_of_seq f n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SIGN_READ_BYTES_LIST_OF_SEQ] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN ASM_SIMP_TAC[]);;

let SIGN_READ_BYTES_OF_BYTES8_OFF = prove
 (`!(B:int64) off n (f:num->byte) (s:x86state).
        (!j. j < n
             ==> read (memory :> bytes8 (word_add B (word (off + j)))) s = f j)
        ==> read (memory :> bytes(word_add B (word off),n)) s =
            num_of_bytelist(list_of_seq f n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIGN_READ_BYTES_OF_BYTES8 THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let SIGN_BYTES8_OF_READ_BYTES_OFF = prove
 (`!(B:int64) off n (f:num->byte) (s:x86state).
        read (memory :> bytes(word_add B (word off),n)) s =
        num_of_bytelist(list_of_seq f n)
        ==> !j. j < n
                ==> read (memory :> bytes8 (word_add B (word (off + j)))) s =
                    f j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SIGN_BYTES8_OF_READ_BYTES) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

(*** The low 32 bits of a 64-bit word in memory, as the code loads the    ***)
(*** argument ext from the stack, and the bytes of memory that is zero    ***)

let SIGN_BYTES32_OF_BYTES64 = prove
 (`!(a:int64) x (s:x86state).
        read (memory :> bytes64 a) s = x
        ==> read (memory :> bytes32 a) s = word_zx x`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; BYTES64_WBYTES; BYTES32_WBYTES;
              READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_64;
              DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP (8 * 4)`; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SIGN_BYTES8_ZERO = prove
 (`!(a:int64) n (s:x86state).
        read (memory :> bytes(a,n)) s = 0
        ==> !t. t < n
                ==> read (memory :> bytes8 (word_add a (word t))) s = word 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `0`; `t:num`; `1`; `s:x86state`]
    READ_MEMORY_BYTES_SUB) THEN
  ASM_REWRITE_TAC[DIV_0; MOD_0] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_0; BYTES8_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[GSYM READ_COMPONENT_COMPOSE]);;

(*** Bytes as 128-bit words, as the inlined copy of mu moves them ***)

let SIGN_BYTES128_OF_BYTES = prove
 (`!(a:int64) k x n (s:x86state).
        read (memory :> bytes(a,k)) s = x /\ 16 * n + 16 <= k
        ==> read (memory :> bytes128(word_add a (word(16 * n)))) s =
            word((x DIV 2 EXP (128 * n)) MOD 2 EXP 128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
    ASSUME_TAC) THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE] THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_READ_WBYTES; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `128 * n = 8 * 16 * n`;
              ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (k - 16 * n) 16 = 16` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; REFL_TAC]);;

let SIGN_BYTES_OF_BYTES128 = prove
 (`!(a:int64) x n (s:x86state).
        (!i. i < n
             ==> read (memory :> bytes128(word_add a (word(16 * i)))) s =
                 word((x DIV 2 EXP (128 * i)) MOD 2 EXP 128))
        ==> read (memory :> bytes(a,16 * n)) s = x MOD 2 EXP (128 * n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL];
    ALL_TAC] THEN
  X_GEN_TAC `s:x86state` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:x86state`) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * SUC n = 16 * n + 16`; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 16 * n = 128 * n`] THEN
  REWRITE_TAC[ARITH_RULE `128 * SUC n = 128 * n + 128`; EXP_ADD;
              MOD_MULT_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The counter kappa, a 32-bit word on the stack that the code passes in RDX *)
(* to the sampling of y, as the polynomials of mld_sign_y need it.           *)
(* ------------------------------------------------------------------------- *)

let SIGN_KAPPA16 = prove
 (`!k. word_zx(word_zx(word k:int32):int64):int16 = word k`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
    DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let SIGN_Y_KAPPA = prove
 (`!(g:num->int16->num->int32) rhop k.
        mld_polyvec
         (\j. g rhop (word_add (word_zx(word_zx(word k:int32):int64))
                               (word j))) =
        mld_sign_y g rhop k`,
  REWRITE_TAC[SIGN_KAPPA16; mld_sign_y; GSYM WORD_ADD]);;

(* ------------------------------------------------------------------------- *)
(* The alignment of the buffers in the frame, which the code aligns to 32    *)
(* bytes with AND RSP,-32 (see REALIGN_ALIGNED_TAC of                        *)
(* utils/mldsa_native_realign.ml), for the aligned SSE stores of the code    *)
(* and the callees that need it: an address aligned to 16 bytes stays so     *)
(* when a multiple of 16 is added.                                           *)
(* ------------------------------------------------------------------------- *)

let SIGN_ALIGNED_ADD = prove
 (`!(b:int64) off d.
        aligned 16 (word_add b (word off)) /\ 16 divides d
        ==> aligned 16 (word_add b (word(off + d)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC] THEN
  MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(NUM_REDUCE_CONV THENC DIVIDES_CONV));;

let SIGN_ALIGNED_OFF = prove
 (`!(b:int64) off k.
        aligned 16 (word_add b (word off))
        ==> aligned 16 (word_add b (word(off + 1024 * k)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIGN_ALIGNED_ADD THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE);;

(*** The values of the registers rs in state s, e.g. the YMM registers   ***)
(*** whose low 128 bits the code loads (keeping the high bits), as       ***)
(*** SAMPLING_GHOST_REGS_TAC of utils/mldsa_native_sampling.ml does      ***)

let SIGN_GHOST_REGS_TAC rs s =
  let sv = mk_var(s,`:x86state`) in
  MAP_EVERY (fun r ->
    let n = String.lowercase_ascii(fst(dest_const r)) ^ "_" ^ s in
    let t = list_mk_icomb "read" [r; sv] in
    ABBREV_TAC(mk_eq(mk_var(n,type_of t),t))) rs;;

let SIGN_SUBWORD_JOIN_128 = prove
 (`!(h:int128) (l:int128). word_subword (word_join h l:256 word) (0,128) = l`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* The zeroing of the signature, nb bytes at st, after the attempts are      *)
(* exhausted, which gcc inlines as zero quadword stores at st and st + nb -  *)
(* 8 and a REP STOSQ of (val st MOD 8 + nb - 8) DIV 8 quadwords from the     *)
(* first multiple of 8 above st, st + (8 - val st MOD 8) (MEMSET_ALIGN_ADDR  *)
(* of utils/mldsa_native_keccak.ml). As nb is not a multiple of 8, the count *)
(* depends on st (SIGN_STOS_COUNT, from its form in the simulation by        *)
(* bit-blasting), unlike the memsets of MEMSET_PREP_TAC. These are the tools *)
(* of utils/mldsa_native_hints.ml for the hints (GLUE_PSH_STOS_PREP_TAC and  *)
(* the others), for any st and nb: before the REP STOSQ, SIGN_STOS_PREP_TAC  *)
(* st nb abbreviates zk = val st MOD 8, the count zq, its word zc and the    *)
(* tail zt, with 8 * zq + zt = zk + nb - 8, so that the simulation can use   *)
(* their arithmetic, and splits the two quadwords into their parts outside   *)
(* the memory that the REP STOSQ clears; SIGN_STOS_STEP_TAC execth n steps   *)
(* it (instruction n), and SIGN_STOS_DONE_TAC st nb n puts the three parts   *)
(* together as the nb zero bytes at st, weakens the frame of the simulation  *)
(* to these nb bytes and expands the abbreviations, which the events of the  *)
(* template cannot use. SIGN_STOS_GEN_TAC st nb generalizes the count and    *)
(* the parts again in the goal of the memory safety of the events, with      *)
(* their arithmetic, for the bounds of the accesses of the REP STOSQ. As the *)
(* ABI requires on entry, the direction flag DF must be clear.               *)
(* ------------------------------------------------------------------------- *)

let SIGN_STOS_COUNT = prove
 (`!st:int64 m.
        m < 2 EXP 32
        ==> word_ushr (word_add (word_and st (word 7)) (word m)) 3 =
            word((val st MOD 8 + m) DIV 8)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_and st (word 7):int64) = val st MOD 8` ASSUME_TAC
  THENL
   [REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `7 = 2 EXP 3 - 1`] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 3 = 8`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`val(st:int64)`; `8`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_64] THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`val(st:int64) MOD 8`,`k:num`) THEN
  REPEAT STRIP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`k + m:num`; `8`] DIV_LE) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  SUBGOAL_THEN `m MOD 18446744073709551616 = m /\
                (k + m) MOD 18446744073709551616 = k + m /\
                ((k + m) DIV 8) MOD 18446744073709551616 = (k + m) DIV 8`
   (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN SIMPLE_ARITH_TAC);;
let SIGN_STOS_SPLIT = prove
 (`!k m. k < 8 /\ m < 2 EXP 32
         ==> 8 * ((k + m) DIV 8) + (k + m) MOD 8 = k + m /\
             (k + m) MOD 8 < 8 /\
             val(word((k + m) DIV 8):int64) = (k + m) DIV 8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`k + m:num`; `8`] DIVISION) THEN ARITH_TAC;
    ARITH_TAC;
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPECL [`k + m:num`; `8`] DIV_LE) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV
    THEN SIMPLE_ARITH_TAC]);;
let SIGN_ZERO_COMBINE = prove
 (`!a:int64 p q s:x86state.
        read (memory :> bytes(a,p)) s = 0 /\
        read (memory :> bytes(word_add a (word p),q)) s = 0
        ==> read (memory :> bytes(a,p + q)) s = 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES]);;
let SIGN_STOS_PREP_TAC st nb =
  let mkw n = mk_comb(`word:num->int64`,mk_small_numeral n) in
  let addw a n = mk_binop `word_add:int64->int64->int64` a (mkw n) in
  let hi = addw st (nb - 8) and mt = mk_small_numeral(nb - 8) in
  let ath = SPEC st MEMSET_ALIGN_ADDR in
  let cnt = subst [st,`st:int64`; mt,`m:num`]
   `word_ushr (word_add (word_and st (word 7)) (word m)) 3:int64` in
  let cth = MP (SPECL [st; mt] SIGN_STOS_COUNT)
               (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` mt
                                           `2 EXP 32`))) in
  let kt = mk_binop `MOD` (mk_comb(`val:int64->num`,st)) `8` in
  let is_reg r sv th =
    let c = concl th in
    is_eq c && lhand c = list_mk_icomb "read" [r; sv] in
  let rewr_count sv th =
    if is_reg `RCX` sv th then
      TRANS th (TRANS (BITBLAST_RULE(mk_eq(rand(concl th),cnt))) cth)
    else th in
  let is_zero64 a th =
    can (term_match []
          `read (memory :> bytes64 (a:int64)) (s:x86state) = word 0`)
        (concl th) &&
    rand(rand(lhand(lhand(concl th)))) = a in
  W(fun (asl,w) ->
    let sv = rand w in
    RULE_ASSUM_TAC(rewr_count sv) THEN
    RULE_ASSUM_TAC(fun th -> if is_reg `RDI` sv th then REWRITE_RULE[ath] th
                             else th)) THEN
  MP_TAC(REWRITE_RULE[ARITH_EQ] (SPECL [mk_comb(`val:int64->num`,st); `8`]
                                   MOD_LT_EQ)) THEN
  DISCH_TAC THEN
  ABBREV_TAC (mk_eq(`zk:num`,kt)) THEN
  MP_TAC(SPECL [`zk:num`; mt] SIGN_STOS_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
                  STRIP_TAC] THEN
  ABBREV_TAC (subst [mt,`m:num`] `zq = (zk + m) DIV 8`) THEN
  ABBREV_TAC (subst [mt,`m:num`] `zt = (zk + m) MOD 8`) THEN
  ABBREV_TAC `zc = word zq:int64` THEN
  FIRST_X_ASSUM(fun th ->
    if is_zero64 st th
    then ASSUME_TAC(CONJUNCT1(MATCH_MP READ_MEMORY_BYTES64_ZERO_SPLIT
                     (CONJ th (ARITH_RULE `8 - zk <= 8`))))
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_zero64 hi th
    then MP_TAC(CONJUNCT2(MATCH_MP READ_MEMORY_BYTES64_ZERO_SPLIT
                     (CONJ th (ARITH_RULE `8 - zt <= 8`))))
    else NO_TAC) THEN
  SUBGOAL_THEN `8 - (8 - zt) = zt` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   (mk_eq(mk_binop `word_add:int64->int64->int64` hi `word(8 - zt):int64`,
          mk_binop `word_add:int64->int64->int64` st
            `word((8 - zk) + 8 * zq):int64`))
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
    DISCH_TAC];;
let SIGN_STOS_RW_CONV lth =
  let memth = REWRITE_RULE[VALID_COMPONENT_CONV `valid_component memory`]
   (ISPEC `memory:(x86state,int64->byte)component`
     READ_WRITE_VALID_COMPONENT) in
  let bth = REWRITE_RULE[DIMINDEX_64]
   (INST_TYPE [`:64`,`:A`] READ_WRITE_BYTES) in
  REWRITE_CONV[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE; memth] THENC
  (fun tm -> MP (PART_MATCH (lhand o rand) bth tm) lth) THENC
  REWRITE_CONV[VAL_WORD_0; MULT_CLAUSES; NSUM_0; MOD_0];;
let SIGN_STOS_STEP_TAC execth n =
  let sname = "s" ^ string_of_int n in
  let sv = mk_var(sname,`:x86state`) in
  let bnd = `8 * zq <= 2 EXP 64` in
  let rpat = `read (memory :> bytes(a:int64,k)) (s:x86state)`
  and wpat = `read (memory :> bytes(a:int64,k))
                (write (c:(x86state,num)component) (y:num) (s:x86state))` in
  SUBGOAL_THEN bnd ASSUME_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  X86_VSTEPS_TAC execth [n] THEN
  FIRST_ASSUM(fun lth ->
    if concl lth = bnd then
      RULE_ASSUM_TAC(fun th ->
        let c = concl th in
        if is_eq c && can (term_match [] rpat) (lhand c) &&
           rand(lhand c) = sv && can (term_match [] wpat) (rand c)
        then CONV_RULE(RAND_CONV(SIGN_STOS_RW_CONV lth)) th else th)
    else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC sname;;

let SIGN_STOS_DONE_TAC st nb n =
  let sv = mk_var("s" ^ string_of_int n,`:x86state`) in
  let zvs = [`zk:num`; `zq:num`; `zt:num`; `zc:int64`] in
  let mentions th = exists (fun v -> free_in v (concl th)) zvs in
  let is_abbrev th =
    let c = concl th in
    is_eq c && mem (rhs c) zvs && not(lhs c = `val(zc:int64)`) in
  let removable th =
    let c = concl th in
    mentions th && not(is_abbrev th) &&
    (can (term_match []
           `read (memory :> bytes(a:int64,k)) (s:x86state) = 0`) c ||
     (is_eq c && type_of(lhs c) = `:num`) ||
     is_binary "<" c || is_binary "<=" c) in
  let mz = subst [st,`a:int64`; mk_small_numeral nb,`n:num`]
   `MAYCHANGE [memory :> bytes(a,n)]:x86state->x86state->bool` in
  let is_part t =
    match t with
      Comb(Const("MAYCHANGE",_),l) ->
        (try match dest_list l with
               [c] -> let m,x = dest_binary ":>" c in
                      m = `memory` && free_in st x
             | _ -> false
         with Failure _ -> false)
    | _ -> false in
  let expand v =
    FIRST_X_ASSUM(fun th ->
      if is_abbrev th && rhs(concl th) = v then
        RULE_ASSUM_TAC(REWRITE_RULE[SYM th]) THEN REWRITE_TAC[SYM th]
      else NO_TAC) in
  MP_TAC(SPECL [st; `8 - zk`; `8 * zq`; sv] SIGN_ZERO_COMBINE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [st; `8 - zk + 8 * zq`; `zt:num`; sv] SIGN_ZERO_COMBINE) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   (mk_eq(mk_binop `(+):num->num->num` `8 - zk + 8 * zq` `zt:num`,
          mk_small_numeral nb))
  SUBST1_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if maychange_term c && mentions th then
      let parts = setify(find_terms is_part c) in
      SUBGOAL_THEN (subst (map (fun t -> mz,t) parts) c) ASSUME_TAC THENL
       [ASSUME_TAC th THEN MONOTONE_MAYCHANGE_TAC; ALL_TAC]
    else NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if removable th then ALL_TAC else NO_TAC)) THEN
  MAP_EVERY expand [`zc:int64`; `zt:num`; `zq:num`; `zk:num`];;

let SIGN_STOS_GEN_TAC st nb =
  let kt = mk_binop `MOD` (mk_comb(`val:int64->num`,st)) `8`
  and mt = mk_small_numeral(nb - 8) in
  let kth = REWRITE_RULE[ARITH_EQ]
             (SPECL [mk_comb(`val:int64->num`,st); `8`] MOD_LT_EQ) in
  let mth = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` mt
                                       `2 EXP 32`)) in
  let sth = MP (SPECL [kt; mt] SIGN_STOS_SPLIT) (CONJ kth mth) in
  let kmt = mk_binop `(+):num->num->num` kt mt in
  MP_TAC sth THEN MP_TAC kth THEN
  SPEC_TAC(mk_binop `MOD` kmt `8`,`zt:num`) THEN
  SPEC_TAC(mk_binop `DIV` kmt `8`,`zq:num`) THEN
  SPEC_TAC(kt,`zk:num`) THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* Polynomial i of a vector at off + 1024 * i from B, copied by memcpy to    *)
(* doff (the two regions have the same bytes zs after the call): the copy    *)
(* has the coefficients of mld_poly_of f i.                                  *)
(* ------------------------------------------------------------------------- *)

let SIGN_COPY_POLY = prove
 (`!(B:int64) doff soff i n (f:num->int32) zs (s:x86state).
        read (memory :> bytes (word_add B (word doff),1024)) s = zs /\
        read (memory :> bytes (word_add B (word (soff + 1024 * i)),1024)) s =
        zs /\
        (!j. j < n
             ==> read (memory :> bytes32 (word_add B (word (soff + 4 * j)))) s =
                 f j) /\
        256 * i + 256 <= n
        ==> !j. j < 256
                ==> read (memory :> bytes32 (word_add B (word (doff + 4 * j))))
                      s = mld_poly_of f i j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`word_add B (word doff):int64`;
                `word_add B (word (soff + 1024 * i)):int64`; `256`;
                `s:x86state`; `s:x86state`] VEC_BYTES_EQ_BYTES32) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV NUM_MULT_CONV)) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mld_poly_of] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `256 * i + j`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `j < 256` THEN UNDISCH_TAC `256 * i + 256 <= n` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; ADD_ASSOC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The rows of w0 as the loop over them leaves them: row j of the low part   *)
(* (for its first check), the rows after it, and the rows before j + 1 once  *)
(* row j holds w0_j - c s2_j + c t0_j, as mld_sign_hint_x gives it.          *)
(* ------------------------------------------------------------------------- *)

let SIGN_ROW_SLICE = prove
 (`!(B:int64) off n f (w:num->int32) j (s:x86state).
        (!k. 256 * j <= k /\ k < n
             ==> read (memory :> bytes32 (word_add B (word (off + 4 * k)))) s =
                 mld_polyvec_map f w k) /\
        256 * (j + 1) <= n
        ==> (!i. i < 256
                 ==> read (memory :> bytes32
                            (word_add B (word ((off + 1024 * j) + 4 * i)))) s =
                     f (mld_poly_of w j) i) /\
            (!k. 256 * (j + 1) <= k /\ k < n
                 ==> read (memory :> bytes32 (word_add B (word (off + 4 * k))))
                       s = mld_polyvec_map f w k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `256 * j + i`) THEN
    ASM_SIMP_TAC[MLD_POLYVEC_MAP_COEFF] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `i < 256` THEN UNDISCH_TAC `256 * (j + 1) <= n` THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `256 * (j + 1) <= k` THEN UNDISCH_TAC `k < n` THEN
    ARITH_TAC]);;

let SIGN_ROW_JOIN = prove
 (`!(B:int64) off k dlo (w:num->int32) s2h t0h cphat j (s:x86state).
        j < k /\
        (!m. m < 256 * j
             ==> read (memory :> bytes32 (word_add B (word (off + 4 * m)))) s =
                 mld_sign_hint_x k dlo w s2h t0h cphat m) /\
        (!i. i < 256
             ==> read (memory :> bytes32
                        (word_add B (word ((off + 1024 * j) + 4 * i)))) s =
                 mld_poly_add (mld_sign_r0 dlo w s2h cphat j)
                              (mld_sign_ct0 t0h cphat j) i)
        ==> !m. m < 256 * (j + 1)
                ==> read (memory :> bytes32 (word_add B (word (off + 4 * m))))
                      s = mld_sign_hint_x k dlo w s2h t0h cphat m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `m < 256 * j` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m - 256 * j`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `m < 256 * (j + 1)` THEN UNDISCH_TAC `~(m < 256 * j)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(off + 1024 * j) + 4 * (m - 256 * j) = off + 4 * m`
   SUBST1_TAC THENL
   [UNDISCH_TAC `~(m < 256 * j)` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `m = 256 * j + (m - 256 * j)`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
   [UNDISCH_TAC `~(m < 256 * j)` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIGN_HINT_X_ROW THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `m < 256 * (j + 1)` THEN UNDISCH_TAC `~(m < 256 * j)` THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The packing of z: byte j of the packing of a polynomial depends only on   *)
(* its coefficients, so that the bytes that mld_pack_sig_z writes for z_i    *)
(* extend those of mld_polyvec_pack for the polynomials before it.           *)
(* ------------------------------------------------------------------------- *)

let SIGN_PACK_JOIN = prove
 (`!(f:(num->int32)->num->byte) P (z:num->num->int32) (sig:int64) off i
    (s:x86state).
        (!a b j. (!i. i < 256 ==> a i = b i) /\ j < P ==> f a j = f b j) /\
        (!t. t < P * i
             ==> read (memory :> bytes8 (word_add sig (word (off + t)))) s =
                 mld_polyvec_pack P f (mld_polyvec z) t) /\
        (!j. j < P
             ==> read (memory :> bytes8 (word_add sig (word (off + P * i + j))))
                   s = f (z i) j)
        ==> !t. t < P * (i + 1)
                ==> read (memory :> bytes8 (word_add sig (word (off + t)))) s =
                    mld_polyvec_pack P f (mld_polyvec z) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `t < P * i` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - P * i`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `t < P * (i + 1)` THEN UNDISCH_TAC `~(t < P * i)` THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `off + P * i + t - P * i = off + t` SUBST1_TAC THENL
   [UNDISCH_TAC `~(t < P * i)` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `t = P * i + (t - P * i)` (fun th ->
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [UNDISCH_TAC `~(t < P * i)` THEN ARITH_TAC; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_POLYVEC_PACK_COEFF o rand o snd) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `t < P * (i + 1)` THEN UNDISCH_TAC `~(t < P * i)` THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [SIMP_TAC[MLD_POLY_OF_POLYVEC];
    UNDISCH_TAC `t < P * (i + 1)` THEN UNDISCH_TAC `~(t < P * i)` THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The signature of a successful attempt, from its three parts: c~ (ctlen    *)
(* bytes), z (zlen bytes after it) and the hints (hlen bytes after that), in *)
(* the form of mld_sign_attempt_sig.                                         *)
(* ------------------------------------------------------------------------- *)

let SIGN_SIG_ASSEMBLE = prove
 (`!(sig:int64) (ct:num->byte) zz hh ctlen zlen hlen (s:x86state).
        (!j. j < ctlen
             ==> read (memory :> bytes8 (word_add sig (word j))) s = ct j) /\
        (!t. t < zlen
             ==> read (memory :> bytes8 (word_add sig (word (ctlen + t)))) s =
                 zz t) /\
        (!t. t < hlen
             ==> read (memory :> bytes8
                        (word_add sig (word ((ctlen + zlen) + t)))) s = hh t)
        ==> !t. t < (ctlen + zlen) + hlen
                ==> read (memory :> bytes8 (word_add sig (word t))) s =
                    (if t < ctlen then ct t
                     else if t < ctlen + zlen then zz (t - ctlen)
                     else hh (t - (ctlen + zlen)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t - ctlen` o check (fun th ->
      can (term_match [`zlen:num`] `!t. t < zlen ==> P t`) (concl th)));
    FIRST_X_ASSUM(MP_TAC o SPEC `t - (ctlen + zlen)` o check (fun th ->
      can (term_match [`hlen:num`] `!t. t < hlen ==> P t`) (concl th)))] THEN
  (ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC EQ_IMP THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
  SIMPLE_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the FULL proofs of the parts.                                 *)
(*                                                                           *)
(* SIGN_LOOP_DISCHARGE_TAC ends the body of a loop of                        *)
(* ENSURES_EVENTS_WHILE_UP2_TAC: it unifies the events of the iteration with *)
(* the function of the template (after reassociating the APPENDs so that the *)
(* events before the iteration are the same on both sides) and splits the    *)
(* memaccess_inbounds goal and those of the events so far, so that each part *)
(* is discharged on its own. SIGN_PATH_DISCHARGE_TAC does the same at the    *)
(* end of a path of the attempt, whose events are those of the path, given   *)
(* by a function of the template under conditionals that the case            *)
(* assumptions select, followed by those of its start. SIGN_PC_SIMP_TAC and  *)
(* SIGN_PC_COND_TAC put the PC after a lemma or a loop in the form that the  *)
(* simulation or the postcondition needs.                                    *)
(* ------------------------------------------------------------------------- *)

(* Atomic, for proofs on several domains (see common/par.ml) *)

let SIGN_SPLIT_MEMACCESS_ASM_TAC =
  W(fun (asl,w) ->
    let is_ev_eq th =
      let c = concl th in
      is_eq c && is_var(lhs c) && is_uarch_event_list_ty(type_of(lhs c)) in
    let eths = map snd (filter (is_ev_eq o snd) asl) in
    let mas = filter (fun (_,th) ->
      match strip_comb(concl th) with
        (Const("memaccess_inbounds",_),[_;_;_]) -> true
      | _ -> false) asl in
    MAP_EVERY (fun (_,th) ->
      UNDISCH_THEN (concl th) (fun th' ->
        STRIP_ASSUME_TAC
         (REWRITE_RULE (MEMACCESS_INBOUNDS_APPEND::eths) th'))) mas);;

let SIGN_MEMACCESS_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SPLIT_MEMACCESS_ASM_TAC THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let SIGN_LOOP_DISCHARGE_TAC =
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_LOOP_UNIFY_TAC; SIGN_MEMACCESS_TAC];;

let SIGN_CONCRETE_DISCHARGE_TAC =
  SIGN_BETA_ALL_TAC THEN
  REWRITE_TAC[ENUMERATEL; APPEND; APPEND_NIL] THEN
  SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[APPEND; APPEND_NIL]; SIGN_MEMACCESS_TAC];;

let SIGN_NIL_EVENTS_TAC =
  EXISTS_TAC `[]:(uarch_event)list` THEN
  REWRITE_TAC[APPEND; memaccess_inbounds; ALL];;

let SIGN_PATH_DISCHARGE_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [SIGN_PATH_UNIFY_TAC; SIGN_MEMACCESS_TAC];;

let SIGN_PC_SIMP_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `read RIP s = x`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let SIGN_PC_COND_TAC =
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `read RIP s = word (if b then x else y)`) o concl)) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COND_RAND] THEN DISCH_TAC;;

(*** The test of a 64-bit counter against a bound, as CMP and JNE leave it ***)

let SIGN_VAL_WORD_SUB_EQ_0 = prove
 (`!a b. a < 2 EXP 64 /\ b < 2 EXP 64
         ==> (val(word_sub (word a) (word b):int64) = 0 <=> a = b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]);;

let SIGN_TEST_TAC =
  let pat = `val(word_sub (word a) (word b):int64) = 0`
  and lth = SPECL [`a:num`; `b:num`] SIGN_VAL_WORD_SUB_EQ_0 in
  W(fun (asl,w) ->
    let tms = setify(find_terms (can (term_match [] pat)) w) in
    MAP_EVERY (fun t ->
      let th = INSTANTIATE (term_match [] pat t) lth in
      MP_TAC th THEN ANTS_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) tms);;

(*** The same for the 32-bit counter kappa, and the return value, the low ***)
(*** 32 bits of R13 zero-extended                                         ***)

let SIGN_VAL_WORD_SUB_EQ_0_32 = prove
 (`!a b. a < 2 EXP 32 /\ b < 2 EXP 32
         ==> (val(word_sub (word a) (word b):int32) = 0 <=> a = b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[VAL_WORD; DIMINDEX_32; MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the FULL proof of a whole function.                           *)
(*                                                                           *)
(* SIGN_SEL_DISCHARGE_TAC ends a path whose template is selected by the case *)
(* assumptions, as SIGN_PATH_DISCHARGE_TAC, with FULL_UNIFY_F_EVENTS_TAC for *)
(* the events. After calls of memset and memcpy the events so far are        *)
(* reassociated (FULL_EXISTS_E2_TAC), so that at the end of an iteration of  *)
(* the outer loop, or of its exit, those of the invariant are no longer a    *)
(* suffix of the events: SIGN_SUFFIX_UNIFY_TAC puts both sides in normal     *)
(* form (SIGN_LIST_CONV, under the lambdas and conditionals too), folds the  *)
(* normal form of the events e2 of the invariant back into e2 and unifies    *)
(* the part before it with the template (of the form APPEND f_ev e2), and    *)
(* SIGN_SUFFIX_MEMACCESS_TAC does the same for the memory safety, taking     *)
(* that of e2 from the assumptions and splitting the rest. SIGN_DROP_TAC     *)
(* drops the assumptions that match one of the patterns, e.g. equations      *)
(* that would rewrite the postcondition in the simulation of a call.         *)
(* SIGN_NUMS_TAC and SIGN_NUM_ARITH_CONV evaluate numeral sums and products, *)
(* and SIGN_PC_SIMP_RW_TAC rewrites the PC with the assumptions and ths.     *)
(* ------------------------------------------------------------------------- *)

let SIGN_SEL_DISCHARGE_TAC =
  SIGN_BETA_ALL_TAC THEN SIGN_SELECT_TAC THEN SIGN_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; SIGN_MEMACCESS_TAC];;

let SIGN_PC_SIMP_RW_TAC ths =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `read RIP s = x`) (concl th))) THEN
  ASM_REWRITE_TAC ths THEN DISCH_TAC;;
