(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece from join5 (phase 3): the three table updates (table2 at        *)
(* Load64(ip + 1) and Load64(ip + 2), table at Load32(ip + 1)) and, if       *)
(* next_emit < ip, EmitLiteral of [next_emit, ip), then loop5 (phase 4).     *)
(* The literal of len = ip - next_emit bytes is written as gcc inlined it:   *)
(*                                                                           *)
(*   len <= 16 (+0x778)  the tag (len - 1) << 2, then 16 bytes at once       *)
(*   len <= 60 (+0x748)  the tag, then loop11, 16 bytes at a time            *)
(*   len > 60  (+0x544)  the tag 60 << 2 or 61 << 2, the 4 bytes of len - 1  *)
(*                       (of which 1 or 2 count), then loop11                *)
(*                                                                           *)
(* so up to 15 bytes beyond the literal are written (inside the output       *)
(* region) and read (inside the input, as ip <= ip_limit).                    *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_join5_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Lemmas and tactics.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Lemmas of the join5 piece (to go into compress_fragment_double_hash_join5_proof.ml) *)

let CF2_J5_MOD_ADD_MUL = prove
 (`!x y n. (x + n * y) MOD n = x MOD n`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[MOD_MULT_ADD]);;

let CF2_J5_READ_BYTES_PREFIX = prove
 (`!(m:(S,int64->byte)component) a k j (l:byte list) p s.
     read (m :> bytes(a,k)) s = num_of_bytelist(SUB_LIST(p,k) l) /\ j <= k
     ==> read (m :> bytes(a,j)) s = num_of_bytelist(SUB_LIST(p,j) l)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD 2 EXP (8 * j)`) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[SNAPPY_NUM_OF_BYTELIST_SUB_LIST; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `MIN (8 * (j + d)) (8 * j) = 8 * j`] THEN
  SIMP_TAC[CF2_J5_MOD_ADD_MUL; MOD_LT; READ_BYTES_BOUND]);;

let CF2_J5_LOAD64_PAIR = prove
 (`!(src:byte list) p.
     snappy_load64 src p + 2 EXP 64 * snappy_load64 src (p + 8) =
     num_of_bytelist(SUB_LIST(p,16) src)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[snappy_load64; SNAPPY_NUM_OF_BYTELIST_SUB_LIST] THEN
  REWRITE_TAC[ARITH_RULE `8 * (p + 8) = 8 * p + 64`; EXP_ADD; GSYM DIV_DIV] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          18446744073709551616 * 18446744073709551616`] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN ARITH_TAC);;

let CF2_J5_BYTES64_PAIR = prove
 (`!(m:(S,int64->byte)component) a x y s.
     read (m :> bytes64 a) s = word x /\
     read (m :> bytes64 (word_add a (word 8))) s = word y /\
     x < 2 EXP 64 /\ y < 2 EXP 64
     ==> read (m :> bytes(a,16)) s = x + 2 EXP 64 * y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `16 = 8 + 8` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM VAL_EQ; BYTES64_WBYTES;
                              READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
                              DIMINDEX_64; VAL_WORD]) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* The bytes of a region after its first k from a region of k + j bytes. *)

let CF2_J5_READ_BYTES_APPEND = prove
 (`!(m:(S,int64->byte)component) a k j x y s.
     read (m :> bytes(a,k)) s = x /\
     read (m :> bytes(word_add a (word k),j)) s = y
     ==> read (m :> bytes(a,k + j)) s = x + 2 EXP (8 * k) * y`,
  SIMP_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE]);;

let CF2_J5_SUB_LIST_ADD = prove
 (`!(l:byte list) p a b.
     p + a + b <= LENGTH l
     ==> num_of_bytelist(SUB_LIST(p,a + b) l) =
         num_of_bytelist(SUB_LIST(p,a) l) +
         2 EXP (8 * a) * num_of_bytelist(SUB_LIST(p + a,b) l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SNAPPY_NUM_OF_BYTELIST_SUB_LIST] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM DIV_DIV] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN ARITH_TAC);;

let CF2_J5_IVAL_WORD64 = prove
 (`!k. k < 2 EXP 63 ==> ival(word k:int64) = &k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word k:int64) = k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `word k:int64` IVAL_EQ_VAL) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
                  SIMP_TAC[]]);;

let CF2_J5_IVAL_WORD32 = prove
 (`!k. k < 2 EXP 31 ==> ival(word k:int32) = &k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word k:int32) = k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `word k:int32` IVAL_EQ_VAL) THEN
  ASM_REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
                  SIMP_TAC[]]);;

let CF2_J5_WORD_SX32 = prove
 (`!k. k < 2 EXP 31 ==> word_sx(word k:int32):int64 = word k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_sx] THEN
  ASM_SIMP_TAC[CF2_J5_IVAL_WORD32; GSYM WORD_IWORD]);;

let CF2_J5_WSUB_IWORD = prove
 (`!a b. word_sub (word a) (word b):N word = iword(&a - &b)`,
  REWRITE_TAC[IWORD_INT_SUB; GSYM WORD_IWORD]);;

let CF2_J5_HASH4_WORD = prove
 (`!ts v. snappy_pow2 ts /\ ts <= 16384 /\ v < 2 EXP 32
          ==> word_zx (word_and (word_zx (word (2 * (ts - 1)):int64):int32)
                (word_ushr (word (0 + val (word v:int32) * 2654435761)) 17))
              :int64 =
              word(2 * snappy_hash4 ts v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ts:num`; `v:num`] SNAPPY_HASH4_WORD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `v < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `v MOD 2 EXP 32 = v /\ v MOD 2 EXP 64 = v`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `v < 2 EXP 32` THEN
    ARITH_TAC;
    REWRITE_TAC[MULT_SYM]]);;

let CF2_J5_ZXZX = prove
 (`!k. k < 2 EXP 32 ==> word_zx(word_zx(word k:int64):int32):int64 = word k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `k MOD 2 EXP 32 = k /\ k MOD 2 EXP 64 = k`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `k < 2 EXP 32` THEN
  ARITH_TAC);;

let CF2_J5_IVAL_SUB32 = prove
 (`!a b. a < 2 EXP 31 /\ b < 2 EXP 31
         ==> ival(word_sub (word a) (word b):int32) = &a - &b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CF2_J5_WSUB_IWORD] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW]) THEN
  RULE_ASSUM_TAC(CONV_RULE INT_REDUCE_CONV) THEN ASM_INT_ARITH_TAC);;

let CF2_J5_WORD_SUB_LE = prove
 (`!x y. y <= x ==> word_sub (word x) (word y):N word = word(x - y)`,
  SIMP_TAC[WORD_SUB]);;

let CF2_J5_ZX_SUB1 = prove
 (`!k. 1 <= k /\ k < 2 EXP 32
       ==> word_zx(word_sub (word_zx(word k:int64):int32) (word 1)):int64 =
           word(k - 1)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[WORD_ZX_WORD_SIMPLE; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  ASM_SIMP_TAC[CF2_J5_WORD_SUB_LE] THEN
  REWRITE_TAC[WORD_ZX_WORD; DIMINDEX_32] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let CF2_J5_LIT2 = prove
 (`!(m:(S,int64->byte)component) op (out:byte list) t h d s.
     read (m :> bytes(op,LENGTH out + 1 + LENGTH h + LENGTH d)) s =
     (num_of_bytelist out +
      2 EXP (8 * LENGTH out) * (val t + 256 * num_of_bytelist h)) +
     2 EXP (8 * (LENGTH out + 1 + LENGTH h)) * num_of_bytelist d
     ==> read (m :> bytes(op,LENGTH(APPEND out (CONS t (APPEND h d))))) s =
         num_of_bytelist(APPEND out (CONS t (APPEND h d)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; SNAPPY_NUM_OF_BYTELIST_APPEND;
              num_of_bytelist] THEN
  REWRITE_TAC[ARITH_RULE `a + SUC(b + c) = a + 1 + b + c`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC NUM_RING);;


let CF2_J5_ZX32 = prove
 (`!k. word_zx (word k:int64):int32 = word k`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64;
              MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* The signed comparison k <= 59 of the 32-bit word k.                      *)

let CF2_J5_IVAL_SMALL = prove
 (`!k. k < 2 EXP 31 ==> ival(word k:int32) = &k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_IWORD] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
  POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

(* The number of bytes of the length of a long literal, from clz.           *)

let CF2_J5_CLZ_DIV8 = prove
 (`!v. 0 < v /\ v < 65536
       ==> word_clz(word v:int32) DIV 8 = (if v < 256 then 3 else 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word v:int32`; `24`] WORD_LE_CLZ_VAL) THEN
  MP_TAC(ISPECL [`word v:int32`; `16`] WORD_LE_CLZ_VAL) THEN
  MP_TAC(ISPECL [`word v:int32`; `32`] WORD_LE_CLZ_VAL) THEN
  REWRITE_TAC[DIMINDEX_32; VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `v MOD 4294967296 = v` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `v < 1 <=> v = 0`] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < v ==> ~(v = 0)`] THEN
  ABBREV_TAC `z = word_clz(word v:int32)` THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIV_UNIQ THENL
   [EXISTS_TAC `z - 24`; EXISTS_TAC `z - 16`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NOT_LT]) THEN ASM_ARITH_TAC);;

(* An arithmetic shift of a 32-bit word below 2^31 is the division.         *)

let CF2_J5_ISHR_SMALL = prove
 (`!k n. k < 2 EXP 31 ==> word_ishr (word k:int32) n = word(k DIV 2 EXP n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ishr] THEN
  ASM_SIMP_TAC[CF2_J5_IVAL_SMALL] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_DIV; GSYM WORD_IWORD]);;

let CF2_J5_CLZ_SMALL = prove
 (`!x:int32. word_clz x < 2 EXP 31`,
  GEN_TAC THEN MP_TAC(ISPEC `x:int32` WORD_CLZ_LE_DIMINDEX) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let CF2_J5_BYTES_OF_32 = prove
 (`!(m:(S,int64->byte)component) a v k s.
     read (m :> bytes32 a) s = word v /\ v < 2 EXP (8 * k) /\ k <= 4
     ==> read (m :> bytes(a,k)) s = v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v < 4294967296` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (8 * k)` THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC LE_TRANS `2 EXP 32` THEN CONJ_TAC THENL
     [REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `read (bytes(a,4)) (read (m:(S,int64->byte)component) s) = v`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `val:int32->num` o
      check (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:int32`)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES32_WBYTES; VAL_READ_WBYTES;
                DIMINDEX_32; VAL_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:int64`; `4`; `k:num`;
                 `read (m:(S,int64->byte)component) s`] READ_BYTES_MOD) THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= 4 ==> MIN 4 k = k`; MOD_LT] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN MESON_TAC[]);;

(* loop11 of EmitLiteral: 16 bytes at a time from next_emit to op + P,     *)
(* until op + P + len (so up to 15 bytes more than the literal, in the      *)
(* output region and from the input).                                       *)

let cf2_j5_loop11_inv =
 `\i (s:armstate).
    read X1 s = word_add inp (word(ne + 16 * i)) /\
    read X15 s = word_add op (word(P + 16 * i)) /\
    read X2 s = word_add op (word(P + len)) /\
    read (memory :> bytes(inp,LENGTH src)) s = num_of_bytelist src /\
    read (memory :> bytes(op,P)) s = v /\
    read (memory :> bytes(word_add op (word P),16 * i)) s =
    num_of_bytelist(SUB_LIST(ne,16 * i) src) /\
    (?e2. read events s = APPEND e2 e /\
          memaccess_inbounds e2 [inp,LENGTH src; op,mx] [op,mx])`;;

let CF2_J5_LOOP11_STMT =
 `!(src:byte list) inp ne len op P mx v pc e.
    aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
    val inp + LENGTH src < 2 EXP 64 /\ val op + mx < 2 EXP 64 /\
    nonoverlapping (op,mx) (inp,LENGTH src) /\
    nonoverlapping (op,mx) (word pc,libsnappy_rw + libsnappy_rw_size) /\
    1 <= len /\ ne + len + 15 <= LENGTH src /\ P + len + 15 <= mx
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + 16464) /\
              read X1 s = word_add inp (word ne) /\
              read X15 s = word_add op (word P) /\
              read X2 s = word_add op (word(P + len)) /\
              read (memory :> bytes(inp,LENGTH src)) s = num_of_bytelist src /\
              read (memory :> bytes(op,P)) s = v /\
              read events s = e)
         (\s. read PC s = word(pc + 16480) /\
              read X2 s = word_add op (word(P + len)) /\
              read (memory :> bytes(op,P + len)) s =
              v + 2 EXP (8 * P) * num_of_bytelist(SUB_LIST(ne,len) src) /\
              ?e2. read events s = APPEND e2 e /\
                   memaccess_inbounds e2 [inp,LENGTH src; op,mx] [op,mx])
         (MAYCHANGE [PC; X1; X6; X7; X15] ,, MAYCHANGE [NF; ZF; CF; VF] ,,
          MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(op,mx)])`;;

let CF2_J5_LOOP11 = prove
 (CF2_J5_LOOP11_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`len + 15`; `16`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ENSURES_WHILE_UP_TAC `(len + 15) DIV 16` `pc + 16464` `pc + 16472`
   cf2_j5_loop11_inv THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    (* the start *)
    ENSURES_INIT_TAC "s0" THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES; num_of_bytelist;
                READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
    EXISTS_TAC `[]:(uarch_event)list` THEN
    REWRITE_TAC[APPEND; memaccess_inbounds; ALL];
    (* the body *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `e2:(uarch_event)list` STRIP_ASSUME_TAC o
      check (is_exists o concl)) THEN
    SUBGOAL_THEN `ne + 16 * i + 16 <= LENGTH(src:byte list) /\
                  P + 16 * i + 16 <= mx` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    CF2_INPUT_TAC SNAPPY_READ_LOAD64 `ne + 16 * i` THEN
    CF2_INPUT_TAC SNAPPY_READ_LOAD64 `(ne + 16 * i) + 8` THEN
    ARM_BSTEP_TAC SNAPPY_CF2_GCC12_O2_EXEC (1--2) THEN
    MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`;
                   `word_add op (word(P + 16 * i)):int64`;
                   `snappy_load64 src (ne + 16 * i)`;
                   `snappy_load64 src ((ne + 16 * i) + 8)`; `s2:armstate`]
                  CF2_J5_BYTES64_PAIR) THEN
    REWRITE_TAC[SNAPPY_LOAD64_BOUND; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CF2_J5_LOAD64_PAIR] THEN DISCH_TAC THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    REPEAT CONJ_TAC THENL
     [CF2_WORD_EQ_TAC;
      CF2_WORD_EQ_TAC;
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
       `num_of_bytelist(SUB_LIST(ne,16 * i) src) +
        2 EXP (8 * 16 * i) * num_of_bytelist(SUB_LIST(ne + 16 * i,16) src)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CF2_J5_READ_BYTES_APPEND THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        ASM_REWRITE_TAC[];
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC CF2_J5_SUB_LIST_ADD THEN
        ASM_ARITH_TAC];
      MEMSAFE_EVENTS_TAC];
    (* the back edge *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `e2:(uarch_event)list` STRIP_ASSUME_TAC o
      check (is_exists o concl)) THEN
    ARM_BSTEP_TAC SNAPPY_CF2_GCC12_O2_EXEC (1--2) THEN
    CF2_BRANCH_TAC `16 * i < len` THENL [ALL_TAC; CF2_ARITH_TAC] THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN MEMSAFE_EVENTS_TAC;
    (* the end *)
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `e2:(uarch_event)list` STRIP_ASSUME_TAC o
      check (is_exists o concl)) THEN
    ARM_BSTEP_TAC SNAPPY_CF2_GCC12_O2_EXEC (1--2) THEN
    CF2_BRANCH_TAC `16 * (len + 15) DIV 16 < len` THENL [CF2_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`;
                   `word_add op (word P):int64`; `16 * (len + 15) DIV 16`;
                   `len:num`; `src:byte list`; `ne:num`; `s2:armstate`]
                  CF2_J5_READ_BYTES_PREFIX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CF2_J5_READ_BYTES_APPEND THEN ASM_REWRITE_TAC[];
      MEMSAFE_EVENTS_TAC]]);;

(* Tactics of the join5 piece *)

let CF2_J5_WSUB = WORD_RULE `word_sub (word_add a b) a:int64 = b`;;

let CF2_J5_AND65535 = prove
 (`!x:int32. word_and x (word 65535) = word(val x MOD 65536)`,
  GEN_TAC THEN MP_TAC(ISPECL [`x:int32`; `16`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* Replace the fact read c s = v (s the current state) by read c s = t,     *)
(* proving v = t with tac.                                                  *)

let CF2_J5_FIX_TAC (c:term) (t:term) (tac:tactic) : tactic = fun (asl,w) ->
  let s = rand w in
  let _,th = find (fun (_,th) -> is_eq(concl th) &&
      (match lhs(concl th) with
         Comb(Comb(Const("read",_),c'),s') -> c' = c && s' = s
       | _ -> false)) asl in
  let v = rhs(concl th) in
  let eth = TAC_PROOF((asl,mk_eq(v,t)),tac) in
  (FIRST_X_ASSUM(fun th' -> if concl th' = concl th
                            then ASSUME_TAC(TRANS th' eth) else failwith ""))
  (asl,w);;

let CF2_J5_VAL_TAC =
  REWRITE_TAC[CF2_J5_WSUB; CF2_J5_AND65535] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC CF2_VAL_RULES THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CF2_MOD_ELIM_TAC THEN
  REWRITE_TAC CF2_VAL_RULES THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CF2_MOD_ELIM_TAC THEN CF2_ARITH_TAC;;

let CF2_J5_HASH8_TAC =
  FIRST_ASSUM(fun pth -> if concl pth = `snappy_pow2 ts`
    then ASM_SIMP_TAC[SNAPPY_HASH8_WORD; SNAPPY_LOAD64_BOUND; pth]
    else failwith "CF2_J5_HASH8_TAC");;

(* e < ts and 2 * e + 2 <= 2 * ts for a hash e, for the orthogonality      *)
(* of its entry from the other regions.                                      *)

let CF2_J5_ENTRY_BOUND_TAC (e:term) : tactic =
  SUBGOAL_THEN (mk_conj(mk_binary "<" (e,`ts:num`),
     mk_binary "<=" (mk_binary "+" (mk_binary "*" (`2`,e),`2`),`2 * ts`)))
   STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `e < ts ==> e < ts /\ 2 * e + 2 <= 2 * ts`) THEN
    ASM_SIMP_TAC[SNAPPY_HASH4_LT; SNAPPY_HASH8_LT; ARITH_RULE
      `128 <= ts ==> ~(ts = 0)`];
    ALL_TAC];;

(* CF2_TABLE_SPLIT_TAC with the table bound for an updated table (eta).  *)

let CF2_J5_TABLE_SPLIT_TAC (a:term) (e:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let th = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes",_),Comb(Comb(Const(",",_),a'),_)))),s')),
           Comb(Comb(Const("snappy_tval",_),_),_)) -> a' = a && s' = s
    | _ -> false) asl) in
  let t = rand(rhs(concl th)) and k = lhand(rhs(concl th)) in
  let ith = ISPECL [`memory:(armstate,int64->byte)component`; a; k; t; e; s]
                   SNAPPY_TABLE_SPLIT in
  (MP_TAC ith THEN ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
      [ACCEPT_TAC th;
       ASM_SIMP_TAC[SNAPPY_HASH4_LT; SNAPPY_HASH8_LT; ARITH_RULE
         `128 <= ts ==> ~(ts = 0)`] THEN CF2_ARITH_TAC;
       MATCH_MP_TAC SNAPPY_TBOUND_16 THEN REWRITE_TAC[ETA_AX] THEN
       FIRST_ASSUM(fun bth -> match concl bth with
           Comb(Comb(Const("snappy_tbound",_),t'),b) when t' = t ->
             EXISTS_TAC b THEN CONJ_TAC THENL [ACCEPT_TAC bth; CF2_ARITH_TAC]
         | _ -> failwith "")];
     STRIP_TAC]) (asl,w);;

(* A store of v to the entry e of the table at tbl (a uint16_t table of ts *)
(* entries) by the steps m..n: split the table fact, run the steps (with    *)
(* the rewrites for the address), and put the table together again.        *)

let CF2_J5_STORE_TAC ?(rewrites=[]) (tbl:term) (e:term) (v:term) (m,n) : tactic =
  fun (asl,w) ->
    let s = rand w in
    let _,th = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
          Comb(Comb(Const(":>",_),Const("memory",_)),
               Comb(Const("bytes",_),Comb(Comb(Const(",",_),a'),k)))),s')),
             Comb(Comb(Const("snappy_tval",_),_),_)) ->
           a' = tbl && s' = s && k = `2 * ts`
      | _ -> false) asl in
    let t = rand(rhs(concl th)) in
    let sn = mk_var("s"^string_of_int n,`:armstate`) in
    let goal = subst [sn,`s:armstate`; tbl,`a:int64`; t,`t:num->num`;
                      e,`e:num`; v,`v:num`]
      `read (memory :> bytes(a,2 * ts)) s = snappy_tval ts (snappy_tupd t e v)` in
    let is_part th = match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
          Comb(Comb(Const(":>",_),Const("memory",_)),c)),_)),_) ->
          (match c with
             Comb(Const("bytes",_),Comb(Comb(Const(",",_),a'),k)) ->
               (a' = tbl && k = mk_binary "*" (`2`,e)) ||
               (try lhand(a') = tbl &&
                    rand(rand a') = mk_binary "+" (mk_binary "*" (`2`,e),`2`)
                with Failure _ -> false)
           | Comb(Const("bytes16",_),a') ->
               (try lhand a' = tbl && rand(rand a') = mk_binary "*" (`2`,e)
                with Failure _ -> false)
           | _ -> false)
      | _ -> false in
    (CF2_J5_ENTRY_BOUND_TAC e THEN CF2_J5_TABLE_SPLIT_TAC tbl e THEN
     ARM_BSTEP_TAC ~rewrites SNAPPY_CF2_GCC12_O2_EXEC (m--n) THEN
     SUBGOAL_THEN goal ASSUME_TAC THENL [CF2_TABLE_JOIN_TAC; ALL_TAC] THEN
     DISCARD_ASSUMPTIONS_TAC is_part THEN
     SUBGOAL_THEN (list_mk_icomb "snappy_tbound"
                    [list_mk_icomb "snappy_tupd" [t;e;v]; `LENGTH(src:byte list) - 4`])
      ASSUME_TAC THENL [SNAPPY_TB_TAC; ALL_TAC]) (asl,w);;

let CF2_J5_SYM tm = ISPECL [lhand tm; rand tm] WORD_ADD_SYM;;

let CF2_J5_HASH4_TAC =
  FIRST_ASSUM(fun pth -> if concl pth = `snappy_pow2 ts`
    then ASM_SIMP_TAC[CF2_J5_HASH4_WORD; SNAPPY_LOAD32_BOUND; pth]
    else failwith "CF2_J5_HASH4_TAC");;

(* A branch on data, the condition proved equivalent to cond by tac.       *)

let CF2_J5_BRANCH_TAC (cond:term) (tac:tactic) : tactic = fun (asl,w) ->
  let s = rand w in
  let is_pc th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),r)
        -> s' = s && is_cond r
    | _ -> false in
  let pcth = snd(find (is_pc o snd) asl) in
  let b,_ = dest_cond(rhs(concl pcth)) in
  let eqth = TAC_PROOF((asl,mk_iff(b,cond)),tac) in
  (ASM_CASES_TAC cond THEN
   FIRST_X_ASSUM(fun cth ->
     FIRST_X_ASSUM(fun th -> if concl th = concl pcth then
        ASSUME_TAC(REWRITE_RULE[eqth; cth] th) else failwith "") THEN
     ASSUME_TAC cth)) (asl,w);;


(* The output bound: the literal's writes are below the end of the region. *)

let CF2_J5_OUTBOUND_TAC =
  SUBGOAL_THEN
   `LENGTH(out:byte list) + (ip - ne) + 25 <=
    snappy_max_compressed_length (LENGTH(src:byte list)) - 5`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `LENGTH(src:byte list)` SNAPPY_MAX_COMPRESSED_LENGTH_32) THEN
    ANTS_TAC THENL [CF2_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `ne DIV 30 <= LENGTH(src:byte list) DIV 6` MP_TAC THENL
     [TRANS_TAC LE_TRANS `LENGTH(src:byte list) DIV 30` THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIV_MONO THEN CF2_ARITH_TAC;
        MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC];
      CF2_ARITH_TAC];
    ALL_TAC];;

(* Bounds a + k <= M of the form the frame check of a store uses.           *)

let CF2_J5_BOUNDS_TAC (tms:term list) =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL [CF2_ARITH_TAC; ALL_TAC]) tms;;

(* The value of a component in the current state.                          *)

let cf2_j5_value (c:term) (asl,w) =
  let s = rand w in
  rhs(concl(snd(find (fun (_,th) -> is_eq(concl th) &&
     (match lhs(concl th) with
        Comb(Comb(Const("read",_),c'),s') -> c' = c && s' = s
      | _ -> false)) asl)));;

(* loop11, from the state with X1 = inp + ne, X15 = op + P, X2 = op + P +  *)
(* len and bytes(op,P) = v, to its end.                                    *)

let CF2_J5_LOOP11_TAC (len:term) (p:term) (v:term) (sname:string) : tactic =
  fun (asl,w) ->
    let e = cf2_j5_value `events` (asl,w) in
    let th = SPECL [`src:byte list`; `inp:int64`; `ne:num`; len; `op:int64`; p;
                    `snappy_max_compressed_length (LENGTH(src:byte list)) - 5`;
                    v; `pc:num`; e] CF2_J5_LOOP11 in
    let ant = lhand(concl th) in
    let ath = TAC_PROOF((asl,ant),
      REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY CF2_ARITH_TAC) in
    ARM_BSTEP_CALL_TAC SNAPPY_CF2_GCC12_O2_EXEC (MP th ath) sname (asl,w);;

(* signed conditions *)
let CF2_J5_SCOND_TAC (ths:thm list) =
  SIMP_TAC[WORD_SUB_0; WORD_ZX_WORD_SIMPLE; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC ths THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ] THEN
  REWRITE_TAC CF2_VAL_RULES THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CF2_MOD_ELIM_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE] THEN
  W(fun (asl,w) -> ACCEPT_TAC(TAC_PROOF((cf2_arith_asl asl,w),
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LT;
                                GSYM INT_OF_NUM_LE]) THEN
    ASM_INT_ARITH_TAC)));;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let CF2_J5_EXEC = SNAPPY_CF2_GCC12_O2_EXEC;;

let cf2_j5_is_emit_eq th =
  is_eq(concl th) &&
  (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "snappy_emit_literal"
   with Failure _ -> false);;

let cf2_j5_ival_facts asl =
  map snd (filter (fun (_,th) ->
    can (find_term ((=) `ival:int64->int`)) (concl th) ||
    can (find_term ((=) `ival:int32->int`)) (concl th)) asl);;

let cf2_j5_ival_eqs asl =
  map snd (filter (fun (_,th) -> is_eq(concl th) &&
    (can (find_term ((=) `ival:int64->int`)) (lhs(concl th)) ||
     can (find_term ((=) `ival:int32->int`)) (lhs(concl th)))) asl);;

(* The state at loop5: phase 4 with the three table updates and the output   *)
(* out', from the state ip ne sk c x t1 t2 out at join5.                      *)

let cf2_j5_st4 out' =
  subst [out',`out':byte list`]
   `SnappyCState 4 ip ne sk c x
     (snappy_tupd t1 (snappy_hash4 ts (snappy_load32 src (ip + 1))) (ip + 1))
     (snappy_tupd (snappy_tupd t2 (snappy_hash8 ts (snappy_load64 src (ip + 1)))
                               (ip + 1))
                  (snappy_hash8 ts (snappy_load64 src (ip + 2))) (ip + 2))
     out'`;;

let CF2_J5_ST4 = cf2_j5_st4
  `APPEND out (snappy_emit_literal (SUB_LIST(ne,ip - ne) src))`;;

(* The tag byte (len - 1) << 2 of a literal of up to 60 bytes.              *)

let CF2_J5_TAG_TAC =
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_SHL; VAL_WORD_SUBWORD;
              VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
  REPEAT CF2_MOD_ELIM_TAC THEN CF2_ARITH_TAC;;

(* op + k + sx(w), w the 32-bit length ip - ne (plus 1 if one), as          *)
(* op + k + (ip - ne) (+ 1).                                                 *)

let CF2_J5_SX_TAC (n:term) : tactic = fun (asl,w) ->
  let sx = hd(find_terms (fun t -> is_comb t &&
     (try fst(dest_const(rator t)) = "word_sx" with Failure _ -> false) &&
     not(is_numeral(rand(rand t)))) w) in
  let e = rand sx in
  let wn32 = mk_comb(`word:num->int32`,n) in
  (SUBGOAL_THEN (mk_eq(e,wn32)) SUBST1_TAC THENL
    [REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC CF2_VAL_RULES THEN
     CONV_TAC NUM_REDUCE_CONV THEN REPEAT CF2_MOD_ELIM_TAC THEN CF2_ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN (mk_eq(mk_comb(`word_sx:int32->int64`,wn32),
                       mk_comb(`word:num->int64`,n))) SUBST1_TAC THENL
    [MATCH_MP_TAC CF2_J5_WORD_SX32 THEN CF2_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC WORD_REDUCE_CONV THEN CF2_WORD_EQ_TAC) (asl,w);;

(* Rewrite with the fact whose left side is l.                               *)

let CF2_J5_READ_EQ_TAC (l:term) : tactic =
  FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = l
                        then REWRITE_TAC[th] else failwith "CF2_J5_READ_EQ_TAC");;

let cf2_j5_bytes s a n =
  list_mk_icomb "read"
   [mk_icomb(`(:>) (memory:(armstate,int64->byte)component)`,
             mk_comb(`bytes:int64#num->(int64->byte,num)component`,mk_pair(a,n)));
    s];;

(* The output after the literal: from the fact read (bytes(op,P + len)) s at *)
(* the state s (the bytes before the data are v), its form as out followed   *)
(* by the literal, with the literal as the tag t, the length bytes h and the *)
(* data.                                                                     *)

let CF2_J5_OUT_TAC (tag:term) (h:term) (pfx:term) (s:term) =
  let d = `SUB_LIST(ne,ip - ne) (src:byte list)` in
  SUBGOAL_THEN `LENGTH(SUB_LIST(ne,ip - ne) (src:byte list)) = ip - ne`
   ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN CF2_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   (mk_eq(`snappy_emit_literal (SUB_LIST(ne,ip - ne) src)`,
          mk_icomb(mk_icomb(`CONS:byte->byte list->byte list`,tag),
                   mk_icomb(mk_icomb(`APPEND:byte list->byte list->byte list`,h),
                            d))))
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[snappy_emit_literal; APPEND] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
           CONV_TAC NUM_REDUCE_CONV THEN TRY(CF2_ARITH_TAC THEN NO_TAC)) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `op:int64`;
                 `out:byte list`; tag; h; d; s] CF2_J5_LIT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; LENGTH] THEN
    W(fun (asl,w) ->
      let n = rand(rand(rand(lhand(lhand w)))) in
      let n' = mk_binary "+" (pfx,`ip - ne`) in
      SUBGOAL_THEN (mk_eq(n,n')) SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      CF2_J5_READ_EQ_TAC (cf2_j5_bytes s `op:int64` n')) THEN
    REWRITE_TAC[num_of_bytelist; LEFT_ADD_DISTRIB; EXP_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUM_RING;
    FIRST_ASSUM(fun th -> if cf2_j5_is_emit_eq th then REWRITE_TAC[GSYM th]
                          else failwith "") THEN
    DISCH_TAC];;

(* The end of a case with a literal: X2 as op + the length of the output,    *)
(* and loop5 with phase 4.                                                   *)

let CF2_J5_LIT_END_TAC =
  CF2_J5_FIX_TAC `X2`
   `word_add op (word(LENGTH(APPEND out (snappy_emit_literal
                   (SUB_LIST(ne,ip - ne) src))))):int64`
   (ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_BYTELIST_OF_NUM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CF2_ARITH_TAC) THEN
  DISCARD_ASSUMPTIONS_TAC cf2_j5_is_emit_eq THEN
  BSTEP_FINAL_TAC THEN
  CF2_TARGET_TAC `CompressFragmentDoubleHash_loop5:num` CF2_J5_ST4 [];;

(* bytes(op,lo + 1) = out and the tag, at the state s.                      *)

let CF2_J5_TAGGED_TAC (tag:term) (s:term) =
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `op:int64`; `lo:num`;
                 `1`; `num_of_bytelist out`; mk_comb(`val:byte->num`,tag); s]
         CF2_J5_READ_BYTES_APPEND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[READ_MEMORY_BYTES_BYTES8]; DISCH_TAC];;

let cf2_j5_v0 tag =
  subst [tag,`t:byte`] `num_of_bytelist out + 2 EXP (8 * lo) * val(t:byte)`;;

(* Up to 16 bytes (+0x778): the tag, then 16 bytes of the input at once.     *)

let CF2_J5_SHORT_TAC =
  let tag = `word(4 * (ip - ne - 1)):byte` in
  CF2_INPUT_TAC SNAPPY_READ_LOAD64 `ne:num` THEN
  CF2_INPUT_TAC SNAPPY_READ_LOAD64 `ne + 8` THEN
  ARM_BSTEP_TAC CF2_J5_EXEC (24--30) THEN
  CF2_J5_FIX_TAC `memory :> bytes8 (word_add op (word lo))` tag
    CF2_J5_TAG_TAC THEN
  CF2_J5_FIX_TAC `X2` `word_add op (word((lo + 1) + (ip - ne))):int64`
    (CF2_J5_SX_TAC `ip - ne + 1`) THEN
  SUBGOAL_THEN `read (memory :> bytes(word_add op (word(lo + 1)),16)) s30 =
                num_of_bytelist(SUB_LIST(ne,16) src)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CF2_J5_LOAD64_PAIR] THEN
    MATCH_MP_TAC CF2_J5_BYTES64_PAIR THEN
    REWRITE_TAC[SNAPPY_LOAD64_BOUND] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`;
                 `word_add op (word(lo + 1)):int64`; `16`; `ip - ne`;
                 `src:byte list`; `ne:num`; `s30:armstate`]
                CF2_J5_READ_BYTES_PREFIX) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; CF2_ARITH_TAC];
                  DISCH_TAC] THEN
  CF2_J5_TAGGED_TAC tag `s30:armstate` THEN
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `op:int64`;
                 `lo + 1`; `ip - ne`; cf2_j5_v0 tag;
                 `num_of_bytelist(SUB_LIST(ne,ip - ne) (src:byte list))`;
                 `s30:armstate`] CF2_J5_READ_BYTES_APPEND) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  ARM_BSTEP_TAC CF2_J5_EXEC (31--31) THEN
  CF2_J5_OUT_TAC tag `[]:byte list` `lo + 1` `s31:armstate` THEN
  CF2_J5_LIT_END_TAC;;

(* 17 to 60 bytes (+0x748): the tag, then loop11.                            *)

let CF2_J5_MEDIUM_TAC =
  let tag = `word(4 * (ip - ne - 1)):byte` in
  ARM_BSTEP_TAC CF2_J5_EXEC (26--31) THEN
  CF2_J5_FIX_TAC `memory :> bytes8 (word_add op (word lo))` tag
    CF2_J5_TAG_TAC THEN
  CF2_J5_FIX_TAC `X15` `word_add op (word(lo + 1)):int64` CF2_WORD_EQ_TAC THEN
  CF2_J5_FIX_TAC `X2` `word_add op (word((lo + 1) + (ip - ne))):int64`
    (CF2_J5_SX_TAC `ip - ne`) THEN
  CF2_J5_TAGGED_TAC tag `s31:armstate` THEN
  CF2_J5_LOOP11_TAC `ip - ne` `lo + 1` (cf2_j5_v0 tag) "s32" THEN
  ARM_BSTEP_TAC CF2_J5_EXEC (33--33) THEN
  CF2_J5_OUT_TAC tag `[]:byte list` `lo + 1` `s33:armstate` THEN
  CF2_J5_LIT_END_TAC;;

(* More than 60 bytes (+0x544): the tag 60 or 61 and the length - 1 in cnt   *)
(* = 1 or 2 bytes (q = clz / 8 = 3 or 2), then loop11.                       *)

let CF2_J5_LONG_TAC q cnt tag =
  let cnt_tm = mk_small_numeral cnt
  and tagb = mk_comb(`word:num->byte`,mk_small_numeral tag) in
  let p = mk_binary "+" (`lo + 1`,cnt_tm) in
  let h = list_mk_icomb "bytelist_of_num" [cnt_tm; `ip - ne - 1`] in
  let v0 = cf2_j5_v0 tagb in
  let v = mk_binary "+"
   (v0, mk_binary "*" (`2 EXP (8 * (lo + 1))`, mk_icomb(`num_of_bytelist`,h))) in
  let s36 = `s36:armstate` in
  CF2_J5_FIX_TAC `X6` (mk_comb(`word:num->int64`,mk_small_numeral q))
   (REWRITE_TAC[CF2_J5_ZX32] THEN
    SIMP_TAC[CF2_J5_ISHR_SMALL; CF2_J5_CLZ_SMALL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[CF2_J5_CLZ_DIV8] THEN
    CONV_TAC WORD_REDUCE_CONV) THEN
  CF2_J5_FIX_TAC `memory :> bytes32 (word_add op (word (lo + 1)))`
   `word(ip - ne - 1):int32` (REWRITE_TAC[CF2_J5_ZX32]) THEN
  ARM_BSTEP_TAC CF2_J5_EXEC (29--36) THEN
  CF2_J5_FIX_TAC `X15`
   (mk_icomb(`word_add (op:int64)`,mk_comb(`word:num->int64`,p)))
   (CONV_TAC WORD_REDUCE_CONV THEN CF2_WORD_EQ_TAC) THEN
  CF2_J5_FIX_TAC `X2`
   (mk_icomb(`word_add (op:int64)`,
             mk_comb(`word:num->int64`,mk_binary "+" (p,`ip - ne`))))
   (CF2_J5_SX_TAC `ip - ne`) THEN
  CF2_J5_FIX_TAC `memory :> bytes8 (word_add op (word lo))` tagb
   (CONV_TAC WORD_REDUCE_CONV) THEN
  CF2_J5_TAGGED_TAC tagb s36 THEN
  SUBGOAL_THEN (mk_eq(cf2_j5_bytes s36 `word_add op (word(lo + 1)):int64` cnt_tm,
                      mk_icomb(`num_of_bytelist`,h))) ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[NUM_OF_BYTELIST_OF_NUM_EQ]
     `n < 256 EXP k /\ x = n ==> x = num_of_bytelist(bytelist_of_num k n)`) THEN
    CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CF2_J5_BYTES_OF_32 THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC;
                    CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`; `op:int64`;
                 `lo + 1`; cnt_tm; v0; mk_icomb(`num_of_bytelist`,h); s36]
         CF2_J5_READ_BYTES_APPEND) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  CF2_J5_LOOP11_TAC `ip - ne` p v "s37" THEN
  ARM_BSTEP_TAC CF2_J5_EXEC (38--38) THEN
  CF2_J5_OUT_TAC tagb h p `s38:armstate` THEN
  CF2_J5_LIT_END_TAC;;

(* No literal (next_emit = ip): loop5 with the output as it was.            *)

let CF2_J5_NOLIT_TAC =
  ARM_BSTEP_TAC CF2_J5_EXEC (19--20) THEN
  SUBGOAL_THEN `ival(word(ip - ne):int64) = &(ip - ne)` ASSUME_TAC THENL
   [MATCH_MP_TAC CF2_J5_IVAL_WORD64 THEN CF2_ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> CF2_J5_BRANCH_TAC `0 < ip - ne`
     (CF2_J5_SCOND_TAC (cf2_j5_ival_facts asl))) THENL
   [UNDISCH_TAC `0 < ip - ne` THEN UNDISCH_TAC `~(ne < ip)` THEN ARITH_TAC;
    BSTEP_FINAL_TAC THEN
    CF2_TARGET_TAC `CompressFragmentDoubleHash_loop5:num`
     (cf2_j5_st4 `out:byte list`) []];;

let SNAPPY_CF2_GCC12_O2_JOIN5 = prove
 (SNAPPY_CF2_GCC12_O2_JOIN5_STMT,
  CF2_PIECE_START_TAC THEN CF2_INIT_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `ts:num`)) THEN
  CF2_INPUT_TAC SNAPPY_READ_LOAD64 `ip + 1` THEN
  CF2_INPUT_TAC SNAPPY_READ_LOAD64 `ip + 2` THEN
  CF2_INPUT_TAC SNAPPY_READ_LOAD32 `ip + 1` THEN
  ARM_BSTEP_TAC CF2_J5_EXEC (1--9) THEN
  CF2_J5_OUTBOUND_TAC THEN ABBREV_TAC `lo = LENGTH(out:byte list)` THEN
  CF2_J5_BOUNDS_TAC
   (map (fun k -> parse_term ("(" ^ k ^ ") <= snappy_max_compressed_length " ^
                              "(LENGTH(src:byte list)) - 5"))
        ["lo + 1"; "(lo + 1) + 8"; "lo + 17"; "lo + 5"; "(lo + 1) + 4"]) THEN
  SUBGOAL_THEN `snappy_tbound t2 (LENGTH(src:byte list) - 4) /\
                snappy_tbound t1 (LENGTH(src:byte list) - 4)`
   STRIP_ASSUME_TAC THENL [CONJ_TAC THEN SNAPPY_TB_TAC; ALL_TAC] THEN
  CF2_J5_FIX_TAC `X15` `word(ip + 1):int64` CF2_J5_VAL_TAC THEN
  CF2_J5_FIX_TAC `X6` `word(ip + 2):int64` CF2_J5_VAL_TAC THEN
  CF2_J5_FIX_TAC `X7`
   `word(2 * snappy_hash8 ts (snappy_load64 src (ip + 1))):int64`
   CF2_J5_HASH8_TAC THEN
  CF2_J5_STORE_TAC ~rewrites:[CF2_J5_SYM
    `word_add (word (2 * snappy_hash8 ts (snappy_load64 src (ip + 1))))
              (table2:int64)`]
   `table2:int64` `snappy_hash8 ts (snappy_load64 src (ip + 1))` `ip + 1`
   (10,10) THEN
  ARM_BSTEP_TAC CF2_J5_EXEC (11--13) THEN
  CF2_J5_FIX_TAC `X7`
   `word(2 * snappy_hash8 ts (snappy_load64 src (ip + 2))):int64`
   CF2_J5_HASH8_TAC THEN
  CF2_J5_STORE_TAC ~rewrites:[CF2_J5_SYM
    `word_add (word (2 * snappy_hash8 ts (snappy_load64 src (ip + 2))))
              (table2:int64)`]
   `table2:int64` `snappy_hash8 ts (snappy_load64 src (ip + 2))` `ip + 2`
   (14,14) THEN
  ARM_BSTEP_TAC CF2_J5_EXEC (15--17) THEN
  CF2_J5_FIX_TAC `X6`
   `word(2 * snappy_hash4 ts (snappy_load32 src (ip + 1))):int64`
   CF2_J5_HASH4_TAC THEN
  SUBGOAL_THEN
   `word_zx(word_zx(word (2 * snappy_hash4 ts (snappy_load32 src (ip + 1)))
                    :int64):int32):int64 =
    word(2 * snappy_hash4 ts (snappy_load32 src (ip + 1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC CF2_J5_ZXZX THEN
    MATCH_MP_TAC(ARITH_RULE `e < 16384 ==> 2 * e < 2 EXP 32`) THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `ts:num` THEN
    ASM_SIMP_TAC[SNAPPY_HASH4_LT; ARITH_RULE `128 <= ts ==> ~(ts = 0)`];
    ALL_TAC] THEN
  FIRST_ASSUM(fun zth ->
    if is_eq(concl zth) &&
       can (find_term ((=) `word_zx:int32->int64`)) (lhs(concl zth))
    then CF2_J5_STORE_TAC ~rewrites:[zth] `table:int64`
           `snappy_hash4 ts (snappy_load32 src (ip + 1))` `ip + 1` (18,18)
    else failwith "") THEN
  CF2_J5_FIX_TAC `X17` `word(ip - ne):int64`
   (REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
    ASM_SIMP_TAC[WORD_SUB]) THEN
  ASM_CASES_TAC `ne < ip` THENL
   [ARM_BSTEP_TAC CF2_J5_EXEC (19--20) THEN
    SUBGOAL_THEN
     `ival(word(ip - ne):int64) = &(ip - ne) /\
      ival(word(ip - ne):int32) = &(ip - ne) /\
      ival(word_sub (word(ip - ne)) (word 16):int32) = &(ip - ne) - &16`
     STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC CF2_J5_IVAL_WORD64) THEN
      TRY(MATCH_MP_TAC CF2_J5_IVAL_WORD32) THEN
      TRY(MATCH_MP_TAC CF2_J5_IVAL_SUB32) THEN CF2_ARITH_TAC;
      ALL_TAC] THEN
    W(fun (asl,w) -> CF2_J5_BRANCH_TAC `0 < ip - ne`
       (CF2_J5_SCOND_TAC (cf2_j5_ival_facts asl))) THENL
     [ARM_BSTEP_TAC CF2_J5_EXEC (21--23) THEN
      CF2_J5_FIX_TAC `X7` `word(ip - ne - 1):int64`
       (MATCH_MP_TAC CF2_J5_ZX_SUB1 THEN CF2_ARITH_TAC) THEN
      W(fun (asl,w) -> CF2_J5_BRANCH_TAC `ip - ne <= 16`
         (CF2_J5_SCOND_TAC (cf2_j5_ival_eqs asl))) THENL
       [CF2_J5_SHORT_TAC;
        ARM_BSTEP_TAC CF2_J5_EXEC (24--25) THEN
        SUBGOAL_THEN
         `ival(word(ip - ne - 1):int32) = &(ip - ne - 1) /\
          ival(word_sub (word(ip - ne - 1)) (word 59):int32) =
          &(ip - ne - 1) - &59`
         STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC CF2_J5_IVAL_WORD32) THEN
          TRY(MATCH_MP_TAC CF2_J5_IVAL_SUB32) THEN CF2_ARITH_TAC;
          ALL_TAC] THEN
        W(fun (asl,w) -> CF2_J5_BRANCH_TAC `ip - ne - 1 <= 59`
           (CF2_J5_SCOND_TAC (cf2_j5_ival_eqs asl))) THENL
         [CF2_J5_MEDIUM_TAC;
          SUBGOAL_THEN `0 < ip - ne - 1 /\ ip - ne - 1 < 65536`
           STRIP_ASSUME_TAC THENL [CONJ_TAC THEN CF2_ARITH_TAC; ALL_TAC] THEN
          ARM_BSTEP_TAC CF2_J5_EXEC (26--28) THEN
          ASM_CASES_TAC `ip - ne - 1 < 256` THENL
           [CF2_J5_LONG_TAC 3 1 240; CF2_J5_LONG_TAC 2 2 244]]];
      UNDISCH_TAC `~(0 < ip - ne)` THEN UNDISCH_TAC `ne < ip` THEN ARITH_TAC];
    CF2_J5_NOLIT_TAC]);;
