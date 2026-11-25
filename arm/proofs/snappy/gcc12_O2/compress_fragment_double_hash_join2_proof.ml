(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece from join2, emit_remainder (phase 5): if ip < ip_end, the tag   *)
(* of the literal of the rest of the input (one byte for up to 60 bytes,     *)
(* else one or two bytes of the length after it), then memcpy through the    *)
(* PLT of the data after the tag, and the return with the output of the     *)
(* model; otherwise the return at once.                                      *)
(*                                                                           *)
(*   +0xdc  cmp  x1, x13         +0x608 sub  x13, x13, x1                    *)
(*   +0xe0  b.cc +0x608          +0x60c sub  w3, w13, #0x1                   *)
(*   +0xe4  ldp  x19, x20, ..    +0x610 cmp  w3, #0x3b; b.le +0x754 (short)  *)
(*   +0xe8  ldp  x29, x30, ..    +0x618 .. clz, stur w3, [x2, #1] (long)     *)
(*   +0xec  ret                  join19: strb w4, [x2]; .. bl memcpy; ret    *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_join2_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Lemmas and tactics.                                                       *)
(* ------------------------------------------------------------------------- *)

let CF2_J2_SUB_OFFSETS = prove
 (`!a x y. y <= x
           ==> word_sub (word_add a (word x)) (word_add a (word y)):int64 =
               word(x - y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add a b) (word_add a c):int64 =
                         word_sub b c`] THEN
  ASM_REWRITE_TAC[WORD_SUB]);;

let CF2_J2_ZX32 = prove
 (`!k. word_zx (word k:int64):int32 = word k`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64;
              MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let CF2_J2_ZX_SUB1 = prove
 (`!k. 1 <= k /\ k < 2 EXP 32
       ==> word_zx(word_sub (word_zx(word k:int64):int32) (word 1)):int64 =
           word(k - 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CF2_J2_ZX32] THEN
  SUBGOAL_THEN `word_sub (word k) (word 1):int32 = word(k - 1)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[WORD_SUB]; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `k - 1 < 2 EXP 32 /\ k - 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `k < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]]);;

(* The signed comparison k <= 59 of the 32-bit word k.                      *)

let CF2_J2_IVAL_SMALL = prove
 (`!k. k < 2 EXP 31 ==> ival(word k:int32) = &k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_IWORD] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
  POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let CF2_J2_IVAL_SUB_SMALL = prove
 (`!k m. k < 2 EXP 31 /\ m < 2 EXP 31
         ==> ival(word_sub (word k) (word m):int32) = &k - &m`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_sub (word x) (word y):int32 = iword(&x - &y)`] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let CF2_J2_VAL_SUB_EQ0 = prove
 (`!k m. k < 2 EXP 32 /\ m < 2 EXP 32
         ==> (val(word_sub (word k) (word m):int32) = 0 <=> k = m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_32] THEN ASM_SIMP_TAC[MOD_LT]);;

(* Replace the fact read c s = v by read c s = t, with v = t proved by tac. *)

let CF2_J2_CANON_TAC (c:term) (t:term) (tac:tactic) : tactic = fun (asl,w) ->
  let s = rand w in
  let th = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s')),_) ->
        c' = c && s' = s
    | _ -> false) asl) in
  let v = rhs(concl th) in
  let eth = TAC_PROOF((asl,mk_eq(v,t)),tac) in
  (FIRST_X_ASSUM(fun th' -> if concl th' = concl th then
     ASSUME_TAC(TRANS th' eth) else failwith "")) (asl,w);;

(* The branch of b.le on w3 = k with 59, as k < 60.                         *)

let CF2_J2_LE_BRANCH_TAC (k:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let is_pc th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),r)
        -> s' = s && is_cond r
    | _ -> false in
  let pcth = snd(find (is_pc o snd) asl) in
  let b,_ = dest_cond(rhs(concl pcth)) in
  let cond = mk_binary "<" (k,`60`) in
  let kb = TAC_PROOF((cf2_arith_asl asl,mk_binary "<" (k,`2 EXP 31`)),
             CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC) in
  let kb32 = TAC_PROOF((cf2_arith_asl asl,mk_binary "<" (k,`2 EXP 32`)),
             CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC) in
  let eqth = TAC_PROOF((asl,mk_iff(b,cond)),
    REWRITE_TAC[CF2_J2_ZX32] THEN
    ASM_SIMP_TAC[kb; kb32; CF2_J2_IVAL_SMALL; CF2_J2_IVAL_SUB_SMALL; CF2_J2_VAL_SUB_EQ0;
                 ARITH_RULE `59 < 2 EXP 31 /\ 59 < 2 EXP 32`] THEN
    REWRITE_TAC[INT_LT_SUB_RADD; INT_ADD_LID; INT_OF_NUM_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[INT_ARITH `&k - &59:int = &k - &59`] THEN ARITH_TAC) in
  (ASM_CASES_TAC cond THEN
   FIRST_X_ASSUM(fun cth ->
     FIRST_X_ASSUM(fun th -> if concl th = concl pcth then
        ASSUME_TAC(REWRITE_RULE[eqth; cth] th) else failwith "") THEN
     ASSUME_TAC cth)) (asl,w);;

(* The number of bytes of the length of a long literal, from clz.           *)

let CF2_J2_CLZ_DIV8 = prove
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

let CF2_J2_ISHR_SMALL = prove
 (`!k n. k < 2 EXP 31 ==> word_ishr (word k:int32) n = word(k DIV 2 EXP n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ishr] THEN
  ASM_SIMP_TAC[CF2_J2_IVAL_SMALL] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_DIV; GSYM WORD_IWORD]);;

let CF2_J2_OUT_BOUND = prove
 (`!n ip l. n <= 65536 /\ ip <= n /\ l <= ip + ip DIV 30
            ==> l + 8 + (n - ip) <= snappy_max_compressed_length n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n < 2 EXP 32` (fun th -> REWRITE_TAC[MATCH_MP SNAPPY_MAX_COMPRESSED_LENGTH_32 th]) THENL
   [UNDISCH_TAC `n <= 65536` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ip:num`; `30`] DIVISION) THEN
  MP_TAC(SPECL [`n:num`; `6`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC);;

let CF2_J2_CONTAINED_OFFSET = prove
 (`!a k l1 l2. k + l1 <= l2 ==> contained (word_add a (word k):int64,l1) (a,l2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[contained; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  REWRITE_TAC[CONTAINED_MODULO_LMOD] THEN
  ONCE_REWRITE_TAC[GSYM CONTAINED_MODULO_LMOD] THEN
  CONV_TAC(ONCE_DEPTH_CONV MOD_DOWN_CONV) THEN
  REWRITE_TAC[CONTAINED_MODULO_LMOD] THEN
  MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN ASM_ARITH_TAC);;

let CF2_J2_IVAL_SMALL64 = prove
 (`!k. k < 2 EXP 63 ==> ival(word k:int64) = &k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_IWORD] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
  POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let CF2_J2_ISHR_SMALL64 = prove
 (`!k n. k < 2 EXP 63 ==> word_ishr (word k:int64) n = word(k DIV 2 EXP n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ishr] THEN
  ASM_SIMP_TAC[CF2_J2_IVAL_SMALL64] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_DIV; GSYM WORD_IWORD]);;

let CF2_J2_SXFROM = prove
 (`!k. k < 2 EXP 31
       ==> word_sxfrom 31 (word_subword (word k:int64) (0,32)):int64 = word k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k < 4294967296 /\ k < 18446744073709551616 /\
                4294967296 * k < 2 EXP 63` STRIP_ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_subword (word k:int64) (0,32):int64 = word k`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_64;
                ARITH_RULE `MIN 32 64 = 32`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT; DIV_1];
    ALL_TAC] THEN
  REWRITE_TAC[word_sxfrom; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_SHL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[CF2_J2_ISHR_SMALL64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  AP_TERM_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC);;

let CF2_J2_CLZ_SMALL = prove
 (`!x:int32. word_clz x < 2 EXP 31`,
  GEN_TAC THEN MP_TAC(ISPEC `x:int32` WORD_CLZ_LE_DIMINDEX) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* The bytes of the output.                                                *)

let CF2_J2_APPEND_BYTE = prove
 (`!(m:(S,int64->byte)component) op (p:byte list) b k s.
     read (m :> bytes(op,k)) s = num_of_bytelist p /\ LENGTH p = k /\
     read (m :> bytes8 (word_add op (word k))) s = b
     ==> read (m :> bytes(op,k + 1)) s = num_of_bytelist(APPEND p [b])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SNAPPY_NUM_OF_BYTELIST_APPEND; num_of_bytelist; MULT_CLAUSES;
              ADD_CLAUSES] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_BYTES8] THEN
  ASM_REWRITE_TAC[]);;

let CF2_J2_APPEND = prove
 (`!(m:(S,int64->byte)component) op (p:byte list) d k j s.
     read (m :> bytes(op,k)) s = num_of_bytelist p /\ LENGTH p = k /\
     read (m :> bytes(word_add op (word k),j)) s = num_of_bytelist d /\
     LENGTH d = j
     ==> read (m :> bytes(op,k + j)) s = num_of_bytelist(APPEND p d)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
              SNAPPY_NUM_OF_BYTELIST_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[]);;

let CF2_J2_BYTES_OF_32 = prove
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

let CF2_J2_WORD_EQ_TAC =
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC(CF2_VAL_RULES @ [VAL_WORD_SHL; VAL_WORD_SUBWORD; DIV_1; EXP; MIN]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CF2_MOD_ELIM_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN TRY CF2_ARITH_TAC;;

let CF2_J2_FINAL_OUT = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\
     snappy_cf2_reach src (SnappyCState 5 ip ne sk c x t1 t2 out)
     ==> snappy_compress_fragment 2 src =
         (if ip < LENGTH src
          then APPEND out (snappy_emit_literal (SUB_LIST(ip,LENGTH src - ip) src))
          else out)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`src:byte list`;
    `snappy_cf2_step src (SnappyCState 5 ip ne sk c x t1 t2 out)`]
    SNAPPY_CF2_REACH_DONE) THEN
  ASM_SIMP_TAC[SNAPPY_CF2_REACH_STEP] THEN
  SNAPPY_CF2_UNFOLD_TAC THEN REWRITE_TAC[snappy_phase; snappy_out]);;

(* The contract's disjointness hypotheses: the destination is in the output *)
(* region, the source in the input.                                          *)

let CF2_J2_NONOV_TAC =
  MATCH_MP_TAC NONOVERLAPPING_SUBREGIONS THEN
  FIRST (map (fun (b2,l2) ->
     MAP_EVERY EXISTS_TAC
      [`op:int64`; `snappy_max_compressed_length (LENGTH(src:byte list)) - 5`;
       b2; l2] THEN
     REPEAT CONJ_TAC THENL
      [REWRITE_TAC[nonoverlapping; DIMINDEX_64] THEN FIRST_ASSUM ACCEPT_TAC;
       MATCH_MP_TAC CF2_J2_CONTAINED_OFFSET THEN ASM_REWRITE_TAC[] THEN CF2_ARITH_TAC;
       (REWRITE_TAC[contained; CONTAINED_MODULO_REFL; LE_REFL] THEN NO_TAC) ORELSE
       (MATCH_MP_TAC CF2_J2_CONTAINED_OFFSET THEN ASM_REWRITE_TAC[] THEN
        CF2_ARITH_TAC)] THEN NO_TAC)
   [(`ea:int64`,`el:num`); (`inp:int64`,`LENGTH(src:byte list)`)]);;

let CF2_J2_CALL_TAC execth (args:term list) sname : tactic =
  USE_THEN "H_MEMCPY" (fun th -> W(fun (asl,w) ->
    let s' = rand w in
    let vals = map (arm_bstep_eval asl s') args in
    let sth = SPECL vals th in
    let sth = CONV_RULE(REWRITE_CONV[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                    MODIFIABLE_UPPER_SIMD_REGS; ALLPAIRS; ALL;
                    PAIRWISE] THENC DEPTH_CONV VAL_WORD_NUMERAL_CONV) sth in
    let hth = TAC_PROOF((asl,lhand(concl sth)),
                        REPEAT CONJ_TAC THEN CF2_J2_NONOV_TAC) in
    let vths = mapfilter (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("val",_),Comb(Const("word",_),_))),_)
          -> th
      | _ -> fail()) asl in
    ARM_BSTEP_CALL_TAC execth (PURE_REWRITE_RULE vths (MP sth hth)) sname));;

let CF2_J2_APPEND_CONS = prove
 (`!(l:A list) t d. APPEND l (CONS t d) = APPEND (APPEND l [t]) d`,
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

(* Rewriting with the assumptions except the contracts and the events.     *)

let CF2_J2_ASM_REWRITE_TAC thl : tactic = fun (asl,w) ->
  let bad t = match t with
      Const(("ensures"|"events"|"memaccess_inbounds"),_) -> true
    | _ -> false in
  let ths = mapfilter (fun (_,th) ->
      if can (find_term bad) (concl th) then fail() else th) asl in
  REWRITE_TAC (thl @ ths) (asl,w);;

let CF2_J2_REG_TAC : tactic = fun (asl,w) ->
  let l = lhs w in
  let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = l) asl) in
  (GEN_REWRITE_TAC LAND_CONV [th] THEN
   FIRST [REFL_TAC; W(fun (_,w) -> ACCEPT_TAC(WORD_RULE w));
          REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          (REFL_TAC ORELSE (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC))])
  (asl,w);;

let CF2_J2_ASSUME_REWRITE_TAC (tms:term list) : tactic = fun (asl,w) ->
  let ths = map (fun t -> snd(find (fun (_,th) -> concl th = t) asl)) tms in
  REWRITE_TAC ths (asl,w);;

let CF2_J2_OFS_EQ_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  (REFL_TAC ORELSE (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC));;


(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let CF2_J2_EXEC = SNAPPY_CF2_GCC12_O2_EXEC;;

let CF2_J2_LABEL_MEMCPY_TAC =
  FIRST_X_ASSUM(fun th -> match concl th with
     Comb(Comb(Comb(Comb(Const(("memcpy_contract"|
                                "memcpy_correct_safe_contract") as nm,_),_),_),_),_) ->
       LABEL_TAC "H_MEMCPY" (REWRITE_RULE[if nm = "memcpy_contract"
         then memcpy_contract else memcpy_correct_safe_contract] th)
   | _ -> failwith "");;

let CF2_J2_SX_TAC =
  MATCH_MP_TAC CF2_J2_SXFROM THEN CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC;;

(* The call of memcpy(op + k, ip, n - ip) at the bl at step bl, the return   *)
(* and the epilogue, to the end of the function.                            *)

let CF2_J2_CALL_RET_TAC (bl:int) (sk:term) contract_args =
  SUBGOAL_THEN `val(word(LENGTH(src:byte list) - ip):int64) = LENGTH src - ip`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (subst [sk,`sk:armstate`]
    `read (memory :> bytes(word_add inp (word ip),LENGTH(src:byte list) - ip))
          sk = num_of_bytelist(SUB_LIST(ip,LENGTH src - ip) src)`)
  ASSUME_TAC THENL
   [MATCH_MP_TAC SNAPPY_READ_BYTES_SUB THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; CF2_ARITH_TAC]; ALL_TAC] THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
     ~select:(elf_slots_importing ["memcpy"]) THEN
  ARM_BSTEP_TAC CF2_J2_EXEC (bl--bl) THEN
  ARM_BSTEP_PLT_STUB_TAC CF2_J2_EXEC THEN
  CF2_J2_CALL_TAC CF2_J2_EXEC contract_args ("s" ^ string_of_int(bl + 5)) THEN
  ARM_BSTEP_TAC CF2_J2_EXEC ((bl + 6)--(bl + 9)) THEN BSTEP_FINAL_TAC;;

(* The output: the model's final output, the literal lit (the bytes before   *)
(* its data, as `APPEND [tag] B`), from the prefix of k bytes and the data.  *)

let CF2_J2_FIN_TAC (lit:term) (pre:term) (k:term) =
  REWRITE_TAC[snappy_cf2_post] THEN
  MP_TAC(SPECL [`src:byte list`; `ip:num`; `ne:num`; `sk:num`; `c:num`;
                `x:num`; `t1:num->num`; `t2:num->num`; `out:byte list`]
               CF2_J2_FINAL_OUT) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CF2_J2_ASSUME_REWRITE_TAC [`ip < LENGTH(src:byte list)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN (mk_eq(`snappy_emit_literal (SUB_LIST(ip,LENGTH(src:byte list) - ip) src)`,
                      lit)) SUBST1_TAC THENL
   [REWRITE_TAC[snappy_emit_literal; LENGTH_SUB_LIST] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[ARITH_RULE `MIN (a:num) a = a`] THEN
    W(fun (asl,w) -> REWRITE_TAC(mapfilter (fun (_,th) ->
       if can (term_match [] `a < b`) (concl th) ||
          can (term_match [] `~(a < b)`) (concl th) then th else fail()) asl)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_icomb(mk_icomb(`APPEND:byte list->byte list->byte list`,
                                        `out:byte list`),lit),
                      mk_icomb(mk_icomb(`APPEND:byte list->byte list->byte list`,
                                        pre),
                               `SUB_LIST(ip,LENGTH(src:byte list) - ip) src`)))
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_icomb(`LENGTH:byte list->num`,
      mk_icomb(mk_icomb(`APPEND:byte list->byte list->byte list`,pre),
               `SUB_LIST(ip,LENGTH(src:byte list) - ip) src`)),
      mk_binary "+" (k,`LENGTH(src:byte list) - ip`)))
   SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_SUB_LIST; LENGTH_BYTELIST_OF_NUM] THEN
    CF2_J2_ASSUME_REWRITE_TAC [`LENGTH(out:byte list) = l`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(CF2_J2_REG_TAC THEN NO_TAC) THEN
  MATCH_MP_TAC CF2_J2_APPEND THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_SUB_LIST; LENGTH_BYTELIST_OF_NUM] THEN
  CF2_J2_ASSUME_REWRITE_TAC [`LENGTH(out:byte list) = l`] THEN ARITH_TAC;;

let CF2_J2_LONG_TAC (q:int) (cnt:int) (tag:int) contract_args fin =
  let cnt_tm = mk_small_numeral cnt and tag_tm = mk_small_numeral tag in
  let tagb = mk_comb(`word:num->byte`,tag_tm) in
  let k1 = `l + 1` in
  let k = mk_binary "+" (k1,cnt_tm) in
  let blist = list_mk_icomb "bytelist_of_num"
                [cnt_tm; `LENGTH(src:byte list) - ip - 1`] in
  let pre = mk_icomb(mk_icomb(`APPEND:byte list->byte list->byte list`,
              mk_icomb(mk_icomb(`APPEND:byte list->byte list->byte list`,
                                `out:byte list`),
                       mk_list([tagb],`:byte`))),blist) in
  let lit = mk_icomb(mk_icomb(`CONS:byte->byte list->byte list`,tagb),
              mk_icomb(mk_icomb(`APPEND:byte list->byte list->byte list`,blist),
                       `SUB_LIST(ip,LENGTH(src:byte list) - ip) src`)) in
  ARM_BSTEP_TAC CF2_J2_EXEC (7--9) THEN
  CF2_J2_CANON_TAC `X0` (mk_comb(`word:num->int64`,mk_small_numeral q))
     (REWRITE_TAC[CF2_J2_ZX32] THEN SIMP_TAC[CF2_J2_ISHR_SMALL; CF2_J2_CLZ_SMALL] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[CF2_J2_CLZ_DIV8] THEN
      CONV_TAC WORD_REDUCE_CONV) THEN
  CF2_J2_CANON_TAC `memory :> bytes32 (word_add op (word(l + 1)))`
     `word(LENGTH(src:byte list) - ip - 1):int32` (REWRITE_TAC[CF2_J2_ZX32]) THEN
  ARM_BSTEP_TAC CF2_J2_EXEC (10--18) THEN
  CF2_J2_CANON_TAC `X0` (mk_icomb(mk_icomb(`word_add:int64->int64->int64`,`op:int64`),
                              mk_comb(`word:num->int64`,k))) CF2_J2_OFS_EQ_TAC THEN
  CF2_J2_CANON_TAC `X2` `word(LENGTH(src:byte list) - ip):int64` CF2_J2_SX_TAC THEN
  CF2_J2_CANON_TAC `X19` `word(LENGTH(src:byte list) - ip):int64` CF2_J2_SX_TAC THEN
  CF2_J2_CANON_TAC `memory :> bytes8 (word_add op (word l))` tagb
    (CONV_TAC WORD_REDUCE_CONV) THEN
  SUBGOAL_THEN (subst [tagb,`b:byte`]
    `read (memory :> bytes(op,l + 1)) s18 = num_of_bytelist(APPEND out [b])`)
  ASSUME_TAC THENL [MATCH_MP_TAC CF2_J2_APPEND_BYTE THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(list_mk_comb(`read:(armstate,num)component->armstate->num`,
      [mk_icomb(mk_icomb(`(:>):(armstate,int64->byte)component->(int64->byte,num)component->(armstate,num)component`,
                `memory:(armstate,int64->byte)component`),
                mk_comb(`bytes:int64#num->(int64->byte,num)component`,
                        mk_pair(`word_add op (word(l + 1)):int64`,cnt_tm)));
       `s18:armstate`]),
      mk_icomb(`num_of_bytelist`,blist)))
  ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[NUM_OF_BYTELIST_OF_NUM_EQ]
      `n < 256 EXP k /\ x = n ==> x = num_of_bytelist(bytelist_of_num k n)`) THEN
    CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CF2_J2_BYTES_OF_32 THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; CONV_TAC NUM_REDUCE_CONV THEN
      CF2_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(list_mk_comb(`read:(armstate,num)component->armstate->num`,
      [mk_icomb(mk_icomb(`(:>):(armstate,int64->byte)component->(int64->byte,num)component->(armstate,num)component`,
                `memory:(armstate,int64->byte)component`),
                mk_comb(`bytes:int64#num->(int64->byte,num)component`,
                        mk_pair(`op:int64`,k)));
       `s18:armstate`]),
      mk_icomb(`num_of_bytelist`,pre)))
  ASSUME_TAC THENL
   [MATCH_MP_TAC CF2_J2_APPEND THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_BYTELIST_OF_NUM] THEN
    CF2_J2_ASSUME_REWRITE_TAC [`LENGTH(out:byte list) = l`] THEN ARITH_TAC;
    ALL_TAC] THEN
  CF2_J2_CALL_RET_TAC 19 `s18:armstate` contract_args THEN
  fin lit pre k;;

let CF2_J2_SHORT_TAC contract_args fin =
  let tag = `word(4 * (LENGTH(src:byte list) - ip - 1)):byte` in
  let pre = mk_icomb(mk_icomb(`APPEND:byte list->byte list->byte list`,
                              `out:byte list`),mk_list([tag],`:byte`)) in
  let lit = mk_icomb(mk_icomb(`CONS:byte->byte list->byte list`,tag),
                     `SUB_LIST(ip,LENGTH(src:byte list) - ip) src`) in
  ARM_BSTEP_TAC CF2_J2_EXEC (7--13) THEN
  CF2_J2_CANON_TAC `X0` `word_add op (word(l + 1)):int64` CF2_J2_OFS_EQ_TAC THEN
  CF2_J2_CANON_TAC `X2` `word(LENGTH(src:byte list) - ip):int64` CF2_J2_SX_TAC THEN
  CF2_J2_CANON_TAC `X19` `word(LENGTH(src:byte list) - ip):int64` CF2_J2_SX_TAC THEN
  CF2_J2_CANON_TAC `memory :> bytes8 (word_add op (word l))` tag CF2_J2_WORD_EQ_TAC THEN
  SUBGOAL_THEN (subst [tag,`b:byte`]
    `read (memory :> bytes(op,l + 1)) s13 = num_of_bytelist(APPEND out [b])`)
  ASSUME_TAC THENL [MATCH_MP_TAC CF2_J2_APPEND_BYTE THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CF2_J2_CALL_RET_TAC 14 `s13:armstate` contract_args THEN
  fin lit pre `l + 1`;;

let CF2_J2_NOLIT_POST_TAC =
  REWRITE_TAC[snappy_cf2_post] THEN
  MP_TAC(SPECL [`src:byte list`; `ip:num`; `ne:num`; `sk:num`; `c:num`;
                `x:num`; `t1:num->num`; `t2:num->num`; `out:byte list`]
               CF2_J2_FINAL_OUT) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CF2_J2_ASSUME_REWRITE_TAC [`~(ip < LENGTH(src:byte list))`] THEN
  DISCH_THEN SUBST1_TAC THEN
  CF2_J2_ASSUME_REWRITE_TAC [`LENGTH(out:byte list) = l`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN CF2_J2_REG_TAC;;

let CF2_J2_NOLIT_TAC post =
  ARM_BSTEP_TAC CF2_J2_EXEC (3--5) THEN BSTEP_FINAL_TAC THEN post;;

let CF2_J2_TAC contract_args fin nolit_post =
  CF2_PIECE_START_TAC THEN CF2_J2_LABEL_MEMCPY_TAC THEN CF2_INIT_TAC THEN
  MP_TAC(SPECL [`LENGTH(src:byte list)`; `ip:num`; `LENGTH(out:byte list)`]
               CF2_J2_OUT_BOUND) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  ABBREV_TAC `l = LENGTH(out:byte list)` THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(fun th' ->
    if concl th' = concl th then th' else PURE_REWRITE_RULE[th] th')) THEN
  ARM_BSTEP_TAC CF2_J2_EXEC (1--2) THEN
  CF2_BRANCH_TAC `ip < LENGTH(src:byte list)` THENL
   [ARM_BSTEP_TAC CF2_J2_EXEC (3--3) THEN
    CF2_J2_CANON_TAC `X13` `word(LENGTH(src:byte list) - ip):int64`
      (MATCH_MP_TAC CF2_J2_SUB_OFFSETS THEN CF2_ARITH_TAC) THEN
    ARM_BSTEP_TAC CF2_J2_EXEC (4--4) THEN
    CF2_J2_CANON_TAC `X3` `word(LENGTH(src:byte list) - ip - 1):int64`
      (MP_TAC(SPEC `LENGTH(src:byte list) - ip` CF2_J2_ZX_SUB1) THEN
       ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN CF2_ARITH_TAC;
                       DISCH_THEN ACCEPT_TAC]) THEN
    ARM_BSTEP_TAC CF2_J2_EXEC (5--6) THEN
    CF2_J2_LE_BRANCH_TAC `LENGTH(src:byte list) - ip - 1` THENL
     [CF2_J2_SHORT_TAC contract_args fin;
      SUBGOAL_THEN `0 < LENGTH(src:byte list) - ip - 1 /\
                    LENGTH src - ip - 1 < 65536` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN CF2_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `LENGTH(src:byte list) - ip - 1 < 256` THENL
       [CF2_J2_LONG_TAC 3 1 240 contract_args fin;
        CF2_J2_LONG_TAC 2 2 244 contract_args fin]];
    CF2_J2_NOLIT_TAC nolit_post];;

let CF2_J2_CORRECT_ARGS =
  [`read X0 s`; `read X1 s`; `read X2 s`;
   `num_of_bytelist(SUB_LIST(ip,LENGTH(src:byte list) - ip) src)`;
   `read X30 s`];;

let SNAPPY_CF2_GCC12_O2_JOIN2 = prove
 (SNAPPY_CF2_GCC12_O2_JOIN2_STMT,
  CF2_J2_TAC CF2_J2_CORRECT_ARGS CF2_J2_FIN_TAC CF2_J2_NOLIT_POST_TAC);;


(* ------------------------------------------------------------------------- *)
(* Memory safety: the events of memcpy are in the regions of the piece; the  *)
(* other events are concrete.                                                *)
(* ------------------------------------------------------------------------- *)

let CF2_J2_CONT_TAC =
  FIRST [REWRITE_TAC[contained; CONTAINED_MODULO_REFL; LE_REFL] THEN NO_TAC;
         MATCH_MP_TAC CF2_J2_CONTAINED_OFFSET THEN CF2_ARITH_TAC];;

let rec CF2_J2_DISJ_TAC g =
  (FIRST [CF2_J2_CONT_TAC;
          DISJ1_TAC THEN CF2_J2_CONT_TAC;
          DISJ2_TAC THEN CF2_J2_DISJ_TAC]) g;;

let CF2_J2_EVENTS_TAC : tactic = fun (asl,w) ->
  let w' = rhs(concl(REWRITE_CONV[snappy_cf2_events] w)) in
  let _,bod = dest_exists w' in
  let inb = rand bod in
  let rr' = rand(rator inb) and wr' = rand inb in
  let is_callee th = match concl th with
      Comb(Comb(Comb(Const("memaccess_inbounds",_),Var(v,_)),_),_) ->
        String.length v > 5 && String.sub v 0 5 = "bstep"
    | _ -> false in
  let absorb =
    match filter (is_callee o snd) asl with
      [] -> ALL_TAC
    | (_,th)::_ ->
        let ev = rand(rator(rator(concl th))) and rr = rand(rator(concl th))
        and wr = rand(concl th) in
        MP_TAC(ISPECL [ev; rr; rr'; wr; wr'] MEMACCESS_INBOUNDS_CONTAINED) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[ALL; EX] THEN REPEAT CONJ_TAC THEN CF2_J2_DISJ_TAC;
          DISCH_THEN(fun imp -> ASSUME_TAC(MP imp th))] in
  (REWRITE_TAC[snappy_cf2_events] THEN absorb THEN MEMSAFE_EVENTS_TAC) (asl,w);;

let CF2_J2_SAFE_FIN_TAC lit pre k =
  REWRITE_TAC[snappy_cf2_post_safe] THEN CONJ_TAC THENL
   [CF2_J2_FIN_TAC lit pre k; CF2_J2_EVENTS_TAC];;

let CF2_J2_SAFE_ARGS =
  [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`;
   `num_of_bytelist(SUB_LIST(ip,LENGTH(src:byte list) - ip) src)`;
   `read X30 s`];;

let SNAPPY_CF2_GCC12_O2_JOIN2_SAFE = prove
 (SNAPPY_CF2_GCC12_O2_JOIN2_SAFE_STMT,
  CF2_J2_TAC CF2_J2_SAFE_ARGS CF2_J2_SAFE_FIN_TAC
   (REWRITE_TAC[snappy_cf2_post_safe] THEN CONJ_TAC THENL
     [CF2_J2_NOLIT_POST_TAC; CF2_J2_EVENTS_TAC]));;
