(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The piece from loop2: a probe of the search at ip (phase 2), whose bound  *)
(* ip + skip / 512 <= ip_limit is known. The entry of table2 for            *)
(* Load64(ip) is the candidate c2 and becomes ip; if Load32 at c2 matches,   *)
(* FindMatchLengthPlain (FML A) and join4 (phase 7). Otherwise the entry of  *)
(* table for Load32(ip) is c1 and becomes ip; if Load32 at c1 matches,       *)
(* FML B for c1 and FML C for the candidate c3 of table2 at ip + 1, and      *)
(* join4 with the longer match (c3 at ip + 1, whose entry then becomes ip,   *)
(* if it is longer). Otherwise the next probe: loop2 if its bound holds,     *)
(* else join2 (emit_remainder from next_emit, two steps of the model).       *)
(*                                                                           *)
(*   +0x68  ldrh w14, [x4]   (c2)        +0xa0  ldrh w7, [x3, w4, uxtw] (c1) *)
(*   +0x7c  strh w15, [x4]   (ip)        +0xa4  strh w15, [x3, w4, uxtw]     *)
(*   +0x88  ldr  w7, [x0, x14]           +0xac  ldr  w4, [x0, x7]            *)
(*   +0x98  cmp  w16, w7; b.eq FML A     +0xb0  cmp  w16, w4; b.eq +0x238    *)
(*   +0xb8 .. +0xcc  the next probe      +0xd0  cmp x10, x6; b.cs loop2      *)
(*   +0x238 .. FML B, +0x2b4 .. Load64(ip + 1), its entry c3 of table2,      *)
(*   FML C, +0x32c cmp x7, w4, uxtw; b.ls join21 (c1) or c3 (+0x334)         *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_loop2_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Lemmas and tactics.                                                       *)
(* ------------------------------------------------------------------------- *)

let CF2_L2_TB_TAC (t:term) (e:term) =
  FIRST_ASSUM(fun th -> match concl th with
      Comb(Comb(Const("snappy_tbound",_),t'),_) when t' = t ->
        ASSUME_TAC(SPEC e (MATCH_MP SNAPPY_TBOUND_LOOKUP th))
    | _ -> failwith "CF2_L2_TB_TAC");;

let CF2_L2_ZX16 = prove
 (`!v. v < 65536 ==> word_zx (word v:int16):int64 = word v`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `v < 65536 ==> v < 18446744073709551616`]);;

let CF2_L2_ZX16_TAC (v:term) : tactic = fun (asl,w) ->
  let lt = mk_binary "<" (v,`65536`) in
  let lth = TAC_PROOF((asl,lt),CF2_ARITH_TAC) in
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP CF2_L2_ZX16 lth]) (asl,w);;

(* e < ts for a hash entry e, as an assumption.                         *)
let CF2_L2_HASH_LT_TAC (e:term) : tactic = fun (asl,w) ->
  let lt = mk_binary "<" (e,`ts:num`) in
  let th = TAC_PROOF((asl,lt),
    ASM_SIMP_TAC[SNAPPY_HASH4_LT; SNAPPY_HASH8_LT;
                 ARITH_RULE `128 <= ts ==> ~(ts = 0)`]) in
  ASSUME_TAC th (asl,w);;

let CF2_L2_MOD32 = CONV_RULE NUM_REDUCE_CONV SNAPPY_LOAD64_MOD32;;

(* CF2_WORD_EQ_TAC with the arithmetic on the numerical assumptions only.  *)
let CF2_L2_WORD_EQ_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  FIRST
   [REFL_TAC;
    AP_TERM_TAC THEN AP_TERM_TAC THEN CF2_ARITH_TAC;
    REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC CF2_VAL_RULES THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CF2_MOD_ELIM_TAC THEN
    CF2_ARITH_TAC];;

let CF2_L2_CONTAINED_REFL = prove
 (`!x:int64 n. contained (x,n) (x,n)`,
  REWRITE_TAC[contained; contained_modulo] THEN MESON_TAC[CONG_REFL]);;

let CF2_L2_INB_LIFT = prove
 (`!e (x:int64) n r1 w.
     memaccess_inbounds e [x,n] [] ==> memaccess_inbounds e (CONS (x,n) r1) w`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MEMACCESS_INBOUNDS_CONTAINED THEN
  REWRITE_TAC[ALL; EX; CF2_L2_CONTAINED_REFL]);;

(* Lift memaccess_inbounds x [inp,LENGTH src] [] to the regions of the piece. *)
let CF2_L2_INB_LIFT_TAC =
  let r1 = `[op,snappy_max_compressed_length (LENGTH (src:byte list)) - 5;
             table:int64,2 * ts; table2:int64,2 * ts;
             word_sub stackpointer (word 48),48;
             word pc,libsnappy_rw + libsnappy_rw_size; ea:int64,el:num]`
  and w = `[op:int64,snappy_max_compressed_length (LENGTH (src:byte list)) - 5;
            table:int64,2 * ts; table2:int64,2 * ts;
            word_sub stackpointer (word 48),48]` in
  RULE_ASSUM_TAC(fun th ->
    match concl th with
      Comb(Comb(Comb(Const("memaccess_inbounds",_),ev),
           Comb(Comb(Const("CONS",_),Comb(Comb(Const(",",_),x),_)),
                Const("NIL",_))),Const("NIL",_)) when x = `inp:int64` ->
        CONV_RULE NUM_REDUCE_CONV
         (MATCH_MP (ISPECL [ev; `inp:int64`; `LENGTH(src:byte list)`; r1; w]
                     CF2_L2_INB_LIFT) th)
    | _ -> th);;

(* Go through a contract th (an assume_spec theorem hyps ==> ensures ...),  *)
(* with its events variable e set to the current events and insts.          *)
let CF2_L2_CALL_TAC (th:thm) (args:term list) sname : tactic =
  fun (asl,w) ->
  let s = rand w in
  let evth = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("events",_)),s')),_)
        -> s' = s | _ -> false) asl) in
  let ev = rhs(concl evth) in
  let th1 = SPECL (args @ [ev]) th in
  let hyp_tm = lhand(concl th1) in
  let hth = TAC_PROOF((asl,hyp_tm),
     REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE CF2_ARITH_TAC)) in
  (ARM_BSTEP_CALL_TAC SNAPPY_CF2_GCC12_O2_EXEC (MP th1 hth) sname THEN
   CF2_L2_INB_LIFT_TAC) (asl,w);;

let CF2_L2_DIVPOS = prove
 (`!sk. 512 <= sk ==> 1 <= sk DIV 512`,
  SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC);;

let CF2_L2_MLEN_TAC (a:term) (b:term) =
  ASSUME_TAC(SPECL [`src:byte list`; a; b] SNAPPY_MATCH_LENGTH);;

(* Join the parts of a table into the whole fact at the current state.     *)
let CF2_L2_JOIN_TAC (tab:term) (t:term) (e:term) (v:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let tm = subst [tab,`tab:int64`; t,`t:num->num`; e,`e:num`; v,`v:num`; s,`s:armstate`]
    `read (memory :> bytes(tab:int64,2 * ts)) (s:armstate) =
     snappy_tval ts (snappy_tupd (t:num->num) e v)` in
  (SUBGOAL_THEN tm ASSUME_TAC THENL [CF2_TABLE_JOIN_TAC; ALL_TAC]) (asl,w);;

(* The 32-bit hash of the data as the code computes it, in the facts.       *)
let CF2_L2_HASH4_TAC (d:term) : tactic = fun (asl,w) ->
  let th0 = SPECL [`ts:num`; d] SNAPPY_HASH4_WORD in
  let hth = TAC_PROOF((asl,lhand(concl th0)),
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[SNAPPY_LOAD64_BOUND]) in
  RULE_ASSUM_TAC(REWRITE_RULE[MP th0 hth; SNAPPY_LOAD64_MOD32]) (asl,w);;

(* bstep rewrites branch conditions with the static assumptions: orient     *)
(* ts = snappy_table_size .. DIV 2 the other way, so that ts stays.          *)
let CF2_L2_TS_FLIP_TAC =
  FIRST_X_ASSUM(fun th -> match concl th with
      Comb(Comb(Const("=",_),Var("ts",_)),_) -> ASSUME_TAC(SYM th)
    | _ -> failwith "CF2_L2_TS_FLIP_TAC");;

let CF2_L2_ZXZX = prove
 (`!n. n < 4294967296 ==> word_zx (word_zx (word n:int64):int32):int64 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `n < 4294967296` THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `n < 4294967296 ==> n < 18446744073709551616`]);;

(* The instance for 2 * h, h a hash entry (h < ts as an assumption).       *)
let CF2_L2_ZXZX_RULE (asl:(string*thm) list) (h:term) =
  let n = mk_comb(mk_comb(`( * ):num->num->num`,`2`),h) in
  let lt = mk_comb(mk_comb(`(<):num->num->bool`,n),`4294967296`) in
  MP (SPEC n CF2_L2_ZXZX) (TAC_PROOF((asl,lt),CF2_ARITH_TAC));;

let CF2_L2_AND16 = BITBLAST_RULE
 `word_zx (word_and (y:int32) (word 65535)):int16 = word_zx y`;;

let CF2_L2_ENTRY = prove
 (`!x:int64 v. v < 65536
      ==> word_zx (word_and (word_zx (word_sub (word_add x (word v)) x):int32)
                            (word 65535)):int16 = word v`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CF2_L2_AND16; WORD_RULE `word_sub (word_add x y) x:int64 = y`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16;
              DIMINDEX_32; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* The stored entry ip (or ip + 1): its word form in the facts.            *)
let CF2_L2_ENTRY_TAC (v:term) : tactic = fun (asl,w) ->
  let lt = mk_comb(mk_comb(`(<):num->num->bool`,v),`65536`) in
  let lth = TAC_PROOF((asl,lt),CF2_ARITH_TAC) in
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP (SPEC `inp:int64` CF2_L2_ENTRY) lth]) (asl,w);;

(* The target, with the remaining conjuncts of the state at the point left  *)
(* as goals (to be closed by the caller).                                    *)
let CF2_L2_TARGET_TAC (pt:term) (st:term) (mids:term list) =
  MAP_EVERY EXISTS_TAC [pt; st] THEN
  REPEAT CONJ_TAC THENL
   [CF2_REACH_TAC mids;
    REWRITE_TAC[snappy_cf2_pot] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CF2_ARITH_TAC;
    REWRITE_TAC[snappy_cf2_point] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[snappy_cf2_at; snappy_cf2_regs; snappy_phase; snappy_ip;
                snappy_ne; snappy_skip; snappy_cand; snappy_aux; snappy_t1;
                snappy_t2; snappy_out] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC];;

let CF2_L2_OUT_BOUND = prove
 (`!n ne. n <= 65536 /\ ne <= n
          ==> ne + ne DIV 30 + 20 <= snappy_max_compressed_length n - 5`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n < 2 EXP 32` (fun th -> SIMP_TAC[SNAPPY_MAX_COMPRESSED_LENGTH_32; th])
  THENL [UNDISCH_TAC `n <= 65536` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ne DIV 30 <= n DIV 6` MP_TAC THENL
   [TRANS_TAC LE_TRANS `ne DIV 6` THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC;
      MATCH_MP_TAC DIV_MONO THEN ASM_REWRITE_TAC[]];
    ASM_ARITH_TAC]);;

(* LENGTH out + 20 is within the output region (out from next_emit ne).     *)
let CF2_L2_OUT_TAC : tactic = fun (asl,w) ->
  let th = SPECL [`LENGTH(src:byte list)`; `ne:num`] CF2_L2_OUT_BOUND in
  let hth = TAC_PROOF((asl,lhand(concl th)), CONJ_TAC THEN CF2_ARITH_TAC) in
  ASSUME_TAC (MP th hth) (asl,w);;

(* Replace the value of a register (or other component) fact by an equal     *)
(* word new, proved by CF2_WORD_EQ_TAC.                                     *)
let CF2_L2_REG_EQ_TAC (c:term) (nw:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let th = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s')),_)
        -> s' = s && c' = c | _ -> false) asl) in
  let old = rhs(concl th) in
  let eth = TAC_PROOF((asl,mk_eq(old,nw)),CF2_L2_WORD_EQ_TAC) in
  (FIRST_X_ASSUM(fun th' -> if concl th' = concl th then
     ASSUME_TAC(TRANS th' eth) else failwith "")) (asl,w);;

let CF2_L2_CLOSE_TAC =
  FIRST [REWRITE_TAC[snappy_cf2_events] THEN MEMSAFE_EVENTS_TAC THEN NO_TAC;
         CF2_ARITH_TAC; CF2_L2_WORD_EQ_TAC THEN NO_TAC;
         CF2_TABLE_JOIN_TAC THEN NO_TAC];;

(* CF2_BRANCH_TAC with the case used as cond = T (not as a rewrite of its    *)
(* left side, which may occur inside its right side).                        *)
let CF2_L2_BRANCH_TAC ?(extra=[]) (cond:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let is_pc th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),r)
        -> s' = s && is_cond r
    | _ -> false in
  let pcth = snd(find (is_pc o snd) asl) in
  let b,_ = dest_cond(rhs(concl pcth)) in
  let eqth = TAC_PROOF((asl,mk_iff(b,cond)),CF2_COND_EQ_TAC extra) in
  (ASM_CASES_TAC cond THEN
   FIRST_X_ASSUM(fun cth ->
     let cth' = if is_neg(concl cth) then EQF_INTRO cth
                else EQT_INTRO cth in
     FIRST_X_ASSUM(fun th -> if concl th = concl pcth then
        ASSUME_TAC(REWRITE_RULE[eqth; cth'] th) else failwith "") THEN
     ASSUME_TAC cth)) (asl,w);;


let CF2_L2_HASH8_32 = prove
 (`!ts d. snappy_pow2 ts /\ ts <= 16384 /\ d < 2 EXP 64
          ==> word_zx (word_and (word_zx (word (2 * (ts - 1)):int64):int32)
                (word_zx (word_ushr (word (0 + val (word d:int64) *
                                         58295818150454627)) 49:int64):int32))
              :int64 =
              word(2 * snappy_hash8 ts d)`,
  REWRITE_TAC[snappy_pow2] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `word_zx (word (2 * (2 EXP k - 1)):int64):int32 =
                word (2 * (2 EXP k - 1))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SNAPPY_TABLE_MASK; snappy_hash8] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_USHR;
              DIMINDEX_32; DIMINDEX_64; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `!y. (y MOD 18446744073709551616) DIV 562949953421312 <
                    4294967296`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT (SPEC_ALL th)]) THENL
   [GEN_TAC THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    MP_TAC(SPECL [`y:num`; `18446744073709551616`] MOD_LT_EQ) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `!y. 2 * y MOD 2 EXP k < 4294967296`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT (SPEC_ALL th)]) THENL
   [GEN_TAC THEN MATCH_MP_TAC(ARITH_RULE
     `x < 2 EXP k /\ 2 EXP k <= 16384 ==> 2 * x < 4294967296`) THEN
    ASM_REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    REWRITE_TAC[MULT_SYM]]);;

(* tbound for an updated table: snappy_tbound (tupd t e v) b.             *)
let CF2_L2_TBUPD_TAC (t:term) (e:term) (v:term) (b:term) : tactic = fun (asl,w) ->
  let tm = list_mk_comb(`snappy_tbound`,
             [list_mk_comb(`snappy_tupd`,[t;e;v]); b]) in
  let th = TAC_PROOF((asl,tm),
    MATCH_MP_TAC SNAPPY_TBOUND_TUPD_MONO THEN
    FIRST_ASSUM(fun bth -> match concl bth with
        Comb(Comb(Const("snappy_tbound",_),t'),b0) when t' = t ->
          EXISTS_TAC b0 THEN REPEAT CONJ_TAC THENL
           [ACCEPT_TAC bth; CF2_ARITH_TAC; CF2_ARITH_TAC]
      | _ -> failwith "")) in
  ASSUME_TAC th (asl,w);;

let CF2_L2_HASH8_32_TAC (d:term) : tactic = fun (asl,w) ->
  let th0 = SPECL [`ts:num`; d] CF2_L2_HASH8_32 in
  let hth = TAC_PROOF((asl,lhand(concl th0)),
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[SNAPPY_LOAD64_BOUND]) in
  RULE_ASSUM_TAC(REWRITE_RULE[MP th0 hth]) (asl,w);;

let CF2_L2_HASH8_TAC (d:term) : tactic = fun (asl,w) ->
  let th0 = SPECL [`ts:num`; d] SNAPPY_HASH8_WORD in
  let hth = TAC_PROOF((asl,lhand(concl th0)),
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[SNAPPY_LOAD64_BOUND]) in
  RULE_ASSUM_TAC(REWRITE_RULE[MP th0 hth]) (asl,w);;

let CF2_L2_CLOSE2_TAC =
  FIRST [REWRITE_TAC[snappy_cf2_events] THEN MEMSAFE_EVENTS_TAC THEN NO_TAC;
         CF2_ARITH_TAC;
         CF2_L2_WORD_EQ_TAC THEN NO_TAC;
         W(fun (asl,w) -> ASM_SIMP_TAC[SNAPPY_HASH8_WORD; SNAPPY_LOAD64_BOUND])
           THEN NO_TAC];;

let CF2_L2_CLOSE3_TAC = CF2_L2_CLOSE_TAC ORELSE CF2_L2_CLOSE2_TAC;;

(* ------------------------------------------------------------------------- *)
(* The proof.                                                                *)
(* ------------------------------------------------------------------------- *)

let CF2_L2_EXEC = SNAPPY_CF2_GCC12_O2_EXEC;;

(* The entries and candidates: e2/c2 of table2 at ip, e1/c1 of table at ip,  *)
(* e2b/c3 of table2 (after the update at e2) at ip + 1, the match lengths    *)
(* len1 and len3, and the updated tables.                                    *)

let CF2_L2_E2 = `snappy_hash8 ts (snappy_load64 src ip)`;;
let CF2_L2_C2 = `(t2:num->num) (snappy_hash8 ts (snappy_load64 src ip))`;;
let CF2_L2_E1 = `snappy_hash4 ts (snappy_load32 src ip)`;;
let CF2_L2_C1 = `(t1:num->num) (snappy_hash4 ts (snappy_load32 src ip))`;;
let CF2_L2_E2B = `snappy_hash8 ts (snappy_load64 src (ip + 1))`;;
let CF2_L2_T1P = `snappy_tupd t1 (snappy_hash4 ts (snappy_load32 src ip)) ip`;;
let CF2_L2_T2P = `snappy_tupd t2 (snappy_hash8 ts (snappy_load64 src ip)) ip`;;
let CF2_L2_C3 = mk_comb(CF2_L2_T2P,CF2_L2_E2B);;
let CF2_L2_LEN1 =
  `snappy_match_length src
     ((t1:num->num) (snappy_hash4 ts (snappy_load32 src ip)) + 4) (ip + 4) + 4`;;
let CF2_L2_LEN3 =
  list_mk_icomb "snappy_match_length" [`src:byte list`; CF2_L2_C3; `ip + 1`];;

(* A match with table2: FML A, the entry e2 of table2 put together again,    *)
(* and join4 with phase 7.                                                   *)

let CF2_L2_MATCH2_TAC =
  CF2_L2_CALL_TAC SNAPPY_CF2_GCC12_O2_FML_A
   [`src:byte list`; `inp:int64`; `ip:num`; CF2_L2_C2; `pc:num`] "s15" THEN
  ARM_BSTEP_TAC CF2_L2_EXEC (16--16) THEN
  CF2_L2_ENTRY_TAC `ip:num` THEN
  CF2_L2_JOIN_TAC `table2:int64` `t2:num->num` CF2_L2_E2 `ip:num` THEN
  CF2_L2_MLEN_TAC (mk_binary "+" (CF2_L2_C2,`4`)) `ip + 4` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CF2_L2_DIVPOS) THEN
  BSTEP_FINAL_TAC THEN
  CF2_L2_TARGET_TAC `CompressFragmentDoubleHash_join4:num`
   (list_mk_icomb "SnappyCState"
     [`7`; `ip:num`; `ne:num`; `sk + 1`; CF2_L2_C2;
      list_mk_icomb "snappy_match_length"
       [`src:byte list`; mk_binary "+" (CF2_L2_C2,`4`); `ip + 4`] |>
      (fun t -> mk_binary "+" (t,`4`));
      `t1:num->num`; CF2_L2_T2P; `out:byte list`]) [] THEN
  CF2_L2_CLOSE3_TAC;;

(* A match with table: FML B for c1, the candidate c3 of table2 at ip + 1,   *)
(* FML C for it, and join4 with the longer match.                            *)

let CF2_L2_MATCH1_TAC =
  ARM_BSTEP_TAC CF2_L2_EXEC (21--23) THEN
  CF2_L2_REG_EQ_TAC `X6` `word_add inp (word(ip + 4)):int64` THEN
  CF2_L2_REG_EQ_TAC `X16`
   `word_add inp (word(LENGTH(src:byte list) - 8)):int64` THEN
  CF2_L2_CALL_TAC SNAPPY_CF2_GCC12_O2_FML_B
   [`src:byte list`; `inp:int64`; `ip:num`; CF2_L2_C1; `pc:num`] "s25" THEN
  CF2_INPUT_TAC SNAPPY_READ_LOAD64 `ip + 1` THEN
  ARM_BSTEP_TAC CF2_L2_EXEC (26--36) THEN
  CF2_L2_ENTRY_TAC `ip:num` THEN
  CF2_L2_JOIN_TAC `table2:int64` `t2:num->num` CF2_L2_E2 `ip:num` THEN
  CF2_L2_TBUPD_TAC `t2:num->num` CF2_L2_E2 `ip:num` `ip:num` THEN
  CF2_L2_HASH_LT_TAC CF2_L2_E2B THEN
  CF2_TABLE_SPLIT_TAC `table2:int64` CF2_L2_E2B THEN
  CF2_L2_HASH8_32_TAC `snappy_load64 src (ip + 1)` THEN
  W(fun (asl,w) ->
    ARM_BSTEP_TAC ~rewrites:[CF2_L2_ZXZX_RULE asl CF2_L2_E2B]
      CF2_L2_EXEC (37--37)) THEN
  CF2_L2_TB_TAC CF2_L2_T2P CF2_L2_E2B THEN
  CF2_L2_ZX16_TAC CF2_L2_C3 THEN
  ARM_BSTEP_TAC CF2_L2_EXEC (38--38) THEN
  CF2_L2_REG_EQ_TAC `X20` `word_add inp (word(ip + 1)):int64` THEN
  CF2_L2_REG_EQ_TAC `X6` `word_add inp (word(ip + 1)):int64` THEN
  CF2_L2_CALL_TAC SNAPPY_CF2_GCC12_O2_FML_C
   [`src:byte list`; `inp:int64`; `ip:num`; CF2_L2_C3; `pc:num`] "s39" THEN
  CF2_L2_MLEN_TAC (mk_binary "+" (CF2_L2_C1,`4`)) `ip + 4` THEN
  CF2_L2_MLEN_TAC CF2_L2_C3 `ip + 1` THEN
  ARM_BSTEP_TAC CF2_L2_EXEC (40--41) THEN
  CF2_L2_BRANCH_TAC (mk_binary "<=" (CF2_L2_LEN3,CF2_L2_LEN1)) THENL
   [CF2_L2_ENTRY_TAC `ip:num` THEN
    CF2_L2_JOIN_TAC `table:int64` `t1:num->num` CF2_L2_E1 `ip:num` THEN
    ARM_BSTEP_TAC CF2_L2_EXEC (42--43) THEN
    CF2_L2_REG_EQ_TAC `X4` (mk_comb(`word:num->int64`,CF2_L2_LEN1)) THEN
    BSTEP_FINAL_TAC THEN
    CF2_L2_TARGET_TAC `CompressFragmentDoubleHash_join4:num`
     (list_mk_icomb "SnappyCState"
       [`7`; `ip:num`; `ne:num`; `sk + 1`; CF2_L2_C1; CF2_L2_LEN1;
        CF2_L2_T1P; CF2_L2_T2P; `out:byte list`]) [] THEN
    CF2_L2_CLOSE3_TAC;
    ARM_BSTEP_TAC CF2_L2_EXEC (42--44) THEN
    CF2_L2_ENTRY_TAC `ip:num` THEN
    W(fun (asl,w) ->
      ARM_BSTEP_TAC ~rewrites:[CF2_L2_ZXZX_RULE asl CF2_L2_E2B]
        CF2_L2_EXEC (45--45)) THEN
    CF2_L2_ENTRY_TAC `ip:num` THEN
    CF2_L2_JOIN_TAC `table2:int64` CF2_L2_T2P CF2_L2_E2B `ip:num` THEN
    CF2_L2_JOIN_TAC `table:int64` `t1:num->num` CF2_L2_E1 `ip:num` THEN
    ARM_BSTEP_TAC CF2_L2_EXEC (46--47) THEN
    CF2_L2_REG_EQ_TAC `X4` (mk_comb(`word:num->int64`,CF2_L2_LEN3)) THEN
    BSTEP_FINAL_TAC THEN
    CF2_L2_TARGET_TAC `CompressFragmentDoubleHash_join4:num`
     (list_mk_icomb "SnappyCState"
       [`7`; `ip + 1`; `ne:num`; `sk + 1`; CF2_L2_C3; CF2_L2_LEN3; CF2_L2_T1P;
        list_mk_icomb "snappy_tupd" [CF2_L2_T2P; CF2_L2_E2B; `ip:num`];
        `out:byte list`]) [] THEN
    CF2_L2_CLOSE3_TAC];;

(* No match: the next probe at ip + skip / 512, loop2 if its bound holds,    *)
(* else join2 with ip = next_emit.                                           *)

let CF2_L2_NOMATCH_TAC =
  CF2_INPUT_TAC SNAPPY_READ_LOAD64 `ip + sk DIV 512` THEN
  ARM_BSTEP_TAC CF2_L2_EXEC (21--28) THEN
  CF2_L2_BRANCH_TAC
   `ip + sk DIV 512 + (sk + 1) DIV 512 <= LENGTH(src:byte list) - 15` THENL
   [CF2_L2_ENTRY_TAC `ip:num` THEN
    CF2_L2_JOIN_TAC `table2:int64` `t2:num->num` CF2_L2_E2 `ip:num` THEN
    CF2_L2_JOIN_TAC `table:int64` `t1:num->num` CF2_L2_E1 `ip:num` THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CF2_L2_DIVPOS) THEN
    BSTEP_FINAL_TAC THEN
    CF2_L2_TARGET_TAC `CompressFragmentDoubleHash_loop2:num`
     `SnappyCState 2 (ip + sk DIV 512) ne (sk + 1) c x
        (snappy_tupd t1 (snappy_hash4 ts (snappy_load32 src ip)) ip)
        (snappy_tupd t2 (snappy_hash8 ts (snappy_load64 src ip)) ip) out` [] THEN
    CF2_L2_CLOSE3_TAC;
    ARM_BSTEP_TAC CF2_L2_EXEC (29--29) THEN
    CF2_L2_ENTRY_TAC `ip:num` THEN
    CF2_L2_JOIN_TAC `table2:int64` `t2:num->num` CF2_L2_E2 `ip:num` THEN
    CF2_L2_JOIN_TAC `table:int64` `t1:num->num` CF2_L2_E1 `ip:num` THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CF2_L2_DIVPOS) THEN
    BSTEP_FINAL_TAC THEN
    CF2_L2_TARGET_TAC `CompressFragmentDoubleHash_join2:num`
     `SnappyCState 5 ne ne (sk + 2) c x
        (snappy_tupd t1 (snappy_hash4 ts (snappy_load32 src ip)) ip)
        (snappy_tupd t2 (snappy_hash8 ts (snappy_load64 src ip)) ip) out`
     [`SnappyCState 2 (ip + sk DIV 512) ne (sk + 1) c x
        (snappy_tupd t1 (snappy_hash4 ts (snappy_load32 src ip)) ip)
        (snappy_tupd t2 (snappy_hash8 ts (snappy_load64 src ip)) ip) out`] THEN
    CF2_L2_CLOSE3_TAC];;

let SNAPPY_CF2_GCC12_O2_LOOP2 = prove
 (SNAPPY_CF2_GCC12_O2_LOOP2_STMT,
  CF2_PIECE_START_TAC THEN CF2_INIT_TAC THEN CF2_L2_TS_FLIP_TAC THEN
  CF2_L2_OUT_TAC THEN
  CF2_L2_HASH_LT_TAC CF2_L2_E2 THEN
  CF2_TABLE_SPLIT_TAC `table2:int64` CF2_L2_E2 THEN
  ARM_BSTEP_TAC CF2_L2_EXEC (1--1) THEN
  CF2_L2_TB_TAC `t2:num->num` CF2_L2_E2 THEN
  CF2_L2_ZX16_TAC CF2_L2_C2 THEN
  CF2_INPUT_TAC SNAPPY_READ_LOAD32 CF2_L2_C2 THEN
  ARM_BSTEP_TAC CF2_L2_EXEC (2--14) THEN
  CF2_L2_BRANCH_TAC ~extra:[CF2_L2_MOD32]
   (mk_eq(`snappy_load32 src ip`,
          mk_icomb(`snappy_load32 src`,CF2_L2_C2))) THENL
   [CF2_L2_MATCH2_TAC;
    CF2_L2_HASH4_TAC `snappy_load64 src ip` THEN
    CF2_L2_HASH_LT_TAC CF2_L2_E1 THEN
    CF2_TABLE_SPLIT_TAC `table:int64` CF2_L2_E1 THEN
    W(fun (asl,w) ->
      ARM_BSTEP_TAC ~rewrites:[CF2_L2_ZXZX_RULE asl CF2_L2_E1]
        CF2_L2_EXEC (15--15)) THEN
    CF2_L2_TB_TAC `t1:num->num` CF2_L2_E1 THEN
    CF2_L2_ZX16_TAC CF2_L2_C1 THEN
    CF2_INPUT_TAC SNAPPY_READ_LOAD32 CF2_L2_C1 THEN
    W(fun (asl,w) ->
      ARM_BSTEP_TAC ~rewrites:[CF2_L2_ZXZX_RULE asl CF2_L2_E1]
        CF2_L2_EXEC (16--20)) THEN
    CF2_L2_BRANCH_TAC ~extra:[CF2_L2_MOD32]
     (mk_eq(`snappy_load32 src ip`,
            mk_icomb(`snappy_load32 src`,CF2_L2_C1))) THENL
     [CF2_L2_MATCH1_TAC; CF2_L2_NOMATCH_TAC]]);;
